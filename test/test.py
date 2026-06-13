import random, time
from collections import namedtuple, defaultdict
import psycopg

SIZE = 4000000 # instance size
N_REWRITES = 500000 # number of rewrites applied
RELSIZES = {'P':2000000,'T':2000000} # table sizes
N_TRIALS = 9 # number of trials

QUERY_L = "SELECT x7.t1, x6.p1, x6.p2, x6.p3, x7.t3 FROM P AS x6, T AS x7 WHERE x6.p1 = x7.t2"
QUERY_Q = "SELECT x7.p1, x6.p1, x6.p2, x6.p3, x7.p3 FROM P AS x6, P AS x7 WHERE x6.p1 = x7.p2"

class Timer:
  def __init__(self, name): self.name = name
  def __enter__(self):
    self._begin_ns = time.perf_counter_ns()
    return self
  def __exit__(self, _exc_type, _exc_value, _traceback):
    self.duration_ns = time.perf_counter_ns() - self._begin_ns
    print(f"{self.duration_ns / 1_000_000:9.0f} ms  {self.name}")

TimingData = namedtuple("TimingData", ["total", "insertions", "q_updates", "edge_updates"])

class Instance:
  """Python in-memory representation of database instance"""
  def __init__(self, n:int, P:list[tuple],T:list[tuple]):
    self.n = n 
    self.P = P
    self.T = T
  
  def relations(self):
    return {'P':sorted(self.P),'T':sorted(self.T)}

  def rewrite(self, x1:int, x2:int, x3:int, x4:int, x5:int):
    """Apply rewrite rule, *assuming rule preconditions are met*"""
    r1, r2, r3, r4, r5, r6, r7 = x1, x2, x3, x4, x5, (self.n + 1), (self.n + 2)
    new_tuples = {'P':[],'T':[]}
    self.n += 2
    self.P.append((r1, r6, r7))
    new_tuples['P'].append((r1, r6, r7))
    self.T.append((r6, r3, r5))
    self.T.append((r7, r4, r5))
    new_tuples['T'].append((r6, r3, r5))
    new_tuples['T'].append((r7, r4, r5))
    return (r1, r2, r3, r4, r5, r6, r7), new_tuples

def generate_instance(vertices:int, relsizes: dict[str,int])->tuple[int,dict]:
  """ Generates a random DB instance """
  r = random.Random(0)
  return Instance(vertices, sorted([tuple([r.randint(1,vertices) for _ in ['p1', 'p2', 'p3']]) 
           for _ in range(relsizes['P'])]), sorted([tuple([r.randint(1,vertices) for _ in ['t1', 't2', 't3']]) 
           for _ in range(relsizes['T'])]))


def db_setup(cur):
  """ Creates DB tables for rewrite """
  # to standardize some performance-relevant settings, check postgres configuration
  # has 1GB for each of max_wal_size, shared_buffers, & work_mem.
  mws, sb, wm = cur.execute("""SELECT name, setting, unit FROM pg_settings
                              WHERE name = 'max_wal_size' 
                              OR name = 'shared_buffers'
                              OR name = 'work_mem'
                              ORDER BY name;""")
  assert mws == ('max_wal_size', '1024', 'MB')
  assert sb == ('shared_buffers', '131072', '8kB')
  assert wm == ('work_mem', '1048576', 'kB')
  
  cur.execute("CREATE TABLE IF NOT EXISTS P (p1 INTEGER, p2 INTEGER, p3 INTEGER)")
  cur.execute("ALTER TABLE P SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")

  cur.execute("CREATE TABLE IF NOT EXISTS delta_P (p1 INTEGER, p2 INTEGER, p3 INTEGER)")
  cur.execute("ALTER TABLE delta_P SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")

  cur.execute("CREATE TABLE IF NOT EXISTS T (t1 INTEGER, t2 INTEGER, t3 INTEGER)")
  cur.execute("ALTER TABLE T SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")

  cur.execute("CREATE TABLE IF NOT EXISTS delta_T (t1 INTEGER, t2 INTEGER, t3 INTEGER)")
  cur.execute("ALTER TABLE delta_T SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")

  cur.execute("CREATE TABLE IF NOT EXISTS Q (q1 INTEGER, q2 INTEGER, q3 INTEGER, q4 INTEGER, q5 INTEGER)")
  cur.execute("ALTER TABLE Q SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")

  cur.execute("CREATE TABLE IF NOT EXISTS Rewrite (id SERIAL PRIMARY KEY, r1 INTEGER, r2 INTEGER, r3 INTEGER, r4 INTEGER, r5 INTEGER, r6 INTEGER, r7 INTEGER)")
  cur.execute("ALTER TABLE Rewrite SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")



def show_tables(cur):
  for x in cur.execute("SELECT * FROM pg_catalog.pg_tables WHERE schemaname != 'pg_catalog' AND schemaname != 'information_schema'"):
    print(f"Table: {x}")

def db_clear(cur):
  cur.execute("DROP TABLE IF EXISTS P")
  cur.execute("DROP TABLE IF EXISTS delta_P")
  cur.execute("DROP TABLE IF EXISTS T")
  cur.execute("DROP TABLE IF EXISTS delta_T")
  cur.execute("DROP TABLE IF EXISTS Q")
  cur.execute("DROP TABLE IF EXISTS Rewrite")


def batch_delta(cur, new_tuples: dict):
  """ Update Q based on contents of the normal relations and the delta relations, then update the normal relations based on the delta relations """
  with Timer("Rewrites (total)") as total:
    """Run the incremental query via delta rules"""
    # Batch delta query.
    with Timer("Inserts into delta tables") as insertions:
        with cur.copy("COPY delta_P (p1,p2,p3) FROM STDIN") as copy:
          for (x1,x2,x3) in new_tuples['P']:
              copy.write_row((x1,x2,x3))
    cur.execute("ANALYZE delta_P")

    with cur.copy("COPY delta_T (t1,t2,t3) FROM STDIN") as copy:
          for (x1,x2,x3) in new_tuples['T']:
              copy.write_row((x1,x2,x3))
    cur.execute("ANALYZE delta_T")


    with Timer("Update Q") as q_updates:
      query = """INSERT INTO Q SELECT x7.p1, x6.p1, x6.p2, x6.p3, x7.p3
            FROM delta_P AS x6, P AS x7
            WHERE x6.p1 = x7.p2
            UNION ALL
            SELECT x7.p1, x6.p1, x6.p2, x6.p3, x7.p3
            FROM P AS x6, delta_P AS x7
            WHERE x6.p1 = x7.p2
            UNION ALL
            SELECT x7.p1, x6.p1, x6.p2, x6.p3, x7.p3
            FROM delta_P AS x6, delta_P AS x7
            WHERE x6.p1 = x7.p2"""
      # print('\n'.join(' * ' + r[0] for r in cur.execute(f"EXPLAIN {query}")))
      cur.execute(query)

    with Timer("Update relations from delta relations") as rel_updates:
      cur.execute("INSERT INTO P SELECT * FROM delta_P")
      cur.execute("INSERT INTO T SELECT * FROM delta_T")

  return TimingData(total.duration_ns, insertions.duration_ns, q_updates.duration_ns, rel_updates.duration_ns)

def batch_kris(cur, rewrites:tuple):
  """Run the incremental query via cube-based approach"""
  with Timer("Rewrites (total)") as total:

    with Timer("Inserts into rewrites") as insertions:
      with cur.copy("COPY Rewrite (r1, r2, r3, r4, r5, r6, r7) FROM STDIN") as copy:
        for (r1, r2, r3, r4, r5, r6, r7) in rewrites:
          copy.write_row((r1, r2, r3, r4, r5, r6, r7))
      cur.execute("ANALYZE Rewrite")

    with Timer("Update Q from rewrites") as q_updates:
      query = """ INSERT INTO Q (q1, q2, q3, q4, q5) 
    SELECT P1.p1, P1.p2, RW1.r6, RW1.r7, P1.p3
    FROM P AS P1, Rewrite AS RW1
    WHERE P1.p2 = RW1.r1"""
      cur.execute(query)

    with Timer("Update relations from rewrites") as rel_updates:
      cur.execute("""INSERT INTO P (p1,p2,p3) 
  SELECT r1, r6, r7 FROM Rewrite""")
      cur.execute("""INSERT INTO T (t1,t2,t3) 
  SELECT r6, r3, r5 FROM Rewrite
  UNION ALL 
  SELECT r7, r4, r5 FROM Rewrite""")

  return TimingData(total.duration_ns, insertions.duration_ns, q_updates.duration_ns, rel_updates.duration_ns)



def go(conn, cur):
  run_log = []

  with Timer(f"Create tables, load initial instance, create indexes"):
    db_setup(cur)

    db = generate_instance(SIZE, RELSIZES)

  # Add the instance to SQL 
  #------------------------
  with cur.copy("COPY P (p1, p2, p3) FROM STDIN") as copy:
      for tup in db.P: copy.write_row(tup)
  with cur.copy("COPY T (t1, t2, t3) FROM STDIN") as copy:
      for tup in db.T: copy.write_row(tup)

  # Generate rewrites
  #------------------
  r, rewrites, new_tuples = random.Random(0), [], {'P':[],'T':[]}
  # Get all matches for the pattern of the rewrite
  pattern_matches = list(cur.execute(QUERY_L))

  # Randomly select N_REWRITES of them
  if len(pattern_matches) < N_REWRITES:
    raise ValueError(f"Only {len(pattern_matches)} matches, wanted to perform {N_REWRITES}") 

  # Apply rewrites to in-memory instance
  for match in r.sample(pattern_matches, N_REWRITES):
    rws, new_tups = db.rewrite(*match)
    rewrites.append(rws)
    new_tuples['P'].extend(new_tups['P'])
    new_tuples['T'].extend(new_tups['T'])

  # Get all old matches for Q 
  old_results = defaultdict(int)
  for row in cur.execute(QUERY_Q):
    old_results[row] += 1

  # Get new matches for Q 
  with conn.transaction(force_rollback = True):
    db_clear(cur)
    db_setup(cur)
    with cur.copy("COPY P (p1, p2, p3) FROM STDIN") as copy:
        for tup in db.P: copy.write_row(tup)
    with cur.copy("COPY T (t1, t2, t3) FROM STDIN") as copy:
        for tup in db.T: copy.write_row(tup)
    all_results = defaultdict(int)
    for row in cur.execute(QUERY_Q):
      all_results[row] += 1

  new_results = {k: all_results[k]-old_results[k] for k in all_results.keys()}

  for v in new_results.values():
    assert v >= 0

  new_results = sorted([k for (k,v) in new_results.items() for _ in range(v)])


  # Going 1st seems to convey a small advantage
  thue_morse = [True] # using Thue-Morse sequence
  while len(thue_morse) < N_TRIALS:
    thue_morse += [not x for x in thue_morse]

  for i, bit in zip(range(N_TRIALS), thue_morse):
    for delta in ([True,False] if bit else [False,True]):
      print(f"\nRunning {'delta' if delta else 'kris'} {i}")

      # Vacuum before runs to try and improve consistency. Not sure if this works.
      with Timer("Vacuum (not counted in total)"): cur.execute("VACUUM")

      with conn.transaction(force_rollback = True):
        timing_data = batch_delta(cur, new_tuples) if delta else batch_kris(cur, rewrites)
        with Timer("Extracting database as sorted tuples"):
          relations = {'P':sorted(list(cur.execute("SELECT * FROM P ORDER BY p1, p2, p3"))), 'T':sorted(list(cur.execute("SELECT * FROM T ORDER BY t1, t2, t3")))}

        # Check relations match expected relations
        if db.relations() != relations:
          raise ValueError(f"{db.relations()}\n{relations}")

        # Check delta query table matches expectations
        with Timer("Getting Q rows in sorted order"):
          qrows = list(cur.execute("select * from Q order by q1,q2,q3,q4,q5"))


        if qrows != new_results:
          raise ValueError(f"{qrows}\n{new_results}")

      run_log.append((delta, i, timing_data))


  # timing table
  headers = ["total", "insert", "Q Δ", "edge Δ"]
  format_row = lambda row: [f"{v / 1_000_000_000:.2f}s" for v in row]

  deltas = [row for delta,_,row in run_log if delta]
  krises = [row for delta,_,row in run_log if not delta]

  cols_delta = [list(sorted(column)) for column in zip(*deltas)]
  cols_kris  = [list(sorted(column)) for column in zip(*krises)]

  avgs = lambda cols: [sum(c) / len(c) for c in cols]
  p = lambda p, cols: [c[round((len(c)-1) * p/100)] for c in cols]

  rows = ([[""] + headers] +
          [[f"delta {i}" if delta else f"kris {i}"] + format_row(row)
           for delta, i, row in run_log] +
          [[""] * (1 + len(cols_delta)),
           #[f"kris min"]  + format_row(mins(cols_kris)),
           [f"kris p10"]  + format_row(p(10, cols_kris)),
           [f"kris p50"]  + format_row(p(50, cols_kris)),
           [f"kris p90"]  + format_row(p(90, cols_kris)),
           #[f"kris max"]  + format_row(maxs(cols_kris)),
           [""] * (1 + len(cols_delta)),
           #[f"delta min"] + format_row(mins(cols_delta)),
           [f"delta p10"] + format_row(p(10, cols_delta)),
           [f"delta p50"] + format_row(p(50, cols_delta)),
           [f"delta p90"] + format_row(p(90, cols_delta)),
           #[f"delta max"] + format_row(maxs(cols_delta)),
           [""] * (1 + len(cols_delta)),
           [f"kris avg"]  + format_row(avgs(cols_kris)),
           [f"delta avg"] + format_row(avgs(cols_delta)),
           ])
  colsizes = [max(len(x) for x in column) for column in zip(*rows)]
  for row in rows:
      print("", *(v.rjust(size) for v, size in zip(row, colsizes)),
            sep="    ")



def main():
  with psycopg.connect("dbname=krisb", autocommit=True) as conn:
    # Disable auto-preparing queries for (hopefully) more consistent timing. Not sure
    # this makes a difference.
    conn.prepare_threshold = None
    # I tried cursor(binary=True) but didn't make much difference.
    with conn.cursor() as cur:
      with Timer("Clear tables"): db_clear(cur)
      go(conn, cur)
      db_clear(cur)

if __name__ == "__main__":
  main() # Don't forget `brew services start postgresql`!
