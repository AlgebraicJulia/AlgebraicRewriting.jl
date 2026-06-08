import random, time, math, sys
from collections import namedtuple
import psycopg

X = 1000000
SIZE = 2*X # instance size
N_REWRITES = X # number of rewrites applied
RELSIZES = {'E':X} # table sizes
N_TRIALS = 3 # number of trials

QUERY_L = "SELECT x3.src, x3.tgt FROM E AS x3 "
QUERY_Q = "SELECT x4.src, x5.src, x5.tgt FROM E AS x4, E AS x5 WHERE x5.src = x4.tgt"

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
  def __init__(self, n:int, E:list[tuple]):
    self.n = n 
    self.E = E
  
  def relations(self):
    return {'E':sorted(self.E)}

  def rewrite(self, x1:int, x2:int):
    """Apply rewrite rule, *assuming rule preconditions are met*"""
    r1, r2, r3 = x1, (self.n + 1), x2
    self.n += 1
    self.E.append((r1, r2))
    self.E.append((r2, r3))
    return (r1, r2, r3)

def generate_instance(vertices:int, relsizes: dict[str,int])->tuple[int,dict]:
  """ Generates a random DB instance """
  r = random.Random(0)
  return Instance(vertices, sorted([tuple([r.randint(1,vertices) for _ in ['src', 'tgt']]) 
           for _ in range(relsizes['E'])]))


def db_setup(cur):
  """ Creates DB tables for rewrite """
  cur.execute("CREATE TABLE IF NOT EXISTS E (src INTEGER, tgt INTEGER)")
  cur.execute("ALTER TABLE E SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")

  cur.execute("CREATE TABLE IF NOT EXISTS delta_E (src INTEGER, tgt INTEGER)")
  cur.execute("ALTER TABLE delta_E SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")

  cur.execute("CREATE TABLE IF NOT EXISTS Q (q1 INTEGER, q2 INTEGER, q3 INTEGER)")
  cur.execute("ALTER TABLE Q SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")

  cur.execute("CREATE TABLE IF NOT EXISTS Rewrite (id SERIAL PRIMARY KEY, r1 INTEGER, r2 INTEGER, r3 INTEGER)")
  cur.execute("ALTER TABLE Rewrite SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")



def show_tables(cur):
  for x in cur.execute("SELECT * FROM pg_catalog.pg_tables WHERE schemaname != 'pg_catalog' AND schemaname != 'information_schema'"):
    print(f"Table: {x}")

def db_clear(cur):
  cur.execute("DROP TABLE IF EXISTS E")
  cur.execute("DROP TABLE IF EXISTS delta_E")
  cur.execute("DROP TABLE IF EXISTS Q")
  cur.execute("DROP TABLE IF EXISTS Rewrite")


def batch_delta(cur, db: Instance):
  """ Update Q based on contents of the normal relations and the delta relations, then update the normal relations based on the delta relations """
  with Timer("Rewrites (total)") as total:
    """Run the incremental query via delta rules"""
    # Batch delta query.
    with Timer("Inserts into delta tables") as insertions:
        with cur.copy("COPY delta_E (src, tgt) FROM STDIN") as copy:
          for (x1,x2) in db.E:
            if max([x1,x2]) > SIZE: # i.e. if this is a new E
              copy.write_row((x1,x2))
    cur.execute("ANALYZE delta_E")


    with Timer("Update Q") as q_updates:
      query = """INSERT INTO Q SELECT x4.src, x5.src, x5.tgt
            FROM delta_E AS x4, E AS x5
            WHERE x5.src = x4.tgt
            UNION ALL
            SELECT x4.src, x5.src, x5.tgt
            FROM E AS x4, delta_E AS x5
            WHERE x5.src = x4.tgt
            UNION ALL
            SELECT x4.src, x5.src, x5.tgt
            FROM delta_E AS x4, delta_E AS x5
            WHERE x5.src = x4.tgt"""
      # print('\n'.join(' * ' + r[0] for r in cur.execute(f"EXPLAIN {query}")))
      cur.execute(query)

    with Timer("Update relations from delta relations") as rel_updates:
      cur.execute("INSERT INTO E SELECT * FROM delta_E")

  return TimingData(total.duration_ns, insertions.duration_ns, q_updates.duration_ns, rel_updates.duration_ns)

def batch_kris(cur, _: Instance, rewrites:tuple):
  """Run the incremental query via cube-based approach"""
  with Timer("Rewrites (total)") as total:

    with Timer("Inserts into rewrites") as insertions:
      with cur.copy("COPY Rewrite (r1, r2, r3) FROM STDIN") as copy:
        for (r1, r2, r3) in rewrites:
          copy.write_row((r1, r2, r3))
      cur.execute("ANALYZE Rewrite")

    with Timer("Update Q from rewrites") as q_updates:
      query = """ INSERT INTO Q (q1, q2, q3) 
		SELECT E1.src, E1.tgt, RW1.r2
		FROM E AS E1, Rewrite AS RW1
		WHERE E1.tgt = RW1.r1

	UNION ALL

		SELECT RW1.r2, E1.src, E1.tgt
		FROM E AS E1, Rewrite AS RW1
		WHERE E1.src = RW1.r3

	UNION ALL

		SELECT RW1.r1, RW1.r2, RW1.r3
		FROM Rewrite AS RW1

	UNION ALL

		SELECT RW1.r2, RW1.r1, RW1.r2
		FROM Rewrite AS RW1
		WHERE RW1.r1 = RW1.r3

	UNION ALL

		SELECT RW1.r2, RW1.r3, RW2.r2
		FROM Rewrite AS RW1, Rewrite AS RW2
		WHERE RW1.r3 = RW2.r1 AND RW1.id != RW2.id"""
      cur.execute(query)

    with Timer("Update relations from rewrites") as rel_updates:
      cur.execute("""INSERT INTO E (src,tgt) 
	SELECT r1, r2 FROM Rewrite
	UNION ALL 
	SELECT r2, r3 FROM Rewrite""")

  return TimingData(total.duration_ns, insertions.duration_ns, q_updates.duration_ns, rel_updates.duration_ns)



def go(conn, cur):
  run_log = []

  with Timer(f"Create tables, load initial instance, create indexes"):
    db_setup(cur)

    db = generate_instance(SIZE, RELSIZES)

    # Add the instance to SQL 
    #------------------------
    with cur.copy("COPY E (src, tgt) FROM STDIN") as copy:
      for tup in db.E: copy.write_row(tup)

    # Generate rewrites
    #------------------
    r, rewrites = random.Random(0), []
    # Get all matches for the pattern of the rewrite
    pattern_matches = list(cur.execute(QUERY_L))
    
    # Randomly select N_REWRITES of them
    if len(pattern_matches) < N_REWRITES:
      raise ValueError(f"Only {len(pattern_matches)} matches, wanted to perform {N_REWRITES}") 

    # Apply rewrites to in-memory instance
    for match in r.sample(pattern_matches, N_REWRITES):
      rewrites.append(db.rewrite(*match))

    # Get all old matches for Q 
    old_results = set(cur.execute(QUERY_Q))

    # Get new matches for Q 
    with conn.transaction(force_rollback = True):
      db_clear(cur)
      db_setup(cur)
      with cur.copy("COPY E (src, tgt) FROM STDIN") as copy:
        for tup in db.E: copy.write_row(tup)
      all_results = set(list(cur.execute(QUERY_Q)))

    if not old_results.issubset(all_results):
      raise ValueError("Mistake")

    new_results = all_results.difference(old_results)

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
          timing_data = batch_delta(cur, db) if delta else batch_kris(cur, db, rewrites)
          with Timer("Extracting database as sorted tuples"):
            relations = {'E':sorted(list(cur.execute("SELECT * FROM E ORDER BY src, tgt")))}

          # Check relations match expected relations
          if db.relations() != relations:
            raise ValueError(f"{db.relations()}\n{relations}")

          # Check delta query table matches expectations
          with Timer("Getting Q rows in sorted order"):
            qrows = tuple(cur.execute("select * from Q order by q1,q2,q3"))

          # For debugging
          if len(qrows)!=len(set(qrows)):
            print(f"WARNING: qrows {len(qrows)} (unique: {len(set(qrows))}))")

          if set(qrows) != new_results:
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
