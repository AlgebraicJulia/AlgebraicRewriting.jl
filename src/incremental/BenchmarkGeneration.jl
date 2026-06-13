module BenchmarkGeneration

using Catlab
using Combinatorics: powerset
using ..IHSData: distinguished_object, IHS
using ..IHSAccess: state, pattern, get_cases


"""
Generates a query that implements the delta rules. E.g. for path graph of length 
two, it produces:

```sql
INSERT INTO Q 
SELECT x4.src, x5.src, x5.tgt
FROM deltaE AS x4, E AS x5
WHERE x5.src = x4.tgt
 UNION ALL
SELECT x4.src, x5.src, x5.tgt
FROM E AS x4, deltaE AS x5
WHERE x5.src = x4.tgt
 UNION ALL
SELECT x4.src, x5.src, x5.tgt
FROM deltaE AS x4, deltaE AS x5
WHERE x5.src = x4.tgt
```
"""
function generate_delta_query(query::ACSet)
  V = distinguished_object(acset_schema(query))
  elems = elements(query)
  representatives = [incident(elems, v, :tgt) for v in parts(query, V)] # This assumes that the "V" object is first!
  lookup(rep_idx::Int) = "x$(elems[rep_idx,:src]).$(elems[rep_idx,(:πₐ,:nameh)])"
  function delta_query(delta_tuples)
    SELECT = "SELECT "*join(lookup.(first.(representatives)), ", ")
    FROM = "FROM "* join(map(unique(elems[:src])) do el 
      arr = first(incident(elems, el, :src))
      table = elems[arr,(:πₐ,:dom,:nameo)]
      "$(el ∈ delta_tuples ? "delta_" : "")$(table) AS x$el"
    end ,", ")
    WHERE = "WHERE "*join(vcat(map(representatives) do reprs
      n = 1:length(reprs)
      ijs = collect(filter(((i,j),)->i<j, collect(Iterators.product(n,n))))
      map(ijs) do (i, j)
          "$(lookup(reprs[i])) = $(lookup(reprs[j]))"
      end
    end...)," AND ")
    join([SELECT, FROM, WHERE],"\n            ")
  end

  # A delta rule case for each nonempty subset of the query
  res = delta_query.(collect(powerset(unique(elems[:src])))[2:end])    
  "INSERT INTO Q " * join(res,"\n            UNION ALL\n            ")
end

""" Convert an CSet into an ordinary SQL query """
function generate_query(query::ACSet)
  V = distinguished_object(acset_schema(query))
  elems = elements(query)
  representatives = [incident(elems, v, :tgt) for v in parts(query, V)]
  lookup(rep_idx::Int) = "x$(elems[rep_idx,:src]).$(elems[rep_idx,(:πₐ,:nameh)])"
  SELECT = "SELECT "*join(lookup.(first.(representatives)), ", ")

  FROM = "FROM "* join(map(unique(elems[:src])) do el 
    arr = first(incident(elems, el, :src))
    table = elems[arr,(:πₐ,:dom,:nameo)]
    "$(table) AS x$el"
  end ,", ")

  whereclauses = vcat(map(representatives) do reprs
    map(zip(reprs, reprs[2:end])) do (i, j)
        "$(lookup(i)) = $(lookup(j))"
    end
  end...)
  WHERE = (isempty(whereclauses) ? "" : "WHERE ")*join(whereclauses, " AND ")

  "$SELECT $FROM $WHERE"
end

""" Construct relations with uniform probabilities """
function generate_initial_data(S::Schema)
  V = distinguished_object(S)
  vecs = join(map(filter(!=(V), ob(S))) do o 
    "sorted([tuple([r.randint(1,vertices) for _ in [$(join(["'$h'" for h in homs(S; from=o, just_names=true)], ", "))]]) 
           for _ in range(relsizes['$o'])])"
  end, ", ")
  """
def generate_instance(vertices:int, relsizes: dict[str,int])->tuple[int,dict]:
  \"\"\" Generates a random DB instance \"\"\"
  r = random.Random(0)
  return Instance(vertices, $vecs)
"""
end

function generate_db_setup(Q::ACSet, f::ACSetTransformation)
  function ct(tabname, cols::Vector{String}; id=false)::String 
    i = id ? "id SERIAL PRIMARY KEY, " : ""
    """
    cur.execute("CREATE TABLE IF NOT EXISTS $tabname ($i$(join([x*" INTEGER" for x in cols],", ")))")
      cur.execute("ALTER TABLE $tabname SET (autovacuum_enabled = false, toast.autovacuum_enabled = off)")
    """
  end
  S::Schema = acset_schema(f)
  V = distinguished_object(S)
  nv(X::ACSet) = nparts(X, V)
  NQ = nv(Q)
  ctrels = join(map(filter(!=(V), ob(S))) do o 
    ct1 = ct(string(o), string.(homs(S; from=o, just_names=true))) 
    ct2 = ct("delta_$o", string.(homs(S; from=o, just_names=true)))
    "$ct1\n  $ct2"
  end, "\n  ")
  qcols = ["q$i" for i in 1:NQ]
  rcols = ["r$i" for i in 1:nparts(codom(f), V)]
  """
def db_setup(cur):
  \"\"\" Creates DB tables for rewrite \"\"\"
  # to standardize some performance-relevant settings, check postgres configuration
  # has 1GB for each of max_wal_size, shared_buffers, & work_mem.
  mws, sb, wm = cur.execute(\"\"\"SELECT name, setting, unit FROM pg_settings
                              WHERE name = 'max_wal_size' 
                              OR name = 'shared_buffers'
                              OR name = 'work_mem'
                              ORDER BY name;\"\"\")
  assert mws == ('max_wal_size', '1024', 'MB')
  assert sb == ('shared_buffers', '131072', '8kB')
  assert wm == ('work_mem', '1048576', 'kB')
  
  $ctrels
  $(ct('Q', qcols))
  $(ct("Rewrite",rcols;id=true))
"""
end


""" Create a UNION clause for each rewrite-aware multidecomposition """
function batch_kris(ihs; cases=nothing)
  Q = pattern(ihs)
  S = acset_schema(Q)
  V = distinguished_object(S)
  f = ihs[1, :qrule]
  case_analysis = isnothing(cases) ? get_cases(ihs; batch=true, quotient=true) : cases;
  cases = map(case_analysis) do case
    ιG, decomps = case[:old], case[:decomps]
    Q = codom(ιG)

    ι_vec = [ιG; getindex.(decomps,:QR)]

    # FOR ANY VERTEX IN Q, GET RELATIONS IN Q_G / R_i
    function get_rels(vert::Int)
      # get all relations the vertex participates in that are included in ιG
      qg_rels = []
      for o in filter(!=(V), ob(S))
        for r in parts(dom(ιG), o)
          for f in homs(S; from=o, just_names=true)
            if codom(ιG)[ιG[o](r), f] == vert 
              push!(qg_rels, (o, r, f))
            end
          end
        end
      end
      rs_rels = map(zip(ι_vec[2:end], getindex.(decomps,:hR))) do (ιR, hR)
        pi = preimage(ιR[V], vert)
        isempty(pi) ? nothing : hR[V](only(pi))
      end
      
      [preimage(ιR[V], vert) for ιR in ι_vec[2:end]]
      (qg_rels, rs_rels)
    end

    select_strs = map(parts(Q, V)) do i 
      (qg_rels, rs_rels) = get_rels(i)
      if !isempty(qg_rels)
        (rel, rel_i, fk) = first(qg_rels)
        "$rel$rel_i.$fk"
      else
        rw_idx = findfirst(!isnothing, rs_rels)
        "RW$rw_idx.r$(rs_rels[rw_idx][1])"
      end
    end

    sel = "\n    SELECT "*join(select_strs, ", ")

    # A join for each relation in ιG and each decomposition R
    fromstrs = []
    for x in first.(get_rels.(parts(Q,V))), (o, i) in x
      push!(fromstrs, "$o AS $o$i")
    end
    for i in 1:length(decomps)
      push!(fromstrs, "Rewrite AS RW$i")
    end
    from = "\n    FROM "*join(unique(fromstrs), ", ")

    whereconds = vcat(map(get_rels.(parts(Q, V))) do (qg_rels, rs_rels)
      eqclass = ["$rel$rel_i.$fk" for (rel, rel_i, fk)  in qg_rels
                ] ∪ ["RW$i.r$r" for (i,r) in enumerate(rs_rels) if !isnothing(r)]
      gconds = map(zip(eqclass, eqclass[2:end])) do (a,b)
        "$a = $b"
      end
    end...)
    for (idx, dc) in enumerate(decomps)
      quot = dc[:quot][V]
      fV = dc[:rule][V]
      for eqclass in [sort(fV.(collect(e))) for e in quot if length(e)>1]
        for (a,b) in zip(eqclass, eqclass[2:end])
          push!(whereconds, "RW$idx.r$a = RW$idx.r$b")
        end
      end
      for idx2 in (idx+1):length(decomps)
        push!(whereconds, "RW$idx.id != RW$idx2.id")
      end
    end

    # possibly that add that RW#i.primary_key ≠ RW#j.primary_key?

    wher = (isempty(whereconds) ? "" : "\n    WHERE ")*join(whereconds, " AND ")

    sel*from*wher
  end

  cases = if isempty(cases) 
    "SELECT "*join(fill("NULL",nv(pattern(ihs))),",")*" WHERE FALSE"
  else 
    join(cases, "\n\n  UNION ALL\n")
  end

  qcols = join(["q$i" for i in 1:nparts(pattern(ihs),V)], ", ")
  " INSERT INTO Q ($qcols) "*cases
end

""" Given a Rewrite table, update the relations of the DB
"""
function batch_updates(ihs)
  f = ihs[1, :qrule]
  R = codom(f)
  S::Schema = acset_schema(f)
  V = distinguished_object(S)

  qs = map(filter(!=(V), ob(S))) do o 
    fks = homs(S; from=o, just_names=true)
    new_o = join(filter(!isnothing, map(parts(R, o)) do i 
      if isempty(preimage(f[o], i))
        rs = ["r$(R[i, fk])" for fk in fks]
        return "SELECT $(join(rs,", ")) FROM Rewrite"
      end
    end), "\n  UNION ALL \n  ")
    """cur.execute(\"\"\"INSERT INTO $o ($(join(fks, ","))) \n  $new_o\"\"\")"""
  end
  join(qs, "\n      ")
end

function generate_benchmark(ihs::IHS; SIZE=4_000_000, N_REWRITES=500_000, 
                            RELSIZE=2_000_000, N_TRIALS=9, cases=nothing, 
                            runbenchmark=true)
  nparts(ihs, :Rule) == 1 && nparts(ihs, :PatternCC) == 1 || error(
    "Maximum one pattern and one rule")
  S = acset_schema(state(ihs))
  f = ihs[1,:qrule]
  L, R = dom(f), codom(f)

  V = distinguished_object(S)
  nv(X::ACSet) = nparts(X, V)

  nL = nv(L)

  xs(i::Int) = ["x$a" for a in 1:i]
  Q = pattern(ihs)
  NQ = nv(Q)
  qcols = ["q$i" for i in 1:NQ]
  rels = filter(!=(V), ob(S))
  qrels = join(map(rels) do o 
    """'$o':sorted(list(cur.execute("SELECT * FROM $o ORDER BY $(join(homs(S; from=o, just_names=true),", "))")))"""
  end,", ")

  # clear 
  #-------
  drop(t) = """cur.execute("DROP TABLE IF EXISTS $t")"""
  clear_stmts = [drop(r)*"\n  "*drop("delta_$r") for r in rels]

  # instance to sql 
  #---------------
  function inst_to_sqlclause(o::Symbol, indent=0)
    fks = homs(S; from=o, just_names=true)
    ind = join(fill("  ",indent+2))
    ("with cur.copy(\"COPY $o ($(join(fks, ", "))) FROM STDIN\") as copy:\n"
    *"$(ind)  for tup in db.$o: copy.write_row(tup)")    
  end

  # Instance definition 
  #--------------------
  new_rvals = findall(r->isempty(preimage(f[V], r)), parts(R, V))
  rvals = map(parts(R, V)) do r 
    rval = findfirst(==(r), new_rvals)
    isnothing(rval) ? "x$(only(preimage(f[V], r)))" : "(self.n + $rval)"
  end
  rewrite_stmts = vcat(map(rels) do rel
    tups = map(parts(R, rel)) do relᵢ
      [R[relᵢ, fk] for fk in homs(S; from=rel, just_names=true)]
    end
    filter!(tup->any(∈(new_rvals), tup), tups)
    map(tups) do tup
      "self.$rel.append(($(join(["r$i" for i in tup],", "))))"
    end ∪ map(tups) do tup 
      "new_tuples['$rel'].append(($(join(["r$i" for i in tup],", "))))"
    end
  end...)

  # Batch delta
  #--------------
  dq = generate_delta_query(Q)
  batch_delta_inserts = map(rels) do rel 
    hs = homs(S; from=rel, just_names=true)
    vars = join(xs(length(hs)), ",")
    
    """
    with cur.copy("COPY delta_$rel ($(join(Symbol.(hs),","))) FROM STDIN") as copy:
            for ($vars) in new_tuples['$rel']:
                copy.write_row(($vars))
      cur.execute("ANALYZE delta_$rel")
  """
  end
  # Batch Kris 
  #-----------
  ridx = join(["r$i" for i in 1:nv(R)],", ")


  # Putting it all together 
  #-------------------------
  file = """
import random, time
from collections import namedtuple, defaultdict
import psycopg

SIZE = $SIZE # instance size
N_REWRITES = $N_REWRITES # number of rewrites applied
RELSIZES = {$(join(["'$rel':$RELSIZE" for rel in rels],","))} # table sizes
N_TRIALS = $N_TRIALS # number of trials

QUERY_L = "$(generate_query(L))"
QUERY_Q = "$(generate_query(Q))"

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
  \"\"\"Python in-memory representation of database instance\"\"\"
  def __init__(self, n:int, $(join(["$r:list[tuple]" for r in rels], ","))):
    self.n = n 
    $(join(["self.$r = $r" for r in rels], "\n    "))
  
  def relations(self):
    return {$(join(["'$r':sorted(self.$r)" for r in rels],","))}

  def rewrite(self, $(join(["$x:int" for x in xs(nL)], ", "))):
    \"\"\"Apply rewrite rule, *assuming rule preconditions are met*\"\"\"
    $ridx = $(join(rvals,", "))
    new_tuples = {$(join(["'$r':[]" for r in rels], ","))}
    self.n += $(nv(R)-nL)
    $(join(rewrite_stmts,"\n    "))
    return ($ridx), new_tuples

$(generate_initial_data(S))

$(generate_db_setup(Q,f))

def show_tables(cur):
  for x in cur.execute("SELECT * FROM pg_catalog.pg_tables WHERE schemaname != 'pg_catalog' AND schemaname != 'information_schema'"):
    print(f"Table: {x}")

def db_clear(cur):
  $(join(clear_stmts, "\n  "))
  cur.execute("DROP TABLE IF EXISTS Q")
  cur.execute("DROP TABLE IF EXISTS Rewrite")


def batch_delta(cur, new_tuples: dict):
  \"\"\" Update Q based on contents of the normal relations and the delta relations, then update the normal relations based on the delta relations \"\"\"
  with Timer("Rewrites (total)") as total:
    \"\"\"Run the incremental query via delta rules\"\"\"
    # Batch delta query.
    with Timer("Inserts into delta tables") as insertions:
      $(join(batch_delta_inserts, "\n  "))

    with Timer("Update Q") as q_updates:
      query = \"\"\"$dq\"\"\"
      # print('\\n'.join(' * ' + r[0] for r in cur.execute(f"EXPLAIN {query}")))
      cur.execute(query)

    with Timer("Update relations from delta relations") as rel_updates:
      $(join(["cur.execute(\"INSERT INTO $r SELECT * FROM delta_$r\")" for r in rels], "\n      "))

  return TimingData(total.duration_ns, insertions.duration_ns, q_updates.duration_ns, rel_updates.duration_ns)

def batch_kris(cur, rewrites:tuple):
  \"\"\"Run the incremental query via cube-based approach\"\"\"
  with Timer("Rewrites (total)") as total:

    with Timer("Inserts into rewrites") as insertions:
      with cur.copy("COPY Rewrite ($ridx) FROM STDIN") as copy:
        for ($ridx) in rewrites:
          copy.write_row(($ridx))
      cur.execute("ANALYZE Rewrite")

    with Timer("Update Q from rewrites") as q_updates:
      query = \"\"\"$(batch_kris(ihs; cases))\"\"\"
      cur.execute(query)

    with Timer("Update relations from rewrites") as rel_updates:
      $(batch_updates(ihs))

  return TimingData(total.duration_ns, insertions.duration_ns, q_updates.duration_ns, rel_updates.duration_ns)



def go(conn, cur):
  run_log = []

  with Timer(f"Create tables, load initial instance, create indexes"):
    db_setup(cur)

    db = generate_instance(SIZE, RELSIZES)

  # Add the instance to SQL 
  #------------------------
  $(join(inst_to_sqlclause.(filter(!=(V),ob(S))), "\n  "))

  # Generate rewrites
  #------------------
  r, rewrites, new_tuples = random.Random(0), [], {$(join(["'$r':[]" for r in rels],","))}
  # Get all matches for the pattern of the rewrite
  pattern_matches = list(cur.execute(QUERY_L))

  # Randomly select N_REWRITES of them
  if len(pattern_matches) < N_REWRITES:
    raise ValueError(f"Only {len(pattern_matches)} matches, wanted to perform {N_REWRITES}") 

  # Apply rewrites to in-memory instance
  for match in r.sample(pattern_matches, N_REWRITES):
    rws, new_tups = db.rewrite(*match)
    rewrites.append(rws)
    $(join(["new_tuples['$r'].extend(new_tups['$r'])" for r in rels],"\n    "))

  # Get all old matches for Q 
  old_results = defaultdict(int)
  for row in cur.execute(QUERY_Q):
    old_results[row] += 1

  # Get new matches for Q 
  with conn.transaction(force_rollback = True):
    db_clear(cur)
    db_setup(cur)
    $(join(inst_to_sqlclause.(filter(!=(V),ob(S)),1), "\n    "))
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
      print(f"\\nRunning {'delta' if delta else 'kris'} {i}")

      # Vacuum before runs to try and improve consistency. Not sure if this works.
      with Timer("Vacuum (not counted in total)"): cur.execute("VACUUM")

      with conn.transaction(force_rollback = True):
        timing_data = batch_delta(cur, new_tuples) if delta else batch_kris(cur, rewrites)
        with Timer("Extracting database as sorted tuples"):
          relations = {$qrels}

        # Check relations match expected relations
        if db.relations() != relations:
          raise ValueError(f"{db.relations()}\\n{relations}")

        # Check delta query table matches expectations
        with Timer("Getting Q rows in sorted order"):
          qrows = list(cur.execute("select * from Q order by $(join(qcols, ','))"))


        if qrows != new_results:
          raise ValueError(f"{qrows}\\n{new_results}")

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
"""
  open("test/test.py", "w") do io 
    write(io, file)
  end
  runbenchmark && run(`test/venv/bin/python3 test/test.py`)
end

end # module
