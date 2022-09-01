module Visuals
export view_traj

using ..Schedules

using Interact

function view_traj(rG::ScheduleResult, viewer; positions=nothing)
  positions_cache = Vector{Any}(fill(nothing, length(rG)))
  positions_cache[1] = positions
  # Push forward previous positions along partial map if current ones unknown
  function get_positions(i)
    if      isnothing(positions)          return nothing
    elseif !isnothing(positions_cache[i]) return positions_cache[i]
    end
    old_pos, morph = get_positions(i-1), rG[i]
    pos = Vector{Any}(fill(nothing, nv(rG[i].G)))
    l, r = rG[i].pmap
    for (v, lv) in enumerate(collect(l[:V]))
      pos[r[:V](v)] = old_pos[lv]
    end
    return positions_cache[i] = pos
  end
  return Interact.@manipulate for n in Interact.slider(1:length(rG), value=1, label="Step:")
      step = rG[n]
      if n == length(rG)
        name, c = "end", ""
      else
        name = rG[n+1].title
        c = join([string(k=>c) for (k,c) in pairs(components(rG[n+1].m))
                  if !isempty(collect(c.func))], '\n')
      end
      viewer(step.G, get_positions(n); title="$name \n $c")
  end
end;

end # module
