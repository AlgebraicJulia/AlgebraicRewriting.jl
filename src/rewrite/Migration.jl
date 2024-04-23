module Migration 
export yoneda_cache, SchRule, SchRulel, SchRuler, SchRule, SchPBPO

using Catlab
using ..Utils 

# Rule schemas 
##############

@present SchRule_(FreeSchema) begin
  L::Ob # inputs
  R::Ob # outputs
  K::Ob # keep
end

@present SchRulel <: SchRule_ begin 
  l::Hom(L, K)
end
@present SchRuler <: SchRule_ begin 
  r::Hom(R, K)
end

@present SchRule <: SchRulel begin 
  r::Hom(R, K)
end

@present SchPBPO <: SchRule begin 
  (L′, K′)::Ob 
  tₗ::Hom(L′,L) 
  tₖ::Hom(K′,K)
  l′::Hom(L′,K′)
end

# Caching
#########

"""
Want a filename that is stable to multiple Julia sessions but changes when the
schema changes. This minimizes the need to clear the cache.
"""
pres_hash(p::Presentation) = "$(hash(p.generators))_$(hash(p.equations))"

function yoneda_cache(T::Type,S=nothing; clear=false, cache="cache")
  S = isnothing(S) ? Presentation(T) : S
  tname = "$(nameof(T))_$(pres_hash(S))"
  cache_dict = Dict{Symbol,Tuple{T,Int}}(map(generators(S, :Ob)) do ob
    name = nameof(ob)
    cache_dir = mkpath(joinpath(cache, "$tname"))
    path, ipath = joinpath.(cache_dir, ["$name.json", "_id_$name.json"])
    name => if !clear && isfile(path)
      (read_json_acset(T, path), parse(Int,open(io->read(io, String), ipath)))
    else 
      @debug "Computing representable $name"
      rep, i = representable(T, S, name; return_unit_id=true)
      write_json_acset(rep, path)
      write(ipath, string(i))
      (rep, i)
    end
  end)
  return yoneda(T; cache=cache_dict)
end

end # module 