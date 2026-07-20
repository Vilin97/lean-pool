/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import LeanPool.CencovPetz.LeftInverseIsometry
import LeanPool.CencovPetz.Replication


/-!
# `CencovPetz.ReplicationInvariance`

For a monotone metric family (Čencov setting), replication maps `α → α × Fin m` are isometries:
they have a deterministic left inverse (coarsening), so monotonicity holds in both directions.
-/

namespace LeanPool.CencovPetz
open scoped BigOperators

universe u

variable {α : Type u} [Fintype α]

namespace MonotoneMetricFamily

lemma comp_eq_of_replicate (G : MonotoneMetricFamily) (m : ℕ) (hm : 0 < m) (p : Simplex α) :
    (G.g (α := α × Fin m) ((MarkovMorphism.replicate (α := α) m hm).pushforward p)).comp
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforwardLinear)
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforwardLinear)
      = G.g (α := α) p := by
  classical
  let κ : MarkovMorphism α (α × Fin m) := MarkovMorphism.replicate (α := α) m hm
  let κ' : MarkovMorphism (α × Fin m) α := MarkovMorphism.coarsen (α := α) m hm
  refine MonotoneMetricFamily.comp_eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_
  · simpa [κ, κ'] using
      MarkovMorphism.coarsen_pushforward_replicate
        (α := α) (m := m) (hm := hm) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.coarsen_tangentPushforward_replicate
        (α := α) (m := m) (hm := hm) (u := u)

lemma eq_of_replicate (G : MonotoneMetricFamily) (m : ℕ) (hm : 0 < m) (p : Simplex α)
    (u v : tangentSpace (α := α)) :
    G.g (α := α × Fin m) ((MarkovMorphism.replicate (α := α) m hm).pushforward p)
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforward u)
        ((MarkovMorphism.replicate (α := α) m hm).tangentPushforward v)
      = G.g (α := α) p u v := by
  classical
  let κ : MarkovMorphism α (α × Fin m) := MarkovMorphism.replicate (α := α) m hm
  let κ' : MarkovMorphism (α × Fin m) α := MarkovMorphism.coarsen (α := α) m hm
  refine MonotoneMetricFamily.eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_ u v
  · simpa [κ, κ'] using
      MarkovMorphism.coarsen_pushforward_replicate
        (α := α) (m := m) (hm := hm) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.coarsen_tangentPushforward_replicate
        (α := α) (m := m) (hm := hm) (u := u)

end MonotoneMetricFamily
end LeanPool.CencovPetz
