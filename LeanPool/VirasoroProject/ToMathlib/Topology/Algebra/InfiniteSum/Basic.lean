/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import LeanPool.VirasoroProject.ToMathlib.Topology.Order

/-!
# LeanPool.VirasoroProject.ToMathlib.Topology.Algebra.InfiniteSum.Basic
-/

section

open Filter
open scoped Topology

lemma DiscreteTopology.summable_iff_eventually_zero
    {E : Type*} [AddCommGroup E] [TopologicalSpace E] [DiscreteTopology E]
    {ι : Type*} (f : ι → E) :
    Summable f ↔ cofinite.Eventually (fun n ↦ f n = 0) := by
  classical
  constructor
  · intro ⟨v, hv⟩
    obtain ⟨s, hs⟩ := mem_atTop_sets.mp <|
      tendsto_iff_forall_eventually_mem.mp hv _ (show {v} ∈ 𝓝 v from mem_nhds_discrete.mpr rfl)
    apply eventually_cofinite.mpr (s.finite_toSet.subset ?_)
    intro i (hi : f i ≠ 0)
    by_contra con
    apply hi
    have obs : ∑ b ∈ insert i s, f b = v := hs (insert i s) (by simp)
    simpa [Finset.sum_insert con, show ∑ b ∈ s, f b = v from hs s le_rfl, add_eq_right] using obs
  · intro ev_zero
    exact summable_of_hasFiniteSupport (eventually_cofinite.mp ev_zero)

end
