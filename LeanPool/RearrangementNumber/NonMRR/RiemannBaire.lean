/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.Riemann
import Mathlib.Topology.Order.LiminfLimsup

/-!
# A rearrangement with unbounded partial sums

The finite extension lemma supplies dense open conditions in the complete
space of injections. Simultaneously requiring each integer in the range
turns the resulting injection into a permutation.
-/

open Filter Finset Set Topology

namespace NonMRR

theorem continuous_partialSum_on_injections (a : ℕ → ℝ) (M : ℕ) :
    Continuous (fun f : InjectionSpace => partialSum (a ∘ f.val) M) := by
  apply continuous_finsetSum
  intro i _hi
  exact (continuous_of_discreteTopology : Continuous a).comp
    ((continuous_apply i).comp continuous_subtype_val)

/-- Every real sequence which is not absolutely summable has a permutation
with unbounded absolute partial sums. -/
theorem exists_perm_unbounded_partialSum (a : ℕ → ℝ)
    (ha : ¬ Summable (fun i => |a i|)) :
    ∃ π : Equiv.Perm ℕ, ∀ k : ℕ,
      ∃ M, (k : ℝ) < |partialSum (a ∘ π) M| := by
  classical
  let U (k : ℕ) : Set InjectionSpace :=
    {f | (∃ M, (k : ℝ) < |partialSum (a ∘ f.val) M|) ∧ k ∈ Set.range f.val}
  have hUopen (k : ℕ) : IsOpen (U k) := by
    have hpartial : IsOpen {f : InjectionSpace |
        ∃ M, (k : ℝ) < |partialSum (a ∘ f.val) M|} := by
      simp only [Set.setOf_exists]
      exact isOpen_iUnion fun M => isOpen_lt continuous_const
        (continuous_partialSum_on_injections a M).abs
    have hrange : IsOpen {f : InjectionSpace | k ∈ Set.range f.val} := by
      change IsOpen {f : InjectionSpace | ∃ j, f.val j = k}
      simp only [Set.setOf_exists]
      apply isOpen_iUnion
      intro j
      have hpre : IsOpen ((fun f : InjectionSpace => f.val j) ⁻¹' ({k} : Set ℕ)) :=
        (isOpen_discrete _).preimage ((continuous_apply j).comp continuous_subtype_val)
      convert hpre using 1
    exact hpartial.inter hrange
  have hUdense (k : ℕ) : Dense (U k) := by
    apply dense_injections_of_extension
    intro f N
    obtain ⟨π, hπextend, hπlarge⟩ :=
      exists_perm_large_partialSum a ha f.val f.property N k
    exact ⟨⟨π, π.injective⟩, ⟨hπlarge, π.surjective k⟩, hπextend⟩
  obtain ⟨f, hf⟩ := (dense_iInter_of_isOpen hUopen hUdense).nonempty
  have hsurj : Function.Surjective f.val := fun k => (Set.mem_iInter.mp hf k).2
  let π : Equiv.Perm ℕ := Equiv.ofBijective f.val ⟨f.property, hsurj⟩
  refine ⟨π, ?_⟩
  intro k
  exact (Set.mem_iInter.mp hf k).1

/-- Every conditionally convergent series is rearranged by some permutation. -/
theorem exists_rearranges (a : ConditionalSeries) :
    ∃ π : Equiv.Perm ℕ, Rearranges a π := by
  obtain ⟨π, hπ⟩ := exists_perm_unbounded_partialSum a.term a.not_absolute
  refine ⟨π, ?_⟩
  intro hpreserves
  have hbounded := (hasSum_conditional_iff.mp hpreserves).norm.bddAbove_range
  obtain ⟨C, hC⟩ := hbounded
  obtain ⟨k, hk⟩ := exists_nat_gt C
  obtain ⟨M, hM⟩ := hπ k
  have hCM : |partialSum (a.term ∘ π) M| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (Set.mem_range_self M)
  exact (not_lt_of_ge hCM) (hk.trans hM)

theorem forall_exists_rearranges :
    ∀ a : ConditionalSeries, ∃ π : Equiv.Perm ℕ, Rearranges a π :=
  exists_rearranges

/-- All permutations form a rearranging family. -/
theorem isRearranging_univ : IsRearranging (Set.univ : Set (Equiv.Perm ℕ)) := by
  intro a
  obtain ⟨π, hπ⟩ := exists_rearranges a
  exact ⟨π, Set.mem_univ π, hπ⟩

theorem exists_rearranging_family :
    ∃ P : Set (Equiv.Perm ℕ), IsRearranging P :=
  ⟨Set.univ, isRearranging_univ⟩

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
