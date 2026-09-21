/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanPool.RearrangementNumber.NonMRR.Padding
import LeanPool.RearrangementNumber.NonMRR.PermutationBounds

/-!
# The classical lower bound by the bounding number

Every family of fewer than `boundingNumber` permutations preserves a common
conditionally convergent real series. Thus every rearranging family has size at
least the bounding number. This statement does not presume that a rearranging
family has already been constructed.
-/

open Filter Cardinal Topology

namespace NonMRR

/-- Permuting a zero-padded series changes its placement to the inverse-permuted
placement. -/
theorem extend_comp_perm (b : ℕ → ℝ) (l : ℕ → ℕ) (hl : Function.Injective l)
    (π : Equiv.Perm ℕ) :
    Function.extend l b 0 ∘ π = Function.extend (π.symm ∘ l) b 0 := by
  have heq := hl.extend_comp π.symm.injective b (0 : ℕ → ℝ)
  funext i
  simpa [Function.comp_def, Pi.zero_def] using (congrFun heq i).symm

/-- A small family of permutations cannot rearrange every conditionally
convergent real series. -/
theorem not_isRearranging_of_cardinal_lt_boundingNumber
    (P : Set (Equiv.Perm ℕ)) (hP : #P < boundingNumber) : ¬ IsRearranging P := by
  classical
  obtain ⟨l, hl, horder⟩ := exists_common_eventually_ordered_subsequence P hP
  let b : ConditionalSeries := Classical.choice conditionalSeries_nonempty
  have hb : Tendsto (partialSum b.term) atTop (𝓝 b.sum) :=
    hasSum_conditional_iff.mp b.converges
  let a : ConditionalSeries := {
    term := Function.extend l b.term 0
    sum := b.sum
    converges := hasSum_conditional_iff.mpr
      (tendsto_partialSum_extend b.term l hl.injective 0
        (fun _ _ _ hnm ↦ hl hnm) b.sum hb)
    not_absolute := not_summable_abs_extend b.term l hl.injective b.not_absolute }
  apply not_isRearranging_of_preserves a
  intro π hπ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (horder π hπ)
  apply hasSum_conditional_iff.mpr
  change Tendsto (partialSum (Function.extend l b.term 0 ∘ π)) atTop (𝓝 b.sum)
  rw [extend_comp_perm b.term l hl.injective π]
  exact tendsto_partialSum_extend b.term (π.symm ∘ l)
    (π.symm.injective.comp hl.injective) N hN b.sum hb

/-- Every rearranging family has cardinality at least the bounding number. -/
theorem boundingNumber_le_cardinal_of_isRearranging
    {P : Set (Equiv.Perm ℕ)} (hP : IsRearranging P) : boundingNumber ≤ #P := by
  by_contra h
  exact not_isRearranging_of_cardinal_lt_boundingNumber P (lt_of_not_ge h) hP

/-- In particular, every rearranging family is infinite. -/
theorem aleph0_le_cardinal_of_isRearranging
    {P : Set (Equiv.Perm ℕ)} (hP : IsRearranging P) : ℵ₀ ≤ #P :=
  aleph0_lt_boundingNumber.le.trans (boundingNumber_le_cardinal_of_isRearranging hP)

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
