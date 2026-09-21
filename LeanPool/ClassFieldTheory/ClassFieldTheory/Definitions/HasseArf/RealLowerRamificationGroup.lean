/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Basic.Real.Basic
/-!
# Real-index lower ramification groups

The ideal exponent at a real index `s` is `max(0, ceil(s + 1))`.
Consequently, indices at or below `-1` give the whole decomposition group,
and natural indices recover the usual `m^(n+1)` displacement condition.
-/

noncomputable section

namespace ClassFieldTheory

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

private lemma smul_mem_maximalIdeal_pow_real
    (A : ValuationSubring L) (k : ℕ)
    (σ : A.decompositionSubgroup K) {x : A}
    (hx : x ∈ (IsLocalRing.maximalIdeal A) ^ k) :
    σ • x ∈ (IsLocalRing.maximalIdeal A) ^ k := by
  let e : A ≃+* A :=
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) A σ
  have hx' : e x ∈ ((IsLocalRing.maximalIdeal A) ^ k).map e :=
    Ideal.mem_map_of_mem e hx
  rwa [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal] at hx'

/-- The real-index lower ramification group of a valuation subring. Its
elements act trivially modulo `m ^ max(0, ceil(s + 1))`. -/
def realLowerRamificationGroup (A : ValuationSubring L) (s : ℝ) :
    Subgroup (A.decompositionSubgroup K) where
  carrier := {σ | ∀ x : A,
    σ • x - x ∈
      (IsLocalRing.maximalIdeal A) ^ (Int.ceil (s + 1)).toNat}
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ x
    have hτ' := smul_mem_maximalIdeal_pow_real K A
      (Int.ceil (s + 1)).toNat σ (hτ x)
    have hsum :=
      (IsLocalRing.maximalIdeal A ^ (Int.ceil (s + 1)).toNat).add_mem
        hτ' (hσ x)
    simpa [mul_smul, smul_sub, sub_eq_add_neg, add_assoc] using hsum
  inv_mem' := by
    intro σ hσ x
    simpa [smul_smul] using
      (IsLocalRing.maximalIdeal A ^ (Int.ceil (s + 1)).toNat).neg_mem
        (hσ (σ⁻¹ • x))

/-- At or below index `-1`, the real lower ramification group is the full
decomposition group. -/
theorem realLowerRamificationGroup_eq_top_of_le_neg_one
    (A : ValuationSubring L) {s : ℝ} (hs : s ≤ -1) :
    realLowerRamificationGroup K A s = ⊤ := by
  have hzero : (Int.ceil (s + 1)).toNat = 0 := by
    rw [Int.toNat_eq_zero]
    exact Int.ceil_nonpos.mpr (by linarith)
  apply (Subgroup.eq_top_iff' _).2
  intro σ
  change ∀ x : A,
    σ • x - x ∈ (IsLocalRing.maximalIdeal A) ^ (Int.ceil (s + 1)).toNat
  intro x
  rw [hzero, pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

end ClassFieldTheory
