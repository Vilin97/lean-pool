/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.RingTheory.Valuation.RamificationGroup
/-!
# Lower ramification groups
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

private lemma smul_mem_maximalIdeal_pow
    (A : ValuationSubring L) (n : ℕ)
    (σ : A.decompositionSubgroup K) {x : A}
    (hx : x ∈ (IsLocalRing.maximalIdeal A) ^ n) :
    σ • x ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  let e : A ≃+* A :=
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) A σ
  have hx' : e x ∈ ((IsLocalRing.maximalIdeal A) ^ n).map e :=
    Ideal.mem_map_of_mem e hx
  rwa [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal] at hx'

/-- The `n`-th ramification group in lower numbering for the valuation
subring `A`.  Its elements act trivially on `A / m^(n + 1)`. -/
def lowerRamificationGroup (A : ValuationSubring L) (n : ℕ) :
    Subgroup (A.decompositionSubgroup K) where
  carrier := {σ | ∀ x : A,
    σ • x - x ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1)}
  one_mem' := by simp
  mul_mem' := by
    intro σ τ hσ hτ x
    have hτ' := smul_mem_maximalIdeal_pow K A (n + 1) σ (hτ x)
    have hsum :=
      (IsLocalRing.maximalIdeal A ^ (n + 1)).add_mem hτ' (hσ x)
    simpa [mul_smul, smul_sub, sub_eq_add_neg, add_assoc] using hsum
  inv_mem' := by
    intro σ hσ x
    simpa [smul_smul] using
      (IsLocalRing.maximalIdeal A ^ (n + 1)).neg_mem (hσ (σ⁻¹ • x))

end ClassFieldTheory
