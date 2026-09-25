/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup
/-!
# Normality of lower ramification groups

Every level of the lower ramification filtration is normal in the
decomposition group: conjugation preserves the maximal-ideal powers that
define the filtration.
-/

@[expose] public section

namespace ClassFieldTheory

universe u v

/-- Each lower ramification group is normal in the decomposition group. -/
theorem lowerRamificationGroup_normal
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    (lowerRamificationGroup K A n).Normal where
  conj_mem := by
    intro σ hσ γ
    change ∀ x : A,
      (γ * σ * γ⁻¹) • x - x ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1)
    intro x
    let e : A ≃+* A :=
      MulSemiringAction.toRingAut (A.decompositionSubgroup K) A γ
    have hmap :
        e (σ • (γ⁻¹ • x) - (γ⁻¹ • x)) ∈
          ((IsLocalRing.maximalIdeal A) ^ (n + 1)).map e :=
      Ideal.mem_map_of_mem e (hσ (γ⁻¹ • x))
    have hstable :
        γ • (σ • (γ⁻¹ • x) - (γ⁻¹ • x)) ∈
          (IsLocalRing.maximalIdeal A) ^ (n + 1) := by
      change γ • (σ • (γ⁻¹ • x) - (γ⁻¹ • x)) ∈
        ((IsLocalRing.maximalIdeal A) ^ (n + 1)).map e at hmap
      rwa [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal] at hmap
    simpa only [smul_sub, mul_smul, smul_inv_smul] using hstable

end ClassFieldTheory
