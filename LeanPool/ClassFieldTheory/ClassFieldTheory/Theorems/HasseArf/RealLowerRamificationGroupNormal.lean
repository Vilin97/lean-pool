/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HasseArf.RealLowerRamificationGroup
/-!
# Normality of real lower ramification groups

Conjugation preserves powers of the maximal ideal, so the real lower groups
are normal in the decomposition group.
-/

namespace ClassFieldTheory

universe u v

/-- Each real lower ramification group is normal in its decomposition group. -/
theorem realLowerRamificationGroup_normal
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (s : ℝ) :
    (realLowerRamificationGroup K A s).Normal where
  conj_mem := by
    intro σ hσ γ
    change ∀ x : A,
      (γ * σ * γ⁻¹) • x - x ∈
        (IsLocalRing.maximalIdeal A) ^ (Int.ceil (s + 1)).toNat
    intro x
    let e : A ≃+* A :=
      MulSemiringAction.toRingAut (A.decompositionSubgroup K) A γ
    have hmap :
        e (σ • (γ⁻¹ • x) - (γ⁻¹ • x)) ∈
          ((IsLocalRing.maximalIdeal A) ^ (Int.ceil (s + 1)).toNat).map e :=
      Ideal.mem_map_of_mem e (hσ (γ⁻¹ • x))
    have hstable :
        γ • (σ • (γ⁻¹ • x) - (γ⁻¹ • x)) ∈
          (IsLocalRing.maximalIdeal A) ^ (Int.ceil (s + 1)).toNat := by
      change γ • (σ • (γ⁻¹ • x) - (γ⁻¹ • x)) ∈
        ((IsLocalRing.maximalIdeal A) ^ (Int.ceil (s + 1)).toNat).map e at hmap
      rwa [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal] at hmap
    simpa only [smul_sub, mul_smul, smul_inv_smul] using hstable

end ClassFieldTheory
