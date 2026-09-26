/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Examples.DegreeTwoPrime
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.DegreeTwoExample

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Primality.Primality

/-! # Degree Two Prime Proof -/

public noncomputable section

namespace ConwayRefinement.Standalone.Hahn.DegreeTwoExample

open PommersheimShahriari.DegreeTwoExample

universe u

variable {K : Type u} [Field K]

private theorem nonpositiveSeries_eq :
    NonpositiveSeries K = HahnSeries.nonpositiveSubring ℝ K := by
  ext x
  rfl

private theorem coeff_eq_one_of_isDisplayedExponent {r : ℝ} (hr : IsDisplayedExponent r) :
    ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : HahnSeries ℝ K).coeff r = 1 := by
  rcases hr with rfl | ⟨m, n, rfl⟩
  · exact degreeTwoWithConstant_coeff_zero
  · simpa only [exponent, degreeTwoExponentEmbedding_apply,
      degreeTwoExponentPair_apply] using
      degreeTwoWithConstant_coeff_embedding (K := K) m n

private theorem coeff_eq_zero_of_not_isDisplayedExponent {r : ℝ}
    (hr : ¬ IsDisplayedExponent r) :
    ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : HahnSeries ℝ K).coeff r = 0 := by
  apply degreeTwoWithConstant_coeff_eq_zero
  · rintro ⟨p, rfl⟩
    rcases p with ⟨m, n⟩
    apply hr
    exact Or.inr ⟨m, n, by
      change degreeTwoExponentEmbedding (toLex (m, n)) = exponent m n
      rw [degreeTwoExponentEmbedding_apply, degreeTwoExponentPair_apply]
      rfl⟩
  · intro hzero
    exact hr (Or.inl hzero)

namespace ExistsPrime

/-- The displayed coefficient-one Hahn series is prime. -/
theorem proof (K : Type u) [Field K] : ExistsPrime K := by
  intro hK
  let : CharZero K := hK
  let E : NonpositiveSeries K ≃+* HahnSeries.Nonpositive ℝ K :=
    RingEquiv.subringCongr nonpositiveSeries_eq
  let x : NonpositiveSeries K := E.symm (degreeTwoWithConstant (K := K))
  refine ⟨x, ?_, ?_, ?_⟩
  · intro r hr
    rw [show (x : HahnSeries ℝ K) =
      ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : HahnSeries ℝ K) by rfl]
    exact coeff_eq_one_of_isDisplayedExponent hr
  · intro r hr
    rw [show (x : HahnSeries ℝ K) =
      ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : HahnSeries ℝ K) by rfl]
    exact coeff_eq_zero_of_not_isDisplayedExponent hr
  · apply (MulEquiv.prime_iff E.toMulEquiv).mp
    change Prime (degreeTwoWithConstant (K := K))
    exact Berarducci.prime_of_irreducible degreeTwoWithConstant_irreducible

end ExistsPrime

end ConwayRefinement.Standalone.Hahn.DegreeTwoExample
