/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.NormalPolynomialBound
public import LeanPool.OperatorTheory.Operator.Crouzeix.SpectralSetMonotone
public import LeanPool.OperatorTheory.Operator.NumericalRange.RadiusAffine

/-!
# Compact supersets of the closed numerical range

The Crouzeix--Palencia estimate, and its normal-operator constant-one
improvement, persist on every compact set containing the closed numerical
range.
-/

@[expose] public section

open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Every compact superset of the closed numerical range is a polynomial
spectral set with the Crouzeix--Palencia constant. -/
theorem isKPolynomialSpectralSet_of_closure_numericalRange_subset
    (A : E →L[ℂ] E) {K : Set ℂ} (hK : IsCompact K)
    (hsub : closure (numericalRange A) ⊆ K) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) K :=
  (crouzeix_palencia A).mono_set (by positivity) hsub hK

/-- For a normal operator, every compact superset of the closed numerical
range is a constant-one polynomial spectral set. -/
theorem isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset
    (A : E →L[ℂ] E) [IsStarNormal A]
    {K : Set ℂ} (hK : IsCompact K)
    (hsub : closure (numericalRange A) ⊆ K) :
    IsPolynomialSpectralSet A K :=
  (isPolynomialSpectralSet_closure_numericalRange_of_isStarNormal A).mono_set
    hsub hK

/-- The closed disk centered at zero with radius `w(A)` is a polynomial
spectral set with the Crouzeix--Palencia constant. -/
theorem isKPolynomialSpectralSet_closedBall_numericalRadius
    (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (Metric.closedBall 0 (numericalRadius A)) :=
  isKPolynomialSpectralSet_of_closure_numericalRange_subset A
    (isCompact_closedBall (0 : ℂ) (numericalRadius A))
    (closure_numericalRange_subset_closedBall_numericalRadius A)

/-- For a normal operator, the numerical-radius disk is a constant-one
polynomial spectral set. -/
theorem isPolynomialSpectralSet_closedBall_numericalRadius_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] :
    IsPolynomialSpectralSet A
      (Metric.closedBall 0 (numericalRadius A)) :=
  isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset A
    (isCompact_closedBall (0 : ℂ) (numericalRadius A))
    (closure_numericalRange_subset_closedBall_numericalRadius A)

/-- Every centered closed disk whose radius dominates `w(A)` is a polynomial
spectral set with the Crouzeix--Palencia constant. -/
theorem isKPolynomialSpectralSet_closedBall_of_numericalRadius_le
    (A : E →L[ℂ] E) {R : ℝ} (hR : numericalRadius A ≤ R) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (Metric.closedBall 0 R) :=
  (isKPolynomialSpectralSet_closedBall_numericalRadius A).mono_set
    (by positivity) (Metric.closedBall_subset_closedBall hR)
    (isCompact_closedBall (0 : ℂ) R)

/-- For a normal operator, every centered closed disk whose radius dominates
`w(A)` is a constant-one polynomial spectral set. -/
theorem isPolynomialSpectralSet_closedBall_of_isStarNormal_of_numericalRadius_le
    (A : E →L[ℂ] E) [IsStarNormal A] {R : ℝ}
    (hR : numericalRadius A ≤ R) :
    IsPolynomialSpectralSet A (Metric.closedBall 0 R) :=
  (isPolynomialSpectralSet_closedBall_numericalRadius_of_isStarNormal A).mono_set
    (Metric.closedBall_subset_closedBall hR) (isCompact_closedBall (0 : ℂ) R)

/-- The disk centered at `c` with radius `w(A-cI)` is a polynomial spectral
set with the Crouzeix--Palencia constant. -/
theorem isKPolynomialSpectralSet_closedBall_centered_numericalRadius
    (A : E →L[ℂ] E) (c : ℂ) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (Metric.closedBall c (numericalRadius (A - c • 1))) :=
  isKPolynomialSpectralSet_of_closure_numericalRange_subset A
    (isCompact_closedBall c (numericalRadius (A - c • 1)))
    (closure_numericalRange_subset_closedBall_centered_numericalRadius A c)

/-- For a normal operator, the disk centered at `c` with radius `w(A-cI)` is
a constant-one polynomial spectral set. -/
theorem
    isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) :
    IsPolynomialSpectralSet A
      (Metric.closedBall c (numericalRadius (A - c • 1))) :=
  isPolynomialSpectralSet_of_isStarNormal_of_closure_numericalRange_subset A
    (isCompact_closedBall c (numericalRadius (A - c • 1)))
    (closure_numericalRange_subset_closedBall_centered_numericalRadius A c)

/-- Every disk whose radius dominates `w(A-cI)` is a polynomial spectral set
with the Crouzeix--Palencia constant. -/
theorem isKPolynomialSpectralSet_closedBall_of_centered_numericalRadius_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (Metric.closedBall c R) :=
  (isKPolynomialSpectralSet_closedBall_centered_numericalRadius A c).mono_set
    (by positivity) (Metric.closedBall_subset_closedBall hR)
    (isCompact_closedBall c R)

/-- For a normal operator, every disk whose radius dominates `w(A-cI)` is a
constant-one polynomial spectral set. -/
theorem
    isPolynomialSpectralSet_closedBall_of_isStarNormal_of_centered_numericalRadius_le
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) :
    IsPolynomialSpectralSet A (Metric.closedBall c R) :=
  (isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal
    A c).mono_set (Metric.closedBall_subset_closedBall hR)
      (isCompact_closedBall c R)

/-- Direct polynomial form of the Crouzeix--Palencia bound on any disk whose
radius dominates `w(A-cI)`. -/
theorem
    norm_aeval_le_one_add_sqrt_two_mul_polynomialNorm_closedBall_of_centered_numericalRadius_le
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤
      (1 + Real.sqrt 2) * polynomialSupNorm p (Metric.closedBall c R) :=
  (isKPolynomialSpectralSet_closedBall_of_centered_numericalRadius_le
    A c hR).2 p

/-- Direct constant-one polynomial bound for a normal operator on any disk
whose radius dominates `w(A-cI)`. -/
theorem
    norm_aeval_le_polynomialSupNorm_closedBall_of_isStarNormal_of_centered_numericalRadius_le
    (A : E →L[ℂ] E) [IsStarNormal A] (c : ℂ) {R : ℝ}
    (hR : numericalRadius (A - c • 1) ≤ R) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤ polynomialSupNorm p (Metric.closedBall c R) := by
  simpa only [one_mul] using
    (isPolynomialSpectralSet_closedBall_of_isStarNormal_of_centered_numericalRadius_le
      A c hR).2 p

/-- A nontrivial Hilbert space admits a globally minimal centered
numerical-radius disk, and that disk is a polynomial spectral set with the
Crouzeix--Palencia constant. -/
theorem exists_minimal_centered_numericalRadius_isKPolynomialSpectralSet
    [Nontrivial E] (A : E →L[ℂ] E) :
    ∃ c : ℂ,
      (∀ d : ℂ,
        numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1)) ∧
      IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
        (Metric.closedBall c (numericalRadius (A - c • 1))) := by
  obtain ⟨c, hc⟩ := exists_center_minimizing_numericalRadius A
  exact ⟨c, hc, isKPolynomialSpectralSet_closedBall_centered_numericalRadius A c⟩

/-- For a normal operator, a globally minimal centered numerical-radius disk
is a constant-one polynomial spectral set. -/
theorem
    exists_minimal_centered_numericalRadius_isPolynomialSpectralSet_of_isStarNormal
    [Nontrivial E] (A : E →L[ℂ] E) [IsStarNormal A] :
    ∃ c : ℂ,
      (∀ d : ℂ,
        numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1)) ∧
      IsPolynomialSpectralSet A
        (Metric.closedBall c (numericalRadius (A - c • 1))) := by
  obtain ⟨c, hc⟩ := exists_center_minimizing_numericalRadius A
  exact ⟨c, hc,
    isPolynomialSpectralSet_closedBall_centered_numericalRadius_of_isStarNormal A c⟩

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
