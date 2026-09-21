/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.InfinityOne

/-! # AEEq -/

open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section


/-!
# A.E. Invariance for Chapter 2.5 Homogenization Error

This file proves the public basic properties of the homogenization error
`\mathcal E_{s,\infty,1}` from Sec. 2.5.
-/

/-- The normalized one-cube block-response value set depends only on the
coefficient family modulo a.e. equality on each triadic cube. -/
theorem normalizedBlockResponseValueSet_eq_ofAEEq {d : ℕ} [NeZero d]
    {a b : TriadicCoeffFamily d} (h : TriadicCoeffFamily.AEEq a b)
    (Q : TriadicCube d) (a0 : Mat d) :
    normalizedBlockResponseValueSet Q a a0 =
      normalizedBlockResponseValueSet Q b a0 := by
  unfold normalizedBlockResponseValueSet
  ext m
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    rw [doubledResponseJ_eq_ofAEEq (h Q)]
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    rw [doubledResponseJ_eq_ofAEEq (h Q)]

/-- The normalized one-cube block-response maximum is a.e.-representative
invariant. -/
theorem normalizedBlockResponseMax_eq_ofAEEq {d : ℕ} [NeZero d]
    {a b : TriadicCoeffFamily d} (h : TriadicCoeffFamily.AEEq a b)
    (Q : TriadicCube d) (a0 : Mat d) :
    normalizedBlockResponseMax Q a a0 =
      normalizedBlockResponseMax Q b a0 := by
  unfold normalizedBlockResponseMax
  rw [normalizedBlockResponseValueSet_eq_ofAEEq h Q a0]

/-- The descendant normalized block-response maximum is a.e.-representative
invariant. -/
theorem maxDescendantNormalizedBlockResponseAtScale_eq_ofAEEq
    {d : ℕ} [NeZero d] {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.AEEq a b) (Q : TriadicCube d) (k : ℤ)
    (a0 : Mat d) :
    maxDescendantNormalizedBlockResponseAtScale Q k a a0 =
      maxDescendantNormalizedBlockResponseAtScale Q k b a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale
  exact finsetSupReal_congr _ fun R _ =>
    normalizedBlockResponseMax_eq_ofAEEq h R a0

/-- The scale-level response aggregation in the homogenization error is
a.e.-representative invariant. -/
theorem scaleResponseAtScale_eq_ofAEEq {d : ℕ} [NeZero d]
    {a b : TriadicCoeffFamily d} (h : TriadicCoeffFamily.AEEq a b)
    (Q : TriadicCube d) (k : ℤ) (p : MultiscaleExponent) (a0 : Mat d) :
    scaleResponseAtScale Q k p a a0 =
      scaleResponseAtScale Q k p b a0 := by
  cases p with
  | finite p =>
      unfold scaleResponseAtScale finsetAverageReal
      change
        Real.rpow
            (((descendantsAtScale Q k).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtScale Q k,
                Real.rpow (normalizedBlockResponseMax R a a0) (p / 2))
            (1 / p) =
          Real.rpow
            (((descendantsAtScale Q k).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtScale Q k,
                Real.rpow (normalizedBlockResponseMax R b a0) (p / 2))
            (1 / p)
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro R _hR
      rw [normalizedBlockResponseMax_eq_ofAEEq h R a0]
  | infinity =>
      unfold scaleResponseAtScale
      rw [maxDescendantNormalizedBlockResponseAtScale_eq_ofAEEq h Q k a0]

/-- The finite-`q` multiscale homogenization error is a.e.-representative
invariant. -/
theorem HomogenizationErrorFinite_eq_ofAEEq {d : ℕ} [NeZero d]
    {a b : TriadicCoeffFamily d} (h : TriadicCoeffFamily.AEEq a b)
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (p : MultiscaleExponent)
    (q : ℝ) (a0 : Mat d) :
    HomogenizationErrorFinite Q n s p q a a0 =
      HomogenizationErrorFinite Q n s p q b a0 := by
  unfold HomogenizationErrorFinite
  congr 1
  apply tsum_congr
  intro l
  rw [scaleResponseAtScale_eq_ofAEEq h Q (n - (l : ℤ)) p a0]

/-- The endpoint-`q` multiscale homogenization error is a.e.-representative
invariant. -/
theorem HomogenizationErrorInfinity_eq_ofAEEq {d : ℕ} [NeZero d]
    {a b : TriadicCoeffFamily d} (h : TriadicCoeffFamily.AEEq a b)
    (Q : TriadicCube d) (n : ℤ) (s : ℝ) (p : MultiscaleExponent)
    (a0 : Mat d) :
    HomogenizationErrorInfinity Q n s p a a0 =
      HomogenizationErrorInfinity Q n s p b a0 := by
  unfold HomogenizationErrorInfinity
  refine congrArg sSup ?_
  ext m
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨l, ?_⟩
    rw [scaleResponseAtScale_eq_ofAEEq h Q (n - (l : ℤ)) p a0]
  · rintro ⟨l, rfl⟩
    refine ⟨l, ?_⟩
    rw [scaleResponseAtScale_eq_ofAEEq h Q (n - (l : ℤ)) p a0]

/-- The multiscale homogenization error is a.e.-representative invariant. -/
theorem HomogenizationError_eq_ofAEEq {d : ℕ} [NeZero d]
    {a b : TriadicCoeffFamily d} (h : TriadicCoeffFamily.AEEq a b)
    (Q : TriadicCube d) (n : ℤ) (s : ℝ)
    (p q : MultiscaleExponent) (a0 : Mat d) :
    HomogenizationError Q n s p q a a0 =
      HomogenizationError Q n s p q b a0 := by
  cases q with
  | finite q =>
      exact HomogenizationErrorFinite_eq_ofAEEq h Q n s p q a0
  | infinity =>
      exact HomogenizationErrorInfinity_eq_ofAEEq h Q n s p a0

/-- The untruncated cube homogenization error is a.e.-representative
invariant. -/
theorem HomogenizationErrorOnCube_eq_ofAEEq {d : ℕ} [NeZero d]
    {a b : TriadicCoeffFamily d} (h : TriadicCoeffFamily.AEEq a b)
    (Q : TriadicCube d) (s : ℝ) (p q : MultiscaleExponent) (a0 : Mat d) :
    HomogenizationErrorOnCube Q s p q a a0 =
      HomogenizationErrorOnCube Q s p q b a0 :=
  HomogenizationError_eq_ofAEEq h Q Q.scale s p q a0

end

end Ch02
end Book
end Homogenization
