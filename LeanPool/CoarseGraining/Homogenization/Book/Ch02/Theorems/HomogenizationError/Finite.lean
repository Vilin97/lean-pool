/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-! # Finite -/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-!
# Finite exponent identities for the homogenization error

This file records the finite-`q` algebra for the public homogenization error.
The first downstream use is the `p = infinity`, `q = 2` route: after squaring,
the square roots in the scale response disappear and `\mathcal E` is exactly
the geometrically weighted sum of the normalized block-response maxima.
-/

theorem scaleResponseAtScale_infinity_sq_eq
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : TriadicCoeffFamily d) (a0 : Mat d) :
    (scaleResponseAtScale Q k .infinity a a0) ^ 2 =
      maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  simpa [scaleResponseAtScale_infinity_eq, Real.sqrt_eq_rpow] using
    Real.sq_sqrt (maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk a a0)

theorem scaleResponseAtScale_infinity_rpow_two_eq
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (a : TriadicCoeffFamily d) (a0 : Mat d) :
    Real.rpow (scaleResponseAtScale Q k .infinity a a0) (2 : ℝ) =
      maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  simpa [Real.rpow_two] using scaleResponseAtScale_infinity_sq_eq Q hk a a0

theorem homogenizationErrorFinite_infinity_two_sq_eq_tsum
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    {s : ℝ} (hs : 0 < s) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    (HomogenizationErrorFinite Q n s .infinity 2 a a0) ^ 2 =
      ∑' l : ℕ,
        geometricWeight s 2 l *
          maxDescendantNormalizedBlockResponseAtScale Q (n - (l : ℤ)) a a0 := by
  let S : ℝ :=
    ∑' l : ℕ,
      geometricWeight s 2 l *
        maxDescendantNormalizedBlockResponseAtScale Q (n - (l : ℤ)) a a0
  have hterm :
      (fun l : ℕ =>
          geometricWeight s 2 l *
            Real.rpow (scaleResponseAtScale Q (n - (l : ℤ)) .infinity a a0) 2) =
        fun l : ℕ =>
          geometricWeight s 2 l *
            maxDescendantNormalizedBlockResponseAtScale Q (n - (l : ℤ)) a a0 := by
    funext l
    have hk : n - (l : ℤ) ≤ Q.scale := by
      exact (sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn
    rw [scaleResponseAtScale_infinity_rpow_two_eq Q hk a a0]
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    refine tsum_nonneg ?_
    intro l
    refine mul_nonneg ?_ ?_
    · simpa [geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := s) (q := 2) l
          (by positivity : 0 ≤ s * (2 : ℝ)))
    · have hk : n - (l : ℤ) ≤ Q.scale := by
        exact (sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn
      exact maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk a a0
  unfold HomogenizationErrorFinite
  rw [hterm]
  change Real.rpow S (1 / 2 : ℝ) ^ 2 = S
  simpa [Real.sqrt_eq_rpow] using Real.sq_sqrt hS_nonneg

theorem homogenizationErrorOnCube_infinity_two_sq_eq_tsum
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    (HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0) ^ 2 =
      ∑' l : ℕ,
        geometricWeight s 2 l *
          maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0 := by
  simpa [HomogenizationErrorOnCube, HomogenizationError] using
    homogenizationErrorFinite_infinity_two_sq_eq_tsum
      (Q := Q) (n := Q.scale) le_rfl hs a a0

end

end Ch02
end Book
end Homogenization
