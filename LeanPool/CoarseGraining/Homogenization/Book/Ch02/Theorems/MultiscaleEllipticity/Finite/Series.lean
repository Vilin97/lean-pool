/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Representatives

/-! # Series -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

/-!
# Finite-exponent multiscale ellipticity: series identities
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

theorem LambdaSqFinite_series_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s q : ℝ) (a : TriadicCoeffFamily d)
    (_hq : 0 ≤ q) (hsq : 0 ≤ s * q) :
    0 ≤
      ∑' n : ℕ,
        geometricWeight s q n *
          Real.rpow
            (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2) := by
  refine tsum_nonneg ?_
  intro n
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  refine mul_nonneg ?_ ?_
  · simpa [geometricWeight_eq_old] using Homogenization.geometricWeight_nonneg n hsq
  · exact Real.rpow_nonneg
      (maxDescendantBMatrixNormAtScale_nonneg Q (sub_le_self _ hn) a) _

theorem lambdaSqFinite_series_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s q : ℝ) (a : TriadicCoeffFamily d)
    (_hq : 0 ≤ q) (hsq : 0 ≤ s * q) :
    0 ≤
      ∑' n : ℕ,
        geometricWeight s q n *
          Real.rpow
            (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2) := by
  refine tsum_nonneg ?_
  intro n
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  refine mul_nonneg ?_ ?_
  · simpa [geometricWeight_eq_old] using Homogenization.geometricWeight_nonneg n hsq
  · exact Real.rpow_nonneg
      (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
        (sub_le_self _ hn) a) _

theorem LambdaSqFinite_rpow_q_div_two_eq_tsum {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s q : ℝ) (a : TriadicCoeffFamily d)
    (hq : 0 < q) (hsq : 0 ≤ s * q) :
    Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) =
      ∑' n : ℕ,
        geometricWeight s q n *
          Real.rpow
            (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2) := by
  rw [LambdaSq_finite]
  let S : ℝ :=
    ∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow
          (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact LambdaSqFinite_series_nonneg Q s q a hq.le hsq
  have hmul : (2 / q : ℝ) * (q / 2) = 1 := by
    field_simp [hq.ne']
  calc
    Real.rpow (Real.rpow S (2 / q)) (q / 2) =
        Real.rpow S ((2 / q) * (q / 2)) := by
          symm
          exact Real.rpow_mul hS_nonneg (2 / q : ℝ) (q / 2)
    _ = Real.rpow S 1 := by simp [hmul]
    _ = S := by exact Real.rpow_one S
    _ =
        ∑' n : ℕ,
          geometricWeight s q n *
            Real.rpow
              (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (q / 2) := by
          rfl

theorem lambdaSqFinite_rpow_neg_q_div_two_eq_tsum {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s q : ℝ) (a : TriadicCoeffFamily d)
    (hq : 0 < q) (hsq : 0 ≤ s * q) :
    Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) =
      ∑' n : ℕ,
        geometricWeight s q n *
          Real.rpow
            (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2) := by
  rw [lambdaSq_finite]
  let S : ℝ :=
    ∑' n : ℕ,
      geometricWeight s q n *
        Real.rpow
          (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          (q / 2)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact lambdaSqFinite_series_nonneg Q s q a hq.le hsq
  have hmul : (-(2 / q) : ℝ) * (-q / 2) = 1 := by
    field_simp [hq.ne']
  calc
    Real.rpow (Real.rpow S (-(2 / q))) (-q / 2) =
        Real.rpow S ((-(2 / q)) * (-q / 2)) := by
          symm
          exact Real.rpow_mul hS_nonneg (-(2 / q) : ℝ) (-q / 2)
    _ = Real.rpow S 1 := by simp [hmul]
    _ = S := by exact Real.rpow_one S
    _ =
        ∑' n : ℕ,
          geometricWeight s q n *
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (q / 2) := by
          rfl

end

end Ch02
end Book
end Homogenization
