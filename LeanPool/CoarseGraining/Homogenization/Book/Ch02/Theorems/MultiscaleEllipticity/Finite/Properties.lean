/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.DiscountBounds

/-! # Properties -/

namespace Homogenization
namespace Book
namespace Ch02

/-!
# Finite-exponent multiscale ellipticity: public properties
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

theorem LambdaSq_finite_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) :
    0 ≤ LambdaSq Q s (.finite q) a := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  rw [LambdaSq_finite]
  exact Real.rpow_nonneg
    (LambdaSqFinite_series_nonneg Q s q a hq0 (mul_nonneg hs.le hq0)) _

theorem lambdaSq_finite_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) :
    0 ≤ lambdaSq Q s (.finite q) a := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  rw [lambdaSq_finite]
  exact Real.rpow_nonneg
    (lambdaSqFinite_series_nonneg Q s q a hq0 (mul_nonneg hs.le hq0)) _

/-- The q=1 upper operator-norm series is summable for every Ch2 triadic
coefficient family. -/
theorem summable_geometricWeight_one_mul_maxDescendantBMatrixNormAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) := by
  let Apw : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let C : ℝ :=
    4 * (Fintype.card (Fin d) : ℝ) * (a.coeffOn Q).lam⁻¹ *
      (a.coeffOn Q).Lam ^ 2
  have hEll :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet Q) Apw := by
    simpa [Apw] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q Apw := by
    simpa [Apw] using
      pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  refine
    Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := 1) (C := C) (by simpa using hs) ?_ ?_
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    exact maxDescendantBMatrixNormAtScale_nonneg Q (sub_le_self Q.scale hn) a
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hmatrix_le :=
      maxDescendantBMatrixNormAtScale_le_maxDescendantBBlockNormAtScale
        (a := a) Q (sub_le_self Q.scale hn)
    have hblock_le :
        maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) Apw ≤ C := by
      simpa [Apw, C] using
        maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
          (Q := Q) (a := Apw) hEll hData n
    exact hmatrix_le.trans hblock_le

/-- The q=1 lower inverse operator-norm series is summable for every Ch2
triadic coefficient family. -/
theorem summable_geometricWeight_one_mul_maxDescendantSigmaStarInvMatrixNormAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ =>
      geometricWeight s 1 n *
        maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) := by
  let Apw : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  let C : ℝ :=
    4 * (Fintype.card (Fin d) : ℝ) * (a.coeffOn Q).lam⁻¹
  have hEll :
      IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
        (openCubeSet Q) Apw := by
    simpa [Apw] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q Apw := by
    simpa [Apw] using
      pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  refine
    Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := 1) (C := C) (by simpa using hs) ?_ ?_
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    exact maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self Q.scale hn) a
  · intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hmatrix_le :=
      maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
        (a := a) Q (sub_le_self Q.scale hn)
    have hblock_le :
        maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) Apw ≤ C := by
      simpa [Apw, C] using
        maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
          (Q := Q) (a := Apw) hEll hData n
    exact hmatrix_le.trans hblock_le

private theorem rpow_two_tsum_weighted_rpow_half_le_tsum_weighted
    {w H : ℕ → ℝ}
    (hw_nonneg : ∀ n, 0 ≤ w n)
    (hH_nonneg : ∀ n, 0 ≤ H n)
    (hw_sum : Summable w)
    (hw_tsum_le_one : (∑' n : ℕ, w n) ≤ 1)
    (hWH_sum : Summable (fun n : ℕ => w n * H n))
    (hWsqrt_sum : Summable (fun n : ℕ => w n * Real.rpow (H n) (1 / 2 : ℝ))) :
    Real.rpow (∑' n : ℕ, w n * Real.rpow (H n) (1 / 2 : ℝ)) (2 : ℝ) ≤
      ∑' n : ℕ, w n * H n := by
  classical
  let sqrtH : ℕ → ℝ := fun n => Real.rpow (H n) (1 / 2 : ℝ)
  let B : ℝ := ∑' n : ℕ, w n * H n
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact tsum_nonneg fun n => mul_nonneg (hw_nonneg n) (hH_nonneg n)
  have hfinite :
      ∀ s : Finset ℕ,
        ∑ n ∈ s, w n * sqrtH n ≤ Real.rpow B (1 / 2 : ℝ) := by
    intro s
    have hholder :
        ∑ n ∈ s, w n * sqrtH n ≤
          (∑ n ∈ s, w n) ^ (1 - (2 : ℝ)⁻¹) *
            (∑ n ∈ s, w n * sqrtH n ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ :=
      Real.inner_le_weight_mul_Lp_of_nonneg
        (s := s) (p := (2 : ℝ)) (w := w) (f := sqrtH)
        (by norm_num) hw_nonneg
        (fun n => Real.rpow_nonneg (hH_nonneg n) _)
    have hsquares :
        (∑ n ∈ s, w n * sqrtH n ^ (2 : ℝ)) =
          ∑ n ∈ s, w n * H n := by
      refine Finset.sum_congr rfl ?_
      intro n _hn
      have hsqrt_sq : sqrtH n ^ 2 = H n := by
        simpa [sqrtH] using
          Homogenization.sq_rpow_half_eq_self_of_nonneg (hH_nonneg n)
      have hsqrt_sq_rpow : sqrtH n ^ (2 : ℝ) = H n := by
        calc
          sqrtH n ^ (2 : ℝ) = sqrtH n ^ 2 := Real.rpow_natCast _ 2
          _ = H n := hsqrt_sq
      exact congrArg (fun x : ℝ => w n * x) hsqrt_sq_rpow
    have hsumw_nonneg : 0 ≤ ∑ n ∈ s, w n :=
      Finset.sum_nonneg fun n _hn => hw_nonneg n
    have hsumw_le_tsum : ∑ n ∈ s, w n ≤ ∑' n : ℕ, w n :=
      hw_sum.sum_le_tsum s fun n _hn => hw_nonneg n
    have hsumw_le_one : ∑ n ∈ s, w n ≤ 1 :=
      hsumw_le_tsum.trans hw_tsum_le_one
    have hsumw_rpow_le_one :
        (∑ n ∈ s, w n) ^ (1 / 2 : ℝ) ≤ 1 := by
      have hpow :=
        Real.rpow_le_rpow hsumw_nonneg hsumw_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      simpa using hpow
    have hsumWH_nonneg : 0 ≤ ∑ n ∈ s, w n * H n :=
      Finset.sum_nonneg fun n _hn => mul_nonneg (hw_nonneg n) (hH_nonneg n)
    have hsumWH_le_B : ∑ n ∈ s, w n * H n ≤ B := by
      dsimp [B]
      exact hWH_sum.sum_le_tsum s fun n _hn =>
        mul_nonneg (hw_nonneg n) (hH_nonneg n)
    have hsumWH_rpow_le_B :
        (∑ n ∈ s, w n * H n) ^ (1 / 2 : ℝ) ≤ Real.rpow B (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow hsumWH_nonneg hsumWH_le_B
        (by norm_num : 0 ≤ (1 / 2 : ℝ))
    calc
      ∑ n ∈ s, w n * sqrtH n
          ≤ (∑ n ∈ s, w n) ^ (1 / 2 : ℝ) *
              (∑ n ∈ s, w n * H n) ^ (1 / 2 : ℝ) := by
            have hleftExp : 1 - (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
            have hrightExp : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
            calc
              ∑ n ∈ s, w n * sqrtH n ≤
                  (∑ n ∈ s, w n) ^ (1 - (2 : ℝ)⁻¹) *
                    (∑ n ∈ s, w n * sqrtH n ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ :=
                    hholder
              _ = (∑ n ∈ s, w n) ^ (1 / 2 : ℝ) *
                    (∑ n ∈ s, w n * H n) ^ (1 / 2 : ℝ) := by
                    rw [hsquares, hleftExp, hrightExp]
      _ ≤ 1 * Real.rpow B (1 / 2 : ℝ) := by
            exact mul_le_mul hsumw_rpow_le_one hsumWH_rpow_le_B
              (Real.rpow_nonneg hsumWH_nonneg _) (by norm_num)
      _ = Real.rpow B (1 / 2 : ℝ) := by ring
  have hS_nonneg :
      0 ≤ ∑' n : ℕ, w n * Real.rpow (H n) (1 / 2 : ℝ) :=
    tsum_nonneg fun n =>
      mul_nonneg (hw_nonneg n) (Real.rpow_nonneg (hH_nonneg n) _)
  have hS_le :
      (∑' n : ℕ, w n * Real.rpow (H n) (1 / 2 : ℝ)) ≤
        Real.rpow B (1 / 2 : ℝ) := by
    have hfinite' :
        ∀ s : Finset ℕ,
          ∑ n ∈ s, w n * Real.rpow (H n) (1 / 2 : ℝ) ≤
            Real.rpow B (1 / 2 : ℝ) := by
      intro s
      simpa [sqrtH] using hfinite s
    exact hWsqrt_sum.tsum_le_of_sum_le hfinite'
  calc
    Real.rpow (∑' n : ℕ, w n * Real.rpow (H n) (1 / 2 : ℝ)) (2 : ℝ)
        = (∑' n : ℕ, w n * Real.rpow (H n) (1 / 2 : ℝ)) ^ 2 := by
          exact Real.rpow_natCast _ 2
    _ ≤ (Real.rpow B (1 / 2 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hS_nonneg hS_le 2
    _ = B := Homogenization.sq_rpow_half_eq_self_of_nonneg hB_nonneg

/-- Jensen upper bound for the q=1 Ch2 upper operator multiscale ellipticity.
The norm here is `Ch02.matrixNorm` through
`maxDescendantBMatrixNormAtScale`. -/
theorem LambdaSq_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    LambdaSq Q s (.finite 1) a ≤
      ∑' n : ℕ,
        geometricWeight s 1 n *
          maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
  have hNorm_sum :=
    summable_geometricWeight_one_mul_maxDescendantBMatrixNormAtScale Q a hs
  have hSqrt_sum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow
            (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) := by
    simpa using
      summable_B_series_pointwiseCoeffField Q a hs (by norm_num : (0 : ℝ) < 1)
  calc
    LambdaSq Q s (.finite 1) a =
        (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) ^ 2 := by
          symm
          exact Homogenization.sq_rpow_half_eq_self_of_nonneg
            (LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1))
    _ =
        (∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow
              (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) ^ 2 := by
          rw [LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 1 a
            (by norm_num : (0 : ℝ) < 1) (by positivity : 0 ≤ s * (1 : ℝ))]
    _ =
        Real.rpow
          (∑' n : ℕ,
            geometricWeight s 1 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) (2 : ℝ) := by
          exact (Real.rpow_natCast _ 2).symm
    _ ≤
        ∑' n : ℕ,
          geometricWeight s 1 n *
            maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
          rpow_two_tsum_weighted_rpow_half_le_tsum_weighted
            (w := fun n : ℕ => geometricWeight s 1 n)
            (H := fun n : ℕ =>
              maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (fun n => by
              simpa [geometricWeight_eq_old] using
                Homogenization.geometricWeight_nonneg n
                  (mul_nonneg hs.le (by norm_num : (0 : ℝ) ≤ 1)))
            (fun n =>
              have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
              maxDescendantBMatrixNormAtScale_nonneg Q (sub_le_self Q.scale hn) a)
            (by
              simpa [geometricWeight_eq_old] using
                Homogenization.summable_geometricWeight_one (s := s) hs)
            (by
              simpa [geometricWeight_eq_old] using
                (Homogenization.tsum_geometricWeight_one_eq_one (s := s) hs).le)
            hNorm_sum hSqrt_sum

/-- Jensen upper bound for the q=1 Ch2 lower inverse operator multiscale
ellipticity. The norm here is `Ch02.matrixNorm` through
`maxDescendantSigmaStarInvMatrixNormAtScale`. -/
theorem lambdaSq_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    (lambdaSq Q s (.finite 1) a)⁻¹ ≤
      ∑' n : ℕ,
        geometricWeight s 1 n *
          maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
  have hNorm_sum :=
    summable_geometricWeight_one_mul_maxDescendantSigmaStarInvMatrixNormAtScale Q a hs
  have hSqrt_sum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow
            (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) := by
    simpa using
      summable_sigmaStarInv_series_pointwiseCoeffField Q a hs
        (by norm_num : (0 : ℝ) < 1)
  calc
    (lambdaSq Q s (.finite 1) a)⁻¹ =
        (Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ)) ^ 2 := by
          symm
          exact Homogenization.sq_rpow_neg_half_eq_inv_of_nonneg
            (lambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 1))
    _ =
        (∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) ^ 2 := by
          rw [lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 1 a
            (by norm_num : (0 : ℝ) < 1) (by positivity : 0 ≤ s * (1 : ℝ))]
    _ =
        Real.rpow
          (∑' n : ℕ,
            geometricWeight s 1 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) (2 : ℝ) := by
          exact (Real.rpow_natCast _ 2).symm
    _ ≤
        ∑' n : ℕ,
          geometricWeight s 1 n *
            maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
          rpow_two_tsum_weighted_rpow_half_le_tsum_weighted
            (w := fun n : ℕ => geometricWeight s 1 n)
            (H := fun n : ℕ =>
              maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (fun n => by
              simpa [geometricWeight_eq_old] using
                Homogenization.geometricWeight_nonneg n
                  (mul_nonneg hs.le (by norm_num : (0 : ℝ) ≤ 1)))
            (fun n =>
              have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
              maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
                (sub_le_self Q.scale hn) a)
            (by
              simpa [geometricWeight_eq_old] using
                Homogenization.summable_geometricWeight_one (s := s) hs)
            (by
              simpa [geometricWeight_eq_old] using
                (Homogenization.tsum_geometricWeight_one_eq_one (s := s) hs).le)
            hNorm_sum hSqrt_sum

theorem LambdaSqFinite_le_change_exponent {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s p q : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) (hp : 1 ≤ p) (hpq : p ≤ q) :
    LambdaSq Q s (.finite q) a ≤
      (25 * Real.exp 4) * Real.rpow s (2 / q - 2 / p) *
        LambdaSq Q s (.finite p) a := by
  have hexact :=
    LambdaSqFinite_le_change_exponent_geometricDiscount
      Q a hs hp hpq
  have hfactor :=
    geometricDiscount_change_exponent_factor_le
      (s := s) (p := p) (q := q) hs hs_le hp hpq
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite p) a :=
    LambdaSq_finite_nonneg Q a hs hp
  calc
    LambdaSq Q s (.finite q) a ≤
        (Real.rpow (geometricDiscount s q) (2 / q) *
            Real.rpow (geometricDiscount s p) (-2 / p)) *
          LambdaSq Q s (.finite p) a := by
          simpa [mul_assoc] using hexact
    _ ≤
        ((25 * Real.exp 4) * Real.rpow s (2 / q - 2 / p)) *
          LambdaSq Q s (.finite p) a :=
          mul_le_mul_of_nonneg_right hfactor hLambda_nonneg
    _ =
        (25 * Real.exp 4) * Real.rpow s (2 / q - 2 / p) *
          LambdaSq Q s (.finite p) a := by
          ring

theorem lambdaSqFinite_inv_le_change_exponent {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s p q : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) (hp : 1 ≤ p) (hpq : p ≤ q) :
    (lambdaSq Q s (.finite q) a)⁻¹ ≤
      (25 * Real.exp 4) * Real.rpow s (2 / q - 2 / p) *
        (lambdaSq Q s (.finite p) a)⁻¹ := by
  have hexact :=
    lambdaSqFinite_inv_le_change_exponent_geometricDiscount
      Q a hs hp hpq
  have hfactor :=
    geometricDiscount_change_exponent_factor_le
      (s := s) (p := p) (q := q) hs hs_le hp hpq
  have hlambda_inv_nonneg : 0 ≤ (lambdaSq Q s (.finite p) a)⁻¹ :=
    inv_nonneg.mpr (lambdaSq_finite_nonneg Q a hs hp)
  calc
    (lambdaSq Q s (.finite q) a)⁻¹ ≤
        (Real.rpow (geometricDiscount s q) (2 / q) *
            Real.rpow (geometricDiscount s p) (-2 / p)) *
          (lambdaSq Q s (.finite p) a)⁻¹ := by
          simpa [mul_assoc] using hexact
    _ ≤
        ((25 * Real.exp 4) * Real.rpow s (2 / q - 2 / p)) *
          (lambdaSq Q s (.finite p) a)⁻¹ :=
          mul_le_mul_of_nonneg_right hfactor hlambda_inv_nonneg
    _ =
        (25 * Real.exp 4) * Real.rpow s (2 / q - 2 / p) *
          (lambdaSq Q s (.finite p) a)⁻¹ := by
          ring

theorem oneCube_b_le_LambdaSq_finite {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) :
    coarseBMatrixNorm Q a ≤ LambdaSq Q s (.finite q) a := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let H : ℕ → ℝ := fun n =>
    Real.rpow
      (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  have hmono : Monotone H := by
    intro m n hmn
    have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by linarith
    have hlQ : Q.scale - (m : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le m)
    refine Real.rpow_le_rpow ?_ ?_ ?_
    · exact maxDescendantBMatrixNormAtScale_nonneg Q hlQ a
    · exact maxDescendantBMatrixNormAtScale_le_of_le a Q hkl hlQ
    · positivity
  have hsum := summable_B_series_pointwiseCoeffField Q a hs hqpos
  have hpow :
      Real.rpow (coarseBMatrixNorm Q a) (q / 2) ≤
        Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) := by
    have hself :
        H 0 ≤ ∑' n : ℕ, geometricWeight s q n * H n := by
      exact Homogenization.self_le_tsum_geometricWeight_of_monotone hmono
        (mul_pos hs hqpos) (by simpa [H, geometricWeight_eq_old] using hsum)
    calc
      Real.rpow (coarseBMatrixNorm Q a) (q / 2) = H 0 := by
        dsimp [H]
        simp [maxDescendantBMatrixNormAtScale_self]
      _ ≤ ∑' n : ℕ, geometricWeight s q n * H n := hself
      _ = Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) := by
        symm
        simpa [H] using
          LambdaSqFinite_rpow_q_div_two_eq_tsum Q s q a hqpos
            (mul_nonneg hs.le hqpos.le)
  exact (Real.rpow_le_rpow_iff
    (coarseBMatrixNorm_nonneg Q a)
    (LambdaSq_finite_nonneg Q a hs hq)
    (by positivity : 0 < q / 2)).1 hpow

theorem oneCube_sigmaStarInv_le_lambdaSq_finite_inv {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) :
    coarseSigmaStarInvMatrixNorm Q a ≤ (lambdaSq Q s (.finite q) a)⁻¹ := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let H : ℕ → ℝ := fun n =>
    Real.rpow
      (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) (q / 2)
  have hmono : Monotone H := by
    intro m n hmn
    have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by linarith
    have hlQ : Q.scale - (m : ℤ) ≤ Q.scale := by
      exact sub_le_self _ (by exact_mod_cast Nat.zero_le m)
    refine Real.rpow_le_rpow ?_ ?_ ?_
    · exact maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hlQ a
    · exact maxDescendantSigmaStarInvMatrixNormAtScale_le_of_le a Q hkl hlQ
    · positivity
  have hsum := summable_sigmaStarInv_series_pointwiseCoeffField Q a hs hqpos
  have hpow :
      Real.rpow (coarseSigmaStarInvMatrixNorm Q a) (q / 2) ≤
        Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
    have hself :
        H 0 ≤ ∑' n : ℕ, geometricWeight s q n * H n := by
      exact Homogenization.self_le_tsum_geometricWeight_of_monotone hmono
        (mul_pos hs hqpos) (by simpa [H, geometricWeight_eq_old] using hsum)
    calc
      Real.rpow (coarseSigmaStarInvMatrixNorm Q a) (q / 2) = H 0 := by
        dsimp [H]
        simp [maxDescendantSigmaStarInvMatrixNormAtScale_self]
      _ ≤ ∑' n : ℕ, geometricWeight s q n * H n := hself
      _ = Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
        symm
        simpa [H] using
          lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s q a hqpos
            (mul_nonneg hs.le hqpos.le)
  have hpow' :
      Real.rpow (coarseSigmaStarInvMatrixNorm Q a) (q / 2) ≤
        Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) := by
    calc
      Real.rpow (coarseSigmaStarInvMatrixNorm Q a) (q / 2) ≤
          Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := hpow
      _ = Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) := by
        have hneg : (-(q / 2 : ℝ)) = -q / 2 := by ring
        simpa [hneg] using
          (Real.rpow_neg_eq_inv_rpow (lambdaSq Q s (.finite q) a) (q / 2))
  exact (Real.rpow_le_rpow_iff
    (coarseSigmaStarInvMatrixNorm_nonneg Q a)
    (inv_nonneg.mpr (lambdaSq_finite_nonneg Q a hs hq))
    (by positivity : 0 < q / 2)).1 hpow'

theorem coarseBMatrixNorm_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) :
    0 < coarseBMatrixNorm Q a := by
  simpa [coarseBMatrixNorm] using
    matrixNorm_pos_of_posDef (bCoarse_posDef (cubeDomain Q) (a.coeffOn Q))

theorem coarseSigmaStarInvMatrixNorm_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) :
    0 < coarseSigmaStarInvMatrixNorm Q a := by
  simpa [coarseSigmaStarInvMatrixNorm] using
    matrixNorm_pos_of_posDef
      (sigmaStarInvCoarse_posDef (cubeDomain Q) (a.coeffOn Q))

theorem LambdaSq_finite_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) :
    0 < LambdaSq Q s (.finite q) a := by
  exact lt_of_lt_of_le (coarseBMatrixNorm_pos Q a)
    (oneCube_b_le_LambdaSq_finite Q a hs hq)

theorem lambdaSq_finite_pos {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) :
    0 < lambdaSq Q s (.finite q) a := by
  have hle :
      coarseSigmaStarInvMatrixNorm Q a ≤
        (lambdaSq Q s (.finite q) a)⁻¹ :=
    oneCube_sigmaStarInv_le_lambdaSq_finite_inv Q a hs hq
  have hinvpos : 0 < (lambdaSq Q s (.finite q) a)⁻¹ :=
    lt_of_lt_of_le (coarseSigmaStarInvMatrixNorm_pos Q a) hle
  exact inv_pos.mp hinvpos

theorem oneCube_sigmaStarInv_le_b {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) :
    (coarseSigmaStarInvMatrixNorm Q a)⁻¹ ≤ coarseBMatrixNorm Q a := by
  let U : Domain d := cubeDomain Q
  let aQ : CoeffOn U := a.coeffOn Q
  have hMul :
      sigmaStarInvCoarse U aQ * sigmaStarCoarse U aQ = 1 :=
    sigmaStarInvCoarse_mul_sigmaStarCoarse
      (isUnit_det_sigmaStarInvCoarse U aQ)
  have hInvNorm :
      (matrixNorm (sigmaStarInvCoarse U aQ))⁻¹ ≤
        matrixNorm (sigmaStarCoarse U aQ) := by
    have hSInvPos : 0 < matrixNorm (sigmaStarInvCoarse U aQ) := by
      simpa [U, aQ, coarseSigmaStarInvMatrixNorm] using
        coarseSigmaStarInvMatrixNorm_pos Q a
    exact matrixNorm_inv_le_of_mul_eq_one hMul hSInvPos
  have hStarB : MatLoewnerLE (sigmaStarCoarse U aQ) (bCoarse U aQ) := by
    intro x
    exact le_trans ((sigmaStarCoarse_le_sigmaCoarse U aQ) x)
      ((sigmaCoarse_le_bCoarse U aQ) x)
  have hNormOrder :
      matrixNorm (sigmaStarCoarse U aQ) ≤ matrixNorm (bCoarse U aQ) :=
    matrixNorm_le_of_matLoewnerLE_of_posSemidef
      (sigmaStarCoarse_posDef U aQ).posSemidef
      (bCoarse_posSemidef U aQ) hStarB
  calc
    (coarseSigmaStarInvMatrixNorm Q a)⁻¹ =
        (matrixNorm (sigmaStarInvCoarse U aQ))⁻¹ := by
          rfl
    _ ≤ matrixNorm (sigmaStarCoarse U aQ) := hInvNorm
    _ ≤ matrixNorm (bCoarse U aQ) := hNormOrder
    _ = coarseBMatrixNorm Q a := by
          rfl

theorem LambdaSq_finite_antitone {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {t s q : ℝ}
    (ht : 0 < t) (hts : t < s) (hq : 1 ≤ q) :
    LambdaSq Q s (.finite q) a ≤ LambdaSq Q t (.finite q) a := by
  have hs : 0 < s := lt_trans ht hts
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t q n *
          Real.rpow
            (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2)) := by
    exact summable_B_series_pointwiseCoeffField Q a ht hqpos
  have hpow :
      Real.rpow (LambdaSq Q s (.finite q) a) (q / 2) ≤
        Real.rpow (LambdaSq Q t (.finite q) a) (q / 2) := by
    rw [LambdaSqFinite_rpow_q_div_two_eq_tsum Q s q a hqpos
        (mul_nonneg hs.le hqpos.le),
      LambdaSqFinite_rpow_q_div_two_eq_tsum Q t q a hqpos
        (mul_nonneg ht.le hqpos.le)]
    refine Homogenization.tsum_geometricWeight_le_of_monotone ?_ ?_
      hqpos ht hts (by simpa [geometricWeight_eq_old] using hsum_t)
    · intro m n hmn
      have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
      have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by linarith
      have hlQ : Q.scale - (m : ℤ) ≤ Q.scale := by
        exact sub_le_self _ (by exact_mod_cast Nat.zero_le m)
      refine Real.rpow_le_rpow ?_ ?_ ?_
      · exact maxDescendantBMatrixNormAtScale_nonneg Q hlQ a
      · exact maxDescendantBMatrixNormAtScale_le_of_le a Q hkl hlQ
      · positivity
    · intro n
      refine Real.rpow_nonneg ?_ _
      exact maxDescendantBMatrixNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  exact (Real.rpow_le_rpow_iff
    (LambdaSq_finite_nonneg Q a hs hq)
    (LambdaSq_finite_nonneg Q a ht hq)
    (by positivity : 0 < q / 2)).1 hpow

theorem lambdaSq_finite_mono {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {t s q : ℝ}
    (ht : 0 < t) (hts : t < s) (hq : 1 ≤ q) :
    lambdaSq Q t (.finite q) a ≤ lambdaSq Q s (.finite q) a := by
  have hs : 0 < s := lt_trans ht hts
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t q n *
          Real.rpow
            (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (q / 2)) := by
    exact summable_sigmaStarInv_series_pointwiseCoeffField Q a ht hqpos
  have hpow_neg :
      Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) ≤
        Real.rpow (lambdaSq Q t (.finite q) a) (-q / 2) := by
    rw [lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s q a hqpos
        (mul_nonneg hs.le hqpos.le),
      lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q t q a hqpos
        (mul_nonneg ht.le hqpos.le)]
    refine Homogenization.tsum_geometricWeight_le_of_monotone ?_ ?_
      hqpos ht hts (by simpa [geometricWeight_eq_old] using hsum_t)
    · intro m n hmn
      have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
      have hkl : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ) := by linarith
      have hlQ : Q.scale - (m : ℤ) ≤ Q.scale := by
        exact sub_le_self _ (by exact_mod_cast Nat.zero_le m)
      refine Real.rpow_le_rpow ?_ ?_ ?_
      · exact maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hlQ a
      · exact maxDescendantSigmaStarInvMatrixNormAtScale_le_of_le a Q hkl hlQ
      · positivity
    · intro n
      refine Real.rpow_nonneg ?_ _
      exact maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hpow_inv :
      Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) ≤
        Real.rpow ((lambdaSq Q t (.finite q) a)⁻¹) (q / 2) := by
    have hneg : (-(q / 2 : ℝ)) = -q / 2 := by ring
    calc
      Real.rpow ((lambdaSq Q s (.finite q) a)⁻¹) (q / 2) =
          Real.rpow (lambdaSq Q s (.finite q) a) (-q / 2) := by
            simpa [hneg] using
              (Real.rpow_neg_eq_inv_rpow (lambdaSq Q s (.finite q) a) (q / 2)).symm
      _ ≤ Real.rpow (lambdaSq Q t (.finite q) a) (-q / 2) := hpow_neg
      _ = Real.rpow ((lambdaSq Q t (.finite q) a)⁻¹) (q / 2) := by
            simpa [hneg] using
              (Real.rpow_neg_eq_inv_rpow (lambdaSq Q t (.finite q) a) (q / 2))
  have hinv :
      (lambdaSq Q s (.finite q) a)⁻¹ ≤
        (lambdaSq Q t (.finite q) a)⁻¹ :=
    (Real.rpow_le_rpow_iff
      (inv_nonneg.mpr (lambdaSq_finite_nonneg Q a hs hq))
      (inv_nonneg.mpr (lambdaSq_finite_nonneg Q a ht hq))
      (by positivity : 0 < q / 2)).1 hpow_inv
  exact (inv_le_inv₀ (lambdaSq_finite_pos Q a hs hq)
    (lambdaSq_finite_pos Q a ht hq)).1 hinv

theorem lambdaSq_finite_le_oneCube {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) :
    lambdaSq Q s (.finite q) a ≤ (coarseSigmaStarInvMatrixNorm Q a)⁻¹ := by
  have hlambda_pos : 0 < lambdaSq Q s (.finite q) a :=
    lambdaSq_finite_pos Q a hs hq
  have hSigpos : 0 < coarseSigmaStarInvMatrixNorm Q a :=
    coarseSigmaStarInvMatrixNorm_pos Q a
  have hle :
      coarseSigmaStarInvMatrixNorm Q a ≤
        (lambdaSq Q s (.finite q) a)⁻¹ :=
    oneCube_sigmaStarInv_le_lambdaSq_finite_inv Q a hs hq
  have hinvpos : 0 < (lambdaSq Q s (.finite q) a)⁻¹ := by
    exact inv_pos.mpr hlambda_pos
  have hconverted :
      ((lambdaSq Q s (.finite q) a)⁻¹)⁻¹ ≤
        (coarseSigmaStarInvMatrixNorm Q a)⁻¹ :=
    (inv_le_inv₀ hinvpos hSigpos).2 hle
  simpa [inv_inv] using hconverted

end

end Ch02
end Book
end Homogenization
