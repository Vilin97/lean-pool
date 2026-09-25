/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Series

/-! # One Cube Bounds -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

/-!
# Finite-exponent multiscale ellipticity: one-cube bounds
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius

noncomputable section

private theorem natCast_rpow_half_le_self {d : ℕ} [NeZero d] :
    Real.rpow (d : ℝ) (1 / 2 : ℝ) ≤ (d : ℝ) := by
  have hd_one : (1 : ℝ) ≤ (d : ℝ) := by
    norm_num [Nat.one_le_iff_ne_zero, NeZero.ne d]
  simpa using Real.rpow_le_rpow_of_exponent_le hd_one
    (by norm_num : (1 / 2 : ℝ) ≤ 1)

private theorem sqrt_natCast_mul_le_natCast_mul_sqrt {d : ℕ} [NeZero d] (x : ℝ) :
    Real.sqrt ((d : ℝ) * x) ≤ (d : ℝ) * Real.sqrt x := by
  calc
    Real.sqrt ((d : ℝ) * x) = Real.sqrt (d : ℝ) * Real.sqrt x := by
      exact Real.sqrt_mul (Nat.cast_nonneg d) _
    _ ≤ (d : ℝ) * Real.sqrt x := by
      exact mul_le_mul_of_nonneg_right
        (by simpa [Real.sqrt_eq_rpow] using natCast_rpow_half_le_self (d := d))
        (Real.sqrt_nonneg x)

theorem LambdaSq_one_rpow_half_le_old_pointwiseCoeffField {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) ≤
      Real.rpow
        (Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))
        (1 / 2 : ℝ) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hpubSummable := summable_B_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 1)
  have holdSummable := summable_old_B_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 1)
  have hterm :
      ∀ n : ℕ,
        geometricWeight s 1 n *
            Real.rpow
              (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) ≤
          Homogenization.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.maxDescendantBBlockNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hweight_nonneg : 0 ≤ geometricWeight s 1 n := by
      simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (by positivity : 0 ≤ s * (1 : ℝ))
    have hmax :=
      maxDescendantBMatrixNormAtScale_le_maxDescendantBBlockNormAtScale
        (a := a) Q (sub_le_self _ hn)
    have hpow :
        Real.rpow
            (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ) ≤
          Real.rpow
            (Homogenization.maxDescendantBBlockNormAtScale Q
              (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow
        (maxDescendantBMatrixNormAtScale_nonneg Q (sub_le_self _ hn) a)
        (by simpa [A] using hmax) (by positivity)
    simpa [geometricWeight_eq_old, A] using
      mul_le_mul_of_nonneg_left hpow hweight_nonneg
  calc
    Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) =
        ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow
              (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
          simpa using
            (LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 1 a
              (by norm_num : (0 : ℝ) < 1) (by positivity : 0 ≤ s * (1 : ℝ)))
    _ ≤
        ∑' n : ℕ,
          Homogenization.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.maxDescendantBBlockNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) := by
          exact Summable.tsum_le_tsum hterm hpubSummable
            (by simpa [A] using holdSummable)
    _ =
        Real.rpow
          (Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1) A)
          (1 / 2 : ℝ) := by
          simpa [A] using
            (Homogenization.multiscale_ellipticity_LambdaSq_one_rpow_half_eq_tsum
              Q s A hs.le).symm

theorem lambdaSq_one_rpow_neg_half_le_old_pointwiseCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) ≤
      Real.rpow
        (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))
        (-1 / 2 : ℝ) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hpubSummable := summable_sigmaStarInv_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 1)
  have holdSummable := summable_old_sigmaStarInv_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 1)
  have hterm :
      ∀ n : ℕ,
        geometricWeight s 1 n *
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) ≤
          Homogenization.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hweight_nonneg : 0 ≤ geometricWeight s 1 n := by
      simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (by positivity : 0 ≤ s * (1 : ℝ))
    have hmax :=
      maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
        (a := a) Q (sub_le_self _ hn)
    have hpow :
        Real.rpow
            (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ) ≤
          Real.rpow
            (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
              (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) := by
      exact Real.rpow_le_rpow
        (maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
          (sub_le_self _ hn) a)
        (by simpa [A] using hmax) (by positivity)
    simpa [geometricWeight_eq_old, A] using
      mul_le_mul_of_nonneg_left hpow hweight_nonneg
  calc
    Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) =
        ∑' n : ℕ,
          geometricWeight s 1 n *
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
          simpa using
            (lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 1 a
              (by norm_num : (0 : ℝ) < 1) (by positivity : 0 ≤ s * (1 : ℝ)))
    _ ≤
        ∑' n : ℕ,
          Homogenization.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) := by
          exact Summable.tsum_le_tsum hterm hpubSummable
            (by simpa [A] using holdSummable)
    _ =
        Real.rpow
          (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1) A)
          (-1 / 2 : ℝ) := by
          simpa [A] using
            (Homogenization.multiscale_ellipticity_lambdaSq_one_rpow_neg_half_eq_tsum
              Q s A hs.le).symm

theorem old_LambdaSq_one_rpow_half_le_dim_mul_pointwiseCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Real.rpow
        (Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))
        (1 / 2 : ℝ) ≤
      (d : ℝ) * Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hpubSummable := summable_B_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 1)
  have holdSummable := summable_old_B_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 1)
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdim_half_le :
      Real.rpow (d : ℝ) (1 / 2 : ℝ) ≤ (d : ℝ) :=
    natCast_rpow_half_le_self
  have hterm :
      ∀ n : ℕ,
        Homogenization.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.maxDescendantBBlockNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) ≤
          (d : ℝ) *
            (geometricWeight s 1 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hweight_nonneg : 0 ≤ geometricWeight s 1 n := by
      simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (by positivity : 0 ≤ s * (1 : ℝ))
    have hpub_nonneg :
        0 ≤ maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
      maxDescendantBMatrixNormAtScale_nonneg Q (sub_le_self _ hn) a
    have hold_nonneg :
        0 ≤
          Homogenization.maxDescendantBBlockNormAtScale Q
            (Q.scale - (n : ℤ)) A := by
      exact Homogenization.maxDescendantBBlockNormAtScale_nonneg Q
        (sub_le_self _ hn) A
    have hmax :=
      maxDescendantBBlockNormAtScale_le_dim_mul_maxDescendantBMatrixNormAtScale
        (a := a) Q (sub_le_self _ hn)
    have hpow :
        Real.rpow
            (Homogenization.maxDescendantBBlockNormAtScale Q
              (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) ≤
          (d : ℝ) *
            Real.rpow
              (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
      calc
        Real.rpow
            (Homogenization.maxDescendantBBlockNormAtScale Q
              (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) ≤
            Real.rpow
              ((d : ℝ) *
                maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
              exact Real.rpow_le_rpow hold_nonneg (by simpa [A] using hmax)
                (by positivity)
        _ =
            Real.rpow (d : ℝ) (1 / 2 : ℝ) *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ) := by
              exact Real.mul_rpow hd_nonneg hpub_nonneg
        _ ≤
            (d : ℝ) *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ) := by
              exact mul_le_mul_of_nonneg_right hdim_half_le
                (Real.rpow_nonneg hpub_nonneg _)
    calc
      Homogenization.geometricWeight s 1 n *
          Real.rpow
            (Homogenization.maxDescendantBBlockNormAtScale Q
              (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) ≤
          geometricWeight s 1 n *
            ((d : ℝ) *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) := by
            simpa [geometricWeight_eq_old] using
              mul_le_mul_of_nonneg_left hpow hweight_nonneg
      _ =
          (d : ℝ) *
            (geometricWeight s 1 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) := by ring
  have hscaledSummable :
      Summable
        (fun n : ℕ =>
          (d : ℝ) *
            (geometricWeight s 1 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ))) :=
    hpubSummable.mul_left (d : ℝ)
  calc
    Real.rpow
        (Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 1) A)
        (1 / 2 : ℝ) =
        ∑' n : ℕ,
          Homogenization.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.maxDescendantBBlockNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) := by
          simpa [A] using
            Homogenization.multiscale_ellipticity_LambdaSq_one_rpow_half_eq_tsum
              Q s A hs.le
    _ ≤
        ∑' n : ℕ,
          (d : ℝ) *
            (geometricWeight s 1 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) := by
          exact Summable.tsum_le_tsum hterm
            (by simpa [A] using holdSummable) hscaledSummable
    _ =
        (d : ℝ) *
          ∑' n : ℕ,
            geometricWeight s 1 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ) := by
          simpa using
            (Summable.tsum_mul_left (d : ℝ) hpubSummable)
    _ =
        (d : ℝ) * Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
          rw [LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 1 a
            (by norm_num : (0 : ℝ) < 1) (by positivity : 0 ≤ s * (1 : ℝ))]

theorem old_lambdaSq_one_rpow_neg_half_le_dim_mul_pointwiseCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Real.rpow
        (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1)
          (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))
        (-1 / 2 : ℝ) ≤
      (d : ℝ) * Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hpubSummable := summable_sigmaStarInv_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 1)
  have holdSummable := summable_old_sigmaStarInv_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 1)
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdim_half_le :
      Real.rpow (d : ℝ) (1 / 2 : ℝ) ≤ (d : ℝ) :=
    natCast_rpow_half_le_self
  have hterm :
      ∀ n : ℕ,
        Homogenization.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) ≤
          (d : ℝ) *
            (geometricWeight s 1 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hweight_nonneg : 0 ≤ geometricWeight s 1 n := by
      simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (by positivity : 0 ≤ s * (1 : ℝ))
    have hpub_nonneg :
        0 ≤ maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) a :=
      maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q (sub_le_self _ hn) a
    have hold_nonneg :
        0 ≤
          Homogenization.maxDescendantSigmaStarInvNormAtScale Q
            (Q.scale - (n : ℤ)) A := by
      exact Homogenization.maxDescendantSigmaStarInvNormAtScale_nonneg Q
        (sub_le_self _ hn) A
    have hmax :=
      maxDescendantSigmaStarInvNormAtScale_le_dim_mul_maxDescendantSigmaStarInvMatrixNormAtScale
        (a := a) Q (sub_le_self _ hn)
    have hpow :
        Real.rpow
            (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
              (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) ≤
          (d : ℝ) *
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
      calc
        Real.rpow
            (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
              (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) ≤
            Real.rpow
              ((d : ℝ) *
                maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ) := by
              exact Real.rpow_le_rpow hold_nonneg (by simpa [A] using hmax)
                (by positivity)
        _ =
            Real.rpow (d : ℝ) (1 / 2 : ℝ) *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ) := by
              exact Real.mul_rpow hd_nonneg hpub_nonneg
        _ ≤
            (d : ℝ) *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ) := by
              exact mul_le_mul_of_nonneg_right hdim_half_le
                (Real.rpow_nonneg hpub_nonneg _)
    calc
      Homogenization.geometricWeight s 1 n *
          Real.rpow
            (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
              (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) ≤
          geometricWeight s 1 n *
            ((d : ℝ) *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) := by
            simpa [geometricWeight_eq_old] using
              mul_le_mul_of_nonneg_left hpow hweight_nonneg
      _ =
          (d : ℝ) *
            (geometricWeight s 1 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) := by ring
  have hscaledSummable :
      Summable
        (fun n : ℕ =>
          (d : ℝ) *
            (geometricWeight s 1 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ))) :=
    hpubSummable.mul_left (d : ℝ)
  calc
    Real.rpow
        (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 1) A)
        (-1 / 2 : ℝ) =
        ∑' n : ℕ,
          Homogenization.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) := by
          simpa [A] using
            Homogenization.multiscale_ellipticity_lambdaSq_one_rpow_neg_half_eq_tsum
              Q s A hs.le
    _ ≤
        ∑' n : ℕ,
          (d : ℝ) *
            (geometricWeight s 1 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ)) := by
          exact Summable.tsum_le_tsum hterm
            (by simpa [A] using holdSummable) hscaledSummable
    _ =
        (d : ℝ) *
          ∑' n : ℕ,
            geometricWeight s 1 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (1 / 2 : ℝ) := by
          simpa using
            (Summable.tsum_mul_left (d : ℝ) hpubSummable)
    _ =
        (d : ℝ) * Real.rpow (lambdaSq Q s (.finite 1) a) (-1 / 2 : ℝ) := by
          rw [lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 1 a
            (by norm_num : (0 : ℝ) < 1) (by positivity : 0 ≤ s * (1 : ℝ))]

theorem old_LambdaSq_two_le_dim_mul_pointwiseCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 2)
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)) ≤
      (d : ℝ) * LambdaSq Q s (.finite 2) a := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hpubSummable := summable_B_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 2)
  have holdSummable := summable_old_B_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 2)
  have hterm :
      ∀ n : ℕ,
        Homogenization.geometricWeight s 2 n *
            Real.rpow
              (Homogenization.maxDescendantBBlockNormAtScale Q
                (Q.scale - (n : ℤ)) A) (2 / 2 : ℝ) ≤
          (d : ℝ) *
            (geometricWeight s 2 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ)) := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hweight_nonneg : 0 ≤ geometricWeight s 2 n := by
      simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (by positivity : 0 ≤ s * (2 : ℝ))
    have hmax :=
      maxDescendantBBlockNormAtScale_le_dim_mul_maxDescendantBMatrixNormAtScale
        (a := a) Q (sub_le_self _ hn)
    have hpow :
        Real.rpow
            (Homogenization.maxDescendantBBlockNormAtScale Q
              (Q.scale - (n : ℤ)) A) (2 / 2 : ℝ) ≤
          (d : ℝ) *
            Real.rpow
              (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
              (2 / 2 : ℝ) := by
      simpa [A, Real.rpow_one] using hmax
    calc
      Homogenization.geometricWeight s 2 n *
          Real.rpow
            (Homogenization.maxDescendantBBlockNormAtScale Q
              (Q.scale - (n : ℤ)) A) (2 / 2 : ℝ) ≤
          geometricWeight s 2 n *
            ((d : ℝ) *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ)) := by
            simpa [geometricWeight_eq_old] using
              mul_le_mul_of_nonneg_left hpow hweight_nonneg
      _ =
          (d : ℝ) *
            (geometricWeight s 2 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ)) := by ring
  have hscaledSummable :
      Summable
        (fun n : ℕ =>
          (d : ℝ) *
            (geometricWeight s 2 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ))) :=
    hpubSummable.mul_left (d : ℝ)
  calc
    Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 2) A =
        ∑' n : ℕ,
          Homogenization.geometricWeight s 2 n *
            Real.rpow
              (Homogenization.maxDescendantBBlockNormAtScale Q
                (Q.scale - (n : ℤ)) A) (2 / 2 : ℝ) := by
          simpa [A] using
            Homogenization.multiscale_ellipticity_LambdaSq_finite_rpow_q_div_two_eq_tsum
              Q s 2 A (by norm_num : (0 : ℝ) < 2)
              (by positivity : 0 ≤ s * (2 : ℝ))
    _ ≤
        ∑' n : ℕ,
          (d : ℝ) *
            (geometricWeight s 2 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ)) := by
          exact Summable.tsum_le_tsum hterm
            (by simpa [A] using holdSummable) hscaledSummable
    _ =
        (d : ℝ) *
          ∑' n : ℕ,
            geometricWeight s 2 n *
              Real.rpow
                (maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ) := by
          simpa using
            (Summable.tsum_mul_left (d : ℝ) hpubSummable)
    _ =
        (d : ℝ) * LambdaSq Q s (.finite 2) a := by
          congr 1
          simpa [Real.rpow_one] using
            (LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 2 a
              (by norm_num : (0 : ℝ) < 2)
              (by positivity : 0 ≤ s * (2 : ℝ))).symm

theorem old_LambdaSq_two_rpow_half_le_dim_mul_pointwiseCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Real.rpow
        (Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 2)
          (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))
        (1 / 2 : ℝ) ≤
      (d : ℝ) * Real.rpow (LambdaSq Q s (.finite 2) a) (1 / 2 : ℝ) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hLambda_le := old_LambdaSq_two_le_dim_mul_pointwiseCoeffField Q a hs
  have hsqrts :
      Real.sqrt
          (Homogenization.LambdaSq Q s (Homogenization.MultiscaleExponent.finite 2) A) ≤
        Real.sqrt ((d : ℝ) * LambdaSq Q s (.finite 2) a) :=
    Real.sqrt_le_sqrt (by simpa [A] using hLambda_le)
  have hsqrt_dim :
      Real.sqrt ((d : ℝ) * LambdaSq Q s (.finite 2) a) ≤
        (d : ℝ) * Real.sqrt (LambdaSq Q s (.finite 2) a) :=
    sqrt_natCast_mul_le_natCast_mul_sqrt _
  simpa [A, Real.sqrt_eq_rpow] using hsqrts.trans hsqrt_dim

theorem old_lambdaSq_two_inv_le_dim_mul_pointwiseCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 2)
        (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))⁻¹ ≤
      (d : ℝ) * (lambdaSq Q s (.finite 2) a)⁻¹ := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hpubSummable := summable_sigmaStarInv_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 2)
  have holdSummable := summable_old_sigmaStarInv_series_pointwiseCoeffField Q a hs
    (by norm_num : (0 : ℝ) < 2)
  have hterm :
      ∀ n : ℕ,
        Homogenization.geometricWeight s 2 n *
            Real.rpow
              (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
                (Q.scale - (n : ℤ)) A) (2 / 2 : ℝ) ≤
          (d : ℝ) *
            (geometricWeight s 2 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ)) := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hweight_nonneg : 0 ≤ geometricWeight s 2 n := by
      simpa [geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (by positivity : 0 ≤ s * (2 : ℝ))
    have hmax :=
      maxDescendantSigmaStarInvNormAtScale_le_dim_mul_maxDescendantSigmaStarInvMatrixNormAtScale
        (a := a) Q (sub_le_self _ hn)
    have hpow :
        Real.rpow
            (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
              (Q.scale - (n : ℤ)) A) (2 / 2 : ℝ) ≤
          (d : ℝ) *
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) a)
              (2 / 2 : ℝ) := by
      simpa [A, Real.rpow_one] using hmax
    calc
      Homogenization.geometricWeight s 2 n *
          Real.rpow
            (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
              (Q.scale - (n : ℤ)) A) (2 / 2 : ℝ) ≤
          geometricWeight s 2 n *
            ((d : ℝ) *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ)) := by
            simpa [geometricWeight_eq_old] using
              mul_le_mul_of_nonneg_left hpow hweight_nonneg
      _ =
          (d : ℝ) *
            (geometricWeight s 2 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ)) := by ring
  have hscaledSummable :
      Summable
        (fun n : ℕ =>
          (d : ℝ) *
            (geometricWeight s 2 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ))) :=
    hpubSummable.mul_left (d : ℝ)
  calc
    (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 2) A)⁻¹ =
        Real.rpow
          (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 2) A)
          (-1 : ℝ) := by
          exact (Real.rpow_neg_one _).symm
    _ =
        ∑' n : ℕ,
          Homogenization.geometricWeight s 2 n *
            Real.rpow
              (Homogenization.maxDescendantSigmaStarInvNormAtScale Q
                (Q.scale - (n : ℤ)) A) (2 / 2 : ℝ) := by
          simpa [A] using
            Homogenization.multiscale_ellipticity_lambdaSq_finite_rpow_neg_q_div_two_eq_tsum
              Q s 2 A (by norm_num : (0 : ℝ) < 2)
              (by positivity : 0 ≤ s * (2 : ℝ))
    _ ≤
        ∑' n : ℕ,
          (d : ℝ) *
            (geometricWeight s 2 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ)) := by
          exact Summable.tsum_le_tsum hterm
            (by simpa [A] using holdSummable) hscaledSummable
    _ =
        (d : ℝ) *
          ∑' n : ℕ,
            geometricWeight s 2 n *
              Real.rpow
                (maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) a)
                (2 / 2 : ℝ) := by
          simpa using
            (Summable.tsum_mul_left (d : ℝ) hpubSummable)
    _ =
        (d : ℝ) * Real.rpow (lambdaSq Q s (.finite 2) a) (-1 : ℝ) := by
          congr 1
          simpa using
            (lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 2 a
              (by norm_num : (0 : ℝ) < 2)
              (by positivity : 0 ≤ s * (2 : ℝ))).symm
    _ =
        (d : ℝ) * (lambdaSq Q s (.finite 2) a)⁻¹ := by
          congr 1
          exact Real.rpow_neg_one _

theorem old_lambdaSq_two_rpow_neg_half_le_dim_mul_pointwiseCoeffField
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    Real.rpow
        (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 2)
          (Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)))
        (-1 / 2 : ℝ) ≤
      (d : ℝ) * Real.rpow (lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) := by
  let A : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (cubeDomain Q) (a.coeffOn Q)
  have hinv_le := old_lambdaSq_two_inv_le_dim_mul_pointwiseCoeffField Q a hs
  have hsqrts :
      Real.sqrt
          ((Homogenization.lambdaSq Q s
              (Homogenization.MultiscaleExponent.finite 2) A)⁻¹) ≤
        Real.sqrt ((d : ℝ) * (lambdaSq Q s (.finite 2) a)⁻¹) :=
    Real.sqrt_le_sqrt (by simpa [A] using hinv_le)
  have hsqrt_dim :
      Real.sqrt ((d : ℝ) * (lambdaSq Q s (.finite 2) a)⁻¹) ≤
        (d : ℝ) * Real.sqrt ((lambdaSq Q s (.finite 2) a)⁻¹) :=
    sqrt_natCast_mul_le_natCast_mul_sqrt _
  have hleft :
      Real.sqrt
          ((Homogenization.lambdaSq Q s
              (Homogenization.MultiscaleExponent.finite 2) A)⁻¹) =
        Real.rpow
          (Homogenization.lambdaSq Q s
            (Homogenization.MultiscaleExponent.finite 2) A)
          (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
    rw [← Real.rpow_eq_pow]
    ring_nf
  have hright :
      Real.sqrt ((lambdaSq Q s (.finite 2) a)⁻¹) =
        Real.rpow (lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_eq_inv_rpow]
    rw [← Real.rpow_eq_pow]
    ring_nf
  calc
    Real.rpow
        (Homogenization.lambdaSq Q s (Homogenization.MultiscaleExponent.finite 2) A)
        (-1 / 2 : ℝ) =
        Real.sqrt
          ((Homogenization.lambdaSq Q s
              (Homogenization.MultiscaleExponent.finite 2) A)⁻¹) := hleft.symm
    _ ≤ Real.sqrt ((d : ℝ) * (lambdaSq Q s (.finite 2) a)⁻¹) := hsqrts
    _ ≤ (d : ℝ) * Real.sqrt ((lambdaSq Q s (.finite 2) a)⁻¹) := hsqrt_dim
    _ = (d : ℝ) * Real.rpow (lambdaSq Q s (.finite 2) a) (-1 / 2 : ℝ) := by
      rw [hright]

end

end Ch02
end Book
end Homogenization
