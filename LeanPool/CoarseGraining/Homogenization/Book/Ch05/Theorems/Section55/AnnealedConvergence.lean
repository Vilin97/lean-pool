/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.AnnealedImprovement

/-! # Annealed Convergence -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section55

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Main annealed convergence theorem

This file contains the scalar iteration which turns the one-step annealed
improvement into the main annealed convergence theorem.
-/

private theorem thetaAtScale_mono_of_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {n m : ℕ} (hnm : n ≤ m) :
    thetaAtScale hP hStruct (m : ℤ) ≤
      thetaAtScale hP hStruct (n : ℤ) :=
  (Section52.scalarPreliminaries_homogenizationScale
    hP hStruct hP4 n m n hnm le_rfl 0 0).2.1

private theorem thetaAtScale_zero_le_widetildeThetaAtScale_zero
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    thetaAtScale hP hStruct (0 : ℤ) ≤
      widetildeThetaAtScale P (0 : ℤ) hP4 :=
  (Section52.scalarPreliminaries_homogenizationScale
    hP hStruct hP4 0 0 0 le_rfl le_rfl 0 0).2.2.1

private theorem widetildeThetaAtScale_nonneg
    {d : ℕ} [NeZero d] (P : Ch04.RestrictionCoeffLaw d)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℤ) :
    0 ≤ widetildeThetaAtScale P m hP4 := by
  unfold widetildeThetaAtScale Ch04.widetildeThetaAtScale
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P m hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P m hP4.xi hP4.sLower_pos)

private theorem log_two_add_mul_le_const_mul_log_two_add
    {A x : ℝ} (hA : 1 ≤ A) (hx : 0 ≤ x) :
    Real.log (2 + x * A) ≤ (1 + 2 * A) * Real.log (2 + x) := by
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hxarg_pos : 0 < 2 + x := add_pos_of_pos_of_nonneg (by norm_num) hx
  have hleft_pos : 0 < 2 + x * A := by
    exact add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg hx hA_pos.le)
  have harg_le : 2 + x * A ≤ A * (2 + x) := by
    have htwoA : (2 : ℝ) ≤ 2 * A := by
      simpa using
        mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 + x * A = x * A + 2 := by ring
      _ ≤ x * A + 2 * A := add_le_add_right htwoA (x * A)
      _ = 2 * A + x * A := by ring
      _ = A * (2 + x) := by ring
  have hlog_le :
      Real.log (2 + x * A) ≤ Real.log (A * (2 + x)) :=
    Real.log_le_log hleft_pos harg_le
  have hmul_log :
      Real.log (A * (2 + x)) = Real.log A + Real.log (2 + x) := by
    rw [Real.log_mul hA_pos.ne' hxarg_pos.ne']
  have hlogA_le : Real.log A ≤ A := Real.log_le_self hA_pos.le
  have hlog_two_le : Real.log 2 ≤ Real.log (2 + x) := by
    exact Real.log_le_log (by norm_num)
      (le_add_of_nonneg_right hx : (2 : ℝ) ≤ 2 + x)
  have hone_le_two_log : (1 : ℝ) ≤ 2 * Real.log (2 + x) := by
    have htwo : (1 : ℝ) ≤ 2 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    exact htwo.trans (mul_le_mul_of_nonneg_left hlog_two_le (by norm_num))
  have hA_le : A ≤ 2 * A * Real.log (2 + x) := by
    have hmul := mul_le_mul_of_nonneg_left hone_le_two_log hA_pos.le
    calc
      A = A * 1 := by ring
      _ ≤ A * (2 * Real.log (2 + x)) := hmul
      _ = 2 * A * Real.log (2 + x) := by ring
  calc
    Real.log (2 + x * A) ≤ Real.log (A * (2 + x)) := hlog_le
    _ = Real.log A + Real.log (2 + x) := hmul_log
    _ ≤ 2 * A * Real.log (2 + x) + Real.log (2 + x) := by
      calc
        Real.log A + Real.log (2 + x) =
            Real.log (2 + x) + Real.log A := by ring
        _ ≤ Real.log (2 + x) + 2 * A * Real.log (2 + x) :=
          add_le_add_right (hlogA_le.trans hA_le) (Real.log (2 + x))
        _ = 2 * A * Real.log (2 + x) + Real.log (2 + x) := by ring
    _ = (1 + 2 * A) * Real.log (2 + x) := by ring

private theorem quarter_pow_natCeil_log_two_add_mul_le_one
    {T : ℝ} (hT : 0 ≤ T) :
    ((1 / 4 : ℝ) ^ Nat.ceil (Real.log (2 + T))) * T ≤ 1 := by
  let L : ℝ := Real.log (2 + T)
  let J : ℕ := Nat.ceil L
  have harg_pos : 0 < 2 + T := add_pos_of_pos_of_nonneg (by norm_num) hT
  have harg_ge_one : 1 ≤ 2 + T := by
    calc
      (1 : ℝ) ≤ 2 := by norm_num
      _ ≤ 2 + T := le_add_of_nonneg_right hT
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg harg_ge_one
  have hJ_ge_L : L ≤ (J : ℝ) := by
    simpa [J] using Nat.le_ceil L
  have hbase_pos : 0 < (1 / 4 : ℝ) := by norm_num
  have hbase_le_one : (1 / 4 : ℝ) ≤ 1 := by norm_num
  have hpow_le :
      (1 / 4 : ℝ) ^ (J : ℝ) ≤ (1 / 4 : ℝ) ^ L :=
    Real.rpow_le_rpow_of_exponent_ge hbase_pos hbase_le_one hJ_ge_L
  have hlog4_ge_one : (1 : ℝ) ≤ Real.log 4 := by
    have htwo : (1 : ℝ) ≤ 2 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rwa [hlog4]
  have hquarter_log :
      Real.log (1 / 4 : ℝ) * L ≤ -L := by
    have hlog_quarter : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
      rw [Real.log_inv]
    rw [hlog_quarter]
    calc
      -Real.log 4 * L ≤ (-1 : ℝ) * L :=
        mul_le_mul_of_nonneg_right (neg_le_neg hlog4_ge_one) hL_nonneg
      _ = -L := by ring
  have hquarter_le_inv :
      (1 / 4 : ℝ) ^ L ≤ (2 + T)⁻¹ := by
    calc
      (1 / 4 : ℝ) ^ L =
          Real.exp (Real.log (1 / 4 : ℝ) * L) := by
          simpa using
            (Real.rpow_def_of_pos (x := (1 / 4 : ℝ)) (y := L) hbase_pos)
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr hquarter_log
      _ = (2 + T)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log harg_pos]
  have hmul :
      ((1 / 4 : ℝ) ^ (J : ℝ)) * T ≤ (2 + T)⁻¹ * T :=
    mul_le_mul_of_nonneg_right (hpow_le.trans hquarter_le_inv) hT
  have hfrac : (2 + T)⁻¹ * T ≤ 1 := by
    have hpos : 0 < 2 + T := harg_pos
    rw [inv_mul_le_iff₀ hpos]
    nlinarith
  have hnat :
      ((1 / 4 : ℝ) ^ Nat.ceil L) * T =
        ((1 / 4 : ℝ) ^ (J : ℝ)) * T := by
    simp [J, Real.rpow_natCast]
  rw [show Real.log (2 + T) = L by rfl]
  rw [hnat]
  exact hmul.trans hfrac

private theorem scalar_quarter_iteration_le_three
    {f : ℕ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    {H J : ℕ}
    (h0 : f 0 ≤ T)
    (hstep : ∀ j : ℕ, f ((j + 1) * H) ≤ 1 + (1 / 4 : ℝ) * f (j * H))
    (hJ : J = Nat.ceil (Real.log (2 + T))) :
    f (J * H) ≤ 3 := by
  have hiter : ∀ j : ℕ, f (j * H) ≤ 2 + (1 / 4 : ℝ) ^ j * T := by
    intro j
    induction j with
    | zero =>
        simpa using h0.trans (by nlinarith : T ≤ 2 + (1 / 4 : ℝ) ^ (0 : ℕ) * T)
    | succ j ih =>
        calc
          f ((j + 1) * H)
              ≤ 1 + (1 / 4 : ℝ) * f (j * H) := hstep j
          _ ≤ 1 + (1 / 4 : ℝ) * (2 + (1 / 4 : ℝ) ^ j * T) := by
                have hquarter_nonneg : 0 ≤ (1 / 4 : ℝ) := by norm_num
                nlinarith [mul_le_mul_of_nonneg_left ih hquarter_nonneg]
          _ ≤ 2 + (1 / 4 : ℝ) ^ (j + 1) * T := by
                have hpow :
                    (1 / 4 : ℝ) ^ (j + 1) * T =
                      (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ j * T) := by
                  rw [pow_succ]
                  ring
                rw [hpow]
                nlinarith
  have htail :
      ((1 / 4 : ℝ) ^ J) * T ≤ 1 := by
    rw [hJ]
    exact quarter_pow_natCeil_log_two_add_mul_le_one hT
  have hmain := hiter J
  nlinarith

private theorem log_two_add_ge_half {T : ℝ} (hT : 0 ≤ T) :
    (1 / 2 : ℝ) ≤ Real.log (2 + T) := by
  have hlog_two_le : Real.log (2 : ℝ) ≤ Real.log (2 + T) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hhalf_le_log_two : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
    nlinarith [Real.log_two_gt_d9]
  exact hhalf_le_log_two.trans hlog_two_le

private theorem natCeil_le_three_mul_of_half_le {x : ℝ}
    (hx : (1 / 2 : ℝ) ≤ x) :
    (Nat.ceil x : ℝ) ≤ 3 * x := by
  have hx_nonneg : 0 ≤ x := by nlinarith
  have hceil : (Nat.ceil x : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hx_nonneg).le
  have htail : x + 1 ≤ 3 * x := by nlinarith
  exact hceil.trans htail

private theorem natCeil_nonneg_le_add_one {x : ℝ} (hx : 0 ≤ x) :
    (Nat.ceil x : ℝ) ≤ x + 1 :=
  (Nat.ceil_lt_add_one hx).le

private theorem exists_burnInScaleConstant
    {d : ℕ} (params : QuantitativeCoarseGrainedEllipticityParams d)
    {Cstep : ℝ} (hCstep_pos : 0 < Cstep) :
    ∃ Cburn : ℝ, 0 < Cburn ∧
      ∀ T : ℝ, 0 ≤ T →
        let L := Real.log (2 + T)
        let J := Nat.ceil L
        let S := Cstep * (params.xi : ℝ) *
          ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) * |Real.log (1 / 4 : ℝ)| *
          Real.log (2 + ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
            (params.xi : ℝ) * T)
        let H := Nat.ceil S
        ((J * H : ℕ) : ℝ) ≤ Cburn * L ^ (2 : ℕ) := by
  classical
  let A : ℝ := ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) * (params.xi : ℝ)
  let B : ℝ := Cstep * (params.xi : ℝ) *
    ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) * |Real.log (1 / 4 : ℝ)| * (1 + 2 * A)
  refine ⟨3 * (B + 2), ?_, ?_⟩
  · have hB_nonneg : 0 ≤ B := by
      dsimp [B, A]
      positivity
    nlinarith
  · intro T hT
    dsimp
    let L : ℝ := Real.log (2 + T)
    let J : ℕ := Nat.ceil L
    let S : ℝ := Cstep * (params.xi : ℝ) *
      ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) * |Real.log (1 / 4 : ℝ)| *
      Real.log (2 + ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
        (params.xi : ℝ) * T)
    let H : ℕ := Nat.ceil S
    have hξ_ge_one : (1 : ℝ) ≤ (params.xi : ℝ) := by
      have htwo : 2 ≤ params.xi := params.two_le_xi
      exact_mod_cast (show (1 : ℕ) ≤ params.xi by omega)
    have hξ_nonneg : 0 ≤ (params.xi : ℝ) := by nlinarith
    have hqpow_ge_one : (1 : ℝ) ≤ ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) := by
      norm_num
    have hqpow_nonneg : 0 ≤ ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) := by positivity
    have hA_ge_one : 1 ≤ A := by
      have hmul := mul_le_mul hqpow_ge_one hξ_ge_one
        (by norm_num : (0 : ℝ) ≤ 1) hqpow_nonneg
      simpa [A] using hmul
    have hA_nonneg : 0 ≤ A := le_trans zero_le_one hA_ge_one
    have hL_half : (1 / 2 : ℝ) ≤ L := by
      simpa [L] using log_two_add_ge_half hT
    have hL_nonneg : 0 ≤ L := by nlinarith
    have hJ_le : (J : ℝ) ≤ 3 * L := by
      simpa [J] using natCeil_le_three_mul_of_half_le hL_half
    have hlog_arg_ge_one :
        1 ≤ 2 + ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
            (params.xi : ℝ) * T := by
      have hprod : 0 ≤ ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
          (params.xi : ℝ) * T := by positivity
      nlinarith
    have hS_nonneg : 0 ≤ S := by
      have hlog_nonneg :
          0 ≤ Real.log (2 + ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
              (params.xi : ℝ) * T) :=
        Real.log_nonneg hlog_arg_ge_one
      have hcoef_nonneg :
          0 ≤ Cstep * (params.xi : ℝ) *
            ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
            |Real.log (1 / 4 : ℝ)| := by positivity
      dsimp [S]
      exact mul_nonneg hcoef_nonneg hlog_nonneg
    have hH_le_add : (H : ℝ) ≤ S + 1 := by
      simpa [H] using natCeil_nonneg_le_add_one hS_nonneg
    have hlog_le :
        Real.log (2 + ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
            (params.xi : ℝ) * T) ≤ (1 + 2 * A) * L := by
      have hrewrite :
          2 + T * A =
            2 + ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
              (params.xi : ℝ) * T := by
        simp [A]
        ring
      have h :=
        log_two_add_mul_le_const_mul_log_two_add
          (A := A) (x := T) hA_ge_one hT
      simpa [L, hrewrite] using h
    have hS_le : S ≤ B * L := by
      have hcoef_nonneg :
          0 ≤ Cstep * (params.xi : ℝ) *
            ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
            |Real.log (1 / 4 : ℝ)| := by positivity
      calc
        S ≤ (Cstep * (params.xi : ℝ) *
              ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
              |Real.log (1 / 4 : ℝ)|) * ((1 + 2 * A) * L) := by
            dsimp [S]
            exact mul_le_mul_of_nonneg_left hlog_le hcoef_nonneg
        _ = B * L := by
            simp [B]
            ring
    have hB_nonneg : 0 ≤ B := by
      dsimp [B, A]
      positivity
    have hH_le : (H : ℝ) ≤ (B + 2) * L := by
      calc
        (H : ℝ) ≤ S + 1 := hH_le_add
        _ = 1 + S := by ring
        _ ≤ 1 + B * L := add_le_add_right hS_le 1
        _ = B * L + 1 := by ring
        _ ≤ B * L + 2 * L := by
          have hone_le_twoL : (1 : ℝ) ≤ 2 * L := by
            calc
              (1 : ℝ) = 2 * (1 / 2 : ℝ) := by norm_num
              _ ≤ 2 * L := mul_le_mul_of_nonneg_left hL_half (by norm_num)
          calc
            B * L + 1 = 1 + B * L := by ring
            _ ≤ 2 * L + B * L := add_le_add_left hone_le_twoL (B * L)
            _ = B * L + 2 * L := by ring
        _ = (B + 2) * L := by ring
    have hH_nonneg : 0 ≤ (H : ℝ) := by exact_mod_cast Nat.zero_le H
    have hprod :=
      mul_le_mul hJ_le hH_le hH_nonneg (mul_nonneg (by norm_num) hL_nonneg)
    have hcast : ((J * H : ℕ) : ℝ) = (J : ℝ) * (H : ℝ) := by
      norm_num
    calc
      ((J * H : ℕ) : ℝ) = (J : ℝ) * (H : ℝ) := hcast
      _ ≤ (3 * L) * ((B + 2) * L) := hprod
      _ = 3 * (B + 2) * L ^ (2 : ℕ) := by ring

private theorem abs_log_div_four_le_four_abs_log
    {sigma : ℝ} (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1 / 2) :
    |Real.log (sigma / 4)| ≤ 4 * |Real.log sigma| := by
  have hsigma_nonneg : 0 ≤ sigma := hsigma_pos.le
  have hlog_sigma_nonpos : Real.log sigma ≤ 0 :=
    Real.log_nonpos hsigma_nonneg (by linarith)
  have habs_sigma : |Real.log sigma| = -Real.log sigma :=
    abs_of_nonpos hlog_sigma_nonpos
  have hlog_half : Real.log sigma ≤ Real.log (1 / 2 : ℝ) :=
    Real.log_le_log hsigma_pos hsigma_le
  have hlog_inv : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    rw [Real.log_inv]
  have hlog2_le_abs : Real.log 2 ≤ |Real.log sigma| := by
    rw [habs_sigma]
    linarith
  have hlog4_le : Real.log (4 : ℝ) ≤ 2 * |Real.log sigma| := by
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [hlog4]
    nlinarith
  have hlog_div :
      Real.log (sigma / 4) = Real.log sigma - Real.log (4 : ℝ) := by
    rw [div_eq_mul_inv, Real.log_mul hsigma_pos.ne' (by norm_num : ((4 : ℝ)⁻¹) ≠ 0),
      Real.log_inv]
    ring
  have hdiv_nonpos : Real.log (sigma / 4) ≤ 0 := by
    rw [hlog_div]
    have hlog4_nonneg : 0 ≤ Real.log (4 : ℝ) :=
      Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    nlinarith
  rw [abs_of_nonpos hdiv_nonpos, hlog_div, habs_sigma]
  nlinarith

private theorem sigma_div_four_inv_pow_four_eq
    {sigma : ℝ} (hsigma_pos : 0 < sigma) :
    (sigma / 4)⁻¹ ^ (4 : ℕ) =
      ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) * sigma⁻¹ ^ (4 : ℕ) := by
  field_simp [hsigma_pos.ne']

private theorem exists_sigmaTailScaleConstant
    {d : ℕ} (params : QuantitativeCoarseGrainedEllipticityParams d)
    {Cstep : ℝ} (hCstep_pos : 0 < Cstep) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ {T sigma : ℝ}, 0 ≤ T → 0 < sigma → sigma ≤ 1 / 2 →
        Cstep * (params.xi : ℝ) * ((sigma / 4)⁻¹ ^ (4 : ℕ)) *
            |Real.log (sigma / 4)| *
            Real.log (2 + (sigma / 4)⁻¹ ^ (4 : ℕ) *
              (params.xi : ℝ) * T) ≤
          Ctail * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
            |Real.log sigma| *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T) := by
  classical
  let A : ℝ := ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ))
  let Ctail : ℝ := Cstep * A * 4 * (1 + 2 * A)
  refine ⟨Ctail, ?_, ?_⟩
  · dsimp [Ctail, A]
    positivity
  · intro T sigma hT hsigma_pos hsigma_le
    have hξ_nonneg : 0 ≤ (params.xi : ℝ) := by
      exact_mod_cast Nat.zero_le params.xi
    have hsigInv_nonneg : 0 ≤ sigma⁻¹ ^ (4 : ℕ) := by positivity
    have hlog_abs_nonneg : 0 ≤ |Real.log sigma| := abs_nonneg _
    have hbase_log_arg_ge_one :
        1 ≤ 2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T := by
      have hprod : 0 ≤ sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T := by positivity
      nlinarith
    have hbase_log_nonneg :
        0 ≤ Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T) :=
      Real.log_nonneg hbase_log_arg_ge_one
    have hA_ge_one : 1 ≤ A := by
      dsimp [A]
      norm_num
    have hA_nonneg : 0 ≤ A := le_trans zero_le_one hA_ge_one
    have hpow_eq := sigma_div_four_inv_pow_four_eq hsigma_pos
    have hlog_le :
        Real.log (2 + (sigma / 4)⁻¹ ^ (4 : ℕ) *
              (params.xi : ℝ) * T) ≤
          (1 + 2 * A) *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T) := by
      have hx_nonneg : 0 ≤ sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T := by positivity
      have h :=
        log_two_add_mul_le_const_mul_log_two_add
          (A := A) (x := sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T)
          hA_ge_one hx_nonneg
      have hrewrite :
          2 + (sigma / 4)⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T =
            2 + (sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T) * A := by
        rw [hpow_eq]
        ring
      calc
        Real.log (2 + (sigma / 4)⁻¹ ^ (4 : ℕ) *
              (params.xi : ℝ) * T)
            = Real.log (2 + (sigma⁻¹ ^ (4 : ℕ) *
                (params.xi : ℝ) * T) * A) := by rw [hrewrite]
        _ ≤ (1 + 2 * A) *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * T) := h
    have habs_le := abs_log_div_four_le_four_abs_log hsigma_pos hsigma_le
    calc
      Cstep * (params.xi : ℝ) * ((sigma / 4)⁻¹ ^ (4 : ℕ)) *
          |Real.log (sigma / 4)| *
          Real.log (2 + (sigma / 4)⁻¹ ^ (4 : ℕ) *
            (params.xi : ℝ) * T)
          = Cstep * A * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
              |Real.log (sigma / 4)| *
              Real.log (2 + (sigma / 4)⁻¹ ^ (4 : ℕ) *
                (params.xi : ℝ) * T) := by
            rw [hpow_eq]
            ring
      _ ≤ Cstep * A * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
              (4 * |Real.log sigma|) *
              Real.log (2 + (sigma / 4)⁻¹ ^ (4 : ℕ) *
                (params.xi : ℝ) * T) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left habs_le (by positivity))
              (by
                have hleft_arg :
                    1 ≤ 2 + (sigma / 4)⁻¹ ^ (4 : ℕ) *
                        (params.xi : ℝ) * T := by
                  have hprod : 0 ≤ (sigma / 4)⁻¹ ^ (4 : ℕ) *
                      (params.xi : ℝ) * T := by positivity
                  nlinarith
                exact Real.log_nonneg hleft_arg)
      _ ≤ Cstep * A * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
              (4 * |Real.log sigma|) *
              ((1 + 2 * A) *
                Real.log (2 + sigma⁻¹ ^ (4 : ℕ) *
                  (params.xi : ℝ) * T)) := by
            exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
      _ = Ctail * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
            |Real.log sigma| *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) *
              (params.xi : ℝ) * T) := by
            simp [Ctail]
            ring

/-- A quarter-sized improvement from an initial bound of three reaches the target accuracy. -/
private theorem quarter_step_le_one_add_of_le_three
    {x y sigma : ℝ} (hstep : x ≤ 1 + (sigma / 4) * y)
    (hy : y ≤ 3) (hsigma : 0 ≤ sigma) : x ≤ 1 + sigma := by
  have hmul := mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ sigma / 4)
  nlinarith only [hstep, hmul, hsigma]

/-- Proposition `p.annealed.convergence.homogenization.scale`.

The constant is chosen from the parameter record before the law and the target
accuracy.  The entry scale is the manuscript two-ceiling scale from
`annealedEntryScale`. -/
theorem annealedPerturbativeEntry_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ sigma : ℝ, 0 < sigma → sigma ≤ (1 / 2 : ℝ) →
        thetaAtScale hP hStruct
          (annealedEntryScale P hP4 C sigma : ℤ) ≤ 1 + sigma := by
  classical
  obtain ⟨Cstep, hCstep_pos, hstep⟩ :=
    oneStepAnnealedImprovement_homogenizationScale params
  obtain ⟨Cburn, hCburn_pos, hburn⟩ :=
    exists_burnInScaleConstant params hCstep_pos
  obtain ⟨Ctail, hCtail_pos, htail⟩ :=
    exists_sigmaTailScaleConstant params hCstep_pos
  let C : ℝ := max Cburn Ctail
  have hC_pos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le hCburn_pos (le_max_left _ _)
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hP4 hparams sigma hsigma_pos hsigma_le
  let W : ℝ := widetildeThetaAtScale P (0 : ℤ) hP4
  let L : ℝ := Real.log (2 + W)
  let J : ℕ := Nat.ceil L
  let S : ℝ := Cstep * (params.xi : ℝ) *
    ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) * |Real.log (1 / 4 : ℝ)| *
    Real.log (2 + ((1 / 4 : ℝ)⁻¹ ^ (4 : ℕ)) *
      (params.xi : ℝ) * W)
  let H : ℕ := Nat.ceil S
  let Nburn : ℕ := J * H
  let Nentry : ℕ := annealedConvergenceEntryScaleBound P hP4 C
  let Ntail : ℕ := annealedConvergenceSigmaTailScale P hP4 C sigma
  let N : ℕ := annealedEntryScale P hP4 C sigma
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact widetildeThetaAtScale_nonneg P hP4 0
  have htheta0_le_W :
      thetaAtScale hP hStruct (0 : ℤ) ≤ W := by
    dsimp [W]
    exact thetaAtScale_zero_le_widetildeThetaAtScale_zero hP hStruct hP4
  have hquarter_pos : 0 < (1 / 4 : ℝ) := by norm_num
  have hquarter_le : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
  have hstep_quarter :
      ∀ j : ℕ,
        thetaAtScale hP hStruct (((j + 1) * H : ℕ) : ℤ) ≤
          1 + (1 / 4 : ℝ) *
            thetaAtScale hP hStruct ((j * H : ℕ) : ℤ) := by
    intro j
    have hkN : j * H ≤ (j + 1) * H :=
      Nat.mul_le_mul_right H (Nat.le_succ j)
    have hceilS : S ≤ (H : ℝ) := by
      simpa [H] using Nat.le_ceil S
    have hdiff : ((j + 1) * H - j * H : ℕ) = H := by
      rw [Nat.succ_mul]
      omega
    exact
      hstep hP hStruct hP4 hparams hquarter_pos hquarter_le hkN
        (by
          simpa [S, W, hdiff] using hceilS)
  let f : ℕ → ℝ := fun n => thetaAtScale hP hStruct (n : ℤ)
  have hburn_theta : f Nburn ≤ 3 := by
    have hiter :=
      scalar_quarter_iteration_le_three
        (f := f) hW_nonneg (H := H) (J := J)
        (by simpa [f] using htheta0_le_W)
        (by
          intro j
          simpa [f] using hstep_quarter j)
        (by rfl : J = Nat.ceil (Real.log (2 + W)))
    simpa [Nburn] using hiter
  have hCburn_le_C : Cburn ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hburn_real :
      (Nburn : ℝ) ≤ C * L ^ (2 : ℕ) := by
    have h0 := hburn W hW_nonneg
    have hsquare_nonneg : 0 ≤ L ^ (2 : ℕ) := sq_nonneg L
    calc
      (Nburn : ℝ) ≤ Cburn * L ^ (2 : ℕ) := by
        simpa [Nburn, J, H, L, S, W] using h0
      _ ≤ C * L ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hCburn_le_C hsquare_nonneg
  have hentry_ceiling :
      C * L ^ (2 : ℕ) ≤ (Nentry : ℝ) := by
    simpa [Nentry, annealedConvergenceEntryScaleBound, L, W] using
      Nat.le_ceil (C * (Real.log (2 + W)) ^ (2 : ℕ))
  have hNburn_le_entry : Nburn ≤ Nentry := by
    exact Nat.cast_le.mp (hburn_real.trans hentry_ceiling)
  have hentry_theta_le_three :
      thetaAtScale hP hStruct (Nentry : ℤ) ≤ 3 := by
    have hmono :=
      thetaAtScale_mono_of_P4 hP hStruct hP4 hNburn_le_entry
    exact hmono.trans (by simpa [f, Nburn] using hburn_theta)
  have hsigma4_pos : 0 < sigma / 4 := by positivity
  have hsigma4_le : sigma / 4 ≤ (1 / 2 : ℝ) := by
    calc
      sigma / 4 ≤ (1 / 2 : ℝ) / 4 :=
        div_le_div_of_nonneg_right hsigma_le (by norm_num)
      _ ≤ (1 / 2 : ℝ) := by norm_num
  have hCtail_le_C : Ctail ≤ C := by
    dsimp [C]
    exact le_max_right _ _
  have hxi_eq : hP4.xi = params.xi := by
    rw [← hparams]
    rfl
  have htail_gap_real :
      Cstep * (params.xi : ℝ) * ((sigma / 4)⁻¹ ^ (4 : ℕ)) *
          |Real.log (sigma / 4)| *
          Real.log (2 + (sigma / 4)⁻¹ ^ (4 : ℕ) *
            (params.xi : ℝ) * W) ≤
        (Ntail : ℝ) := by
    have htail_base :=
      htail (T := W) (sigma := sigma) hW_nonneg hsigma_pos hsigma_le
    have htail_factor_nonneg :
        0 ≤ (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
          |Real.log sigma| *
          Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W) := by
      have hlog_arg_ge_one :
          1 ≤ 2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W := by
        have hprod :
            0 ≤ sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W := by
          positivity
        calc
          (1 : ℝ) ≤ 2 := by norm_num
          _ ≤ 2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W :=
            le_add_of_nonneg_right hprod
      have hlog_nonneg :
          0 ≤ Real.log (2 + sigma⁻¹ ^ (4 : ℕ) *
              (params.xi : ℝ) * W) :=
        Real.log_nonneg hlog_arg_ge_one
      positivity
    have htail_C :
        Ctail * ((params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
            |Real.log sigma| *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W)) ≤
          C * ((params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
            |Real.log sigma| *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W)) :=
      mul_le_mul_of_nonneg_right hCtail_le_C htail_factor_nonneg
    have htail_upgraded :
        Cstep * (params.xi : ℝ) * ((sigma / 4)⁻¹ ^ (4 : ℕ)) *
            |Real.log (sigma / 4)| *
            Real.log (2 + (sigma / 4)⁻¹ ^ (4 : ℕ) *
              (params.xi : ℝ) * W) ≤
          C * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
            |Real.log sigma| *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W) := by
      calc
        Cstep * (params.xi : ℝ) * ((sigma / 4)⁻¹ ^ (4 : ℕ)) *
            |Real.log (sigma / 4)| *
            Real.log (2 + (sigma / 4)⁻¹ ^ (4 : ℕ) *
              (params.xi : ℝ) * W)
            ≤ Ctail * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
              |Real.log sigma| *
              Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W) :=
              htail_base
        _ = Ctail * ((params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
              |Real.log sigma| *
              Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W)) := by ring
        _ ≤ C * ((params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
              |Real.log sigma| *
              Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W)) :=
              htail_C
        _ = C * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
              |Real.log sigma| *
              Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W) := by ring
    have hceil_tail :
        C * (params.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) *
            |Real.log sigma| *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (params.xi : ℝ) * W) ≤
          (Ntail : ℝ) := by
      have hceil :=
        Nat.le_ceil
          (C * (hP4.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) * |Real.log sigma| *
            Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) *
              widetildeThetaAtScale P (0 : ℤ) hP4))
      simpa [Ntail, annealedConvergenceSigmaTailScale, W, hxi_eq] using hceil
    exact htail_upgraded.trans hceil_tail
  have hentry_le_N : Nentry ≤ N := by
    dsimp [N, annealedEntryScale, Nentry, Ntail]
    omega
  have hdiff_tail : (N - Nentry : ℕ) = Ntail := by
    dsimp [N, annealedEntryScale, Nentry, Ntail]
    omega
  have hfinal_step :
      thetaAtScale hP hStruct (N : ℤ) ≤
        1 + (sigma / 4) * thetaAtScale hP hStruct (Nentry : ℤ) := by
    exact
      hstep hP hStruct hP4 hparams hsigma4_pos hsigma4_le hentry_le_N
        (by
          simpa [W, hdiff_tail] using htail_gap_real)
  have hfinal :
      thetaAtScale hP hStruct (N : ℤ) ≤ 1 + sigma :=
    quarter_step_le_one_add_of_le_three hfinal_step hentry_theta_le_three hsigma_pos.le
  simpa [N] using hfinal

end

end Section55
end Ch05
end Book
end Homogenization
