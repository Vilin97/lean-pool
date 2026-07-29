/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.GammaFactor
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set

namespace NumberField.Odlyzko

theorem cpow_prod_of_nonneg {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i) (s : ℂ) :
    (((∏ i ∈ t, a i : ℝ) : ℂ) ^ s) =
      ∏ i ∈ t, ((a i : ℂ) ^ s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (ha i (Finset.mem_insert_self i t))
          (Finset.prod_nonneg fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)),
        Finset.prod_insert hi]
      simp_all

theorem integrableOn_cpow_mul_cexp_neg_mul_sq_Ioi
    {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn
      (fun x : ℝ ↦
        (x : ℂ) ^ (2 * s - 1) * Complex.exp (-(r * x ^ 2)))
      (Ioi 0) := by
  have hbase :
      MellinConvergent (fun t : ℝ ↦ Complex.exp (-(t : ℂ))) s := by
    rw [MellinConvergent]
    convert Complex.GammaIntegral_convergent hs using 1
    · ext t
      simp [mul_comm]
  have hscaled :
      MellinConvergent
        (fun t : ℝ ↦ Complex.exp (-((r * t : ℝ) : ℂ))) s := by
    simpa only [Complex.ofReal_mul] using
      (MellinConvergent.comp_mul_left (f :=
        fun t : ℝ ↦ Complex.exp (-(t : ℂ))) (s := s) hr).2 hbase
  have hsquare :
      MellinConvergent
        (fun t : ℝ ↦ Complex.exp (-((r * t ^ 2 : ℝ) : ℂ)))
        (2 * s) := by
    have h := (MellinConvergent.comp_rpow
      (f := fun t : ℝ ↦ Complex.exp (-((r * t : ℝ) : ℂ)))
      (s := 2 * s) (a := 2) (by norm_num)).2
    simp_all
  rw [MellinConvergent] at hsquare
  simp_all

theorem integral_cpow_mul_cexp_neg_mul_sq_Ioi
    {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0,
      (x : ℂ) ^ (2 * s - 1) * Complex.exp (-(r * x ^ 2))) =
      (2 : ℂ)⁻¹ * (1 / r : ℂ) ^ s * Complex.Gamma s := by
  have hsq := mellin_comp_rpow
    (f := fun t : ℝ ↦ Complex.exp (-(r * t))) (2 * s) 2
  rw [show (2 * s) / (2 : ℝ) = s by norm_num] at hsq
  have hgamma := integral_cpow_mul_exp_neg_mul_Ioi hs hr
  rw [mellin] at hsq
  rw [mellin] at hsq
  simp only [smul_eq_mul, Complex.real_smul] at hsq
  rw [hgamma] at hsq
  have htwo : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  simpa only [htwo, Complex.ofReal_inv, Complex.ofReal_ofNat,
    Complex.ofReal_pow, one_div, Real.rpow_two, mul_assoc] using hsq

theorem integral_complexPlaceGaussian
    {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0,
      (x : ℂ) ^ (2 * s - 1) *
        Complex.exp (-(((2 * Real.pi * a : ℝ) : ℂ) *
          (x : ℂ) ^ 2))) =
      (2 : ℂ)⁻¹ * (a : ℂ) ^ (-s) * CompletedZeta.complexPlaceGammaFactor s := by
  rw [integral_cpow_mul_cexp_neg_mul_sq_Ioi hs
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) ha)]
  have hinv {r : ℝ} (hr : 0 < r) :
      (1 / r : ℂ) ^ s = (r : ℂ) ^ (-s) := by
    rw [one_div,
      Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg hr.le]
        exact Real.pi_ne_zero.symm),
      Complex.cpow_neg]
  rw [hinv (mul_pos (mul_pos (by norm_num) Real.pi_pos) ha)]
  rw [show ((2 * Real.pi * a : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * (a : ℂ) by simp]
  rw [Complex.mul_cpow_ofReal_nonneg
    (mul_nonneg (by norm_num) Real.pi_pos.le) ha.le (-s)]
  rw [complexPlaceGammaFactor_eq]
  rw [show ((2 * Real.pi : ℝ) : ℂ) =
    2 * (Real.pi : ℂ) by simp]
  ring

theorem integral_pi_complexPlaceGaussian_eq_prod
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ι → ℝ,
      ∏ i,
        (x i : ℂ) ^ (2 * s - 1) *
          Complex.exp (-(((2 * Real.pi * a i : ℝ) : ℂ) *
            (x i : ℂ) ^ 2))
      ∂Measure.pi (fun _ ↦ volume.restrict (Ioi 0))) =
      ∏ i, (2 : ℂ)⁻¹ * (a i : ℂ) ^ (-s) *
        CompletedZeta.complexPlaceGammaFactor s := by
  calc
    _ = ∏ i, ∫ x : ℝ,
        (x : ℂ) ^ (2 * s - 1) *
          Complex.exp (-(((2 * Real.pi * a i : ℝ) : ℂ) *
            (x : ℂ) ^ 2))
        ∂volume.restrict (Ioi 0) :=
      integral_fintype_prod_eq_prod _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact integral_complexPlaceGaussian hs (ha i)

end NumberField.Odlyzko
