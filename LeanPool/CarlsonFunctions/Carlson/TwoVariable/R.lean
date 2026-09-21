/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.R.Basic
public import LeanPool.CarlsonFunctions.Carlson.TwoVariable.RPolynomial.Basic
public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegral.Continuation

/-! # The two-variable Carlson R-function -/

open Complex Filter
open scoped Classical Topology
@[expose] public noncomputable section CarlsonTwoVariable
namespace DirichletTransform.TwoVariable

/-- The two-variable integral at a natural exponent agrees with the Carlson polynomial. -/
theorem regRIntegral_natCast (n : ℕ) (b₀ b₁ z₀ z₁ : ℂ)
    (hb : pair b₀ b₁ ∈ mvBetaConvergent) :
    regRIntegral n b₀ b₁ z₀ z₁ = regRPolynomial n b₀ b₁ z₀ z₁ := by
  exact regCarlsonRIntegral_natCast n (pair z₀ z₁) hb

/-- Simultaneously exchanging the two parameters and variables leaves the native
regularized two-variable R-integral unchanged. -/
theorem regRIntegral_swap (t b₀ b₁ z₀ z₁ : ℂ) :
    regRIntegral t b₁ b₀ z₁ z₀ = regRIntegral t b₀ b₁ z₀ z₁ := by
  have h := regCarlsonDirichletAverage_perm (pair b₀ b₁) (pair z₀ z₁)
    (fun w => w ^ t) (Equiv.swap 0 1)
  rw [show pair b₀ b₁ ∘ Equiv.swap 0 1 = pair b₁ b₀ by
      funext i; fin_cases i <;> rfl,
    show pair z₀ z₁ ∘ Equiv.swap 0 1 = pair z₁ z₀ by
      funext i; fin_cases i <;> rfl] at h
  exact h

/-- Positive-real homogeneity of the native regularized two-variable R-integral. -/
theorem regRIntegral_smul_of_pos (t b₀ b₁ x y : ℂ) {a : ℝ} (ha : 0 < a)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    regRIntegral t b₀ b₁ ((a : ℂ) * x) ((a : ℂ) * y) =
      (a : ℂ) ^ t * regRIntegral t b₀ b₁ x y := by
  change regCarlsonRIntegral t (pair b₀ b₁)
      (pair ((a : ℂ) * x) ((a : ℂ) * y)) = _
  rw [show pair ((a : ℂ) * x) ((a : ℂ) * y) =
      fun i => (a : ℂ) * pair x y i by funext i; fin_cases i <;> rfl]
  exact DirichletTransform.regCarlsonRIntegral_smul_of_pos t hz ha

/-- The logarithmic base case in Carlson 8.5(2), without division by a node
difference. Thus the identity also holds on the diagonal. -/
theorem sub_mul_regRContinued_neg_one_one_one (x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) :
    (y - x) * regCarlsonRContinued (-1) (pair x y) hz (pair 1 1) = log y - log x := by
  let q : ℂ → ℝ → ℂ := fun z u => (1 - u : ℂ) + (u : ℂ) * z
  have hq (z : ℂ) (hz : 0 < z.re) {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
      q z u ∈ slitPlane := by
    apply carlsonRightHalfPlane_subset_slitPlane
    change 0 < ((1 - u : ℂ) + (u : ℂ) * z).re
    simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
    by_cases h : u = 0
    · simp [h]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hu.2)
        (mul_pos (lt_of_le_of_ne hu.1 (Ne.symm h)) hz)
  have hx : 0 < x.re := hz 0
  have hy : 0 < y.re := hz 1
  let K : ℝ → ℂ := fun u => (q x u)⁻¹ * (q y u)⁻¹
  have hK : ContinuousOn K (Set.Icc 0 1) := by
    apply ContinuousOn.mul
    · exact (by fun_prop : Continuous (q x)).continuousOn.inv₀
        (fun u hu => slitPlane_ne_zero (hq x hx hu))
    · exact (by fun_prop : Continuous (q y)).continuousOn.inv₀
        (fun u hu => slitPlane_ne_zero (hq y hy hu))
  have hd (z : ℂ) (u : ℝ) : HasDerivAt (q z) (z - 1) u := by
    have h := (hasDerivAt_id u).ofReal_comp
    simpa [q, Pi.add_def, Pi.sub_def, sub_eq_add_neg, add_comm] using
      ((hasDerivAt_const u (1 : ℂ)).sub h).add (h.mul_const z)
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => log (q y u) - log (q x u))
    (f' := fun u => (y - x) * K u) (a := (0 : ℝ)) (b := 1)
    (fun u hu => by
      rw [Set.uIcc_of_le zero_le_one] at hu
      have h := ((hd y u).clog_real (hq y hy hu)).sub ((hd x u).clog_real (hq x hx hu))
      have heq : (y - 1) / q y u - (x - 1) / q x u = (y - x) * K u := by
        dsimp only [K]
        have hqx := slitPlane_ne_zero (hq x hx hu)
        have hqy := slitPlane_ne_zero (hq y hy hu)
        field_simp
        dsimp only [q]
        ring
      rwa [heq] at h)
    ((hK.const_mul (y - x)).intervalIntegrable_of_Icc zero_le_one)
  have hI : carlsonRUnitIntervalIntegral 1 1 (pair 1 1) (pair x y) =
      regCarlsonRContinued (-1) (pair x y) hz (pair 1 1) := by
    simpa using carlsonRUnitIntervalIntegral_eq_gamma_mul_continued
      (a := 1) (a' := 1) (b := pair 1 1) (by norm_num) (by norm_num)
      (by simp) hz
  have hIK : carlsonRUnitIntervalIntegral 1 1 (pair 1 1) (pair x y) =
      ∫ u : ℝ in (0 : ℝ)..1, K u := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      ← MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc]
    simp [carlsonRUnitIntervalIntegral, K, q, Fin.prod_univ_two, pair, cpow_neg_one]
  rw [← hI, hIK]
  simpa [q, intervalIntegral.integral_const_mul] using H

/-- Carlson's logarithmic elementary function, for distinct nodes. -/
theorem regRContinued_neg_one_one_one (x y : ℂ)
    (hz : pair x y ∈ carlsonRVariableDomain) (hxy : x ≠ y) :
    regCarlsonRContinued (-1) (pair x y) hz (pair 1 1) =
      (log y - log x) / (y - x) := by
  apply (eq_div_iff (sub_ne_zero.mpr hxy.symm)).mpr
  simpa only [mul_comm] using sub_mul_regRContinued_neg_one_one_one x y hz

/-- The diagonal value completing the logarithmic base case. -/
theorem regRContinued_neg_one_one_one_diag (x : ℂ)
    (hz : pair x x ∈ carlsonRVariableDomain) :
    regCarlsonRContinued (-1) (pair x x) hz (pair 1 1) = x⁻¹ := by
  have hb : pair (1 : ℂ) 1 ∈ mvBetaConvergent := by
    intro i; fin_cases i <;> norm_num [pair]
  rw [regCarlsonRContinued_eq_integral _ hz hb]
  change regCarlsonDirichletAverage (pair 1 1) (pair x x)
    (fun w => w ^ (-1 : ℂ)) = _
  rw [show pair x x = (fun _ => x) by ext i; fin_cases i <;> rfl,
    regCarlsonDirichletAverage_const _ _ hb]
  simp [cpow_neg_one, Gamma_add_one 1 one_ne_zero]

end DirichletTransform.TwoVariable
end CarlsonTwoVariable
