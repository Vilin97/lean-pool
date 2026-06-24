/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.Bochner.Sazonov
import LeanPool.OSforGFF.Bochner.PositiveDefinite
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike

/-! # Sazonov Tightness

This module establishes that Sazonov-continuous characteristic functions
imply tightness of finite-dimensional marginals via Gaussian averaging,
spectral decomposition, and Chebyshev inequalities.

## Main definitions

- `SazonovContinuousAt`: Characteristic function continuity in the Sazonov topology
- `marginalFun`: Finite-dimensional marginal characteristic function

## Main statements

- `marginalFun_isPositiveDefinite`: Marginals of PD functions are PD
- `sazonov_tight_marginals`: Sazonov CF continuity implies tight marginals
- `sazonov_tight_marginals_apply`: Explicit tightness bound via Gaussian averaging
-/

open MeasureTheory Complex Filter Topology Set InnerProductSpace Function
open scoped Real FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ## Sazonov Continuity -/

/-- Sazonov continuity at 0: for every ε > 0, there exists a positive trace-class
    operator S such that ⟪x, Sx⟫ < 1 implies |1 - φ(x)| < ε.
-/
def SazonovContinuousAt (φ : H → ℂ) :=
  ∀ ε > 0, ∃ S : SazonovIndex H,
    ∀ x : H, quadForm S.op x < 1 → ‖1 - φ x‖ < ε

/-! ## Finite-Dimensional Marginals -/

/-- For a family v : Fin n → H, the marginal function
    φ_v(t) = φ(∑ i, t i • v i).
-/
def marginalFun (φ : H → ℂ) {n : ℕ} (v : Fin n → H) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun t => φ (∑ i, t i • v i)

omit [CompleteSpace H] in
/-- The marginal function of a PD function is PD. -/
lemma marginalFun_isPositiveDefinite (φ : H → ℂ) (hpd : IsPositiveDefinite φ)
    {n : ℕ} (v : Fin n → H) :
    IsPositiveDefinite (marginalFun φ v) := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] H := {
    toFun := fun t => ∑ i, t i • v i
    map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
    map_smul' := fun r x => by
      simp only [RingHom.id_apply]
      rw [Finset.smul_sum]
      congr 1; ext i
      simp [smul_smul, mul_comm r]
  }
  have key : marginalFun φ v = fun t => φ (T t) := by ext t; rfl
  rw [key]
  exact isPositiveDefinite_precomp_linear φ hpd T

/-! ## Tail Bound Algebra -/

/-- 1 - exp(-t) > 0 for t > 0. -/
lemma one_sub_exp_neg_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have h1 : Real.exp (-t) < 1 := by
    calc Real.exp (-t) < Real.exp 0 := Real.exp_strictMono (by linarith)
      _ = 1 := Real.exp_zero
  linarith

/-- exp(-b) ≤ exp(-a) when a ≤ b. -/
lemma exp_neg_le_exp_neg {a b : ℝ} (hab : a ≤ b) :
    Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp_of_le (neg_le_neg hab)

/-- The denominator 1 - exp(-R²/2) is positive for R > 0. -/
lemma one_sub_exp_half_sq_pos (R : ℝ) (hR : 0 < R) :
    0 < 1 - Real.exp (-(R ^ 2 / 2)) := by
  apply one_sub_exp_neg_pos; positivity

/-- Chebyshev/Markov bound with scaling: if ∫ (1 - exp(-σ²‖y‖²/2)) dμ ≤ C,
    then μ({‖y‖ ≥ R}) ≤ C / (1 - exp(-σ²R²/2)).
-/
lemma tail_bound_from_exp_integral {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : ProbabilityMeasure V) (σ : ℝ) (hσ : 0 < σ)
    (C : ℝ) (_hC0 : 0 ≤ C)
    (hC : ∫ y, (1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) ∂μ.toMeasure ≤ C)
    (R : ℝ) (hR : 0 < R) :
    (μ.toMeasure {y | R ≤ ‖y‖}).toReal ≤ C / (1 - Real.exp (-(σ ^ 2 * R ^ 2 / 2))) := by
  set δ := 1 - Real.exp (-(σ ^ 2 * R ^ 2 / 2)) with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    have : Real.exp (-(σ ^ 2 * R ^ 2 / 2)) < 1 := by
      calc Real.exp (-(σ ^ 2 * R ^ 2 / 2)) < Real.exp 0 :=
            Real.exp_strictMono (by linarith [show 0 < σ ^ 2 * R ^ 2 / 2 from by positivity])
        _ = 1 := Real.exp_zero
    linarith
  set A := {y : V | R ≤ ‖y‖}
  set f : V → ℝ := fun y => 1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))
  have hA_meas : MeasurableSet A :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hf_nn : ∀ y, 0 ≤ f y := by
    intro y; simp only [f]
    have : Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2)) ≤ Real.exp 0 :=
      Real.exp_le_exp_of_le (by linarith [show 0 ≤ σ ^ 2 * ‖y‖ ^ 2 / 2 from by positivity])
    rw [Real.exp_zero] at this; linarith
  have hf_ge_δ : ∀ y ∈ A, δ ≤ f y := by
    intro y hy
    simp only [A, mem_setOf_eq] at hy; simp only [f, hδ_def]
    have : σ ^ 2 * R ^ 2 / 2 ≤ σ ^ 2 * ‖y‖ ^ 2 / 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ 2)
      exact mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith) hy) (by positivity)
    linarith [Real.exp_le_exp_of_le (neg_le_neg this)]
  have hf_cont : Continuous f := by
    simp only [f]; apply continuous_const.sub
    exact Real.continuous_exp.comp (continuous_neg.comp
      ((continuous_const.mul (continuous_norm.pow 2)).div_const _))
  have hf_int : Integrable f μ.toMeasure := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hf_cont.aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_nn y)]
      simp only [f]; linarith [Real.exp_nonneg (-(σ ^ 2 * ‖y‖ ^ 2 / 2))]
  have key : δ * (μ.toMeasure A).toReal ≤ C :=
    calc δ * (μ.toMeasure A).toReal
        = ∫ _ in A, δ ∂μ.toMeasure := by
          simp only [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
      _ ≤ ∫ y in A, f y ∂μ.toMeasure :=
          setIntegral_mono_on (integrable_const δ).integrableOn
            hf_int.integrableOn hA_meas hf_ge_δ
      _ ≤ ∫ y, f y ∂μ.toMeasure :=
          setIntegral_le_integral hf_int (Eventually.of_forall hf_nn)
      _ ≤ C := hC
  exact (le_div_iff₀ hδ_pos).mpr (by linarith)

/-! ## The Gaussian Averaging Bound (with scaling parameter) -/

/-! ## Gaussian Averaging Infrastructure -/

section GaussianAveraging

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

/-- Centered Gaussian density profile with scale `σ`. -/
abbrev gaussDensity (σ : ℝ) (x : V) : ℝ :=
  Real.exp (-(1 / (2 * σ ^ 2)) * ‖x‖ ^ 2)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] in
lemma gaussDensity_nonneg' (σ : ℝ) (x : V) : 0 ≤ gaussDensity σ x :=
  Real.exp_nonneg _

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] in
lemma gaussDensity_continuous' (σ : ℝ) : Continuous (gaussDensity (V := V) σ) := by
  unfold gaussDensity; fun_prop

omit [SecondCountableTopology V] in
lemma gaussDensity_integrable' (σ : ℝ) (hσ : 0 < σ) :
    Integrable (gaussDensity σ) (volume : Measure V) := by
  set b : ℝ := 1 / (2 * σ ^ 2)
  have hb : 0 < b := by positivity
  have hcint : Integrable (fun x : V => cexp (-(b : ℂ) * ↑(‖x‖ ^ 2))) := by
    have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (show 0 < ((b : ℂ)).re by simp [hb]) (0 : ℂ) (0 : V)
    simp only [neg_mul] at this
    convert this using 1
    ext x
    simp [Complex.ofReal_pow]
  have heq : gaussDensity (V := V) σ = fun x => ‖cexp (-(b : ℂ) * ↑(‖x‖ ^ 2))‖ := by
    ext x; unfold gaussDensity; rw [Complex.norm_exp]; congr 1
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]; ring
  rw [heq]; exact hcint.norm

omit [SecondCountableTopology V] in
lemma gaussDensity_integral_pos' (σ : ℝ) (hσ : 0 < σ) :
    0 < ∫ x : V, gaussDensity σ x := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0)
    (gaussDensity_continuous' σ) (gaussDensity_integrable' σ hσ)
    (fun x => gaussDensity_nonneg' σ x)
    (ne_of_gt (Real.exp_pos _))

omit [SecondCountableTopology V] in
private lemma gaussian_fourier_eq' (σ : ℝ) (hσ : 0 < σ) (y : V) :
    ∫ x : V, (gaussDensity σ x : ℂ) * cexp (↑(@inner ℝ V _ y x) * I) =
    ↑(∫ x : V, gaussDensity σ x) * cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ)) := by
  set b : ℝ := 1 / (2 * σ ^ 2) with hb_def
  have hb : 0 < b := by positivity
  have hb_re : 0 < ((b : ℂ)).re := by simp [hb]
  have step1 : (∫ x : V, (gaussDensity σ x : ℂ) * cexp (↑(@inner ℝ V _ y x) * I)) =
      ∫ x : V, cexp (-(b : ℂ) * ‖x‖ ^ 2 + I * ↑⟪y, x⟫_ℝ) := by
    congr 1; ext x
    rw [Complex.ofReal_exp, mul_comm (↑⟪y, x⟫_ℝ) I, ← exp_add]; congr 1
    rw [show (-(1 / (2 * σ ^ 2)) * ‖x‖ ^ 2 : ℝ) = -b * ‖x‖ ^ 2 from by rw [hb_def]]
    push_cast; ring
  rw [step1, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb_re I y]
  set n := Module.finrank ℝ V
  congr 1
  · have hgd : (∫ x : V, gaussDensity σ x) = (π / b) ^ ((n : ℝ) / 2) := by
      rw [show (∫ x : V, gaussDensity σ x) = ∫ x : V, Real.exp (-b * ‖x‖ ^ 2) from by
        congr 1]
      exact GaussianFourier.integral_rexp_neg_mul_sq_norm hb
    rw [hgd, ← Complex.ofReal_natCast n, ← Complex.ofReal_ofNat 2,
      ← Complex.ofReal_div, ← Complex.ofReal_div]
    exact (Complex.ofReal_cpow (le_of_lt (by positivity : (0 : ℝ) < π / b)) _).symm
  · congr 1; rw [I_sq]
    rw [show (b : ℂ) = 1 / (2 * (σ : ℂ) ^ 2) from by rw [hb_def]; push_cast; ring]
    push_cast; field_simp; ring

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [SecondCountableTopology V] in
private lemma exp_neg_sq_integrable_prob' (μ : ProbabilityMeasure V) (σ : ℝ) (_hσ : 0 < σ) :
    Integrable (fun y : V => Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) μ.toMeasure := by
  apply (integrable_const (1 : ℝ)).mono'
    (by fun_prop : Continuous (fun y : V =>
      Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2)))).aestronglyMeasurable
  filter_upwards with y
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  rw [← Real.exp_zero]
  exact Real.exp_le_exp_of_le (by nlinarith [sq_nonneg σ, sq_nonneg ‖y‖])

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [SecondCountableTopology V] in
private lemma cexp_neg_sq_integrable_prob' (μ : ProbabilityMeasure V) (σ : ℝ) (_hσ : 0 < σ) :
    Integrable (fun y : V => cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ))) μ.toMeasure := by
  have : (fun y : V => cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ))) =
      fun y => (Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2)) : ℂ) := by
    ext y; rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rw [this]
  exact (exp_neg_sq_integrable_prob' μ σ ‹_›).ofReal

lemma gaussDensity_mul_charFun_re_integrable' (μ : ProbabilityMeasure V)
    (φ : V → ℂ) (hφ : ∀ t, charFun μ.toMeasure t = φ t) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun x : V => gaussDensity σ x * (φ x).re) volume := by
  have heq : (fun x => gaussDensity σ x * (φ x).re) =
      fun x => gaussDensity σ x * (charFun μ.toMeasure x).re := by
    ext x; rw [hφ]
  rw [heq]
  apply Integrable.mono' (gaussDensity_integrable' σ hσ)
    (((by fun_prop : Measurable (gaussDensity (V := V) σ)).mul
      (Measurable.re measurable_charFun)).aestronglyMeasurable)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg' σ x)]
  exact mul_le_of_le_one_right (gaussDensity_nonneg' σ x)
    (abs_re_le_norm _ |>.trans (norm_charFun_le_one (μ := μ.toMeasure) x))

private lemma gaussDensity_mul_charFun_integrable' (μ : ProbabilityMeasure V)
    (φ : V → ℂ) (hφ : ∀ t, charFun μ.toMeasure t = φ t) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun x : V => (gaussDensity σ x : ℂ) * φ x) volume := by
  have heq : (fun x => (gaussDensity σ x : ℂ) * φ x) =
      fun x => (gaussDensity σ x : ℂ) * charFun μ.toMeasure x := by
    ext x; rw [hφ]
  rw [heq]
  apply Integrable.mono' (gaussDensity_integrable' σ hσ)
    ((Complex.measurable_ofReal.comp (by fun_prop : Measurable (gaussDensity (V := V) σ))
      |>.mul measurable_charFun).aestronglyMeasurable)
  filter_upwards with x
  simp only [Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gaussDensity_nonneg' σ x)]
  exact mul_le_of_le_one_right (gaussDensity_nonneg' σ x)
    (norm_charFun_le_one (μ := μ.toMeasure) x)

/-- Fubini identity for Gaussian averaging:
    ∫_μ (1-exp(-σ²‖y‖²/2)) = C⁻¹ ∫ exp(-b‖x‖²) Re(1-φ(x)) dx.
-/
theorem fubini_gaussian_charFun
    (μ : ProbabilityMeasure V) (φ : V → ℂ)
    (hφ : ∀ t, charFun μ.toMeasure t = φ t) (σ : ℝ) (hσ : 0 < σ) :
    ∫ y, (1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) ∂μ.toMeasure =
    (∫ x : V, gaussDensity σ x)⁻¹ *
      ∫ x : V, gaussDensity σ x * (1 - (φ x).re) := by
  set C := ∫ x : V, gaussDensity σ x
  have hC_pos : 0 < C := gaussDensity_integral_pos' σ hσ
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hexp_int := exp_neg_sq_integrable_prob' μ σ hσ
  have hcexp_int := cexp_neg_sq_integrable_prob' μ σ hσ
  have hgdre_int := gaussDensity_mul_charFun_re_integrable' μ φ hφ σ hσ
  have hgdphi_int := gaussDensity_mul_charFun_integrable' μ φ hφ σ hσ
  have norm_bound : ∀ y x : V,
      ‖(gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I)‖ = gaussDensity σ x := by
    intro y x
    rw [norm_mul, Complex.norm_real, Complex.norm_exp,
      show (↑⟪y, x⟫_ℝ * I : ℂ).re = 0 from by simp [Complex.mul_re], Real.exp_zero,
      mul_one, Real.norm_eq_abs, abs_of_nonneg (gaussDensity_nonneg' σ x)]
  suffices key : C * ∫ y, Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2)) ∂μ.toMeasure =
      ∫ x, gaussDensity σ x * (φ x).re by
    rw [integral_sub (integrable_const 1) hexp_int]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    rw [show (fun x : V => gaussDensity σ x * (1 - (φ x).re)) =
      (fun x => gaussDensity σ x - gaussDensity σ x * (φ x).re) from by ext x; ring]
    rw [integral_sub (gaussDensity_integrable' σ hσ) hgdre_int,
      mul_sub, inv_mul_cancel₀ hC_ne]
    congr 1
    rw [← key, ← mul_assoc, inv_mul_cancel₀ hC_ne, one_mul]
  -- Product integrability
  have hprod : Integrable (uncurry (fun (y : V) (x : V) =>
      (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I)))
      (μ.toMeasure.prod volume) := by
    rw [integrable_prod_iff
      (by fun_prop : Continuous (uncurry fun (y : V) (x : V) =>
        (↑(gaussDensity σ x) : ℂ) * cexp (↑⟪y, x⟫_ℝ * I))).aestronglyMeasurable]
    constructor
    · filter_upwards with y
      apply Integrable.mono' (gaussDensity_integrable' σ hσ)
        (by fun_prop : Continuous (fun x : V =>
          (↑(gaussDensity σ x) : ℂ) * cexp (↑⟪y, x⟫_ℝ * I))).aestronglyMeasurable
      filter_upwards with x
      rw [norm_bound]
    · have : (fun y : V => ∫ x, ‖uncurry (fun (y : V) (x : V) =>
            (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I)) (y, x)‖ ∂volume) =
          fun _ => ∫ x : V, gaussDensity σ x := by
        ext y; congr 1; ext x
        simp only [Function.uncurry_apply_pair, norm_bound]
      rw [this]; exact integrable_const _
  have fubini := integral_integral_swap hprod
  have lhs_eq : ∫ y, (∫ x, (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I)) ∂μ.toMeasure =
      ↑C * ∫ y, cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ)) ∂μ.toMeasure := by
    trans ∫ y, (↑C : ℂ) * cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ)) ∂μ.toMeasure
    · congr 1; ext y; exact gaussian_fourier_eq' σ hσ y
    · exact integral_const_mul _ _
  have rhs_eq : ∫ x, (∫ y, (gaussDensity σ x : ℂ) * cexp (↑⟪y, x⟫_ℝ * I) ∂μ.toMeasure) =
      ∫ x, (gaussDensity σ x : ℂ) * φ x := by
    congr 1; ext x
    trans (↑(gaussDensity σ x) : ℂ) * ∫ y, cexp (↑⟪y, x⟫_ℝ * I) ∂μ.toMeasure
    · exact integral_const_mul _ _
    · congr 1
      show ∫ y, cexp (↑⟪y, x⟫_ℝ * I) ∂μ.toMeasure = φ x
      rw [← hφ x]; rfl
  have key_complex : ↑C * ∫ y, cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ)) ∂μ.toMeasure =
      ∫ x, (gaussDensity σ x : ℂ) * φ x := by
    rw [← lhs_eq, fubini, rhs_eq]
  have integral_re_eq : ∀ {f : V → ℂ} {ν : Measure V}, Integrable f ν →
      (∫ x, f x ∂ν).re = ∫ x, (f x).re ∂ν := by
    intro f ν hf
    exact (Complex.reCLM.integral_comp_comm hf).symm
  calc C * ∫ y, Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2)) ∂μ.toMeasure
      = (↑C * ∫ y, cexp (-(σ ^ 2 * ‖y‖ ^ 2 / 2 : ℝ)) ∂μ.toMeasure).re := by
        rw [re_ofReal_mul]; congr 1
        rw [integral_re_eq hcexp_int]
        congr 1; ext y
        rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re]
    _ = (∫ x, (gaussDensity σ x : ℂ) * φ x).re := by rw [key_complex]
    _ = ∫ x, gaussDensity σ x * (φ x).re := by
        rw [integral_re_eq hgdphi_int]
        congr 1; ext x; exact re_ofReal_mul _ _

omit [SecondCountableTopology V] in
/-- The real Gaussian integral formula as a function of parameter c. -/
private lemma gaussian_real_formula' (b : ℝ) (hb : 0 < b) (w : V) (c : ℝ) :
    ∫ x : V, Real.exp (-b * ‖x‖ ^ 2 + c * @inner ℝ V _ w x) =
    (∫ x : V, Real.exp (-b * ‖x‖ ^ 2)) * Real.exp (c ^ 2 * ‖w‖ ^ 2 / (4 * b)) := by
  have hb_re : 0 < ((b : ℂ)).re := by simp [hb]
  rw [← Complex.ofReal_inj, Complex.ofReal_mul, Complex.ofReal_exp]
  have lift1 : (↑(∫ x : V, rexp (-b * ‖x‖ ^ 2 + c * ⟪w, x⟫_ℝ)) : ℂ) =
      ∫ x : V, cexp (-(b : ℂ) * ‖x‖ ^ 2 + ↑c * ↑⟪w, x⟫_ℝ) := by
    change ofRealLI (∫ x, _) = _
    rw [← ofRealLI.integral_comp_comm]
    congr 1; ext x; simp [ofRealLI, Complex.ofReal_exp]
  have lift0 : (↑(∫ x : V, rexp (-b * ‖x‖ ^ 2)) : ℂ) =
      ∫ x : V, cexp (-(b : ℂ) * ‖x‖ ^ 2) := by
    change ofRealLI (∫ x, _) = _
    rw [← ofRealLI.integral_comp_comm]
    congr 1; ext x; simp [ofRealLI, Complex.ofReal_exp]
  rw [lift1, lift0]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb_re (c : ℂ) w,
    GaussianFourier.integral_cexp_neg_mul_sq_norm hb_re]
  congr 1; push_cast; ring

private lemma id_le_sinh' {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.sinh t := by
  have hmono : MonotoneOn (fun x => Real.sinh x - x) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (Real.continuous_sinh.sub continuous_id).continuousOn
    · intro x _
      exact ((Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)).differentiableAt.differentiableWithinAt
    · intro x _
      have hd : HasDerivAt (fun y => Real.sinh y - y) (Real.cosh x - 1) x :=
        (Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)
      rw [hd.deriv]
      linarith [Real.one_le_cosh x]
  have h0 : Real.sinh 0 - 0 = 0 := by simp [Real.sinh_zero]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  linarith [h0]

private lemma half_sq_le_cosh_sub_one' (x : ℝ) : x ^ 2 / 2 ≤ Real.cosh x - 1 := by
  suffices key : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 by
    have h1 := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x from by ring] at h1
    nlinarith [Real.cosh_sq (x / 2)]
  set t := x / 2
  suffices h : 0 ≤ (Real.sinh t + t) * (Real.sinh t - t) by nlinarith [sq_sub_sq (Real.sinh t) t]
  by_cases ht : 0 ≤ t
  · have h1 := id_le_sinh' ht
    exact mul_nonneg (by linarith) (by linarith)
  · push Not at ht
    have h1 : Real.sinh t ≤ t := by
      have := id_le_sinh' (by linarith : 0 ≤ -t)
      rw [Real.sinh_neg] at this; linarith
    have h2 : Real.sinh t ≤ 0 := by
      have := id_le_sinh' (by linarith : 0 ≤ -t)
      rw [Real.sinh_neg] at this; linarith
    have ha : Real.sinh t + t ≤ 0 := by linarith
    have hb : Real.sinh t - t ≤ 0 := by linarith
    exact mul_nonneg_of_nonpos_of_nonpos ha hb

omit [SecondCountableTopology V] in
private lemma gaussDensity_mul_exp_inner_integrable' (σ : ℝ) (hσ : 0 < σ) (w : V) (c : ℝ) :
    Integrable (fun x : V => gaussDensity σ x * rexp (c * @inner ℝ V _ w x)) volume := by
  set b := 1 / (2 * σ ^ 2)
  have hb : 0 < b := by positivity
  have hb_re : 0 < ((b : ℂ)).re := by simp [hb]
  have hci := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb_re (c : ℂ) w
  rw [show (fun x : V => gaussDensity σ x * rexp (c * @inner ℝ V _ w x)) =
    fun x => rexp (-b * ‖x‖ ^ 2 + c * @inner ℝ V _ w x) from by
    ext x; unfold gaussDensity; rw [← Real.exp_add]]
  have : (fun x : V => rexp (-b * ‖x‖ ^ 2 + c * @inner ℝ V _ w x)) =
      fun x => ‖cexp (-(b : ℂ) * ‖x‖ ^ 2 + ↑c * ↑⟪w, x⟫_ℝ)‖ := by
    ext x; rw [Complex.norm_exp]
    congr 1
    have : (-(b : ℂ) * ↑‖x‖ ^ 2 + ↑c * ↑⟪w, x⟫_ℝ) = ↑(-b * ‖x‖ ^ 2 + c * ⟪w, x⟫_ℝ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [this]; exact hci.norm

omit [SecondCountableTopology V] in
private lemma gaussDensity_exp_inner_integral' (σ : ℝ) (hσ : 0 < σ) (w : V) (c : ℝ) :
    ∫ x : V, gaussDensity σ x * rexp (c * @inner ℝ V _ w x) =
    (∫ x : V, gaussDensity σ x) * rexp (c ^ 2 * σ ^ 2 * ‖w‖ ^ 2 / 2) := by
  set b := 1 / (2 * σ ^ 2) with hb_def
  have hb : 0 < b := by positivity
  have h := gaussian_real_formula' b hb w c
  have lhs_eq : (fun x : V => gaussDensity σ x * rexp (c * @inner ℝ V _ w x)) =
      fun x => rexp (-b * ‖x‖ ^ 2 + c * @inner ℝ V _ w x) := by
    ext x; unfold gaussDensity; rw [← Real.exp_add]
  have rhs_eq : c ^ 2 * σ ^ 2 * ‖w‖ ^ 2 / 2 = c ^ 2 * ‖w‖ ^ 2 / (4 * b) := by
    rw [hb_def]; field_simp; ring
  rw [lhs_eq, h, rhs_eq]

private lemma tendsto_exp_slope' (A : ℝ) :
    Filter.Tendsto (fun t => (rexp (t * A) - 1) / t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds A) := by
  have hd : HasDerivAt (fun t => rexp (t * A) - 1) A 0 := by
    have h1 : HasDerivAt (fun t => rexp (t * A)) A 0 := by
      have := (Real.hasDerivAt_exp (0 * A)).comp (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).mul_const A)
      change HasDerivAt (fun t : ℝ => rexp (t * A)) A 0
      simpa [zero_mul, Real.exp_zero, Function.comp_def] using this
    have h2 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 := hasDerivAt_const 0 1
    have h := h1.sub h2
    rwa [sub_zero] at h
  have := hd.tendsto_slope_zero_right
  simp only [zero_add, zero_mul, Real.exp_zero, sub_self, sub_zero] at this
  exact this.congr fun t => by rw [smul_eq_mul, ← div_eq_inv_mul]

omit [SecondCountableTopology V] in
private lemma gaussDensity_mul_cosh_integrable' (σ : ℝ) (hσ : 0 < σ) (w : V) (c : ℝ) :
    Integrable (fun x : V => gaussDensity σ x * Real.cosh (c * @inner ℝ V _ w x)) volume := by
  have : (fun x : V => gaussDensity σ x * Real.cosh (c * @inner ℝ V _ w x)) =
      fun x => (gaussDensity σ x * rexp (c * @inner ℝ V _ w x) +
        gaussDensity σ x * rexp (-(c * @inner ℝ V _ w x))) / 2 := by
    ext x; rw [Real.cosh_eq]; ring
  rw [this]
  apply Integrable.div_const
  have : (fun x : V => gaussDensity σ x * rexp (c * @inner ℝ V _ w x) +
      gaussDensity σ x * rexp (-(c * @inner ℝ V _ w x))) =
    fun x => gaussDensity σ x * rexp (c * @inner ℝ V _ w x) +
      gaussDensity σ x * rexp ((-c) * @inner ℝ V _ w x) := by
    ext x; congr 1; congr 1; ring_nf
  rw [this]
  exact (gaussDensity_mul_exp_inner_integrable' σ hσ w c).add
    (gaussDensity_mul_exp_inner_integrable' σ hσ w (-c))

omit [SecondCountableTopology V] in
private lemma gaussDensity_cosh_integral' (σ : ℝ) (hσ : 0 < σ) (w : V) (c : ℝ) :
    ∫ x : V, gaussDensity σ x * Real.cosh (c * @inner ℝ V _ w x) =
    (∫ x : V, gaussDensity σ x) * rexp (c ^ 2 * σ ^ 2 * ‖w‖ ^ 2 / 2) := by
  have step1 : (fun x : V => gaussDensity σ x * Real.cosh (c * @inner ℝ V _ w x)) =
      fun x => (gaussDensity σ x * rexp (c * @inner ℝ V _ w x) +
        gaussDensity σ x * rexp (-(c * @inner ℝ V _ w x))) / 2 := by
    ext x; rw [Real.cosh_eq]; ring
  have hint_neg : Integrable (fun x : V => gaussDensity σ x *
      rexp (-(c * @inner ℝ V _ w x))) volume :=
    (gaussDensity_mul_exp_inner_integrable' σ hσ w (-c)).congr
      (Eventually.of_forall fun x => by show _ = _; ring_nf)
  rw [step1, integral_div, integral_add
    (gaussDensity_mul_exp_inner_integrable' σ hσ w c) hint_neg]
  have hrw : ∫ x : V, gaussDensity σ x * rexp (-(c * @inner ℝ V _ w x)) =
      ∫ x : V, gaussDensity σ x * rexp ((-c) * @inner ℝ V _ w x) :=
    integral_congr_ae (Eventually.of_forall fun x => by ring_nf)
  rw [gaussDensity_exp_inner_integral' σ hσ w c, hrw,
    gaussDensity_exp_inner_integral' σ hσ w (-c),
    show (-c) ^ 2 = c ^ 2 from by ring]; ring

private lemma gaussDensity_mul_inner_sq_integrable' (σ : ℝ) (hσ : 0 < σ) (w : V) :
    Integrable (fun x : V => gaussDensity σ x * (@inner ℝ V _ w x) ^ 2) volume := by
  apply ((gaussDensity_mul_cosh_integrable' σ hσ w 1).const_mul 2).mono'
    (by fun_prop : AEStronglyMeasurable
      (fun x : V => gaussDensity σ x * (@inner ℝ V _ w x) ^ 2) volume)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg' σ x)]
  change gaussDensity σ x * |(@inner ℝ V _ w x) ^ 2| ≤
    2 * (gaussDensity σ x * Real.cosh (1 * @inner ℝ V _ w x))
  rw [abs_of_nonneg (sq_nonneg _), one_mul]
  nlinarith [half_sq_le_cosh_sub_one' (@inner ℝ V _ w x),
    Real.one_le_cosh (@inner ℝ V _ w x),
    gaussDensity_nonneg' σ x, Real.cosh_pos (@inner ℝ V _ w x)]

private lemma gaussian_inner_sq_le' (σ : ℝ) (hσ : 0 < σ) (w : V) :
    ∫ x : V, gaussDensity σ x * (@inner ℝ V _ w x) ^ 2 ≤
    (∫ x : V, gaussDensity σ x) * (σ ^ 2 * ‖w‖ ^ 2) := by
  set C := ∫ x : V, gaussDensity σ x
  set I := ∫ x : V, gaussDensity σ x * (@inner ℝ V _ w x) ^ 2
  set A := σ ^ 2 * ‖w‖ ^ 2 / 2 with hA_def
  have hC_pos : 0 < C := gaussDensity_integral_pos' σ hσ
  have step1 : ∀ t : ℝ, 0 < t → I ≤ 2 * C * (rexp (t * A) - 1) / t := by
    intro t ht
    rw [le_div_iff₀ ht, mul_comm I t]
    set c := Real.sqrt t
    have hc : c ^ 2 = t := Real.sq_sqrt (le_of_lt ht)
    have htI : t * I = ∫ x : V, gaussDensity σ x * (c * @inner ℝ V _ w x) ^ 2 := by
      rw [show t = c ^ 2 from hc.symm, ← integral_const_mul]; congr 1; ext x; ring
    rw [htI]
    calc ∫ x, gaussDensity σ x * (c * @inner ℝ V _ w x) ^ 2
        ≤ ∫ x, gaussDensity σ x * (2 * (Real.cosh (c * @inner ℝ V _ w x) - 1)) := by
          apply integral_mono
            ((gaussDensity_mul_inner_sq_integrable' σ hσ w).const_mul (c ^ 2) |>.congr
              (Eventually.of_forall fun x => by show _ = _; ring))
            ((gaussDensity_mul_cosh_integrable' σ hσ w c).sub
              (gaussDensity_integrable' σ hσ) |>.const_mul 2 |>.congr
              (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring))
            fun x => mul_le_mul_of_nonneg_left
              (by nlinarith [half_sq_le_cosh_sub_one' (c * @inner ℝ V _ w x)])
              (gaussDensity_nonneg' σ x)
      _ = 2 * C * (rexp (t * A) - 1) := by
          have step_a : ∫ x : V, gaussDensity σ x *
              (2 * (Real.cosh (c * @inner ℝ V _ w x) - 1)) =
              2 * ∫ x : V, (gaussDensity σ x * Real.cosh (c * @inner ℝ V _ w x) -
                gaussDensity σ x) := by
            rw [← integral_const_mul]; congr 1; ext x; ring
          rw [step_a, integral_sub (gaussDensity_mul_cosh_integrable' σ hσ w c)
            (gaussDensity_integrable' σ hσ), gaussDensity_cosh_integral' σ hσ w c, hc]
          have : rexp (t * σ ^ 2 * ‖w‖ ^ 2 / 2) = rexp (t * A) := by congr 1; rw [hA_def]; ring
          rw [this]; ring
  have step2 : Filter.Tendsto (fun t => 2 * C * (rexp (t * A) - 1) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (C * (σ ^ 2 * ‖w‖ ^ 2))) := by
    have htarget : C * (σ ^ 2 * ‖w‖ ^ 2) = 2 * C * A := by rw [hA_def]; ring
    rw [htarget]
    have : (fun t => 2 * C * (rexp (t * A) - 1) / t) =
        (fun t => 2 * C * ((rexp (t * A) - 1) / t)) := by ext t; ring
    rw [this]
    exact (tendsto_exp_slope' A).const_mul (2 * C)
  exact ge_of_tendsto step2 (eventually_nhdsWithin_of_forall fun t ht => step1 t ht)

/-- Gaussian second moment bound:
    C⁻¹ ∫ exp(-b‖x‖²) ⟪x,Sx⟫ dx ≤ σ²·Tr(S).
    Uses spectral decomposition to reduce to single-direction bounds.
-/
theorem gaussian_quadForm_integral_le
    (σ : ℝ) (hσ : 0 < σ)
    (S : V →L[ℝ] V) (hS : S.IsPositive)
    (T : ℝ) (_hT : 0 ≤ T)
    (h_trace : ∀ (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ V),
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ T) :
    (∫ x : V, gaussDensity σ x)⁻¹ *
      ∫ x : V, gaussDensity σ x * quadForm S x ≤ σ ^ 2 * T := by
  set C := ∫ x : V, gaussDensity σ x
  have hC_pos : 0 < C := gaussDensity_integral_pos' σ hσ
  set n := Module.finrank ℝ V
  -- Spectral decomposition
  have hLPos : (S : V →ₗ[ℝ] V).IsPositive := hS.toLinearMap
  have hSym := hLPos.isSymmetric
  set b := hSym.eigenvectorBasis rfl
  set ev := hSym.eigenvalues rfl
  have hevnonneg : ∀ i, 0 ≤ ev i := hLPos.nonneg_eigenvalues rfl
  -- Key: ⟪e_i, Sx⟫ = λ_i * ⟪e_i, x⟫
  have hinner : ∀ (i : Fin n) (x : V),
      @inner ℝ V _ (b i) ((S : V →ₗ[ℝ] V) x) = ev i * @inner ℝ V _ (b i) x := by
    intro i x
    have := hSym.eigenvectorBasis_apply_self_apply rfl x i
    rwa [b.repr_apply_apply, b.repr_apply_apply] at this
  -- quadForm S x = ∑ᵢ λᵢ * ⟪b i, x⟫²
  have hqf : ∀ x : V, quadForm S x = ∑ i, ev i * (@inner ℝ V _ (b i) x) ^ 2 := by
    intro x; change @inner ℝ V _ x (S x) = _
    conv_lhs => rw [show (S : V →L[ℝ] V) x = (S : V →ₗ[ℝ] V) x from rfl]
    rw [← b.sum_inner_mul_inner x ((S : V →ₗ[ℝ] V) x)]
    congr 1; ext i; rw [hinner, real_inner_comm x (b i)]; ring
  -- ∫ gD * quadForm S = ∑ᵢ λᵢ * ∫ gD * ⟪b i, ·⟫²
  have hint_eq : ∫ x, gaussDensity σ x * quadForm S x =
      ∑ i, ev i * ∫ x, gaussDensity σ x * (@inner ℝ V _ (b i) x) ^ 2 := by
    simp_rw [hqf, Finset.mul_sum]
    rw [integral_finsetSum]
    · congr 1; ext i; rw [← integral_const_mul]; congr 1; ext x; ring
    · intro i _
      exact (gaussDensity_mul_inner_sq_integrable' σ hσ (b i)).const_mul (ev i) |>.congr
        (Eventually.of_forall fun x => by ring)
  have hbound : ∀ i, ∫ x : V, gaussDensity σ x * (@inner ℝ V _ (b i) x) ^ 2 ≤
      C * (σ ^ 2 * ‖b i‖ ^ 2) :=
    fun i => gaussian_inner_sq_le' σ hσ (b i)
  have hnorm : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have heveq : ∀ i, ev i = @inner ℝ V _ (b i) (S (b i)) := by
    intro i
    have h := hinner i (b i)
    rw [real_inner_self_eq_norm_sq, hnorm i, one_pow, mul_one] at h
    exact h.symm
  rw [hint_eq]
  have hbound' : ∀ i, ∫ x : V, gaussDensity σ x * (@inner ℝ V _ (b i) x) ^ 2 ≤
      C * σ ^ 2 := by
    intro i; have := hbound i; rw [hnorm i, one_pow, mul_one] at this; exact this
  calc C⁻¹ * ∑ i, ev i * ∫ x, gaussDensity σ x * (@inner ℝ V _ (b i) x) ^ 2
      ≤ C⁻¹ * ∑ i, ev i * (C * σ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hC_pos))
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hbound' i) (hevnonneg i)
    _ = σ ^ 2 * ∑ i, ev i := by
        trans C⁻¹ * ((C * σ ^ 2) * ∑ i, ev i)
        · congr 1; simp_rw [mul_comm (ev _) _]; rw [← Finset.mul_sum]
        · rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hC_pos), one_mul]
    _ = σ ^ 2 * ∑ i, @inner ℝ V _ (b i) (S (b i)) := by
        congr 1; exact Finset.sum_congr rfl fun i _ => heveq i
    _ ≤ σ ^ 2 * T := by
        have htrace : ∑ i : Fin n, @inner ℝ V _ (b i) (S (b i)) ≤ T := by
          have h := h_trace (ULift (Fin n)) (b.reindex Equiv.ulift.symm)
          simp only [OrthonormalBasis.reindex_apply, Equiv.symm_symm] at h
          rwa [Equiv.sum_comp Equiv.ulift
            (fun i => @inner ℝ V _ (b i) (S (b i)))] at h
        exact mul_le_mul_of_nonneg_left htrace (sq_nonneg σ)

private lemma mul_exp_neg_le_one' {t : ℝ} (_ht : 0 ≤ t) : t * Real.exp (-t) ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos t)]
  linarith [Real.add_one_le_exp t]

omit [SecondCountableTopology V] in
lemma gaussDensity_mul_quadForm_integrable' (σ : ℝ) (hσ : 0 < σ)
    (S : V →L[ℝ] V) :
    Integrable (fun x => gaussDensity σ x * quadForm S x) volume := by
  set b := 1 / (2 * σ ^ 2) with hb_def
  have hb : 0 < b := by positivity
  set C := ‖S‖ * (2 / b)
  have hC : 0 ≤ C := by positivity
  have hbound_int : Integrable (fun x : V => C * Real.exp (-(b / 2) * ‖x‖ ^ 2)) volume := by
    apply Integrable.const_mul
    have h := gaussDensity_integrable' (V := V) (σ * Real.sqrt 2) (by positivity)
    unfold gaussDensity at h
    convert h using 1; ext x; congr 1
    rw [mul_pow, Real.sq_sqrt (by positivity : (2 : ℝ) ≥ 0)]; ring
  have hqf_cont : Continuous (fun x : V => quadForm S x) := by unfold quadForm; fun_prop
  apply hbound_int.mono'
  · exact ((gaussDensity_continuous' σ).mul hqf_cont).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDensity_nonneg' σ x)]
    have hqf_bound : |quadForm S x| ≤ ‖S‖ * ‖x‖ ^ 2 := by
      unfold quadForm
      calc |@inner ℝ V _ x (S x)| ≤ ‖x‖ * ‖S x‖ := abs_real_inner_le_norm x (S x)
        _ ≤ ‖x‖ * (‖S‖ * ‖x‖) :=
            mul_le_mul_of_nonneg_left (S.le_opNorm x) (norm_nonneg _)
        _ = ‖S‖ * ‖x‖ ^ 2 := by ring
    have hgsq_bound : gaussDensity σ x * ‖x‖ ^ 2 ≤
        (2 / b) * Real.exp (-(b / 2) * ‖x‖ ^ 2) := by
      unfold gaussDensity
      set s := ‖x‖ ^ 2
      have hs : 0 ≤ s := sq_nonneg _
      have h_split : Real.exp (-(1 / (2 * σ ^ 2)) * s) =
          Real.exp (-(b / 2) * s) * Real.exp (-(b / 2) * s) := by
        rw [← Real.exp_add]; congr 1; rw [hb_def]; ring
      rw [h_split]
      have hexp_nn := (Real.exp_pos (-(b / 2) * s)).le
      have key := mul_exp_neg_le_one' (show 0 ≤ b / 2 * s by positivity)
      have hkey2 : b / 2 * (Real.exp (-(b / 2 * s)) * s) ≤ 1 := by
        linarith [show b / 2 * s * Real.exp (-(b / 2 * s)) =
          b / 2 * (Real.exp (-(b / 2 * s)) * s) from by ring]
      have hse : Real.exp (-(b / 2 * s)) * s ≤ 2 / b := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < b)]
        calc Real.exp (-(b / 2 * s)) * s * b
            = 2 * (b / 2 * (Real.exp (-(b / 2 * s)) * s)) := by ring
          _ = 2 * (b / 2 * s * Real.exp (-(b / 2 * s))) := by ring
          _ ≤ 2 * 1 := by linarith
          _ = 2 := by ring
      rw [show -(b / 2) * s = -(b / 2 * s) from by ring] at hexp_nn ⊢
      calc Real.exp (-(b / 2 * s)) * Real.exp (-(b / 2 * s)) * s
          = Real.exp (-(b / 2 * s)) * (Real.exp (-(b / 2 * s)) * s) := by ring
        _ ≤ Real.exp (-(b / 2 * s)) * (2 / b) :=
            mul_le_mul_of_nonneg_left hse hexp_nn
        _ = 2 / b * Real.exp (-(b / 2 * s)) := by ring
    calc gaussDensity σ x * |quadForm S x|
        ≤ gaussDensity σ x * (‖S‖ * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hqf_bound (gaussDensity_nonneg' σ x)
      _ = ‖S‖ * (gaussDensity σ x * ‖x‖ ^ 2) := by ring
      _ ≤ ‖S‖ * ((2 / b) * Real.exp (-(b / 2) * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hgsq_bound (norm_nonneg S)
      _ = C * Real.exp (-(b / 2) * ‖x‖ ^ 2) := by ring

/-- The Gaussian averaging bound with scaling parameter σ > 0:

    ∫ (1 - exp(-σ²‖y‖²/2)) dμ(y) ≤ ε + 2σ²·T

    Here exp(-σ²‖y‖²/2) is the characteristic function of N(0, σ²I).
    The bound follows from Fubini + pointwise bound Re(1-φ) ≤ ε + 2·qf
    + Gaussian second moment E_γ[⟨x,Sx⟩] ≤ σ²·Tr(S).
-/
theorem gaussian_averaging_bound
    (μ : ProbabilityMeasure V) (φ : V → ℂ)
    (hφ : ∀ t, charFun μ.toMeasure t = φ t)
    (ε : ℝ) (hε : 0 < ε)
    (σ : ℝ) (hσ : 0 < σ)
    (S : V →L[ℝ] V) (hS : S.IsPositive)
    (h_bound : ∀ x, quadForm S x < 1 → ‖1 - φ x‖ < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (h_trace : ∀ (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ V),
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ T) :
    ∫ y, (1 - Real.exp (-(σ ^ 2 * ‖y‖ ^ 2 / 2))) ∂μ.toMeasure ≤ ε + 2 * σ ^ 2 * T := by
  set g := gaussDensity (V := V) σ with hg_def
  set C := ∫ x : V, g x with hC_def
  have hC_pos : 0 < C := gaussDensity_integral_pos' (V := V) σ hσ
  have hCinv_nn : 0 ≤ C⁻¹ := inv_nonneg.mpr hC_pos.le
  have hg_int := gaussDensity_integrable' (V := V) σ hσ
  -- Step 1: Fubini
  rw [fubini_gaussian_charFun μ φ hφ σ hσ]
  -- Step 2: Pointwise bound
  have hpointwise : ∀ x, (1 - (φ x).re) ≤ ε + 2 * quadForm S x := by
    intro x
    by_cases hqf : quadForm S x < 1
    · have hre : (1 - (φ x).re) ≤ ‖1 - φ x‖ := by
        calc (1 - (φ x).re) = (1 - φ x).re := by simp [sub_re]
          _ ≤ |(1 - φ x).re| := le_abs_self _
          _ ≤ ‖1 - φ x‖ := abs_re_le_norm _
      linarith [h_bound x hqf, quadForm_nonneg hS x]
    · push Not at hqf
      have hre_le : (φ x).re ≤ ‖φ x‖ := le_trans (le_abs_self _) (abs_re_le_norm _)
      have hnorm_le : ‖φ x‖ ≤ 1 := by
        rw [← hφ]; haveI : IsProbabilityMeasure μ.toMeasure := inferInstance
        exact norm_charFun_le_one x
      have hneg_re : -(φ x).re ≤ ‖φ x‖ := le_trans (neg_le_abs _) (abs_re_le_norm _)
      linarith
  -- Step 3: Integrability
  have hgqf_int : Integrable (fun x => g x * quadForm S x) volume :=
    gaussDensity_mul_quadForm_integrable' (V := V) σ hσ S
  have hprod_int : Integrable (fun x => g x * (1 - (φ x).re)) volume := by
    have hφ_eq : φ = charFun μ.toMeasure := funext (fun t => (hφ t).symm)
    rw [hφ_eq]
    have hφ_meas : Measurable (fun x => (charFun μ.toMeasure x).re) :=
      Complex.measurable_re.comp measurable_charFun
    apply Integrable.mono (hg_int.const_mul 2)
      (((gaussDensity_continuous' σ).measurable.mul
        (measurable_const.sub hφ_meas)).aestronglyMeasurable)
    filter_upwards with x
    haveI : IsProbabilityMeasure μ.toMeasure := inferInstance
    have hg_nn := gaussDensity_nonneg' σ x
    have hre := le_trans (le_abs_self (charFun μ.toMeasure x).re) (abs_re_le_norm _)
    have hnre := le_trans (neg_le_abs (charFun μ.toMeasure x).re) (abs_re_le_norm _)
    have hnorm := norm_charFun_le_one (μ := μ.toMeasure) x
    have h1 : |1 - (charFun μ.toMeasure x).re| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have h2 : ‖g x * (1 - (charFun μ.toMeasure x).re)‖ ≤ g x * 2 := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg_nn]
      exact mul_le_mul_of_nonneg_left h1 hg_nn
    have h3 : ‖2 * g x‖ = g x * 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hg_nn)]; ring
    linarith
  have hprod2_int : Integrable (fun x => g x * (ε + 2 * quadForm S x)) volume := by
    have : (fun x => g x * (ε + 2 * quadForm S x)) =
        (fun x => ε * g x + 2 * (g x * quadForm S x)) := by ext x; ring
    rw [this]; exact (hg_int.const_mul ε).add (hgqf_int.const_mul 2)
  -- Step 4: Integral inequality + split + combine
  have hint_le : C⁻¹ * ∫ x, g x * (1 - (φ x).re) ≤
      C⁻¹ * ∫ x, g x * (ε + 2 * quadForm S x) :=
    mul_le_mul_of_nonneg_left
      (integral_mono hprod_int hprod2_int fun x =>
        mul_le_mul_of_nonneg_left (hpointwise x) (gaussDensity_nonneg' σ x))
      hCinv_nn
  have hint_split : ∫ x, g x * (ε + 2 * quadForm S x) =
      ε * C + 2 * ∫ x, g x * quadForm S x := by
    have heq : (fun x => g x * (ε + 2 * quadForm S x)) =
        (fun x => ε * g x + 2 * (g x * quadForm S x)) := by ext x; ring
    rw [heq, integral_add (hg_int.const_mul ε) (hgqf_int.const_mul 2),
      integral_const_mul ε, integral_const_mul 2]
  calc C⁻¹ * ∫ x, g x * (1 - (φ x).re)
      ≤ C⁻¹ * ∫ x, g x * (ε + 2 * quadForm S x) := hint_le
    _ = C⁻¹ * (ε * C + 2 * ∫ x, g x * quadForm S x) := by rw [hint_split]
    _ = ε + 2 * (C⁻¹ * ∫ x, g x * quadForm S x) := by
        have hCne : C ≠ 0 := ne_of_gt hC_pos
        rw [mul_add]; congr 1
        · rw [← mul_assoc, mul_comm C⁻¹ ε, mul_assoc, inv_mul_cancel₀ hCne, mul_one]
        · ring
    _ ≤ ε + 2 * (σ ^ 2 * T) := by linarith [gaussian_quadForm_integral_le σ hσ S hS T hT h_trace]
    _ = ε + 2 * σ ^ 2 * T := by ring

end GaussianAveraging

/-- Scaled Chebyshev: combining Gaussian averaging with the tail bound. -/
lemma scaled_tail_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : ProbabilityMeasure V) (φ : V → ℂ)
    (hφ : ∀ t, charFun μ.toMeasure t = φ t)
    (ε : ℝ) (hε : 0 < ε)
    (σ : ℝ) (hσ : 0 < σ)
    (S : V →L[ℝ] V) (hS : S.IsPositive)
    (h_bound : ∀ x, quadForm S x < 1 → ‖1 - φ x‖ < ε)
    (T : ℝ) (hT : 0 ≤ T)
    (h_trace : ∀ (ι : Type*) [Fintype ι] (b : OrthonormalBasis ι ℝ V),
      ∑ i, @inner ℝ V _ (b i) (S (b i)) ≤ T)
    (R : ℝ) (hR : 0 < R) :
    (μ.toMeasure {y | R ≤ ‖y‖}).toReal ≤
      (ε + 2 * σ ^ 2 * T) / (1 - Real.exp (-(σ ^ 2 * R ^ 2 / 2))) := by
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hRσ : 0 < σ ^ 2 * R ^ 2 / 2 := by positivity
  have hC0 : 0 ≤ ε + 2 * σ ^ 2 * T := by nlinarith
  have hgab := gaussian_averaging_bound μ φ hφ ε hε σ hσ S hS h_bound T hT h_trace
  exact tail_bound_from_exp_integral μ σ hσ _ hC0 hgab R hR

/-! ## Restriction of Operators to Marginal Subspaces -/

/-- The embedding t ↦ ∑ tᵢvᵢ from EuclideanSpace to H. -/
private def embedON {n : ℕ} (v : Fin n → H) : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] H :=
  { toFun := fun t => ∑ i, t i • v i
    map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
    map_smul' := fun r x => by
      simp only [RingHom.id_apply]; rw [Finset.smul_sum]
      congr 1; ext i; simp [smul_smul, mul_comm r] }

/-- The projection x ↦ (⟪vᵢ, x⟫)ᵢ from H to EuclideanSpace. -/
private def projON {n : ℕ} (v : Fin n → H) : H →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  { toFun := fun x => EuclideanSpace.equiv (Fin n) ℝ |>.symm (fun i => @inner ℝ H _ (v i) x)
    map_add' := fun x y => by ext i; simp [inner_add_right]
    map_smul' := fun r x => by ext i; simp [inner_smul_right] }

/-- Restriction of an operator S on H to a finite-dimensional subspace
    spanned by an orthonormal family v : Fin n → H. Defined as π ∘ S ∘ ι
    where ι embeds and π projects. Matrix: (S_v)_{ij} = ⟪vᵢ, S(vⱼ)⟫.
-/
def restrictOp (S : H →L[ℝ] H) {n : ℕ} (v : Fin n → H) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap (projON v ∘ₗ S.toLinearMap ∘ₗ embedON v)

omit [CompleteSpace H] in
/-- Coordinate formula for restrictOp. -/
lemma restrictOp_apply (S : H →L[ℝ] H) {n : ℕ} (v : Fin n → H)
    (t : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (restrictOp S v t) i = @inner ℝ H _ (v i) (S (∑ j, t j • v j)) := by
  unfold restrictOp projON embedON; simp

omit [CompleteSpace H] in
/-- The quadratic form of the restricted operator equals the original. -/
lemma restrictOp_quadForm (S : H →L[ℝ] H) {n : ℕ} (v : Fin n → H)
    (t : EuclideanSpace ℝ (Fin n)) :
    quadForm (restrictOp S v) t = quadForm S (∑ i, t i • v i) := by
  simp only [quadForm]
  rw [PiLp.inner_apply]
  simp only [restrictOp_apply]
  simp_rw [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = b * a from fun a b => RCLike.inner_apply a b]
  rw [sum_inner]
  simp only [inner_smul_left, RCLike.conj_to_real]
  congr 1; ext i; ring

/-- Inner product symmetry for self-adjoint operators: ⟪a, Sb⟫ = ⟪b, Sa⟫. -/
private lemma inner_self_adjoint_comm (S : H →L[ℝ] H) (hS : S.IsPositive)
    (a b : H) : @inner ℝ H _ a (S b) = @inner ℝ H _ b (S a) := by
  have h := ContinuousLinearMap.adjoint_inner_left S b a
  rw [hS.isSelfAdjoint.adjoint_eq] at h
  rw [← h, real_inner_comm]

/-- The restriction of a positive operator is positive. -/
lemma restrictOp_isPositive (S : H →L[ℝ] H) (hS : S.IsPositive)
    {n : ℕ} (v : Fin n → H) :
    (restrictOp S v).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    simp only [ContinuousLinearMap.coe_coe]
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [restrictOp_apply]
    simp_rw [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = b * a from fun a b => RCLike.inner_apply a b]
    trans @inner ℝ H _ (∑ i, y i • v i) (S (∑ j, x j • v j))
    · rw [sum_inner]; congr 1; ext i; rw [inner_smul_left, RCLike.conj_to_real]
    trans @inner ℝ H _ (∑ i, x i • v i) (S (∑ j, y j • v j))
    · exact inner_self_adjoint_comm S hS _ _
    · rw [sum_inner]; congr 1; ext i; rw [inner_smul_left, RCLike.conj_to_real]; ring
  · intro x
    simp only [ContinuousLinearMap.reApplyInnerSelf]
    rw [RCLike.re_to_real, real_inner_comm]
    change 0 ≤ quadForm (restrictOp S v) x
    rw [restrictOp_quadForm]
    exact quadForm_nonneg hS _

/-- For a finite orthonormal set in a Hilbert space, the sum of diagonal
    entries ∑ⱼ ⟪vⱼ, S(vⱼ)⟫ is bounded by the trace ∑' k ⟪bₖ, S(bₖ)⟫.
    Proof: decompose bₖ = P(bₖ) + Q(bₖ) via the projection P onto span(v).
    The cross term ∑' k ⟪Q(bₖ), S(P(bₖ))⟫ vanishes by Parseval + orthonormality,
    so the difference = ∑' k ⟪Q(bₖ), S(Q(bₖ))⟫ ≥ 0 by positivity of S.
-/
theorem orthonormal_diag_le_hilbert_trace (S : H →L[ℝ] H) (hS : S.IsPositive)
    {n : ℕ} (v : Fin n → H) (hv : Orthonormal ℝ v)
    {ι : Type} (b : HilbertBasis ι ℝ H)
    (hsum : Summable (fun i => @inner ℝ H _ (b i) (S (b i)))) :
    ∑ j : Fin n, @inner ℝ H _ (v j) (S (v j)) ≤
      ∑' i, @inner ℝ H _ (b i) (S (b i)) := by
  have sa : ∀ a c : H, @inner ℝ H _ a (S c) = @inner ℝ H _ c (S a) := by
    intro a c
    have h := ContinuousLinearMap.adjoint_inner_left S c a
    rw [hS.isSelfAdjoint.adjoint_eq] at h; rw [← h, real_inner_comm]
  have hnn : ∀ x : H, 0 ≤ @inner ℝ H _ x (S x) := by
    intro x; have := hS.re_inner_nonneg_left x
    simp only [RCLike.re_to_real] at this; rwa [real_inner_comm]
  set Pv : H → H := fun x => ∑ j, @inner ℝ H _ (v j) x • v j with hPv_def
  suffices hsuff :
      ∑ j, @inner ℝ H _ (v j) (S (v j)) +
        ∑' k, @inner ℝ H _ (b k - Pv (b k)) (S (b k - Pv (b k))) =
      ∑' k, @inner ℝ H _ (b k) (S (b k)) by
    have h_nn : 0 ≤ ∑' k, @inner ℝ H _ (b k - Pv (b k)) (S (b k - Pv (b k))) :=
      tsum_nonneg fun k => hnn (b k - Pv (b k))
    linarith
  have expand : ∀ k, @inner ℝ H _ (b k - Pv (b k)) (S (b k - Pv (b k))) =
      @inner ℝ H _ (b k) (S (b k)) - 2 * @inner ℝ H _ (Pv (b k)) (S (b k)) +
      @inner ℝ H _ (Pv (b k)) (S (Pv (b k))) := by
    intro k; rw [map_sub]; simp only [inner_sub_left, inner_sub_right, sa (b k) (Pv (b k))]; ring
  have hA_eq : ∀ k, @inner ℝ H _ (Pv (b k)) (S (b k)) =
      ∑ j, @inner ℝ H _ (v j) (b k) * @inner ℝ H _ (b k) (S (v j)) := by
    intro k; simp only [hPv_def, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, RCLike.conj_to_real, sa]
  have hA : HasSum (fun k => @inner ℝ H _ (Pv (b k)) (S (b k)))
      (∑ j, @inner ℝ H _ (v j) (S (v j))) := by
    simp_rw [hA_eq]
    exact hasSum_sum fun j _ => b.hasSum_inner_mul_inner (v j) (S (v j))
  have hB_eq : ∀ k, @inner ℝ H _ (Pv (b k)) (S (Pv (b k))) =
      ∑ j, ∑ i, @inner ℝ H _ (v j) (S (v i)) *
        (@inner ℝ H _ (v j) (b k) * @inner ℝ H _ (v i) (b k)) := by
    intro k; simp only [hPv_def, sum_inner, inner_smul_left, RCLike.conj_to_real]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sa (v j) (∑ i, @inner ℝ H _ (v i) (↑(b k)) • v i)]
    simp only [sum_inner, inner_smul_left, RCLike.conj_to_real]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sa]; ring
  have hB_parseval : ∀ j i : Fin n,
      HasSum (fun k => @inner ℝ H _ (v j) (b k) * @inner ℝ H _ (v i) (b k))
        (@inner ℝ H _ (v j) (v i)) := by
    intro j i
    have h := b.hasSum_inner_mul_inner (v j) (v i)
    simp_rw [real_inner_comm (v i) (b _)] at h; exact h
  have hB_target_eq : ∑ j : Fin n, @inner ℝ H _ (v j) (S (v j)) =
      ∑ j, ∑ i, @inner ℝ H _ (v j) (S (v i)) * @inner ℝ H _ (v j) (v i) := by
    congr 1; ext j
    conv_lhs => rw [show @inner ℝ H _ (v j) (S (v j)) =
      ∑ i, @inner ℝ H _ (v j) (S (v i)) * @inner ℝ H _ (v j) (v i) from by
        simp_rw [orthonormal_iff_ite.mp hv]
        simp [Finset.mem_univ]]
  have hB : HasSum (fun k => @inner ℝ H _ (Pv (b k)) (S (Pv (b k))))
      (∑ j, @inner ℝ H _ (v j) (S (v j))) := by
    rw [hB_target_eq]; simp_rw [hB_eq]
    exact hasSum_sum fun j _ => hasSum_sum fun i _ =>
      (hB_parseval j i).const_smul (@inner ℝ H _ (v j) (S (v i)))
  simp_rw [expand]
  have hQ : HasSum (fun k =>
      @inner ℝ H _ (b k) (S (b k)) - 2 * @inner ℝ H _ (Pv (b k)) (S (b k)) +
      @inner ℝ H _ (Pv (b k)) (S (Pv (b k))))
      (∑' k, @inner ℝ H _ (b k) (S (b k)) -
       ∑ j, @inner ℝ H _ (v j) (S (v j))) := by
    have h := ((hsum.hasSum.sub (hA.add hA)).add hB)
    have hv : (∑' k, @inner ℝ H _ (b k) (S (b k)) -
        (∑ j, @inner ℝ H _ (v j) (S (v j)) + ∑ j, @inner ℝ H _ (v j) (S (v j))) +
        ∑ j, @inner ℝ H _ (v j) (S (v j))) =
        ∑' k, @inner ℝ H _ (b k) (S (b k)) - ∑ j, @inner ℝ H _ (v j) (S (v j)) := by ring
    rw [← hv]
    refine h.congr (fun k => ?_)
    ring_nf
  linarith [hQ.tsum_eq]

omit [CompleteSpace H] in
/-- The trace of restrictOp in any ONB of EuclideanSpace equals ∑ⱼ ⟪vⱼ, S(vⱼ)⟫.
    Uses `LinearMap.trace_eq_sum_inner` for basis independence on finite-dimensional
    EuclideanSpace, then computes the standard basis entries.
-/
lemma restrictOp_trace_eq_diag (S : H →L[ℝ] H) {n : ℕ} (v : Fin n → H)
    (_hv : Orthonormal ℝ v)
    (ι' : Type*) [Fintype ι']
    (b' : OrthonormalBasis ι' ℝ (EuclideanSpace ℝ (Fin n))) :
    ∑ i, @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (b' i) (restrictOp S v (b' i)) =
    ∑ j : Fin n, @inner ℝ H _ (v j) (S (v j)) := by
  classical
  set T := (restrictOp S v).toLinearMap
  have h1 := LinearMap.trace_eq_sum_inner T b'
  have h2 := LinearMap.trace_eq_sum_inner T (EuclideanSpace.basisFun (Fin n) ℝ)
  have lhs_eq : ∑ i, @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (b' i)
      (restrictOp S v (b' i)) = ∑ i, @inner ℝ _ _ (b' i) (T (b' i)) := by
    congr
  have rhs_eq : ∑ j, @inner ℝ _ _ ((EuclideanSpace.basisFun (Fin n) ℝ) j)
      (T ((EuclideanSpace.basisFun (Fin n) ℝ) j)) =
      ∑ j : Fin n, @inner ℝ H _ (v j) (S (v j)) := by
    congr 1; ext j
    simp only [EuclideanSpace.basisFun_apply]
    change @inner ℝ (EuclideanSpace ℝ (Fin n)) _
      (EuclideanSpace.single j 1) (restrictOp S v (EuclideanSpace.single j 1)) = _
    rw [PiLp.inner_apply]
    simp_rw [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = b * a from fun a b => RCLike.inner_apply a b]
    have h_app : ∀ i, (restrictOp S v (EuclideanSpace.single j 1)) i =
        @inner ℝ H _ (v i) (S (v j)) := by
      intro i; rw [restrictOp_apply]
      congr 1
      simp [PiLp.single_apply, ite_smul, Finset.sum_ite_eq']
    simp_rw [h_app, PiLp.single_apply]
    simp [Finset.sum_ite_eq']
  exact lhs_eq.trans ((h1.symm.trans h2).trans rhs_eq)

/-- The trace of the restricted operator is bounded by the trace of the
    original on any Hilbert basis. Combines trace basis independence on
    EuclideanSpace with the diagonal bound.
-/
lemma restrictOp_trace_le (S : H →L[ℝ] H) (hS : S.IsPositive)
    {n : ℕ} (v : Fin n → H) (hv : Orthonormal ℝ v)
    {ι : Type} (b : HilbertBasis ι ℝ H)
    (hsum : Summable (fun i => @inner ℝ H _ (b i) (S (b i)))) :
    ∀ (ι' : Type) [Fintype ι'] (b' : OrthonormalBasis ι' ℝ (EuclideanSpace ℝ (Fin n))),
      ∑ i, @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (b' i) (restrictOp S v (b' i)) ≤
        ∑' i, @inner ℝ H _ (b i) (S (b i)) := by
  intro ι' _ b'
  haveI : DecidableEq ι' := Classical.decEq _
  rw [restrictOp_trace_eq_diag S v hv ι' b']
  exact orthonormal_diag_le_hilbert_trace S hS v hv b hsum

/-! ## Main Tightness Theorem -/

/-- For any C < η and σ > 0, there exists R > 0 such that
    C / (1 - exp(-σ²R²/2)) < η.
-/
lemma exists_R_for_tail_bound (C η σ : ℝ) (hC : 0 < C) (hCη : C < η) (hσ : 0 < σ) :
    ∃ R > 0, C / (1 - Real.exp (-(σ ^ 2 * R ^ 2 / 2))) < η := by
  have hη : 0 < η := by linarith
  set δ := (1 - C / η) / 2 with hδ_def
  have hCη' : C / η < 1 := by rwa [div_lt_one hη]
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have hδ_bound : δ < 1 - C / η := by rw [hδ_def]; linarith
  have hδ_lt_one : δ < 1 := by linarith [div_pos hC hη]
  have hlog_neg : Real.log δ < 0 := Real.log_neg hδ_pos hδ_lt_one
  set R := Real.sqrt (2 * (-Real.log δ)) / σ with hR_def
  use R
  constructor
  · rw [hR_def]; apply div_pos (Real.sqrt_pos.mpr (by nlinarith)) hσ
  · have hσ2 : 0 < σ ^ 2 := by positivity
    have hR_sq : R ^ 2 = 2 * (-Real.log δ) / σ ^ 2 := by
      rw [hR_def, div_pow, Real.sq_sqrt (by nlinarith)]
    have h_exp_arg : σ ^ 2 * R ^ 2 / 2 = -Real.log δ := by rw [hR_sq]; field_simp
    rw [h_exp_arg, neg_neg, Real.exp_log hδ_pos, div_lt_iff₀ (by linarith : 0 < 1 - δ)]
    have : η * (1 - δ) = (η + C) / 2 := by rw [hδ_def]; field_simp; ring
    linarith

/-- **Sazonov Tightness Theorem.** If φ : H → ℂ is positive definite, normalized,
    and Sazonov-continuous at 0, then the family of all finite-dimensional
    marginal measures is uniformly tight.
-/
theorem sazonov_tightness (φ : H → ℂ) (_hpd : IsPositiveDefinite φ)
    (_hnorm : φ 0 = 1) (_hcont : Continuous φ)
    (hsaz : SazonovContinuousAt φ) :
    ∀ η > 0, ∃ R > 0, ∀ (n : ℕ) (v : Fin n → H) (_ : Orthonormal ℝ v)
      (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
      (_ : ∀ t, charFun μ.toMeasure t = marginalFun φ v t),
    (μ.toMeasure {y | R ≤ ‖y‖}).toReal < η := by
  intro η hη
  set ε := η / 3 with hε_def
  have hε : 0 < ε := by linarith
  obtain ⟨S, hS_bound⟩ := hsaz ε hε
  obtain ⟨hpos, ι, b, hsum⟩ := S.traceClass
  set T := ∑' i, @inner ℝ H _ (b i) (S.op (b i)) with hT_def
  have hT_nn : 0 ≤ T := by
    apply tsum_nonneg; intro i
    have := hpos.re_inner_nonneg_left (b i)
    simp only [RCLike.re_to_real] at this
    rwa [real_inner_comm]
  set σ := Real.sqrt (η / (6 * (T + 1))) with hσ_def
  have hT1 : 0 < T + 1 := by linarith
  have hσ_sq_pos : 0 < η / (6 * (T + 1)) := by positivity
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hσ_sq_pos
  have hσ_sq : σ ^ 2 = η / (6 * (T + 1)) := by rw [hσ_def, sq, Real.mul_self_sqrt hσ_sq_pos.le]
  set C := ε + 2 * σ ^ 2 * T with hC_def
  have hC_bound : C < η := by
    rw [hC_def, hε_def, hσ_sq]
    have h6T1 : (0:ℝ) < 6 * (T + 1) := by positivity
    rw [show 2 * (η / (6 * (T + 1))) * T = η * T / (3 * (T + 1)) by
      field_simp; ring]
    rw [div_add_div _ _ (by positivity : (3:ℝ) ≠ 0) (by positivity : 3 * (T + 1) ≠ 0)]
    rw [div_lt_iff₀ (by positivity : 0 < 3 * (3 * (T + 1)))]
    nlinarith
  have hC_pos : 0 < C := by rw [hC_def]; nlinarith [sq_nonneg σ]
  obtain ⟨R, hR, hR_bound⟩ := exists_R_for_tail_bound C η σ hC_pos hC_bound hσ_pos
  use R, hR
  intro n v hv μ hμ
  have h_gauss := gaussian_averaging_bound μ (marginalFun φ v) hμ ε hε σ hσ_pos
      (restrictOp S.op v) (restrictOp_isPositive S.op hpos v)
  have h_bound_v : ∀ t : EuclideanSpace ℝ (Fin n),
      quadForm (restrictOp S.op v) t < 1 → ‖1 - marginalFun φ v t‖ < ε := by
    intro t ht
    rw [restrictOp_quadForm] at ht
    exact hS_bound _ ht
  have h_trace_v := restrictOp_trace_le S.op hpos v hv b hsum
  have h_gauss' := h_gauss h_bound_v T hT_nn (fun ι' _ b' => by
    calc ∑ i, @inner ℝ _ _ (b' i) (restrictOp S.op v (b' i))
        ≤ ∑' i, @inner ℝ H _ (b i) (S.op (b i)) := h_trace_v ι' b'
      _ = T := rfl)
  have h_tail := tail_bound_from_exp_integral μ σ hσ_pos _ (by nlinarith [sq_nonneg σ]) h_gauss' R
    hR
  calc (μ.toMeasure {y | R ≤ ‖y‖}).toReal
      ≤ C / (1 - Real.exp (-(σ ^ 2 * R ^ 2 / 2))) := h_tail
    _ < η := hR_bound

end
