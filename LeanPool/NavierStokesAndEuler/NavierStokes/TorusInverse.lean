/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.DiophantineGraph
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Smooth Fourier series and directional inversion on the two-dimensional torus

We work on the universal cover `ℝ × ℝ`, with frequencies in `ℤ × ℤ`.
Rapid coefficients have summable polynomially weighted norms of every order.
-/

noncomputable section

namespace NavierStokes.TorusInverse

open scoped BigOperators Topology ContDiff

abbrev Frequency := ℤ × ℤ
abbrev Plane := ℝ × ℝ

def weight (k : Frequency) : ℝ := 1 + |(k.1 : ℝ)| + |(k.2 : ℝ)|

theorem weight_pos (k : Frequency) : 0 < weight k := by
  unfold weight
  positivity

/-- Polynomially weighted absolute summability of every order. -/
def Rapid (a : Frequency → ℂ) : Prop :=
  ∀ p : ℕ, Summable (fun k => weight k ^ p * ‖a k‖)

theorem Rapid.summable_norm {a : Frequency → ℂ} (ha : Rapid a) :
    Summable (fun k => ‖a k‖) := by
  simpa using ha 0

theorem Rapid.mul_linear {a b : Frequency → ℂ} (ha : Rapid a) (C : ℝ)
    (hb : ∀ k, ‖b k‖ ≤ C * weight k) : Rapid (fun k => b k * a k) := by
  intro p
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (weight_pos k).le _) (norm_nonneg _)) _
    ((ha (p + 1)).mul_left C)
  intro k
  calc
    weight k ^ p * ‖b k * a k‖ = weight k ^ p * (‖b k‖ * ‖a k‖) := by rw [norm_mul]
    _ ≤ weight k ^ p * ((C * weight k) * ‖a k‖) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (weight_pos k).le _)
      exact mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _)
    _ = C * (weight k ^ (p + 1) * ‖a k‖) := by rw [pow_succ]; ring

def omega : ℂ := 2 * Real.pi * Complex.I

def freqX (k : Frequency) : ℂ := omega * (k.1 : ℂ)
def freqY (k : Frequency) : ℂ := omega * (k.2 : ℂ)

def dx : Plane →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
def dy : Plane →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

def liftX : ℂ →L[ℝ] (Plane →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ Plane ℂ dx
def liftY : ℂ →L[ℝ] (Plane →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ Plane ℂ dy

@[simp] theorem liftX_apply (c : ℂ) (x : Plane) : liftX c x = x.1 • c := rfl
@[simp] theorem liftY_apply (c : ℂ) (x : Plane) : liftY c x = x.2 • c := rfl

def phase (k : Frequency) : Plane →L[ℝ] ℂ := liftX (freqX k) + liftY (freqY k)

def mode (k : Frequency) (x : Plane) : ℂ := Complex.exp (phase k x)

theorem phase_formula (k : Frequency) (x : Plane) :
    phase k x = omega * ((k.1 : ℂ) * (x.1 : ℂ) + (k.2 : ℂ) * (x.2 : ℂ)) := by
  simp only [phase, freqX, freqY, add_apply,
    liftX_apply, liftY_apply, Complex.real_smul]
  ring

theorem norm_mode (k : Frequency) (x : Plane) : ‖mode k x‖ = 1 := by
  rw [mode, Complex.norm_exp, phase_formula]
  simp [omega, Complex.mul_re, Complex.mul_im]

theorem continuous_mode (k : Frequency) : Continuous (mode k) :=
  Complex.continuous_exp.comp (phase k).continuous

def derivX (a : Frequency → ℂ) (k : Frequency) : ℂ := freqX k * a k
def derivY (a : Frequency → ℂ) (k : Frequency) : ℂ := freqY k * a k

theorem norm_freqX_le (k : Frequency) : ‖freqX k‖ ≤ ‖omega‖ * weight k := by
  rw [freqX, norm_mul, Complex.norm_intCast]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold weight
  have := abs_nonneg (k.2 : ℝ)
  linarith

theorem norm_freqY_le (k : Frequency) : ‖freqY k‖ ≤ ‖omega‖ * weight k := by
  rw [freqY, norm_mul, Complex.norm_intCast]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold weight
  have := abs_nonneg (k.1 : ℝ)
  linarith

theorem Rapid.derivX {a : Frequency → ℂ} (ha : Rapid a) : Rapid (derivX a) :=
  ha.mul_linear ‖omega‖ norm_freqX_le

theorem Rapid.derivY {a : Frequency → ℂ} (ha : Rapid a) : Rapid (derivY a) :=
  ha.mul_linear ‖omega‖ norm_freqY_le

def series (a : Frequency → ℂ) (x : Plane) : ℂ := ∑' k, a k * mode k x

theorem summable_terms {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    Summable (fun k => a k * mode k x) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_mode, mul_one] using ha.summable_norm

theorem continuous_series {a : Frequency → ℂ} (ha : Rapid a) : Continuous (series a) := by
  apply continuous_tsum (fun k => continuous_const.fun_mul (continuous_mode k)) ha.summable_norm
  intro k x
  simp only [norm_mul, norm_mode, mul_one, le_refl]

def termDeriv (a : Frequency → ℂ) (k : Frequency) (x : Plane) : Plane →L[ℝ] ℂ :=
  liftX (derivX a k * mode k x) + liftY (derivY a k * mode k x)

theorem hasFDerivAt_term (a : Frequency → ℂ) (k : Frequency) (x : Plane) :
    HasFDerivAt (fun y => a k * mode k y) (termDeriv a k x) x := by
  have h := ((phase k).hasFDerivAt (x := x)).cexp.const_mul (a k)
  have hd : termDeriv a k x = a k • (Complex.exp (phase k x) • phase k) := by
    apply ContinuousLinearMap.ext
    intro y
    simp only [termDeriv, phase, derivX, derivY, liftX_apply, liftY_apply,
      add_apply, smul_apply,
      Complex.real_smul, smul_eq_mul, mode]
    ring
  simpa only [mode, hd] using h

def derivativeMajorant (a : Frequency → ℂ) (k : Frequency) : ℝ :=
  ‖liftX‖ * ‖derivX a k‖ + ‖liftY‖ * ‖derivY a k‖

theorem summable_derivativeMajorant {a : Frequency → ℂ} (ha : Rapid a) :
    Summable (derivativeMajorant a) :=
  (ha.derivX.summable_norm.mul_left ‖liftX‖).add
    (ha.derivY.summable_norm.mul_left ‖liftY‖)

theorem norm_termDeriv_le (a : Frequency → ℂ) (k : Frequency) (x : Plane) :
    ‖termDeriv a k x‖ ≤ derivativeMajorant a k := by
  apply (norm_add_le _ _).trans
  apply add_le_add
  · simpa only [norm_mul, norm_mode, mul_one] using
      liftX.le_opNorm (derivX a k * mode k x)
  · simpa only [norm_mul, norm_mode, mul_one] using
      liftY.le_opNorm (derivY a k * mode k x)

theorem summable_termDeriv {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    Summable (fun k => termDeriv a k x) :=
  Summable.of_norm_bounded (summable_derivativeMajorant ha) (fun k => norm_termDeriv_le a k x)

theorem hasFDerivAt_series {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    HasFDerivAt (series a) (∑' k, termDeriv a k x) x := by
  exact hasFDerivAt_tsum (summable_derivativeMajorant ha) (hasFDerivAt_term a)
    (norm_termDeriv_le a) (summable_terms ha (0 : Plane)) x

theorem fderiv_series {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    fderiv ℝ (series a) x = liftX (series (derivX a) x) + liftY (series (derivY a) x) := by
  rw [(hasFDerivAt_series ha x).fderiv]
  have hx := liftX.summable (summable_terms ha.derivX x)
  have hy := liftY.summable (summable_terms ha.derivY x)
  rw [show (fun k => termDeriv a k x) =
    (fun k => liftX (derivX a k * mode k x) + liftY (derivY a k * mode k x)) from rfl]
  rw [Summable.tsum_add hx hy, ← liftX.map_tsum (summable_terms ha.derivX x),
    ← liftY.map_tsum (summable_terms ha.derivY x)]
  rfl

/-- Smoothness is proved from summability and termwise differentiation. -/
theorem contDiff_series_nat (p : ℕ) {a : Frequency → ℂ} (ha : Rapid a) :
    ContDiff ℝ p (series a) := by
  induction p generalizing a with
  | zero => exact contDiff_zero.mpr (continuous_series ha)
  | succ p ih =>
    rw [show ((p + 1 : ℕ) : WithTop ℕ∞) = (p : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_fderiv]
    refine ⟨(fun x => (hasFDerivAt_series ha x).differentiableAt), ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (series a) =
          (fun x => liftX (series (derivX a) x) + liftY (series (derivY a) x)) :=
        funext (fderiv_series ha)
      rw [heq]
      exact (liftX.contDiff.comp (ih ha.derivX)).add (liftY.contDiff.comp (ih ha.derivY))

theorem contDiff_series {a : Frequency → ℂ} (ha : Rapid a) :
    ContDiff ℝ ∞ (series a) :=
  contDiff_infty.mpr (fun p => contDiff_series_nat p ha)

inductive Direction
  | radial
  | temporal
  deriving DecidableEq

def vector : Direction → Plane
  | .radial => (1, 1 - Real.sqrt 2)
  | .temporal => (Real.sqrt 2 - 1, 1)

def symbol : Direction → Frequency → ℝ
  | .radial, k => DiophantineGraph.radialSymbol k.1 k.2
  | .temporal, k => DiophantineGraph.timeSymbol k.1 k.2

theorem pair_nonzero {k : Frequency} (hk : k ≠ 0) : k.1 ≠ 0 ∨ k.2 ≠ 0 := by
  by_cases h₁ : k.1 = 0
  · right
    intro h₂
    exact hk (Prod.ext h₁ h₂)
  · exact Or.inl h₁

theorem symbol_formula (d : Direction) (k : Frequency) :
    symbol d k = (k.1 : ℝ) * (vector d).1 + (k.2 : ℝ) * (vector d).2 := by
  cases d <;> simp only [symbol, vector, DiophantineGraph.radialSymbol_formula,
    DiophantineGraph.timeSymbol_formula] <;> ring

theorem symbol_ne_zero (d : Direction) {k : Frequency} (hk : k ≠ 0) : symbol d k ≠ 0 := by
  cases d
  · exact DiophantineGraph.radialSymbol_ne_zero k.1 k.2 (pair_nonzero hk)
  · exact DiophantineGraph.timeSymbol_ne_zero k.1 k.2 (pair_nonzero hk)

theorem length_le_weight (k : Frequency) :
    1 + DiophantineGraph.frequencyLength k.1 k.2 ≤ weight k := by
  have hs := DiophantineGraph.frequencyLength_nonneg k.1 k.2
  have hsq : DiophantineGraph.frequencyLength k.1 k.2 ^ 2 =
      (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
  have ht : DiophantineGraph.frequencyLength k.1 k.2 ≤
      |(k.1 : ℝ)| + |(k.2 : ℝ)| := by
    apply (sq_le_sq₀ hs (by positivity)).mp
    rw [hsq]
    nlinarith [sq_abs (k.1 : ℝ), sq_abs (k.2 : ℝ),
      mul_nonneg (abs_nonneg (k.1 : ℝ)) (abs_nonneg (k.2 : ℝ))]
  unfold weight
  linarith

theorem reciprocal_symbol_bound (d : Direction) {k : Frequency} (hk : k ≠ 0) :
    |1 / symbol d k| ≤ 6 * weight k := by
  have hb : |1 / symbol d k| ≤
      6 * (1 + DiophantineGraph.frequencyLength k.1 k.2) := by
    cases d
    · exact DiophantineGraph.radial_reciprocal_bound k.1 k.2 (pair_nonzero hk)
    · exact DiophantineGraph.time_reciprocal_bound k.1 k.2 (pair_nonzero hk)
  exact hb.trans (mul_le_mul_of_nonneg_left (length_le_weight k) (by norm_num))

theorem omega_ne_zero : omega ≠ 0 := by
  unfold omega
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

def multiplier (d : Direction) (k : Frequency) : ℂ := (omega * (symbol d k : ℂ))⁻¹
def inverseCoeff (d : Direction) (a : Frequency → ℂ) (k : Frequency) : ℂ :=
  multiplier d k * a k

@[simp] theorem symbol_zero (d : Direction) : symbol d 0 = 0 := by
  cases d <;> simp [symbol, DiophantineGraph.radialSymbol,
    DiophantineGraph.timeSymbol, DiophantineGraph.quadraticForm]

@[simp] theorem inverseCoeff_zero (d : Direction) (a : Frequency → ℂ) :
    inverseCoeff d a 0 = 0 := by
  simp [inverseCoeff, multiplier]

theorem norm_multiplier_le (d : Direction) (k : Frequency) :
    ‖multiplier d k‖ ≤ (6 * ‖omega⁻¹‖) * weight k := by
  by_cases hk : k = 0
  · subst k
    simp only [multiplier, symbol_zero, Complex.ofReal_zero, mul_zero, inv_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (weight_pos _).le
  · have h := reciprocal_symbol_bound d hk
    calc
      ‖multiplier d k‖ = ‖omega⁻¹‖ * |1 / symbol d k| := by
        simp [multiplier, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, one_div, mul_inv_rev, mul_comm]
      _ ≤ ‖omega⁻¹‖ * (6 * weight k) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by ring

theorem Rapid.inverseCoeff {a : Frequency → ℂ} (ha : Rapid a) (d : Direction) :
    Rapid (inverseCoeff d a) := ha.mul_linear (6 * ‖omega⁻¹‖) (norm_multiplier_le d)

/-- The coefficient estimate loses one polynomial frequency weight. -/
theorem inverseCoeff_weighted_bound (d : Direction) (a : Frequency → ℂ)
    (p : ℕ) (k : Frequency) :
    weight k ^ p * ‖inverseCoeff d a k‖ ≤
      (6 * ‖omega⁻¹‖) * (weight k ^ (p + 1) * ‖a k‖) := by
  unfold inverseCoeff
  rw [norm_mul]
  calc
    weight k ^ p * (‖multiplier d k‖ * ‖a k‖) ≤
        weight k ^ p * (((6 * ‖omega⁻¹‖) * weight k) * ‖a k‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (norm_multiplier_le d k) (norm_nonneg _))
        (pow_nonneg (weight_pos k).le p)
    _ = _ := by rw [pow_succ]; ring

theorem coefficient_cancel (d : Direction) {a : Frequency → ℂ} (hzero : a 0 = 0)
    (k : Frequency) : omega * (symbol d k : ℂ) * inverseCoeff d a k = a k := by
  by_cases hk : k = 0
  · simp [hk, hzero]
  · have hd : omega * (symbol d k : ℂ) ≠ 0 :=
      mul_ne_zero omega_ne_zero (Complex.ofReal_ne_zero.mpr (symbol_ne_zero d hk))
    change (omega * (symbol d k : ℂ)) * ((omega * (symbol d k : ℂ))⁻¹ * a k) = a k
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

def directionalInverse (d : Direction) (a : Frequency → ℂ) : Plane → ℂ :=
  series (inverseCoeff d a)

theorem contDiff_directionalInverse (d : Direction) {a : Frequency → ℂ} (ha : Rapid a) :
    ContDiff ℝ ∞ (directionalInverse d a) := contDiff_series (ha.inverseCoeff d)

theorem termDeriv_direction (d : Direction) {a : Frequency → ℂ} (hzero : a 0 = 0)
    (k : Frequency) (x : Plane) :
    termDeriv (inverseCoeff d a) k x (vector d) = a k * mode k x := by
  have hs : (symbol d k : ℂ) = (k.1 : ℂ) * ((vector d).1 : ℂ) +
      (k.2 : ℂ) * ((vector d).2 : ℂ) := by
    exact_mod_cast symbol_formula d k
  calc
    termDeriv (inverseCoeff d a) k x (vector d) =
        (omega * (symbol d k : ℂ) * inverseCoeff d a k) * mode k x := by
      rw [hs]
      simp only [termDeriv, add_apply, liftX_apply, liftY_apply,
        derivX, derivY, freqX, freqY, Complex.real_smul]
      ring
    _ = a k * mode k x := by rw [coefficient_cancel d hzero k]

/-- The genuine Fréchet derivative of the smooth inverse solves the equation. -/
theorem directionalInverse_solves (d : Direction) {a : Frequency → ℂ}
    (ha : Rapid a) (hzero : a 0 = 0) (x : Plane) :
    fderiv ℝ (directionalInverse d a) x (vector d) = series a x := by
  unfold directionalInverse
  rw [(hasFDerivAt_series (ha.inverseCoeff d) x).fderiv]
  calc
    (∑' k, termDeriv (inverseCoeff d a) k x) (vector d) =
        ∑' k, termDeriv (inverseCoeff d a) k x (vector d) :=
      (ContinuousLinearMap.apply ℝ ℂ (vector d)).map_tsum
        (summable_termDeriv (ha.inverseCoeff d) x)
    _ = series a x := tsum_congr (fun k => termDeriv_direction d hzero k x)

/-! ## Descent to the torus and actual Haar means -/

open MeasureTheory
local instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

abbrev Torus := UnitAddCircle × UnitAddCircle

def torusMeasure : Measure Torus :=
  (AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle

instance : IsProbabilityMeasure torusMeasure := by
  unfold torusMeasure
  infer_instance

def torusMode (k : Frequency) : C(Torus, ℂ) where
  toFun z := fourier k.1 z.1 * fourier k.2 z.2
  continuous_toFun := ((fourier k.1).continuous.comp continuous_fst).mul
    ((fourier k.2).continuous.comp continuous_snd)

theorem norm_torusMode (k : Frequency) (z : Torus) : ‖torusMode k z‖ = 1 := by
  simp [torusMode, fourier_apply, Circle.norm_coe]

def torusSeries (a : Frequency → ℂ) (z : Torus) : ℂ := ∑' k, a k * torusMode k z

theorem mode_eq_torusMode (k : Frequency) (x : Plane) :
    mode k x = torusMode k ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle)) := by
  change Complex.exp (phase k x) =
    fourier k.1 (x.1 : UnitAddCircle) * fourier k.2 (x.2 : UnitAddCircle)
  rw [phase_formula, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_one, div_one, omega]
  ring

theorem series_eq_torusSeries (a : Frequency → ℂ) (x : Plane) :
    series a x = torusSeries a ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle)) :=
  tsum_congr (fun k => congrArg (fun z => a k * z) (mode_eq_torusMode k x))

theorem circle_int_eq_zero (m : ℤ) : (((m : ℝ) : UnitAddCircle)) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨m, by simp⟩

/-- Integer translation invariance is actual descent to `(ℝ/ℤ)²`. -/
theorem series_periodic (a : Frequency → ℂ) (x : Plane) (m n : ℤ) :
    series a (x.1 + m, x.2 + n) = series a x := by
  rw [series_eq_torusSeries, series_eq_torusSeries]
  simp only [AddCircle.coe_add, circle_int_eq_zero, add_zero]

theorem continuous_torusSeries {a : Frequency → ℂ} (ha : Rapid a) :
    Continuous (torusSeries a) := by
  apply continuous_tsum (fun k => continuous_const.fun_mul (torusMode k).continuous)
    ha.summable_norm
  intro k z
  simp only [norm_mul, norm_torusMode, mul_one, le_refl]

theorem integral_fourier (n : ℤ) :
    (∫ z : UnitAddCircle, fourier n z ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1 : ℝ)))) 0 n
  rw [ContinuousMap.inner_toLp] at h
  simpa [fourier_zero, eq_comm] using h

theorem integral_torusMode (k : Frequency) :
    (∫ z, torusMode k z ∂torusMeasure) = if k = 0 then 1 else 0 := by
  change (∫ z : Torus, fourier k.1 z.1 * fourier k.2 z.2
    ∂(AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) = _
  rw [integral_prod_mul, integral_fourier, integral_fourier]
  by_cases h₁ : k.1 = 0 <;> by_cases h₂ : k.2 = 0 <;>
    simp [h₁, h₂, Prod.ext_iff]

theorem integrable_torusTerm (a : Frequency → ℂ) (k : Frequency) :
    Integrable (fun z => a k * torusMode k z) torusMeasure := by
  apply (integrable_const (‖a k‖ : ℝ)).mono'
    (continuous_const.fun_mul (torusMode k).continuous).aestronglyMeasurable
  filter_upwards with z
  simp only [norm_mul, norm_torusMode, mul_one, le_refl]

/-- The zeroth coefficient equals the actual normalized Haar integral. -/
theorem integral_torusSeries {a : Frequency → ℂ} (ha : Rapid a) :
    (∫ z, torusSeries a z ∂torusMeasure) = a 0 := by
  have hsum : Summable (fun k => ∫ z, ‖a k * torusMode k z‖ ∂torusMeasure) := by
    simpa only [norm_mul, norm_torusMode, mul_one, integral_const,
      probReal_univ, one_smul] using ha.summable_norm
  unfold torusSeries
  rw [← integral_tsum_of_summable_integral_norm (integrable_torusTerm a) hsum]
  simp only [integral_const_mul, integral_torusMode]
  simp only [mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single (0 : Frequency) (fun i hi => by simp [hi])]
  simp

/-- Weighted absolute Fourier coefficient seminorm. -/
def coeffSeminorm (p : ℕ) (a : Frequency → ℂ) : ℝ :=
  ∑' k, weight k ^ p * ‖a k‖

theorem inverseCoeff_seminorm_le (d : Direction) {a : Frequency → ℂ}
    (ha : Rapid a) (p : ℕ) :
    coeffSeminorm p (inverseCoeff d a) ≤ (6 * ‖omega⁻¹‖) * coeffSeminorm (p + 1) a := by
  have h := (ha.inverseCoeff d p).tsum_le_tsum (inverseCoeff_weighted_bound d a p)
    ((ha (p + 1)).mul_left (6 * ‖omega⁻¹‖))
  simpa only [coeffSeminorm, tsum_mul_left] using h

theorem norm_series_le {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    ‖series a x‖ ≤ coeffSeminorm 0 a := by
  simpa only [series, coeffSeminorm, pow_zero, one_mul, norm_mul, norm_mode, mul_one] using
    norm_tsum_le_tsum_norm (summable_terms ha x).norm

theorem norm_directionalInverse_le (d : Direction) {a : Frequency → ℂ}
    (ha : Rapid a) (x : Plane) :
    ‖directionalInverse d a x‖ ≤ (6 * ‖omega⁻¹‖) * coeffSeminorm 1 a := by
  exact (norm_series_le (ha.inverseCoeff d) x).trans (inverseCoeff_seminorm_le d ha 0)

def coordinateCoeff (j : Bool) (a : Frequency → ℂ) : Frequency → ℂ :=
  if j then derivY a else derivX a

def coordinatePartial (j : Bool) (f : Plane → ℂ) (x : Plane) : ℂ :=
  fderiv ℝ f x (if j then (0, 1) else (1, 0))

def coefficientWord : List Bool → (Frequency → ℂ) → Frequency → ℂ
  | [], a => a
  | j :: js, a => coordinateCoeff j (coefficientWord js a)

def derivativeWord : List Bool → (Plane → ℂ) → Plane → ℂ
  | [], f => f
  | j :: js, f => coordinatePartial j (derivativeWord js f)

theorem Rapid.coordinateCoeff {a : Frequency → ℂ} (ha : Rapid a) (j : Bool) :
    Rapid (coordinateCoeff j a) := by
  cases j
  · exact ha.derivX
  · exact ha.derivY

theorem Rapid.coefficientWord {a : Frequency → ℂ} (ha : Rapid a) (w : List Bool) :
    Rapid (coefficientWord w a) := by
  induction w with
  | nil => exact ha
  | cons j js ih => exact ih.coordinateCoeff j

theorem coordinatePartial_series (j : Bool) {a : Frequency → ℂ} (ha : Rapid a) :
    coordinatePartial j (series a) = series (coordinateCoeff j a) := by
  funext x
  cases j <;> simp [coordinatePartial, coordinateCoeff, fderiv_series ha,
    liftX_apply, liftY_apply]

theorem derivativeWord_series (w : List Bool) {a : Frequency → ℂ} (ha : Rapid a) :
    derivativeWord w (series a) = series (coefficientWord w a) := by
  induction w with
  | nil => rfl
  | cons j js ih =>
    simp only [derivativeWord, coefficientWord, ih]
    exact coordinatePartial_series j (ha.coefficientWord js)

theorem norm_coordinateCoeff_le (j : Bool) (a : Frequency → ℂ) (k : Frequency) :
    ‖coordinateCoeff j a k‖ ≤ (‖omega‖ * weight k) * ‖a k‖ := by
  cases j
  · exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (norm_freqX_le k) (norm_nonneg _))
  · exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (norm_freqY_le k) (norm_nonneg _))

theorem norm_coefficientWord_le (w : List Bool) (a : Frequency → ℂ) (k : Frequency) :
    ‖coefficientWord w a k‖ ≤ (‖omega‖ * weight k) ^ w.length * ‖a k‖ := by
  induction w with
  | nil => simp [coefficientWord]
  | cons j js ih =>
    calc
      ‖coefficientWord (j :: js) a k‖ ≤
          (‖omega‖ * weight k) * ‖coefficientWord js a k‖ := norm_coordinateCoeff_le _ _ _
      _ ≤ (‖omega‖ * weight k) * ((‖omega‖ * weight k) ^ js.length * ‖a k‖) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg (norm_nonneg _) (weight_pos k).le)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

/-- A uniform bound for every actual mixed coordinate derivative of the inverse. -/
theorem inverse_derivativeWord_bound (d : Direction) {a : Frequency → ℂ} (ha : Rapid a)
    (w : List Bool) (x : Plane) :
    ‖derivativeWord w (directionalInverse d a) x‖ ≤
      ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length) * coeffSeminorm (w.length + 1) a := by
  have hr := (ha.inverseCoeff d).coefficientWord w
  change ‖derivativeWord w (series (inverseCoeff d a)) x‖ ≤ _
  rw [derivativeWord_series w (ha.inverseCoeff d)]
  apply (norm_series_le hr x).trans
  have hb : ∀ k, ‖coefficientWord w (inverseCoeff d a) k‖ ≤
      ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length) * (weight k ^ (w.length + 1) * ‖a k‖) := by
    intro k
    calc
      ‖coefficientWord w (inverseCoeff d a) k‖ ≤
          (‖omega‖ * weight k) ^ w.length * ‖inverseCoeff d a k‖ := norm_coefficientWord_le _ _ _
      _ ≤ (‖omega‖ * weight k) ^ w.length * (((6 * ‖omega⁻¹‖) * weight k) * ‖a k‖) := by
        apply mul_le_mul_of_nonneg_left _
          (pow_nonneg (mul_nonneg (norm_nonneg _) (weight_pos k).le) _)
        exact (norm_mul _ _).le.trans
          (mul_le_mul_of_nonneg_right (norm_multiplier_le d k) (norm_nonneg _))
      _ = _ := by rw [mul_pow, pow_succ]; ring
  have hs := hr.summable_norm.tsum_le_tsum hb
    ((ha (w.length + 1)).mul_left ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length))
  simpa only [coeffSeminorm, pow_zero, one_mul, tsum_mul_left] using hs

/-! ## Parameters and support -/

theorem hasDerivAt_parameter_series (a a' : ℝ → Frequency → ℂ) (B : Frequency → ℝ)
    (hderiv : ∀ k t, HasDerivAt (fun s => a s k) (a' t k) t)
    (hB : Summable B) (hbound : ∀ k t, ‖a' t k‖ ≤ B k)
    (t₀ : ℝ) (hinit : Rapid (a t₀)) (x : Plane) (t : ℝ) :
    HasDerivAt (fun s => series (a s) x) (series (a' t) x) t := by
  apply hasDerivAt_tsum hB
    (fun k s => (hderiv k s).mul_const (mode k x)) _ (summable_terms hinit x) t
  intro k s
  simpa only [norm_mul, norm_mode, mul_one] using hbound k s

/-- Parameter differentiation commutes with the actual inverse series under a
uniform summable bound on one frequency-weighted parameter derivative. -/
theorem hasDerivAt_parameter_inverse (d : Direction) (a a' : ℝ → Frequency → ℂ)
    (B : Frequency → ℝ)
    (hderiv : ∀ k t, HasDerivAt (fun s => a s k) (a' t k) t)
    (hB : Summable (fun k => weight k * B k))
    (hbound : ∀ k t, ‖a' t k‖ ≤ B k)
    (t₀ : ℝ) (hinit : Rapid (a t₀)) (x : Plane) (t : ℝ) :
    HasDerivAt (fun s => directionalInverse d (a s) x)
      (directionalInverse d (a' t) x) t := by
  refine hasDerivAt_parameter_series
    (fun s => inverseCoeff d (a s)) (fun s => inverseCoeff d (a' s))
    (fun k => (6 * ‖omega⁻¹‖) * (weight k * B k)) ?_ ?_ ?_
      t₀ (hinit.inverseCoeff d) x t
  · intro k s
    exact HasDerivAt.const_mul (multiplier d k) (hderiv k s)
  · exact hB.mul_left _
  · intro k s
    calc
      ‖inverseCoeff d (a' s) k‖ = ‖multiplier d k‖ * ‖a' s k‖ := norm_mul _ _
      _ ≤ ((6 * ‖omega⁻¹‖) * weight k) * B k :=
        mul_le_mul (norm_multiplier_le d k) (hbound k s) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (weight_pos k).le)
      _ = _ := by ring

/-- Inversion uses only the torus variable and preserves support in every
external parameter. No nonvanishing or convergence hypothesis is needed here. -/
theorem inverse_preserves_parameter_support {P : Type*} (d : Direction)
    (a : P → Frequency → ℂ) (S : Set P)
    (hsupport : ∀ p, p ∉ S → ∀ k, a p k = 0) :
    ∀ p, p ∉ S → ∀ x, directionalInverse d (a p) x = 0 := by
  intro p hp x
  simp [directionalInverse, series, inverseCoeff, hsupport p hp]

/-- The constructed directional inverse has zero normalized Haar mean. -/
theorem inverse_zero_mean (d : Direction) {a : Frequency → ℂ} (ha : Rapid a) :
    (∫ z, torusSeries (inverseCoeff d a) z ∂torusMeasure) = 0 := by
  rw [integral_torusSeries (ha.inverseCoeff d), inverseCoeff_zero]

theorem directionalInverse_periodic (d : Direction) (a : Frequency → ℂ)
    (x : Plane) (m n : ℤ) :
    directionalInverse d a (x.1 + m, x.2 + n) = directionalInverse d a x :=
  series_periodic (inverseCoeff d a) x m n

/-- A zero-average rapidly convergent Fourier series on the actual torus has
a zero-average inverse whose universal-cover lift is smooth and solves the
directional equation. Both manuscript directions are covered. -/
theorem zero_mean_series_has_smooth_inverse (d : Direction) {a : Frequency → ℂ}
    (ha : Rapid a) (hmean : (∫ z, torusSeries a z ∂torusMeasure) = 0) :
    ∃ u : Torus → ℂ, Continuous u ∧ (∫ z, u z ∂torusMeasure) = 0 ∧
      ContDiff ℝ ∞ (fun x : Plane => u ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle))) ∧
      ∀ x : Plane,
        fderiv ℝ (fun y : Plane => u ((y.1 : UnitAddCircle), (y.2 : UnitAddCircle)))
          x (vector d) = series a x := by
  have hzero : a 0 = 0 := by rwa [integral_torusSeries ha] at hmean
  have hpull : (fun x : Plane =>
      torusSeries (inverseCoeff d a) ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle))) =
      directionalInverse d a := by
    funext x
    exact (series_eq_torusSeries (inverseCoeff d a) x).symm
  refine ⟨torusSeries (inverseCoeff d a), continuous_torusSeries (ha.inverseCoeff d),
    inverse_zero_mean d ha, ?_, ?_⟩
  · rw [hpull]
    exact contDiff_directionalInverse d ha
  · rw [hpull]
    exact directionalInverse_solves d ha hzero

end NavierStokes.TorusInverse
