/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational

/-!
# Fourier coefficients of actual smooth periodic functions

Coefficients are defined by actual unit-interval integrals. Their decay is
derived from integration by parts and bounds for actual coordinate derivatives.
-/

section

/-!
# Smooth Fourier series and directional inversion on the two-dimensional torus

We work on the universal cover `ℝ × ℝ`, with frequencies in `ℤ × ℤ`.
Rapid coefficients have summable polynomially weighted norms of every order.
-/

section

/-!
# Diophantine bounds for the manuscript's graph directions

For every nonzero integer frequency `(m,n)`, the directions
`v_r = (1, 1 - sqrt 2)` and `v_t = (sqrt 2 - 1, 1)` have symbols bounded
below by `(1/6)/(1 + sqrt (m^2+n^2))`. The proof multiplies each quadratic
integer by its conjugate, proves that the resulting integer is nonzero using
irrationality of `sqrt 2`, and bounds the conjugate explicitly.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.DiophantineGraph

/-- Quadratic form, given by `(p : ℝ) + Real.sqrt 2 * (q : ℝ)`. -/
def quadraticForm (p q : ℤ) : ℝ := (p : ℝ) + Real.sqrt 2 * (q : ℝ)

/-- Integer norm, given by `p ^ 2 - 2 * q ^ 2`. -/
def integerNorm (p q : ℤ) : ℤ := p ^ 2 - 2 * q ^ 2

theorem sqrt_two_square : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
  Real.sq_sqrt (by norm_num)

theorem sqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
  nlinarith [sqrt_two_square, Real.sqrt_nonneg (2 : ℝ)]

theorem quadraticForm_ne_zero (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) :
    quadraticForm p q ≠ 0 := by
  by_cases hq : q = 0
  · have hp : p ≠ 0 := hpq.resolve_right (not_not.mpr hq)
    simpa [quadraticForm, hq] using hp
  · exact ((irrational_sqrt_two.mul_intCast hq).intCast_add p).ne_zero

theorem conjugate_product (p q : ℤ) :
    quadraticForm p q * quadraticForm p (-q) = (integerNorm p q : ℝ) := by
  simp only [quadraticForm, integerNorm, Int.cast_neg, Int.cast_sub,
    Int.cast_pow, Int.cast_mul, Int.cast_ofNat]
  nlinarith [congrArg (fun x : ℝ => x * (q : ℝ) ^ 2) sqrt_two_square]

theorem integerNorm_ne_zero (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) :
    integerNorm p q ≠ 0 := by
  have hconj : p ≠ 0 ∨ -q ≠ 0 := by
    rcases hpq with hp | hq
    · exact Or.inl hp
    · exact Or.inr (neg_ne_zero.mpr hq)
  have hprod := mul_ne_zero (quadraticForm_ne_zero p q hpq)
    (quadraticForm_ne_zero p (-q) hconj)
  intro hz
  apply hprod
  rw [conjugate_product, hz, Int.cast_zero]

/-- The nonzero algebraic norm is an integer, so its absolute value is at least one. -/
theorem conjugate_product_lower (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) :
    1 ≤ |quadraticForm p q| * |quadraticForm p (-q)| := by
  have hi : (1 : ℤ) ≤ |integerNorm p q| :=
    Int.add_one_le_iff.mpr (abs_pos.mpr (integerNorm_ne_zero p q hpq))
  have hr : (1 : ℝ) ≤ |(integerNorm p q : ℝ)| := by exact_mod_cast hi
  rw [← conjugate_product, abs_mul] at hr
  exact hr

/-- Radial symbol, given by `quadraticForm (m + n) (-n)`. -/
def radialSymbol (m n : ℤ) : ℝ := quadraticForm (m + n) (-n)

/-- Time symbol, given by `quadraticForm (n - m) m`. -/
def timeSymbol (m n : ℤ) : ℝ := quadraticForm (n - m) m

/-- Radial conjugate, given by `quadraticForm (m + n) n`. -/
def radialConjugate (m n : ℤ) : ℝ := quadraticForm (m + n) n

/-- Time conjugate, given by `quadraticForm (n - m) (-m)`. -/
def timeConjugate (m n : ℤ) : ℝ := quadraticForm (n - m) (-m)

theorem radialSymbol_formula (m n : ℤ) :
    radialSymbol m n = (m : ℝ) + (1 - Real.sqrt 2) * (n : ℝ) := by
  simp only [radialSymbol, quadraticForm, Int.cast_add, Int.cast_neg]
  ring

theorem timeSymbol_formula (m n : ℤ) :
    timeSymbol m n = (Real.sqrt 2 - 1) * (m : ℝ) + (n : ℝ) := by
  simp only [timeSymbol, quadraticForm, Int.cast_sub]
  ring

theorem radialConjugate_formula (m n : ℤ) :
    radialConjugate m n = (m : ℝ) + (1 + Real.sqrt 2) * (n : ℝ) := by
  simp only [radialConjugate, quadraticForm, Int.cast_add]
  ring

theorem timeConjugate_formula (m n : ℤ) :
    timeConjugate m n = (n : ℝ) - (1 + Real.sqrt 2) * (m : ℝ) := by
  simp only [timeConjugate, quadraticForm, Int.cast_sub, Int.cast_neg]
  ring

theorem radial_product_lower (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    1 ≤ |radialSymbol m n| * |radialConjugate m n| := by
  have hpq : m + n ≠ 0 ∨ -n ≠ 0 := by
    by_cases hn : n = 0
    · left
      simpa [hn] using hmn.resolve_right (not_not.mpr hn)
    · exact Or.inr (neg_ne_zero.mpr hn)
  simpa only [radialSymbol, radialConjugate, neg_neg] using
    conjugate_product_lower (m + n) (-n) hpq

theorem time_product_lower (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    1 ≤ |timeSymbol m n| * |timeConjugate m n| := by
  have hpq : n - m ≠ 0 ∨ m ≠ 0 := by
    by_cases hm : m = 0
    · left
      simpa [hm] using hmn.resolve_left (not_not.mpr hm)
    · exact Or.inr hm
  exact conjugate_product_lower (n - m) m hpq

/-- Frequency L1, given by `|(m : ℝ)| + |(n : ℝ)|`. -/
def frequencyL1 (m n : ℤ) : ℝ := |(m : ℝ)| + |(n : ℝ)|

/-- This is the usual Euclidean length of the integer frequency. -/
def frequencyLength (m n : ℤ) : ℝ := Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)

theorem frequencyL1_nonneg (m n : ℤ) : 0 ≤ frequencyL1 m n := by
  unfold frequencyL1
  positivity

theorem frequencyLength_nonneg (m n : ℤ) : 0 ≤ frequencyLength m n :=
  Real.sqrt_nonneg _

theorem radialConjugate_upper (m n : ℤ) :
    |radialConjugate m n| ≤ 3 * frequencyL1 m n := by
  rw [radialConjugate_formula]
  calc
    |(m : ℝ) + (1 + Real.sqrt 2) * (n : ℝ)| ≤
        |(m : ℝ)| + |(1 + Real.sqrt 2) * (n : ℝ)| := abs_add_le _ _
    _ = |(m : ℝ)| + (1 + Real.sqrt 2) * |(n : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + Real.sqrt 2)]
    _ ≤ 3 * frequencyL1 m n := by
      unfold frequencyL1
      nlinarith [mul_le_mul_of_nonneg_right sqrt_two_le_two (abs_nonneg (n : ℝ)),
        abs_nonneg (m : ℝ)]

theorem timeConjugate_upper (m n : ℤ) :
    |timeConjugate m n| ≤ 3 * frequencyL1 m n := by
  rw [timeConjugate_formula]
  calc
    |(n : ℝ) - (1 + Real.sqrt 2) * (m : ℝ)| ≤
        |(n : ℝ)| + |(1 + Real.sqrt 2) * (m : ℝ)| := abs_sub _ _
    _ = |(n : ℝ)| + (1 + Real.sqrt 2) * |(m : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + Real.sqrt 2)]
    _ ≤ 3 * frequencyL1 m n := by
      unfold frequencyL1
      nlinarith [mul_le_mul_of_nonneg_right sqrt_two_le_two (abs_nonneg (m : ℝ)),
        abs_nonneg (n : ℝ)]

theorem frequencyL1_le_twice_length (m n : ℤ) :
    frequencyL1 m n ≤ 2 * frequencyLength m n := by
  have hs : frequencyLength m n ^ 2 = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hm : |(m : ℝ)| ≤ frequencyLength m n := by
    apply (sq_le_sq₀ (abs_nonneg _) (frequencyLength_nonneg m n)).mp
    rw [sq_abs, hs]
    nlinarith [sq_nonneg (n : ℝ)]
  have hn : |(n : ℝ)| ≤ frequencyLength m n := by
    apply (sq_le_sq₀ (abs_nonneg _) (frequencyLength_nonneg m n)).mp
    rw [sq_abs, hs]
    nlinarith [sq_nonneg (m : ℝ)]
  unfold frequencyL1
  linarith

theorem lower_of_conjugate_bound {a b D : ℝ} (hprod : 1 ≤ |a| * |b|)
    (hD : 0 < D) (hb : |b| ≤ D) : 1 / D ≤ |a| := by
  apply (div_le_iff₀ hD).mpr
  exact hprod.trans (mul_le_mul_of_nonneg_left hb (abs_nonneg a))

/-- Explicit Diophantine bound for `v_r = (1,1-sqrt 2)` in the L1 length. -/
theorem radial_diophantine_l1 (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    (1 / 3 : ℝ) / (1 + frequencyL1 m n) ≤ |radialSymbol m n| := by
  rw [div_div]
  apply lower_of_conjugate_bound (radial_product_lower m n hmn)
  · have := frequencyL1_nonneg m n
    positivity
  · have := radialConjugate_upper m n
    linarith

/-- Explicit Diophantine bound for `v_t = (sqrt 2-1,1)` in the L1 length. -/
theorem time_diophantine_l1 (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    (1 / 3 : ℝ) / (1 + frequencyL1 m n) ≤ |timeSymbol m n| := by
  rw [div_div]
  apply lower_of_conjugate_bound (time_product_lower m n hmn)
  · have := frequencyL1_nonneg m n
    positivity
  · have := timeConjugate_upper m n
    linarith

/-- The manuscript's estimate with an explicit constant and Euclidean length. -/
theorem radial_diophantine (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    (1 / 6 : ℝ) / (1 + frequencyLength m n) ≤ |radialSymbol m n| := by
  rw [div_div]
  apply lower_of_conjugate_bound (radial_product_lower m n hmn)
  · have := frequencyLength_nonneg m n
    positivity
  · have := radialConjugate_upper m n
    have := frequencyL1_le_twice_length m n
    linarith

/-- The manuscript's estimate for the second graph direction. -/
theorem time_diophantine (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    (1 / 6 : ℝ) / (1 + frequencyLength m n) ≤ |timeSymbol m n| := by
  rw [div_div]
  apply lower_of_conjugate_bound (time_product_lower m n hmn)
  · have := frequencyLength_nonneg m n
    positivity
  · have := timeConjugate_upper m n
    have := frequencyL1_le_twice_length m n
    linarith

theorem radialSymbol_ne_zero (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    radialSymbol m n ≠ 0 := by
  intro hz
  have h := radial_product_lower m n hmn
  norm_num [hz] at h

theorem timeSymbol_ne_zero (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    timeSymbol m n ≠ 0 := by
  intro hz
  have h := time_product_lower m n hmn
  norm_num [hz] at h

/-- The radial inverse Fourier multiplier grows at most linearly in frequency. -/
theorem radial_reciprocal_bound (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    |1 / radialSymbol m n| ≤ 6 * (1 + frequencyLength m n) := by
  rw [abs_div, abs_one]
  apply (div_le_iff₀ (abs_pos.mpr (radialSymbol_ne_zero m n hmn))).mpr
  have hb : |radialConjugate m n| ≤ 6 * (1 + frequencyLength m n) := by
    have := radialConjugate_upper m n
    have := frequencyL1_le_twice_length m n
    linarith
  calc
    1 ≤ |radialSymbol m n| * |radialConjugate m n| := radial_product_lower m n hmn
    _ ≤ |radialSymbol m n| * (6 * (1 + frequencyLength m n)) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

/-- The temporal inverse Fourier multiplier grows at most linearly in frequency. -/
theorem time_reciprocal_bound (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    |1 / timeSymbol m n| ≤ 6 * (1 + frequencyLength m n) := by
  rw [abs_div, abs_one]
  apply (div_le_iff₀ (abs_pos.mpr (timeSymbol_ne_zero m n hmn))).mpr
  have hb : |timeConjugate m n| ≤ 6 * (1 + frequencyLength m n) := by
    have := timeConjugate_upper m n
    have := frequencyL1_le_twice_length m n
    linarith
  calc
    1 ≤ |timeSymbol m n| * |timeConjugate m n| := time_product_lower m n hmn
    _ ≤ |timeSymbol m n| * (6 * (1 + frequencyLength m n)) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

/-- Repeated radial inversion has the corresponding finite polynomial loss. -/
theorem radial_inverse_power_bound (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) (p : ℕ) :
    |1 / radialSymbol m n| ^ p ≤ (6 * (1 + frequencyLength m n)) ^ p := by
  exact pow_le_pow_left₀ (abs_nonneg _) (radial_reciprocal_bound m n hmn) p

/-- Repeated temporal inversion has the corresponding finite polynomial loss. -/
theorem time_inverse_power_bound (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) (p : ℕ) :
    |1 / timeSymbol m n| ^ p ≤ (6 * (1 + frequencyLength m n)) ^ p := by
  exact pow_le_pow_left₀ (abs_nonneg _) (time_reciprocal_bound m n hmn) p

/-- Both estimates packaged for a nonzero integer vector. -/
theorem graph_directions_diophantine (k : ℤ × ℤ) (hk : k ≠ 0) :
    (1 / 6 : ℝ) / (1 + frequencyLength k.1 k.2) ≤
        |(k.1 : ℝ) + (1 - Real.sqrt 2) * (k.2 : ℝ)| ∧
      (1 / 6 : ℝ) / (1 + frequencyLength k.1 k.2) ≤
        |(Real.sqrt 2 - 1) * (k.1 : ℝ) + (k.2 : ℝ)| := by
  have hmn : k.1 ≠ 0 ∨ k.2 ≠ 0 := by
    by_cases hm : k.1 = 0
    · right
      intro hn
      exact hk (Prod.ext hm hn)
    · exact Or.inl hm
  constructor
  · simpa only [radialSymbol_formula] using radial_diophantine k.1 k.2 hmn
  · simpa only [timeSymbol_formula] using time_diophantine k.1 k.2 hmn

/-- The integer matrix `[[3,1],[1,5]]` acting on a frequency. -/
def coveringFrequency (k : ℤ × ℤ) : ℤ × ℤ :=
  (3 * k.1 + k.2, k.1 + 5 * k.2)

theorem coveringFrequency_injective : Function.Injective coveringFrequency := by
  intro k l hkl
  have h₁ := congrArg Prod.fst hkl
  have h₂ := congrArg Prod.snd hkl
  simp only [coveringFrequency] at h₁ h₂
  apply Prod.ext <;> linarith

theorem coveringFrequency_ne_zero (k : ℤ × ℤ) (hk : k ≠ 0) :
    coveringFrequency k ≠ 0 := by
  intro hz
  apply hk
  apply coveringFrequency_injective
  simpa [coveringFrequency] using hz

/-- The radial symbol scales by the smaller eigenvalue of the covering matrix. -/
theorem radial_symbol_covering (k : ℤ × ℤ) :
    radialSymbol (coveringFrequency k).1 (coveringFrequency k).2 =
      (4 - Real.sqrt 2) * radialSymbol k.1 k.2 := by
  simp only [coveringFrequency, radialSymbol_formula, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat]
  nlinarith [congrArg (fun x : ℝ => x * (k.2 : ℝ)) sqrt_two_square]

/-- The temporal symbol scales by the larger eigenvalue of the covering matrix. -/
theorem time_symbol_covering (k : ℤ × ℤ) :
    timeSymbol (coveringFrequency k).1 (coveringFrequency k).2 =
      (4 + Real.sqrt 2) * timeSymbol k.1 k.2 := by
  simp only [coveringFrequency, timeSymbol_formula, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat]
  nlinarith [congrArg (fun x : ℝ => x * (k.1 : ℝ)) sqrt_two_square]

theorem covering_eigenvalues_gt_one :
    1 < 4 - Real.sqrt 2 ∧ 1 < 4 + Real.sqrt 2 := by
  constructor <;> nlinarith [sqrt_two_le_two, Real.sqrt_nonneg (2 : ℝ)]

end NavierStokes.DiophantineGraph

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.TorusInverse

open scoped BigOperators Topology ContDiff

/-- Frequency: an abbreviation for `ℤ × ℤ`. -/
abbrev Frequency := ℤ × ℤ
/-- Plane: an abbreviation for `ℝ × ℝ`. -/
abbrev Plane := ℝ × ℝ

/-- Weight, given by `1 + |(k.1 : ℝ)| + |(k.2 : ℝ)|`. -/
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

/-- Omega, given by `2 * Real.pi * Complex.I`. -/
def omega : ℂ := 2 * Real.pi * Complex.I

/-- Freq X, given by `omega * (k.1 : ℂ)`. -/
def freqX (k : Frequency) : ℂ := omega * (k.1 : ℂ)
/-- Freq Y, given by `omega * (k.2 : ℂ)`. -/
def freqY (k : Frequency) : ℂ := omega * (k.2 : ℂ)

/-- Dx, given by `ContinuousLinearMap.fst ℝ ℝ ℝ`. -/
def dx : Plane →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
/-- Dy, given by `ContinuousLinearMap.snd ℝ ℝ ℝ`. -/
def dy : Plane →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Lift X, given by `ContinuousLinearMap.smulRightL ℝ Plane ℂ dx`. -/
def liftX : ℂ →L[ℝ] (Plane →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ Plane ℂ dx
/-- Lift Y, given by `ContinuousLinearMap.smulRightL ℝ Plane ℂ dy`. -/
def liftY : ℂ →L[ℝ] (Plane →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ Plane ℂ dy

@[simp] theorem liftX_apply (c : ℂ) (x : Plane) : liftX c x = x.1 • c := rfl
@[simp] theorem liftY_apply (c : ℂ) (x : Plane) : liftY c x = x.2 • c := rfl

/-- Phase, given by `liftX (freqX k) + liftY (freqY k)`. -/
def phase (k : Frequency) : Plane →L[ℝ] ℂ := liftX (freqX k) + liftY (freqY k)

/-- Mode, given by `Complex.exp (phase k x)`. -/
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

/-- Deriv X, given by `freqX k * a k`. -/
def derivX (a : Frequency → ℂ) (k : Frequency) : ℂ := freqX k * a k
/-- Deriv Y, given by `freqY k * a k`. -/
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

/-- Series, given by `∑' k, a k * mode k x`. -/
def series (a : Frequency → ℂ) (x : Plane) : ℂ := ∑' k, a k * mode k x

theorem summable_terms {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    Summable (fun k => a k * mode k x) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_mode, mul_one] using ha.summable_norm

theorem continuous_series {a : Frequency → ℂ} (ha : Rapid a) : Continuous (series a) := by
  apply continuous_tsum (fun k => continuous_const.fun_mul (continuous_mode k)) ha.summable_norm
  intro k x
  simp only [norm_mul, norm_mode, mul_one, le_refl]

/-- Term derivative, given by `liftX (derivX a k * mode k x) + liftY (derivY a k * mode k x)`. -/
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

/-- Derivative majorant, given by `‖liftX‖ * ‖derivX a k‖ + ‖liftY‖ * ‖derivY a k‖`. -/
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

/-- Direction data for torus inverse. -/
inductive Direction
  | radial
  | temporal
  deriving DecidableEq

/-- Vector as an element of `Direction → Plane | .radial => (1, 1 - Real.sqrt 2) | .temporal =>
(Real.sqrt 2 - 1, 1)`. -/
def vector : Direction → Plane
  | .radial => (1, 1 - Real.sqrt 2)
  | .temporal => (Real.sqrt 2 - 1, 1)

/-- Symbol as an element of `Direction → Frequency → ℝ | .radial, k =>
DiophantineGraph.radialSymbol k.1 k.2 | .temporal, k => DiophantineGraph.timeSymbol k.1
k.2`. -/
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

/-- Multiplier, given by `(omega * (symbol d k : ℂ))⁻¹`. -/
def multiplier (d : Direction) (k : Frequency) : ℂ := (omega * (symbol d k : ℂ))⁻¹
/-- Inverse coefficient, given by `multiplier d k * a k`. -/
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

/-- Directional inverse, given by `series (inverseCoeff d a)`. -/
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
local instance instTorusInverse1 : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- Torus: an abbreviation for `UnitAddCircle × UnitAddCircle`. -/
abbrev Torus := UnitAddCircle × UnitAddCircle

/-- Torus measure as an element of `Measure Torus`. -/
def torusMeasure : Measure Torus :=
  (AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle

instance : IsProbabilityMeasure torusMeasure := by
  unfold torusMeasure
  infer_instance

/-- Torus mode, bundling `toFun`, `continuous_toFun`. -/
def torusMode (k : Frequency) : C(Torus, ℂ) where
  toFun z := fourier k.1 z.1 * fourier k.2 z.2
  continuous_toFun := ((fourier k.1).continuous.comp continuous_fst).mul
    ((fourier k.2).continuous.comp continuous_snd)

theorem norm_torusMode (k : Frequency) (z : Torus) : ‖torusMode k z‖ = 1 := by
  simp [torusMode, fourier_apply, Circle.norm_coe]

/-- Torus series, given by `∑' k, a k * torusMode k z`. -/
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

/-- Coordinate coefficient, with branches according to `j`. -/
def coordinateCoeff (j : Bool) (a : Frequency → ℂ) : Frequency → ℂ :=
  if j then derivY a else derivX a

/-- Coordinate partial, given by `fderiv ℝ f x (if j then (0, 1) else (1, 0))`. -/
def coordinatePartial (j : Bool) (f : Plane → ℂ) (x : Plane) : ℂ :=
  fderiv ℝ f x (if j then (0, 1) else (1, 0))

/-- Coefficient word as an element of `js, a => coordinateCoeff j (coefficientWord js a)`. -/
def coefficientWord : List Bool → (Frequency → ℂ) → Frequency → ℂ
  | [], a => a
  | j :: js, a => coordinateCoeff j (coefficientWord js a)

/-- Derivative word as an element of `js, f => coordinatePartial j (derivativeWord js f)`. -/
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

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.SmoothFourierData

open Set Function MeasureTheory TorusInverse
open scoped BigOperators ContDiff Interval Topology

local instance instSmoothFourierData1 : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- The actual unit-period Fourier coefficient of a function on the line. -/
def unitCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f n

theorem unitCoeff_eq_integral (f : ℝ → ℂ) (n : ℤ) :
    unitCoeff f n = ∫ x in (0 : ℝ)..1, fourier (-n) (x : UnitAddCircle) * f x := by
  have h := fourierCoeffOn_eq_integral f n (show (0 : ℝ) < 1 by norm_num)
  simpa [unitCoeff, fourier_coe_apply, smul_eq_mul] using h

theorem unitCoeff_const_mul (f : ℝ → ℂ) (c : ℂ) (n : ℤ) :
    unitCoeff (fun x => c * f x) n = c * unitCoeff f n :=
  fourierCoeffOn.const_mul f c n (show (0 : ℝ) < 1 by norm_num)

theorem unitCoeff_norm_le {f : ℝ → ℂ} {C : ℝ} (n : ℤ)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C) : ‖unitCoeff f n‖ ≤ C := by
  rw [unitCoeff_eq_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := C) (f := fun x => fourier (-n) (x : UnitAddCircle) * f x)
    (fun x hx => by
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using uIoc_subset_uIcc hx
      simpa only [norm_mul, fourier_apply, Circle.norm_coe, one_mul] using hb x hx')
  simpa only [sub_zero, abs_one, mul_one] using h

/-- The boundary term cancels because the actual endpoint values agree. -/
theorem unitCoeff_of_hasDerivAt {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f') (hp : f 1 = f 0) :
    unitCoeff f n = (omega * (n : ℂ))⁻¹ * unitCoeff f' n := by
  have h := fourierCoeffOn_of_hasDerivAt (show (0 : ℝ) < 1 by norm_num) hn
    (fun x _ => hd x) (hc.intervalIntegrable 0 1)
  have hden : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = -(omega * (n : ℂ)) := by
    unfold omega
    ring
  simpa only [unitCoeff, hp, sub_self, mul_zero, sub_zero, Complex.ofReal_one,
    Complex.ofReal_zero, one_mul, zero_sub, hden, one_div, inv_neg, neg_mul_neg] using h

/-- Unit-periodicity in both coordinates, expressed on the universal cover. -/
def UnitPeriodic (f : Plane → ℂ) : Prop :=
  ∀ z : Plane, ∀ k : Frequency, f (z + ((k.1 : ℝ), (k.2 : ℝ))) = f z

/-- The genuine first coordinate derivative. -/
noncomputable def partialX (f : Plane → ℂ) (z : Plane) : ℂ := fderiv ℝ f z (1, 0)

/-- X jet, given by `partialX^[p] f`. -/
noncomputable def xJet (p : ℕ) (f : Plane → ℂ) : Plane → ℂ := partialX^[p] f

@[simp] theorem xJet_zero (f : Plane → ℂ) : xJet 0 f = f := rfl

theorem xJet_succ (p : ℕ) (f : Plane → ℂ) : xJet (p + 1) f = partialX (xJet p f) := by
  exact Function.iterate_succ_apply' partialX p f

theorem partialX_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (partialX f) :=
  (ContinuousLinearMap.apply ℝ ℂ (1, 0)).contDiff.comp
    (hf.fderiv_right (by simp))

theorem xJet_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (p : ℕ) :
    ContDiff ℝ ∞ (xJet p f) := by
  induction p with
  | zero => exact hf
  | succ p ih => rw [xJet_succ]; exact partialX_smooth ih

theorem partialX_periodic {f : Plane → ℂ} (hf : UnitPeriodic f) :
    UnitPeriodic (partialX f) := by
  intro z k
  have hfun : (fun w : Plane => f (w + ((k.1 : ℝ), (k.2 : ℝ)))) = f := funext fun w => hf w k
  have h := congrArg (fun g : Plane → ℂ => fderiv ℝ g z) hfun
  rw [fderiv_comp_add_right] at h
  exact congrArg (fun L : Plane →L[ℝ] ℂ => L (1, 0)) h

theorem xJet_periodic {f : Plane → ℂ} (hf : UnitPeriodic f) (p : ℕ) :
    UnitPeriodic (xJet p f) := by
  induction p with
  | zero => exact hf
  | succ p ih => rw [xJet_succ]; exact partialX_periodic ih

theorem hasDerivAt_slice {f : Plane → ℂ} {x y : ℝ}
    (hf : DifferentiableAt ℝ f (x, y)) :
    HasDerivAt (fun t => f (t, y)) (partialX f (x, y)) x := by
  exact hf.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

/-- The actual two-dimensional Fourier coefficient, with the first coordinate integrated first. -/
def coefficient (f : Plane → ℂ) (k : Frequency) : ℂ :=
  unitCoeff (fun y => unitCoeff (fun x => f (x, y)) k.1) k.2

theorem coefficient_norm_le {f : Plane → ℂ} {C : ℝ} (k : Frequency)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C) :
    ‖coefficient f k‖ ≤ C := by
  apply unitCoeff_norm_le
  intro y hy
  exact unitCoeff_norm_le k.1 (fun x hx => hb x hx y hy)

theorem coefficient_partialX {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) :
    coefficient f k = (omega * (k.1 : ℂ))⁻¹ * coefficient (partialX f) k := by
  have heq : (fun y => unitCoeff (fun x => f (x, y)) k.1) =
      (fun y => (omega * (k.1 : ℂ))⁻¹ * unitCoeff (fun x => partialX f (x, y)) k.1) := by
    funext y
    apply unitCoeff_of_hasDerivAt hk
    · intro x
      exact hasDerivAt_slice ((hf.differentiable (by simp)) (x, y))
    · exact (partialX_smooth hf).continuous.comp (continuous_id.prodMk continuous_const)
    · simpa using hp (0, y) (1, 0)
  unfold coefficient
  rw [heq, unitCoeff_const_mul]

/-- Repeated Fourier integration by parts in the first coordinate. -/
theorem coefficient_xJet {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) (p : ℕ) :
    coefficient f k = (omega * (k.1 : ℂ))⁻¹ ^ p * coefficient (xJet p f) k := by
  induction p with
  | zero => simp only [pow_zero, one_mul, xJet_zero]
  | succ p ih =>
      rw [ih, coefficient_partialX (xJet_smooth hf p) (xJet_periodic hp p) hk,
        xJet_succ, pow_succ, mul_assoc]

/-- A coefficient-decay estimate obtained from a bound on an actual derivative. -/
theorem coefficient_decay_first {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) (p : ℕ) {C : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖xJet p f (x, y)‖ ≤ C) :
    ‖coefficient f k‖ ≤ ‖(omega * (k.1 : ℂ))⁻¹‖ ^ p * C := by
  rw [coefficient_xJet hf hp hk p, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (coefficient_norm_le k hb) (pow_nonneg (norm_nonneg _) p)

/-- The negative Fourier character on the unit square. -/
def kernel (k : Frequency) (z : Plane) : ℂ :=
  fourier (-k.1) (z.1 : UnitAddCircle) * fourier (-k.2) (z.2 : UnitAddCircle)

theorem kernel_continuous (k : Frequency) : Continuous (kernel k) :=
  (((fourier (-k.1)).continuous.comp (AddCircle.continuous_mk' 1)).comp continuous_fst).mul
    (((fourier (-k.2)).continuous.comp (AddCircle.continuous_mk' 1)).comp continuous_snd)

theorem coefficient_eq_doubleIntegral (f : Plane → ℂ) (k : Frequency) :
    coefficient f k = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, kernel k (x, y) * f (x, y) := by
  unfold coefficient
  rw [unitCoeff_eq_integral]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [unitCoeff_eq_integral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  unfold kernel
  ring

theorem integral_square_swap {f : Plane → ℂ} (hf : Continuous f) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y) := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply (integral_integral_swap ?_).symm
  change Integrable f ((volume.restrict (Ioc (0 : ℝ) 1)).prod
    (volume.restrict (Ioc (0 : ℝ) 1)))
  rw [Measure.prod_restrict]
  exact (hf.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- Swap function, defined pointwise by `f (z.2, z.1)`. -/
noncomputable def swapFunction (f : Plane → ℂ) : Plane → ℂ := fun z => f (z.2, z.1)

theorem swapFunction_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (swapFunction f) := hf.comp (contDiff_snd.prodMk contDiff_fst)

theorem swapFunction_periodic {f : Plane → ℂ} (hp : UnitPeriodic f) :
    UnitPeriodic (swapFunction f) := by
  intro z k
  exact hp (z.2, z.1) (k.2, k.1)

theorem coefficient_swap {f : Plane → ℂ} (hf : Continuous f) (k : Frequency) :
    coefficient f k = coefficient (swapFunction f) (k.2, k.1) := by
  rw [coefficient_eq_doubleIntegral, coefficient_eq_doubleIntegral,
    integral_square_swap ((kernel_continuous k).fun_mul hf)]
  apply intervalIntegral.integral_congr
  intro x _
  apply intervalIntegral.integral_congr
  intro y _
  unfold kernel swapFunction
  ring

theorem coefficient_decay_second {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.2 ≠ 0) (p : ℕ) {C : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet p (swapFunction f) (x, y)‖ ≤ C) :
    ‖coefficient f k‖ ≤ ‖(omega * (k.2 : ℂ))⁻¹‖ ^ p * C := by
  rw [coefficient_swap hf.continuous k]
  exact coefficient_decay_first (swapFunction_smooth hf) (swapFunction_periodic hp) hk p hb

theorem norm_omega_ge_one : 1 ≤ ‖omega‖ := by
  have hnorm : ‖omega‖ = 2 * Real.pi := by
    simp [omega, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm]
  linarith [Real.two_le_pi]

/-- Multiplying by the first frequency power is controlled by the actual derivative norm. -/
theorem coefficient_first_moment {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) (p : ℕ) {C : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖xJet p f (x, y)‖ ≤ C) :
    |(k.1 : ℝ)| ^ p * ‖coefficient f k‖ ≤ C := by
  have hsymbol : omega * (k.1 : ℂ) ≠ 0 :=
    mul_ne_zero omega_ne_zero (by exact_mod_cast hk)
  have hident : (omega * (k.1 : ℂ)) ^ p * coefficient f k = coefficient (xJet p f) k := by
    rw [coefficient_xJet hf hp hk p, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hsymbol, one_pow, one_mul]
  have hn := congrArg norm hident
  simp only [norm_mul, norm_pow, Complex.norm_intCast] at hn
  have hfreq : |(k.1 : ℝ)| ≤ ‖omega‖ * |(k.1 : ℝ)| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right norm_omega_ge_one (abs_nonneg (k.1 : ℝ))
  calc
    |(k.1 : ℝ)| ^ p * ‖coefficient f k‖ ≤
        (‖omega‖ * |(k.1 : ℝ)|) ^ p * ‖coefficient f k‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hfreq p) (norm_nonneg _)
    _ = ‖coefficient (xJet p f) k‖ := hn
    _ ≤ C := coefficient_norm_le k hb

theorem dominant_coordinate_ne_zero {k : Frequency} (hk : k ≠ 0)
    (hdom : |(k.2 : ℝ)| ≤ |(k.1 : ℝ)|) : k.1 ≠ 0 := by
  intro hzero
  have hsecond : (k.2 : ℝ) = 0 := abs_eq_zero.mp
    (le_antisymm (by simpa [hzero] using hdom) (abs_nonneg _))
  exact hk (Prod.ext hzero (by exact_mod_cast hsecond))

theorem weight_le_dominant {k : Frequency} (hk : k.1 ≠ 0)
    (hdom : |(k.2 : ℝ)| ≤ |(k.1 : ℝ)|) : weight k ≤ 3 * |(k.1 : ℝ)| := by
  have hi : (1 : ℤ) ≤ |k.1| := Int.add_one_le_iff.mpr (abs_pos.mpr hk)
  have hr : (1 : ℝ) ≤ |(k.1 : ℝ)| := by exact_mod_cast hi
  unfold weight
  linarith

theorem weight_moment_of_dominant {k : Frequency} {p : ℕ} {A C : ℝ}
    (hk : k.1 ≠ 0) (hdom : |(k.2 : ℝ)| ≤ |(k.1 : ℝ)|) (hA : 0 ≤ A)
    (hb : |(k.1 : ℝ)| ^ p * A ≤ C) : weight k ^ p * A ≤ 3 ^ p * C := by
  calc
    weight k ^ p * A ≤ (3 * |(k.1 : ℝ)|) ^ p * A :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (weight_pos k).le (weight_le_dominant hk hdom) p) hA
    _ = 3 ^ p * (|(k.1 : ℝ)| ^ p * A) := by rw [mul_pow]; ring
    _ ≤ 3 ^ p * C := mul_le_mul_of_nonneg_left hb (by positivity)

/-- Finite derivative loss: a p-th frequency moment uses only the values and
the p-th pure derivative in each coordinate on the unit square. -/
theorem coefficient_polynomial_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (p : ℕ) {C : ℝ}
    (hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖xJet p f (x, y)‖ ≤ C)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet p (swapFunction f) (x, y)‖ ≤ C) (k : Frequency) :
    weight k ^ p * ‖coefficient f k‖ ≤ 3 ^ p * C := by
  by_cases hk : k = 0
  · subst k
    have hC : 0 ≤ C := (norm_nonneg _).trans (hzero 0 (by norm_num) 0 (by norm_num))
    simp only [weight, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, abs_zero, add_zero,
      one_pow, one_mul]
    exact (coefficient_norm_le 0 hzero).trans
      (le_mul_of_one_le_left hC (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)))
  rcases le_total |(k.2 : ℝ)| |(k.1 : ℝ)| with hdom | hdom
  · have hne := dominant_coordinate_ne_zero hk hdom
    exact weight_moment_of_dominant hne hdom (norm_nonneg _)
      (coefficient_first_moment hf hp hne p hfirst)
  · have hswap : (k.2, k.1) ≠ (0 : Frequency) := by
      intro h
      exact hk (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
    have hne := dominant_coordinate_ne_zero hswap hdom
    have h := weight_moment_of_dominant hne hdom
      (norm_nonneg (coefficient (swapFunction f) (k.2, k.1)))
      (coefficient_first_moment (swapFunction_smooth hf) (swapFunction_periodic hp) hne p hsecond)
    rw [← coefficient_swap hf.continuous k] at h
    have hw : weight (k.2, k.1) = weight k := by unfold weight; dsimp; ring
    simpa only [hw] using h

/-- Smoothness on the compact unit square supplies the derivative bounds;
no coefficient-decay hypothesis is used. -/
theorem exists_coefficient_polynomial_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (p : ℕ) :
    ∃ C : ℝ, ∀ k : Frequency, weight k ^ p * ‖coefficient f k‖ ≤ C := by
  have hc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn (xJet_smooth hf p).continuous.continuousOn
  obtain ⟨D, hD⟩ := hc.exists_bound_of_continuousOn
    (xJet_smooth (swapFunction_smooth hf) p).continuous.continuousOn
  let C := max A (max B D)
  refine ⟨3 ^ p * C, coefficient_polynomial_bound hf hp p ?_ ?_ ?_⟩
  · intro x hx y hy
    exact (hA (x, y) ⟨hx, hy⟩).trans (le_max_left _ _)
  · intro x hx y hy
    exact (hB (x, y) ⟨hx, hy⟩).trans ((le_max_left B D).trans (le_max_right _ _))
  · intro x hx y hy
    exact (hD (x, y) ⟨hx, hy⟩).trans ((le_max_right B D).trans (le_max_right _ _))

theorem summable_integer_weight_inv_two :
    Summable (fun n : ℤ => ((1 + |(n : ℝ)|) ^ 2)⁻¹) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hNat : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_one] using h
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast, Nat.abs_cast, add_comm, one_div] using hNat
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
      Nat.abs_cast, add_comm, one_div] using hNat

theorem weight_inv_four_le_product (k : Frequency) :
    (weight k ^ 4)⁻¹ ≤ ((1 + |(k.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(k.2 : ℝ)|) ^ 2)⁻¹ := by
  have hfirst : 1 + |(k.1 : ℝ)| ≤ weight k := by
    unfold weight
    linarith [abs_nonneg (k.2 : ℝ)]
  have hsecond : 1 + |(k.2 : ℝ)| ≤ weight k := by
    unfold weight
    linarith [abs_nonneg (k.1 : ℝ)]
  have hproduct : (1 + |(k.1 : ℝ)|) ^ 2 * (1 + |(k.2 : ℝ)|) ^ 2 ≤ weight k ^ 4 := by
    calc
      _ ≤ (weight k ^ 2) * (weight k ^ 2) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hfirst 2)
          (pow_le_pow_left₀ (by positivity) hsecond 2) (sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have h := one_div_le_one_div_of_le (by positivity :
    0 < (1 + |(k.1 : ℝ)|) ^ 2 * (1 + |(k.2 : ℝ)|) ^ 2) hproduct
  simpa only [one_div, mul_inv_rev, mul_comm] using h

theorem summable_weight_inv_four : Summable (fun k : Frequency => (weight k ^ 4)⁻¹) := by
  have hprod := summable_integer_weight_inv_two.mul_of_nonneg
    summable_integer_weight_inv_two (fun n => by positivity) (fun n => by positivity)
  exact Summable.of_nonneg_of_le (fun k => inv_nonneg.mpr (pow_nonneg (weight_pos k).le _))
    weight_inv_four_le_product hprod

/-- Every smooth unit-periodic function has all weighted absolute Fourier moments.
For the p-th moment the proof uses p+4 derivatives and a summable lattice majorant. -/
theorem rapid_coefficient {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) :
    Rapid (coefficient f) := by
  intro p
  obtain ⟨C, hC⟩ := exists_coefficient_polynomial_bound hf hp (p + 4)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (weight_pos k).le _) (norm_nonneg _)) _
    (summable_weight_inv_four.mul_left C)
  intro k
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (weight_pos k) 4)).mpr
  calc
    (weight k ^ p * ‖coefficient f k‖) * weight k ^ 4 =
        weight k ^ (p + 4) * ‖coefficient f k‖ := by rw [pow_add]; ring
    _ ≤ C := hC k

/-- A quantitative finite-loss estimate for the exact seminorm used by
`TorusInverse`. The lattice constant is finite by `summable_weight_inv_four`. -/
theorem coefficient_seminorm_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (p : ℕ) {C : ℝ}
    (hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (p + 4) f (x, y)‖ ≤ C)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (p + 4) (swapFunction f) (x, y)‖ ≤ C) :
    coeffSeminorm p (coefficient f) ≤
      (3 ^ (p + 4) * C) * ∑' k : Frequency, (weight k ^ 4)⁻¹ := by
  have hb (k : Frequency) : weight k ^ p * ‖coefficient f k‖ ≤
      (3 ^ (p + 4) * C) * (weight k ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (weight_pos k) 4)).mpr
    calc
      (weight k ^ p * ‖coefficient f k‖) * weight k ^ 4 =
          weight k ^ (p + 4) * ‖coefficient f k‖ := by rw [pow_add]; ring
      _ ≤ 3 ^ (p + 4) * C := coefficient_polynomial_bound hf hp (p + 4) hzero hfirst hsecond k
  have h := (rapid_coefficient hf hp p).tsum_le_tsum hb
    (summable_weight_inv_four.mul_left (3 ^ (p + 4) * C))
  simpa only [coeffSeminorm, tsum_mul_left] using h

/-! ## Identification with the actual torus Fourier coefficients -/

/-- Torus lift, given by `f ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle))`. -/
noncomputable def torusLift (f : Torus → ℂ) (x : Plane) : ℂ :=
  f ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle))

theorem torusLift_periodic (f : Torus → ℂ) : UnitPeriodic (torusLift f) := by
  intro z k
  simp [torusLift]

/-- Torus coefficient, given by `∫ z, torusMode (-k) z * f z ∂torusMeasure`. -/
def torusCoefficient (f : Torus → ℂ) (k : Frequency) : ℂ :=
  ∫ z, torusMode (-k) z * f z ∂torusMeasure

theorem unitCoeff_torusLift (f : UnitAddCircle → ℂ) (n : ℤ) :
    unitCoeff (fun x : ℝ => f (x : UnitAddCircle)) n = fourierCoeff f n := by
  rw [unitCoeff_eq_integral, fourierCoeff_eq_intervalIntegral f n 0]
  simp only [one_div_one, zero_add, one_smul, smul_eq_mul]

theorem torusCoefficient_integrable (f : C(Torus, ℂ)) (k : Frequency) :
    Integrable (fun z => torusMode (-k) z * f z) torusMeasure := by
  apply (integrable_const (‖f‖ : ℝ)).mono'
    ((torusMode (-k)).continuous.fun_mul f.continuous).aestronglyMeasurable
  filter_upwards with z
  simpa only [norm_mul, norm_torusMode, one_mul] using f.norm_coe_le_norm z

theorem coefficient_lift_eq_torus (f : C(Torus, ℂ)) (k : Frequency) :
    coefficient (torusLift f) k = torusCoefficient f k := by
  change unitCoeff (fun y => unitCoeff
    (fun x => f ((x : UnitAddCircle), (y : UnitAddCircle))) k.1) k.2 = _
  have hinner : (fun y : ℝ => unitCoeff
      (fun x => f ((x : UnitAddCircle), (y : UnitAddCircle))) k.1) =
      (fun y : ℝ => fourierCoeff (fun x : UnitAddCircle => f (x, (y : UnitAddCircle))) k.1) := by
    funext y
    exact unitCoeff_torusLift (fun x : UnitAddCircle => f (x, (y : UnitAddCircle))) k.1
  rw [hinner, unitCoeff_torusLift
    (fun y : UnitAddCircle => fourierCoeff (fun x : UnitAddCircle => f (x, y)) k.1) k.2]
  unfold fourierCoeff torusCoefficient
  rw [show torusMeasure = (AddCircle.haarAddCircle : Measure UnitAddCircle).prod
    AddCircle.haarAddCircle from rfl,
    integral_prod_symm _ (torusCoefficient_integrable f k)]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [torusMode, ContinuousMap.coe_mk, Prod.fst_neg, Prod.snd_neg]
  ring

/-- The same continuous function on Mathlib's native finite-product torus. -/
noncomputable def nativeFunction (f : C(Torus, ℂ)) : C(UnitAddTorus (Fin 2), ℂ) where
  toFun z := f (z 0, z 1)
  continuous_toFun := f.continuous.comp ((continuous_apply 0).prodMk (continuous_apply 1))

theorem native_mode_eq (k : Fin 2 → ℤ) (z : UnitAddTorus (Fin 2)) :
    UnitAddTorus.mFourier k z = torusMode (k 0, k 1) (z 0, z 1) := by
  simp [UnitAddTorus.mFourier, torusMode, Fin.prod_univ_two]

theorem native_coefficient_eq (f : C(Torus, ℂ)) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (nativeFunction f) k = torusCoefficient f (k 0, k 1) := by
  have h := (measurePreserving_finTwoArrow
    (AddCircle.haarAddCircle : Measure UnitAddCircle)).integral_comp'
      (fun z : Torus => torusMode (-(k 0, k 1)) z * f z)
  simp only [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier, torusMode, torusCoefficient,
    torusMeasure, nativeFunction, Fin.prod_univ_two, smul_eq_mul,
    MeasureTheory.volume_pi,
    MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo_apply] at h ⊢
  exact h

/-- Genuine Fourier reconstruction: summability is derived from smoothness. -/
theorem torusSeries_coefficient (f : C(Torus, ℂ))
    (hf : ContDiff ℝ ∞ (torusLift f)) (z : Torus) :
    torusSeries (coefficient (torusLift f)) z = f z := by
  have ha := rapid_coefficient hf (torusLift_periodic f)
  have hc (k : Fin 2 → ℤ) : UnitAddTorus.mFourierCoeff (nativeFunction f) k =
      coefficient (torusLift f) (k 0, k 1) := by
    rw [native_coefficient_eq, coefficient_lift_eq_torus]
  have hsum : Summable (UnitAddTorus.mFourierCoeff (nativeFunction f)) := by
    have hcoef : Summable (coefficient (torusLift f)) := Summable.of_norm ha.summable_norm
    have h := hcoef.comp_injective (finTwoArrowEquiv ℤ).injective
    have heq : UnitAddTorus.mFourierCoeff (nativeFunction f) =
        (fun k : Fin 2 → ℤ => coefficient (torusLift f) (k 0, k 1)) := funext hc
    rw [heq]
    exact h
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum ![z.1, z.2]
  simp_rw [hc] at h
  have hnative : HasSum (fun k : Fin 2 → ℤ =>
      coefficient (torusLift f) (k 0, k 1) * torusMode (k 0, k 1) z) (f z) := by
    simpa [hc, native_mode_eq, nativeFunction, smul_eq_mul] using h
  have hpairs : HasSum (fun k : Frequency =>
      coefficient (torusLift f) k * torusMode k z) (f z) :=
    (finTwoArrowEquiv ℤ).hasSum_iff.mp hnative
  exact hpairs.tsum_eq

theorem series_coefficient_lift (f : C(Torus, ℂ))
    (hf : ContDiff ℝ ∞ (torusLift f)) (x : Plane) :
    series (coefficient (torusLift f)) x = torusLift f x := by
  rw [series_eq_torusSeries]
  exact torusSeries_coefficient f hf _

theorem coefficient_zero_eq_mean (f : C(Torus, ℂ)) :
    coefficient (torusLift f) 0 = ∫ z, f z ∂torusMeasure := by
  rw [coefficient_lift_eq_torus]
  simp [torusCoefficient, torusMode]

/-- The constructed inverse now solves the equation for an arbitrary smooth
zero-mean torus function, not only for a preassigned coefficient sequence. -/
theorem inverse_solves_smooth_torus (d : Direction) (f : C(Torus, ℂ))
    (hf : ContDiff ℝ ∞ (torusLift f)) (hmean : (∫ z, f z ∂torusMeasure) = 0) (x : Plane) :
    fderiv ℝ (directionalInverse d (coefficient (torusLift f))) x (vector d) =
      torusLift f x := by
  have ha := rapid_coefficient hf (torusLift_periodic f)
  have hz : coefficient (torusLift f) 0 = 0 := by rw [coefficient_zero_eq_mean, hmean]
  rw [directionalInverse_solves d ha hz, series_coefficient_lift f hf]

/-! ## Descent of an arbitrary periodic function on the plane -/

theorem unitPeriodic_first {f : Plane → ℂ} (hp : UnitPeriodic f) (y : ℝ) :
    Periodic (fun x => f (x, y)) 1 := by
  intro x
  simpa using hp (x, y) (1, 0)

theorem unitPeriodic_second {f : Plane → ℂ} (hp : UnitPeriodic f) (x : ℝ) :
    Periodic (fun y => f (x, y)) 1 := by
  intro y
  simpa using hp (x, y) (0, 1)

/-- First lift, given by `(unitPeriodic_first hp y).lift z`. -/
noncomputable def firstLift (f : Plane → ℂ) (hp : UnitPeriodic f)
    (z : UnitAddCircle) (y : ℝ) : ℂ :=
  (unitPeriodic_first hp y).lift z

theorem firstLift_periodic (f : Plane → ℂ) (hp : UnitPeriodic f) (z : UnitAddCircle) :
    Periodic (firstLift f hp z) 1 := by
  intro y
  refine Quotient.inductionOn' z (fun x => ?_)
  change f (x, y + 1) = f (x, y)
  exact unitPeriodic_second hp x y

/-- Descend, given by `(firstLift_periodic f hp z.1).lift z.2`. -/
noncomputable def descend (f : Plane → ℂ) (hp : UnitPeriodic f) (z : Torus) : ℂ :=
  (firstLift_periodic f hp z.1).lift z.2

@[simp] theorem descend_coe (f : Plane → ℂ) (hp : UnitPeriodic f) (x y : ℝ) :
    descend f hp ((x : UnitAddCircle), (y : UnitAddCircle)) = f (x, y) := rfl

theorem descend_continuous {f : Plane → ℂ} (hf : Continuous f) (hp : UnitPeriodic f) :
    Continuous (descend f hp) := by
  have hq : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  apply (hq.prodMap hq).isQuotientMap.continuous_iff.mpr
  exact hf

/-- Descend continuous, bundling `toFun`, `continuous_toFun`. -/
noncomputable def descendContinuous (f : Plane → ℂ) (hf : Continuous f)
    (hp : UnitPeriodic f) : C(Torus, ℂ) where
  toFun := descend f hp
  continuous_toFun := descend_continuous hf hp

@[simp] theorem torusLift_descendContinuous (f : Plane → ℂ) (hf : Continuous f)
    (hp : UnitPeriodic f) : torusLift (descendContinuous f hf hp) = f := rfl

/-- Pointwise reconstruction for an arbitrary actual smooth unit-periodic
function on the plane; neither rapid decay nor reconstruction is a premise. -/
theorem series_coefficient {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (x : Plane) : series (coefficient f) x = f x := by
  have h := series_coefficient_lift (descendContinuous f hf.continuous hp)
    (show ContDiff ℝ ∞ (torusLift (descendContinuous f hf.continuous hp)) from hf) x
  exact h

theorem coefficient_zero_eq_integral (f : Plane → ℂ) :
    coefficient f 0 = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y) := by
  rw [coefficient_eq_doubleIntegral]
  simp [kernel]

/-- The final coefficient bridge to the existing inverse construction. -/
theorem smooth_periodic_fourier_data {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) : Rapid (coefficient f) ∧ series (coefficient f) = f :=
  ⟨rapid_coefficient hf hp, funext (series_coefficient hf hp)⟩

theorem inverse_solves_smooth_periodic (d : Direction) {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f)
    (hmean : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)) = 0) (x : Plane) :
    fderiv ℝ (directionalInverse d (coefficient f)) x (vector d) = f x := by
  have hz : coefficient f 0 = 0 := by rw [coefficient_zero_eq_integral, hmean]
  rw [directionalInverse_solves d (rapid_coefficient hf hp) hz, series_coefficient hf hp]

end NavierStokes.SmoothFourierData
