/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Positivity.Finset

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
