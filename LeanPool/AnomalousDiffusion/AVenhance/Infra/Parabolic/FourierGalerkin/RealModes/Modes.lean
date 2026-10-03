/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.RealModes.Frequency

/-! # Modes

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open MeasureTheory
attribute [local instance] realModesMeasureSpace realModesMeasureIsAddHaar realModesProbability
namespace AVenhance.Infra.Parabolic.FourierGalerkin

theorem Modes.pairFrequency_injective {p q : ℤ × ℤ}
    (h : pairFrequency p = pairFrequency q) : p = q := by
  have h₀ := congrFun h (0 : Fin 2)
  have h₁ := congrFun h (1 : Fin 2)
  simp only [pairFrequency, Fin.isValue, ↓reduceIte, one_ne_zero] at h₀ h₁
  exact Prod.ext h₀ h₁

theorem Modes.integral_mFourier (k : Fin 2 → ℤ) :
    ∫ x : Torus, UnitAddTorus.mFourier k x = if k = 0 then (1 : ℂ) else 0 := by
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier))
    (0 : Fin 2 → ℤ) k
  rw [ContinuousMap.inner_toLp] at h
  simpa [UnitAddTorus.mFourier_zero, eq_comm] using h

theorem Modes.mFourierCoeff_mFourier (k l : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier l) k =
      if k = l then (1 : ℂ) else 0 := by
  change ∫ x : Torus, UnitAddTorus.mFourier (-k) x *
      UnitAddTorus.mFourier l x = _
  have hprod : (fun x : Torus => UnitAddTorus.mFourier (-k) x *
      UnitAddTorus.mFourier l x) = fun x => UnitAddTorus.mFourier (-k + l) x := by
    funext x
    rw [← UnitAddTorus.mFourier_add]
  rw [hprod, Modes.integral_mFourier]
  simp [add_eq_zero_iff_eq_neg]

/-- A Fourier character in the cutoff box is exactly fixed by the finite Fourier sum. -/
theorem complexFourierPartialSumComplex_mFourier {N : ℕ} (k : Fin 2 → ℤ)
    (hk : frequencyPair k ∈ symmetricFrequencyBox N) (x : Torus) :
    complexFourierPartialSumComplex N (UnitAddTorus.mFourier k) x =
      UnitAddTorus.mFourier k x := by
  classical
  rw [complexFourierPartialSumComplex, Finset.sum_eq_single_of_mem
    (frequencyPair k) hk]
  · simp [Modes.mFourierCoeff_mFourier, pairFrequency_frequencyPair]
  · intro p hp hne
    have hfreq : pairFrequency p ≠ k := by
      intro heq
      apply hne
      apply Modes.pairFrequency_injective
      calc
        pairFrequency p = k := heq
        _ = pairFrequency (frequencyPair k) := (pairFrequency_frequencyPair k).symm
    simp [Modes.mFourierCoeff_mFourier, hfreq]

theorem Modes.integrable_mFourier_mul_of_continuous {f : Torus → ℂ}
    (hf : Continuous f) (k : Fin 2 → ℤ) :
    Integrable (fun x : Torus => UnitAddTorus.mFourier (-k) x * f x) volume := by
  exact ((UnitAddTorus.mFourier (-k)).continuous.mul hf)
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem Modes.mFourierCoeff_add_of_continuous {f g : Torus → ℂ}
    (hf : Continuous f) (hg : Continuous g) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => f x + g x) k =
      UnitAddTorus.mFourierCoeff f k + UnitAddTorus.mFourierCoeff g k := by
  change ∫ x : Torus, UnitAddTorus.mFourier (-k) x * (f x + g x) = _
  have hpoint : (fun x : Torus => UnitAddTorus.mFourier (-k) x * (f x + g x)) =
      fun x => UnitAddTorus.mFourier (-k) x * f x +
        UnitAddTorus.mFourier (-k) x * g x := by
    funext x
    ring
  rw [hpoint, integral_add (Modes.integrable_mFourier_mul_of_continuous hf k)
    (Modes.integrable_mFourier_mul_of_continuous hg k)]
  rfl

theorem Modes.mFourierCoeff_const_mul {f : Torus → ℂ}
    (c : ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x => c * f x) k =
      c * UnitAddTorus.mFourierCoeff f k := by
  change ∫ x : Torus, UnitAddTorus.mFourier (-k) x * (c * f x) = _
  have hpoint : (fun x : Torus => UnitAddTorus.mFourier (-k) x * (c * f x)) =
      fun x => c * (UnitAddTorus.mFourier (-k) x * f x) := by
    funext x
    ring
  rw [hpoint, integral_const_mul]
  rfl

theorem complexFourierPartialSumComplex_add {N : ℕ} {f g : Torus → ℂ}
    (hf : Continuous f) (hg : Continuous g) (x : Torus) :
    complexFourierPartialSumComplex N (fun y => f y + g y) x =
      complexFourierPartialSumComplex N f x +
        complexFourierPartialSumComplex N g x := by
  classical
  unfold complexFourierPartialSumComplex
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Modes.mFourierCoeff_add_of_continuous hf hg]
  ring

theorem complexFourierPartialSumComplex_const_mul {N : ℕ} {f : Torus → ℂ}
    (c : ℂ) (x : Torus) :
    complexFourierPartialSumComplex N (fun y => c * f y) x =
      c * complexFourierPartialSumComplex N f x := by
  classical
  unfold complexFourierPartialSumComplex
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Modes.mFourierCoeff_const_mul c]
  ring

theorem Modes.ofReal_sqrtTwo_mul_re (z : ℂ) :
    ((Real.sqrt 2 * z.re : ℝ) : ℂ) =
      (Real.sqrt 2 / 2 : ℝ) * (z + star z) := by
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp [Complex.mul_im]

theorem Modes.ofReal_sqrtTwo_mul_im (z : ℂ) :
    ((Real.sqrt 2 * z.im : ℝ) : ℂ) =
      (Real.sqrt 2 / 2 : ℝ) * (-Complex.I) * (z - star z) := by
  apply Complex.ext
  · simp [Complex.mul_re]
    ring
  · simp [Complex.mul_im]

theorem Modes.mFourier_star_at (k : Fin 2 → ℤ) (x : Torus) :
    star (UnitAddTorus.mFourier k x) = UnitAddTorus.mFourier (-k) x := by
  rw [Complex.star_def]
  exact (UnitAddTorus.mFourier_neg (n := k) (x := x)).symm

theorem Modes.integrable_mFourier (k : Fin 2 → ℤ) :
    Integrable (fun x : Torus => UnitAddTorus.mFourier k x) volume := by
  exact (UnitAddTorus.mFourier k).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem Modes.integral_re_mFourier (k : Fin 2 → ℤ) :
    ∫ x : Torus, (UnitAddTorus.mFourier k x).re = if k = 0 then 1 else 0 := by
  change ∫ x : Torus, Complex.reCLM (UnitAddTorus.mFourier k x) = _
  rw [Complex.reCLM.integral_comp_comm (Modes.integrable_mFourier k), Modes.integral_mFourier]
  by_cases hk : k = 0 <;> simp [hk]

theorem Modes.integral_im_mFourier (k : Fin 2 → ℤ) :
    ∫ x : Torus, (UnitAddTorus.mFourier k x).im = 0 := by
  change ∫ x : Torus, Complex.imCLM (UnitAddTorus.mFourier k x) = _
  rw [Complex.imCLM.integral_comp_comm (Modes.integrable_mFourier k), Modes.integral_mFourier]
  by_cases hk : k = 0 <;> simp [hk]

theorem Modes.integrable_re_mFourier (k : Fin 2 → ℤ) :
    Integrable (fun x : Torus => (UnitAddTorus.mFourier k x).re) volume := by
  exact (Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous)
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem Modes.integrable_im_mFourier (k : Fin 2 → ℤ) :
    Integrable (fun x : Torus => (UnitAddTorus.mFourier k x).im) volume := by
  exact (Complex.continuous_im.comp (UnitAddTorus.mFourier k).continuous)
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem Modes.integral_re_fourierProduct (k l : Fin 2 → ℤ) :
    ∫ x : Torus, (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x).re =
      if k = -l then 1 else 0 := by
  have heq : (fun x : Torus =>
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x).re) =
      fun x => (UnitAddTorus.mFourier (k + l) x).re := by
    funext x
    rw [← UnitAddTorus.mFourier_add]
  rw [heq, Modes.integral_re_mFourier]
  simp [add_eq_zero_iff_eq_neg]

theorem Modes.integral_im_fourierProduct (k l : Fin 2 → ℤ) :
    ∫ x : Torus, (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x).im = 0 := by
  have heq : (fun x : Torus =>
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x).im) =
      fun x => (UnitAddTorus.mFourier (k + l) x).im := by
    funext x
    rw [← UnitAddTorus.mFourier_add]
  rw [heq, Modes.integral_im_mFourier]

theorem Modes.two_re_mul_re (z w : ℂ) :
    2 * z.re * w.re = (z * w).re + (z * star w).re := by
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring_nf

theorem Modes.two_im_mul_im (z w : ℂ) :
    2 * z.im * w.im = (z * star w).re - (z * w).re := by
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring_nf

theorem Modes.two_re_mul_im (z w : ℂ) :
    2 * z.re * w.im = (z * w).im - (z * star w).im := by
  simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring_nf

theorem Modes.two_im_mul_re (z w : ℂ) :
    2 * z.im * w.re = (z * w).im + (z * star w).im := by
  simp [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring_nf

theorem Modes.mFourier_add_at (k l : Fin 2 → ℤ) (x : Torus) :
    UnitAddTorus.mFourier (k + l) x =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier l x := by
  exact UnitAddTorus.mFourier_add

theorem Modes.mFourier_sub_at (k l : Fin 2 → ℤ) (x : Torus) :
    UnitAddTorus.mFourier (k - l) x =
      UnitAddTorus.mFourier k x * star (UnitAddTorus.mFourier l x) := by
  calc
    UnitAddTorus.mFourier (k - l) x = UnitAddTorus.mFourier (k + -l) x := by
      rw [sub_eq_add_neg]
    _ = UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-l) x :=
      Modes.mFourier_add_at k (-l) x
    _ = _ := by rw [UnitAddTorus.mFourier_neg, Complex.star_def]

theorem Modes.integral_re_mul_re (k l : Fin 2 → ℤ) :
    ∫ x : Torus, (UnitAddTorus.mFourier k x).re * (UnitAddTorus.mFourier l x).re =
      (if k = -l then (1 : ℝ) / 2 else 0) +
        (if k = l then (1 : ℝ) / 2 else 0) := by
  have hpoint : ∀ x : Torus,
      (UnitAddTorus.mFourier k x).re * (UnitAddTorus.mFourier l x).re =
        (1 / 2 : ℝ) * ((UnitAddTorus.mFourier (k + l) x).re +
          (UnitAddTorus.mFourier (k - l) x).re) := by
    intro x
    rw [Modes.mFourier_add_at, Modes.mFourier_sub_at]
    have h := Modes.two_re_mul_re (UnitAddTorus.mFourier k x) (UnitAddTorus.mFourier l x)
    nlinarith
  calc
    _ = ∫ x : Torus, (1 / 2 : ℝ) *
          ((UnitAddTorus.mFourier (k + l) x).re +
            (UnitAddTorus.mFourier (k - l) x).re) := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    _ = (1 / 2 : ℝ) *
          ((∫ x : Torus, (UnitAddTorus.mFourier (k + l) x).re) +
            (∫ x : Torus, (UnitAddTorus.mFourier (k - l) x).re)) := by
      rw [integral_const_mul, integral_add (Modes.integrable_re_mFourier _)
          (Modes.integrable_re_mFourier _)]
    _ = _ := by
      rw [Modes.integral_re_mFourier, Modes.integral_re_mFourier]
      have hplus : (k + l = 0) = (k = -l) := propext add_eq_zero_iff_eq_neg
      have hminus : (k - l = 0) = (k = l) := propext sub_eq_zero
      simp only [hplus, hminus, mul_add, mul_ite, mul_one, mul_zero]

theorem Modes.integral_im_mul_im (k l : Fin 2 → ℤ) :
    ∫ x : Torus, (UnitAddTorus.mFourier k x).im * (UnitAddTorus.mFourier l x).im =
      (if k = l then (1 : ℝ) / 2 else 0) -
        (if k = -l then (1 : ℝ) / 2 else 0) := by
  have hpoint : ∀ x : Torus,
      (UnitAddTorus.mFourier k x).im * (UnitAddTorus.mFourier l x).im =
        (1 / 2 : ℝ) * ((UnitAddTorus.mFourier (k - l) x).re -
          (UnitAddTorus.mFourier (k + l) x).re) := by
    intro x
    rw [Modes.mFourier_sub_at, Modes.mFourier_add_at]
    have h := Modes.two_im_mul_im (UnitAddTorus.mFourier k x) (UnitAddTorus.mFourier l x)
    nlinarith
  calc
    _ = ∫ x : Torus, (1 / 2 : ℝ) *
          ((UnitAddTorus.mFourier (k - l) x).re -
            (UnitAddTorus.mFourier (k + l) x).re) := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    _ = (1 / 2 : ℝ) *
          ((∫ x : Torus, (UnitAddTorus.mFourier (k - l) x).re) -
            (∫ x : Torus, (UnitAddTorus.mFourier (k + l) x).re)) := by
      rw [integral_const_mul, integral_sub (Modes.integrable_re_mFourier _)
          (Modes.integrable_re_mFourier _)]
    _ = _ := by
      rw [Modes.integral_re_mFourier, Modes.integral_re_mFourier]
      have hminus : (k - l = 0) = (k = l) := propext sub_eq_zero
      have hplus : (k + l = 0) = (k = -l) := propext add_eq_zero_iff_eq_neg
      simp only [hminus, hplus, mul_sub, mul_ite, mul_one, mul_zero]

theorem Modes.integral_re_mul_im (k l : Fin 2 → ℤ) :
    ∫ x : Torus, (UnitAddTorus.mFourier k x).re * (UnitAddTorus.mFourier l x).im = 0 := by
  have hpoint : ∀ x : Torus,
      (UnitAddTorus.mFourier k x).re * (UnitAddTorus.mFourier l x).im =
        (1 / 2 : ℝ) * ((UnitAddTorus.mFourier (k + l) x).im -
          (UnitAddTorus.mFourier (k - l) x).im) := by
    intro x
    rw [Modes.mFourier_add_at, Modes.mFourier_sub_at]
    have h := Modes.two_re_mul_im (UnitAddTorus.mFourier k x) (UnitAddTorus.mFourier l x)
    nlinarith
  calc
    _ = ∫ x : Torus, (1 / 2 : ℝ) *
          ((UnitAddTorus.mFourier (k + l) x).im -
            (UnitAddTorus.mFourier (k - l) x).im) := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    _ = (1 / 2 : ℝ) *
          ((∫ x : Torus, (UnitAddTorus.mFourier (k + l) x).im) -
            (∫ x : Torus, (UnitAddTorus.mFourier (k - l) x).im)) := by
      rw [integral_const_mul, integral_sub (Modes.integrable_im_mFourier _)
          (Modes.integrable_im_mFourier _)]
    _ = 0 := by rw [Modes.integral_im_mFourier, Modes.integral_im_mFourier]; ring

theorem Modes.integral_im_mul_re (k l : Fin 2 → ℤ) :
    ∫ x : Torus, (UnitAddTorus.mFourier k x).im * (UnitAddTorus.mFourier l x).re = 0 := by
  have hpoint : ∀ x : Torus,
      (UnitAddTorus.mFourier k x).im * (UnitAddTorus.mFourier l x).re =
        (1 / 2 : ℝ) * ((UnitAddTorus.mFourier (k + l) x).im +
          (UnitAddTorus.mFourier (k - l) x).im) := by
    intro x
    rw [Modes.mFourier_add_at, Modes.mFourier_sub_at]
    have h := Modes.two_im_mul_re (UnitAddTorus.mFourier k x) (UnitAddTorus.mFourier l x)
    nlinarith
  calc
    _ = ∫ x : Torus, (1 / 2 : ℝ) *
          ((UnitAddTorus.mFourier (k + l) x).im +
            (UnitAddTorus.mFourier (k - l) x).im) := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    _ = (1 / 2 : ℝ) *
          ((∫ x : Torus, (UnitAddTorus.mFourier (k + l) x).im) +
            (∫ x : Torus, (UnitAddTorus.mFourier (k - l) x).im)) := by
      rw [integral_const_mul, integral_add (Modes.integrable_im_mFourier _)
          (Modes.integrable_im_mFourier _)]
    _ = 0 := by rw [Modes.integral_im_mFourier, Modes.integral_im_mFourier]; ring

/-- The ordered integer frequency of a positive representative. -/
def representativeFrequency {N : ℕ}
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) : Fin 2 → ℤ :=
  pairFrequency p.1

theorem representativeFrequency_mem_box {N : ℕ}
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    frequencyPair (representativeFrequency p) ∈ symmetricFrequencyBox N := by
  have hp := (mem_positiveFrequencyRepresentatives p.2).1
  have hpair : frequencyPair (pairFrequency p.1) = p.1 := by
    rcases p.1 with ⟨a, b⟩
    simp [frequencyPair, pairFrequency]
  simpa [representativeFrequency, hpair] using hp

theorem representativeFrequency_injective {N : ℕ}
    {p q : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}}
    (h : representativeFrequency p = representativeFrequency q) : p = q := by
  apply Subtype.ext
  exact Modes.pairFrequency_injective h

theorem representativeFrequency_ne_neg {N : ℕ}
    (p q : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    representativeFrequency p ≠ -representativeFrequency q := by
  intro h
  have hpq : p.1 = -q.1 := by
    apply Modes.pairFrequency_injective
    simpa [representativeFrequency, pairFrequency_neg] using h
  have hneg : -q.1 ∈ positiveFrequencyRepresentatives N := by rw [← hpq]; exact p.2
  exact positiveFrequencyRepresentatives_neg_not q.2 hneg

/-- The finite real Fourier index: one constant mode and a cosine/sine pair for each representative.
`Bool.false` selects cosine and `Bool.true` selects sine. -/
abbrev RealFourierIndex (N : ℕ) :=
  Option ({p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N} × Bool)

noncomputable instance realFourierIndexFintype (N : ℕ) : Fintype (RealFourierIndex N) :=
  by
    dsimp [RealFourierIndex]
    infer_instance

/-- Real trigonometric modes on the unit torus, normalized so nonconstant modes have norm one. -/
def realFourierMode (N : ℕ) (a : RealFourierIndex N) (x : Torus) : ℝ :=
  match a with
  | none => 1
  | some (p, isSine) =>
    let z := UnitAddTorus.mFourier (representativeFrequency p) x
    if isSine then Real.sqrt 2 * z.im else Real.sqrt 2 * z.re

/-- Complexification of a cosine mode as the two characters at opposite frequencies. -/
theorem realFourierMode_cos_complexExpansion (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) (x : Torus) :
    (realFourierMode N (some (p, false)) x : ℂ) =
      (Real.sqrt 2 / 2 : ℝ) *
        (UnitAddTorus.mFourier (representativeFrequency p) x +
          UnitAddTorus.mFourier (-representativeFrequency p) x) := by
  have h := Modes.ofReal_sqrtTwo_mul_re
    (UnitAddTorus.mFourier (representativeFrequency p) x)
  simpa only [realFourierMode, Bool.false_eq_true, ↓reduceIte, Modes.mFourier_star_at] using h

/-- Complexification of a sine mode as the two characters at opposite frequencies. -/
theorem realFourierMode_sin_complexExpansion (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) (x : Torus) :
    (realFourierMode N (some (p, true)) x : ℂ) =
      (Real.sqrt 2 / 2 : ℝ) * (-Complex.I) *
        (UnitAddTorus.mFourier (representativeFrequency p) x -
          UnitAddTorus.mFourier (-representativeFrequency p) x) := by
  have h := Modes.ofReal_sqrtTwo_mul_im
    (UnitAddTorus.mFourier (representativeFrequency p) x)
  simpa only [realFourierMode, ↓reduceIte, Modes.mFourier_star_at] using h

/-- Each real trigonometric mode is continuous on the quotient torus. -/
theorem realFourierMode_continuous (N : ℕ) (a : RealFourierIndex N) :
    Continuous (realFourierMode N a) := by
  cases a with
  | none => exact continuous_const
  | some q =>
    rcases q with ⟨p, isSine⟩
    have hz : Continuous (UnitAddTorus.mFourier (representativeFrequency p)) :=
      (UnitAddTorus.mFourier (representativeFrequency p)).continuous
    cases isSine
    · change Continuous (fun x => Real.sqrt 2 *
        (UnitAddTorus.mFourier (representativeFrequency p) x).re)
      exact continuous_const.mul (Complex.continuous_re.comp hz)
    · change Continuous (fun x => Real.sqrt 2 *
        (UnitAddTorus.mFourier (representativeFrequency p) x).im)
      exact continuous_const.mul (Complex.continuous_im.comp hz)

/-- The corresponding smooth periodic function on Euclidean representatives. -/
def realFourierModeAmbient (N : ℕ) (a : RealFourierIndex N) (x : Homogenization.Vec 2) : ℝ :=
  match a with
  | none => 1
  | some (p, isSine) =>
    let z := AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p) x
    if isSine then Real.sqrt 2 * z.im else Real.sqrt 2 * z.re

theorem representativeFrequency_ne_zero {N : ℕ}
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    representativeFrequency p ≠ 0 := by
  intro hz
  have hzero : pairFrequency (0, 0) = 0 := by
    funext i
    fin_cases i <;> simp [pairFrequency]
  have hp : pairFrequency p.1 = pairFrequency (0, 0) := by
    calc
      pairFrequency p.1 = 0 := hz
      _ = pairFrequency (0, 0) := hzero.symm
  have hp0 : p.1 = (0, 0) := Modes.pairFrequency_injective hp
  exact positiveFrequencyPair_ne_zero
    (mem_positiveFrequencyRepresentatives p.2).2 hp0

theorem Modes.representativeFrequency_eq_iff {N : ℕ}
    (p q : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N}) :
    representativeFrequency p = representativeFrequency q ↔ p = q := by
  constructor
  · exact representativeFrequency_injective
  · rintro rfl
    rfl

/-- The real modes on a symmetric frequency box form an orthonormal family. -/
theorem realFourierMode_orthonormal (N : ℕ) (a b : RealFourierIndex N) :
    ∫ x : Torus, realFourierMode N a x * realFourierMode N b x =
      if a = b then 1 else 0 := by
  classical
  cases a with
  | none =>
    cases b with
    | none => simp [realFourierMode]
    | some q =>
      rcases q with ⟨p, isSine⟩
      have hfreq := representativeFrequency_ne_zero p
      cases isSine <;>
        simp [realFourierMode, integral_const_mul, Modes.integral_re_mFourier,
          Modes.integral_im_mFourier, hfreq]
  | some p =>
    rcases p with ⟨p, isSine⟩
    cases b with
    | none =>
      have hfreq := representativeFrequency_ne_zero p
      cases isSine <;>
        simp [realFourierMode, integral_const_mul,
          Modes.integral_re_mFourier, Modes.integral_im_mFourier, hfreq]
    | some q =>
      rcases q with ⟨q, isSine'⟩
      let k := representativeFrequency p
      let l := representativeFrequency q
      have hsq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hneg : k ≠ -l := by
        exact representativeFrequency_ne_neg p q
      have heq : (k = l) ↔ p = q := Modes.representativeFrequency_eq_iff p q
      cases isSine <;> cases isSine'
      · have hpoint : ∀ x : Torus,
            realFourierMode N (some (p, false)) x *
                realFourierMode N (some (q, false)) x =
              2 * ((UnitAddTorus.mFourier k x).re * (UnitAddTorus.mFourier l x).re) := by
          intro x
          simp only [realFourierMode, Bool.false_eq_true, ↓reduceIte]
          calc
            (Real.sqrt 2 * (UnitAddTorus.mFourier k x).re) *
                (Real.sqrt 2 * (UnitAddTorus.mFourier l x).re) =
              (Real.sqrt 2 * Real.sqrt 2) *
                ((UnitAddTorus.mFourier k x).re * (UnitAddTorus.mFourier l x).re) := by ring
            _ = _ := by rw [hsq]
        calc
          _ = 2 * (∫ x : Torus,
              (UnitAddTorus.mFourier k x).re * (UnitAddTorus.mFourier l x).re) := by
            rw [show (fun x => realFourierMode N (some (p, false)) x *
                realFourierMode N (some (q, false)) x) =
              fun x => 2 * ((UnitAddTorus.mFourier k x).re *
                (UnitAddTorus.mFourier l x).re) from funext hpoint]
            rw [integral_const_mul]
          _ = if some (p, false) = some (q, false) then 1 else 0 := by
            rw [Modes.integral_re_mul_re]
            simp only [hneg, ite_false, zero_add]
            simp only [heq, Option.some.injEq, Prod.mk.injEq]
            by_cases hpq : p = q <;> simp [hpq]
      · have hpoint : ∀ x : Torus,
            realFourierMode N (some (p, false)) x *
                realFourierMode N (some (q, true)) x =
              2 * ((UnitAddTorus.mFourier k x).re * (UnitAddTorus.mFourier l x).im) := by
          intro x
          simp only [realFourierMode, Bool.false_eq_true, ↓reduceIte]
          calc
            (Real.sqrt 2 * (UnitAddTorus.mFourier k x).re) *
                (Real.sqrt 2 * (UnitAddTorus.mFourier l x).im) =
              (Real.sqrt 2 * Real.sqrt 2) *
                ((UnitAddTorus.mFourier k x).re * (UnitAddTorus.mFourier l x).im) := by ring
            _ = _ := by rw [hsq]
        rw [show (fun x => realFourierMode N (some (p, false)) x *
            realFourierMode N (some (q, true)) x) =
          fun x => 2 * ((UnitAddTorus.mFourier k x).re *
            (UnitAddTorus.mFourier l x).im) from funext hpoint]
        rw [integral_const_mul, Modes.integral_re_mul_im]
        simp
      · have hpoint : ∀ x : Torus,
            realFourierMode N (some (p, true)) x *
                realFourierMode N (some (q, false)) x =
              2 * ((UnitAddTorus.mFourier k x).im * (UnitAddTorus.mFourier l x).re) := by
          intro x
          simp only [realFourierMode, Bool.false_eq_true, ↓reduceIte]
          calc
            (Real.sqrt 2 * (UnitAddTorus.mFourier k x).im) *
                (Real.sqrt 2 * (UnitAddTorus.mFourier l x).re) =
              (Real.sqrt 2 * Real.sqrt 2) *
                ((UnitAddTorus.mFourier k x).im * (UnitAddTorus.mFourier l x).re) := by ring
            _ = _ := by rw [hsq]
        rw [show (fun x => realFourierMode N (some (p, true)) x *
            realFourierMode N (some (q, false)) x) =
          fun x => 2 * ((UnitAddTorus.mFourier k x).im *
            (UnitAddTorus.mFourier l x).re) from funext hpoint]
        rw [integral_const_mul, Modes.integral_im_mul_re]
        simp
      · have hpoint : ∀ x : Torus,
            realFourierMode N (some (p, true)) x *
                realFourierMode N (some (q, true)) x =
              2 * ((UnitAddTorus.mFourier k x).im * (UnitAddTorus.mFourier l x).im) := by
          intro x
          simp only [realFourierMode, ↓reduceIte]
          calc
            (Real.sqrt 2 * (UnitAddTorus.mFourier k x).im) *
                (Real.sqrt 2 * (UnitAddTorus.mFourier l x).im) =
              (Real.sqrt 2 * Real.sqrt 2) *
                ((UnitAddTorus.mFourier k x).im * (UnitAddTorus.mFourier l x).im) := by ring
            _ = _ := by rw [hsq]
        calc
          _ = 2 * (∫ x : Torus,
              (UnitAddTorus.mFourier k x).im * (UnitAddTorus.mFourier l x).im) := by
            rw [show (fun x => realFourierMode N (some (p, true)) x *
                realFourierMode N (some (q, true)) x) =
              fun x => 2 * ((UnitAddTorus.mFourier k x).im *
                (UnitAddTorus.mFourier l x).im) from funext hpoint]
            rw [integral_const_mul]
          _ = if some (p, true) = some (q, true) then 1 else 0 := by
            rw [Modes.integral_im_mul_im]
            simp only [hneg, ite_false, sub_zero]
            simp only [heq, Option.some.injEq, Prod.mk.injEq]
            by_cases hpq : p = q <;> simp [hpq]

/-- The ambient representative transfers back to the mode on the quotient torus. -/
theorem realFourierMode_eq_periodicToTorus (N : ℕ) (a : RealFourierIndex N) :
    realFourierMode N a =
      AVenhance.Infra.Torus.periodicToTorus (realFourierModeAmbient N a) := by
  funext x
  cases a with
  | none => rfl
  | some q =>
    rcases q with ⟨p, isSine⟩
    simp only [realFourierMode, realFourierModeAmbient,
      AVenhance.Infra.Torus.periodicToTorus,
      AVenhance.Infra.Torus.torusCharacter]
    rw [neg_neg]
    rw [AVenhance.Infra.Torus.toUnitTorus_unitTorusRepresentative]

/-- The Euclidean real modes are smooth, including every derivative order. -/
theorem realFourierModeAmbient_contDiff (N : ℕ) (a : RealFourierIndex N) :
    ContDiff ℝ ⊤ (realFourierModeAmbient N a) := by
  cases a with
  | none => exact contDiff_const
  | some q =>
    rcases q with ⟨p, isSine⟩
    let χ := AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p)
    have hχ : ContDiff ℝ ⊤ χ :=
      AVenhance.Infra.Torus.torusCharacter_contDiff (-representativeFrequency p)
    have hre : ContDiff ℝ ⊤ (fun x => (χ x).re) := by
      convert Complex.reCLM.contDiff.comp hχ using 1
      funext x
      exact Complex.reCLM_apply (χ x)
    have him : ContDiff ℝ ⊤ (fun x => (χ x).im) := by
      convert Complex.imCLM.contDiff.comp hχ using 1
      funext x
      exact Complex.imCLM_apply (χ x)
    cases isSine
    · change ContDiff ℝ ⊤ (fun x => Real.sqrt 2 * (χ x).re)
      exact contDiff_const.mul hre
    · change ContDiff ℝ ⊤ (fun x => Real.sqrt 2 * (χ x).im)
      exact contDiff_const.mul him

/-- The Euclidean real modes are periodic in the lattice convention. -/
theorem realFourierModeAmbient_periodic (N : ℕ) (a : RealFourierIndex N) :
    AVenhance.IsZ2Periodic (realFourierModeAmbient N a) := by
  cases a with
  | none => intro k x; rfl
  | some q =>
    rcases q with ⟨p, isSine⟩
    intro k x
    have hχ := AVenhance.Infra.Torus.torusCharacter_periodic
      (-representativeFrequency p) k x
    have hshift : AVenhance.latticeShift k = AVenhance.Infra.Torus.intVector k := rfl
    cases isSine
    · change Real.sqrt 2 *
        (AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p)
          (x + AVenhance.latticeShift k)).re =
        Real.sqrt 2 *
          (AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p) x).re
      rw [hshift, hχ]
    · change Real.sqrt 2 *
        (AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p)
          (x + AVenhance.latticeShift k)).im =
        Real.sqrt 2 *
          (AVenhance.Infra.Torus.torusCharacter (-representativeFrequency p) x).im
      rw [hshift, hχ]

theorem Modes.spaceGrad_periodic_of_smooth {f : Homogenization.Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (AVenhance.spaceGrad f) := by
  intro k x
  let v : Homogenization.Vec 2 := AVenhance.latticeShift k
  have hfun : (fun y : Homogenization.Vec 2 => f (y + v)) = f := by
    funext y
    exact hper k y
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have htranslate : HasFDerivAt (fun y : Homogenization.Vec 2 => y + v)
      (ContinuousLinearMap.id ℝ (Homogenization.Vec 2)) x := by
    have hid : HasFDerivAt (fun y : Homogenization.Vec 2 => y)
        (ContinuousLinearMap.id ℝ (Homogenization.Vec 2)) x := hasFDerivAt_id x
    simpa only [id_eq] using hid.add_const v
  have hcomp := (hdiff (x + v)).hasFDerivAt.comp x htranslate
  have hshift : HasFDerivAt f (fderiv ℝ f (x + v)) x := by
    have hshift' := hcomp
    change HasFDerivAt (fun y : Homogenization.Vec 2 => f (y + v))
      (fderiv ℝ f (x + v) ∘L ContinuousLinearMap.id ℝ (Homogenization.Vec 2)) x at hshift'
    rw [ContinuousLinearMap.comp_id, hfun] at hshift'
    exact hshift'
  have hbase : HasFDerivAt f (fderiv ℝ f x) x := (hdiff x).hasFDerivAt
  have hderiv : fderiv ℝ f (x + v) = fderiv ℝ f x := hshift.unique hbase
  funext i
  change fderiv ℝ f (x + AVenhance.latticeShift k) (Homogenization.basisVec i) =
    fderiv ℝ f x (Homogenization.basisVec i)
  exact congrArg (fun L : Homogenization.Vec 2 →L[ℝ] ℝ => L (Homogenization.basisVec i)) hderiv

/-- The Euclidean gradient field attached to a real Fourier mode. -/
def realFourierModeAmbientGrad (N : ℕ) (a : RealFourierIndex N)
    (x : Homogenization.Vec 2) : Homogenization.Vec 2 :=
  AVenhance.spaceGrad (realFourierModeAmbient N a) x

theorem realFourierModeAmbientGrad_continuous (N : ℕ) (a : RealFourierIndex N) :
    Continuous (realFourierModeAmbientGrad N a) := by
  have hcont : ContDiff ℝ ⊤ (realFourierModeAmbient N a) :=
    realFourierModeAmbient_contDiff N a
  have hfderiv := hcont.continuous_fderiv (by simp)
  have hcoord (i : Fin 2) : Continuous (fun x =>
      AVenhance.spaceGrad (realFourierModeAmbient N a) x i) :=
    hfderiv.clm_apply continuous_const
  exact continuous_pi fun i => hcoord i

theorem realFourierModeAmbientGrad_periodic (N : ℕ) (a : RealFourierIndex N) :
    AVenhance.IsZ2Periodic (realFourierModeAmbientGrad N a) := by
  exact Modes.spaceGrad_periodic_of_smooth
    ((realFourierModeAmbient_contDiff N a).of_le (by simp))
    (realFourierModeAmbient_periodic N a)

/-- The periodic gradient mode on the quotient torus. -/
def realFourierModeGrad (N : ℕ) (a : RealFourierIndex N) (x : Torus) :
    Homogenization.Vec 2 :=
  AVenhance.Infra.Torus.periodicToTorus (realFourierModeAmbientGrad N a) x

/-- Complex Fourier coefficients of a real cosine mode are supported on its two opposite
characters. -/
theorem realFourierMode_cos_fourierCoeff (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N})
    (l : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun y => (realFourierMode N (some (p, false)) y : ℂ)) l =
      (Real.sqrt 2 / 2 : ℝ) * (if l = representativeFrequency p then 1 else 0) +
        (Real.sqrt 2 / 2 : ℝ) * (if l = -representativeFrequency p then 1 else 0) := by
  let d : ℂ := (Real.sqrt 2 / 2 : ℝ)
  let k := representativeFrequency p
  have hfun : (fun y => (realFourierMode N (some (p, false)) y : ℂ)) =
      fun y => d * UnitAddTorus.mFourier k y + d * UnitAddTorus.mFourier (-k) y := by
    funext y
    calc
      _ = d * (UnitAddTorus.mFourier (representativeFrequency p) y +
          UnitAddTorus.mFourier (-representativeFrequency p) y) := by
        simpa [d] using realFourierMode_cos_complexExpansion N p y
      _ = d * UnitAddTorus.mFourier k y + d * UnitAddTorus.mFourier (-k) y := by
        simp [k, mul_add]
  have hlin := Modes.mFourierCoeff_add_of_continuous
    (f := fun y => d * UnitAddTorus.mFourier k y)
    (g := fun y => d * UnitAddTorus.mFourier (-k) y)
    (continuous_const.mul (UnitAddTorus.mFourier k).continuous)
    (continuous_const.mul (UnitAddTorus.mFourier (-k)).continuous) l
  calc
    _ = UnitAddTorus.mFourierCoeff
        (fun y => d * UnitAddTorus.mFourier k y +
          d * UnitAddTorus.mFourier (-k) y) l := by rw [hfun]
    _ = UnitAddTorus.mFourierCoeff (fun y => d * UnitAddTorus.mFourier k y) l +
        UnitAddTorus.mFourierCoeff (fun y => d * UnitAddTorus.mFourier (-k) y) l := hlin
    _ = d * (if l = k then 1 else 0) + d * (if l = -k then 1 else 0) := by
      rw [Modes.mFourierCoeff_const_mul, Modes.mFourierCoeff_mFourier l k,
        Modes.mFourierCoeff_const_mul, Modes.mFourierCoeff_mFourier l (-k)]
    _ = _ := by simp [d, k]

/-- Complex Fourier coefficients of a real sine mode are supported on its two opposite
characters, with the imaginary signs fixed by the Fourier convention. -/
theorem realFourierMode_sin_fourierCoeff (N : ℕ)
    (p : {p : ℤ × ℤ // p ∈ positiveFrequencyRepresentatives N})
    (l : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun y => (realFourierMode N (some (p, true)) y : ℂ)) l =
      ((Real.sqrt 2 / 2 : ℝ) * (-Complex.I)) *
          (if l = representativeFrequency p then 1 else 0) -
        ((Real.sqrt 2 / 2 : ℝ) * (-Complex.I)) *
          (if l = -representativeFrequency p then 1 else 0) := by
  let d : ℂ := (Real.sqrt 2 / 2 : ℝ) * (-Complex.I)
  let k := representativeFrequency p
  have hfun : (fun y => (realFourierMode N (some (p, true)) y : ℂ)) =
      fun y => d * UnitAddTorus.mFourier k y + (-d) * UnitAddTorus.mFourier (-k) y := by
    funext y
    calc
      _ = d * (UnitAddTorus.mFourier (representativeFrequency p) y -
          UnitAddTorus.mFourier (-representativeFrequency p) y) := by
        simpa [d] using realFourierMode_sin_complexExpansion N p y
      _ = d * UnitAddTorus.mFourier k y + (-d) * UnitAddTorus.mFourier (-k) y := by
        simp [k]
        ring
  have hlin := Modes.mFourierCoeff_add_of_continuous
    (f := fun y => d * UnitAddTorus.mFourier k y)
    (g := fun y => (-d) * UnitAddTorus.mFourier (-k) y)
    (continuous_const.mul (UnitAddTorus.mFourier k).continuous)
    (continuous_const.mul (UnitAddTorus.mFourier (-k)).continuous) l
  calc
    _ = UnitAddTorus.mFourierCoeff
        (fun y => d * UnitAddTorus.mFourier k y +
          (-d) * UnitAddTorus.mFourier (-k) y) l := by rw [hfun]
    _ = UnitAddTorus.mFourierCoeff (fun y => d * UnitAddTorus.mFourier k y) l +
        UnitAddTorus.mFourierCoeff (fun y => (-d) * UnitAddTorus.mFourier (-k) y) l := hlin
    _ = d * (if l = k then 1 else 0) + (-d) * (if l = -k then 1 else 0) := by
      rw [Modes.mFourierCoeff_const_mul, Modes.mFourierCoeff_mFourier l k,
        Modes.mFourierCoeff_const_mul, Modes.mFourierCoeff_mFourier l (-k)]
    _ = _ := by
      simp only [d, k]
      split_ifs <;> push_cast <;> ring

/-- The constant real mode has only its zero Fourier coefficient. -/
theorem realFourierMode_const_fourierCoeff (N : ℕ) (l : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (fun y => (realFourierMode N none y : ℂ)) l =
      if l = 0 then 1 else 0 := by
  have hconst : (fun y : Torus => (realFourierMode N none y : ℂ)) =
      UnitAddTorus.mFourier (0 : Fin 2 → ℤ) := by
    funext y
    have h0 := congrArg (fun f : C(Torus, ℂ) => f y) UnitAddTorus.mFourier_zero
    simpa [realFourierMode] using h0.symm
  rw [hconst]
  exact Modes.mFourierCoeff_mFourier l 0

end AVenhance.Infra.Parabolic.FourierGalerkin

end
