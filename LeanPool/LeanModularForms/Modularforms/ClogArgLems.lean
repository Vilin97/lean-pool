/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.Cases

/-! # ClogArgLems -/


@[expose] public section

open UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


lemma arg_pow_aux (n : ℕ) (x : ℂ) (hx : x ≠ 0) (hna : |arg x| < π / n) :
  Complex.arg (x ^ n) = n * Complex.arg x := by
  induction n with
  | zero => simp only [pow_zero, arg_one, CharP.cast_eq_zero, zero_mul]
  | succ n hn2 =>
    by_cases hn0 : n = 0
    · simp only [hn0, zero_add, pow_one, Nat.cast_one, one_mul]
    · rw [pow_succ, arg_mul, hn2, Nat.cast_add]
      · ring
      · apply lt_trans hna
        gcongr
        exact (lt_add_one n)
      · apply pow_ne_zero n hx
      · exact hx
      simp only [mem_Ioc]
      rw [hn2]
      · rw [abs_lt] at hna
        constructor
        · have hnal := hna.1
          rw [← neg_div] at hnal
          rw [div_lt_iff₀' ] at hnal
          · rw [Nat.cast_add, add_mul] at hnal
            simpa only [gt_iff_lt, Nat.cast_one, one_mul] using hnal
          · norm_cast
            omega
        · have hnal := hna.2
          rw [lt_div_iff₀', Nat.cast_add] at hnal
          · rw [add_mul] at hnal
            simpa only [ge_iff_le, Nat.cast_one, one_mul] using hnal.le
          · norm_cast
            omega
      apply lt_trans hna
      gcongr
      exact (lt_add_one n)

lemma one_add_abs_half_ne_zero {x : ℂ} (hb : ‖x‖ < 1 / 2) : 1 + x ≠ 0 := by
  by_contra h
  rw [@add_eq_zero_iff_neg_eq] at h
  rw [← h] at hb
  simp at hb
  linarith

/-- The eventual argument power rule over any filter, for nonzero exponents. -/
lemma arg_pow_eventually {α : Type*} {F : Filter α} (n : ℕ) (hn0 : n ≠ 0) (f : α → ℂ)
    (hf : Tendsto f F (𝓝 0)) :
    ∀ᶠ m in F, Complex.arg ((1 + f m) ^ n) = n * Complex.arg (1 + f m) := by
  have hf1 := hf.const_add 1
  simp only [add_zero] at hf1
  have h2 := Complex.continuousAt_arg (x := 1) one_mem_slitPlane
  rw [ContinuousAt] at h2
  have h3 := h2.comp hf1
  simp only [arg_one] at h3
  have hpi : 0 < π / n := by positivity
  have hbound : ∀ᶠ m in F, |Complex.arg (1 + f m)| < π / n := by
    have := h3.eventually (Metric.ball_mem_nhds 0 hpi)
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, comp_apply] using this
  have hsmall : ∀ᶠ m in F, ‖f m‖ < 1 / 2 :=
    hf.eventually (Metric.ball_mem_nhds 0 one_half_pos) |>.mono fun m hm => by
      simpa only [Metric.mem_ball, dist_zero_right] using hm
  filter_upwards [hbound, hsmall] with b hb hs
  exact arg_pow_aux n (1 + f b) (one_add_abs_half_ne_zero hs) hb

lemma arg_pow (n : ℕ) (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) : ∀ᶠ m : ℕ in atTop,
    Complex.arg ((1 + f m) ^ n) = n * Complex.arg (1 + f m) := by
  rcases eq_or_ne n 0 with hn0 | hn0
  · filter_upwards with b
    simp [hn0]
  exact arg_pow_eventually n hn0 f hf

lemma arg_pow2 (n : ℕ) (f : ℍ → ℂ) (hf : Tendsto f atImInfty (𝓝 0)) : ∀ᶠ m : ℍ in atImInfty,
    Complex.arg ((1 + f m) ^ n) = n * Complex.arg (1 + f m) := by
  rcases eq_or_ne n 0 with hn0 | hn0
  · filter_upwards with b
    simp [hn0]
  exact arg_pow_eventually n hn0 f hf

/-- The complex-logarithm power rule from the corresponding argument identity. -/
lemma clog_pow_of_arg (n : ℕ) (w : ℂ) (harg : Complex.arg (w ^ n) = n * Complex.arg w) :
    Complex.log (w ^ n) = n * Complex.log w := by
  simp_rw [Complex.log]
  rw [harg]
  simp only [norm_pow, Real.log_pow, ofReal_mul, ofReal_natCast]
  ring

lemma clog_pow (n : ℕ) (f : ℕ → ℂ) (hf : Tendsto f atTop (𝓝 0)) : ∀ᶠ m : ℕ in atTop,
    Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m) := by
  filter_upwards [arg_pow n f hf] with b hb using clog_pow_of_arg n (1 + f b) hb

lemma clog_pow2 (n : ℕ) (f : ℍ → ℂ) (hf : Tendsto f atImInfty (𝓝 0)) : ∀ᶠ m : ℍ in atImInfty,
    Complex.log ((1 + f m) ^ n) = n * Complex.log (1 + f m) := by
  filter_upwards [arg_pow2 n f hf] with b hb using clog_pow_of_arg n (1 + f b) hb



lemma log_summable_pow (f : ℕ → ℂ) (hf : Summable f) (m : ℕ) :
    Summable (fun n => Complex.log ((1 + f n)^m)) := by
  have hfl := Complex.summable_log_one_add_of_summable hf
  have := (Summable.mul_left m (f := (fun n => Complex.log (1 + f n))) hfl).norm
  apply Summable.of_norm_bounded_eventually_nat this
  have hft := hf.tendsto_atTop_zero
  have H := clog_pow m f hft
  simp only [norm_mul, Complex.norm_natCast, eventually_atTop, ge_iff_le] at *
  obtain ⟨a, ha⟩ := H
  use a
  intro b hb
  apply le_of_eq
  rw [ha b hb]
  simp only [Complex.norm_mul, norm_natCast]
