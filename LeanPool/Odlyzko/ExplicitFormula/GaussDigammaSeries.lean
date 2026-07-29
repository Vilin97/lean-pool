/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GaussDigammaFunction

/-!
# Gauss Digamma Series

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A gauss digamma partial integrand used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaPartialIntegrand (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n,
    (Complex.exp (-(k + 1 : ℂ) * x) -
      Complex.exp (-(s + k) * x))

/-- A gauss digamma partial sum used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaPartialSum (s : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℂ)⁻¹ - (s + k)⁻¹)

theorem gaussDigammaPartialIntegrand_eq
    (s : ℂ) (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    gaussDigammaPartialIntegrand s n x =
      (1 - Complex.exp (-n * x)) * gaussDigammaIntegrand s x := by
  induction n with
  | zero =>
      simp [gaussDigammaPartialIntegrand]
  | succ n ih =>
      rw [gaussDigammaPartialIntegrand, Finset.sum_range_succ]
      change
        gaussDigammaPartialIntegrand s n x +
            (Complex.exp (-(n + 1 : ℂ) * x) -
              Complex.exp (-(s + n) * x)) =
          (1 - Complex.exp (-(n + 1 : ℕ) * x)) *
            gaussDigammaIntegrand s x
      rw [ih]
      have hden : 1 - Complex.exp (-x) ≠ 0 := by
        intro h
        have hexp : Complex.exp (-(x : ℂ)) = 1 :=
          sub_eq_zero.mp h |>.symm
        have hnorm := congrArg norm hexp
        have hre : Real.exp (-x) = Real.exp 0 := by
          simpa [Complex.norm_exp] using hnorm
        simp_all
      have hpow_n :
          Complex.exp (-(n : ℂ) * x) =
            Complex.exp (-x) ^ n := by
        rw [← Complex.exp_nat_mul]
        simp
      have hpow_s :
          Complex.exp (-(s + n) * x) =
            Complex.exp (-s * x) * Complex.exp (-x) ^ n := by
        rw [← hpow_n, ← Complex.exp_add]
        grind
      have hterm_succ :
          Complex.exp (-(n + 1 : ℂ) * x) =
            Complex.exp (-x) * Complex.exp (-x) ^ n := by
        rw [← hpow_n, ← Complex.exp_add]
        grind
      have hfactor_succ :
          Complex.exp (-(n + 1 : ℕ) * x) =
            Complex.exp (-x) * Complex.exp (-x) ^ n := by simp_all
      rw [gaussDigammaIntegrand, hpow_n, hpow_s, hterm_succ,
        hfactor_succ]
      grind

theorem integral_gaussDigammaPartialIntegrand
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, gaussDigammaPartialIntegrand s n x) =
      gaussDigammaPartialSum s n := by
  unfold gaussDigammaPartialIntegrand gaussDigammaPartialSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have hfirst :
        IntegrableOn
          (fun x : ℝ ↦ Complex.exp (-(k + 1 : ℂ) * x)) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (a := -(k + 1 : ℂ))
        (by
          simp only [neg_re, add_re, natCast_re, one_re]
          grind) 0
    have hsecond :
        IntegrableOn
          (fun x : ℝ ↦ Complex.exp (-(s + k) * x)) (Ioi 0) :=
      integrableOn_exp_mul_complex_Ioi (a := -(s + k))
        (by
          simp only [neg_re, add_re, natCast_re]
          grind) 0
    rw [integral_sub]
    · rw [integral_cexp_neg_mul_Ioi, integral_cexp_neg_mul_Ioi]
      · simp only [Nat.cast_add, Nat.cast_one, one_div]
      · simp only [add_re, natCast_re]
        grind
      · simp only [add_re, natCast_re, one_re]
        grind
    · exact hfirst
    · exact hsecond
  · intro k hk
    exact
      (integrableOn_exp_mul_complex_Ioi (a := -(k + 1 : ℂ))
        (by
          simp only [neg_re, add_re, natCast_re, one_re]
          grind) 0).sub
      (integrableOn_exp_mul_complex_Ioi (a := -(s + k))
        (by
          simp only [neg_re, add_re, natCast_re]
          grind) 0)

theorem tendsto_integral_gaussDigammaPartialIntegrand
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ ↦
        ∫ x : ℝ in Ioi 0, gaussDigammaPartialIntegrand s n x)
      atTop
      (𝓝 (∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x)) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let bound : ℝ → ℝ := fun x ↦ 2 * ‖gaussDigammaIntegrand s x‖
  have hint :
      Integrable (gaussDigammaIntegrand s) μ :=
    gaussDigammaIntegrand_integrableOn_Ioi hs
  apply tendsto_integral_of_dominated_convergence bound
  · intro n
    have hfactorMeas :
        AEStronglyMeasurable
          (fun x : ℝ ↦
            (1 - Complex.exp (-n * x)) *
              gaussDigammaIntegrand s x) μ :=
      (by fun_prop : Continuous
          (fun x : ℝ ↦ (1 - Complex.exp (-n * x)))).aestronglyMeasurable.mul
        hint.aestronglyMeasurable
    apply hfactorMeas.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (gaussDigammaPartialIntegrand_eq s n hx.ne').symm
  · simpa [bound] using hint.norm.const_mul 2
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [gaussDigammaPartialIntegrand_eq s n hx.ne', norm_mul]
    have hexpNorm :
        ‖Complex.exp (-n * x)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      simp_all
    have hfactorNorm :
        ‖1 - Complex.exp (-n * x)‖ ≤ 2 := by
      calc
        ‖1 - Complex.exp (-n * x)‖ ≤
            ‖(1 : ℂ)‖ + ‖Complex.exp (-n * x)‖ :=
          norm_sub_le _ _
        _ ≤ 1 + 1 := by
          simpa using add_le_add_right hexpNorm 1
        _ = 2 := by norm_num
    calc
      ‖1 - Complex.exp (-n * x)‖ *
            ‖gaussDigammaIntegrand s x‖ ≤
          2 * ‖gaussDigammaIntegrand s x‖ := by
        exact mul_le_mul_of_nonneg_right hfactorNorm (norm_nonneg _)
      _ = bound x := by simp [bound]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hq :
        ‖Complex.exp (-x)‖ < 1 := by
      rw [Complex.norm_exp]
      simp_all
    have hp :
        Tendsto (fun n : ℕ ↦ Complex.exp (-x) ^ n)
          atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
    have hfactor :
        Tendsto
          (fun n : ℕ ↦
            (1 - Complex.exp (-x) ^ n) *
              gaussDigammaIntegrand s x)
          atTop
          (𝓝 (gaussDigammaIntegrand s x)) := by
      have hone :
          Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (𝓝 1) :=
        tendsto_const_nhds
      simpa using (hone.sub hp).mul_const (gaussDigammaIntegrand s x)
    apply hfactor.congr'
    filter_upwards [] with n
    rw [gaussDigammaPartialIntegrand_eq s n hx.ne']
    rw [← Complex.exp_nat_mul]
    simp

theorem tendsto_gaussDigammaPartialSum
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (gaussDigammaPartialSum s) atTop
      (𝓝 (∫ x : ℝ in Ioi 0, gaussDigammaIntegrand s x)) := by
  apply
    (tendsto_integral_gaussDigammaPartialIntegrand hs).congr'
  filter_upwards [] with n
  exact integral_gaussDigammaPartialIntegrand hs n

end NumberField.Odlyzko
