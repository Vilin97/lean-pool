/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeightedSobolev

@[expose] public section

/-!
# The compact test function in the pressure flux

The identity `φ² r = D(φ⁸)[w]` places the localized pressure flux in the
commutator form.  Its estimates use only the unweighted velocity energy and
the weighted velocity and gradient norms.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.PressureFluxTest

open ProblemStatement Comparison

/-- The scalar test function for the pressure commutator. -/
noncomputable def r (φ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  8 * φ x ^ 5 * (fderiv ℝ φ x (w x))

theorem multiplier_r_eq_weight_deriv {φ : Space → ℝ} (w : Space → Space)
    {x : Space} (hφ : DifferentiableAt ℝ φ x) :
    φ x ^ 2 * r φ w x = fderiv ℝ (fun y => φ y ^ 8) x (w x) := by
  have hd : fderiv ℝ (fun y => φ y ^ 8) x = (8 * φ x ^ 7) • fderiv ℝ φ x := by
    simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
      ((hasDerivAt_pow 8 (φ x)).comp_hasFDerivAt x hφ.hasFDerivAt).fderiv
  rw [hd]
  simp only [r, _root_.smul_apply, smul_eq_mul]
  ring

theorem r_smooth {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (r φ w) :=
  (contDiff_const.mul (hφ.pow 5)).mul
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply hw)

theorem r_hasCompactSupport {φ : Space → ℝ} (hs : HasCompactSupport φ)
    (w : Space → Space) : HasCompactSupport (r φ w) := by
  apply hs.mono
  intro x hx
  change φ x ≠ 0
  intro hzero
  apply hx
  simp [r, hzero]

theorem memLp_r {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (p : ℝ≥0∞) : MemLp (r φ w) p volume :=
  (r_smooth hφ hw).continuous.memLp_of_hasCompactSupport (r_hasCompactSupport hs w)

theorem memLp_fderiv_r {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (p : ℝ≥0∞) : MemLp (fderiv ℝ (r φ w)) p volume :=
  ((r_smooth hφ hw).fderiv_right (m := ∞) (by simp)).continuous.memLp_of_hasCompactSupport
    ((r_hasCompactSupport hs w).fderiv ℝ)

theorem norm_r_le {φ : Space → ℝ} {w : Space → Space} {x : Space}
    (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ‖fderiv ℝ φ x‖ ≤ L) :
    ‖r φ w x‖ ≤ (8 * L) * ‖(φ x ^ 3) • w x‖ := by
  have hp2 : φ x ^ 2 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hp : φ x ^ 5 ≤ φ x ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hp2 (pow_nonneg hφ0 3)]
  have happly : ‖fderiv ℝ φ x (w x)‖ ≤ L * ‖w x‖ :=
    ((fderiv ℝ φ x).le_opNorm (w x)).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    ‖r φ w x‖ = 8 * φ x ^ 5 * ‖fderiv ℝ φ x (w x)‖ := by
      simp [r, norm_mul, Real.norm_eq_abs, abs_of_nonneg hφ0]
    _ ≤ 8 * φ x ^ 5 * (L * ‖w x‖) :=
      mul_le_mul_of_nonneg_left happly (by positivity)
    _ ≤ (8 * L) * (φ x ^ 3 * ‖w x‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg hL0 (norm_nonneg (w x)))]
    _ = (8 * L) * ‖(φ x ^ 3) • w x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hφ0 3)]

/-- The test belongs to `L⁴`, with the exact endpoint interpolation exponents. -/
theorem memLp_and_lpNorm_r_four_le {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L) :
    MemLp (r φ w) 4 volume ∧
      comparisonLpNorm 4 (r φ w) ≤ 8 * L * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  have hw6 := WeightedSobolev.memLp_cutoff_pow_smul hφ.continuous hs hw.continuous
    (by norm_num : (4 : ℕ) ≠ 0) 6
  obtain ⟨hw4, hbound⟩ := WeightedInterpolation.cutoff_interpolation_four
    hφ.continuous.aestronglyMeasurable hφ0 hw2 hw6
  refine ⟨memLp_r hφ hs hw 4, ?_⟩
  calc
    comparisonLpNorm 4 (r φ w) ≤ comparisonLpNorm 4 (fun x => (8 * L) • (φ x ^ 3 • w x)) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (hw4.const_smul (8 * L))
      intro x
      change ‖r φ w x‖ ≤ ‖(8 * L) • (φ x ^ 3 • w x)‖
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 8 * L)]
      exact norm_r_le (hφ0 x) (hφ1 x) hL0 (hL x)
    _ = (8 * L) * comparisonLpNorm 4 (fun x => φ x ^ 3 • w x) := by
      rw [LpNormTools.lpNorm_const_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 8 * L)]
    _ ≤ (8 * L) * (comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 8 * L * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (3 / 4 : ℝ) := by ring

private theorem norm_fderiv_product_le {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => f y * g y) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖ := by
  rw [fderiv_fun_mul hf hg]
  exact (norm_add_le _ _).trans (add_le_add
    (ContinuousLinearMap.opNorm_smul_le _ _) (ContinuousLinearMap.opNorm_smul_le _ _))

private theorem norm_fderiv_apply_le {φ : Space → ℝ} {w : Space → Space} {x : Space}
    (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (hw : DifferentiableAt ℝ w x) :
    ‖fderiv ℝ (fun y => fderiv ℝ φ y (w y)) x‖ ≤
      ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ + ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ := by
  have hflip : ‖(fderiv ℝ (fderiv ℝ φ) x).flip (w x)‖ ≤
      ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    change ‖fderiv ℝ (fderiv ℝ φ) x z (w x)‖ ≤ _
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ φ) x z‖ * ‖w x‖ :=
        (fderiv ℝ (fderiv ℝ φ) x z).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖z‖) * ‖w x‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ φ) x).le_opNorm z)
          (norm_nonneg _)
      _ = _ := by ring
  rw [fderiv_clm_apply hφ hw]
  exact (norm_add_le _ _).trans
    (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) hflip)

/-- Product differentiation before replacing the cutoff derivative norms by constants. -/
theorem norm_fderiv_r_le_raw {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (x : Space) (hφ0 : 0 ≤ φ x) :
    ‖fderiv ℝ (r φ w) x‖ ≤ 8 *
      (φ x ^ 5 * ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ +
        φ x ^ 5 * ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ +
        5 * φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2 * ‖w x‖) := by
  have hdφ : DifferentiableAt ℝ φ x := (contDiff_infty.1 hφ 1).differentiable (by simp) x
  have hdw : DifferentiableAt ℝ w x := (contDiff_infty.1 hw 1).differentiable (by simp) x
  have hdDφ : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  let q : Space → ℝ := fun y => fderiv ℝ φ y (w y)
  have hdq : DifferentiableAt ℝ q x := hdDφ.clm_apply hdw
  have hr : r φ w = fun y => 8 * (φ y ^ 5 * q y) := by
    funext y
    simp only [r, q]
    ring
  have hpow : ‖fderiv ℝ (fun y => φ y ^ 5) x‖ ≤
      5 * φ x ^ 4 * ‖fderiv ℝ φ x‖ := by
    have heq : fderiv ℝ (fun y => φ y ^ 5) x = (5 * φ x ^ 4) • fderiv ℝ φ x := by
      simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
        ((hasDerivAt_pow 5 (φ x)).comp_hasFDerivAt x hdφ.hasFDerivAt).fderiv
    rw [heq]
    calc
      _ ≤ ‖(5 : ℝ) * φ x ^ 4‖ * ‖fderiv ℝ φ x‖ :=
        ContinuousLinearMap.opNorm_smul_le (5 * φ x ^ 4) (fderiv ℝ φ x)
      _ = _ := by rw [Real.norm_of_nonneg (by positivity : 0 ≤ 5 * φ x ^ 4)]
  have hq : ‖q x‖ ≤ ‖fderiv ℝ φ x‖ * ‖w x‖ := (fderiv ℝ φ x).le_opNorm _
  have hDq : ‖fderiv ℝ q x‖ ≤ ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ +
      ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ := norm_fderiv_apply_le hdDφ hdw
  calc
    ‖fderiv ℝ (r φ w) x‖ ≤ 8 * ‖fderiv ℝ (fun y => φ y ^ 5 * q y) x‖ := by
      rw [hr, fderiv_const_mul (a := fun y => φ y ^ 5 * q y) ((hdφ.pow 5).mul hdq) 8]
      simpa using ContinuousLinearMap.opNorm_smul_le (8 : ℝ)
        (fderiv ℝ (fun y => φ y ^ 5 * q y) x)
    _ ≤ 8 * (φ x ^ 5 * ‖fderiv ℝ q x‖ +
        ‖q x‖ * ‖fderiv ℝ (fun y => φ y ^ 5) x‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hφ0 5)] using!
        norm_fderiv_product_le (hdφ.pow 5) hdq
    _ ≤ 8 * (φ x ^ 5 * (‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ +
        ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖) +
        (‖fderiv ℝ φ x‖ * ‖w x‖) * (5 * φ x ^ 4 * ‖fderiv ℝ φ x‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add (mul_le_mul_of_nonneg_left hDq (pow_nonneg hφ0 5))
      exact mul_le_mul hq hpow (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Only the weighted velocity derivative occurs in the pointwise bound. -/
theorem norm_fderiv_r_le_amplitude {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (x : Space)
    (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1) {L J : ℝ} (hL0 : 0 ≤ L)
    (hL : ‖fderiv ℝ φ x‖ ≤ L) (hJ : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ J) :
    ‖fderiv ℝ (r φ w) x‖ ≤
      (24 * L) * WeightedSobolev.cutoffGradientAmplitude φ w x +
        (40 * L ^ 2 + 8 * J) * ‖w x‖ := by
  have hp4 : φ x ^ 4 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hp5 : φ x ^ 5 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hp54 : φ x ^ 5 ≤ φ x ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hφ1 (pow_nonneg hφ0 4)]
  have hgrad := GradientOperator.norm_fderiv_le_three_mul_sqrt_gradientSq w x
  have h1 : φ x ^ 5 * ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ ≤
      3 * L * WeightedSobolev.cutoffGradientAmplitude φ w x := by
    calc
      _ ≤ (φ x ^ 4 * L) * (3 * Real.sqrt (gradientSq w x)) :=
        mul_le_mul (mul_le_mul hp54 hL (norm_nonneg _) (pow_nonneg hφ0 4)) hgrad
          (norm_nonneg _) (mul_nonneg (pow_nonneg hφ0 4) hL0)
      _ = _ := by unfold WeightedSobolev.cutoffGradientAmplitude; ring
  have h2 : φ x ^ 5 * ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ ≤ J * ‖w x‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [one_mul] using
      mul_le_mul hp5 hJ (norm_nonneg (fderiv ℝ (fderiv ℝ φ) x)) zero_le_one
  have hsquare : ‖fderiv ℝ φ x‖ ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hL 2
  have h3 : 5 * φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2 * ‖w x‖ ≤
      5 * L ^ 2 * ‖w x‖ := by
    have hh : φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2 ≤ L ^ 2 := by
      simpa only [one_mul] using mul_le_mul hp4 hsquare (sq_nonneg _) zero_le_one
    calc
      _ = 5 * (φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2) * ‖w x‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (by norm_num)) (norm_nonneg _)
  calc
    ‖fderiv ℝ (r φ w) x‖ ≤ _ := norm_fderiv_r_le_raw hφ hw x hφ0
    _ ≤ 8 * (3 * L * WeightedSobolev.cutoffGradientAmplitude φ w x +
        J * ‖w x‖ + 5 * L ^ 2 * ‖w x‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) (by norm_num)
    _ = _ := by ring

/-- The derivative is square integrable and controlled by weighted dissipation. -/
theorem memLp_and_lpNorm_fderiv_r_two_le {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L J : ℝ} (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J)
    (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L)
    (hJ : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ J) :
    MemLp (fderiv ℝ (r φ w)) 2 volume ∧
      comparisonLpNorm 2 (fderiv ℝ (r φ w)) ≤
        (24 * L) * Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) +
          (40 * L ^ 2 + 8 * J) * comparisonLpNorm 2 w := by
  let G := WeightedSobolev.cutoffGradientAmplitude φ w
  have hw1 := contDiff_infty.1 hw 1
  have hG : MemLp G 2 volume :=
    WeightedSobolev.memLp_cutoffGradientAmplitude hφ.continuous hs hw1 2
  have hG24 : MemLp (fun x => (24 * L) • G x) 2 volume := hG.const_smul (24 * L)
  have hw40 : MemLp (fun x => (40 * L ^ 2 + 8 * J) • ‖w x‖) 2 volume :=
    hw2.norm.const_smul (40 * L ^ 2 + 8 * J)
  have hc : 0 ≤ 40 * L ^ 2 + 8 * J := by positivity
  refine ⟨memLp_fderiv_r hφ hs hw 2, ?_⟩
  calc
    comparisonLpNorm 2 (fderiv ℝ (r φ w)) ≤
        comparisonLpNorm 2 (fun x => (24 * L) • G x + (40 * L ^ 2 + 8 * J) • ‖w x‖) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (hG24.add hw40)
      intro x
      have hp := norm_fderiv_r_le_amplitude hφ hw x (hφ0 x) (hφ1 x) hL0 (hL x) (hJ x)
      simpa only [Pi.add_apply, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ (24 * L) * G x + (40 * L ^ 2 + 8 * J) * ‖w x‖ by
          have := WeightedSobolev.cutoffGradientAmplitude_nonneg φ w x
          dsimp [G] at *
          positivity)] using hp
    _ ≤ comparisonLpNorm 2 (fun x => (24 * L) • G x) +
        comparisonLpNorm 2 (fun x => (40 * L ^ 2 + 8 * J) • ‖w x‖) :=
      LpNormTools.lpNorm_add_le (by norm_num) hG24 hw40
    _ = (24 * L) * Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) +
        (40 * L ^ 2 + 8 * J) * comparisonLpNorm 2 w := by
      rw [LpNormTools.lpNorm_const_smul, LpNormTools.lpNorm_const_smul]
      have hGeq := WeightedSobolev.lpNorm_cutoffGradientAmplitude hφ.continuous hs hw1
      change comparisonLpNorm 2 G = _ at hGeq
      rw [hGeq]
      simp [comparisonLpNorm, eLpNorm_norm, Real.norm_eq_abs, abs_of_nonneg hL0, abs_of_nonneg hc]

theorem lpNorm_fderiv_r_two_le {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L J : ℝ} (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J)
    (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L)
    (hJ : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ J) :
    comparisonLpNorm 2 (fderiv ℝ (r φ w)) ≤
      40 * (L * Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) +
        (L ^ 2 + J) * comparisonLpNorm 2 w) := by
  have h := (memLp_and_lpNorm_fderiv_r_two_le hφ hs hw hw2 hφ0 hφ1 hL0 hJ0 hL hJ).2
  have hA := Real.sqrt_nonneg (∫ x, φ x ^ 8 * gradientSq w x)
  have hM := LpNormTools.lpNorm_nonneg 2 w
  nlinarith [mul_nonneg hL0 hA, mul_nonneg hJ0 hM]

/-- The actual test at radius `R` in the fixed cutoff family. -/
def cutoffTest (R : ℝ) (w : Space → Space) : Space → ℝ :=
  r (ComparisonCutoffs.cutoff R) w

theorem cutoffTest_flux_identity (R : ℝ) (w : Space → Space) (x : Space) :
    ComparisonCutoffs.multiplier R x * cutoffTest R w x =
      fderiv ℝ (ComparisonCutoffs.weight R) x (w x) :=
  multiplier_r_eq_weight_deriv w
    ((contDiff_infty.1 (ComparisonCutoffs.cutoff_smooth R) 1).differentiable (by simp) x)

theorem cutoffTest_smooth (R : ℝ) {w : Space → Space} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (cutoffTest R w) := r_smooth (ComparisonCutoffs.cutoff_smooth R) hw

theorem cutoffTest_hasCompactSupport {R : ℝ} (hR : 0 < R) (w : Space → Space) :
    HasCompactSupport (cutoffTest R w) :=
  r_hasCompactSupport (ComparisonCutoffs.cutoff_hasCompactSupport hR) w

theorem memLp_cutoffTest {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (p : ℝ≥0∞) : MemLp (cutoffTest R w) p volume :=
  memLp_r (ComparisonCutoffs.cutoff_smooth R) (ComparisonCutoffs.cutoff_hasCompactSupport hR) hw p

theorem memLp_fderiv_cutoffTest {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (p : ℝ≥0∞) : MemLp (fderiv ℝ (cutoffTest R w)) p volume :=
  memLp_fderiv_r (ComparisonCutoffs.cutoff_smooth R)
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hw p

theorem cutoffTest_four_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) :
    MemLp (cutoffTest R w) 4 volume ∧
      comparisonLpNorm 4 (cutoffTest R w) ≤ (8 * ComparisonCutoffs.derivativeConstant 1 / R) *
        comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
          comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  have h := memLp_and_lpNorm_r_four_le (ComparisonCutoffs.cutoff_smooth R)
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hw hw2
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R)
    (div_nonneg (ComparisonCutoffs.derivativeConstant_pos 1).le hR.le)
    (ComparisonCutoffs.cutoff_fderiv_le hR)
  simpa only [cutoffTest, mul_div_assoc] using h

/-- A fixed constant for the derivative bound of the pressure test. -/
def cutoffDerivativeConstant : ℝ :=
  max (24 * ComparisonCutoffs.derivativeConstant 1)
    (40 * ComparisonCutoffs.derivativeConstant 1 ^ 2 + 8 * ComparisonCutoffs.derivativeConstant 2)

theorem cutoffDerivativeConstant_pos : 0 < cutoffDerivativeConstant :=
  lt_of_lt_of_le (mul_pos (by norm_num) (ComparisonCutoffs.derivativeConstant_pos 1))
    (le_max_left _ _)

theorem cutoffTest_derivative_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) :
    MemLp (fderiv ℝ (cutoffTest R w)) 2 volume ∧
      comparisonLpNorm 2 (fderiv ℝ (cutoffTest R w)) ≤
        (cutoffDerivativeConstant / R) *
          Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) +
        (cutoffDerivativeConstant / R ^ 2) * comparisonLpNorm 2 w := by
  have h := memLp_and_lpNorm_fderiv_r_two_le (ComparisonCutoffs.cutoff_smooth R)
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hw hw2
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R)
    (div_nonneg (ComparisonCutoffs.derivativeConstant_pos 1).le hR.le)
    (div_nonneg (ComparisonCutoffs.derivativeConstant_pos 2).le (sq_nonneg R))
    (ComparisonCutoffs.cutoff_fderiv_le hR) (ComparisonCutoffs.cutoff_second_fderiv_le hR)
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ = ((24 * ComparisonCutoffs.derivativeConstant 1) / R) *
          Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) +
        ((40 * ComparisonCutoffs.derivativeConstant 1 ^ 2 +
          8 * ComparisonCutoffs.derivativeConstant 2) / R ^ 2) * comparisonLpNorm 2 w := by
      field_simp [hR.ne']
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right hR).2 (le_max_left _ _)) (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2 (le_max_right _ _))
        (LpNormTools.lpNorm_nonneg 2 w))

end NavierStokesR3.PressureFluxTest
