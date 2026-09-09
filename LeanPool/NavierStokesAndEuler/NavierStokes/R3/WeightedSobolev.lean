/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LpNormTools
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.GradientOperator
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeightedInterpolation
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

@[expose] public section

/-!
# Weighted Sobolev estimates for compact cutoffs

The derivative estimate is local: the unweighted velocity only needs to be in
`L²`. No integrability assumption is made on its unweighted derivative.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal NNReal

namespace NavierStokesR3.WeightedSobolev

open ProblemStatement Comparison

/-- The fixed whole-space `H¹ → L⁶` Sobolev constant in dimension three. -/
def sobolevConstant : ℝ :=
  (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ)

theorem sobolevConstant_nonneg : 0 ≤ sobolevConstant := NNReal.coe_nonneg _

/-- Compactly supported continuous functions have finite norms at every
exponent, including infinity. -/
theorem memLp_of_compact {E : Type*} [NormedAddCommGroup E]
    {f : Space → E} (hf : Continuous f) (hs : HasCompactSupport f)
    (p : ℝ≥0∞) : MemLp f p (volume : Measure Space) :=
  hf.memLp_of_hasCompactSupport hs

/-- Mathlib's homogeneous Sobolev inequality specialized to Euclidean `R³`.
The finite derivative norm is supplied by compact support and `C¹` regularity. -/
theorem lpNorm_six_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : Space → E} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    comparisonLpNorm 6 f ≤ sobolevConstant * comparisonLpNorm 2 (fderiv ℝ f) := by
  have hn : Module.finrank ℝ Space = 3 := by simp [Space, NavierStokes.ProblemStatement.Space]
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure Space)
    hf hs (p := 2) (p' := 6) (by norm_num) (by omega) (by rw [hn]; norm_num)
  have hd : MemLp (fderiv ℝ f) 2 (volume : Measure Space) :=
    (hf.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hs.fderiv ℝ)
  have hfin : (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ≥0∞) *
      eLpNorm (fderiv ℝ f) 2 volume ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hd.eLpNorm_ne_top
  simpa [comparisonLpNorm, sobolevConstant, ENNReal.toReal_mul] using ENNReal.toReal_mono hfin h

/-- Multiplication by any positive natural power of a compact cutoff preserves
compact support, even if the multiplied function is not compactly supported. -/
theorem hasCompactSupport_cutoff_pow_smul {E : Type*} [Zero E] [SMulWithZero ℝ E]
    {φ : Space → ℝ} (hs : HasCompactSupport φ) (w : Space → E)
    {n : ℕ} (hn : n ≠ 0) : HasCompactSupport (fun x => φ x ^ n • w x) := by
  have hp : HasCompactSupport (fun x => φ x ^ n) :=
    hs.comp_left (g := fun r : ℝ => r ^ n) (by simp [hn])
  exact hp.smul_right

/-- All weighted velocity norms in the comparison argument are finite. -/
theorem memLp_cutoff_pow_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : Space → ℝ} {w : Space → E}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (hw : Continuous w)
    {n : ℕ} (hn : n ≠ 0) (p : ℝ≥0∞) :
    MemLp (fun x => φ x ^ n • w x) p (volume : Measure Space) :=
  ((hφ.pow n).smul hw).memLp_of_hasCompactSupport
    (hasCompactSupport_cutoff_pow_smul hs w hn)

/-- Derivative of the fourth power of a scalar cutoff. -/
theorem fderiv_cutoff_four {φ : Space → ℝ} {x : Space}
    (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (fun y => φ y ^ 4) x = (4 * φ x ^ 3) • fderiv ℝ φ x := by
  simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
    ((hasDerivAt_pow 4 (φ x)).comp_hasFDerivAt x hφ.hasFDerivAt).fderiv

/-- The pointwise product rule keeps the derivative of the velocity weighted. -/
theorem norm_fderiv_cutoff_four_le {φ : Space → ℝ} {w : Space → Space}
    {x : Space} (hφ : DifferentiableAt ℝ φ x) (hw : DifferentiableAt ℝ w x)
    (hφ0 : 0 ≤ φ x) :
    ‖fderiv ℝ (fun y => φ y ^ 4 • w y) x‖ ≤
      φ x ^ 4 * ‖fderiv ℝ w x‖ +
        4 * φ x ^ 3 * ‖fderiv ℝ φ x‖ * ‖w x‖ := by
  rw [fderiv_fun_smul (c := fun y => φ y ^ 4) (hφ.pow 4) hw,
    fderiv_cutoff_four hφ]
  calc
    ‖φ x ^ 4 • fderiv ℝ w x +
        ((4 * φ x ^ 3) • fderiv ℝ φ x).smulRight (w x)‖ ≤
        ‖φ x ^ 4 • fderiv ℝ w x‖ +
          ‖((4 * φ x ^ 3) • fderiv ℝ φ x).smulRight (w x)‖ := norm_add_le _ _
    _ ≤ ‖φ x ^ 4‖ * ‖fderiv ℝ w x‖ +
        (‖4 * φ x ^ 3‖ * ‖fderiv ℝ φ x‖) * ‖w x‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact add_le_add
        (ContinuousLinearMap.opNorm_smul_le (φ x ^ 4) (fderiv ℝ w x))
        (mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.opNorm_smul_le (4 * φ x ^ 3) (fderiv ℝ φ x))
          (norm_nonneg _))
    _ = _ := by simp [Real.norm_eq_abs, abs_of_nonneg hφ0]

/-- The pointwise magnitude of the weighted coordinate gradient. -/
def cutoffGradientAmplitude (φ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  φ x ^ 4 * Real.sqrt (gradientSq w x)

theorem cutoffGradientAmplitude_nonneg (φ : Space → ℝ) (w : Space → Space) (x : Space) :
    0 ≤ cutoffGradientAmplitude φ w x := by
  unfold cutoffGradientAmplitude
  positivity

theorem continuous_cutoffGradientAmplitude {φ : Space → ℝ} {w : Space → Space}
    (hφ : Continuous φ) (hw : ContDiff ℝ 1 w) :
    Continuous (cutoffGradientAmplitude φ w) :=
  (hφ.pow 4).mul (GradientOperator.continuous_gradientSq hw).sqrt

theorem hasCompactSupport_cutoffGradientAmplitude {φ : Space → ℝ}
    (hs : HasCompactSupport φ) (w : Space → Space) :
    HasCompactSupport (cutoffGradientAmplitude φ w) := by
  have hp : HasCompactSupport (fun x => φ x ^ 4) :=
    hs.comp_left (g := fun r : ℝ => r ^ 4) (by norm_num)
  exact hp.mul_right

theorem memLp_cutoffGradientAmplitude {φ : Space → ℝ} {w : Space → Space}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ 1 w)
    (p : ℝ≥0∞) : MemLp (cutoffGradientAmplitude φ w) p volume :=
  (continuous_cutoffGradientAmplitude hφ hw).memLp_of_hasCompactSupport
    (hasCompactSupport_cutoffGradientAmplitude hs w)

theorem norm_cutoffGradientAmplitude_sq (φ : Space → ℝ) (w : Space → Space) (x : Space) :
    ‖cutoffGradientAmplitude φ w x‖ ^ 2 = φ x ^ 8 * gradientSq w x := by
  rw [cutoffGradientAmplitude, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (GradientOperator.gradientSq_nonneg w x)]
  ring

/-- The weighted dissipation integral is finite solely from local regularity. -/
theorem integrable_weighted_gradientSq {φ : Space → ℝ} {w : Space → Space}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ 1 w) :
    Integrable (fun x => φ x ^ 8 * gradientSq w x) volume := by
  have hp : HasCompactSupport (fun x => φ x ^ 8) :=
    hs.comp_left (g := fun r : ℝ => r ^ 8) (by norm_num)
  exact ((hφ.pow 8).mul (GradientOperator.continuous_gradientSq hw)).integrable_of_hasCompactSupport
    hp.mul_right

theorem lpNorm_cutoffGradientAmplitude {φ : Space → ℝ} {w : Space → Space}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ 1 w) :
    comparisonLpNorm 2 (cutoffGradientAmplitude φ w) =
      Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) := by
  rw [LpNormTools.lpNorm_two_eq_sqrt_l2Sq (memLp_cutoffGradientAmplitude hφ hs hw 2)]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall (norm_cutoffGradientAmplitude_sq φ w))

/-- A pointwise majorant with no unweighted derivative term. -/
theorem norm_fderiv_cutoff_four_le_amplitude {φ : Space → ℝ} {w : Space → Space}
    {x : Space} (hφ : DifferentiableAt ℝ φ x) (hw : DifferentiableAt ℝ w x)
    (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1) {L : ℝ}
    (hL : ‖fderiv ℝ φ x‖ ≤ L) :
    ‖fderiv ℝ (fun y => φ y ^ 4 • w y) x‖ ≤
      3 * cutoffGradientAmplitude φ w x + (4 * L) * ‖w x‖ := by
  have hg := GradientOperator.norm_fderiv_le_three_mul_sqrt_gradientSq w x
  have hp : φ x ^ 3 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hd : φ x ^ 3 * ‖fderiv ℝ φ x‖ ≤ L :=
    (mul_le_of_le_one_left (norm_nonneg _) hp).trans hL
  calc
    ‖fderiv ℝ (fun y => φ y ^ 4 • w y) x‖ ≤
        φ x ^ 4 * ‖fderiv ℝ w x‖ +
          4 * φ x ^ 3 * ‖fderiv ℝ φ x‖ * ‖w x‖ :=
      norm_fderiv_cutoff_four_le hφ hw hφ0
    _ ≤ φ x ^ 4 * (3 * Real.sqrt (gradientSq w x)) +
        (4 * L) * ‖w x‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hg (by positivity)
      · nlinarith [mul_le_mul_of_nonneg_right hd (norm_nonneg (w x))]
    _ = _ := by unfold cutoffGradientAmplitude; ring

/-- The derivative of the cutoff velocity has a finite `L²` bound involving
only weighted dissipation and the velocity's unweighted `L²` norm. -/
theorem lpNorm_fderiv_cutoff_four_le {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ 1 w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L) :
    comparisonLpNorm 2 (fderiv ℝ (fun x => φ x ^ 4 • w x)) ≤
      3 * Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) + (4 * L) * comparisonLpNorm 2 w := by
  let G := cutoffGradientAmplitude φ w
  have hG : MemLp G 2 volume := memLp_cutoffGradientAmplitude hφ.continuous hs hw 2
  have hG3 : MemLp (fun x => (3 : ℝ) • G x) 2 volume := hG.const_smul (3 : ℝ)
  have hw4 : MemLp (fun x => (4 * L) • ‖w x‖) 2 volume := hw2.norm.const_smul (4 * L)
  calc
    comparisonLpNorm 2 (fderiv ℝ (fun x => φ x ^ 4 • w x)) ≤
        comparisonLpNorm 2 (fun x => (3 : ℝ) • G x + (4 * L) • ‖w x‖) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (hG3.add hw4)
      intro x
      have hp := norm_fderiv_cutoff_four_le_amplitude
        (hφ.differentiable (by simp) x) (hw.differentiable (by simp) x) (hφ0 x) (hφ1 x) (hL x)
      simpa only [Pi.add_apply, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ 3 * G x + (4 * L) * ‖w x‖ by
          have := cutoffGradientAmplitude_nonneg φ w x
          dsimp [G] at *
          positivity)] using hp
    _ ≤ comparisonLpNorm 2 (fun x => (3 : ℝ) • G x) +
        comparisonLpNorm 2 (fun x => (4 * L) • ‖w x‖) :=
      LpNormTools.lpNorm_add_le (by norm_num) hG3 hw4
    _ = 3 * Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) + (4 * L) * comparisonLpNorm 2 w := by
      rw [LpNormTools.lpNorm_const_smul, LpNormTools.lpNorm_const_smul]
      have hGeq := lpNorm_cutoffGradientAmplitude hφ.continuous hs hw
      change comparisonLpNorm 2 G = _ at hGeq
      rw [hGeq]
      simp [comparisonLpNorm, eLpNorm_norm, Real.norm_eq_abs, abs_of_nonneg hL0]

/-- A positive, fixed constant for the cutoff Sobolev estimate. -/
def weightedSobolevConstant : ℝ := 4 * sobolevConstant + 1

theorem weightedSobolevConstant_pos : 0 < weightedSobolevConstant := by
  have := sobolevConstant_nonneg
  unfold weightedSobolevConstant
  positivity

/-- The weighted Sobolev estimate `B ≤ C (A + L M)`. All dependence on the
cutoff is isolated in the derivative bound `L`; the constant is fixed. -/
theorem weighted_sobolev {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ 1 w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L) :
    comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ≤ weightedSobolevConstant *
      (Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) + L * comparisonLpNorm 2 w) := by
  have hSob := lpNorm_six_le ((hφ.pow 4).smul hw)
    (hasCompactSupport_cutoff_pow_smul hs w (by norm_num : (4 : ℕ) ≠ 0))
  have hDer := lpNorm_fderiv_cutoff_four_le hφ hs hw hw2 hφ0 hφ1 hL0 hL
  have hA := Real.sqrt_nonneg (∫ x, φ x ^ 8 * gradientSq w x)
  have hM := LpNormTools.lpNorm_nonneg 2 w
  have hS := sobolevConstant_nonneg
  apply hSob.trans
  apply (mul_le_mul_of_nonneg_left hDer hS).trans
  unfold weightedSobolevConstant
  nlinarith [mul_nonneg hS hA, mul_nonneg hL0 hM]

/-- Time-slice form using precisely the common comparison definitions. -/
theorem cutoffL6_le {φ : Space → ℝ} {w : VelocityField} {t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hw : ContDiff ℝ 1 (fun x => w (t, x)))
    (hw2 : MemLp (fun x => w (t, x)) 2 volume)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L) :
    cutoffL6 φ w t ≤ weightedSobolevConstant *
      (dissipationRoot φ w t + L * comparisonLpNorm 2 (fun x => w (t, x))) :=
  weighted_sobolev hφ hs hw hw2 hφ0 hφ1 hL0 hL

end NavierStokesR3.WeightedSobolev
