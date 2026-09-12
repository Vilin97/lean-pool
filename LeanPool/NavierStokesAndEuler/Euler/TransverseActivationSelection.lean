/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointVelocity
import LeanPool.NavierStokesAndEuler.Euler.Foundations.DNSelection
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEnergy
import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add
public import LeanPool.NavierStokesAndEuler.Euler.InitialTimePrimitive
import LeanPool.NavierStokesAndEuler.Euler.TimeH1OperatorProduct
import LeanPool.NavierStokesAndEuler.Euler.TimeH1PointwiseBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Source (26) for the actual stationary transverse solution.  The endpoint
matrix is the constructed Dirichlet-to-Neumann operator and its norm is
derived from the explicit moving-projection trial.  The selected velocity is
the genuine derivative η_t minus Mη, not a separately prescribed matrix output.
-/

section

/-!
An explicit terminal-layer H¹ trial obtained by multiplying a differentiable
projection path by the smooth exponential ramp.  Both energy estimates concern
the actual Bochner L² derivative and primitive.
-/

section

/-!
An explicit smooth terminal-layer trial profile.  Its endpoint values are
zero and one, and its squared value/derivative integrals are at most `2/L`
and `2*L` when `L*T ≥ 1`.  These are the same energy bounds needed for the
piecewise linear terminal ramp in the activation argument.
-/

@[expose] public section

noncomputable section

namespace EulerTerminalLayerRamp

open Set MeasureTheory

/-- Ramp, given by `(Real.exp (L * (t - T)) - Real.exp (-L * T)) / (1 - Real.exp (-L * T))`. -/
def ramp (T L t : ℝ) : ℝ :=
  (Real.exp (L * (t - T)) - Real.exp (-L * T)) / (1 - Real.exp (-L * T))

/-- Ramp derivative, given by `L * Real.exp (L * (t - T)) / (1 - Real.exp (-L * T))`. -/
def rampDerivative (T L t : ℝ) : ℝ :=
  L * Real.exp (L * (t - T)) / (1 - Real.exp (-L * T))

theorem denominator_lower {T L : ℝ} (hLT : 1 ≤ L * T) :
    (1 / 2 : ℝ) ≤ 1 - Real.exp (-L * T) := by
  have he : 2 ≤ Real.exp (L * T) := by
    linarith only [Real.add_one_le_exp (L * T), hLT]
  have hp : Real.exp (L * T) * Real.exp (-L * T) = 1 := by
    rw [← Real.exp_add]
    rw [show L * T + -L * T = 0 by ring, Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-L * T))
  nlinarith only [hp, hm]

theorem denominator_pos {T L : ℝ} (hLT : 1 ≤ L * T) :
    0 < 1 - Real.exp (-L * T) := lt_of_lt_of_le (by norm_num) (denominator_lower hLT)

@[simp] theorem ramp_initial (T L : ℝ) : ramp T L 0 = 0 := by
  simp [ramp, mul_neg]

theorem ramp_terminal {T L : ℝ} (hLT : 1 ≤ L * T) : ramp T L T = 1 := by
  simp only [ramp, sub_self, mul_zero, Real.exp_zero]
  exact div_self (denominator_pos hLT).ne'

theorem ramp_hasDerivAt (T L t : ℝ) : HasDerivAt (ramp T L) (rampDerivative T L t) t := by
  change HasDerivAt
    (fun s => (Real.exp (L * (s - T)) - Real.exp (-L * T)) / (1 - Real.exp (-L * T)))
    (L * Real.exp (L * (t - T)) / (1 - Real.exp (-L * T))) t
  simpa only [id_eq, mul_one, mul_comm] using
    (((((hasDerivAt_id t).sub_const T).const_mul L).exp).sub_const
      (Real.exp (-L * T))).div_const (1 - Real.exp (-L * T))

theorem ramp_continuous (T L : ℝ) : Continuous (ramp T L) :=
  continuous_iff_continuousAt.2 fun t => (ramp_hasDerivAt T L t).continuousAt

theorem rampDerivative_continuous (T L : ℝ) : Continuous (rampDerivative T L) := by
  unfold rampDerivative
  fun_prop

theorem ramp_nonneg {T L t : ℝ} (hL : 0 ≤ L) (hLT : 1 ≤ L * T)
    (ht : 0 ≤ t) : 0 ≤ ramp T L t := by
  apply div_nonneg _ (denominator_pos hLT).le
  apply sub_nonneg.mpr (Real.exp_le_exp.mpr _)
  nlinarith only [mul_nonneg hL ht]

theorem ramp_le_exp {T L t : ℝ} (hLT : 1 ≤ L * T) :
    ramp T L t ≤ 2 * Real.exp (L * (t - T)) := by
  apply (div_le_iff₀ (denominator_pos hLT)).2
  have hm := mul_le_mul_of_nonneg_right (denominator_lower hLT)
    (Real.exp_nonneg (L * (t - T)))
  nlinarith only [hm, Real.exp_nonneg (-L * T)]

theorem rampDerivative_nonneg {T L t : ℝ} (hL : 0 ≤ L) (hLT : 1 ≤ L * T) :
    0 ≤ rampDerivative T L t :=
  div_nonneg (mul_nonneg hL (Real.exp_nonneg _)) (denominator_pos hLT).le

theorem rampDerivative_le_exp {T L t : ℝ} (hL : 0 ≤ L) (hLT : 1 ≤ L * T) :
    rampDerivative T L t ≤ 2 * L * Real.exp (L * (t - T)) := by
  apply (div_le_iff₀ (denominator_pos hLT)).2
  have hm := mul_le_mul_of_nonneg_right (denominator_lower hLT)
    (mul_nonneg hL (Real.exp_nonneg (L * (t - T))))
  nlinarith only [hm]

theorem ramp_sq_le {T L t : ℝ} (hL : 0 ≤ L) (hLT : 1 ≤ L * T) (ht : 0 ≤ t) :
    ramp T L t ^ 2 ≤ 4 * Real.exp (2 * L * (t - T)) := by
  have hp := pow_le_pow_left₀ (ramp_nonneg hL hLT ht) (ramp_le_exp (t := t) hLT) 2
  have he : Real.exp (L * (t - T)) ^ 2 = Real.exp (2 * L * (t - T)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, he, show (2 : ℝ) ^ 2 = 4 by norm_num] using hp

theorem rampDerivative_sq_le {T L t : ℝ} (hL : 0 ≤ L) (hLT : 1 ≤ L * T) :
    rampDerivative T L t ^ 2 ≤ (4 * L ^ 2) * Real.exp (2 * L * (t - T)) := by
  have hp := pow_le_pow_left₀ (rampDerivative_nonneg (t := t) hL hLT)
    (rampDerivative_le_exp (t := t) hL hLT) 2
  have he : Real.exp (L * (t - T)) ^ 2 = Real.exp (2 * L * (t - T)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, he, show (2 : ℝ) ^ 2 = 4 by norm_num] using hp

theorem exp_kernel_integral_le {T L : ℝ} (hL : 0 < L) :
    (∫ t in 0..T, Real.exp (2 * L * (t - T))) ≤ 1 / (2 * L) := by
  have hd (t : ℝ) : HasDerivAt
      (fun s => Real.exp (2 * L * (s - T)) / (2 * L))
      (Real.exp (2 * L * (t - T))) t := by
    simpa only [id_eq, mul_one,
      mul_div_cancel_right₀ _ (show 2 * L ≠ 0 by positivity)] using
      (((((hasDerivAt_id t).sub_const T).const_mul (2 * L)).exp).div_const (2 * L))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub
        continuous_const))).intervalIntegrable 0 T)
  calc
    (∫ t in 0..T, Real.exp (2 * L * (t - T))) =
        (1 - Real.exp (2 * L * (0 - T))) / (2 * L) := by
      rw [hi, sub_self, mul_zero, Real.exp_zero, sub_div]
    _ ≤ 1 / (2 * L) := div_le_div_of_nonneg_right
      (sub_le_self _ (Real.exp_nonneg _)) (by positivity)

theorem ramp_energy {T L : ℝ} (hT : 0 ≤ T) (hL : 0 < L) (hLT : 1 ≤ L * T) :
    (∫ t in 0..T, ramp T L t ^ 2) ≤ 2 / L := by
  have hc : Continuous (fun t : ℝ => Real.exp (2 * L * (t - T))) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT
    (((ramp_continuous T L).pow 2).intervalIntegrable 0 T)
    ((continuous_const.mul hc).intervalIntegrable (a := 0) (b := T))
    (fun t ht => ramp_sq_le hL.le hLT ht.1)
  change (∫ t in 0..T, ramp T L t ^ 2) ≤
    ∫ t in 0..T, 4 * Real.exp (2 * L * (t - T)) at hi
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    (∫ t in 0..T, ramp T L t ^ 2) ≤ 4 * (∫ t in 0..T, Real.exp (2 * L * (t - T))) := hi
    _ ≤ 4 * (1 / (2 * L)) := mul_le_mul_of_nonneg_left (exp_kernel_integral_le hL) (by norm_num)
    _ = 2 / L := by ring

theorem rampDerivative_energy {T L : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hLT : 1 ≤ L * T) :
    (∫ t in 0..T, rampDerivative T L t ^ 2) ≤ 2 * L := by
  have hc : Continuous (fun t : ℝ => Real.exp (2 * L * (t - T))) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT
    (((rampDerivative_continuous T L).pow 2).intervalIntegrable 0 T)
    ((continuous_const.mul hc).intervalIntegrable (a := 0) (b := T))
    (fun t _ => rampDerivative_sq_le (t := t) hL.le hLT)
  change (∫ t in 0..T, rampDerivative T L t ^ 2) ≤
    ∫ t in 0..T, (4 * L ^ 2) * Real.exp (2 * L * (t - T)) at hi
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    (∫ t in 0..T, rampDerivative T L t ^ 2) ≤
        (4 * L ^ 2) * (∫ t in 0..T, Real.exp (2 * L * (t - T))) := hi
    _ ≤ (4 * L ^ 2) * (1 / (2 * L)) :=
      mul_le_mul_of_nonneg_left (exp_kernel_integral_le hL) (by positivity)
    _ = 2 * L := by field_simp; ring

end EulerTerminalLayerRamp

end
end

end

@[expose] public section

noncomputable section

namespace EulerTerminalProjectionTrial

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerTimeH1OperatorProduct EulerTimeH1PointwiseBounds EulerVolterraConvolution
  EulerTerminalLayerRamp

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTerminalProjectionTrial1 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTerminalProjectionTrial2 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
/-- Cache the standard `AddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTerminalProjectionTrial3 : AddCommGroup (U →L[ℝ] E) :=
  (inferInstance : NormedAddCommGroup (U →L[ℝ] E)).toAddCommGroup
/-- Cache the standard `Module ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTerminalProjectionTrial4 : Module ℝ (U →L[ℝ] E) :=
  (inferInstance : NormedSpace ℝ (U →L[ℝ] E)).toModule
/-- Cache the standard `TopologicalSpace (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTerminalProjectionTrial5 : TopologicalSpace (U →L[ℝ] E) :=
  (inferInstance : PseudoMetricSpace (U →L[ℝ] E)).toUniformSpace.toTopologicalSpace

variable (T : ℝ) (hT : 0 ≤ T) (L : ℝ)
  (P P₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))

/-- Evaluation of an actual continuous operator path as a bounded map into paths. -/
def operatorEvaluation (A : C(Icc (0 : ℝ) T, U →L[ℝ] E)) :
    U →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  ({ toFun := fun Y => ⟨fun t => A t Y, A.continuous.clm_apply continuous_const⟩
     map_add' := by intros; ext; simp
     map_smul' := by intros; ext; simp } :
      U →ₗ[ℝ] C(Icc (0 : ℝ) T, E)).mkContinuous ‖A‖ (by
        intro Y
        change ‖(⟨fun t => A t Y, A.continuous.clm_apply continuous_const⟩ :
          C(Icc (0 : ℝ) T, E))‖ ≤ ‖A‖ * ‖Y‖
        apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg Y))).2
        intro t
        exact (A t).le_opNorm Y |>.trans
          (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm t) (norm_nonneg Y)))

omit [CompleteSpace E] in
@[simp] theorem operatorEvaluation_apply
    (A : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (Y : U) (t : Icc (0 : ℝ) T) :
    operatorEvaluation T A Y t = A t Y := rfl

/-- Trial frame, given by `⟨fun t => ramp T L t • P t, ((ramp_continuous T L).comp
continuous_subtype_val).smul P.continuous⟩`. -/
def trialFrame : C(Icc (0 : ℝ) T, U →L[ℝ] E) :=
  ⟨fun t => ramp T L t • P t,
    ((ramp_continuous T L).comp continuous_subtype_val).smul P.continuous⟩

/-- Trial frame derivative as an element of `C(Icc (0 : ℝ) T, U →L[ℝ] E)`. -/
def trialFrameDerivative : C(Icc (0 : ℝ) T, U →L[ℝ] E) :=
  ⟨fun t => rampDerivative T L t • P t + ramp T L t • P₁ t,
    (((rampDerivative_continuous T L).comp continuous_subtype_val).smul P.continuous).add
      (((ramp_continuous T L).comp continuous_subtype_val).smul P₁.continuous)⟩

/-- Trial derivative, given by `(pathLpOperator T hT).comp (operatorEvaluation T
(trialFrameDerivative T L P P₁))`. -/
def trialDerivative : U →L[ℝ] TimeLp T E :=
  (pathLpOperator T hT).comp (operatorEvaluation T (trialFrameDerivative T L P P₁))

variable (hd : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT P) (P₁ t) (Icc (0 : ℝ) T) t)

include hd in
omit [CompleteSpace E] in
theorem trialFrame_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (trialFrame T L P))
      (trialFrameDerivative T L P P₁ t) (Icc (0 : ℝ) T) t := by
  have hs := (ramp_hasDerivAt T L t).hasDerivWithinAt.smul (hd t)
  have hs' : HasDerivWithinAt (fun s => ramp T L s • extendPath T hT P s)
      (trialFrameDerivative T L P P₁ t) (Icc (0 : ℝ) T) t := by
    convert! hs using 1
    simp only [trialFrameDerivative, ContinuousMap.coe_mk,
      extendPath, projIcc_of_mem hT t.property, add_comm]
  apply hs'.congr_of_mem _ t.property
  intro s hs
  simp only [extendPath, projIcc_of_mem hT hs, trialFrame, ContinuousMap.coe_mk]

include hd in
omit [CompleteSpace E] in
/-- The trial derivative is the actual derivative of its explicit ramp-times-projection path. -/
theorem trialDerivative_realizes (Y : U) :
    ∀ᵐ t ∂timeMeasure T,
      HasDerivAt (fun s => extendPath T hT (trialFrame T L P) s Y)
        (trialDerivative T hT L P P₁ Y t) t := by
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem, pathLp_ae T hT
    (operatorEvaluation T (trialFrameDerivative T L P P₁) Y)] with t ht hu
  change trialDerivative T hT L P P₁ Y t =
    extendPath T hT (operatorEvaluation T (trialFrameDerivative T L P P₁) Y) t at hu
  rw [hu]
  have hg := (trialFrame_hasDerivWithinAt T hT L P P₁ hd
    ⟨t, ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  simpa only [extendPath, projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩,
    operatorEvaluation_apply, map_zero, add_zero] using
      hg.clm_apply (hasDerivAt_const t Y)

include hd in
/-- Integrating the constructed L² derivative gives the prescribed trial at every time. -/
theorem initialPrimitive_trialDerivative (Y : U) (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT (trialDerivative T hT L P P₁ Y) t = ramp T L t • P t Y := by
  let η : ℝ → E := fun s => extendPath T hT (trialFrame T L P) s Y
  have hη : AbsolutelyContinuousOnInterval η 0 T :=
    clm_apply_absolutelyContinuous
      (operatorPath_absolutelyContinuous T hT (trialFrame T L P)
        (trialFrameDerivative T L P P₁) (trialFrame_hasDerivWithinAt T hT L P P₁ hd))
      ((LipschitzWith.const Y).lipschitzOnWith.absolutelyContinuousOnInterval)
  have hηd := trialDerivative_realizes T hT L P P₁ hd Y
  have he := eq_primitive_add_terminal T hT (trialDerivative T hT L P P₁ Y) η hη hηd t t.property
  have he0 := eq_primitive_add_terminal T hT (trialDerivative T hT L P P₁ Y) η hη hηd 0 ⟨le_rfl, hT⟩
  have hz : η 0 = 0 := by
    simp only [η, extendPath, projIcc_of_mem hT ⟨le_rfl, hT⟩,
      trialFrame, ContinuousMap.coe_mk, ramp_initial, zero_smul, zero_apply]
  change realPrimitive T (trialDerivative T hT L P P₁ Y) t -
    realPrimitive T (trialDerivative T hT L P P₁ Y) 0 = _
  rw [(eq_sub_iff_add_eq.mpr he.symm), (eq_sub_iff_add_eq.mpr he0.symm), hz]
  simp only [zero_sub, sub_neg_eq_add, sub_add_cancel]
  simp only [η, extendPath, projIcc_of_mem hT t.property, trialFrame,
    ContinuousMap.coe_mk, smul_apply]

include hd in
theorem initialPrimitiveTimeLp_trialDerivative (Y : U) :
    initialPrimitiveTimeLp T hT (trialDerivative T hT L P P₁ Y) =
      pathLp T hT (operatorEvaluation T (trialFrame T L P) Y) := by
  change pathLp T hT (initialPrimitive T hT (trialDerivative T hT L P P₁ Y)) = _
  apply congrArg (pathLp T hT)
  ext t
  exact initialPrimitive_trialDerivative T hT L P P₁ hd Y t

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
theorem norm_add_sq_le (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have hs := pow_le_pow_left₀ (norm_nonneg (a + b)) (norm_add_le a b) 2
  nlinarith only [hs, sq_nonneg (‖a‖ - ‖b‖)]

omit [CompleteSpace E] in
theorem trialFrameDerivative_apply_sq_le (M : ℝ) (_hM : 0 ≤ M)
    (hP : ∀ t, ‖P t‖ ≤ 1) (hP₁ : ∀ t, ‖P₁ t‖ ≤ M)
    (Y : U) (t : Icc (0 : ℝ) T) :
    ‖trialFrameDerivative T L P P₁ t Y‖ ^ 2 ≤
      (2 * rampDerivative T L t ^ 2 + 2 * ramp T L t ^ 2 * M ^ 2) * ‖Y‖ ^ 2 := by
  have hp : ‖P t Y‖ ≤ ‖Y‖ := by
    simpa only [one_mul] using (P t).le_opNorm Y |>.trans
      (mul_le_mul_of_nonneg_right (hP t) (norm_nonneg Y))
  have hp₁ : ‖P₁ t Y‖ ≤ M * ‖Y‖ := (P₁ t).le_opNorm Y |>.trans
    (mul_le_mul_of_nonneg_right (hP₁ t) (norm_nonneg Y))
  change ‖rampDerivative T L t • P t Y + ramp T L t • P₁ t Y‖ ^ 2 ≤ _
  calc
    _ ≤ 2 * ‖rampDerivative T L t • P t Y‖ ^ 2 +
        2 * ‖ramp T L t • P₁ t Y‖ ^ 2 := norm_add_sq_le _ _
    _ = 2 * rampDerivative T L t ^ 2 * ‖P t Y‖ ^ 2 +
        2 * ramp T L t ^ 2 * ‖P₁ t Y‖ ^ 2 := by
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    _ ≤ 2 * rampDerivative T L t ^ 2 * ‖Y‖ ^ 2 +
        2 * ramp T L t ^ 2 * (M * ‖Y‖) ^ 2 := by gcongr
    _ = _ := by ring

omit [CompleteSpace E] in
/-- The actual L² derivative cost of the explicit terminal-layer trial. -/
theorem trialDerivative_norm_sq_le (hL : 0 < L) (hLT : 1 ≤ L * T)
    (M : ℝ) (hM : 0 ≤ M) (hP : ∀ t, ‖P t‖ ≤ 1) (hP₁ : ∀ t, ‖P₁ t‖ ≤ M)
    (Y : U) :
    ‖trialDerivative T hT L P P₁ Y‖ ^ 2 ≤ (4 * L + 4 * M ^ 2 / L) * ‖Y‖ ^ 2 := by
  change ‖pathLp T hT (operatorEvaluation T (trialFrameDerivative T L P P₁) Y)‖ ^ 2 ≤ _
  rw [pathLp_norm_sq]
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT
    (((extendPath_continuous T hT (operatorEvaluation T (trialFrameDerivative T L P P₁)
        Y)).norm.pow 2).intervalIntegrable 0 T)
    ((((((rampDerivative_continuous T L).pow 2).const_mul 2).add
      ((((ramp_continuous T L).pow 2).const_mul 2).mul_const (M ^ 2))).mul_const (‖Y‖ ^
          2)).intervalIntegrable 0 T)
    (fun s hs => by
      change ‖extendPath T hT (operatorEvaluation T (trialFrameDerivative T L P P₁) Y) s‖ ^ 2 ≤
        (2 * rampDerivative T L s ^ 2 + 2 * ramp T L s ^ 2 * M ^ 2) * ‖Y‖ ^ 2
      simpa only [extendPath, projIcc_of_mem hT hs, operatorEvaluation_apply] using
        trialFrameDerivative_apply_sq_le T L P P₁ M hM hP hP₁ Y ⟨s, hs⟩)
  change (∫ s in 0..T, ‖extendPath T hT
    (operatorEvaluation T (trialFrameDerivative T L P P₁) Y) s‖ ^ 2) ≤
      ∫ s in 0..T, (2 * rampDerivative T L s ^ 2 + 2 * ramp T L s ^ 2 * M ^ 2) * ‖Y‖ ^ 2 at hi
  have hv : IntervalIntegrable (fun s => ramp T L s ^ 2) volume 0 T :=
    ((ramp_continuous T L).pow 2).intervalIntegrable 0 T
  have hdv : IntervalIntegrable (fun s => rampDerivative T L s ^ 2) volume 0 T :=
    ((rampDerivative_continuous T L).pow 2).intervalIntegrable 0 T
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add (hdv.const_mul 2) ((hv.const_mul 2).mul_const (M ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul] at hi
  apply hi.trans
  calc
    (2 * (∫ s in 0..T, rampDerivative T L s ^ 2) +
      2 * (∫ s in 0..T, ramp T L s ^ 2) * M ^ 2) * ‖Y‖ ^ 2 ≤
        (2 * (2 * L) + 2 * (2 / L) * M ^ 2) * ‖Y‖ ^ 2 := by
      gcongr
      · exact rampDerivative_energy hT hL hLT
      · exact ramp_energy hT hL hLT
    _ = _ := by ring

include hd in
/-- The corresponding physical displacement cost retains the inverse layer width. -/
theorem trialDisplacement_norm_sq_le (hL : 0 < L) (hLT : 1 ≤ L * T)
    (hP : ∀ t, ‖P t‖ ≤ 1) (Y : U) :
    ‖initialPrimitiveTimeLp T hT (trialDerivative T hT L P P₁ Y)‖ ^ 2 ≤
      (2 / L) * ‖Y‖ ^ 2 := by
  rw [initialPrimitiveTimeLp_trialDerivative T hT L P P₁ hd, pathLp_norm_sq]
  have hv := ((ramp_continuous T L).pow 2).intervalIntegrable (μ := volume) 0 T
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT
    (((extendPath_continuous T hT (operatorEvaluation T (trialFrame T L P) Y)).norm.pow
        2).intervalIntegrable 0 T)
    (hv.mul_const (‖Y‖ ^ 2)) (fun s hs => by
      change ‖extendPath T hT (operatorEvaluation T (trialFrame T L P) Y) s‖ ^ 2 ≤
        ramp T L s ^ 2 * ‖Y‖ ^ 2
      simp only [extendPath, projIcc_of_mem hT hs, operatorEvaluation_apply,
        trialFrame, ContinuousMap.coe_mk, smul_apply, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs]
      have hp : ‖P ⟨s, hs⟩ Y‖ ≤ ‖Y‖ := by
        simpa only [one_mul] using (P ⟨s, hs⟩).le_opNorm Y |>.trans
          (mul_le_mul_of_nonneg_right (hP ⟨s, hs⟩) (norm_nonneg Y))
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hp 2) (sq_nonneg _))
  change (∫ s in 0..T, ‖extendPath T hT
    (operatorEvaluation T (trialFrame T L P) Y) s‖ ^ 2) ≤
      ∫ s in 0..T, ramp T L s ^ 2 * ‖Y‖ ^ 2 at hi
  rw [intervalIntegral.integral_mul_const] at hi
  exact hi.trans (mul_le_mul_of_nonneg_right (ramp_energy hT hL hLT) (sq_nonneg _))

end EulerTerminalProjectionTrial

end
end

end

section

/-!
The explicit activation trial and its endpoint-energy bound.  The trial uses
the actual moving normal, not a deformation-frame condition number.  A layer
of width `1/h` gives `‖Λ‖ ≤ (4 + 64 CM² + 2 CH) h` under the source's low
history bounds.
-/

section

/-!
The actual orthogonal projection onto a moving ray's perpendicular plane.
The derivative bound depends on the ray equation through `‖m'‖/‖m‖`, and
therefore costs only the parent matrix norm, with no deformation-gradient loss.
-/

@[expose] public section

noncomputable section

namespace EulerMovingNormalProjection

open InnerProductSpace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instMovingNormalProjection1 : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instMovingNormalProjection2 : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
/-- Cache the standard `AddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instMovingNormalProjection3 : AddCommGroup (E →L[ℝ] E) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E)).toAddCommGroup
/-- Cache the standard `Module ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instMovingNormalProjection4 : Module ℝ (E →L[ℝ] E) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E)).toModule
/-- Cache the standard `TopologicalSpace (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instMovingNormalProjection5 : TopologicalSpace (E →L[ℝ] E) :=
  (inferInstance : PseudoMetricSpace (E →L[ℝ] E)).toUniformSpace.toTopologicalSpace

/-- Normal projection, given by `ContinuousLinearMap.id ℝ E - (‖m‖ ^ 2)⁻¹ • rankOne ℝ m m`. -/
def normalProjection (m : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (‖m‖ ^ 2)⁻¹ • rankOne ℝ m m

theorem normalProjection_apply (m x : E) :
    normalProjection m x = x - (⟪m, x⟫_ℝ / ‖m‖ ^ 2) • m := by
  simp only [normalProjection, sub_apply, id_apply, smul_apply, rankOne_apply,
    smul_smul, div_eq_mul_inv, mul_comm]

theorem normalProjection_tangent (m : E) (hm : m ≠ 0) (x : E) :
    ⟪m, normalProjection m x⟫_ℝ = 0 := by
  rw [normalProjection_apply, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem normalProjection_fixed (m x : E) (hx : ⟪m, x⟫_ℝ = 0) :
    normalProjection m x = x := by
  rw [normalProjection_apply, hx, zero_div, zero_smul, sub_zero]

theorem normalProjection_norm_sq (m : E) (hm : m ≠ 0) (x : E) :
    ‖normalProjection m x‖ ^ 2 = ‖x‖ ^ 2 - ⟪m, x⟫_ℝ ^ 2 / ‖m‖ ^ 2 := by
  rw [normalProjection_apply, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm m x]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

theorem normalProjection_norm_le (m : E) (hm : m ≠ 0) : ‖normalProjection m‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp only [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [normalProjection_norm_sq m hm]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Normal projection derivative, given by `-((- (2 * ⟪m, m₁⟫_ℝ) / (‖m‖ ^ 2) ^ 2) • rankOne ℝ m
m + (‖m‖ ^ 2)⁻¹ • (rankOne ℝ m₁ m + rankOne ℝ m m₁))`. -/
def normalProjectionDerivative (m m₁ : E) : E →L[ℝ] E :=
  -((- (2 * ⟪m, m₁⟫_ℝ) / (‖m‖ ^ 2) ^ 2) • rankOne ℝ m m +
    (‖m‖ ^ 2)⁻¹ • (rankOne ℝ m₁ m + rankOne ℝ m m₁))

/-- The projection derivative is derived from the actual ray derivative. -/
theorem normalProjection_hasDerivAt {m : ℝ → E} {m₁ : E} {t : ℝ}
    (hd : HasDerivAt m m₁ t) (hm : m t ≠ 0) :
    HasDerivAt (fun s => normalProjection (m s))
      (normalProjectionDerivative (m t) m₁) t := by
  have hr : HasDerivAt (fun s => rankOne ℝ (m s) (m s))
      (rankOne ℝ m₁ (m t) + rankOne ℝ (m t) m₁) t := by
    convert! ContinuousLinearMap.hasDerivAt_of_bilinear
      (B := (rankOne ℝ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)) (fun _ => hd) (fun _ => hd) using 1
    ext v
    change ⟪m t, v⟫_ℝ • m₁ + ⟪m₁, v⟫_ℝ • m t =
      ⟪m₁, v⟫_ℝ • m t + ⟪m t, v⟫_ℝ • m₁
    exact add_comm _ _
  have hi := hd.norm_sq.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hm))
  change HasDerivAt (fun s => ContinuousLinearMap.id ℝ E - (‖m s‖ ^ 2)⁻¹ • rankOne ℝ (m s) (m s))
    (normalProjectionDerivative (m t) m₁) t
  convert! (hi.smul hr).const_sub (ContinuousLinearMap.id ℝ E) using 1
  simp only [normalProjectionDerivative, Pi.inv_apply, add_comm]

theorem normalProjection_hasDerivWithinAt {m : ℝ → E} {m₁ : E} {t : ℝ} {S : Set ℝ}
    (hd : HasDerivWithinAt m m₁ S t) (hm : m t ≠ 0) :
    HasDerivWithinAt (fun s => normalProjection (m s))
      (normalProjectionDerivative (m t) m₁) S t := by
  have hr : HasDerivWithinAt (fun s => rankOne ℝ (m s) (m s))
      (rankOne ℝ m₁ (m t) + rankOne ℝ (m t) m₁) S t := by
    convert! ContinuousLinearMap.hasDerivWithinAt_of_bilinear
      (B := (rankOne ℝ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)) hd hd using 1
    ext v
    change ⟪m t, v⟫_ℝ • m₁ + ⟪m₁, v⟫_ℝ • m t =
      ⟪m₁, v⟫_ℝ • m t + ⟪m t, v⟫_ℝ • m₁
    exact add_comm _ _
  have hi := hd.norm_sq.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hm))
  change HasDerivWithinAt
    (fun s => ContinuousLinearMap.id ℝ E - (‖m s‖ ^ 2)⁻¹ • rankOne ℝ (m s) (m s))
    (normalProjectionDerivative (m t) m₁) S t
  convert! (hi.smul hr).const_sub (ContinuousLinearMap.id ℝ E) using 1
  simp only [normalProjectionDerivative, Pi.inv_apply, add_comm]

theorem normalProjection_continuous {α : Type*} [TopologicalSpace α]
    {f : α → E} (hf : Continuous f) (hne : ∀ a, f a ≠ 0) :
    Continuous (fun a => normalProjection (f a)) := by
  let R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E := rankOne ℝ
  have hr : Continuous (fun a => rankOne ℝ (f a) (f a)) := R.continuous₂.comp₂ hf hf
  exact continuous_const.sub
    (((hf.norm.pow 2).inv₀ (fun a => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne a)))).smul hr)

theorem normalProjectionDerivative_continuous {α : Type*} [TopologicalSpace α]
    {f g : α → E} (hf : Continuous f) (hg : Continuous g) (hne : ∀ a, f a ≠ 0) :
    Continuous (fun a => normalProjectionDerivative (f a) (g a)) := by
  let R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E := rankOne ℝ
  have h0 : Continuous (fun a => rankOne ℝ (f a) (f a)) := R.continuous₂.comp₂ hf hf
  have h1 : Continuous (fun a => rankOne ℝ (g a) (f a)) := R.continuous₂.comp₂ hg hf
  have h2 : Continuous (fun a => rankOne ℝ (f a) (g a)) := R.continuous₂.comp₂ hf hg
  have hn := fun a => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne a))
  have hi := (hf.norm.pow 2).inv₀ hn
  have hq := ((hf.inner hg).const_mul 2).neg.div ((hf.norm.pow 2).pow 2)
    (fun a => pow_ne_zero 2 (hn a))
  exact ((hq.smul h0).add (hi.smul (h1.add h2))).neg

/-- The bound is independent of the length of the ray. -/
theorem normalProjectionDerivative_norm_le (m m₁ : E) (hm : m ≠ 0) :
    ‖normalProjectionDerivative m m₁‖ ≤ 4 * ‖m₁‖ / ‖m‖ := by
  have hmpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hnorm : 0 ≤ ‖m‖ ^ 2 := sq_nonneg _
  have hr := abs_real_inner_le_norm m m₁
  have hs := norm_add_le (rankOne ℝ m₁ m) (rankOne ℝ m m₁)
  simp only [norm_rankOne] at hs
  calc
    ‖normalProjectionDerivative m m₁‖ ≤
        |-(2 * ⟪m, m₁⟫_ℝ) / (‖m‖ ^ 2) ^ 2| * (‖m‖ * ‖m‖) +
          |(‖m‖ ^ 2)⁻¹| * (‖m₁‖ * ‖m‖ + ‖m‖ * ‖m₁‖) := by
      unfold normalProjectionDerivative
      rw [norm_neg]
      apply (norm_add_le _ _).trans
      rw [norm_smul, norm_smul, norm_rankOne, Real.norm_eq_abs, Real.norm_eq_abs]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
    _ = (2 * |⟪m, m₁⟫_ℝ| / (‖m‖ ^ 2) ^ 2) * (‖m‖ * ‖m‖) +
          (‖m‖ ^ 2)⁻¹ * (‖m₁‖ * ‖m‖ + ‖m‖ * ‖m₁‖) := by
      rw [abs_div, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg (‖m‖ ^ 2)), abs_of_nonneg (inv_nonneg.mpr hnorm)]
    _ ≤ (2 * (‖m‖ * ‖m₁‖) / (‖m‖ ^ 2) ^ 2) * (‖m‖ * ‖m‖) +
          (‖m‖ ^ 2)⁻¹ * (‖m₁‖ * ‖m‖ + ‖m‖ * ‖m₁‖) := by
      gcongr
    _ = 4 * ‖m₁‖ / ‖m‖ := by
      field_simp
      ring

variable [CompleteSpace E]

/-- For the actual ray equation `m'=-M* m`, only the parent gradient norm enters. -/
theorem normalProjectionDerivative_ray_bound (m : E) (hm : m ≠ 0) (M : E →L[ℝ] E) :
    ‖normalProjectionDerivative m (-(M.adjoint m))‖ ≤ 4 * ‖M‖ := by
  have hb : ‖-(M.adjoint m)‖ ≤ ‖M‖ * ‖m‖ := by
    simpa only [norm_neg, LinearIsometryEquiv.norm_map] using M.adjoint.le_opNorm m
  calc
    ‖normalProjectionDerivative m (-(M.adjoint m))‖ ≤
        4 * ‖-(M.adjoint m)‖ / ‖m‖ := normalProjectionDerivative_norm_le m _ hm
    _ ≤ 4 * (‖M‖ * ‖m‖) / ‖m‖ := by gcongr
    _ = 4 * ‖M‖ := by field_simp

end EulerMovingNormalProjection

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransverseActivationTrial

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerInitialTimePrimitive EulerVolterraConvolution
  EulerTerminalProjectionTrial EulerTerminalLayerRamp
  EulerMovingNormalProjection EulerTransverseEndpointEnergy

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial1 : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial2 : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
/-- Cache the standard `AddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial3 : AddCommGroup (E →L[ℝ] E) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E)).toAddCommGroup
/-- Cache the standard `Module ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial4 : Module ℝ (E →L[ℝ] E) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E)).toModule
/-- Cache the standard `TopologicalSpace (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial5 : TopologicalSpace (E →L[ℝ] E) :=
  (inferInstance : PseudoMetricSpace (E →L[ℝ] E)).toUniformSpace.toTopologicalSpace
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial6 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial7 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
/-- Cache the standard `AddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial8 : AddCommGroup (U →L[ℝ] E) :=
  (inferInstance : NormedAddCommGroup (U →L[ℝ] E)).toAddCommGroup
/-- Cache the standard `Module ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial9 : Module ℝ (U →L[ℝ] E) :=
  (inferInstance : NormedSpace ℝ (U →L[ℝ] E)).toModule
/-- Cache the standard `TopologicalSpace (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instTransverseActivationTrial10 : TopologicalSpace (U →L[ℝ] E) :=
  (inferInstance : PseudoMetricSpace (U →L[ℝ] E)).toUniformSpace.toTopologicalSpace

variable (T : ℝ) (hT : 0 ≤ T) (m m₁ : C(Icc (0 : ℝ) T, E))
  (hne : ∀ t, m t ≠ 0) (R : U →L[ℝ] E)

/-- Projection path, given by `⟨fun t => (normalProjection (m t)).comp R,
(normalProjection_continuous m.continuous hne).clm_comp continuous_const⟩`. -/
def projectionPath : C(Icc (0 : ℝ) T, U →L[ℝ] E) :=
  ⟨fun t => (normalProjection (m t)).comp R,
    (normalProjection_continuous m.continuous hne).clm_comp continuous_const⟩

/-- Projection derivative path as an element of `C(Icc (0 : ℝ) T, U →L[ℝ] E)`. -/
def projectionDerivativePath : C(Icc (0 : ℝ) T, U →L[ℝ] E) :=
  ⟨fun t => (normalProjectionDerivative (m t) (m₁ t)).comp R,
    (normalProjectionDerivative_continuous m.continuous m₁.continuous hne).clm_comp
        continuous_const⟩

variable (hd : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT m) (m₁ t) (Icc (0 : ℝ) T) t)

include hd in
theorem projectionPath_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (projectionPath T m hne R))
      (projectionDerivativePath T m m₁ hne R t) (Icc (0 : ℝ) T) t := by
  have hm : extendPath T hT m t ≠ 0 := by
    simpa only [extendPath, projIcc_of_mem hT t.property] using hne t
  have hp := normalProjection_hasDerivWithinAt (hd t) hm
  have hc := hp.clm_comp (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) R)
  convert! hc using 1
  simp only [projectionDerivativePath, ContinuousMap.coe_mk,
    extendPath, projIcc_of_mem hT t.property, comp_zero, add_zero]

theorem projectionPath_norm_le (hR : ‖R‖ ≤ 1) (t : Icc (0 : ℝ) T) :
    ‖projectionPath T m hne R t‖ ≤ 1 := by
  calc
    ‖projectionPath T m hne R t‖ ≤ ‖normalProjection (m t)‖ * ‖R‖ := opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (normalProjection_norm_le (m t) (hne t)) hR
      (norm_nonneg R) (by norm_num)
    _ = 1 := one_mul 1

variable [CompleteSpace E]

theorem projectionDerivativePath_norm_le (hR : ‖R‖ ≤ 1)
    (M : Icc (0 : ℝ) T → E →L[ℝ] E)
    (hRay : ∀ t, m₁ t = -(M t).adjoint (m t))
    (B : ℝ) (_hB : 0 ≤ B) (hM : ∀ t, ‖M t‖ ≤ B) (t : Icc (0 : ℝ) T) :
    ‖projectionDerivativePath T m m₁ hne R t‖ ≤ 4 * B := by
  calc
    ‖projectionDerivativePath T m m₁ hne R t‖ ≤
        ‖normalProjectionDerivative (m t) (m₁ t)‖ * ‖R‖ := opNorm_comp_le _ _
    _ ≤ (4 * ‖M t‖) * 1 := by
      apply mul_le_mul _ hR (norm_nonneg R) (by positivity)
      rw [hRay]
      exact normalProjectionDerivative_ray_bound (m t) (hne t) (M t)
    _ ≤ 4 * B := by nlinarith only [hM t]

/-- The actual derivative of the explicit terminal-layer displacement. -/
def activationTrial (h : ℝ) : U →L[ℝ] TimeLp T E :=
  trialDerivative T hT h (projectionPath T m hne R) (projectionDerivativePath T m m₁ hne R)

include hd in
theorem activationTrial_primitive (h : ℝ) (Y : U) (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT (activationTrial T hT m m₁ hne R h Y) t =
      ramp T h t • normalProjection (m t) (R Y) :=
  initialPrimitive_trialDerivative T hT h (projectionPath T m hne R)
    (projectionDerivativePath T m m₁ hne R)
    (projectionPath_hasDerivWithinAt T hT m m₁ hne R hd) Y t

include hd in
theorem activationTrial_tangent (h : ℝ) (Y : U) (t : Icc (0 : ℝ) T) :
    ⟪m t, initialPrimitive T hT (activationTrial T hT m m₁ hne R h Y) t⟫_ℝ = 0 := by
  rw [activationTrial_primitive T hT m m₁ hne R hd, real_inner_smul_right,
    normalProjection_tangent (m t) (hne t), mul_zero]

include hd in
theorem activationTrial_terminal (h : ℝ) (hLayer : 1 ≤ h * T)
    (hR : ∀ Y, ⟪m ⟨T, hT, le_rfl⟩, R Y⟫_ℝ = 0) (Y : U) :
    initialPrimitive T hT (activationTrial T hT m m₁ hne R h Y) ⟨T, hT, le_rfl⟩ = R Y := by
  rw [activationTrial_primitive T hT m m₁ hne R hd, ramp_terminal hLayer,
    one_smul, normalProjection_fixed _ _ (hR Y)]

omit [CompleteSpace E] in
theorem potential_abs_bound (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (u : TimeLp T E) :
    |⟪timeMultiplier T hT H u, u⟫_ℝ| ≤ ‖H‖ * ‖u‖ ^ 2 := by
  calc
    |⟪timeMultiplier T hT H u, u⟫_ℝ| ≤ ‖timeMultiplier T hT H u‖ * ‖u‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖H‖ * ‖u‖) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (timeApply_bound T hT H u) (norm_nonneg u)
    _ = _ := by ring

variable [CompleteSpace U]

include hd in
/-- All input bounds concern the parent coefficients and the actual ray.  The
endpoint operator and its `O(h)` norm are constructed conclusions. -/
theorem activation_endpoint_norm
    (h : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h * T)
    (hR : ‖R‖ ≤ 1) (CM CH : ℝ) (hCM : 0 ≤ CM) (hCH : 0 ≤ CH)
    (M : Icc (0 : ℝ) T → E →L[ℝ] E)
    (hRay : ∀ t, m₁ t = -(M t).adjoint (m t)) (hM : ∀ t, ‖M t‖ ≤ CM * h)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (hHs : ∀ t, (H t).IsSymmetric)
    (hHnorm : ‖H‖ ≤ CH * h ^ 2)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2) :
    ‖dirichletToNeumann T hT (fun t => m t) H K hK hH hsmall
      (activationTrial T hT m m₁ hne R h)‖ ≤ (4 + 64 * CM ^ 2 + 2 * CH) * h := by
  apply dirichletToNeumann_norm_le T hT (fun t => m t) H K hK hH hsmall hHs
    (activationTrial T hT m m₁ hne R h) ((4 + 64 * CM ^ 2 + 2 * CH) * h) (by positivity)
  intro Y
  have hproj := projectionPath_norm_le T m hne R hR
  have hproj₁ := projectionDerivativePath_norm_le T m m₁ hne R hR M hRay
    (CM * h) (by positivity) hM
  have hD := trialDerivative_norm_sq_le T hT h (projectionPath T m hne R)
    (projectionDerivativePath T m m₁ hne R) hh hLayer
    (4 * (CM * h)) (by positivity) hproj hproj₁ Y
  have hη := trialDisplacement_norm_sq_le T hT h (projectionPath T m hne R)
    (projectionDerivativePath T m m₁ hne R)
    (projectionPath_hasDerivWithinAt T hT m m₁ hne R hd) hh hLayer hproj Y
  change ‖activationTrial T hT m m₁ hne R h Y‖ ^ 2 ≤
    (4 * h + 4 * (4 * (CM * h)) ^ 2 / h) * ‖Y‖ ^ 2 at hD
  change ‖initialPrimitiveTimeLp T hT (activationTrial T hT m m₁ hne R h Y)‖ ^ 2 ≤
    (2 / h) * ‖Y‖ ^ 2 at hη
  let u := activationTrial T hT m m₁ hne R h Y
  let η := initialPrimitiveTimeLp T hT u
  have hp : -⟪timeMultiplier T hT H η, η⟫_ℝ ≤ CH * h ^ 2 * ‖η‖ ^ 2 := by
    exact (neg_le_abs _).trans ((potential_abs_bound T hT H η).trans
      (mul_le_mul_of_nonneg_right hHnorm (sq_nonneg _)))
  change ‖u‖ ^ 2 - ⟪timeMultiplier T hT H η, η⟫_ℝ ≤ _
  calc
    ‖u‖ ^ 2 - ⟪timeMultiplier T hT H η, η⟫_ℝ ≤ ‖u‖ ^ 2 + CH * h ^ 2 * ‖η‖ ^ 2 := by
        linarith only [hp]
    _ ≤ (4 * h + 4 * (4 * (CM * h)) ^ 2 / h) * ‖Y‖ ^ 2 +
        CH * h ^ 2 * ((2 / h) * ‖Y‖ ^ 2) :=
      add_le_add hD (mul_le_mul_of_nonneg_left hη (by positivity))
    _ = (4 + 64 * CM ^ 2 + 2 * CH) * h * ‖Y‖ ^ 2 := by field_simp; ring

end EulerTransverseActivationTrial

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransverseActivationSelection

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerInitialTimePrimitive EulerVolterraConvolution
  EulerTransverseEndpointEnergy EulerTransverseEndpointVelocity
  EulerTransverseActivationTrial EulerDNSelection

variable {U E V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Activation constant, given by `4 + 64 * CM ^ 2 + 2 * CH`. -/
def activationConstant (CM CH : ℝ) : ℝ := 4 + 64 * CM ^ 2 + 2 * CH

/-- The actual terminal matrix after subtracting the prescribed shear. -/
def terminalPerturbation (T : ℝ) (hT : 0 ≤ T) (R : V →ₗᵢ[ℝ] E)
    (M : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (p q : V) (h : ℝ) : V →L[ℝ] V :=
  R.toContinuousLinearMap.adjoint.comp
    ((M ⟨T, hT, le_rfl⟩).comp R.toContinuousLinearMap) - h • rankOne ℝ q p

/-- Differentiating the actual moving tangency constraint makes η_t−Mη tangent. -/
theorem corrected_velocity_tangent (T : ℝ) (hT : 0 < T)
    (m m₁ : C(Icc (0 : ℝ) T, E))
    (M : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hdm : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT.le m) (m₁ t) (Icc (0 : ℝ) T) t)
    (hRay : ∀ t, m₁ t = -(M t).adjoint (m t))
    (η v : ℝ → E)
    (hdη : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt η (v t) (Icc (0 : ℝ) T) t)
    (htan : ∀ t : Icc (0 : ℝ) T, ⟪m t, η t⟫_ℝ = 0)
    (t : Icc (0 : ℝ) T) : ⟪m t, v t - M t (η t)⟫_ℝ = 0 := by
  have hd := (hdm t).inner ℝ (hdη t)
  have hz : HasDerivWithinAt (fun s => ⟪extendPath T hT.le m s, η s⟫_ℝ)
      (0 : ℝ) (Icc (0 : ℝ) T) t := by
    apply (hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) T) (0 : ℝ)).congr_of_mem _ t.property
    intro s hs
    simpa only [extendPath, projIcc_of_mem hT.le hs] using htan ⟨s, hs⟩
  have he := (hd.derivWithin ((uniqueDiffOn_Icc hT) t t.property)).symm.trans
    (hz.derivWithin ((uniqueDiffOn_Icc hT) t t.property))
  simp only [extendPath, projIcc_of_mem hT.le t.property, hRay,
    inner_neg_left, adjoint_inner_left, inner_sub_right] at he ⊢
  linarith only [he]

/-- The activation choice is attached to the actual weak inverse, its continuous
physical derivative, and the derived endpoint energy bound. -/
theorem select_actual_activation
    (T : ℝ) (hT : 0 < T)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)
    (hdQ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT.le Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (m m₁ : C(Icc (0 : ℝ) T, E)) (hne : ∀ t, m t ≠ 0)
    (hdm : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT.le m) (m₁ t) (Icc (0 : ℝ) T) t)
    (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (R : V →ₗᵢ[ℝ] E) (hR : ∀ Y, ⟪m ⟨T, hT.le, le_rfl⟩, R Y⟫_ℝ = 0)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (hHs : ∀ t, (H t).IsSymmetric)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
    (M : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (hRay : ∀ t, m₁ t = -(M t).adjoint (m t))
    (h CM CH ε : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h * T)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hε : 0 ≤ ε)
    (hM : ∀ t, ‖M t‖ ≤ CM * h) (hHnorm : ‖H‖ ≤ CH * h ^ 2)
    (p q : V) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫_ℝ = 0)
    (hεsmall : 16 * (activationConstant CM CH + 1) * ε ≤ 1)
    (hB : ‖terminalPerturbation T hT.le R M p q h‖ ≤ ε * h)
    (hBpp : ⟪terminalPerturbation T hT.le R M p q h p, p⟫_ℝ < 0) :
    ∃ Y : V,
      let L := activationTrial T hT.le m m₁ hne R.toContinuousLinearMap h
      let u := endpointDerivative T hT.le (fun t => m t) H K hK hH hsmall L Y
      let η := initialRealPrimitive T u
      let v := physicalVelocityPath T hT.le Q Q₁ c hc hQ H u
      let w := fun t => v t - extendPath T hT.le M t (η t)
      η 0 = 0 ∧ η T = R Y ∧ Continuous v ∧
      (∀ t : Icc (0 : ℝ) T, HasDerivWithinAt η (v t) (Icc (0 : ℝ) T) t) ∧
      (∀ t : Icc (0 : ℝ) T, ⟪m t, w t⟫_ℝ = 0) ∧
      ⟪w T, R q⟫_ℝ = 1 ∧
      -8 * (activationConstant CM CH + 1) ≤ ⟪w T, R p⟫_ℝ ∧
      ⟪w T, R p⟫_ℝ ≤ 0 ∧
      ‖Y‖ ≤ 8 * (activationConstant CM CH + 1) / h := by
  let L := activationTrial T hT.le m m₁ hne R.toContinuousLinearMap h
  let Λ := dirichletToNeumann T hT.le (fun t => m t) H K hK hH hsmall L
  let B := terminalPerturbation T hT.le R M p q h
  have hΛ : Λ.IsPositive :=
    dirichletToNeumann_positive T hT.le (fun t => m t) H K hK hH hsmall hHs L
  have hΛnorm : ‖Λ‖ ≤ activationConstant CM CH * h :=
    activation_endpoint_norm T hT.le m m₁ hne R.toContinuousLinearMap hdm h hh hLayer
      R.norm_toContinuousLinearMap_le CM CH hCM hCH M hRay hM H hHs hHnorm K hK hH hsmall
  have hC : 1 ≤ activationConstant CM CH := by
    unfold activationConstant
    nlinarith only [sq_nonneg CM, hCH]
  obtain ⟨yp, yq, hwq, hwpl, hwpu, hY⟩ :=
    select_endpoint_hilbert Λ B p q (activationConstant CM CH) ε h hΛ hp hq hpq
      hC hε hh hεsmall hΛnorm hB hBpp
  let Y := yp • p + yq • q
  let u := endpointDerivative T hT.le (fun t => m t) H K hK hH hsmall L Y
  let η := initialRealPrimitive T u
  let v := physicalVelocityPath T hT.le Q Q₁ c hc hQ H u
  let w := fun t => v t - extendPath T hT.le M t (η t)
  have hLt : ∀ Z t, ⟪m t, initialPrimitive T hT.le (L Z) t⟫_ℝ = 0 :=
    activationTrial_tangent T hT.le m m₁ hne R.toContinuousLinearMap hdm h
  have hLT : ∀ Z, initialPrimitive T hT.le (L Z) ⟨T, hT.le, le_rfl⟩ = R Z :=
    activationTrial_terminal T hT.le m m₁ hne R.toContinuousLinearMap hdm h hLayer hR
  have hηT : η T = R Y :=
    (endpointDisplacement_terminal T hT.le (fun t => m t) H K hK hH hsmall L Y).trans (hLT Y)
  have hdη : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt η (v t) (Icc (0 : ℝ) T) t :=
    endpointDisplacement_hasDerivWithinAt T hT.le Q Q₁ c hc hQ H hdQ hT
      (fun t => m t) hm hRange K hK hH hsmall L hLt Y
  have hηtan : ∀ t : Icc (0 : ℝ) T, ⟪m t, η t⟫_ℝ = 0 :=
    endpointDisplacement_tangent T hT.le (fun t => m t) H K hK hH hsmall L hLt Y
  have hvt : R.toContinuousLinearMap.adjoint (v T) = Λ Y :=
    (dirichletToNeumann_eq_terminal_velocity T hT.le Q Q₁ c hc hQ H hdQ hT
      (fun t => m t) hm hRange K hK hH hsmall L R.toContinuousLinearMap hLt hLT Y).symm
  have hwt : R.toContinuousLinearMap.adjoint (w T) =
      Λ Y - B Y - (h * ⟪p, Y⟫_ℝ) • q := by
    dsimp only [w]
    rw [map_sub, hvt, hηT]
    simp only [B, terminalPerturbation, sub_apply, comp_apply, smul_apply, rankOne_apply,
      smul_smul, extendPath, projIcc_of_mem hT.le (show T ∈ Icc (0 : ℝ) T from ⟨hT.le, le_rfl⟩)]
    abel
  have hwcoord (z : V) : ⟪w T, R z⟫_ℝ =
      ⟪Λ Y - B Y - (h * ⟪p, Y⟫_ℝ) • q, z⟫_ℝ := by
    change ⟪w T, R.toContinuousLinearMap z⟫_ℝ = _
    rw [← R.toContinuousLinearMap.adjoint_inner_left, hwt]
  refine ⟨Y, initialRealPrimitive_initial T u, hηT,
    physicalVelocityPath_continuous T hT.le Q Q₁ c hc hQ H u, hdη, ?_, ?_, ?_, ?_, hY⟩
  · intro t
    simpa only [w, extendPath, projIcc_of_mem hT.le t.property] using
      corrected_velocity_tangent T hT m m₁ M hdm hRay η v hdη hηtan t
  · exact (hwcoord q).trans hwq
  · exact (hwcoord p).symm ▸ hwpl
  · exact (hwcoord p).symm ▸ hwpu

end EulerTransverseActivationSelection
