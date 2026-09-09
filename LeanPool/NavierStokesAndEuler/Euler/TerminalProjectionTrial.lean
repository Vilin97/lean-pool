/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TerminalLayerRamp
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1PointwiseBounds
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1OperatorProduct

@[expose] public section

/-!
An explicit terminal-layer H¹ trial obtained by multiplying a differentiable
projection path by the smooth exponential ramp.  Both energy estimates concern
the actual Bochner L² derivative and primitive.
-/

noncomputable section


namespace EulerTerminalProjectionTrial

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerTimeH1OperatorProduct EulerTimeH1PointwiseBounds EulerVolterraConvolution
  EulerTerminalLayerRamp

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

private local instance : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
private local instance : AddCommGroup (U →L[ℝ] E) :=
  (inferInstance : NormedAddCommGroup (U →L[ℝ] E)).toAddCommGroup
private local instance : Module ℝ (U →L[ℝ] E) :=
  (inferInstance : NormedSpace ℝ (U →L[ℝ] E)).toModule
private local instance : TopologicalSpace (U →L[ℝ] E) :=
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

def trialFrame : C(Icc (0 : ℝ) T, U →L[ℝ] E) :=
  ⟨fun t => ramp T L t • P t,
    ((ramp_continuous T L).comp continuous_subtype_val).smul P.continuous⟩

def trialFrameDerivative : C(Icc (0 : ℝ) T, U →L[ℝ] E) :=
  ⟨fun t => rampDerivative T L t • P t + ramp T L t • P₁ t,
    (((rampDerivative_continuous T L).comp continuous_subtype_val).smul P.continuous).add
      (((ramp_continuous T L).comp continuous_subtype_val).smul P₁.continuous)⟩

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
