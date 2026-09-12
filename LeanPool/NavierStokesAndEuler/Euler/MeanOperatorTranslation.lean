/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeTranslation
public import LeanPool.NavierStokesAndEuler.Euler.MeanDisplacementRegularity

/-!
# Actual translated coefficient operators for the mean equation

The translated operator is literal conjugation by spatial translation on
ordinary L². Its Bochner multiplier and H¹ frame derivative obey exact
covariance, including the terminal primitive and initial trace.
-/

@[expose] public section


noncomputable section

namespace EulerMeanOperatorTranslation

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerTimeLp EulerTerminalTimePrimitive EulerTimeLpBoundedMap
  EulerMeanTimeTranslation EulerVolterraConvolution EulerMeanVariationalInverse
  EulerTimeH1OperatorProduct

/-- Literal spatial conjugation of a bounded operator on ordinary L². -/
def translateOperator (a : Space) (A : L2 →L[ℝ] L2) : L2 →L[ℝ] L2 :=
  (translation a).toContinuousLinearMap.comp
    (A.comp (translation (-a)).toContinuousLinearMap)

@[simp] theorem translateOperator_apply (a : Space) (A : L2 →L[ℝ] L2) (u : L2) :
    translateOperator a A u = translation a (A (translation (-a) u)) := rfl

/-- Applying the translated coefficient to the translated field is exact covariance. -/
theorem translateOperator_translation (a : Space) (A : L2 →L[ℝ] L2) (u : L2) :
    translateOperator a A (translation a u) = translation a (A u) := by
  simp only [translateOperator_apply, translation_add, neg_add_cancel, translation_zero]

@[simp] theorem translateOperator_zero (A : L2 →L[ℝ] L2) : translateOperator 0 A = A := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [translateOperator_apply, neg_zero, translation_zero]

theorem translateOperator_add (a : Space) (A B : L2 →L[ℝ] L2) :
    translateOperator a (A+B) = translateOperator a A + translateOperator a B := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [translateOperator_apply, add_apply, map_add]

theorem translateOperator_smul (a : Space) (c : ℝ) (A : L2 →L[ℝ] L2) :
    translateOperator a (c • A) = c • translateOperator a A := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [translateOperator_apply, smul_apply, map_smul]

theorem translateOperator_neg_cancel (a : Space) (A : L2 →L[ℝ] L2) :
    translateOperator (-a) (translateOperator a A) = A := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [translateOperator_apply, neg_neg, translation_add, neg_add_cancel, translation_zero]

theorem translateOperator_norm_le (a : Space) (A : L2 →L[ℝ] L2) :
    ‖translateOperator a A‖ ≤ ‖A‖ := by
  apply opNorm_le_bound _ (norm_nonneg _)
  intro u
  calc
    ‖translateOperator a A u‖ = ‖A (translation (-a) u)‖ := (translation a).norm_map _
    _ ≤ ‖A‖*‖translation (-a) u‖ := A.le_opNorm _
    _ = ‖A‖*‖u‖ := by rw [(translation (-a)).norm_map]

theorem translateOperator_norm (a : Space) (A : L2 →L[ℝ] L2) :
    ‖translateOperator a A‖ = ‖A‖ := by
  apply le_antisymm (translateOperator_norm_le a A)
  have h := translateOperator_norm_le (-a) (translateOperator a A)
  simpa only [translateOperator_neg_cancel] using h

/-- Translate the spatial operator at every time in the coefficient path. -/
def translatePath (T : ℝ) (a : Space) (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) :
    C(Icc (0 : ℝ) T, L2 →L[ℝ] L2) :=
  ⟨fun t => translateOperator a (F t),
    continuous_const.clm_comp (F.continuous.clm_comp continuous_const)⟩

@[simp] theorem translatePath_apply (T : ℝ) (a : Space)
    (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (t : Icc (0 : ℝ) T) :
    translatePath T a F t = translateOperator a (F t) := rfl

theorem translatePath_norm_le (T : ℝ) (a : Space)
    (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) : ‖translatePath T a F‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le (translatePath T a F) (norm_nonneg F)).2
  intro t
  exact (translateOperator_norm_le a (F t)).trans (F.norm_coe_le_norm t)

/-- Translation commutes with the genuine time multiplier. -/
theorem timeMultiplier_translate (T : ℝ) (hT : 0 ≤ T) (a : Space)
    (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : TimeLp T L2) :
    timeMultiplier T hT (translatePath T a F) (timeTranslation T a u) =
      timeTranslation T a (timeMultiplier T hT F u) := by
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT (translatePath T a F) (timeTranslation T a u),
    timeTranslation_ae T a u, timeTranslation_ae T a (timeMultiplier T hT F u),
    timeMultiplier_ae T hT F u] with t ht hu hτ hF
  exact (ht.trans (congrArg (translateOperator a (F (projIcc 0 T hT t))) hu)).trans
    ((translateOperator_translation a (F (projIcc 0 T hT t)) (u t)).trans
      ((congrArg (translation a) hF).symm.trans hτ.symm))

/-- The actual solenoidal frame multiplier has the corresponding covariance. -/
theorem frameMultiplier_translate (T : ℝ) (hT : 0 ≤ T) (a : Space)
    (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : TimeLp T solenoidalSpace) :
    timeMultiplier T hT (solenoidalFrame T (translatePath T a F))
        (timeSolenoidalTranslation T a u) =
      timeTranslation T a (timeMultiplier T hT (solenoidalFrame T F) u) := by
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT (solenoidalFrame T (translatePath T a F))
      (timeSolenoidalTranslation T a u), timeSolenoidalTranslation_ae T a u,
    timeTranslation_ae T a (timeMultiplier T hT (solenoidalFrame T F) u),
    timeMultiplier_ae T hT (solenoidalFrame T F) u] with t ht hu hτ hF
  have hu' := congrArg (fun z : solenoidalSpace => (z : L2)) hu
  change (timeSolenoidalTranslation T a u t : L2) = translation a (u t : L2) at hu'
  exact (ht.trans (congrArg (translateOperator a (F (projIcc 0 T hT t))) hu')).trans
    ((translateOperator_translation a (F (projIcc 0 T hT t)) (u t : L2)).trans
      ((congrArg (translation a) hF).symm.trans hτ.symm))

/-- The genuine H¹ product derivative commutes with translated coefficients. -/
theorem frameDerivative_translate (T : ℝ) (hT : 0 ≤ T) (a : Space)
    (F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (u : TimeLp T solenoidalSpace) :
    productDerivative T hT (solenoidalFrame T (translatePath T a F))
        (solenoidalFrame T (translatePath T a F₁)) (timeSolenoidalTranslation T a u) =
      timeTranslation T a
        (productDerivative T hT (solenoidalFrame T F) (solenoidalFrame T F₁) u) := by
  change timeMultiplier T hT (solenoidalFrame T (translatePath T a F₁))
      (primitiveTimeLp T hT (timeSolenoidalTranslation T a u)) +
    timeMultiplier T hT (solenoidalFrame T (translatePath T a F)) (timeSolenoidalTranslation T a u)
        = _
  have h₁ := (congrArg (timeMultiplier T hT (solenoidalFrame T (translatePath T a F₁)))
    (timeSolenoidalTranslation_primitiveTimeLp T hT a u)).trans
    (frameMultiplier_translate T hT a F₁ (primitiveTimeLp T hT u))
  exact (congrArg₂ (fun x y : TimeLp T L2 => x+y) h₁ (frameMultiplier_translate T hT a F u)).trans
    ((timeTranslation T a).map_add _ _).symm

end EulerMeanOperatorTranslation
