/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanOperatorTranslation
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedSpaceInverse

@[expose] public section

/-!
# Spatial translation covariance of the actual fixed mean form

The full form, including its nonlocal initial boundary operator, transforms by
ordinary spatial translation. Consequently its coercivity persists with the
same constant throughout the translated coefficient family.
-/

noncomputable section

namespace EulerMeanFixedTranslation

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerTimeLp EulerTerminalTimePrimitive EulerTimeLpBoundedMap
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerVolterraConvolution
  EulerMeanFixedSpaceInverse

-- Reuse the nested Hilbert-space instances in the translation and adjoint identities.
private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) := inferInstance
private local instance (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) := inferInstance
private local instance (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace) := inferInstance

variable (T : ℝ) (hT : 0 ≤ T) (a : Space)
  (F F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L : ℝ)

/-- The fixed mean operator with genuinely translated spatial coefficients. -/
def translatedMeanOperator : TimeLp T solenoidalSpace →L[ℝ] TimeLp T solenoidalSpace :=
  fixedMeanOperator T hT (translatePath T a F) (translatePath T a F₁) (translatePath T a H)
    (translateOperator a M0) (translateOperator a A) L

/-- The physical primitive map with genuinely translated coefficients. -/
def translatedMeanPrimitive : TimeLp T solenoidalSpace →L[ℝ] TimeLp T L2 :=
  fixedMeanPrimitive T hT (translatePath T a F) (translatePath T a F₁)

/-- Covariance of the actual physical derivative. -/
theorem fixedMeanDerivative_translate (u : TimeLp T solenoidalSpace) :
    fixedMeanDerivative T hT (translatePath T a F) (translatePath T a F₁)
      (timeSolenoidalTranslation T a u) = timeTranslation T a (fixedMeanDerivative T hT F F₁ u) :=
  frameDerivative_translate T hT a F F₁ u

/-- Covariance of the actual physical primitive. -/
theorem fixedMeanPrimitive_translate (u : TimeLp T solenoidalSpace) :
    translatedMeanPrimitive T hT a F F₁ (timeSolenoidalTranslation T a u) =
      timeTranslation T a (fixedMeanPrimitive T hT F F₁ u) :=
  (congrArg (primitiveTimeLp T hT) (fixedMeanDerivative_translate T hT a F F₁ u)).trans
    (timeTranslation_primitiveTimeLp T hT a (fixedMeanDerivative T hT F F₁ u))

/-- Covariance includes the actual initial trace. -/
theorem fixedMeanTrace_translate (u : TimeLp T solenoidalSpace) :
    fixedMeanTrace T hT (translatePath T a F) (translatePath T a F₁)
      (timeSolenoidalTranslation T a u) = translation a (fixedMeanTrace T hT F F₁ u) :=
  (congrArg (initialTrace T hT) (fixedMeanDerivative_translate T hT a F F₁ u)).trans
    (timeTranslation_initialTrace T hT a (fixedMeanDerivative T hT F F₁ u))

/-- The two actual initial boundary terms transform together. -/
theorem boundaryCoefficient_translate (u : L2) :
    (translateOperator a M0 + L • translateOperator a A) (translation a u) =
      translation a ((M0+L • A) u) := by
  simp only [add_apply, smul_apply, translateOperator_translation, map_add, map_smul]

/-- The whole physical bilinear form is invariant under simultaneous translation. -/
theorem fixedMeanForm_translate (u v : TimeLp T solenoidalSpace) :
    ⟪translatedMeanOperator T hT a F F₁ H M0 A L (timeSolenoidalTranslation T a u),
      timeSolenoidalTranslation T a v⟫_ℝ = ⟪fixedMeanOperator T hT F F₁ H M0 A L u, v⟫_ℝ := by
  have hD (z) := fixedMeanDerivative_translate T hT a F F₁ z
  have hJ (z) := fixedMeanPrimitive_translate T hT a F F₁ z
  have hR (z) := fixedMeanTrace_translate T hT a F F₁ z
  have hkin := (congrArg₂ (fun x y : TimeLp T L2 => ⟪x,y⟫_ℝ) (hD u) (hD v)).trans
    ((timeTranslation T a).inner_map_map (fixedMeanDerivative T hT F F₁ u) (fixedMeanDerivative T
      hT F F₁ v))
  have hHJ := (congrArg (timeMultiplier T hT (translatePath T a H)) (hJ u)).trans
    (timeMultiplier_translate T hT a H (fixedMeanPrimitive T hT F F₁ u))
  have hpot := (congrArg₂ (fun x y : TimeLp T L2 => ⟪x,y⟫_ℝ) hHJ (hJ v)).trans
    ((timeTranslation T a).inner_map_map
      (timeMultiplier T hT H (fixedMeanPrimitive T hT F F₁ u)) (fixedMeanPrimitive T hT F F₁ v))
  have hCR := (congrArg (translateOperator a M0+L • translateOperator a A) (hR u)).trans
    (boundaryCoefficient_translate a M0 A L (fixedMeanTrace T hT F F₁ u))
  have hboundary := (congrArg₂ (fun x y : L2 => ⟪x,y⟫_ℝ) hCR (hR v)).trans
    ((translation a).inner_map_map ((M0+L • A) (fixedMeanTrace T hT F F₁ u)) (fixedMeanTrace T hT F
      F₁ v))
  exact (fixedMeanOperator_inner T hT (translatePath T a F) (translatePath T a F₁)
      (translatePath T a H) (translateOperator a M0) (translateOperator a A) L
      (timeSolenoidalTranslation T a u) (timeSolenoidalTranslation T a v)).trans
    ((congrArg₂ (fun x y : ℝ => x+y) (congrArg₂ (fun x y : ℝ => x-y) hkin hpot) hboundary).trans
      (fixedMeanOperator_inner T hT F F₁ H M0 A L u v).symm)

private theorem timeSolenoidalTranslation_neg_cancel (v : TimeLp T solenoidalSpace) :
    timeSolenoidalTranslation T a (timeSolenoidalTranslation T (-a) v) = v :=
  (timeSolenoidalTranslation_add T a (-a) v).trans
    ((congrArg (fun b : Space => timeSolenoidalTranslation T b v) (add_neg_cancel a)).trans
      (timeSolenoidalTranslation_zero T v))

/-- Testing after every spatial translation still determines a Hilbert vector. -/
theorem eq_of_translated_pairing (x y : TimeLp T solenoidalSpace)
    (h : ∀ v, ⟪x, timeSolenoidalTranslation T a v⟫_ℝ = ⟪y, timeSolenoidalTranslation T a v⟫_ℝ) :
    x = y := by
  apply ext_inner_right ℝ
  intro v
  have hv := timeSolenoidalTranslation_neg_cancel T a v
  exact (congrArg (fun w : TimeLp T solenoidalSpace => ⟪x,w⟫_ℝ) hv).symm.trans
    ((h (timeSolenoidalTranslation T (-a) v)).trans
      (congrArg (fun w : TimeLp T solenoidalSpace => ⟪y,w⟫_ℝ) hv))

/-- Covariance is an equality of the actual fixed-space bounded operators. -/
theorem fixedMeanOperator_translate (u : TimeLp T solenoidalSpace) :
    translatedMeanOperator T hT a F F₁ H M0 A L (timeSolenoidalTranslation T a u) =
      timeSolenoidalTranslation T a (fixedMeanOperator T hT F F₁ H M0 A L u) := by
  apply eq_of_translated_pairing T a
  intro v
  exact (fixedMeanForm_translate T hT a F F₁ H M0 A L u v).trans
    ((timeSolenoidalTranslation T a).inner_map_map (fixedMeanOperator T hT F F₁ H M0 A L u) v).symm

/-- The same positive coercivity constant holds for all genuinely translated coefficients. -/
theorem translatedMeanOperator_coercive (c : ℝ)
    (hcoercive : ∀ v, c*‖v‖^2 ≤ ⟪fixedMeanOperator T hT F F₁ H M0 A L v,v⟫_ℝ)
    (v : TimeLp T solenoidalSpace) :
    c*‖v‖^2 ≤ ⟪translatedMeanOperator T hT a F F₁ H M0 A L v,v⟫_ℝ := by
  have h := hcoercive (timeSolenoidalTranslation T (-a) v)
  have heq := fixedMeanForm_translate T hT a F F₁ H M0 A L
    (timeSolenoidalTranslation T (-a) v) (timeSolenoidalTranslation T (-a) v)
  have hpair := congrArg (fun w : TimeLp T solenoidalSpace =>
    ⟪translatedMeanOperator T hT a F F₁ H M0 A L w,w⟫_ℝ)
    (timeSolenoidalTranslation_neg_cancel T a v)
  have hnorm := congrArg (fun r : ℝ => c*r^2) ((timeSolenoidalTranslation T (-a)).norm_map v)
  exact hnorm.symm.trans_le (h.trans_eq (heq.symm.trans hpair))

/-- The forcing adjoint transforms by the same actual spatial action. -/
theorem fixedMeanPrimitive_adjoint_translate (f : TimeLp T L2) :
    (translatedMeanPrimitive T hT a F F₁).adjoint (timeTranslation T a f) =
      timeSolenoidalTranslation T a ((fixedMeanPrimitive T hT F F₁).adjoint f) := by
  apply eq_of_translated_pairing T a
  intro v
  exact (adjoint_inner_left (translatedMeanPrimitive T hT a F F₁)
      (timeSolenoidalTranslation T a v) (timeTranslation T a f)).trans
    ((congrArg (fun z : TimeLp T L2 => ⟪timeTranslation T a f,z⟫_ℝ)
        (fixedMeanPrimitive_translate T hT a F F₁ v)).trans
      (((timeTranslation T a).inner_map_map f (fixedMeanPrimitive T hT F F₁ v)).trans
        ((adjoint_inner_left (fixedMeanPrimitive T hT F F₁) v f).symm.trans
          ((timeSolenoidalTranslation T a).inner_map_map ((fixedMeanPrimitive T hT F F₁).adjoint f)
            v).symm)))

end EulerMeanFixedTranslation
