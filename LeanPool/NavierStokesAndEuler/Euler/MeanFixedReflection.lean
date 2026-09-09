/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanOperatorReflection
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedSpaceInverse

/-!
# Reflection covariance of the full mean variational inverse

Every identity concerns the real time derivative, terminal primitive, initial
trace, and nonlocal boundary form. Uniqueness of the actual coercive inverse
then transports reflection without an assumed symmetry of a solution.
-/

@[expose] public section


noncomputable section

namespace EulerMeanFixedReflection

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerMeanSolenoidal
  EulerTimeLp EulerTerminalTimePrimitive EulerMeanTimeReflection EulerVolterraConvolution
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerTimeH1OperatorProduct
  EulerCoerciveProjection

/-- Cache the standard `NormedAddCommGroup L2` instance to shorten typeclass synthesis. -/
local instance instMeanFixedReflection1 : NormedAddCommGroup L2 := inferInstance
/-- Cache the standard `InnerProductSpace ℝ L2` instance to shorten typeclass synthesis. -/
local instance instMeanFixedReflection2 : InnerProductSpace ℝ L2 := inferInstance
/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedReflection3 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedReflection4 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedReflection5 (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedReflection6 (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) := inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedReflection7 (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedReflection8 (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace) :=
    inferInstance

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L : ℝ)
  (hF : ∀ t, ReflectionInvariant (F t)) (hF₁ : ∀ t, ReflectionInvariant (F₁ t))
  (hH : ∀ t, ReflectionInvariant (H t)) (hM0 : ReflectionInvariant M0) (hA : ReflectionInvariant A)

include hF hF₁ in
theorem fixedMeanDerivative_reflection (u : TimeLp T solenoidalSpace) :
    fixedMeanDerivative T hT F F₁ (timeSolenoidalReflection T u) =
      timeReflection T (fixedMeanDerivative T hT F F₁ u) := by
  change timeMultiplier T hT (solenoidalFrame T F₁)
      (primitiveTimeLp T hT (timeSolenoidalReflection T u)) +
    timeMultiplier T hT (solenoidalFrame T F) (timeSolenoidalReflection T u) = _
  have h₁ := (congrArg (timeMultiplier T hT (solenoidalFrame T F₁))
    (timeSolenoidalReflection_primitiveTimeLp T hT u)).trans
    (frameMultiplier_reflection T hT F₁ hF₁ (primitiveTimeLp T hT u))
  exact (congrArg₂ (fun x y : TimeLp T L2 => x+y) h₁
    (frameMultiplier_reflection T hT F hF u)).trans ((timeReflection T).map_add _ _).symm

include hF hF₁ in
theorem fixedMeanPrimitive_reflection (u : TimeLp T solenoidalSpace) :
    fixedMeanPrimitive T hT F F₁ (timeSolenoidalReflection T u) =
      timeReflection T (fixedMeanPrimitive T hT F F₁ u) :=
  (congrArg (primitiveTimeLp T hT) (fixedMeanDerivative_reflection T hT F F₁ hF hF₁ u)).trans
    (timeReflection_primitiveTimeLp T hT (fixedMeanDerivative T hT F F₁ u))

include hF hF₁ in
theorem fixedMeanTrace_reflection (u : TimeLp T solenoidalSpace) :
    fixedMeanTrace T hT F F₁ (timeSolenoidalReflection T u) =
      reflection (fixedMeanTrace T hT F F₁ u) :=
  (congrArg (initialTrace T hT) (fixedMeanDerivative_reflection T hT F F₁ hF hF₁ u)).trans
    (timeReflection_initialTrace T hT (fixedMeanDerivative T hT F F₁ u))

include hM0 hA in
theorem boundaryCoefficient_reflection (u : L2) :
    (M0+L • A) (reflection u) = reflection ((M0+L • A) u) := by
  simp only [add_apply, smul_apply, hM0 u, hA u, map_add, map_smul]

include hF hF₁ hH hM0 hA in
theorem fixedMeanForm_reflection (u v : TimeLp T solenoidalSpace) :
    ⟪fixedMeanOperator T hT F F₁ H M0 A L (timeSolenoidalReflection T u),
      timeSolenoidalReflection T v⟫_ℝ = ⟪fixedMeanOperator T hT F F₁ H M0 A L u,v⟫_ℝ := by
  have hD (z) := fixedMeanDerivative_reflection T hT F F₁ hF hF₁ z
  have hJ (z) := fixedMeanPrimitive_reflection T hT F F₁ hF hF₁ z
  have hR (z) := fixedMeanTrace_reflection T hT F F₁ hF hF₁ z
  have hkin := (congrArg₂ (fun x y : TimeLp T L2 => ⟪x,y⟫_ℝ) (hD u) (hD v)).trans
    ((timeReflection T).inner_map_map _ _)
  have hHJ := (congrArg (timeMultiplier T hT H) (hJ u)).trans
    (timeMultiplier_reflection T hT H hH (fixedMeanPrimitive T hT F F₁ u))
  have hpot := (congrArg₂ (fun x y : TimeLp T L2 => ⟪x,y⟫_ℝ) hHJ (hJ v)).trans
    ((timeReflection T).inner_map_map _ _)
  have hCR := (congrArg (M0+L • A) (hR u)).trans
    (boundaryCoefficient_reflection M0 A L hM0 hA (fixedMeanTrace T hT F F₁ u))
  have hb := (congrArg₂ (fun x y : L2 => ⟪x,y⟫_ℝ) hCR (hR v)).trans
    (reflection.inner_map_map _ _)
  exact (fixedMeanOperator_inner T hT F F₁ H M0 A L _ _).trans
    ((congrArg₂ (fun x y : ℝ => x+y) (congrArg₂ (fun x y : ℝ => x-y) hkin hpot) hb).trans
      (fixedMeanOperator_inner T hT F F₁ H M0 A L u v).symm)

theorem eq_of_reflected_pairing (x y : TimeLp T solenoidalSpace)
    (h : ∀ v, ⟪x, timeSolenoidalReflection T v⟫_ℝ = ⟪y, timeSolenoidalReflection T v⟫_ℝ) : x = y :=
        by
  apply ext_inner_right ℝ
  intro v
  have hi := timeSolenoidalReflection_involutive T v
  exact (congrArg (fun z : TimeLp T solenoidalSpace => ⟪x,z⟫_ℝ) hi).symm.trans
    ((h (timeSolenoidalReflection T v)).trans
      (congrArg (fun z : TimeLp T solenoidalSpace => ⟪y,z⟫_ℝ) hi))

include hF hF₁ hH hM0 hA in
theorem fixedMeanOperator_reflection (u : TimeLp T solenoidalSpace) :
    fixedMeanOperator T hT F F₁ H M0 A L (timeSolenoidalReflection T u) =
      timeSolenoidalReflection T (fixedMeanOperator T hT F F₁ H M0 A L u) := by
  apply eq_of_reflected_pairing T
  intro v
  exact (fixedMeanForm_reflection T hT F F₁ H M0 A L hF hF₁ hH hM0 hA u v).trans
    ((timeSolenoidalReflection T).inner_map_map _ _).symm

include hF hF₁ in
theorem fixedMeanPrimitive_adjoint_reflection (f : TimeLp T L2) :
    (fixedMeanPrimitive T hT F F₁).adjoint (timeReflection T f) =
      timeSolenoidalReflection T ((fixedMeanPrimitive T hT F F₁).adjoint f) := by
  apply eq_of_reflected_pairing T
  intro v
  exact (adjoint_inner_left (fixedMeanPrimitive T hT F F₁)
      (timeSolenoidalReflection T v) (timeReflection T f)).trans
    ((congrArg (fun z : TimeLp T L2 => ⟪timeReflection T f,z⟫_ℝ)
      (fixedMeanPrimitive_reflection T hT F F₁ hF hF₁ v)).trans
      (((timeReflection T).inner_map_map f (fixedMeanPrimitive T hT F F₁ v)).trans
        ((adjoint_inner_left (fixedMeanPrimitive T hT F F₁) v f).symm.trans
          ((timeSolenoidalReflection T).inner_map_map ((fixedMeanPrimitive T hT F F₁).adjoint f)
              v).symm)))

include hF hF₁ hH hM0 hA in
/-- Uniqueness of the actual coercive solve forces reflection covariance. -/
theorem coerciveSolution_reflection (c : ℝ) (hc : 0 < c)
    (hO : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪fixedMeanOperator T hT F F₁ H M0 A L v, v⟫_ℝ)
    (f : TimeLp T L2) :
    timeSolenoidalReflection T
      (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hO
        (-(fixedMeanPrimitive T hT F F₁).adjoint f)) =
    coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hO
      (-(fixedMeanPrimitive T hT F F₁).adjoint (timeReflection T f)) := by
  apply (coerciveEquiv (fixedMeanOperator T hT F F₁ H M0 A L) c hc hO).injective
  simp only [coerciveEquiv_apply]
  change fixedMeanOperator T hT F F₁ H M0 A L (timeSolenoidalReflection T
    (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hO
      (-(fixedMeanPrimitive T hT F F₁).adjoint f))) =
    fixedMeanOperator T hT F F₁ H M0 A L
      (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hO
        (-(fixedMeanPrimitive T hT F F₁).adjoint (timeReflection T f)))
  exact (fixedMeanOperator_reflection T hT F F₁ H M0 A L hF hF₁ hH hM0 hA _).trans
    ((congrArg (timeSolenoidalReflection T)
      (operator_inverse_apply (fixedMeanOperator T hT F F₁ H M0 A L) c hc hO _)).trans
      (((timeSolenoidalReflection T).map_neg _).trans
        ((congrArg Neg.neg (fixedMeanPrimitive_adjoint_reflection T hT F F₁ hF hF₁ f).symm).trans
          (operator_inverse_apply (fixedMeanOperator T hT F F₁ H M0 A L) c hc hO _).symm)))

end EulerMeanFixedReflection
