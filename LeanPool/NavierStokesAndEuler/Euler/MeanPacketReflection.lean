/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceFixedInverse
import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryReflection
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider
import LeanPool.NavierStokesAndEuler.Euler.MeanSourceSpatialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedSpaceInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanDisplacementRegularity
public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalReflection
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap

/-!
# Actual reflection symmetry of the mean packet solve

Even source matrices and an odd forcing commute through the complete mean
form, including its localized initial boundary operator. The odd coordinate
velocity follows from uniqueness of the constructed inverse.
-/

section

/-!
# Reflection covariance of the full mean variational inverse

Every identity concerns the real time derivative, terminal primitive, initial
trace, and nonlocal boundary form. Uniqueness of the actual coercive inverse
then transports reflection without an assumed symmetry of a solution.
-/

section

/-! Genuine spatial reflection on the mean time Hilbert spaces. -/

@[expose] public section

noncomputable section

namespace EulerMeanTimeReflection

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerMeanSolenoidal
  EulerTimeLp EulerTerminalTimePrimitive EulerTimeLpBoundedMap

/-- Reflection restricted to the actual ordinary solenoidal subspace. -/
def solenoidalReflection : solenoidalSpace →ₗᵢ[ℝ] solenoidalSpace where
  toLinearMap := (reflection.toLinearMap.comp solenoidalSpace.subtype).codRestrict
    solenoidalSpace (fun u => reflection_solenoidal_mem u.property)
  norm_map' := fun u => reflection.norm_map (u : L2)

@[simp] theorem solenoidalReflection_coe (u : solenoidalSpace) :
    (solenoidalReflection u : L2) = reflection (u : L2) := rfl

@[simp] theorem solenoidalReflection_involutive (u : solenoidalSpace) :
    solenoidalReflection (solenoidalReflection u) = u :=
  Subtype.ext (reflection_involutive (u : L2))

/-- Time reflection, given by `timeLiftIsometry T reflection`. -/
def timeReflection (T : ℝ) : TimeLp T L2 →ₗᵢ[ℝ] TimeLp T L2 :=
  timeLiftIsometry T reflection

/-- Time solenoidal reflection, given by `timeLiftIsometry T solenoidalReflection`. -/
def timeSolenoidalReflection (T : ℝ) :
    TimeLp T solenoidalSpace →ₗᵢ[ℝ] TimeLp T solenoidalSpace :=
  timeLiftIsometry T solenoidalReflection

theorem timeReflection_ae (T : ℝ) (u : TimeLp T L2) :
    timeReflection T u =ᵐ[timeMeasure T] fun t => reflection (u t) :=
  timeLift_ae T reflection.toContinuousLinearMap u

theorem timeSolenoidalReflection_ae (T : ℝ) (u : TimeLp T solenoidalSpace) :
    timeSolenoidalReflection T u =ᵐ[timeMeasure T] fun t => solenoidalReflection (u t) :=
  timeLift_ae T solenoidalReflection.toContinuousLinearMap u

@[simp] theorem timeReflection_involutive (T : ℝ) (u : TimeLp T L2) :
    timeReflection T (timeReflection T u) = u := by
  apply Lp.ext
  filter_upwards [timeReflection_ae T (timeReflection T u), timeReflection_ae T u] with t h₁ h₂
  exact h₁.trans ((congrArg reflection h₂).trans (reflection_involutive (u t)))

@[simp] theorem timeSolenoidalReflection_involutive (T : ℝ) (u : TimeLp T solenoidalSpace) :
    timeSolenoidalReflection T (timeSolenoidalReflection T u) = u := by
  apply Lp.ext
  filter_upwards [timeSolenoidalReflection_ae T (timeSolenoidalReflection T u),
    timeSolenoidalReflection_ae T u] with t h₁ h₂
  exact h₁.trans ((congrArg solenoidalReflection h₂).trans (solenoidalReflection_involutive (u t)))

theorem timeReflection_inner_shift (T : ℝ) (u v : TimeLp T L2) :
    ⟪timeReflection T u,v⟫_ℝ = ⟪u,timeReflection T v⟫_ℝ :=
  (congrArg (fun z : TimeLp T L2 => ⟪timeReflection T u,z⟫_ℝ)
    (timeReflection_involutive T v)).symm.trans
      ((timeReflection T).inner_map_map u (timeReflection T v))

theorem timeSolenoidalReflection_inner_shift (T : ℝ) (u v : TimeLp T solenoidalSpace) :
    ⟪timeSolenoidalReflection T u,v⟫_ℝ = ⟪u,timeSolenoidalReflection T v⟫_ℝ := by
  have h := LinearIsometry.inner_map_map (𝕜 := ℝ)
    (E := TimeLp T solenoidalSpace) (E' := TimeLp T solenoidalSpace)
    (timeSolenoidalReflection T) u (timeSolenoidalReflection T v)
  simpa only [timeSolenoidalReflection_involutive] using h

theorem timeReflection_realPrimitive (T : ℝ) (u : TimeLp T L2) (t : ℝ) :
    realPrimitive T (timeReflection T u) t = reflection (realPrimitive T u t) :=
  realPrimitive_timeLift T reflection.toContinuousLinearMap u t

theorem timeSolenoidalReflection_realPrimitive (T : ℝ) (u : TimeLp T solenoidalSpace) (t : ℝ) :
    realPrimitive T (timeSolenoidalReflection T u) t = solenoidalReflection (realPrimitive T u t) :=
  realPrimitive_timeLift T solenoidalReflection.toContinuousLinearMap u t

theorem timeReflection_initialTrace (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T L2) :
    initialTrace T hT (timeReflection T u) = reflection (initialTrace T hT u) :=
  initialTrace_timeLift T hT reflection.toContinuousLinearMap u

theorem timeReflection_primitiveTimeLp (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T L2) :
    primitiveTimeLp T hT (timeReflection T u) = timeReflection T (primitiveTimeLp T hT u) :=
  primitiveTimeLp_timeLift T hT reflection.toContinuousLinearMap u

theorem timeSolenoidalReflection_primitiveTimeLp (T : ℝ) (hT : 0 ≤ T)
    (u : TimeLp T solenoidalSpace) :
    primitiveTimeLp T hT (timeSolenoidalReflection T u) =
      timeSolenoidalReflection T (primitiveTimeLp T hT u) :=
  primitiveTimeLp_timeLift T hT solenoidalReflection.toContinuousLinearMap u

end EulerMeanTimeReflection

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanFixedReflection

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerMeanSolenoidal
  EulerTimeLp EulerTerminalTimePrimitive EulerMeanTimeReflection EulerVolterraConvolution
  EulerMeanVariationalInverse  EulerTimeH1OperatorProduct
  EulerCoerciveProjection

/-- Cache the standard `NormedAddCommGroup L2` instance to shorten typeclass synthesis. -/
local instance instMeanOperatorReflection1 : NormedAddCommGroup L2 := inferInstance
/-- Cache the standard `InnerProductSpace ℝ L2` instance to shorten typeclass synthesis. -/
local instance instMeanOperatorReflection2 : InnerProductSpace ℝ L2 := inferInstance
/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanOperatorReflection3 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanOperatorReflection4 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanOperatorReflection5 (T : ℝ) : NormedAddCommGroup (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanOperatorReflection6 (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanOperatorReflection7 (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace)
    := inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanOperatorReflection8 (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace)
    := inferInstance

/-- Reflection invariant, given by `∀ u, A (reflection u) = reflection (A u)`. -/
def ReflectionInvariant (A : L2 →L[ℝ] L2) : Prop :=
  ∀ u, A (reflection u) = reflection (A u)

theorem timeMultiplier_reflection (T : ℝ) (hT : 0 ≤ T)
    (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (hF : ∀ t, ReflectionInvariant (F t))
    (u : TimeLp T L2) :
    timeMultiplier T hT F (timeReflection T u) = timeReflection T (timeMultiplier T hT F u) := by
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT F (timeReflection T u), timeReflection_ae T u,
    timeReflection_ae T (timeMultiplier T hT F u), timeMultiplier_ae T hT F u]
    with t h₁ h₂ h₃ h₄
  exact (h₁.trans (congrArg (F (projIcc 0 T hT t)) h₂)).trans
    ((hF (projIcc 0 T hT t) (u t)).trans ((congrArg reflection h₄).symm.trans h₃.symm))

theorem frameMultiplier_reflection (T : ℝ) (hT : 0 ≤ T)
    (F : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (hF : ∀ t, ReflectionInvariant (F t))
    (u : TimeLp T solenoidalSpace) :
    timeMultiplier T hT (solenoidalFrame T F) (timeSolenoidalReflection T u) =
      timeReflection T (timeMultiplier T hT (solenoidalFrame T F) u) := by
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT (solenoidalFrame T F) (timeSolenoidalReflection T u),
    timeSolenoidalReflection_ae T u,
    timeReflection_ae T (timeMultiplier T hT (solenoidalFrame T F) u),
    timeMultiplier_ae T hT (solenoidalFrame T F) u] with t h₁ h₂ h₃ h₄
  have h₂' := congrArg (fun z : solenoidalSpace => (z : L2)) h₂
  change (timeSolenoidalReflection T u t : L2) = reflection (u t : L2) at h₂'
  exact (h₁.trans (congrArg (F (projIcc 0 T hT t)) h₂')).trans
    ((hF (projIcc 0 T hT t) (u t : L2)).trans ((congrArg reflection h₄).symm.trans h₃.symm))

end EulerMeanFixedReflection

end
end

end

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic
  EulerMeanSourceInverse EulerMeanVariationalInverse EulerMeanSourceFixedInverse
  EulerMeanFixedSpaceInverse EulerMeanFixedReflection EulerMeanTimeReflection
  EulerMeanScalarPressure EulerTimeLp EulerVolterraConvolution EulerCoerciveProjection
  EulerPacketProfileRecursion
open scoped NNReal ContDiff

/-- These are literal parity assumptions on the prescribed source coefficients. -/
structure EvenData (D : Data) : Prop where
  frame : ∀ t x, D.F.field t (-x) = D.F.field t x
  frameDerivative : ∀ t x, D.F₁.field t (-x) = D.F₁.field t x
  curvature : ∀ t x, D.H.field t (-x) = D.H.field t x
  initialStrain : ∀ x, D.M0.field (-x) = D.M0.field x
  strain : ∀ t x, D.M.field t (-x) = D.M.field t x

/-- Actual pointwise multiplication by an even matrix field commutes with reflection. -/
theorem multiplier_reflection_of_even (A : Field) (hA : ∀ x, A (-x) = A x) :
    ReflectionInvariant (multiplier A) := by
  intro u
  apply Lp.ext
  filter_upwards [multiplier_ae A (reflection u), reflection_ae u,
    reflection_ae (multiplier A u),
    measurePreserving_reflection.quasiMeasurePreserving.ae (multiplier_ae A u)] with x hm hr hmr hrm
  rw [hm, hr, hmr, hrm, hA x]

namespace Data

variable (D : Data)

/-- The actual source coordinate solve as a bounded linear operator. -/
def coordinateSolver : TimeLp D.T L2 →L[ℝ] TimeLp D.T solenoidalSpace :=
  sourceCoordinateSolver D.T D.T_pos.le D.ℓ D.ℓ_pos D.F D.F₁ D.H D.M0 D.opInv
    D.Be D.Bc D.L D.r D.Be_nonneg D.Bc_nonneg D.L_lower D.r_nonneg D.r_le_quarter
    D.exterior_lower D.core_lower D.opInv_left D.opF_time D.K D.K_nonneg D.opInv_initial
    D.curvature_upper D.small

theorem coordinateSolver_reflection (hD : EvenData D) (f : TimeLp D.T L2) :
    timeSolenoidalReflection D.T (D.coordinateSolver f) = D.coordinateSolver (timeReflection D.T f)
        := by
  exact coerciveSolution_reflection D.T D.T_pos.le D.opF D.opF₁ D.opH
    (multiplier D.M0.field) (boundaryOperator (scaledCutoff D.ℓ D.ℓ_pos)) D.L
    (fun t => multiplier_reflection_of_even (D.F.field t) (hD.frame t))
    (fun t => multiplier_reflection_of_even (D.F₁.field t) (hD.frameDerivative t))
    (fun t => multiplier_reflection_of_even (D.H.field t) (hD.curvature t))
    (multiplier_reflection_of_even D.M0.field hD.initialStrain)
    (fun u => (scaledBoundaryOperator_reflection D.ℓ D.ℓ_pos u).symm)
    (sourceFixedCoercivity D.T D.F D.F₁ D.opInv)
    (sourceFixedCoercivity_pos D.T D.T_pos.le D.F D.F₁ D.opInv)
    (sourceFixedForm_coercive D.T D.T_pos.le D.ℓ D.ℓ_pos D.F D.F₁ D.H D.M0 D.opInv
      D.Be D.Bc D.L D.r D.Be_nonneg D.Bc_nonneg D.L_lower D.r_nonneg D.r_le_quarter
      D.exterior_lower D.core_lower D.opInv_left D.opF_time D.K D.K_nonneg D.opInv_initial
      D.curvature_upper D.small) f

end Data

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem velocityLp_eq_coordinateSolver : G.solution.velocityLp = D.coordinateSolver G.lp :=
  EulerMeanSourceSpatialRegularity.velocity_eq_sourceCoordinates D.T D.T_pos.le D.ℓ D.ℓ_pos
    D.F D.F₁ D.H D.M0 D.opInv D.Be D.Bc D.L D.r D.Be_nonneg D.Bc_nonneg D.L_lower
    D.r_nonneg D.r_le_quarter D.exterior_lower D.core_lower D.opInv_left D.opF_time D.opInv_right
    D.K D.K_nonneg D.opInv_initial D.curvature_upper D.small G.lp G.solution

variable (hodd : ∀ (t : Icc (0 : ℝ) D.T) x, raw (t, (-x, 0)) = -raw (t, (x, 0)))

include hodd in
theorem path_reflection (t : Icc (0 : ℝ) D.T) : reflection (G.path t) = -(G.path t) := by
  apply Lp.ext
  filter_upwards [reflection_ae (G.path t),
    measurePreserving_reflection.quasiMeasurePreserving.ae
      (pathRepresentative_ae D.T G.path G.path_orbit t),
    pathRepresentative_ae D.T G.path G.path_orbit t, Lp.coeFn_neg (G.path t)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, G.forcingRepresentative_eq t (-x) 0, hodd t x, h₄]
  change -raw (t,(x,0)) = -(G.path t x)
  rw [h₃, G.forcingRepresentative_eq t x 0]

include hodd in
theorem lp_reflection : timeReflection D.T G.lp = -G.lp := by
  apply Lp.ext
  filter_upwards [timeReflection_ae D.T G.lp, G.lp_rep, Lp.coeFn_neg G.lp] with t h₁ h₂ h₃
  rw [h₁, h₂]
  change reflection (G.path (projIcc 0 D.T D.T_pos.le t)) = _
  rw [G.path_reflection hodd]
  exact (congrArg Neg.neg h₂).symm.trans h₃.symm

include hodd in
theorem velocityLp_reflection (hD : EvenData D) :
    timeSolenoidalReflection D.T G.solution.velocityLp = -G.solution.velocityLp :=
  (congrArg (timeSolenoidalReflection D.T) G.velocityLp_eq_coordinateSolver).trans
    ((D.coordinateSolver_reflection hD G.lp).trans
      ((congrArg D.coordinateSolver (G.lp_reflection hodd)).trans
        ((D.coordinateSolver.map_neg G.lp).trans
          (congrArg Neg.neg G.velocityLp_eq_coordinateSolver).symm)))

include hodd in
/-- Oddness of the actual L² solve holds pointwise for its continuous time representative. -/
theorem coordinate_velocity_reflection (hD : EvenData D) (t : Icc (0 : ℝ) D.T) :
    solenoidalReflection (G.solution.velocity t) = -G.solution.velocity t := by
  have hae : (fun r => solenoidalReflection (G.solution.velocity r)) =ᵐ[timeMeasure D.T]
      (fun r => -G.solution.velocity r) := by
    filter_upwards [timeSolenoidalReflection_ae D.T G.solution.velocityLp,
      G.solution.velocity_ae, Lp.coeFn_neg G.solution.velocityLp] with r h₁ h₂ h₃
    have he := congrArg (fun z : TimeLp D.T solenoidalSpace => z r) (G.velocityLp_reflection hodd
        hD)
    exact (congrArg solenoidalReflection h₂).symm.trans
      (h₁.symm.trans (he.trans (h₃.trans (congrArg Neg.neg h₂))))
  have hc : ContinuousOn G.solution.velocity (Icc (0 : ℝ) D.T) := by
    simpa only [uIcc_of_le D.T_pos.le] using G.solution.velocity_ac.continuousOn
  exact Measure.eqOn_Icc_of_ae_eq volume D.T_pos.ne hae
    (solenoidalReflection.continuous.comp_continuousOn hc) hc.neg t.property

end Forcing

end EulerMeanPacketProvider
