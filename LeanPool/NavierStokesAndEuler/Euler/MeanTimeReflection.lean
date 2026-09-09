/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalReflection
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpBoundedMap

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
