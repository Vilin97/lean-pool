/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCylinderAccelerationLp
import LeanPool.NavierStokesAndEuler.Euler.SmoothCylinderComposition
import LeanPool.NavierStokesAndEuler.Euler.SmoothCylinderFlow

/-! The actual composed acceleration field of the constructed periodic
flow has L² Gevrey jets with its original source amplitudes. -/

@[expose] public section


noncomputable section

namespace EulerSmoothCylinderFlow

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerSmoothFlowGevrey
open scoped ContDiff BoundedContinuousFunction

/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderAccelerationComposition1 (n : ℕ) : NormedAddCommGroup (LiftTangent
    →ᵇ (LiftTangent [×n]→L[ℝ]
    LiftTangent)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderAccelerationComposition2 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ] LiftTangent))
    := inferInstance

variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)
  (hA₁ : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A₁.field t (z.1, (c : ℝ) + z.2) = A₁.field t z)
  (hdiv : ∀ t x,
    LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent)
        x).toLinearMap = 0)

/-- Material acceleration jet, given by `jetSeries P (materialAcceleration T hT A A₁ t) q n`. -/
def materialAccelerationJet (t : Icc (0 : ℝ) T) (q : LiftDomain P) (n : ℕ) :
    LiftTangent [×n]→L[ℝ] LiftTangent :=
  jetSeries P (materialAcceleration T hT A A₁ t) q n

include hA hA₁ in
theorem materialAccelerationJet_local (t : Icc (0 : ℝ) T) (q : LiftDomain P) (n : ℕ) :
    materialAccelerationJet P T hT A A₁ t q n =
      iteratedFDeriv ℝ n (EulerMetricTransport.localFieldLift P
        (descend P (materialAcceleration T hT A A₁ t)) q) 0 := by
  apply jetSeries_eq_local
  exact comp_deck P (accelerationField T A A₁ t)
    (accelerationField_deck P T A A₁ hA hA₁ t) ((flowData T hT A).forward t)
    (EulerCylinderPeriodicFlow.flow_deck P (flowData T hT A) (velocity_deck P T hT A hA) 0 t)

include hA hA₁ hdiv in
theorem materialAccelerationJet_memLp_and_bound (B R C S C₁ S₁ : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hC₁ : 0 ≤ C₁) (hS₁ : 0 ≤ S₁) (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (hLp : ∀ (t : Icc (0 : ℝ) T) j,
      MemLp (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm : ∀ (t : Icc (0 : ℝ) T) j,
      (eLpNorm (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C * S ^ j * (j.factorial : ℝ) ^ 2)
    (hLp₁ : ∀ (t : Icc (0 : ℝ) T) j,
      MemLp (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm₁ : ∀ (t : Icc (0 : ℝ) T) j,
      (eLpNorm (fun q => jetSeries P (A₁.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C₁ * S₁ ^ j * (j.factorial : ℝ) ^ 2)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    MemLp (fun q => materialAccelerationJet P T hT A A₁ t q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => materialAccelerationJet P T hT A A₁ t q n)
        2 (liftMeasure P)).toReal ≤
          (C₁+3*B*R*C)*(flowRadius B R T (accelerationLpRadius R S S₁))^n*(n.factorial : ℝ)^2 := by
  have hout := accelerationField_memLp_and_bound P T A A₁ B R C S C₁ S₁
    hB hR.le hC hS hC₁ hS₁ hb hLp hNorm hLp₁ hNorm₁
  apply composeJet_memLp_and_bound P T hT A hA hdiv (accelerationField T A A₁ t)
    (accelerationField_contDiff T A A₁ t) (accelerationField_deck P T A A₁ hA hA₁ t)
    B R (C₁+3*B*R*C) (accelerationLpRadius R S S₁)
    hB hR (by positivity) (by unfold accelerationLpRadius; positivity)
    hsmall hb n (fun j _ => (hout j t).1) (fun j _ => (hout j t).2) t

end EulerSmoothCylinderFlow
