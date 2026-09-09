/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointUnitBounds

@[expose] public section

/-!
The actual primary endpoint map at arbitrary terminal amplitude. These
fixed-Hq external-word estimates retain the same radius for every amplitude
and shift. The radius guards depend only on the coefficient budget.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients.EndpointBudget

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerGevrey EulerParameterWordGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {D : Coefficients T U E} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : EndpointBudget D ι q) (directions : ι → LiftTangent)
  (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (Y : CylinderL2 P U) (hY : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y))
  (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hYb : ∀ n, block directions q (fun a : LiftTangent => translate P a Y) n 0 ≤ A*majorant L.R d n)

include hdir hY hA hYb

theorem coordinate_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointCoordinate P Y)) n 0 ≤
      (L.coordinateCost*A)*majorant L.R (d+2) n :=
  terminal_amplitude_bound P directions q (D.endpointCoordinate P)
    (fun Z hZ => D.endpointCoordinate_orbit_contDiff P L.frame_smooth
      L.frameDerivative_smooth L.hessian_smooth Z hZ)
    L.R L.coordinateCost d (d+2)
    (fun Z hZ hb => L.coordinate_unit_bound P directions hdir Z hZ d hb)
    Y hY A hA hYb n

theorem acceleration_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointAcceleration P Y)) n 0 ≤
      A*majorant L.R (d+3) n := by
  simpa only [one_mul] using terminal_amplitude_bound P directions q (D.endpointAcceleration P)
    (fun Z hZ => D.endpointAcceleration_orbit_contDiff P L.frame_smooth
      L.frameDerivative_smooth L.hessian_smooth Z hZ)
    L.R 1 d (d+3)
    (fun Z hZ hb k => by
      simpa only [one_mul] using L.acceleration_unit_bound P directions hdir Z hZ d hb k)
    Y hY A hA hYb n

theorem velocity_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointVelocity P Y)) n 0 ≤
      (L.velocityCost*A)*majorant L.R (d+2) n :=
  terminal_amplitude_bound P directions q (D.endpointVelocity P)
    (fun Z hZ => D.endpointVelocity_orbit_contDiff P L.frame_smooth
      L.frameDerivative_smooth L.hessian_smooth Z hZ)
    L.R L.velocityCost d (d+2)
    (fun Z hZ hb => L.velocity_unit_bound P directions hdir Z hZ d hb)
    Y hY A hA hYb n

theorem derivative_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointDerivative P Y)) n 0 ≤
      (L.derivativeCost*A)*majorant L.R (d+3) n :=
  terminal_amplitude_bound P directions q (D.endpointDerivative P)
    (fun Z hZ => D.endpointDerivative_orbit_contDiff P L.frame_smooth
      L.frameDerivative_smooth L.hessian_smooth Z hZ)
    L.R L.derivativeCost d (d+3)
    (fun Z hZ hb => L.derivative_unit_bound P directions hdir Z hZ d hb)
    Y hY A hA hYb n

end EulerCylinderDirichlet.Coefficients.EndpointBudget
