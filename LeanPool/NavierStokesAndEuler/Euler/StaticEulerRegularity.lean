/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerTime
public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerSolution

/-! The actual local Euler velocity and pressure force agree with the
constructed smooth coefficient paths. In particular the local velocity
has a true one-sided time derivative at the initial and terminal times. -/

@[expose] public section


noncomputable section

namespace EulerStaticEuler

open Set ContinuousLinearMap EulerSmoothLimit EulerLpTranslation EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] (u : SmoothL2Field Space) (C R : ℝ)
  (hC : 0 ≤ C) (hR : 0 ≤ R) (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x = 0)

theorem velocityCoefficient_apply (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    (velocityCoefficient P u C R hC hR hu hdiv).field t x =
      localVelocity P u C R hC hR hu hdiv (t,x) := by
  change (amplitude P C R hC hR)⁻¹ •
    (unitVelocityCoefficient P u C R hC hR hu hdiv).field
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t) x = _
  rw [unitVelocityCoefficient_apply]
  change (amplitude P C R hC hR)⁻¹ • EulerConstantEuler.velocity
      (exactPacket P u C R hC hR hu hdiv) ((t : ℝ)/amplitude P C R hC hR,x) =
    (amplitude P C R hC hR)⁻¹ • EulerConstantEuler.velocity
      (exactPacket P u C R hC hR hu hdiv) ((amplitude P C R hC hR)⁻¹*(t : ℝ),x)
  rw [div_eq_mul_inv,mul_comm (t : ℝ)]

theorem forceCoefficient_apply (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    (forceCoefficient P u C R hC hR hu hdiv).field t x =
      localForce P u C R hC hR hu hdiv (t,x) := by
  change ((amplitude P C R hC hR)⁻¹)^2 •
    (unitForceCoefficient P u C R hC hR hu hdiv).field
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t) x = _
  rw [unitForceCoefficient_apply]
  change ((amplitude P C R hC hR)⁻¹)^2 • EulerConstantEuler.force
      (exactPacket P u C R hC hR hu hdiv) ((t : ℝ)/amplitude P C R hC hR,x) =
    ((amplitude P C R hC hR)⁻¹)^2 • EulerConstantEuler.force
      (exactPacket P u C R hC hR hu hdiv) ((amplitude P C R hC hR)⁻¹*(t : ℝ),x)
  rw [div_eq_mul_inv,mul_comm (t : ℝ)]

theorem localVelocity_hasDerivWithinAt
    (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    HasDerivWithinAt (fun s => localVelocity P u C R hC hR hu hdiv (s,x))
      ((derivativeCoefficient P u C R hC hR hu hdiv).field t x)
      (Icc (0 : ℝ) (amplitude P C R hC hR)) t := by
  have hd := coefficient_time P u C R hC hR hu hdiv t x
  apply hd.congr_of_mem _ t.property
  intro s hs
  have he := velocityCoefficient_apply P u C R hC hR hu hdiv ⟨s,hs⟩ x
  simpa only [SmoothTimeField.realField,extendPath,projIcc_of_mem (amplitude_pos P C R hC hR).le hs]
    using he.symm

end EulerStaticEuler
