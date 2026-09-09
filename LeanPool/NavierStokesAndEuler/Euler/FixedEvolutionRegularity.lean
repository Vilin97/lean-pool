/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseFixedClassical
import LeanPool.NavierStokesAndEuler.Euler.ContinuousAccelerationGevrey
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.TimeLpAccelerationForcing
import LeanPool.NavierStokesAndEuler.Euler.TransverseParameterRegularity
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth dependence of the actual fixed-coordinate history

The coercive inverse, Gram inverse and fixed H¹ reconstruction are the actual
ones used in the history solution. Smooth coefficient and forcing parameters
therefore give smooth continuous-time coordinate and physical velocities.
-/

@[expose] public section


noncomputable section

namespace EulerTransverseFixedEvolution

open Set ContinuousLinearMap InnerProductSpace EulerTimeLp EulerVolterraConvolution
  EulerTimeH1FrameTransport EulerTransverseParameterRegularity EulerTimeLpGramGevrey
  EulerTimeLpGramInverse EulerTimeH1Reconstruction EulerContinuousPathCalculus
open scoped ContDiff

variable {X U E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : X → C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : X → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
  (hd : ∀ x (t : Icc (0 : ℝ) T),
    HasDerivWithinAt (extendPath T hT (Q x)) (Q₁ x t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hPotential : ∀ x t v, ⟪H x t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
  {n : ℕ∞ω} (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁) (hH : ContDiff ℝ n H)

include hQ hQ₁ hH

theorem velocityLp_contDiff (f : X → TimeLp T E) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => velocityLp T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
      K hK (hPotential x) hsmall (f x)) :=
  (zeroTraceDerivatives (U := U) T hT).subtypeL.contDiff.comp
    (contDiff_fixedFrameSolution T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH f hf)

theorem accelerationLp_contDiff (f : X → TimeLp T E) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => accelerationLp T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
      K hK (hPotential x) hsmall (f x)) := by
  let v := fun x => velocityLp T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
    K hK (hPotential x) hsmall (f x)
  have hv : ContDiff ℝ n v := velocityLp_contDiff T hT Q Q₁ H c hc hLower hd
    K hK hPotential hsmall hQ hQ₁ hH f hf
  exact gramSolution_contDiff T hT Q c hc hLower
    (EulerTimeLpAccelerationForcing.forcing T hT Q Q₁ f v) hQ
    (EulerTimeLpAccelerationForcing.forcing_contDiff T hT Q Q₁ f v hQ hQ₁ hf hv)

theorem velocityPath_contDiff (f : X → TimeLp T E) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => velocityPath T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
      K hK (hPotential x) hsmall (f x)) :=
  ((valuePart T hT).contDiff.comp
    (velocityLp_contDiff T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH f hf)).add
  ((derivativePart T hT).contDiff.comp
    (accelerationLp_contDiff T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH f hf))

theorem continuousVelocity_contDiff (f : X → C(Icc (0 : ℝ) T, E)) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => velocityPath T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
      K hK (hPotential x) hsmall (pathLp T hT (f x))) := by
  have hmap : ContDiff ℝ n (pathLpOperator (E := E) T hT) :=
    (pathLpOperator (E := E) T hT).contDiff
  exact velocityPath_contDiff T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH
    (fun x => pathLp T hT (f x)) (hmap.comp hf)

theorem classicalAcceleration_contDiff (f : X → C(Icc (0 : ℝ) T, E)) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => classicalAcceleration T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
      K hK (hPotential x) hsmall (f x)) :=
  EulerContinuousAccelerationGevrey.acceleration_contDiff T Q Q₁ c hc hLower
    (fun x => velocityPath T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
      K hK (hPotential x) hsmall (pathLp T hT (f x))) f hQ hQ₁
    (continuousVelocity_contDiff T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH f hf)
        hf

theorem physicalVelocity_contDiff (f : X → C(Icc (0 : ℝ) T, E)) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => physicalVelocityPath T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
      K hK (hPotential x) hsmall (f x)) := by
  exact EulerContinuousPathCalculus.contDiff_apply Q _ hQ
    (continuousVelocity_contDiff T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH f hf)

theorem physicalDerivative_contDiff (f : X → C(Icc (0 : ℝ) T, E)) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => physicalDerivativePath T hT (Q x) (Q₁ x) (H x) c hc (hLower x) (hd x)
      K hK (hPotential x) hsmall (f x)) :=
  (EulerContinuousPathCalculus.contDiff_apply Q₁ _ hQ₁
    (continuousVelocity_contDiff T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH f
        hf)).add
  (EulerContinuousPathCalculus.contDiff_apply Q _ hQ
    (classicalAcceleration_contDiff T hT Q Q₁ H c hc hLower hd K hK hPotential hsmall hQ hQ₁ hH f
        hf))

end EulerTransverseFixedEvolution
