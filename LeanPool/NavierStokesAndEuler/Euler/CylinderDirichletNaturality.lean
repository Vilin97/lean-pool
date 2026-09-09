/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletData
public import LeanPool.NavierStokesAndEuler.Euler.FixedEvolutionNaturality
public import LeanPool.NavierStokesAndEuler.Euler.GramNaturality
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTranslationAdjoint

@[expose] public section

/-!
# Spatial intertwiners for the actual cylinder history

These are consequences of the constructed variational inverse and Gram
inverse. Subsequent support and translation lemmas discharge the displayed
coefficient identities for their actual spatial maps.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerTimeLp
  EulerVolterraConvolution EulerLpCylinderTranslation EulerTimeLpBoundedMap
  EulerTransverseGramInverse

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U V E F : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (D : Coefficients T U E) (G : Coefficients T V F)
  (A : CylinderL2 P U →L[ℝ] CylinderL2 P V)
  (B : CylinderL2 P E →L[ℝ] CylinderL2 P F)
  (hQ : ∀ t u, G.frame P t (A u) = B (D.frame P t u))
  (hQ₁ : ∀ t u, G.frameDerivative P t (A u) = B (D.frameDerivative P t u))
  (hback : ∀ t v, D.frame P t (A.adjoint v) = B.adjoint (G.frame P t v))
  (hback₁ : ∀ t v, D.frameDerivative P t (A.adjoint v) = B.adjoint (G.frameDerivative P t v))
  (hH : ∀ t u, G.hessian P t (B u) = B (D.hessian P t u))

include hQ hQ₁ hback hback₁ hH

theorem velocityLp_intertwines (f : TimeLp T (CylinderL2 P E)) :
    G.velocityLp P (timeLift T B f) = timeLift T A (D.velocityLp P f) :=
  EulerFixedFrameNaturality.velocityLp_intertwines T D.time_pos.le A B
    (D.frame P) (D.frameDerivative P) (G.frame P) (G.frameDerivative P) (D.hessian P) (G.hessian P)
    D.lower D.lower_pos (D.frame_lower P) G.lower G.lower_pos (G.frame_lower P)
    (D.frame_derivative P) (G.frame_derivative P) D.potential G.potential
    D.potential_nonneg G.potential_nonneg (D.hessian_upper P) (G.hessian_upper P)
    D.small G.small hQ hQ₁ hback hback₁ hH f

theorem accelerationLp_intertwines (f : TimeLp T (CylinderL2 P E)) :
    G.accelerationLp P (timeLift T B f) = timeLift T A (D.accelerationLp P f) :=
  EulerFixedFrameNaturality.accelerationLp_intertwines T D.time_pos.le A B
    (D.frame P) (D.frameDerivative P) (G.frame P) (G.frameDerivative P) (D.hessian P) (G.hessian P)
    D.lower D.lower_pos (D.frame_lower P) G.lower G.lower_pos (G.frame_lower P)
    (D.frame_derivative P) (G.frame_derivative P) D.potential G.potential
    D.potential_nonneg G.potential_nonneg (D.hessian_upper P) (G.hessian_upper P)
    D.small G.small hQ hQ₁ hback hback₁ hH f

theorem velocityPath_intertwines (f : TimeLp T (CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    G.velocityPath P (timeLift T B f) t = A (D.velocityPath P f t) :=
  EulerFixedFrameNaturality.velocityPath_intertwines T D.time_pos.le A B
    (D.frame P) (D.frameDerivative P) (G.frame P) (G.frameDerivative P) (D.hessian P) (G.hessian P)
    D.lower D.lower_pos (D.frame_lower P) G.lower G.lower_pos (G.frame_lower P)
    (D.frame_derivative P) (G.frame_derivative P) D.potential G.potential
    D.potential_nonneg G.potential_nonneg (D.hessian_upper P) (G.hessian_upper P)
    D.small G.small hQ hQ₁ hback hback₁ hH f t

theorem continuousVelocity_intertwines (f : C(Icc (0 : ℝ) T,CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    G.velocityPath P (pathLp T G.time_pos.le (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f)) t =
      A (D.velocityPath P (pathLp T D.time_pos.le f) t) := by
  rw [pathLp_timeLift]
  exact D.velocityPath_intertwines P G A B hQ hQ₁ hback hback₁ hH _ t

theorem accelerationPath_intertwines (f : C(Icc (0 : ℝ) T,CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    G.accelerationPath P (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) t =
      A (D.accelerationPath P f t) := by
  change gramInverse (G.frame P t) G.lower G.lower_pos (G.frame_lower P t)
    ((G.frame P t).adjoint (B (f t)-(2 : ℝ) • G.frameDerivative P t
      (G.velocityPath P (pathLp T G.time_pos.le (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f)) t))) = _
  rw [continuousVelocity_intertwines P D G A B hQ hQ₁ hback hback₁ hH]
  exact EulerGramNaturality.acceleration_intertwines A B
    (D.frame P t) (D.frameDerivative P t) (G.frame P t) (G.frameDerivative P t)
    D.lower D.lower_pos (D.frame_lower P t) G.lower G.lower_pos (G.frame_lower P t)
    (hQ t) (hQ₁ t) (hback t) (f t) (D.velocityPath P (pathLp T D.time_pos.le f) t)

theorem physicalVelocity_intertwines (f : C(Icc (0 : ℝ) T,CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    G.physicalVelocity P (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) t =
      B (D.physicalVelocity P f t) := by
  change G.frame P t
    (G.velocityPath P (pathLp T G.time_pos.le (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f)) t) = _
  rw [continuousVelocity_intertwines P D G A B hQ hQ₁ hback hback₁ hH,hQ]
  rfl

theorem physicalDerivative_intertwines (f : C(Icc (0 : ℝ) T,CylinderL2 P E)) (t : Icc (0 : ℝ) T) :
    G.physicalDerivative P (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) t =
      B (D.physicalDerivative P f t) := by
  change G.frameDerivative P t
      (G.velocityPath P (pathLp T G.time_pos.le (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f)) t)+
    G.frame P t (G.accelerationPath P (B.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) t) = _
  rw [continuousVelocity_intertwines P D G A B hQ hQ₁ hback hback₁ hH,
    accelerationPath_intertwines P D G A B hQ hQ₁ hback hback₁ hH,hQ₁,hQ,← map_add]
  rfl

end EulerCylinderDirichlet.Coefficients
