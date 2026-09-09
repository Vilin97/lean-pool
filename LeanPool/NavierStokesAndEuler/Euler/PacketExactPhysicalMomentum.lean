/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedGraphPressure
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalEulerTransform
import LeanPool.NavierStokesAndEuler.Euler.PacketExactSourceEquation
import LeanPool.NavierStokesAndEuler.Euler.PacketParentFlowDifferentiation

/-! The constructed exact lifted packet gives the actual momentum equation
after the genuine parent-flow change of coordinates. The scalar pressure
is the normalized radial potential of the constructed pressure tower. -/

@[expose] public section


noncomputable section

namespace EulerPacketPhysicalTransform

open Set Filter InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerPacketCorrectionCoefficients EulerLagrangian
open scoped Topology ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower P D.T}
  {B : Budget P D.T_pos (correctionData D P κ hκ Z R)}
  (S : ExactLiftedPacket P D.T_pos (correctionData D P κ hκ Z R) B)

/-- All derivatives and the pressure of the perturbation are constructed
from the exact lifted solution. Only the actual parent flow and its inverse
enter as geometric data. -/
theorem exact_source_momentum
    (k : ℝ) (hk : k * κ = 1)
    (F : ℝ × Space → Space →L[ℝ] Space)
    (u : ℝ × Space → Space) (p : ℝ × Space → ℝ) (X Y : ℝ × Space → Space)
    (hmatch : ∀ s : Icc (0 : ℝ) D.T, ∀ y, F (s,y) = D.F.field s y)
    (t : ℝ) (ht : t ∈ Ioo 0 D.T) (x : Space)
    (hleft : ∀ s y, Y (s,X (s,y)) = y)
    (hY : DifferentiableAt ℝ (inverseCoordinates Y) (t,X (t,x)))
    (hX : ContDiffAt ℝ 2 X (t,x))
    (hframe : F =ᶠ[𝓝 (t,x)] fun r => (fderiv ℝ X r).comp (inr ℝ ℝ Space))
    (hflow : (fun r => fderiv ℝ X r (1,0)) =ᶠ[𝓝 (t,x)] fun r => u (r.1,X r))
    (hu : DifferentiableAt ℝ u (t,X (t,x)))
    (hp : DifferentiableAt ℝ (fun y => p (t,y)) (X (t,x)))
    (hparent : momentumResidual u p (t,X (t,x)) = 0) :
    momentumResidual (fun q => u q+physicalVelocity κ k D.m₀ F S.rawVelocity Y q)
      (fun q => p q+physicalPressure (S.rawGraphPotential k) Y q) (t,X (t,x)) = 0 := by
  have hDF : DifferentiableAt ℝ (fun r => (fderiv ℝ X r).comp (inr ℝ ℝ Space)) (t,x) :=
    ((hX.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).clm_comp
      (differentiableAt_const (inr ℝ ℝ Space))
  have hF : HasFDerivAt F (fderiv ℝ F (t,x)) (t,x) :=
    (hDF.congr_of_eventuallyEq hframe).hasFDerivAt
  have hz : HasFDerivAt S.rawVelocity
      (fderiv ℝ S.rawVelocity (spaceTimeGraph k D.m₀ (t,x)))
      (spaceTimeGraph k D.m₀ (t,x)) :=
    (S.rawVelocity_hasFDerivAt t ht (x,k*⟪D.m₀,x⟫_ℝ)).differentiableAt.hasFDerivAt
  have hA : F (t,x) = (D.deformationEquiv ⟨t,ht.1.le,ht.2.le⟩ x).toContinuousLinearMap :=
    hmatch ⟨t,ht.1.le,ht.2.le⟩ x
  exact physical_euler_momentum_of_flow κ k hk D.m₀ F S.rawVelocity u p
    (S.rawGraphPotential k) X Y t x (D.deformationEquiv ⟨t,ht.1.le,ht.2.le⟩ x)
    (fderiv ℝ F (t,x)) (fderiv ℝ S.rawVelocity (spaceTimeGraph k D.m₀ (t,x)))
    (fderiv ℝ u (t,X (t,x))) (S.rawPressure (spaceTimeGraph k D.m₀ (t,x)))
    hleft hY hX hframe hflow hF hz hA hu.hasFDerivAt hp
    ((S.rawGraphPotential_smooth k hk t).differentiable (by simp) x)
    (S.rawGraphPotential_gradient k hk t x) hparent
    (S.source_equation_of_frame D F hmatch t ht (x,k*⟪D.m₀,x⟫_ℝ) _ hF)

end EulerPacketPhysicalTransform
