/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedGraphPressure
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalEulerTransform
import LeanPool.NavierStokesAndEuler.Euler.PacketExactPhysicalDivergence
import LeanPool.NavierStokesAndEuler.Euler.PacketExactPhysicalMomentum

/-! The actual parent velocity plus the constructed exact packet satisfies
both classical Euler equations in physical coordinates. -/

@[expose] public section


noncomputable section

namespace EulerPacketPhysicalTransform

open Set Filter InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerPacketCorrectionCoefficients EulerLagrangian
open scoped Topology ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower P D.T}
  {B : Budget P D.T_pos (correctionData D P κ hκ Z R)}
  (S : ExactLiftedPacket P D.T_pos (correctionData D P κ hκ Z R) B)

theorem exact_source_velocity_differentiableAt
    (k : ℝ) (F : ℝ × Space → Space →L[ℝ] Space) (X Y : ℝ × Space → Space)
    (t : ℝ) (ht : t ∈ Ioo 0 D.T) (x : Space)
    (hleft : Y (t, X (t, x)) = x)
    (hY : DifferentiableAt ℝ (inverseCoordinates Y) (t, X (t, x)))
    (hX : ContDiffAt ℝ 2 X (t, x))
    (hframe : F =ᶠ[𝓝 (t, x)] fun r => (fderiv ℝ X r).comp (inr ℝ ℝ Space)) :
    DifferentiableAt ℝ (physicalVelocity κ k D.m₀ F S.rawVelocity Y) (t,X (t,x)) := by
  have hDF : DifferentiableAt ℝ (fun r => (fderiv ℝ X r).comp (inr ℝ ℝ Space)) (t,x) :=
    ((hX.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).clm_comp
      (differentiableAt_const (inr ℝ ℝ Space))
  have hF : HasFDerivAt F (fderiv ℝ F (t,x)) (t,x) :=
    (hDF.congr_of_eventuallyEq hframe).hasFDerivAt
  have hz : HasFDerivAt S.rawVelocity
      (fderiv ℝ S.rawVelocity (spaceTimeGraph k D.m₀ (t,x)))
      (spaceTimeGraph k D.m₀ (t,x)) :=
    (S.rawVelocity_hasFDerivAt t ht (x,k*⟪D.m₀,x⟫_ℝ)).differentiableAt.hasFDerivAt
  have hG := graphVelocity_hasFDerivAt κ k D.m₀ F S.rawVelocity (t,x) _ _ hF hz
  have hyx : inverseCoordinates Y (t,X (t,x)) = (t,x) := by
    simp only [inverseCoordinates,hleft]
  apply DifferentiableAt.comp _ _ hY
  rw [hyx]
  exact hG.differentiableAt

/-- The classical momentum and incompressibility equations for the actual
new velocity, using the constructed normalized scalar pressure. -/
theorem exact_source_euler
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
    (hspace : ∀ y, fderiv ℝ (fun a => X (t,a)) y = F (t,y))
    (hdet : ∀ y, (EulerPacketPiola.operatorMatrix (F (t,y))).det = 1)
    (hu : DifferentiableAt ℝ u (t,X (t,x)))
    (hp : DifferentiableAt ℝ (fun y => p (t,y)) (X (t,x)))
    (hparent : momentumResidual u p (t,X (t,x)) = 0)
    (hdiv : divergence (fun y => u (t,y)) (X (t,x)) = 0) :
    momentumResidual (fun q => u q+physicalVelocity κ k D.m₀ F S.rawVelocity Y q)
      (fun q => p q+physicalPressure (S.rawGraphPotential k) Y q) (t,X (t,x)) = 0 ∧
    divergence (fun y => u (t,y)+physicalVelocity κ k D.m₀ F S.rawVelocity Y (t,y))
      (X (t,x)) = 0 := by
  refine ⟨exact_source_momentum D S k hk F u p X Y hmatch t ht x
    hleft hY hX hframe hflow hu hp hparent,?_⟩
  have hXs : ContDiffAt ℝ 2 (fun y => X (t,y)) x :=
    hX.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hYs := hY.snd.comp (X (t,x)) (hasFDerivAt_prodMk_right t (X (t,x))).differentiableAt
  change DifferentiableAt ℝ (fun y => Y (t,y)) (X (t,x)) at hYs
  have hWdiv := exact_source_divergence D S k hk F X Y ⟨t,ht.1.le,ht.2.le⟩ x
    (hmatch ⟨t,ht.1.le,ht.2.le⟩) hXs hspace hdet (hleft t) hYs
  have huS : DifferentiableAt ℝ (fun y => u (t,y)) (X (t,x)) :=
    hu.comp (X (t,x)) (hasFDerivAt_prodMk_right t (X (t,x))).differentiableAt
  have hW := exact_source_velocity_differentiableAt D S k F X Y t ht x
    (hleft t x) hY hX hframe
  have hWS : DifferentiableAt ℝ
      (fun y => physicalVelocity κ k D.m₀ F S.rawVelocity Y (t,y)) (X (t,x)) :=
    hW.comp (X (t,x)) (hasFDerivAt_prodMk_right t (X (t,x))).differentiableAt
  rw [divergence_eq_trace,← coordinateTrace_eq_linearTrace,fderiv_fun_add huS hWS,
    map_add,coordinateTrace_eq_linearTrace,coordinateTrace_eq_linearTrace]
  change divergence (fun y => u (t,y)) (X (t,x)) +
    divergence (fun y => physicalVelocity κ k D.m₀ F S.rawVelocity Y (t,y)) (X (t,x)) = 0
  rw [hdiv,hWdiv,add_zero]

end EulerPacketPhysicalTransform
