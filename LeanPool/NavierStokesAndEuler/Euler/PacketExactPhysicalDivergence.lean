/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketExactPhysicalMomentum
public import LeanPool.NavierStokesAndEuler.Euler.PacketVolumeDivergence

@[expose] public section

/-! The actual exact packet remains incompressible after the genuine
unit-Jacobian parent-flow coordinate change. -/

noncomputable section

namespace EulerPacketPhysicalTransform

open Set Filter InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerPacketCorrectionCoefficients EulerPacketVolumeDivergence EulerGraphPressurePotential
  EulerCylinderSmoothOrbit EulerGraphPullback
open scoped Topology ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower P D.T}
  {B : Budget P D.T_pos (correctionData D P κ hκ Z R)}
  (S : ExactLiftedPacket P D.T_pos (correctionData D P κ hκ Z R) B)

theorem exact_source_divergence
    (k : ℝ) (hk : k*κ=1)
    (F : ℝ × Space → Space →L[ℝ] Space) (X Y : ℝ × Space → Space)
    (t : Icc (0 : ℝ) D.T) (x : Space)
    (hmatch : ∀ y, F (t,y) = D.F.field t y)
    (hX : ContDiffAt ℝ 2 (fun y => X (t,y)) x)
    (hspace : ∀ y, fderiv ℝ (fun a => X (t,a)) y = F (t,y))
    (hdet : ∀ y, (EulerPacketPiola.operatorMatrix (F (t,y))).det = 1)
    (hleft : ∀ y, Y (t,X (t,y)) = y)
    (hY : DifferentiableAt ℝ (fun y => Y (t,y)) (X (t,x))) :
    divergence (fun y => physicalVelocity κ k D.m₀ F S.rawVelocity Y (t,y)) (X (t,x)) = 0 := by
  let g : Space → Space := fun y => S.velocity.pointField t (cylinderGraph P k D.m₀ y)
  have hg : ContDiff ℝ ∞ g := by
    have h := (coverField_contDiff P (S.velocity.pointField t) (S.velocity.pointField_smooth
      t)).comp
      (graphMap k D.m₀).contDiff
    simpa only [g,Function.comp_def,graphMap_apply,cylinderGraph] using h
  have hdg : divergence g x = 0 := by
    rw [divergence_eq_coordinate_sum]
    exact S.graphVelocity_divergence k hk t x
  have hv : DifferentiableAt ℝ (fun y => κ • g y) x :=
    (hg.differentiable (by simp) x).const_smul κ
  have hvzero : divergence (fun y => κ • g y) x = 0 := by
    rw [divergence_eq_trace,← coordinateTrace_eq_linearTrace]
    change coordinateTrace (fderiv ℝ (κ • g) x) = 0
    rw [
      ((hg.differentiable (by simp) x).hasFDerivAt.const_smul κ).fderiv,
      map_smul,coordinateTrace_eq_linearTrace]
    change κ • divergence g x = 0
    rw [hdg,smul_zero]
  have he : (fun y => physicalVelocity κ k D.m₀ F S.rawVelocity Y (t,y)) =
      (fun y => fderiv ℝ (fun a => X (t,a)) (Y (t,y)) (κ • g (Y (t,y)))) := by
    funext y
    simp only [physicalVelocity,inverseCoordinates,graphVelocity,spaceTimeGraph_apply,
      ExactLiftedPacket.rawVelocity,FieldTower.rawField,projIcc_of_mem D.T_pos.le t.property,
      g,cylinderGraph,coveringMap,hspace,map_smul]
  rw [he]
  have hdet' : (fun y => (EulerPacketPiola.operatorMatrix
      (fderiv ℝ (fun a => X (t,a)) y)).det) =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.Eventually.of_forall (fun y => by
      change (EulerPacketPiola.operatorMatrix (fderiv ℝ (fun a => X (t,a)) y)).det = 1
      rw [hspace,hdet])
  exact (divergence_pushforward (fun y => X (t,y)) (fun y => Y (t,y))
    (fun y => κ • g y) x (D.deformationEquiv t x) hX
    ((hspace x).trans (hmatch x)) hdet' hleft hY hv).trans hvzero

end EulerPacketPhysicalTransform
