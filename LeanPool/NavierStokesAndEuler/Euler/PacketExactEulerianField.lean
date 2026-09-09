/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketExactPhysicalEuler
public import LeanPool.NavierStokesAndEuler.Euler.PacketEulerianRegularity

@[expose] public section

/-! Literal agreement between the exact physical Euler fields and their
constructed smooth L² representatives, including the scalar pressure. -/

noncomputable section

namespace EulerPacketPhysicalTransform

open Set EulerSmoothLimit EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerPacketCorrectionCoefficients EulerGraphPressurePotential EulerLiftedGradientSpace
  EulerPacketInverseFlowGevrey EulerPacketPhysicalField
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  {κ : ℝ} {hκ : |κ| ≤ 1} {Z R : FieldTower P D.T}
  {B : Budget P D.T_pos (correctionData D P κ hκ Z R)}
  (S : ExactLiftedPacket P D.T_pos (correctionData D P κ hκ Z R) B)

theorem exact_physicalVelocity_eq (k : ℝ)
    (F : ℝ × Space → Space →L[ℝ] Space) (Y : ℝ × Space → Space)
    (hF : ∀ (t : Icc (0 : ℝ) D.T) x, F (t,x)=D.F.field t x)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    physicalVelocity κ k D.m₀ F S.rawVelocity Y (t,x) =
      κ • D.F.field t (Y (t,x))
        (S.velocity.pointField t (cylinderGraph P k D.m₀ (Y (t,x)))) := by
  simp only [physicalVelocity,inverseCoordinates,graphVelocity,spaceTimeGraph_apply,
    ExactLiftedPacket.rawVelocity,FieldTower.rawField,projIcc_of_mem D.T_pos.le t.property,
    hF,cylinderGraph,coveringMap]

variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hY : Continuous (Function.uncurry Y))

include hX hXY hY in
theorem exact_physicalPressure_gradient (k : ℝ) (hk : k*κ=1)
    (Yraw : ℝ × Space → Space)
    (hYraw : ∀ (t : Icc (0 : ℝ) D.T) x, Yraw (t,x)=Y t x)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    gradient (fun y => physicalPressure (S.rawGraphPotential k) Yraw (t,y)) x =
      κ • (D.FInv.field t (Y t x)).adjoint
        (S.pressure.pointField t (cylinderGraph P k D.m₀ (Y t x))) := by
  have he : (fun y => physicalPressure (S.rawGraphPotential k) Yraw (t,y)) =
      S.graphPotential k t ∘ Y t := by
    funext y
    simp only [physicalPressure,inverseCoordinates,ExactLiftedPacket.rawGraphPotential,
      projIcc_of_mem D.T_pos.le t.property,Function.comp_def,hYraw]
  rw [he,EulerLagrangian.gradient_pullback _ _ _ _
    (continuousInverse_hasFDerivAt D X Y hX hXY hY t x)
    ((S.graphPotential_smooth k hk t).differentiable (by simp) (Y t x)),
    S.graphPotential_gradient k hk t (Y t x),map_smul]
  rfl

include hX hXY hY in
theorem exact_physicalPressure_smooth (k : ℝ) (hk : k*κ=1)
    (Yraw : ℝ × Space → Space)
    (hYraw : ∀ (t : Icc (0 : ℝ) D.T) x, Yraw (t,x)=Y t x)
    (t : Icc (0 : ℝ) D.T) :
    ContDiff ℝ ∞ (fun y => physicalPressure (S.rawGraphPotential k) Yraw (t,y)) := by
  have he : (fun y => physicalPressure (S.rawGraphPotential k) Yraw (t,y)) =
      S.graphPotential k t ∘ Y t := by
    funext y
    simp only [physicalPressure,inverseCoordinates,ExactLiftedPacket.rawGraphPotential,
      projIcc_of_mem D.T_pos.le t.property,Function.comp_def,hYraw]
  rw [he]
  exact (S.graphPotential_smooth k hk t).comp (continuousInverse_contDiff D X Y hX hXY hY t)

end EulerPacketPhysicalTransform
