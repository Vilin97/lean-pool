/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import LeanPool.NavierStokesAndEuler.Euler.SmoothImplicitLift
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldTimeJets
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketPhysicalCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedJointDifferentiability
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalEulerTransform
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildParent

/-! The actual normalized parent coordinates used by the packet. Joint
regularity, the frame, and inverse regularity are derived from the parent
time laws and the literal inverse map. -/

section

/-! The child particle velocity matches the physical reconstruction of
the actual common correction, including the source spatial scaling. -/

section

/-! The constructed child particle velocity is the Eulerian pushforward
of the actual graph velocity. The normalized packet formula follows
from the literal lifted coefficient, with the physical scale explicit. -/

@[expose] public section

noncomputable section

namespace EulerPhysicalGraphFlowBounds.Data

open Set EulerLiftedGradientSpace EulerGraphInvariantFlow EulerSmoothBanachFlow
    EulerSmoothFlowGevrey

variable {P T : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P T)
  (k : ℝ) (m : Vector3) (ell : ℝ) (hell : 0 < ell)
  (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)

include hgraph hell in
theorem physicalDisplacementCoefficient_position (t : Icc (0 : ℝ) T) (x : Vector3) :
    x+(G.physicalDisplacementCoefficient k m ell).field t x =
      (flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t x := by
  rw [G.physicalDisplacementCoefficient_eq k m ell hell,
    G.displacementField_eq k m hgraph ell hell,displacement_eq]
  abel

include hgraph hell in
theorem physicalVelocityCoefficient_material (t : Icc (0 : ℝ) T) (x : Vector3) :
    (G.physicalVelocityCoefficient k m ell).field t x =
      (physicalCoefficient k m T G.A ell).field t
        ((flowData T G.time_nonneg (physicalCoefficient k m T G.A ell)).forward t x) := by
  rw [G.physicalVelocityCoefficient_eq k m ell hell,G.velocityField_eq k m hgraph ell hell]
  rfl

end EulerPhysicalGraphFlowBounds.Data

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerGraphInvariantFlow EulerSmoothBanachFlow
  EulerMetricTransport

variable (A : EulerParentPacketFrames.Parent)
  {P : ℝ} [Fact (0 < P)] (G : EulerPhysicalGraphFlowBounds.Data P A.T)
  (k : ℝ) (m : Vector3) (hgraph : ∀ t z, graphConstraint k m (G.A.field t z) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

/-- Graph pushforward velocity, constructed using `u`. -/
def graphPushforwardVelocity (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  u t x + (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) (Y t
      x))
    ((physicalCoefficient k m A.T G.A A.ell).field t (Y t x))

theorem child_position (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).position t x =
      A.position t ((flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t
          x) :=
  A.child_particleMap G k m hgraph nextEll hnext hnext1 t x

theorem child_velocity_formula (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).velocity.field t x =
      let y := (flowData A.T G.time_nonneg (physicalCoefficient k m A.T G.A A.ell)).forward t x
      A.velocity.field t y +
        (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) y)
          ((physicalCoefficient k m A.T G.A A.ell).field t y) := by
  change (EulerChildParticleTime.velocity A.displacement A.velocity
    (G.physicalDisplacementCoefficient k m A.ell) (G.physicalVelocityCoefficient k m A.ell)).field
        t x=_
  rw [EulerChildParticleTime.velocity_apply,
    G.physicalDisplacementCoefficient_position k m A.ell A.ell_pos hgraph,
    G.physicalVelocityCoefficient_material k m A.ell A.ell_pos hgraph]
  simp only [_root_.add_apply,ContinuousLinearMap.id_apply]
  abel

theorem child_velocity_pushforward (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (hYX : ∀ t x, Y t (A.position t x) = x)
    (hvelocity : ∀ t x, A.velocity.field t x = u t (A.position t x))
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).velocity.field t x =
      A.graphPushforwardVelocity G k m Y u t
        ((A.child G k m hgraph nextEll hnext hnext1).position t x) := by
  rw [A.child_velocity_formula G k m hgraph nextEll hnext hnext1,graphPushforwardVelocity,
    A.child_position G k m hgraph nextEll hnext hnext1,hYX]
  dsimp only
  rw [hvelocity]

theorem graphPushforwardVelocity_packet
    (Y u : Icc (0 : ℝ) A.T → Space → Space) (κ : ℝ)
    (z : Icc (0 : ℝ) A.T → LiftTangent → Space)
    (hlift : ∀ t q, G.A.field t q = transportDirection κ m (z t q))
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.graphPushforwardVelocity G k m Y u t x =
      u t x + A.ell • (κ • A.frame.field t (A.ell⁻¹ • Y t x)
        (z t (graphLinear k m (A.ell⁻¹ • Y t x)))) := by
  rw [graphPushforwardVelocity,physicalCoefficient_apply,hlift]
  change u t x +
    (ContinuousLinearMap.id ℝ Space + fderiv ℝ (A.displacement.field t : Space → Space) (Y t x))
      (A.ell • (κ • z t (graphLinear k m (A.ell⁻¹ • Y t x))))=_
  rw [map_smul,map_smul,A.frame_apply]
  have hx : A.ell • (A.ell⁻¹ • Y t x)=Y t x := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  rw [hx]

end EulerParentPacketFrames.Parent

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace EulerGraphInvariantFlow
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerGraphPressurePotential
  EulerMetricTransport EulerPacketPhysicalTransform

variable (A : EulerParentPacketFrames.Parent)
  {P : ℝ} [Fact (0 < P)] {C : EulerAllOrderCorrectionData.Data P A.T}
  (B : EulerAllOrderDriftCorrection.Budget P A.T_pos C)

/-- Corrected packet velocity, constructed using `u`. -/
def correctedPacketVelocity (k : ℝ) (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  u t x + A.ell • (C.κ • A.frame.field t (A.ell⁻¹ • Y t x)
    ((B.correctedFieldTower P).pointField t (cylinderGraph P k C.direction (A.ell⁻¹ • Y t x))))

/-- Packet inverse, given by `A.ell⁻¹ • Y (projIcc 0 A.T A.T_pos.le q.1) (A.ell • q.2)`. -/
def packetInverse (Y : Icc (0 : ℝ) A.T → Space → Space) (q : ℝ × Space) : Space :=
  A.ell⁻¹ • Y (projIcc 0 A.T A.T_pos.le q.1) (A.ell • q.2)

theorem correctedPacketVelocity_eq_physical (k : ℝ)
    (Y u : Icc (0 : ℝ) A.T → Space → Space) (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.correctedPacketVelocity B k Y u t x =
      u t x + A.ell • physicalVelocity C.κ k C.direction
        (fun q => A.frame.realField A.T A.T_pos.le q.1 q.2)
        ((B.correctedFieldTower P).rawField A.T_pos.le) (A.packetInverse Y) (t,A.ell⁻¹ • x) := by
  have hx : A.ell • (A.ell⁻¹ • x)=x := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  simp only [correctedPacketVelocity,EulerPacketPhysicalTransform.physicalVelocity,
    EulerPacketPhysicalTransform.inverseCoordinates,EulerPacketPhysicalTransform.graphVelocity,
    EulerPacketPhysicalTransform.spaceTimeGraph_apply, packetInverse, FieldTower.rawField,
        SmoothTimeField.realField_apply,
    projIcc_of_mem A.T_pos.le t.property,hx,cylinderGraph,coveringMap]

variable {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw)
  (hV : C.approximation = V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data P A.T)
  (hG : G.A = B.liftedPacketCoefficient P V)

include hV hG in
theorem lifted_graph_constraint (k : ℝ) (hk : k * C.κ = 1)
    (t : Icc (0 : ℝ) A.T) (q : LiftTangent) :
    graphConstraint k C.direction (G.A.field t q)=0 := by
  rw [hG,B.liftedPacketCoefficient_eq_corrected P V hV]
  simp only [graphConstraint_apply,transportDirection,real_inner_smul_right]
  rw [← mul_assoc,hk,one_mul,sub_self]

include hV hG in
theorem graphPushforwardVelocity_corrected (k : ℝ)
    (Y u : Icc (0 : ℝ) A.T → Space → Space) (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.graphPushforwardVelocity G k C.direction Y u t x = A.correctedPacketVelocity B k Y u t x := by
  have h := A.graphPushforwardVelocity_packet G k C.direction Y u C.κ
    (fun s q => (B.correctedFieldTower P).pointField s (coveringMap P q))
    (by
      intro s q
      rw [hG]
      exact B.liftedPacketCoefficient_eq_corrected P V hV s q) t x
  simpa only [correctedPacketVelocity,graphLinear_apply,cylinderGraph,coveringMap] using h

include hV hG in
theorem child_velocity_corrected (k : ℝ)
    (hgraph : ∀ t q, graphConstraint k C.direction (G.A.field t q) = 0)
    (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
    (Y u : Icc (0 : ℝ) A.T → Space → Space)
    (hYX : ∀ t x, Y t (A.position t x) = x)
    (hvelocity : ∀ t x, A.velocity.field t x = u t (A.position t x))
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k C.direction hgraph nextEll hnext hnext1).velocity.field t x =
      A.correctedPacketVelocity B k Y u t
        ((A.child G k C.direction hgraph nextEll hnext hnext1).position t x) :=
  (A.child_velocity_pushforward G k C.direction hgraph nextEll hnext hnext1 Y u hYX hvelocity t
      x).trans
    (A.graphPushforwardVelocity_corrected B V hV G hG k Y u t _)

end EulerParentPacketFrames.Parent

end
end

end

section

/-! A true particle velocity law and the actual Euler equation determine
the particle acceleration. Continuity extends the identity to both
endpoints; no acceleration or pressure-force match is assumed. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set Filter EulerSmoothLimit
open scoped Topology

variable (A : EulerParentPacketFrames.Parent)

/-- Real position, given by `x+A.displacement.realField A.T A.T_pos.le t x`. -/
def realPosition (t : ℝ) (x : Space) : Space :=
  x+A.displacement.realField A.T A.T_pos.le t x

@[simp] theorem realPosition_apply (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.realPosition t x=A.position t x := by
  simp only [realPosition,SmoothTimeField.realField_apply,position]

theorem realPosition_joint_continuous : Continuous (Function.uncurry A.realPosition) :=
  continuous_snd.add (A.displacement.realField_joint_continuous A.T A.T_pos.le)

theorem position_time (t : Icc (0 : ℝ) A.T) (x : Space) :
    HasDerivWithinAt (fun s => A.realPosition s x) (A.velocity.field t x) (Icc (0 : ℝ) A.T) t :=
  (A.displacement_time t x).const_add x

theorem acceleration_eq_neg_gradient
    (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
    (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x = u (t, A.position t x))
    (hdiff : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ u (t, x))
    (heuler : ∀ t ∈ Ioo 0 A.T, ∀ x, EulerLagrangian.momentumResidual u p (t, x) = 0)
    (t : Icc (0 : ℝ) A.T) (ht : (t : ℝ) ∈ Ioo 0 A.T) (x : Space) :
    A.acceleration.field t x= -gradient (fun y => p (t,y)) (A.position t x) := by
  have hp := (A.position_time t x).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hi := (hasDerivAt_id (t : ℝ)).prodMk hp
  have ho : HasFDerivAt u (fderiv ℝ u (t,A.position t x)) (id (t : ℝ),A.realPosition t x) := by
    simpa only [id_eq,A.realPosition_apply] using (hdiff t ht (A.position t x)).hasFDerivAt
  have hc := ho.comp_hasDerivAt (t : ℝ) hi
  have hc' : HasDerivAt (fun s => u (s,A.realPosition s x))
      (fderiv ℝ u (t,A.position t x) (1,A.velocity.field t x)) t := by
    simpa only [Function.comp_def,id_eq,A.realPosition_apply] using hc
  have he : (fun s => u (s,A.realPosition s x)) =ᶠ[𝓝 (t : ℝ)]
      (fun s => A.velocity.realField A.T A.T_pos.le s x) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hm := hvelocity ⟨s,hs.1.le,hs.2.le⟩ x
    simpa only [realPosition,SmoothTimeField.realField,EulerVolterraConvolution.extendPath,
      projIcc_of_mem A.T_pos.le ⟨hs.1.le,hs.2.le⟩,position] using hm.symm
  have hv := ((A.velocity_time t x).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).congr_of_eventuallyEq he
  have ha := hv.unique hc'
  have hh := heuler t ht (A.position t x)
  change fderiv ℝ u (t,A.position t x) (1,u (t,A.position t x)) +
    gradient (fun y => p (t,y)) (A.position t x)=0 at hh
  rw [← hvelocity t x,← ha] at hh
  exact eq_neg_of_add_eq_zero_left hh

theorem acceleration_physical_of_euler
    (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
    (force : Icc (0 : ℝ) A.T → Space → Space)
    (hforce : Continuous (Function.uncurry force))
    (hgradient : ∀ (t : Icc (0 : ℝ) A.T) x, gradient (fun y => p (t, y)) x = force t x)
    (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x = u (t, A.position t x))
    (hdiff : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ u (t, x))
    (heuler : ∀ t ∈ Ioo 0 A.T, ∀ x, EulerLagrangian.momentumResidual u p (t, x) = 0)
    (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.acceleration.field t x= -force t (A.position t x) := by
  let f : ℝ → Space := fun s => A.acceleration.realField A.T A.T_pos.le s x
  let g : ℝ → Space := fun s => -force (projIcc 0 A.T A.T_pos.le s) (A.realPosition s x)
  have hf : Continuous f :=
    (A.acceleration.realField_joint_continuous A.T A.T_pos.le).comp
      (continuous_id.prodMk continuous_const)
  have hg : Continuous g :=
    (hforce.comp ((show Continuous (projIcc 0 A.T A.T_pos.le) from continuous_projIcc).prodMk
      (A.realPosition_joint_continuous.comp (continuous_id.prodMk continuous_const)))).neg
  have he : EqOn f g (Ioo 0 A.T) := by
    intro s hs
    have hh := A.acceleration_eq_neg_gradient u p hvelocity hdiff heuler ⟨s,hs.1.le,hs.2.le⟩ hs x
    rw [hgradient] at hh
    simpa only [f,g,realPosition,SmoothTimeField.realField,EulerVolterraConvolution.extendPath,
      projIcc_of_mem A.T_pos.le ⟨hs.1.le,hs.2.le⟩,position] using hh
  have htc : (t : ℝ) ∈ closure (Ioo (0 : ℝ) A.T) := by
    rw [closure_Ioo A.T_pos.ne]
    exact t.property
  have hh := he.closure hf hg htc
  simpa only [f,g,SmoothTimeField.realField_apply,A.realPosition_apply,
    projIcc_of_mem A.T_pos.le t.property] using hh

end EulerParentPacketFrames.Parent

end
end

end

section

/-! Two actual time-derivative pairs give genuine joint C² regularity
for a smooth spatial coefficient path on interior times. -/

@[expose] public section

noncomputable section

open scoped ContDiff Topology

namespace SmoothTimeField

open Set Filter

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ A₂ : SmoothTimeField (Icc (0 : ℝ) T) E V)

theorem jointDerivative_contDiffAt_one
    (hA : TimeDerivative T hT A A₁) (hA₁ : TimeDerivative T hT A₁ A₂)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 1 (Function.uncurry (jointDerivative T hT A A₁)) (t,x) := by
  have hq := realField_contDiffAt_one T hT A₁ A₂ hA₁ t ht x
  have hJ := realField_contDiffAt_one T hT A.derivative A₁.derivative
    (TimeDerivative.derivative T hT A A₁ hA) t ht x
  have hs := (ContinuousLinearMap.toSpanSingletonLIE ℝ
      V).toContinuousLinearEquiv.contDiff.contDiffAt.comp
    (t,x) hq
  let L : ((ℝ →L[ℝ] V) × (E →L[ℝ] V)) →L[ℝ] ((ℝ × E) →L[ℝ] V) :=
    (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ) (F := E) (G := V) ℝ).toContinuousLinearMap
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1)
    (E := (ℝ →L[ℝ] V) × (E →L[ℝ] V)) (F := (ℝ × E) →L[ℝ] V) L).contDiffAt.comp
    (t,x) (hs.prodMk hJ)

theorem realField_contDiffAt_two
    (hA : TimeDerivative T hT A A₁) (hA₁ : TimeDerivative T hT A₁ A₂)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : E) :
    ContDiffAt ℝ 2 (Function.uncurry (A.realField T hT)) (t,x) := by
  rw [show (2 : ℕ∞ω) = ((1 : ℕ)+1) from rfl,contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨Function.uncurry (jointDerivative T hT A A₁),
    ⟨{p : ℝ × E | p.1 ∈ Ioo 0 T},?_,?_⟩,
    jointDerivative_contDiffAt_one T hT A A₁ A₂ hA hA₁ t ht x⟩
  · exact (continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)
  · intro p hp
    exact realField_hasFDerivAt T hT A A₁ hA p.1 hp p.2

end SmoothTimeField

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set Filter ContinuousLinearMap EulerSmoothLimit EulerSmoothBanachFlow
open scoped ContDiff Topology

variable (A : EulerParentPacketFrames.Parent)

/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instParentNormalizedGeometry1 : NormedAddCommGroup Space := inferInstance
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instParentNormalizedGeometry2 : NormedSpace ℝ Space := inferInstance
/-- Cache the standard `NormedAddCommGroup (ℝ × Space)` instance to shorten typeclass synthesis. -/
local instance instParentNormalizedGeometry3 : NormedAddCommGroup (ℝ × Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (ℝ × Space)` instance to shorten typeclass synthesis. -/
local instance instParentNormalizedGeometry4 : NormedSpace ℝ (ℝ × Space) := inferInstance

/-- Packet position, given by `A.ell⁻¹ • A.realPosition q.1 (A.ell • q.2)`. -/
def packetPosition (q : ℝ × Space) : Space :=
  A.ell⁻¹ • A.realPosition q.1 (A.ell • q.2)

@[simp] theorem packetPosition_apply (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.packetPosition (t,x)=A.ell⁻¹ • A.position t (A.ell • x) := by
  rw [packetPosition,A.realPosition_apply]

theorem realPosition_contDiffAt_two (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    ContDiffAt ℝ 2 (Function.uncurry A.realPosition) (t,x) :=
  contDiffAt_snd.add
    (SmoothTimeField.realField_contDiffAt_two A.T A.T_pos.le
      A.displacement A.velocity A.acceleration A.displacement_time A.velocity_time t ht x)

theorem packetPosition_contDiffAt_two (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    ContDiffAt ℝ 2 A.packetPosition (t,x) :=
  ((A.realPosition_contDiffAt_two t ht (A.ell • x)).comp (t,x)
    (contDiffAt_fst.prodMk (contDiffAt_snd.const_smul A.ell))).const_smul A.ell⁻¹

theorem packetPosition_joint_continuous : Continuous A.packetPosition :=
  (A.realPosition_joint_continuous.comp
    (continuous_fst.prodMk (continuous_snd.const_smul A.ell))).const_smul A.ell⁻¹

theorem realPosition_hasFDerivAt (t : Icc (0 : ℝ) A.T) (ht : (t : ℝ) ∈ Ioo 0 A.T) (x : Space) :
    HasFDerivAt (Function.uncurry A.realPosition)
      ((toSpanSingleton ℝ (A.velocity.field t x)).coprod
        (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) x)) (t,x)
            := by
  have h := hasFDerivAt_snd.add
    (SmoothTimeField.realField_hasFDerivAt A.T A.T_pos.le
      A.displacement A.velocity A.displacement_time t ht x)
  have he : snd ℝ ℝ Space + SmoothTimeField.jointDerivative A.T A.T_pos.le
        A.displacement A.velocity t x =
      (toSpanSingleton ℝ (A.velocity.field t x)).coprod
        (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) x) := by
    apply ContinuousLinearMap.ext
    intro v
    change v.2+(v.1 • A.velocity.realField A.T A.T_pos.le t x +
      A.displacement.derivative.realField A.T A.T_pos.le t x v.2) =
      v.1 • A.velocity.field t x+(v.2+fderiv ℝ (A.displacement.field t : Space → Space) x v.2)
    rw [SmoothTimeField.realField_apply,SmoothTimeField.realField_apply]
    change v.2+(v.1 • A.velocity.field t x+A.displacement.derivativeField t x v.2) = _
    rw [A.displacement.derivativeField_eq]
    abel
  rw [he] at h
  exact h

/-- Packet position derivative, given by `(toSpanSingleton ℝ (A.ell⁻¹ • A.velocity.field t
(A.ell • x))).coprod (A.frame.field t x)`. -/
def packetPositionDerivative (t : Icc (0 : ℝ) A.T) (x : Space) : (ℝ × Space) →L[ℝ] Space :=
  (toSpanSingleton ℝ (A.ell⁻¹ • A.velocity.field t (A.ell • x))).coprod (A.frame.field t x)

theorem packetPosition_hasFDerivAt (t : Icc (0 : ℝ) A.T) (ht : (t : ℝ) ∈ Ioo 0 A.T) (x : Space) :
    HasFDerivAt A.packetPosition (A.packetPositionDerivative t x) (t,x) := by
  let L : (ℝ × Space) →L[ℝ] (ℝ × Space) :=
    (fst ℝ ℝ Space).prod ((A.ell • ContinuousLinearMap.id ℝ Space).comp (snd ℝ ℝ Space))
  let J : (ℝ × Space) →L[ℝ] Space :=
    (toSpanSingleton ℝ (A.velocity.field t (A.ell • x))).coprod
      (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) (A.ell • x))
  have hp : HasFDerivAt (Function.uncurry A.realPosition) J (L (t,x)) :=
    A.realPosition_hasFDerivAt t ht (A.ell • x)
  have h := (hp.comp ((t : ℝ),x) L.hasFDerivAt).const_smul A.ell⁻¹
  have he : A.ell⁻¹ • J.comp L = A.packetPositionDerivative t x := by
    apply ContinuousLinearMap.ext
    intro v
    change A.ell⁻¹ • (v.1 • A.velocity.field t (A.ell • x) +
      (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) (A.ell • x))
        (A.ell • v.2)) = v.1 • (A.ell⁻¹ • A.velocity.field t (A.ell • x))+A.frame.field t x v.2
    rw [smul_add]
    apply congrArg₂ (fun a b : Space => a+b)
    · exact smul_comm A.ell⁻¹ v.1 _
    · rw [map_smul,smul_smul,inv_mul_cancel₀ A.ell_pos.ne',one_smul,A.frame_apply]
  rw [he] at h
  exact h

theorem packetPosition_spatial (t : Icc (0 : ℝ) A.T) (x : Space) :
    HasFDerivAt (fun y => A.packetPosition (t,y)) (A.frame.field t x) x := by
  have h := ((A.position_hasFDerivAt t (A.ell • x)).comp x
    (A.ell • ContinuousLinearMap.id ℝ Space).hasFDerivAt).const_smul A.ell⁻¹
  have he : A.ell⁻¹ •
      (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) (A.ell •
          x)).comp
        (A.ell • ContinuousLinearMap.id ℝ Space) = A.frame.field t x := by
    apply ContinuousLinearMap.ext
    intro v
    change A.ell⁻¹ •
      (ContinuousLinearMap.id ℝ Space+fderiv ℝ (A.displacement.field t : Space → Space) (A.ell • x))
        (A.ell • v)=A.frame.field t x v
    rw [map_smul,smul_smul,inv_mul_cancel₀ A.ell_pos.ne',one_smul,A.frame_apply]
  rw [he] at h
  have hf : (fun y => A.packetPosition (t,y)) = (fun y => A.ell⁻¹ • A.position t (A.ell • y)) :=
    funext (A.packetPosition_apply t)
  rw [hf]
  exact h

theorem packetPosition_frame (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    A.frame.realField A.T A.T_pos.le t x =
      (fderiv ℝ A.packetPosition (t,x)).comp (inr ℝ ℝ Space) := by
  rw [(A.packetPosition_hasFDerivAt ⟨t,ht.1.le,ht.2.le⟩ ht x).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [packetPositionDerivative, comp_apply, inr_apply, coprod_apply, toSpanSingleton_apply,
      zero_smul, zero_add]
  simp only [SmoothTimeField.realField,EulerVolterraConvolution.extendPath,
    projIcc_of_mem A.T_pos.le ⟨ht.1.le,ht.2.le⟩]

theorem packetPosition_frame_eventually (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    (fun q : ℝ × Space => A.frame.realField A.T A.T_pos.le q.1 q.2) =ᶠ[𝓝 (t,x)]
      fun q => (fderiv ℝ A.packetPosition q).comp (inr ℝ ℝ Space) := by
  filter_upwards [(continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)] with q hq
  exact A.packetPosition_frame q.1 hq q.2

theorem packetPosition_time (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    fderiv ℝ A.packetPosition (t,x) (1,0) =
      A.ell⁻¹ • A.velocity.field ⟨t,ht.1.le,ht.2.le⟩ (A.ell • x) := by
  rw [(A.packetPosition_hasFDerivAt ⟨t,ht.1.le,ht.2.le⟩ ht x).fderiv]
  simp only [packetPositionDerivative,coprod_apply,toSpanSingleton_apply,one_smul,map_zero,add_zero]

theorem packetInverse_left (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hYX : ∀ t x, Y t (A.position t x) = x) (q : ℝ × Space) :
    A.packetInverse Y (q.1,A.packetPosition q)=q.2 := by
  change A.ell⁻¹ • Y (projIcc 0 A.T A.T_pos.le q.1)
    (A.ell • (A.ell⁻¹ • A.position (projIcc 0 A.T A.T_pos.le q.1) (A.ell • q.2)))=q.2
  rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul,hYX,
    smul_smul,inv_mul_cancel₀ A.ell_pos.ne',one_smul]

theorem packetInverse_right (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hXY : ∀ t x, A.position t (Y t x) = x) (q : ℝ × Space) :
    A.packetPosition (q.1,A.packetInverse Y q)=q.2 := by
  change A.ell⁻¹ • A.position (projIcc 0 A.T A.T_pos.le q.1)
    (A.ell • (A.ell⁻¹ • Y (projIcc 0 A.T A.T_pos.le q.1) (A.ell • q.2)))=q.2
  rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul,hXY,
    smul_smul,inv_mul_cancel₀ A.ell_pos.ne',one_smul]

theorem packetInverse_joint_continuous (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hY : Continuous (Function.uncurry Y)) : Continuous (A.packetInverse Y) :=
  (hY.comp (((show Continuous (projIcc 0 A.T A.T_pos.le) from continuous_projIcc).comp
      continuous_fst).prodMk
    (continuous_snd.const_smul A.ell))).const_smul A.ell⁻¹

/-- Frame equiv, given by `ContinuousLinearEquiv.equivOfInverse (A.frame.field t x)
(A.inverse.field t x) (A.inverse_left t x) (A.inverse_right t x)`. -/
def frameEquiv (t : Icc (0 : ℝ) A.T) (x : Space) : Space ≃L[ℝ] Space :=
  ContinuousLinearEquiv.equivOfInverse (A.frame.field t x) (A.inverse.field t x)
    (A.inverse_left t x) (A.inverse_right t x)

/-- Packet lift, given by `(q.1,A.packetPosition q)`. -/
def packetLift (q : ℝ × Space) : ℝ × Space := (q.1,A.packetPosition q)
/-- Packet inverse lift, given by `(q.1,A.packetInverse Y q)`. -/
def packetInverseLift (Y : Icc (0 : ℝ) A.T → Space → Space) (q : ℝ × Space) : ℝ × Space :=
  (q.1,A.packetInverse Y q)

theorem packetLift_hasFDerivAt (t : Icc (0 : ℝ) A.T) (ht : (t : ℝ) ∈ Ioo 0 A.T) (x : Space) :
    HasFDerivAt A.packetLift
      (timeLiftEquiv (A.frameEquiv t x) (A.ell⁻¹ • A.velocity.field t (A.ell •
          x))).toContinuousLinearMap
      (t,x) := by
  have h := hasFDerivAt_fst.prodMk (A.packetPosition_hasFDerivAt t ht x)
  have he : (fst ℝ ℝ Space).prod (A.packetPositionDerivative t x) =
      (timeLiftEquiv (A.frameEquiv t x) (A.ell⁻¹ • A.velocity.field t (A.ell •
          x))).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext rfl
    rfl
  rw [he] at h
  exact h

theorem packetInverseLift_contDiffAt_two (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hXY : ∀ t x, A.position t (Y t x) = x)
    (hY : Continuous (Function.uncurry Y))
    (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    ContDiffAt ℝ 2 (A.packetInverseLift Y) (t,x) := by
  let y := A.packetInverse Y (t,x)
  apply EulerSmoothImplicitLift.contDiffAt_of_identity
    (A.packetInverseLift Y) A.packetLift id (t,x) 2 (by norm_num)
    ((continuous_fst.prodMk (A.packetInverse_joint_continuous Y hY)).continuousAt)
    (contDiffAt_fst.prodMk (A.packetPosition_contDiffAt_two t ht y))
    contDiff_id.contDiffAt
    (timeLiftEquiv (A.frameEquiv ⟨t,ht.1.le,ht.2.le⟩ y)
      (A.ell⁻¹ • A.velocity.field ⟨t,ht.1.le,ht.2.le⟩ (A.ell • y)))
  · exact A.packetLift_hasFDerivAt ⟨t,ht.1.le,ht.2.le⟩ ht y
  · intro q
    change (q.1,A.packetPosition (q.1,A.packetInverse Y q))=q
    apply Prod.ext
    · rfl
    · exact A.packetInverse_right Y hXY q

end EulerParentPacketFrames.Parent
