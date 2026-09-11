/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerState
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketExactEuler
import LeanPool.NavierStokesAndEuler.Euler.PacketExactPhysicalEuler
import LeanPool.NavierStokesAndEuler.Euler.PacketExactEulerianField

/-! The same exact packet that constructs the next particle map supplies
its physical Euler evolution. All new flow and Euler laws are proved
from the old evolution and the actual correction solver. -/

section

/-! The actual scalar pressure of the corrected source packet has the
constructed continuous physical pressure force, at every time. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketPhysicalTransform EulerLagrangian
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup Space` instance to shorten typeclass synthesis. -/
local instance instParentPacketExactPressure1 : NormedAddCommGroup Space := inferInstance
/-- Cache the standard `NormedSpace ℝ Space` instance to shorten typeclass synthesis. -/
local instance instParentPacketExactPressure2 : NormedSpace ℝ Space := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instParentPacketExactPressure3 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instParentPacketExactPressure4 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

variable (A : EulerParentPacketFrames.Parent)

theorem transformedForce_continuous
    (Y force g : Icc (0 : ℝ) A.T → Space → Space)
    (hY : Continuous (Function.uncurry Y)) (hforce : Continuous (Function.uncurry force))
    (hg : Continuous (Function.uncurry g)) :
    Continuous (fun q : Icc (0 : ℝ) A.T × Space => force q.1 q.2 +
      A.ell • (A.inverse.field q.1 (A.ell⁻¹ • Y q.1 q.2)).adjoint
        (g q.1 (A.ell⁻¹ • Y q.1 q.2))) := by
  let r : Icc (0 : ℝ) A.T × Space → Space := fun q => A.ell⁻¹ • Y q.1 q.2
  have hr : Continuous r := hY.const_smul A.ell⁻¹
  have hI₀ : Continuous (fun q : Icc (0 : ℝ) A.T × Space => A.inverse.field q.1 q.2) := by
    have hc : Continuous (fun q : Icc (0 : ℝ) A.T × Space => ((q.1 : ℝ),q.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have h := (A.inverse.realField_joint_continuous A.T A.T_pos.le).comp
      hc
    simpa only [Function.comp_def,Function.uncurry_def,SmoothTimeField.realField_apply] using h
  have hmap : Continuous (fun q : Icc (0 : ℝ) A.T × Space => (q.1,r q)) :=
    continuous_fst.prodMk hr
  have hIn := hI₀.comp (f := fun q : Icc (0 : ℝ) A.T × Space => (q.1,r q)) hmap
  have ha : Continuous (fun L : Space →L[ℝ] Space => L.adjoint) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Space) (F := Space)).continuous
  have hI := ha.comp (f := fun q : Icc (0 : ℝ) A.T × Space => A.inverse.field q.1 (r q)) hIn
  have hP := hg.comp (f := fun q : Icc (0 : ℝ) A.T × Space => (q.1,r q)) hmap
  have hterm := (hI.clm_apply hP).const_smul A.ell
  exact hforce.add hterm

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)

variable {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos (correctionData (A.transverseData m hm J support
      hSupport) P κ hκ Z R))

/-- Exact packet force, constructed using `force`. -/
def exactPacketForce (k : ℝ) (Y force : Icc (0 : ℝ) A.T → Space → Space)
    (t : Icc (0 : ℝ) A.T) (x : Space) : Space :=
  force t x + A.ell • (A.inverse.field t (A.ell⁻¹ • Y t x)).adjoint
    (((exactPacketOfResidual P B residual)).graphPressure k t (A.ell⁻¹ • Y t x))

theorem exactPacketForce_continuous (k : ℝ) (Y force : Icc (0 : ℝ) A.T → Space → Space)
    (hY : Continuous (Function.uncurry Y)) (hforce : Continuous (Function.uncurry force)) :
    Continuous (Function.uncurry (A.exactPacketForce m hm J support hSupport B residual k Y force))
        := by
  exact A.transformedForce_continuous Y force
    ((exactPacketOfResidual P B residual).graphPressure k) hY hforce
    ((exactPacketOfResidual P B residual).graphPressure_joint_continuous k)

variable (k : ℝ) (hk : k * κ = 1) (Y : Icc (0 : ℝ) A.T → Space → Space)
  (hXY : ∀ t x, A.position t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
  (p : ℝ × Space → ℝ) (force : Icc (0 : ℝ) A.T → Space → Space)
  (hp : ∀ (t : Icc (0 : ℝ) A.T) x, DifferentiableAt ℝ (fun y => p (t, y)) x)
  (hgradient : ∀ (t : Icc (0 : ℝ) A.T) x, gradient (fun y => p (t, y)) x = force t x)

include hk hXY hY hp hgradient in
theorem normalizedExactPressure_gradient (t : Icc (0 : ℝ) A.T) (x : Space) :
    gradient (fun y => A.normalizedExactPressure m hm J support hSupport B residual k Y p (t,y)) x =
      A.ell⁻¹ • force t (A.ell • x) +
        (A.inverse.field t (A.packetInverse Y (t,x))).adjoint
          (((exactPacketOfResidual P B residual)).graphPressure k t (A.packetInverse Y (t,x))) := by
  have hs := exact_physicalPressure_smooth (A.transverseData m hm J support hSupport)
      (exactPacketOfResidual P B residual)
    (fun s y => A.packetPosition (s,y)) (fun s y => A.packetInverse Y (s,y))
    (fun s y => A.packetPosition_spatial s y)
    (fun s y => A.packetInverse_right Y hXY (s,y))
    (A.packetInverse_time_continuous Y hY) k hk (A.packetInverse Y) (fun _ _ => rfl) t
  have hg := exact_physicalPressure_gradient (A.transverseData m hm J support hSupport)
      (exactPacketOfResidual P B residual)
    (fun s y => A.packetPosition (s,y)) (fun s y => A.packetInverse Y (s,y))
    (fun s y => A.packetPosition_spatial s y)
    (fun s y => A.packetInverse_right Y hXY (s,y))
    (A.packetInverse_time_continuous Y hY) k hk (A.packetInverse Y) (fun _ _ => rfl) t x
  have hn := EulerSpatialRescaling.pressure_gradient A.ell⁻¹ (inv_ne_zero A.ell_pos.ne') p (t,x)
    (by simpa only [inv_inv] using hp t (A.ell • x))
  simp only [inv_inv] at hn
  change gradient (fun y => A.normalizedPressure p (t,y)) x =
    A.ell⁻¹ • gradient (fun y => p (t,y)) (A.ell • x) at hn
  change gradient (fun y => A.normalizedPressure p (t,y) +
    physicalPressure (((exactPacketOfResidual P B residual)).rawGraphPotential k) (A.packetInverse
        Y) (t,y)) x=_
  erw [gradient_add _ _ x (A.normalizedPressure_differentiableAt p t x (hp t (A.ell • x)))
    (hs.differentiable (by simp) x),hn,hg,hgradient]
  change A.ell⁻¹ • force t (A.ell • x) + κ •
    (A.inverse.field t (A.packetInverse Y (t,x))).adjoint
      (((exactPacketOfResidual P B residual)).pressure.pointField t
          (EulerGraphPressurePotential.cylinderGraph P k m (A.packetInverse Y (t,x)))) = _
  apply congrArg (fun z => A.ell⁻¹ • force t (A.ell • x) + z)
  exact ((A.inverse.field t (A.packetInverse Y (t,x))).adjoint.map_smul κ
    ((exactPacketOfResidual P B residual).pressure.pointField t
      (EulerGraphPressurePotential.cylinderGraph P k m (A.packetInverse Y (t,x))))).symm

include hk hXY hY hp hgradient in
theorem exactPacketPressure_gradient (t : Icc (0 : ℝ) A.T) (x : Space) :
    gradient (fun y => A.exactPacketPressure m hm J support hSupport B residual k Y p (t,y)) x =
      A.exactPacketForce m hm J support hSupport B residual k Y force t x := by
  have hg := EulerSpatialRescaling.pressure_gradient A.ell A.ell_pos.ne'
    (A.normalizedExactPressure m hm J support hSupport B residual k Y p) (t,x)
    (A.normalizedExactPressure_differentiableAt m hm J support hSupport B residual k hk Y hXY hY p
        hp t
      (A.ell⁻¹ • x))
  change gradient (fun y => EulerSpatialRescaling.pressure A.ell
    (A.normalizedExactPressure m hm J support hSupport B residual k Y p) (t,y)) x=_
  rw [hg,A.normalizedExactPressure_gradient m hm J support hSupport B residual k hk Y hXY hY
    p force hp hgradient t (A.ell⁻¹ • x)]
  have hx : A.ell • (A.ell⁻¹ • x)=x := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  have hy : A.packetInverse Y (t,A.ell⁻¹ • x)=A.ell⁻¹ • Y t x := by
    simp only [packetInverse,projIcc_of_mem A.T_pos.le t.property,hx]
  rw [hx,hy,smul_add,smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  rfl

end EulerParentPacketFrames.Parent

end
end

end

section

/-! Incompressibility of the actual corrected parent velocity. The
normalized packet uses the parent's genuine determinant-one Jacobian,
and the final physical rescaling preserves divergence exactly. -/

@[expose] public section

noncomputable section

namespace EulerSpatialRescaling

open EulerSmoothLimit

theorem divergence_eq (ell : ℝ) (hell : ell ≠ 0)
    (u : ℝ × Space → Space) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y => u (t, y)) (ell⁻¹ • x)) :
    divergence (fun y => velocity ell u (t,y)) x =
      divergence (fun y => u (t,y)) (ell⁻¹ • x) := by
  rw [divergence_eq_trace,spatial_derivative ell hell u t x hu]
  rfl

end EulerSpatialRescaling

namespace EulerParentPacketFrames.Parent

open Set Filter EulerSmoothLimit EulerLiftedGradientSpace EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketPhysicalTransform EulerLagrangian
open scoped ContDiff Topology

variable (A : EulerParentPacketFrames.Parent)

theorem normalizedVelocity_divergence (u : ℝ × Space → Space) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y => u (t, y)) (A.ell • x)) :
    divergence (fun y => A.normalizedVelocity u (t,y)) x =
      divergence (fun y => u (t,y)) (A.ell • x) := by
  have h := EulerSpatialRescaling.divergence_eq A.ell⁻¹ (inv_ne_zero A.ell_pos.ne')
    u t x (by simpa only [inv_inv] using hu)
  simpa only [normalizedVelocity,inv_inv] using h

theorem packetPosition_spatial_frame (t : Icc (0 : ℝ) A.T) (x : Space) :
    fderiv ℝ (fun y => A.packetPosition (t,y)) x=A.packetFrame (t,x) := by
  rw [(A.packetPosition_spatial t x).fderiv]
  exact (A.frame.realField_apply A.T A.T_pos.le t x).symm

theorem packetFrame_det (t : Icc (0 : ℝ) A.T) (x : Space) :
    (EulerPacketPiola.operatorMatrix (A.packetFrame (t,x))).det=1 := by
  change (EulerPacketPiola.operatorMatrix (A.frame.realField A.T A.T_pos.le t x)).det=1
  rw [A.frame.realField_apply A.T A.T_pos.le t x]
  exact A.frame_det t x

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (k : ℝ) (hk : k * κ = 1) (Y : Icc (0 : ℝ) A.T → Space → Space)
  (hYX : ∀ t x, Y t (A.position t x) = x)
  (hXY : ∀ t x, A.position t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
  (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
  (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x = u (t, A.position t x))
  (hu : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ u (t, x))
  (hp : ∀ (t : Icc (0 : ℝ) A.T) x, DifferentiableAt ℝ (fun y => p (t, y)) x)
  (heuler : ∀ t ∈ Ioo 0 A.T, ∀ x, momentumResidual u p (t, x) = 0)
  (hdiv : ∀ t ∈ Ioo 0 A.T, ∀ x, divergence (fun y => u (t, y)) x = 0)

include hYX hXY hY hvelocity hu hp heuler hdiv hk in
theorem normalizedExact_euler (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    momentumResidual (A.normalizedExactVelocity m hm J support hSupport B residual k Y u)
      (A.normalizedExactPressure m hm J support hSupport B residual k Y p) (t,x)=0 ∧
    divergence (fun y => A.normalizedExactVelocity m hm J support hSupport B residual k Y u (t,y))
        x=0 := by
  let y := A.packetInverse Y (t,x)
  have hy : A.packetPosition (t,y)=x := A.packetInverse_right Y hXY (t,x)
  have hd : divergence (fun z => A.normalizedVelocity u (t,z)) (A.packetPosition (t,y))=0 := by
    rw [A.normalizedVelocity_divergence u t (A.packetPosition (t,y))]
    · exact hdiv t ht _
    · exact (hu t ht _).comp _ (hasFDerivAt_prodMk_right t _).differentiableAt
  have hh := exact_source_euler (A.transverseData m hm J support hSupport)
    (exactPacketOfResidual P B residual) k hk A.packetFrame (A.normalizedVelocity u)
    (A.normalizedPressure p) A.packetPosition (A.packetInverse Y)
    (A.packetFrame_match m hm J support hSupport) t ht y
    (fun s z => A.packetInverse_left Y hYX (s,z))
    (A.packetInverseCoordinates_differentiableAt Y hXY hY t ht (A.packetPosition (t,y)))
    (A.packetPosition_contDiffAt_two t ht y)
    (A.packetPosition_frame_eventually t ht y)
    (A.packetPosition_velocity_eventually u hvelocity t ht y)
    (A.packetPosition_spatial_frame ⟨t,ht.1.le,ht.2.le⟩)
    (A.packetFrame_det ⟨t,ht.1.le,ht.2.le⟩)
    (A.normalizedVelocity_differentiableAt u t (A.packetPosition (t,y))
      (hu t ht (A.ell • A.packetPosition (t,y))))
    (A.normalizedPressure_differentiableAt p t (A.packetPosition (t,y))
      (hp ⟨t,ht.1.le,ht.2.le⟩ (A.ell • A.packetPosition (t,y))))
    (A.normalizedMomentum_zero u p t (A.packetPosition (t,y))
      (hu t ht (A.ell • A.packetPosition (t,y)))
      (hp ⟨t,ht.1.le,ht.2.le⟩ (A.ell • A.packetPosition (t,y)))
      (heuler t ht (A.ell • A.packetPosition (t,y)))) hd
  rw [hy] at hh
  exact hh

include hYX hXY hY hvelocity hu hp heuler hdiv hk in
theorem exactPacket_euler (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    momentumResidual (A.exactPacketVelocity m hm J support hSupport B residual k Y u)
      (A.exactPacketPressure m hm J support hSupport B residual k Y p) (t,x)=0 ∧
    divergence (fun y => A.exactPacketVelocity m hm J support hSupport B residual k Y u (t,y)) x=0
        := by
  refine ⟨A.exactPacket_momentum m hm J support hSupport B residual k hk Y
    hYX hXY hY u p hvelocity hu hp heuler t ht x,?_⟩
  have hd : DifferentiableAt ℝ
      (fun y => A.normalizedExactVelocity m hm J support hSupport B residual k Y u (t,y))
      (A.ell⁻¹ • x) :=
    (A.normalizedExactVelocity_differentiableAt m hm J support hSupport B residual k Y
      hYX hXY hY u hu t ht (A.ell⁻¹ • x)).comp _
        (hasFDerivAt_prodMk_right t _).differentiableAt
  change divergence (fun y => EulerSpatialRescaling.velocity A.ell
    (A.normalizedExactVelocity m hm J support hSupport B residual k Y u) (t,y)) x=0
  rw [EulerSpatialRescaling.divergence_eq A.ell A.ell_pos.ne' _ t x hd]
  exact (A.normalizedExact_euler m hm J support hSupport B residual k hk Y
    hYX hXY hY u p hvelocity hu hp heuler hdiv t ht (A.ell⁻¹ • x)).2

end EulerParentPacketFrames.Parent

end
end

end

section

/-! The new parent is the particle map of the actual corrected Euler
velocity, and its acceleration is minus the actual constructed pressure
force. Both matches are derived from the existing parent law and Euler. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow EulerLagrangian

variable (A : EulerParentPacketFrames.Parent)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)

variable {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos (correctionData (A.transverseData m hm J support
      hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z = V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A = B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k * κ = 1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)
  (Y : Icc (0 : ℝ) A.T → Space → Space)
  (hYX : ∀ t x, Y t (A.position t x) = x)
  (hXY : ∀ t x, A.position t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
  (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
  (force : Icc (0 : ℝ) A.T → Space → Space)
  (hforce : Continuous (Function.uncurry force))
  (hgradient : ∀ (t : Icc (0 : ℝ) A.T) x, gradient (fun y => p (t, y)) x = force t x)
  (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x = u (t, A.position t x))
  (hu : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ u (t, x))
  (hp : ∀ (t : Icc (0 : ℝ) A.T) x, DifferentiableAt ℝ (fun y => p (t, y)) x)
  (heuler : ∀ t ∈ Ioo 0 A.T, ∀ x, momentumResidual u p (t, x) = 0)

include hV hG hYX hvelocity in
theorem child_velocity_exact (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).velocity.field t x =
      A.exactPacketVelocity m hm J support hSupport B residual k Y u
        (t,(A.child G k m hgraph nextEll hnext hnext1).position t x) := by
  have h := A.child_velocity_corrected B V hV G hG k hgraph nextEll hnext hnext1
    Y (fun s y => u (s,y)) hYX hvelocity t x
  exact h.trans
    (A.exactPacketVelocity_eq_corrected m hm J support hSupport B residual k Y u t
      ((A.child G k m hgraph nextEll hnext hnext1).position t x)).symm

include hV hG hk hYX hXY hY hforce hgradient hvelocity hu hp heuler in
theorem child_acceleration_exact (t : Icc (0 : ℝ) A.T) (x : Space) :
    (A.child G k m hgraph nextEll hnext hnext1).acceleration.field t x =
      -A.exactPacketForce m hm J support hSupport B residual k Y force t
        ((A.child G k m hgraph nextEll hnext hnext1).position t x) := by
  apply (A.child G k m hgraph nextEll hnext hnext1).acceleration_physical_of_euler
    (A.exactPacketVelocity m hm J support hSupport B residual k Y u)
    (A.exactPacketPressure m hm J support hSupport B residual k Y p)
    (A.exactPacketForce m hm J support hSupport B residual k Y force)
    (A.exactPacketForce_continuous m hm J support hSupport B residual k Y force hY hforce)
    (A.exactPacketPressure_gradient m hm J support hSupport B residual k hk Y hXY hY p force hp
        hgradient)
    (A.child_velocity_exact m hm J support hSupport B residual V hV G hG k hgraph
      nextEll hnext hnext1 Y hYX u hvelocity)
    (A.exactPacketVelocity_differentiableAt m hm J support hSupport B residual k Y hYX hXY hY u hu)
    (A.exactPacket_momentum m hm J support hSupport B residual k hk Y hYX hXY hY u p hvelocity hu
        hp heuler)
    t x

end EulerParentPacketFrames.Parent

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set EulerSmoothLimit EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerGraphInvariantFlow

variable {A : Parent} (E : Evolution A)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  {raw : EulerPacketProfileRecursion.VectorField}
  (V : EulerPacketCylinderField.Field P A.T raw) (hV : Z = V.toFieldTower)
  (G : EulerPhysicalGraphFlowBounds.Data P A.T) (hG : G.A = B.liftedPacketCoefficient P V)
  (k : ℝ) (hk : k * κ = 1) (hgraph : ∀ t q, graphConstraint k m (G.A.field t q) = 0)
  (nextEll : ℝ) (hnext : 0 < nextEll) (hnext1 : nextEll ≤ 1)

/-- Child, bundling `inverse`, `velocity`, `pressure`, `force` and the required compatibility
proofs. -/
def child : Evolution (A.child G k m hgraph nextEll hnext hnext1) where
  inverse := E.inverse.child G k m hgraph nextEll hnext hnext1
  velocity := A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field E.velocity
  pressure := A.exactPacketPressure m hm J support hSupport B residual k E.inverse.field E.pressure
  force := A.exactPacketForce m hm J support hSupport B residual k E.inverse.field E.force
  force_continuous := A.exactPacketForce_continuous m hm J support hSupport B residual k
    E.inverse.field E.force E.inverse.continuous E.force_continuous
  velocity_match := A.child_velocity_exact m hm J support hSupport B residual V hV G hG k
    hgraph nextEll hnext hnext1 E.inverse.field E.inverse.left_inverse E.velocity E.velocity_match
  velocity_differentiable := A.exactPacketVelocity_differentiableAt m hm J support hSupport B
    residual k E.inverse.field E.inverse.left_inverse E.inverse.right_inverse E.inverse.continuous
    E.velocity E.velocity_differentiable
  pressure_differentiable t x := by
    have hd := A.normalizedExactPressure_differentiableAt m hm J support hSupport B residual
      k hk E.inverse.field E.inverse.right_inverse E.inverse.continuous E.pressure
      E.pressure_differentiable t (A.ell⁻¹ • x)
    exact (hd.comp x ((A.ell⁻¹ • ContinuousLinearMap.id ℝ Space).differentiableAt)).const_mul
        (A.ell^2)
  pressure_gradient := A.exactPacketPressure_gradient m hm J support hSupport B residual
    k hk E.inverse.field E.inverse.right_inverse E.inverse.continuous E.pressure E.force
    E.pressure_differentiable E.pressure_gradient
  momentum_zero := A.exactPacket_momentum m hm J support hSupport B residual k hk E.inverse.field
    E.inverse.left_inverse E.inverse.right_inverse E.inverse.continuous E.velocity E.pressure
    E.velocity_match E.velocity_differentiable E.pressure_differentiable E.momentum_zero
  divergence_zero t ht x :=
    (A.exactPacket_euler m hm J support hSupport B residual k hk E.inverse.field
      E.inverse.left_inverse E.inverse.right_inverse E.inverse.continuous E.velocity E.pressure
      E.velocity_match E.velocity_differentiable E.pressure_differentiable E.momentum_zero
      E.divergence_zero t ht x).2

@[simp] theorem child_velocity :
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext
        hnext1).velocity =
      A.exactPacketVelocity m hm J support hSupport B residual k E.inverse.field E.velocity := rfl

@[simp] theorem child_pressure :
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext
        hnext1).pressure =
      A.exactPacketPressure m hm J support hSupport B residual k E.inverse.field E.pressure := rfl

@[simp] theorem child_force :
    (E.child m hm J support hSupport B residual V hV G hG k hk hgraph nextEll hnext hnext1).force =
      A.exactPacketForce m hm J support hSupport B residual k E.inverse.field E.force := rfl

end EulerParentPacketFrames.Evolution
