/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentNormalizedEuler
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactEulerianField

@[expose] public section

/-! The actual source packet is Euler in the physical parent coordinates.
The normalized frame and inverse identities are supplied by the parent
construction, and the final physical scaling is explicit. -/

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set Filter EulerSmoothLimit EulerLiftedGradientSpace EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketPhysicalTransform EulerLagrangian
open scoped ContDiff Topology

variable (A : EulerParentPacketFrames.Parent)

def packetFrame (q : ℝ × Space) : Space →L[ℝ] Space :=
  A.frame.realField A.T A.T_pos.le q.1 q.2

theorem packetInverseCoordinates_differentiableAt
    (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hXY : ∀ t x, A.position t (Y t x)=x) (hY : Continuous (Function.uncurry Y))
    (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    DifferentiableAt ℝ (inverseCoordinates (A.packetInverse Y)) (t,x) :=
  (A.packetInverseLift_contDiffAt_two Y hXY hY t ht x).differentiableAt (by norm_num)

theorem packetInverse_time_continuous
    (Y : Icc (0 : ℝ) A.T → Space → Space) (hY : Continuous (Function.uncurry Y)) :
    Continuous (fun q : Icc (0 : ℝ) A.T × Space => A.packetInverse Y (q.1,q.2)) :=
  (A.packetInverse_joint_continuous Y hY).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)


theorem packetFrame_match (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.packetFrame (t,x)=((A.transverseData m hm J support hSupport)).F.field t x :=
  A.frame.realField_apply A.T A.T_pos.le t x

variable {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos (correctionData (A.transverseData m hm J support
    hSupport) P κ hκ Z R))


def normalizedExactVelocity (k : ℝ) (Y : Icc (0 : ℝ) A.T → Space → Space)
    (u : ℝ × Space → Space) (q : ℝ × Space) : Space :=
  A.normalizedVelocity u q + physicalVelocity κ k m A.packetFrame ((exactPacketOfResidual P B
    residual)).rawVelocity (A.packetInverse Y) q

def normalizedExactPressure (k : ℝ) (Y : Icc (0 : ℝ) A.T → Space → Space)
    (p : ℝ × Space → ℝ) (q : ℝ × Space) : ℝ :=
  A.normalizedPressure p q + physicalPressure (((exactPacketOfResidual P B
    residual)).rawGraphPotential k) (A.packetInverse Y) q

def exactPacketVelocity (k : ℝ) (Y : Icc (0 : ℝ) A.T → Space → Space) (u : ℝ × Space → Space) :
    ℝ × Space → Space :=
  EulerSpatialRescaling.velocity A.ell
    (A.normalizedExactVelocity m hm J support hSupport B residual k Y u)

def exactPacketPressure (k : ℝ) (Y : Icc (0 : ℝ) A.T → Space → Space) (p : ℝ × Space → ℝ) :
    ℝ × Space → ℝ :=
  EulerSpatialRescaling.pressure A.ell
    (A.normalizedExactPressure m hm J support hSupport B residual k Y p)

variable (k : ℝ) (hk : k*κ=1) (Y : Icc (0 : ℝ) A.T → Space → Space)
  (hYX : ∀ t x, Y t (A.position t x)=x)
  (hXY : ∀ t x, A.position t (Y t x)=x) (hY : Continuous (Function.uncurry Y))
  (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
  (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x=u (t,A.position t x))
  (hu : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ u (t,x))
  (hp : ∀ (t : Icc (0 : ℝ) A.T) x, DifferentiableAt ℝ (fun y => p (t,y)) x)
  (heuler : ∀ t ∈ Ioo 0 A.T, ∀ x, momentumResidual u p (t,x)=0)

include hYX hXY hY hu in
theorem normalizedExactVelocity_differentiableAt (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    DifferentiableAt ℝ (A.normalizedExactVelocity m hm J support hSupport B residual k Y u) (t,x)
      := by
  let y := A.packetInverse Y (t,x)
  have hy : A.packetPosition (t,y)=x := A.packetInverse_right Y hXY (t,x)
  have hd := exact_source_velocity_differentiableAt (A.transverseData m hm J support hSupport)
    (exactPacketOfResidual P B residual) k A.packetFrame A.packetPosition
    (A.packetInverse Y) t ht y (A.packetInverse_left Y hYX (t,y))
    (A.packetInverseCoordinates_differentiableAt Y hXY hY t ht (A.packetPosition (t,y)))
    (A.packetPosition_contDiffAt_two t ht y) (A.packetPosition_frame_eventually t ht y)
  rw [hy] at hd
  exact (A.normalizedVelocity_differentiableAt u t x (hu t ht (A.ell • x))).add hd

include hXY hY hp hk in
theorem normalizedExactPressure_differentiableAt (t : Icc (0 : ℝ) A.T) (x : Space) :
    DifferentiableAt ℝ
      (fun y => A.normalizedExactPressure m hm J support hSupport B residual k Y p (t,y)) x := by
  have hs := exact_physicalPressure_smooth (A.transverseData m hm J support hSupport)
    (exactPacketOfResidual P B residual)
    (fun s y => A.packetPosition (s,y)) (fun s y => A.packetInverse Y (s,y))
    (fun s y => A.packetPosition_spatial s y)
    (fun s y => A.packetInverse_right Y hXY (s,y))
    (A.packetInverse_time_continuous Y hY) k hk (A.packetInverse Y) (fun _ _ => rfl) t
  exact (A.normalizedPressure_differentiableAt p t x (hp t (A.ell • x))).add
    (hs.differentiable (by simp) x)

include hYX hXY hY hvelocity hu hp heuler hk in
theorem normalizedExact_momentum (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    momentumResidual (A.normalizedExactVelocity m hm J support hSupport B residual k Y u)
      (A.normalizedExactPressure m hm J support hSupport B residual k Y p) (t,x)=0 := by
  let y := A.packetInverse Y (t,x)
  have hy : A.packetPosition (t,y)=x := A.packetInverse_right Y hXY (t,x)
  have hh := exact_source_momentum (A.transverseData m hm J support hSupport)
    (exactPacketOfResidual P B residual) k hk A.packetFrame (A.normalizedVelocity u)
    (A.normalizedPressure p) A.packetPosition (A.packetInverse Y)
    (A.packetFrame_match m hm J support hSupport) t ht y
    (fun s z => A.packetInverse_left Y hYX (s,z))
    (A.packetInverseCoordinates_differentiableAt Y hXY hY t ht (A.packetPosition (t,y)))
    (A.packetPosition_contDiffAt_two t ht y)
    (A.packetPosition_frame_eventually t ht y)
    (A.packetPosition_velocity_eventually u hvelocity t ht y)
    (A.normalizedVelocity_differentiableAt u t (A.packetPosition (t,y))
      (hu t ht (A.ell • A.packetPosition (t,y))))
    (A.normalizedPressure_differentiableAt p t (A.packetPosition (t,y))
      (hp ⟨t,ht.1.le,ht.2.le⟩ (A.ell • A.packetPosition (t,y))))
    (A.normalizedMomentum_zero u p t (A.packetPosition (t,y))
      (hu t ht (A.ell • A.packetPosition (t,y)))
      (hp ⟨t,ht.1.le,ht.2.le⟩ (A.ell • A.packetPosition (t,y)))
      (heuler t ht (A.ell • A.packetPosition (t,y))))
  rw [hy] at hh
  exact hh

include hYX hXY hY hu in
theorem exactPacketVelocity_differentiableAt (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    DifferentiableAt ℝ (A.exactPacketVelocity m hm J support hSupport B residual k Y u) (t,x) :=
  (EulerSpatialRescaling.velocity_hasFDerivAt A.ell
    (A.normalizedExactVelocity m hm J support hSupport B residual k Y u) (t,x)
    (A.normalizedExactVelocity_differentiableAt m hm J support hSupport B residual k Y
      hYX hXY hY u hu t ht (A.ell⁻¹ • x))).differentiableAt

include hYX hXY hY hvelocity hu hp heuler hk in
theorem exactPacket_momentum (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    momentumResidual (A.exactPacketVelocity m hm J support hSupport B residual k Y u)
      (A.exactPacketPressure m hm J support hSupport B residual k Y p) (t,x)=0 := by
  apply EulerSpatialRescaling.momentumResidual_zero A.ell A.ell_pos.ne'
    (A.normalizedExactVelocity m hm J support hSupport B residual k Y u)
    (A.normalizedExactPressure m hm J support hSupport B residual k Y p) (t,x)
  · exact A.normalizedExactVelocity_differentiableAt m hm J support hSupport B residual k Y
      hYX hXY hY u hu t ht (A.ell⁻¹ • x)
  · exact A.normalizedExactPressure_differentiableAt m hm J support hSupport B residual k hk Y
      hXY hY p hp ⟨t,ht.1.le,ht.2.le⟩ (A.ell⁻¹ • x)
  · exact A.normalizedExact_momentum m hm J support hSupport B residual k hk Y
      hYX hXY hY u p hvelocity hu hp heuler t ht (A.ell⁻¹ • x)

theorem exactPacketVelocity_eq_corrected (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.exactPacketVelocity m hm J support hSupport B residual k Y u (t,x) =
      A.correctedPacketVelocity B k Y (fun s y => u (s,y)) t x := by
  change EulerSpatialRescaling.velocity A.ell
    (fun q => A.normalizedVelocity u q + physicalVelocity κ k m A.packetFrame
      (exactPacketOfResidual P B residual).rawVelocity (A.packetInverse Y) q) (t,x)=_
  rw [A.normalizedVelocity_add_restore]
  exact (A.correctedPacketVelocity_eq_physical B k Y (fun s y => u (s,y)) t x).symm

end EulerParentPacketFrames.Parent
