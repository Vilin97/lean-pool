/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketExactEuler
public import LeanPool.NavierStokesAndEuler.Euler.PacketExactPhysicalEuler

@[expose] public section

/-! Incompressibility of the actual corrected parent velocity. The
normalized packet uses the parent's genuine determinant-one Jacobian,
and the final physical rescaling preserves divergence exactly. -/

noncomputable section

namespace EulerSpatialRescaling

open EulerSmoothLimit

theorem divergence_eq (ell : ℝ) (hell : ell ≠ 0)
    (u : ℝ × Space → Space) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (fun y => u (t,y)) (ell⁻¹ • x)) :
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
    (hu : DifferentiableAt ℝ (fun y => u (t,y)) (A.ell • x)) :
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
  (m : Space) (hm : ‖m‖=1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)
  {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos
    (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (k : ℝ) (hk : k*κ=1) (Y : Icc (0 : ℝ) A.T → Space → Space)
  (hYX : ∀ t x, Y t (A.position t x)=x)
  (hXY : ∀ t x, A.position t (Y t x)=x) (hY : Continuous (Function.uncurry Y))
  (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
  (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x=u (t,A.position t x))
  (hu : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ u (t,x))
  (hp : ∀ (t : Icc (0 : ℝ) A.T) x, DifferentiableAt ℝ (fun y => p (t,y)) x)
  (heuler : ∀ t ∈ Ioo 0 A.T, ∀ x, momentumResidual u p (t,x)=0)
  (hdiv : ∀ t ∈ Ioo 0 A.T, ∀ x, divergence (fun y => u (t,y)) x=0)

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
