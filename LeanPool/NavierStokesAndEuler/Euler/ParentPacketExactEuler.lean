/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ExactLiftedGraphPressure
import LeanPool.NavierStokesAndEuler.Euler.PacketExactEulerianField
import LeanPool.NavierStokesAndEuler.Euler.PacketExactPhysicalEuler
import LeanPool.NavierStokesAndEuler.Euler.PacketExactPhysicalMomentum
public import LeanPool.NavierStokesAndEuler.Euler.ParentNormalizedGeometry
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! The actual source packet is Euler in the physical parent coordinates.
The normalized frame and inverse identities are supplied by the parent
construction, and the final physical scaling is explicit. -/

section

/-! Euler's spatial/amplitude rescaling, proved for the actual first
derivatives and scalar pressure. Time is unchanged. -/

@[expose] public section

noncomputable section

namespace EulerSpatialRescaling

open ContinuousLinearMap InnerProductSpace EulerLagrangian

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Coordinates, given by `(fst ℝ ℝ E).prod ((ell⁻¹ • ContinuousLinearMap.id ℝ E).comp (snd ℝ ℝ
E))`. -/
def coordinates (ell : ℝ) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  (fst ℝ ℝ E).prod ((ell⁻¹ • ContinuousLinearMap.id ℝ E).comp (snd ℝ ℝ E))

omit [CompleteSpace E] in
@[simp] theorem coordinates_apply (ell : ℝ) (q : ℝ × E) :
    coordinates ell q=(q.1,ell⁻¹ • q.2) := rfl

/-- Velocity, given by `ell • u (coordinates ell q)`. -/
def velocity (ell : ℝ) (u : ℝ × E → E) (q : ℝ × E) : E :=
  ell • u (coordinates ell q)

/-- Pressure, given by `ell^2*p (coordinates ell q)`. -/
def pressure (ell : ℝ) (p : ℝ × E → ℝ) (q : ℝ × E) : ℝ :=
  ell^2*p (coordinates ell q)

omit [CompleteSpace E] in
theorem velocity_hasFDerivAt (ell : ℝ) (u : ℝ × E → E) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ell q)) :
    HasFDerivAt (velocity ell u) (ell • (fderiv ℝ u (coordinates ell q)).comp (coordinates ell)) q
        := by
  have hc : HasFDerivAt (coordinates ell : ℝ × E → ℝ × E) (coordinates ell) q :=
    (coordinates (E := E) ell).hasFDerivAt
  exact (hu.hasFDerivAt.comp q hc).const_smul ell

theorem pressure_gradient (ell : ℝ) (hell : ell ≠ 0) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hp : DifferentiableAt ℝ (fun y => p (q.1, y)) (ell⁻¹ • q.2)) :
    gradient (fun y => pressure ell p (q.1,y)) q.2 =
      ell • gradient (fun y => p (q.1,y)) (ell⁻¹ • q.2) := by
  have hs := (hp.hasFDerivAt.comp q.2 (ell⁻¹ • ContinuousLinearMap.id ℝ E).hasFDerivAt).const_smul
      (ell^2)
  change HasFDerivAt (fun y => ell^2 • p (q.1,ell⁻¹ • y)) _ q.2 at hs
  apply ext_inner_right ℝ
  intro v
  change inner ℝ (gradient (fun y => ell^2 • p (q.1,ell⁻¹ • y)) q.2) v = _
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left,hs.fderiv]
  simp only [smul_apply,comp_apply,id_apply,map_smul,smul_eq_mul]
  field_simp [hell]

theorem momentumResidual_eq (ell : ℝ) (hell : ell ≠ 0)
    (u : ℝ × E → E) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ell q))
    (hp : DifferentiableAt ℝ (fun y => p (q.1, y)) (ell⁻¹ • q.2)) :
    momentumResidual (velocity ell u) (pressure ell p) q =
      ell • momentumResidual u p (coordinates ell q) := by
  unfold momentumResidual
  rw [(velocity_hasFDerivAt ell u q hu).fderiv,pressure_gradient ell hell p q hp]
  simp only [smul_apply,comp_apply]
  have hd : coordinates ell ((1 : ℝ),velocity ell u q) = (1,u (coordinates ell q)) := by
    simp only [coordinates_apply,velocity,smul_smul,inv_mul_cancel₀ hell,one_smul]
  rw [hd,← smul_add]
  rfl

theorem momentumResidual_zero (ell : ℝ) (hell : ell ≠ 0)
    (u : ℝ × E → E) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ell q))
    (hp : DifferentiableAt ℝ (fun y => p (q.1, y)) (ell⁻¹ • q.2))
    (hEuler : momentumResidual u p (coordinates ell q) = 0) :
    momentumResidual (velocity ell u) (pressure ell p) q=0 := by
  rw [momentumResidual_eq ell hell u p q hu hp,hEuler,smul_zero]

omit [CompleteSpace E] in
theorem spatial_derivative (ell : ℝ) (hell : ell ≠ 0)
    (u : ℝ × E → E) (t : ℝ) (x : E)
    (hu : DifferentiableAt ℝ (fun y => u (t, y)) (ell⁻¹ • x)) :
    fderiv ℝ (fun y => velocity ell u (t,y)) x =
      fderiv ℝ (fun y => u (t,y)) (ell⁻¹ • x) := by
  have hd := (hu.hasFDerivAt.comp x (ell⁻¹ • ContinuousLinearMap.id ℝ E).hasFDerivAt).const_smul ell
  change HasFDerivAt (fun y => velocity ell u (t,y)) _ x at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply,comp_apply,id_apply,map_smul,smul_smul,mul_inv_cancel₀ hell,one_smul]

end EulerSpatialRescaling

end
end

end

section

/-! Normalizing the actual parent Euler velocity and pressure preserves
Euler and supplies the true time law of the normalized particle map. -/

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set Filter EulerSmoothLimit EulerLagrangian
open scoped Topology

variable (A : EulerParentPacketFrames.Parent)

/-- Normalized velocity, given by `EulerSpatialRescaling.velocity A.ell⁻¹ u`. -/
def normalizedVelocity (u : ℝ × Space → Space) : ℝ × Space → Space :=
  EulerSpatialRescaling.velocity A.ell⁻¹ u

/-- Normalized pressure, given by `EulerSpatialRescaling.pressure A.ell⁻¹ p`. -/
def normalizedPressure (p : ℝ × Space → ℝ) : ℝ × Space → ℝ :=
  EulerSpatialRescaling.pressure A.ell⁻¹ p

@[simp] theorem normalizedVelocity_apply (u : ℝ × Space → Space) (q : ℝ × Space) :
    A.normalizedVelocity u q=A.ell⁻¹ • u (q.1,A.ell • q.2) := by
  simp only [normalizedVelocity, EulerSpatialRescaling.velocity,
      EulerSpatialRescaling.coordinates_apply, inv_inv]

@[simp] theorem normalizedPressure_apply (p : ℝ × Space → ℝ) (q : ℝ × Space) :
    A.normalizedPressure p q=(A.ell⁻¹)^2*p (q.1,A.ell • q.2) := by
  simp only [normalizedPressure, EulerSpatialRescaling.pressure,
      EulerSpatialRescaling.coordinates_apply, inv_inv]

theorem normalizedVelocity_differentiableAt (u : ℝ × Space → Space) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ u (t, A.ell • x)) :
    DifferentiableAt ℝ (A.normalizedVelocity u) (t,x) := by
  apply (EulerSpatialRescaling.velocity_hasFDerivAt A.ell⁻¹ u (t,x) ?_).differentiableAt
  simpa only [EulerSpatialRescaling.coordinates_apply,inv_inv] using hu

theorem normalizedPressure_differentiableAt (p : ℝ × Space → ℝ) (t : ℝ) (x : Space)
    (hp : DifferentiableAt ℝ (fun y => p (t, y)) (A.ell • x)) :
    DifferentiableAt ℝ (fun y => A.normalizedPressure p (t,y)) x := by
  have hc : DifferentiableAt ℝ (fun y => p (t,A.ell • y)) x :=
    hp.comp x (A.ell • ContinuousLinearMap.id ℝ Space).differentiableAt
  have he : (fun y => A.normalizedPressure p (t,y)) = (fun y => (A.ell⁻¹)^2*p (t,A.ell • y)) :=
    funext (fun y => A.normalizedPressure_apply p (t,y))
  rw [he]
  exact hc.const_mul ((A.ell⁻¹)^2)

theorem normalizedMomentum_zero (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
    (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ u (t, A.ell • x))
    (hp : DifferentiableAt ℝ (fun y => p (t, y)) (A.ell • x))
    (he : momentumResidual u p (t, A.ell • x) = 0) :
    momentumResidual (A.normalizedVelocity u) (A.normalizedPressure p) (t,x)=0 := by
  apply EulerSpatialRescaling.momentumResidual_zero A.ell⁻¹ (inv_ne_zero A.ell_pos.ne') u p (t,x)
  · simpa only [EulerSpatialRescaling.coordinates_apply,inv_inv] using hu
  · simpa only [inv_inv] using hp
  · simpa only [EulerSpatialRescaling.coordinates_apply,inv_inv] using he

theorem packetPosition_velocity_eventually (u : ℝ × Space → Space)
    (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x = u (t, A.position t x))
    (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    (fun q => fderiv ℝ A.packetPosition q (1,0)) =ᶠ[𝓝 (t,x)]
      fun q => A.normalizedVelocity u (q.1,A.packetPosition q) := by
  filter_upwards [(continuous_fst.tendsto (t,x)).eventually (Ioo_mem_nhds ht.1 ht.2)] with q hq
  rw [A.packetPosition_time q.1 hq q.2,A.normalizedVelocity_apply]
  have hp : A.ell • A.packetPosition q =
      A.position ⟨q.1,hq.1.le,hq.2.le⟩ (A.ell • q.2) := by
    rw [A.packetPosition_apply ⟨q.1,hq.1.le,hq.2.le⟩ q.2,
      smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  rw [hp,hvelocity]

theorem normalizedVelocity_restore (u : ℝ × Space → Space) (q : ℝ × Space) :
    EulerSpatialRescaling.velocity A.ell (A.normalizedVelocity u) q=u q := by
  simp only [EulerSpatialRescaling.velocity,EulerSpatialRescaling.coordinates_apply,
    normalizedVelocity_apply,smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul,Prod.mk.eta]

theorem normalizedVelocity_add_restore (u w : ℝ × Space → Space) (q : ℝ × Space) :
    EulerSpatialRescaling.velocity A.ell (fun r => A.normalizedVelocity u r+w r) q =
      u q + A.ell • w (q.1,A.ell⁻¹ • q.2) := by
  change A.ell • (A.normalizedVelocity u (q.1,A.ell⁻¹ • q.2)+w (q.1,A.ell⁻¹ • q.2))=_
  rw [smul_add]
  change EulerSpatialRescaling.velocity A.ell (A.normalizedVelocity u) q+_=_
  rw [A.normalizedVelocity_restore]

end EulerParentPacketFrames.Parent

end
end

end

@[expose] public section

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set Filter EulerSmoothLimit EulerLiftedGradientSpace EulerTransverseFrameCoordinates
  EulerAllOrderCorrectionData EulerAllOrderDriftCorrection EulerPacketCorrectionCoefficients
  EulerPacketPhysicalTransform EulerLagrangian
open scoped ContDiff Topology

variable (A : EulerParentPacketFrames.Parent)

/-- Packet frame, given by `A.frame.realField A.T A.T_pos.le q.1 q.2`. -/
def packetFrame (q : ℝ × Space) : Space →L[ℝ] Space :=
  A.frame.realField A.T A.T_pos.le q.1 q.2

theorem packetInverseCoordinates_differentiableAt
    (Y : Icc (0 : ℝ) A.T → Space → Space)
    (hXY : ∀ t x, A.position t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
    (t : ℝ) (ht : t ∈ Ioo 0 A.T) (x : Space) :
    DifferentiableAt ℝ (inverseCoordinates (A.packetInverse Y)) (t,x) :=
  (A.packetInverseLift_contDiffAt_two Y hXY hY t ht x).differentiableAt (by norm_num)

theorem packetInverse_time_continuous
    (Y : Icc (0 : ℝ) A.T → Space → Space) (hY : Continuous (Function.uncurry Y)) :
    Continuous (fun q : Icc (0 : ℝ) A.T × Space => A.packetInverse Y (q.1,q.2)) :=
  (A.packetInverse_joint_continuous Y hY).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (J : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hSupport : IsCompact support)

theorem packetFrame_match (t : Icc (0 : ℝ) A.T) (x : Space) :
    A.packetFrame (t,x)=((A.transverseData m hm J support hSupport)).F.field t x :=
  A.frame.realField_apply A.T A.T_pos.le t x

variable {P : ℝ} [Fact (0 < P)] {κ : ℝ} {hκ : |κ| ≤ 1}
  {Z R : FieldTower P A.T}
  (B : Budget P A.T_pos (correctionData (A.transverseData m hm J support hSupport) P κ hκ Z R))
  (residual : ApproximationResidual P A.T_pos (correctionData (A.transverseData m hm J support
      hSupport) P κ hκ Z R))

/-- Normalized exact velocity, constructed using `A.normalizedVelocity`. -/
def normalizedExactVelocity (k : ℝ) (Y : Icc (0 : ℝ) A.T → Space → Space)
    (u : ℝ × Space → Space) (q : ℝ × Space) : Space :=
  A.normalizedVelocity u q + physicalVelocity κ k m A.packetFrame ((exactPacketOfResidual P B
      residual)).rawVelocity (A.packetInverse Y) q

/-- Normalized exact pressure, given by `A.normalizedPressure p q + physicalPressure
(((exactPacketOfResidual P B residual)).rawGraphPotential k) (A.packetInverse Y) q`. -/
def normalizedExactPressure (k : ℝ) (Y : Icc (0 : ℝ) A.T → Space → Space)
    (p : ℝ × Space → ℝ) (q : ℝ × Space) : ℝ :=
  A.normalizedPressure p q + physicalPressure (((exactPacketOfResidual P B
      residual)).rawGraphPotential k) (A.packetInverse Y) q

/-- Exact packet velocity, given by `EulerSpatialRescaling.velocity A.ell
(A.normalizedExactVelocity m hm J support hSupport B residual k Y u)`. -/
def exactPacketVelocity (k : ℝ) (Y : Icc (0 : ℝ) A.T → Space → Space) (u : ℝ × Space → Space) :
    ℝ × Space → Space :=
  EulerSpatialRescaling.velocity A.ell
    (A.normalizedExactVelocity m hm J support hSupport B residual k Y u)

/-- Exact packet pressure, given by `EulerSpatialRescaling.pressure A.ell
(A.normalizedExactPressure m hm J support hSupport B residual k Y p)`. -/
def exactPacketPressure (k : ℝ) (Y : Icc (0 : ℝ) A.T → Space → Space) (p : ℝ × Space → ℝ) :
    ℝ × Space → ℝ :=
  EulerSpatialRescaling.pressure A.ell
    (A.normalizedExactPressure m hm J support hSupport B residual k Y p)

variable (k : ℝ) (hk : k * κ = 1) (Y : Icc (0 : ℝ) A.T → Space → Space)
  (hYX : ∀ t x, Y t (A.position t x) = x)
  (hXY : ∀ t x, A.position t (Y t x) = x) (hY : Continuous (Function.uncurry Y))
  (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
  (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x = u (t, A.position t x))
  (hu : ∀ t ∈ Ioo 0 A.T, ∀ x, DifferentiableAt ℝ u (t, x))
  (hp : ∀ (t : Icc (0 : ℝ) A.T) x, DifferentiableAt ℝ (fun y => p (t, y)) x)
  (heuler : ∀ t ∈ Ioo 0 A.T, ∀ x, momentumResidual u p (t, x) = 0)

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
