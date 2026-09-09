/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentNormalizedGeometry
public import LeanPool.NavierStokesAndEuler.Euler.EulerSpatialRescaling

@[expose] public section

/-! Normalizing the actual parent Euler velocity and pressure preserves
Euler and supplies the true time law of the normalized particle map. -/

noncomputable section

namespace EulerParentPacketFrames.Parent

open Set Filter EulerSmoothLimit EulerLagrangian
open scoped Topology

variable (A : EulerParentPacketFrames.Parent)

def normalizedVelocity (u : ℝ × Space → Space) : ℝ × Space → Space :=
  EulerSpatialRescaling.velocity A.ell⁻¹ u

def normalizedPressure (p : ℝ × Space → ℝ) : ℝ × Space → ℝ :=
  EulerSpatialRescaling.pressure A.ell⁻¹ p

@[simp] theorem normalizedVelocity_apply (u : ℝ × Space → Space) (q : ℝ × Space) :
    A.normalizedVelocity u q=A.ell⁻¹ • u (q.1,A.ell • q.2) := by
  simp only [normalizedVelocity,EulerSpatialRescaling.velocity,EulerSpatialRescaling.coordinates_apply,inv_inv]

@[simp] theorem normalizedPressure_apply (p : ℝ × Space → ℝ) (q : ℝ × Space) :
    A.normalizedPressure p q=(A.ell⁻¹)^2*p (q.1,A.ell • q.2) := by
  simp only [normalizedPressure,EulerSpatialRescaling.pressure,EulerSpatialRescaling.coordinates_apply,inv_inv]

theorem normalizedVelocity_differentiableAt (u : ℝ × Space → Space) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ u (t,A.ell • x)) :
    DifferentiableAt ℝ (A.normalizedVelocity u) (t,x) := by
  apply (EulerSpatialRescaling.velocity_hasFDerivAt A.ell⁻¹ u (t,x) ?_).differentiableAt
  simpa only [EulerSpatialRescaling.coordinates_apply,inv_inv] using hu

theorem normalizedPressure_differentiableAt (p : ℝ × Space → ℝ) (t : ℝ) (x : Space)
    (hp : DifferentiableAt ℝ (fun y => p (t,y)) (A.ell • x)) :
    DifferentiableAt ℝ (fun y => A.normalizedPressure p (t,y)) x := by
  have hc : DifferentiableAt ℝ (fun y => p (t,A.ell • y)) x :=
    hp.comp x (A.ell • ContinuousLinearMap.id ℝ Space).differentiableAt
  have he : (fun y => A.normalizedPressure p (t,y)) = (fun y => (A.ell⁻¹)^2*p (t,A.ell • y)) :=
    funext (fun y => A.normalizedPressure_apply p (t,y))
  rw [he]
  exact hc.const_mul ((A.ell⁻¹)^2)

theorem normalizedMomentum_zero (u : ℝ × Space → Space) (p : ℝ × Space → ℝ)
    (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ u (t,A.ell • x))
    (hp : DifferentiableAt ℝ (fun y => p (t,y)) (A.ell • x))
    (he : momentumResidual u p (t,A.ell • x)=0) :
    momentumResidual (A.normalizedVelocity u) (A.normalizedPressure p) (t,x)=0 := by
  apply EulerSpatialRescaling.momentumResidual_zero A.ell⁻¹ (inv_ne_zero A.ell_pos.ne') u p (t,x)
  · simpa only [EulerSpatialRescaling.coordinates_apply,inv_inv] using hu
  · simpa only [inv_inv] using hp
  · simpa only [EulerSpatialRescaling.coordinates_apply,inv_inv] using he

theorem packetPosition_velocity_eventually (u : ℝ × Space → Space)
    (hvelocity : ∀ (t : Icc (0 : ℝ) A.T) x, A.velocity.field t x=u (t,A.position t x))
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
