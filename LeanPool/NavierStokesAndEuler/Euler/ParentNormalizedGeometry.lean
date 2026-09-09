/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentLagrangianEuler
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalChildPacketMatch
import LeanPool.NavierStokesAndEuler.Euler.SmoothImplicitLift
import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldSecondJoint

/-! The actual normalized parent coordinates used by the packet. Joint
regularity, the frame, and inverse regularity are derived from the parent
time laws and the literal inverse map. -/

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
