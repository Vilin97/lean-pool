/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketPhysicalCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Lagrangian

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
