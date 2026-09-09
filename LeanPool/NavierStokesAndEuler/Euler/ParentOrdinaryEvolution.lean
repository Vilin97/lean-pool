/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerSobolev
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference

/-! The actual particle-parent Euler solution supplies the ordinary
Sobolev evolution used by the H³ stability estimate. The solenoidal
constraint at the endpoints follows by L² continuity from the interior. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames.SobolevData

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSolenoidal  EulerOrdinarySobolev
open scoped ContDiff

variable {A : Parent} {E : EulerParentPacketFrames.Evolution A} (S : SobolevData E)

theorem velocity_solenoidal (t : Icc (0 : ℝ) A.T) : (S.velocity t).toLp ∈ solenoidalSpace := by
  let f : ℝ → EulerMeanSolenoidal.L2 := fun r => (S.velocity (projIcc 0 A.T A.T_pos.le r)).toLp
  have hc : Continuous f := (continuous_toLp S.velocity (S.velocity_continuous 0)).comp
    continuous_projIcc
  have hclosed : IsClosed (solenoidalSpace : Set EulerMeanSolenoidal.L2) :=
    gradientSpace.isClosed_orthogonal
  have hi : Ioo (0 : ℝ) A.T ⊆ f ⁻¹' (solenoidalSpace : Set EulerMeanSolenoidal.L2) := by
    intro r hr
    change (S.velocity (projIcc 0 A.T A.T_pos.le r)).toLp ∈ solenoidalSpace
    rw [projIcc_of_mem A.T_pos.le ⟨hr.1.le,hr.2.le⟩]
    apply smooth_mem_solenoidal _ (S.velocity _).smooth (S.velocity _).memLp
    intro x
    have he : (S.velocity ⟨r,hr.1.le,hr.2.le⟩).field=(fun y => E.velocity (r,y)) :=
      funext (fun y => (S.velocity_match ⟨r,hr.1.le,hr.2.le⟩ y).symm)
    rw [he]
    exact E.divergence_zero r hr x
  have hh := closure_minimal hi (hclosed.preimage hc)
  have ht : (t : ℝ) ∈ closure (Ioo (0 : ℝ) A.T) := by
    rw [closure_Ioo A.T_pos.ne]
    exact t.property
  have hm := hh ht
  change (S.velocity (projIcc 0 A.T A.T_pos.le (t : ℝ))).toLp ∈ solenoidalSpace at hm
  simpa only [projIcc_of_mem A.T_pos.le t.property] using hm

/-- Ordinary evolution, bundling `velocity`, `pressureForce`, `velocity_continuous`,
`pressure_continuous` and the required compatibility proofs. -/
def ordinaryEvolution : EulerOrdinarySobolev.Evolution A.T A.T_pos.le where
  velocity := S.velocity
  pressureForce := S.force
  velocity_continuous := S.velocity_continuous
  pressure_continuous := S.force_continuous
  solenoidal := S.velocity_solenoidal
  gradient t := by
    have hg : ∀ x, (S.force t).field x=gradient (fun y => E.pressure (t,y)) x :=
      fun x => ((E.pressure_gradient t x).trans (S.force_match t x)).symm
    exact gradient_mem (S.force t) _
      (potential_smooth (S.force t) _ (E.pressure_differentiable t) hg) hg
  time_law := EulerSmoothEulerEvolution.pointwise_time_derivative_of_classical A.T A.T_pos.le
    S.velocity S.force E.velocity E.pressure S.velocity_match
    (fun t x => (E.pressure_gradient t x).trans (S.force_match t x))
    E.velocity_differentiable E.momentum_zero

end EulerParentPacketFrames.SobolevData
