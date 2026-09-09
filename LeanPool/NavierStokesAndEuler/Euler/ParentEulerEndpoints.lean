/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentEulerSobolev

@[expose] public section

/-! The physical gradient is continuous up to the endpoints in the
actual Sobolev class. Incompressibility therefore holds at time zero
and the final time as well as in the open Euler interval. -/

noncomputable section

namespace EulerParentPacketFrames.SobolevData

open Set EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerMeanSobolevBoundedField EulerMeanCoefficients
open scoped Topology

variable {A : Parent} {E : Evolution A} (S : SobolevData E)

include S

theorem spatial_derivative_continuous (x : Space) :
    Continuous (fun t : Icc (0 : ℝ) A.T => fderiv ℝ (fun y => E.velocity (t,y)) x) := by
  let D := coefficientPath (fun t => (S.velocity t).derivative)
    (continuous_jetLp_derivative S.velocity S.velocity_continuous)
  have hc : Continuous (fun t => D.field t x) :=
    (BoundedContinuousFunction.evalCLM ℝ x).continuous.comp D.field.continuous
  apply hc.congr
  intro t
  rw [show D.field t x=fderiv ℝ (S.velocity t).field x from
    coefficientPath_apply _ _ t x]
  rw [funext (S.velocity_match t)]

theorem divergence_closed (t : Icc (0 : ℝ) A.T) (x : Space) :
    divergence (fun y => E.velocity (t,y)) x=0 := by
  let f : ℝ → ℝ := fun s => coordinateTrace
    (fderiv ℝ (fun y => E.velocity (projIcc 0 A.T A.T_pos.le s,y)) x)
  have hf : Continuous f := coordinateTrace.continuous.comp
    ((S.spatial_derivative_continuous x).comp continuous_projIcc)
  have he : EqOn f (fun _ => 0) (Ioo 0 A.T) := by
    intro s hs
    simpa only [f,projIcc_of_mem A.T_pos.le ⟨hs.1.le,hs.2.le⟩,
      coordinateTrace_eq_linearTrace,divergence] using E.divergence_zero s hs x
  have ht : (t : ℝ) ∈ closure (Ioo (0 : ℝ) A.T) := by
    rw [closure_Ioo A.T_pos.ne]
    exact t.property
  have hh := he.closure hf continuous_const ht
  simpa only [f,projIcc_of_mem A.T_pos.le t.property,
    coordinateTrace_eq_linearTrace,divergence] using hh

end EulerParentPacketFrames.SobolevData
