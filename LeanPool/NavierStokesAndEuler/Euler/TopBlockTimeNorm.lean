/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlocks
import LeanPool.NavierStokesAndEuler.Euler.SobolevTopBlocks

/-! Strong time-space completion controlled by genuine finite spatial derivative blocks. -/

@[expose] public section


noncomputable section

namespace EulerTopBlockTimeNorm

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevWordBlocks EulerSobolevTopBlocks
open scoped Topology

/-- Integration preserves a finite quadratic norm comparison between bounded spatial observations.
-/
theorem pathLp_quadratic_bound {X Y Z I : Type*} [Fintype I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : X →L[ℝ] Y) (B : I → X →L[ℝ] Z)
    (hb : ∀ x, ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ∑ i, ‖B i x‖ ^ 2)
    (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, X)) :
    ‖pathLp T hT u‖^2 ≤ ‖pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 +
      ∑ i, ‖pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 := by
  have hu := extendPath_continuous T hT u
  have hA : Continuous (fun t => ‖A (extendPath T hT u t)‖^2) := (A.continuous.comp hu).norm.pow 2
  have hB : ∀ i, Continuous (fun t => ‖B i (extendPath T hT u t)‖^2) :=
    fun i => ((B i).continuous.comp hu).norm.pow 2
  have hsum : Continuous (fun t => ∑ i, ‖B i (extendPath T hT u t)‖^2) := continuous_finsetSum _
      (fun i _ => hB i)
  have h := intervalIntegral.integral_mono_on hT ((hu.norm.pow 2).intervalIntegrable (μ := volume)
      0 T)
    ((hA.add hsum).intervalIntegrable (μ := volume) 0 T) (fun t _ => hb (extendPath T hT u t))
  change (∫ t in (0 : ℝ)..T, ‖extendPath T hT u t‖^2) ≤
    ∫ t in (0 : ℝ)..T, ‖A (extendPath T hT u t)‖^2 + ∑ i, ‖B i (extendPath T hT u t)‖^2 at h
  rw [intervalIntegral.integral_add (hA.intervalIntegrable (μ := volume) 0 T)
    (hsum.intervalIntegrable (μ := volume) 0 T),
    intervalIntegral.integral_finsetSum (fun i _ => (hB i).intervalIntegrable (μ := volume) 0 T)]
        at h
  simp only [pathLp_norm_sq]
  exact h

/-- All actual order-q H² blocks and the lower H^(q+1) norm control the full H^(q+2) time norm. -/
theorem top_blocks_time_norm (period : ℝ) [Fact (0 < period)] (q : ℕ)
    (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, SobolevSpace period (2 + q))) :
    ‖pathLp T hT u‖^2 ≤
      ‖pathLp T hT ((restrictOperator period (by
          omega : 1+q ≤ 2+q)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 +
      ∑ w : Fin q → Fin 4, ‖pathLp T hT ((wordBlock period 2 q w).compLeftContinuous ℝ (Icc (0 : ℝ)
          T) u)‖^2 :=
  pathLp_quadratic_bound _ _ (top_blocks_norm_sq period q) T hT u

end EulerTopBlockTimeNorm
