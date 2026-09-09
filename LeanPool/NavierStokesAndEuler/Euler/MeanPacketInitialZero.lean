/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketContract

@[expose] public section

/-! The actual localized mean initial condition vanishes when the source
boundary coefficient L is zero. -/

noncomputable section


namespace EulerMeanPacketProvider

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanBoundary
  EulerPacketProfileRecursion

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem vector_initial_zero (hL : D.L = 0) (x : Space) (θ : ℝ) :
    G.vector (0,(x,θ)) = 0 := by
  have h := G.initial_vector_ae θ
  have he : D.L • (boundaryOperator (scaledCutoff D.ℓ D.ℓ_pos))
      (G.solution.label 0 : L2) = 0 := by
    exact (congrArg (fun c : ℝ => c • (boundaryOperator (scaledCutoff D.ℓ D.ℓ_pos))
      (G.solution.label 0 : L2)) hL).trans (zero_smul ℝ _)
  rw [he] at h
  have hz : (fun y => G.vector (0,(y,θ))) =ᵐ[volume] (fun _ => (0 : Space)) :=
    h.trans (Lp.coeFn_zero Space 2 volume)
  have hc : Continuous (fun y => G.vector (0,(y,θ))) :=
    (G.vector_spatial_smooth 0).continuous.comp (continuous_id.prodMk continuous_const)
  exact congrFun (Measure.eq_of_ae_eq hz hc continuous_const) x

end Forcing

theorem meanSolve_zero_initial (D : Data) (hL : D.L = 0) (raw : VectorField)
    (h : Nonempty (Forcing D raw)) (x : Space) (θ : ℝ) :
    (meanSolve D raw).1 (0,(x,θ)) = 0 := by
  rw [meanSolve_of_admissible D raw h]
  exact (Classical.choice h).vector_initial_zero hL x θ

end EulerMeanPacketProvider
