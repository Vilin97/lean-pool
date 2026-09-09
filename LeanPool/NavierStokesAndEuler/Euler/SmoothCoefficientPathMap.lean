/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPath
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Bounded linear images of genuine uniformly smooth coefficient paths. -/

@[expose] public section


noncomputable section

namespace EulerMeanCoefficients.SmoothCoefficientPath

open ContinuousLinearMap EulerSmoothLimit
open scoped BoundedContinuousFunction ContDiff

variable {K V W : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Apply a fixed bounded linear map to the actual field and all its literal derivative jets. -/
def map (L : V →L[ℝ] W) (A : SmoothCoefficientPath K V) : SmoothCoefficientPath K W where
  field := mapCoefficientPath L A.field
  smooth t := L.contDiff.comp (A.smooth t)
  jet n := mapCoefficientPath (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin n => Space) V W L) (A.jet n)
  jet_eq n t x := by
    change L.compContinuousMultilinearMap (A.jet n t x) =
      iteratedFDeriv ℝ n (fun y : Space => L (A.field t y)) x
    rw [A.jet_eq]
    exact (L.iteratedFDeriv_comp_left ((A.smooth t).contDiffAt (x := x)) (i := n) (by simp)).symm

@[simp] theorem map_apply (L : V →L[ℝ] W) (A : SmoothCoefficientPath K V) (t : K) (x : Space) :
    (map L A).field t x = L (A.field t x) := rfl

/-- Contraction of coefficient values preserves every actual spatial derivative bound. -/
theorem map_derivative_bound (L : V →L[ℝ] W) (hL : ‖L‖ ≤ 1) (A : SmoothCoefficientPath K V)
    (n : ℕ) (C : ℝ)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C) (t : K) (x : Space) :
    ‖iteratedFDeriv ℝ n ((map L A).field t : Space → W) x‖ ≤ C := by
  have h := L.norm_iteratedFDeriv_comp_left ((A.smooth t).contDiffAt (x := x)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans (by
      simpa only [one_mul] using hb t x))

end EulerMeanCoefficients.SmoothCoefficientPath
