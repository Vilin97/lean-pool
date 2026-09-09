/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import Mathlib.Tactic.Positivity.Finset

/-! Exact bounded observations of genuine higher-order Bochner representatives. -/

@[expose] public section


noncomputable section

namespace EulerTimeLp

open MeasureTheory Set EulerVolterraConvolution

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Composition of actual bounded spatial maps is composition of their genuine Bochner actions. -/
theorem compLpL_comp (T : ℝ) (A : E →L[ℝ] F) (B : F →L[ℝ] G) (u : TimeLp T E) :
    B.compLpL 2 (timeMeasure T) (A.compLpL 2 (timeMeasure T) u) =
      (B.comp A).compLpL 2 (timeMeasure T) u := by
  apply Lp.ext
  filter_upwards [B.coeFn_compLpL (A.compLpL 2 (timeMeasure T) u), A.coeFn_compLpL u,
    (B.comp A).coeFn_compLpL u] with t h1 h2 h3
  rw [h1, h2, h3]
  rfl

/-- A continuous lower-order representative and an actual higher-order time field have identical
bounded observations when the operators agree on restriction. -/
theorem observation_time_eq (T : ℝ) (hT : 0 ≤ T) (A : E →L[ℝ] F) (D : F →L[ℝ] G) (W : E →L[ℝ] G)
    (hDA : ∀ x, D (A x) = W x) (u : TimeLp T E) (f : C(Icc (0 : ℝ) T, F))
    (hf : (fun t => A (u t)) =ᵐ[timeMeasure T] extendPath T hT f) :
    pathLp T hT (D.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) = W.compLpL 2 (timeMeasure T) u := by
  apply Lp.ext
  filter_upwards [pathLp_ae T hT (D.compLeftContinuous ℝ (Icc (0 : ℝ) T) f), W.coeFn_compLpL u, hf]
    with t h1 h2 h3
  exact h1.trans (((congrArg D h3.symm).trans (hDA (u t))).trans h2.symm)

end EulerTimeLp
