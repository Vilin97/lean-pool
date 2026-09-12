/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import Mathlib.Algebra.Order.Ring.Star

/-! Exact bounded-map compatibility for the actual continuous-path to Bochner L² inclusion. -/

@[expose] public section


noncomputable section

namespace EulerTimeLp

open MeasureTheory Set EulerVolterraConvolution
open scoped Topology ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Applying a bounded spatial map commutes exactly with the genuine L² time embedding. -/
theorem pathLp_map (T : ℝ) (hT : 0 ≤ T) (A : E →L[ℝ] F) (f : C(Icc (0 : ℝ) T, E)) :
    A.compLpL 2 (timeMeasure T) (pathLp T hT f) =
      pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (pathLp T hT f), pathLp_ae T hT f,
    pathLp_ae T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) f)] with t h1 h2 h3
  rw [h1, h2, h3]
  rfl

/-- A strong Bochner limit is identified by the limit of any actual bounded spatial restriction. -/
theorem limit_restriction_eq (T : ℝ) (hT : 0 ≤ T) (A : E →L[ℝ] F)
    (f : ℕ → C(Icc (0 : ℝ) T, E)) (g : C(Icc (0 : ℝ) T, F)) (U : TimeLp T E)
    (hf : Filter.Tendsto (fun n => pathLp T hT (f n)) Filter.atTop (𝓝 U))
    (hg : Filter.Tendsto (fun n => A.compLeftContinuous ℝ (Icc (0 : ℝ) T) (f n))
      Filter.atTop (𝓝 g)) :
    A.compLpL 2 (timeMeasure T) U = pathLp T hT g := by
  have hA := (A.compLpL 2 (timeMeasure T)).continuous.continuousAt.tendsto.comp hf
  have hB := pathLp_tendsto T hT _ g hg
  have he : (fun n => A.compLpL 2 (timeMeasure T) (pathLp T hT (f n))) =
      fun n => pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) (f n)) :=
    funext (fun n => pathLp_map T hT A (f n))
  change Filter.Tendsto (fun n => A.compLpL 2 (timeMeasure T) (pathLp T hT (f n))) Filter.atTop _
      at hA
  rw [he] at hA
  exact tendsto_nhds_unique hA hB

/-- The limiting restriction equality identifies genuine pointwise fields almost everywhere in time.
-/
theorem limit_restriction_ae (T : ℝ) (hT : 0 ≤ T) (A : E →L[ℝ] F)
    (f : ℕ → C(Icc (0 : ℝ) T, E)) (g : C(Icc (0 : ℝ) T, F)) (U : TimeLp T E)
    (hf : Filter.Tendsto (fun n => pathLp T hT (f n)) Filter.atTop (𝓝 U))
    (hg : Filter.Tendsto (fun n => A.compLeftContinuous ℝ (Icc (0 : ℝ) T) (f n))
      Filter.atTop (𝓝 g)) :
    (fun t => A (U t)) =ᵐ[timeMeasure T] extendPath T hT g := by
  have he := limit_restriction_eq T hT A f g U hf hg
  have hA := A.coeFn_compLpL U
  rw [he] at hA
  exact hA.symm.trans (pathLp_ae T hT g)

end EulerTimeLp
