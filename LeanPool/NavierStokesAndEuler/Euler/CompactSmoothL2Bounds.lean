/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2GevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffDifferenceBound
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Compact support turns actual uniform tensor bounds into the ordinary
L² tensor bounds used in the label Sobolev estimates. -/

@[expose] public section


noncomputable section

namespace EulerLpTranslation.SmoothL2Field

open Set MeasureTheory EulerSmoothLimit EulerGevrey

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasJetBound_of_support_sup (A : SmoothL2Field V) (K : Set Space)
    (hK : volume K ≠ ⊤) (hs : tsupport A.field ⊆ K)
    (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hb : HasSupBound A.field C R) :
    A.HasJetBound (C*(volume K).toReal^(1/2 : ℝ)) R := by
  intro n
  have hzero : ∀ x ∉ K, iteratedFDeriv ℝ n A.field x=0 := by
    intro x hx
    by_contra hn
    exact hx (hs (support_iteratedFDeriv_subset n hn))
  have h := EulerMeanBoundary.lpNorm_le_bound_volume (iteratedFDeriv ℝ n A.field)
    (A.integrable n).aestronglyMeasurable K hK (C*R^n*(n.factorial : ℝ)^2)
    (by positivity) (hb n) hzero 2
  rw [norm_jetLp,toReal_eLpNorm (A.integrable n).aestronglyMeasurable]
  convert h using 1
  norm_num
  ring

end EulerLpTranslation.SmoothL2Field
