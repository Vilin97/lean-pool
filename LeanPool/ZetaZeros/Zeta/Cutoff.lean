/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import LeanPool.ZetaZeros.Zeta.Defs

/-!
# Cutoffs exist

The source asks for a smooth even cutoff, valued in `[0,1]`, supported in `(-1/2, 1/2)` and
identically one on `|x| ≤ 1/2 - delta`. That is exactly Mathlib's `ContDiffBump` centred at the
origin with inner radius `1/2 - delta` and outer radius `1/2`: the bump is radial, so evenness
comes free from `ContDiffBump.neg`, and the two radius conditions are what `0 < delta < 1/4`
supplies.
-/

@[expose] public section

namespace ZetaZeros

open Metric

/-- **Cutoffs exist.** -/
@[zz_tag "lem_cutoff_exists"]
theorem exists_isCutoff {delta : ℝ} (h0 : 0 < delta) (h4 : delta < 1 / 4) :
    ∃ psi : ℝ → ℝ, IsCutoff delta psi := by
  have hrIn : (0 : ℝ) < 1 / 2 - delta := by linarith
  have hlt : (1 : ℝ) / 2 - delta < 1 / 2 := by linarith
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2 - delta, 1 / 2, hrIn, hlt⟩
  refine ⟨fun x => f x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact f.contDiff
  · intro x hx
    refine f.zero_of_le_dist ?_
    simpa [f, Real.dist_eq] using hx
  · intro x
    exact f.neg x
  · intro x
    exact f.nonneg
  · intro x
    exact f.le_one
  · intro x hx
    refine f.one_of_mem_closedBall ?_
    simpa [f, mem_closedBall, Real.dist_eq] using hx

end ZetaZeros
