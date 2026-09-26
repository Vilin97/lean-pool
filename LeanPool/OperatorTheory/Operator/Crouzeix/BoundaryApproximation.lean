/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import LeanPool.OperatorTheory.Operator.Crouzeix.ApproximationSupNorm
public import LeanPool.OperatorTheory.Operator.Crouzeix.BoundaryMaximum
public import LeanPool.OperatorTheory.Operator.Crouzeix.CompactThickeningApprox

/-!
# Polynomial sup-norms on approximating boundaries

The explicit open thickenings from `SmoothApprox.lean` and the closed
thickenings from `CompactThickeningApprox.lean` use the same radius at every
stage.  The closure of the open thickening is exactly the closed thickening.
The maximum-modulus transfer in `BoundaryMaximum.lean` therefore identifies
the polynomial sup-norm on the open-stage frontier with the norm on the
compact control set.

Consequently, for a compact target, these frontier sup-norms converge to the
sup-norm on the target.  This is the scalar limit needed when a
smooth-boundary estimate is passed through the compact exhaustion.

## Main declarations

* `polynomialSupNorm_frontier_convexThickeningApprox_eq_compactThickeningApprox`
  identifies the boundary and compact-stage norms.
* `tendsto_polynomialSupNorm_frontier_convexThickeningApprox_atTop` proves
  convergence of the boundary norms to the target norm.
-/

@[expose] public section

open Filter Polynomial Set

private theorem smoothApproxRadius_pos_boundary (n : ℕ) :
    0 < smoothApproxRadius n := by
  unfold smoothApproxRadius
  positivity

/-- For a bounded set, the polynomial sup-norm on the frontier of its open
thickening equals the norm on the closed thickening at the same radius. -/
theorem polynomialSupNorm_frontier_convexThickeningApprox_eq_compactThickeningApprox
    (p : Polynomial ℂ) {K : Set ℂ} (hK : Bornology.IsBounded K) (n : ℕ) :
    polynomialSupNorm p (frontier (convexThickeningApprox K n)) =
      polynomialSupNorm p (compactThickeningApprox K n) := by
  have hbounded : Bornology.IsBounded (convexThickeningApprox K n) := by
    exact hK.thickening
  rw [← polynomialSupNorm_closure_eq_frontier_of_isBounded p hbounded]
  congr 1
  exact closure_thickening (smoothApproxRadius_pos_boundary n) K

/-- For a compact target, polynomial sup-norms on the frontiers of the
explicit open thickenings converge to the target sup-norm. -/
theorem tendsto_polynomialSupNorm_frontier_convexThickeningApprox_atTop
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) :
    Tendsto
      (fun n ↦ polynomialSupNorm p (frontier (convexThickeningApprox K n))) atTop
      (nhds (polynomialSupNorm p K)) := by
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · subst K
    simpa only [convexThickeningApprox, Metric.thickening_empty, frontier_empty,
      polynomialSupNorm, Set.mem_empty_iff_false, Real.iSup_of_isEmpty,
      Real.iSup_const_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · obtain ⟨hanti, hcompact, hnonempty, hinter⟩ :=
      compactThickeningApprox_spec K hK hKne
    have ht := tendsto_polynomialSupNorm_atTop_of_antitone_isCompact p
      (compactThickeningApprox K) hanti hcompact hnonempty
    rw [hinter] at ht
    simpa only [
      polynomialSupNorm_frontier_convexThickeningApprox_eq_compactThickeningApprox
        p hK.isBounded] using ht

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
