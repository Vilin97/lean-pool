/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Polynomial sup norms on a domain boundary

The maximum-modulus principle identifies the polynomial sup norm on the
closure of a bounded planar set with the sup norm on its frontier.  A separate
closure-invariance lemma identifies this compact-closure norm with the norm on
the original set.
This is the analytic bridge between compact closure stages in an exhaustion
and the frontier-controlled smooth-domain bounds in `GeneralSymmetrized.lean`.

The boundedness hypothesis is explicit.  Although every intended smooth
convex approximation stage is bounded, `SmoothJordanDomain` currently stores
only a compact parametrized frontier and does not expose boundedness of its
carrier as a field.

## Main declarations

* `polynomialSupNorm_closure_eq_frontier_of_isBounded` -- the general
  maximum-modulus identity;
* `polynomialSupNorm_closure_carrier_eq_frontier` -- the identity specialized
  to the closure of a bounded smooth Jordan carrier;
* `polynomialSupNorm_closure_of_isBounded` -- closure invariance on bounded
  sets;
* `polynomialSupNorm_carrier_eq_frontier` -- the direct carrier/frontier
  identity for a bounded smooth Jordan carrier.
-/
import Mathlib.Analysis.Complex.AbsMax
import LeanPool.OperatorTheory.Operator.Crouzeix.ApproximationSupNorm
import LeanPool.OperatorTheory.Operator.Crouzeix.GeneralSymmetrized

open Complex Polynomial Set

private theorem polynomialSupNorm_eq_of_isMaxOn_boundaryMaximum
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) {z : ℂ}
    (hz : z ∈ K) (hmax : IsMaxOn (fun w => ‖p.eval w‖) K z) :
    polynomialSupNorm p K = ‖p.eval z‖ := by
  apply le_antisymm
  · unfold polynomialSupNorm
    refine Real.iSup_le (fun w => ?_) (norm_nonneg _)
    exact Real.iSup_le (fun hw => hmax hw) (norm_nonneg _)
  · exact norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz

/-- On a bounded planar set, a polynomial's sup norm on the closure equals
its sup norm on the frontier.  The empty-set case is included. -/
theorem polynomialSupNorm_closure_eq_frontier_of_isBounded
    (p : Polynomial ℂ) {U : Set ℂ} (hU : Bornology.IsBounded U) :
    polynomialSupNorm p (closure U) = polynomialSupNorm p (frontier U) := by
  rcases U.eq_empty_or_nonempty with rfl | hUne
  · rw [closure_empty, frontier_empty]
  have hclosure : IsCompact (closure U) := hU.isCompact_closure
  have hfrontier : IsCompact (frontier U) :=
    hclosure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨z, hz, hmax⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm hU hUne p.differentiable.diffContOnCl
  rw [polynomialSupNorm_eq_of_isMaxOn_boundaryMaximum p hclosure
      (frontier_subset_closure hz) hmax,
    polynomialSupNorm_eq_of_isMaxOn_boundaryMaximum p hfrontier hz
      (hmax.on_subset frontier_subset_closure)]

/-- For a bounded smooth Jordan carrier, polynomial sup norms on its closure
and parametrized frontier agree exactly. -/
theorem polynomialSupNorm_closure_carrier_eq_frontier
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier) :
    polynomialSupNorm p (closure Omega.carrier) =
      polynomialSupNorm p (frontier Omega.carrier) :=
  polynomialSupNorm_closure_eq_frontier_of_isBounded p hbounded

/-- Taking the closure of a bounded planar set does not change a polynomial's
sup norm.  The empty-set case is included. -/
theorem polynomialSupNorm_closure_of_isBounded
    (p : Polynomial ℂ) {X : Set ℂ} (hX : Bornology.IsBounded X) :
    polynomialSupNorm p (closure X) = polynomialSupNorm p X := by
  have hcompact : IsCompact (closure X) := hX.isCompact_closure
  have hB : BddAbove ((fun z => ‖p.eval z‖) '' X) :=
    (bddAbove_norm_eval_image_of_isCompact p hcompact).mono
      (Set.image_mono subset_closure)
  have hsub : closure X ⊆ {z | ‖p.eval z‖ ≤ polynomialSupNorm p X} := by
    apply closure_minimal
    · intro z hz
      exact norm_eval_le_polynomialSupNorm p hB hz
    · exact isClosed_le p.continuous.norm continuous_const
  apply le_antisymm
  · rw [show polynomialSupNorm p (closure X) =
      ⨆ z ∈ closure X, ‖p.eval z‖ from rfl]
    refine Real.iSup_le (fun z => ?_) (polynomialSupNorm_nonneg p X)
    exact Real.iSup_le (fun hz => hsub hz) (polynomialSupNorm_nonneg p X)
  · exact polynomialSupNorm_mono_of_isCompact p subset_closure hcompact

/-- For a bounded smooth Jordan carrier, polynomial sup norms on the carrier
and its parametrized frontier agree exactly. -/
theorem polynomialSupNorm_carrier_eq_frontier
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier) :
    polynomialSupNorm p Omega.carrier =
      polynomialSupNorm p (frontier Omega.carrier) := by
  rw [← polynomialSupNorm_closure_of_isBounded p hbounded]
  exact polynomialSupNorm_closure_carrier_eq_frontier Omega p hbounded

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
