/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.RareDistanceFields.OctagonalRational
import LeanPool.RareDistanceFields.PureTranscendental

/-!
# Rare-distance bounds over specified coordinate fields

Source: url:https://www.erdosproblems.com/132
Authors: Egor Lyfar
Status: verified
Main declarations: `LeanPool.RareDistanceFields.bounds`
Tags: discrete-geometry, distance-multiplicity, arithmetic-coordinates
MSC: 52C10, 11R11, 05C35
-/

/-!
# Quantitative rare-distance bounds over specified coordinate fields

For `n` distinct planar points, a rare distance is a positive occurring Euclidean
length with at most `n` unordered realizing pairs. This project proves `n ≤ 2^r`,
where `r` counts all such distances, for coordinates in `ℚ(√2)` and, separately,
in a real purely transcendental extension `ℚ(T)` of the rationals. The two
settings are not combined into an arbitrary algebraic extension of `ℚ(T)`.

The quadratic-field proof constructs a binary descent model with a decreasing
integer height separate from actual Euclidean length. Exact polynomial
specialization transfers all distance equalities for the transcendental case.
The resulting bounds give two rare distances for `n ≥ 3` and at least `k`
when `n ≥ 2^k`. All multiplicities count complete unordered distance classes.

## Source roles and formal dependencies

Erdős problem 132 (https://www.erdosproblems.com/132) motivates these restricted
statements; the unrestricted conjecture is not proved here. Woodall
(DOI 10.1016/0097-3165(73)90020-4) and Madore (arXiv:1509.07023) provide
rational and quadratic-field coloring background, not the claimed
rare-distance bounds. The bounds and specialization are proved in this
project, without a claim that they are new mathematics. The Euclidean
angular-order lemmas are reused from `LeanPool.Erdos132N14.HopfPannwitzGeometry`;
no published-input hypothesis or conditional n=14 theorem is imported.
-/

namespace LeanPool.RareDistanceFields

open Classical in
/-- The common quantitative bound, with the two coordinate regimes stated separately. -/
theorem bounds {σ V : Type*} [Fintype V] :
    (∀ x : V → ℂ, Function.Injective x → OctagonalRational.QuadraticCoordinates x →
      Fintype.card V ≤ 2 ^ (OctagonalRational.rareDistances x).card) ∧
    (∀ (f : PureTranscendental.Functions σ →ₐ[ℚ] ℝ)
      (x : V → PureTranscendental.Functions σ × PureTranscendental.Functions σ),
      Function.Injective (PureTranscendental.point f x) →
        Fintype.card V ≤ 2 ^ (DistancePattern.rareDistances
          (PureTranscendental.point f x)).card) :=
  ⟨fun x hx h => OctagonalRational.card_le_pow_rareDistances x hx h,
    fun f x hx => PureTranscendental.card_le_pow_rare f x hx⟩

end LeanPool.RareDistanceFields
