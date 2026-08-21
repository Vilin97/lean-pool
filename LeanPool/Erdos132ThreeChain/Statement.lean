/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ThreeChain.Support
import LeanPool.Erdos132ThreeChain.HopfPannwitz

/-!
# The 3-chain support theorem

Let `X` be a finite set of points of the plane with squared diameter `D`.  This file forbids the
set of *non-diameter* squared distances of `X` from being a geometric 3-chain
`{a, 3a, 9a, …, 3 ^ (h-1) a}`, once `X` has at least thirteen points.

The lift from the five-point obstruction to arbitrary `n ≥ 13` runs through the *diameter graph*
of `X`, whose vertices are the points of `X` and whose edges join pairs at squared distance
exactly `D`.  Hopf--Pannwitz bounds that graph by `#X` edges, Caro--Wei then produces an
independent set of five points, and those five points have all ten of their squared distances
inside the chain — which `no_five_chain_finset` forbids.

Every ingredient is proved from first principles in this project: the chain-quadruple
catalogue, the five-point Gram obstruction, Caro--Wei, and Hopf--Pannwitz.  The result is
unconditional.  Of those, Hopf--Pannwitz is a supporting lemma only: the same bound already
exists in the pool as `LeanPool.Erdos132N14.diameterEdges_card_le`, and it is reproved here in
this project's model for self-containment, not offered as a new result.

There is no prior write-up to follow.  The 3-chain support statement was produced by the
author's automated research pipeline in August 2026; the cited source poses the ambient Erdős
problem and nothing more.  Section labels used in the docstrings of this development —
"chain-quadruple theorem", "five-point obstruction" — are internal names, not references to a
numbered result anywhere else.  Hopf--Pannwitz (1934) and Caro--Wei are classical statements,
but their Lean proofs here are written from scratch.
-/

namespace Erdos132ThreeChain

open Finset

/-- The set of squared distances realised by distinct points of `X` that are not the squared
diameter `D`. -/
def nonDiameterSqDists (X : Finset Point) (D : ℝ) : Set ℝ :=
  {d : ℝ | ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ sqDist p q = d ∧ d ≠ D}

/-- **The 3-chain support theorem.**  Let `n ≥ 13` and `a > 0`, and let `X` be a set of `n`
points of the plane with squared diameter `D`.  Then the set of squared distances realised by
distinct points of `X` other than `D` is never the geometric 3-chain `{a * 3 ^ j | j < h}`, for
any chain length `h`. -/
theorem nonDiameterSqDists_ne_chain {X : Finset Point} {D a : ℝ} {n h : ℕ}
    (hn : 13 ≤ n) (ha : 0 < a) (hcard : X.card = n) (hD : IsSqDiameter X D) :
    nonDiameterSqDists X D ≠ chain a h := by
  intro hsupport
  obtain ⟨S, hSX, hScard, hSind⟩ := exists_independent_five (DiameterAdj D)
    (diameterAdj_symm D) (diameterAdj_irrefl D) X (by omega) (hopfPannwitz hD)
  refine no_five_chain_finset ha hScard ?_
  intro p hp q hq hpq
  have hne : sqDist p q ≠ D := fun hEq => hSind p hp q hq ⟨hpq, hEq⟩
  have hmem : sqDist p q ∈ nonDiameterSqDists X D :=
    ⟨p, hSX hp, q, hSX hq, hpq, rfl, hne⟩
  rw [hsupport] at hmem
  obtain ⟨j, -, hj⟩ := hmem
  exact ⟨j, hj⟩

/-- The `h ≥ 2` reading of the support theorem, kept so that a statement matching the informal
phrasing "a geometric 3-chain of length at least two" is available directly.  It is a wrapper
around `nonDiameterSqDists_ne_chain`, which needs no bound on `h` at all; `_hh` is therefore
unused. -/
theorem threeChain_support_empty {X : Finset Point} {D a : ℝ} {n h : ℕ}
    (hn : 13 ≤ n) (_hh : 2 ≤ h) (ha : 0 < a) (hcard : X.card = n)
    (hD : IsSqDiameter X D)
    (hsupport : nonDiameterSqDists X D = chain a h) : False :=
  nonDiameterSqDists_ne_chain hn ha hcard hD hsupport

end Erdos132ThreeChain
