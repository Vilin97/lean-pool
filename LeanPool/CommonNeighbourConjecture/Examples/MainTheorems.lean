/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import LeanPool.CommonNeighbourConjecture.Examples.MainTheorems.ProofAliases

/-!
# Main theorem

The complete reader-facing interface: the four non-Mathlib definitions needed
to read the result, followed by one theorem.
-/

namespace SaxlCounterexamples.MainTheorems

/-- For every base size `B ≥ 2` and every prescribed bound there is a primitive
permutation group of degree at least that bound and base size `B` whose
generalised Saxl graph has two nonadjacent vertices with no common neighbour. -/
theorem mainTheorem (B degreeBound : Nat) (hB : 2 ≤ B) :
    ∃ P : FinitePermutationGroup,
      degreeBound ≤ Nat.card P.Point ∧
        MulAction.IsPreprimitive P.G P.Point ∧
        P.baseSize = B ∧
        ∃ x y : P.Point,
          ¬ P.saxlGraph.Adj x y ∧
          P.saxlGraph.commonNeighbors x y = ∅ :=
  Internal.mainTheorem B degreeBound hB

end SaxlCounterexamples.MainTheorems
