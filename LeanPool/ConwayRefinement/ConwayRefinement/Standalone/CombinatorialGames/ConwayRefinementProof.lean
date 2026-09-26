/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.ConwayRefinement
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.Support.ConwayNormalForm
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Refinement.ConwayRefinement
/-!
# Proof of Conway's refinement conjecture

The native omnific-integer theorem is transported to Conway's cut definition.
-/

public noncomputable section

universe u

namespace ConwayRefinement.Standalone.Oz.ConwayConjecture

/-- Every equality of products of cut-defined omnific integers has an omnific four-factor
refinement. -/
@[blueprint "thm:conway-refinement"
  (phase := "Surreal numbers and omnific integers")
  (title := "Conway's refinement theorem for omnific integers")
  (statement := /--
    Let $a,b,c,d$ be surreal numbers satisfying Conway's cut equation
    $x=\{x-1\mid x+1\}$.  If $ab=cd$, then there are surreal numbers
    $e,f,g,h$, each satisfying the same cut equation, such that
    \[
      a=ef,\qquad b=gh,\qquad c=eg,\qquad d=fh.
    \]
  -/)
  (proof := /--
    By \ref{thm:conway-cut-subring-equivalence}, Conway's cut-defined
    statement is equivalent to the refinement property of the omnific-integer
    subring. Apply \ref{thm:omnific-integer-refinement-property}.
  -/)
  (highlight)]
theorem proof : ConwayRefinement.Standalone.Oz.ConwayConjecture.{u} := by
  rw [ConwayRefinement.Standalone.Oz.conwayConjecture_iff_native]
  exact Surreal.OmnificInteger.conwayRefinement

end ConwayRefinement.Standalone.Oz.ConwayConjecture
