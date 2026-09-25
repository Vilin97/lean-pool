/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.OnceMarked

/-!
# Definitions specific to Section 6

The existing `OnceMarkedBNExistence` is the *existence* side of the
once-marked Brill--Noether conjecture: every Young diagram of size at most the
genus occurs.  Section 6 instead uses the opposite, upper-census property:
every Young diagram that occurs has size at most the genus.  The paper calls
that property a once-marked Brill--Noether general graph.
-/

namespace Bananas

open Utilities

/-- Paper source: Definition 1.9, used throughout Section 6. (Definition 1.7
is the once-marked divisor census, `OnceMarkedCensusContains`, above.)

A once-marked graph is Brill--Noether general when every partition in its
divisor census has size at most the genus.  `OnceMarkedCensusContains` is an
all-row, degree-independent encoding of membership in that
census, so this is a literal formalization of the paper's definition rather
than the differently directed `OnceMarkedBNExistence` predicate. -/
def OnceMarkedBrillNoetherGeneral (G : CFGraph) (v : G.V) : Prop :=
  ∀ lambda : YoungDiagram,
    OnceMarkedCensusContains G v lambda → (lambda.card : ℤ) ≤ genus G

/-- On a connected graph the upper-census definition may equivalently use the
finite normalized witness predicate.  This is the form suited to the vertex
wedge rank formula, while the definition above is the literal paper wording. -/
theorem onceMarkedBrillNoetherGeneral_iff_normalized
    {G : CFGraph} (hconn : graphConnected G) (v : G.V) :
    OnceMarkedBrillNoetherGeneral G v ↔
      ∀ lambda : YoungDiagram,
        OnceMarkedBNExists G v lambda → (lambda.card : ℤ) ≤ genus G := by
  constructor
  · intro h lambda hExists
    apply h lambda
    exact (onceMarkedCensusContains_iff_onceMarkedBNExists hconn v lambda).mpr hExists
  · intro h lambda hCensus
    apply h lambda
    exact (onceMarkedCensusContains_iff_onceMarkedBNExists hconn v lambda).mp hCensus

end Bananas
