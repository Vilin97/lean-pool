/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.Rank

/-!
# Brill--Noether parameters

This module fixes the integer parameter conventions used throughout the
library.  For a graph of genus `g`, the Brill--Noether rectangle associated to
rank `r` and degree `d` has height `r + 1` and width `g - d + r`.

The existence predicate deliberately includes the degree equality.  This makes
duality and later arithmetic reductions insensitive to the particular divisor
chosen as a witness.
-/

@[expose] public section

namespace Utilities

/-- The width `g - d + r` of the Brill--Noether rectangle. -/
def rectangleWidth (G : CFGraph) (r d : ℤ) : ℤ :=
  genus G - d + r

/-- The Brill--Noether number `g - (r + 1) * (g - d + r)`. -/
def bnNumber (G : CFGraph) (r d : ℤ) : ℤ :=
  genus G - (r + 1) * rectangleWidth G r d

/-- There is a divisor of degree `d` and rank at least `r` on `G`. -/
def BNExists (G : CFGraph) (r d : ℤ) : Prop :=
  ∃ D : CFDiv G, deg D = d ∧ rank G D ≥ r

/-- The degree complementary to `d` with respect to the canonical divisor. -/
def dualDegree (G : CFGraph) (d : ℤ) : ℤ :=
  2 * genus G - 2 - d

/-- The dual rank `g - d + r - 1`. -/
def dualRank (G : CFGraph) (r d : ℤ) : ℤ :=
  rectangleWidth G r d - 1

end Utilities
