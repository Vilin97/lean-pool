/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08ChamberOne
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08ChamberTwo
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow08ChamberThree

/-!
# AR row 08, assembled

Atanasov--Ranganathan's *seventh* genus-five family.  The paper draws three of
the four sign patterns of `(|e4| - |e3|, |e7| - |e2|)`; the fourth is the image
of the third under the core automorphism `sigma = (0 6)(1 7)(4 5)`, so the row
needs three chamber proofs and one orbit transport.

* chamber 1 (`|e4| ≤ |e3|`, `|e7| ≤ |e2|`) -- `GenusFiveRow08ChamberOne`,
  a `ConfigurationThree` pair on the stem plus two equal-arm banana pairs;
* chamber 2 (`|e3| ≤ |e4|`, `|e2| ≤ |e7|`) -- `GenusFiveRow08ChamberTwo`,
  the chipped triangle plus two equal-arm banana pairs;
* chamber 3 (`|e3| ≤ |e4|`, `|e7| ≤ |e2|`) -- `GenusFiveRow08ChamberThree`,
  the divisor with a double chip, a `ConfigurationThree` pair and the lopsided
  banana pair of `ConfigurationBananaDoubleChip`.

`GenusFiveRow08Symmetry.chamber_covers` moves every length vector into that
three-way disjunction, and `ClosedOrbit.closedConstruction_of_chamber` turns one
chamber proof per disjunct into the statement on the whole closed orthant.
-/

namespace AtanasovRanganathan.GenusFiveRow08

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open GenusFiveCoreAtlas

/-- The three drawn scopes, each discharged by its own chamber file. -/
theorem chamber_pencil (length : Fin 12 → ℕ)
    (forest : IsForest row08Core (zeroSlots length))
    (notLoopy : ¬ IsLoopy row08Core (zeroSlots length))
    (hP : GenusFiveRow08Symmetry.Chamber length) :
    Nonempty (DegreeFourDharPencil
      (faceSpec row08Core (by norm_num) length forest notLoopy).graph) := by
  rcases hP with h1 | h2 | h3
  · exact GenusFiveRow08ChamberOne.chamberOne_pencil length forest notLoopy h1
  · exact GenusFiveRow08ChamberTwo.chamberTwo_pencil length forest notLoopy h2
  · exact GenusFiveRow08ChamberThree.chamberThree_pencil length forest notLoopy h3

/-- **AR's seventh family on row 08.**  The paper's own divisors -- one per
scope, including the one with two chips on a single vertex -- have rank at least
one on every nonloopy forest face, all four sign patterns at once. -/
theorem row08_closedConstruction :
    ClosedSubdivisionDharConstruction row08Core (by norm_num) :=
  ClosedOrbit.closedConstruction_of_chamber row08Core (by norm_num)
    GenusFiveRow08Symmetry.Chamber
    (fun length _ _ => GenusFiveRow08Symmetry.chamber_covers length)
    chamber_pencil

end AtanasovRanganathan.GenusFiveRow08
