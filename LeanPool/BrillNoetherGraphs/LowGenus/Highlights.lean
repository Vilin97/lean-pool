/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.AtanasovRanganathanExistence
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveConstructions
import LeanPool.BrillNoetherGraphs.LowGenus.LowGenusExistence

/-!
# Highlights of the `LowGenus` library

**A public interface, in one file.**  Every main theorem of the
Atanasov–Ranganathan programme is restated below as an `example` whose type is
written out in full and whose proof is the real theorem.  There is not a single
new definition or theorem here.

* **For a reader.**  The shape of the whole programme — sixteen construction
  proofs, one classification boundary, one arithmetic reduction, one public
  conclusion — is visible in one screen.
* **For the build.**  Each `example` is checked by the kernel against the real
  declaration, so a refactor that silently changes a statement breaks *this*
  file loudly.

**The shape of the argument.**  Brill–Noether existence for every connected
graph of genus at most five reduces (`bnExists_of_genus_le_five_of_criticalPencils`)
to two *critical pencils*: a degree-three rank-one divisor in genus four, and a
degree-four rank-one divisor in genus five.  Fossilization and trivalent
expansion reduce genus four to six closed cubic rows.  Genus five reduces to
the sixteen displayed AR constructions plus four bridge rows, all four handled
by the same checked `(2,3)` articulation.  The public canonical classifiers
make both reductions exhaustive.
-/

namespace LowGenus.Highlights

open Utilities
open AtanasovRanganathan.GenusFiveCoreAtlas
open AtanasovRanganathan.GenusFiveConstructions

/-! ## The key definitions -/

/-- One of the sixteen displayed `8`-vertex, `12`-edge cubic cores of AR's
genus-five section.  (`LowGenus/GenusFiveCoreAtlas.lean`) -/
alias Core := AtanasovRanganathan.GenusFiveCoreAtlas.Core

/-- **The obligation for one row**: choose a degree-four divisor throughout the
core's genus-preserving *closed* length orthant, and supply a tagged explicit
Dhar move at every off-support vertex.  The closed form includes the positive
row and all of its nonloopy forest faces.
(`LowGenus/GenusFiveConstructions.lean`) -/
alias RowConstruction := AtanasovRanganathan.GenusFiveConstructions.RowConstruction

/-- The two genuinely geometric inputs left after the low-genus arithmetic
reduction: rank-one degree-three in genus four, rank-one degree-four in genus
five.  (`LowGenus/LowGenusExistence.lean`) -/
alias LowGenusCriticalPencils := Utilities.LowGenusCriticalPencils

/-- The remaining non-construction obligation: classify every valid loop-aware
pseudocore as a face of one of the sixteen closed constructions, or as an
already available structural case.  (`LowGenus/GenusFiveConstructions.lean`) -/
alias CubicAtlasClosedCoverage :=
  AtanasovRanganathan.GenusFiveConstructions.CubicAtlasClosedCoverage

/-! ## The sixteen-row ledger

One line per displayed core.  Each is an independently replaceable proof, and
each is a reportable unit of progress; six are length-dependent families and
ten are AR's straightforward constructions. -/

example : RowConstruction row01Core := row01_firstFamily      -- first family
example : RowConstruction row02Core := row02_secondFamily     -- second family
example : RowConstruction row03Core := row03_straightforward
example : RowConstruction row04Core := row04_fourthFamily     -- fourth family
example : RowConstruction row05Core := row05_sixthFamily      -- sixth family
example : RowConstruction row06Core := row06_straightforward
example : RowConstruction row07Core := row07_straightforward
example : RowConstruction row08Core := row08_seventhFamily    -- seventh family
example : RowConstruction row09Core := row09_straightforward
example : RowConstruction row10Core := row10_ninthFamily      -- ninth family
example : RowConstruction row11Core := row11_straightforward
example : RowConstruction row12Core := row12_straightforward
example : RowConstruction row13Core := row13_straightforward
example : RowConstruction row14Core := row14_straightforward
example : RowConstruction row15Core := row15_straightforward
example : RowConstruction row16Core := row16_straightforward

/-- **The ledger, assembled.**  All sixteen closed source constructions in one
structure — without yet asserting that they exhaust the cubic cores. -/
example : CubicAtlasConstructions := cubicAtlasConstructions

/-- Every closed row construction supplies the positive-subdivision pencil the
public AR reduction expects. -/
example {core : Core} (hLoopless : Loopless core)
    (construction : RowConstruction core) :
    AtanasovRanganathan.PositiveSubdivisionPencil core (by norm_num) hLoopless 4 :=
  RowConstruction.toPositiveSubdivisionPencil hLoopless construction

/-! ## From the ledger to the genus-five pencil -/

/-- Given the classification boundary, the sixteen constructions supply the
critical genus-five degree-four pencil on **every** connected graph of genus
five.  (The conclusion is `GenusFiveRankOneExistence`, spelled out.) -/
example (coverage : CubicAtlasClosedCoverage) :
    ∀ (G : CFGraph.{0}), graph_connected G → genus G = 5 → BNExists G 1 4 :=
  genusFiveRankOneExistence_of_cubicAtlasClosedCoverage coverage

/-! ## The public conclusion -/

/-- Every connected genus-four graph has the critical degree-three pencil. -/
example : GenusFourRankOneExistence :=
  AtanasovRanganathan.genusFourRankOneExistence

/-- **The unconditional Atanasov–Ranganathan theorem.** -/
example : BrillNoetherExistenceThroughFive :=
  AtanasovRanganathan.brillNoetherExistenceThroughFive

/-- Genus at most three is elementary: no geometric input is needed. -/
example {G : CFGraph} (hG : graph_connected G) (hGenus : genus G ≤ 3)
    {r d : ℤ} (hR : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) :
    BNExists G r d :=
  Utilities.bnExists_of_genus_le_three hG hGenus hR hRho

/-- The two critical pencils imply Brill–Noether existence for every
nonnegative rank and every admissible parameter pair in genus at most five. -/
example (critical : LowGenusCriticalPencils)
    {G : CFGraph.{0}} (hG : graph_connected G) (hGenus : genus G ≤ 5)
    {r d : ℤ} (hR : 0 ≤ r) (hRho : 0 ≤ bnNumber G r d) :
    BNExists G r d :=
  Utilities.bnExists_of_genus_le_five_of_criticalPencils critical hG hGenus hR hRho

/-- The arithmetic final step, shown independently: the two critical rank-one
assertions imply the full Brill–Noether existence conjecture for every
connected graph of genus at most five. -/
example (critical : LowGenusCriticalPencils) :
    ∀ (G : CFGraph.{0}) (hG : graph_connected G), genus G ≤ 5 →
      ∀ r d : ℤ, brill_noether_conjecture hG r d :=
  Utilities.criticalPencils_imply_brillNoetherExistenceThroughFive critical

end LowGenus.Highlights
