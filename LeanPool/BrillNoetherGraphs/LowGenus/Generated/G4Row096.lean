/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.Tree
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCubicAtlas

/-!
# Generated proof data for `g4row096`

This checked payload is a deep-embedded proof tree.

The module is passive: it carries the proof tree of the `.rpf` as data, one
`decide` that the public deep-embedded checker under
`Utilities/Subdivision/ClosedRowProof/` accepts it, and the row obligation its theorems
then give.  Nothing here asserts acceptance on its own authority.

Shape: 9 leaf/leaves, 13 split(s), 0 cutvertex node(s),
19 `use` citation(s) of 14 named subtree(s),
core `n = 6`, `p = 9`, goal `BNExists _ 1 3` on the **closed** length
orthant.

Everything is `List ℤ` read with `List.getD`; the representation keeps kernel reduction compact.
The entailment certificates were synthesised by exact rational Farkas and
re-verified over `ℤ` before emission; the kernel re-checks them anyway.
-/

namespace AtanasovRanganathan.GenusFourGeneratedRows.G4Row096

open Utilities

open MarkedGraphs.Certificate
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Subdivision.ClosedRowProof

/-- The public atlas core named by `g4row096.rpf`. -/
abbrev core : ExplicitPotential.Core 6 9 :=
  AtanasovRanganathan.GenusFourCubicAtlas.row096Core

/-! ## The node data

One `def` per `LEAF` witness and per `REDUCE CUTVERTEX` node of the `.rpf`, in
depth-first order.  They are split out rather than inlined into `tree` because
`maxHeartbeats` is charged per declaration..
-/
private def rw0 : RichWitness :=
  { divisorCore := [1, 0, 0, 0, 0, 1]
    chips := [(3, [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 1, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, -1, 0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, -1, 0, 0, 0, 0, 0, 0, 0, 1], []]
        blocks := [[⟨[0, 1], [0, -1, 0, 0, 0, 0, 0, 0, 0, 1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], 1, 1⟩, ⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 1, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, -1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, -1, 0, 0, 1], []]
        blocks := [[⟨[0, 1], [0, -1, 0, 0, 1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 1], [0, 1, 0, 0, -1, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 1, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, -1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, -1, 0, 0, 1], []]
        blocks := [[⟨[0, 1], [0, -1, 0, 0, 1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 1], [0, 1, 0, 0, -1, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 1, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, -1], []]
        blocks := [[⟨[0, 1], [0, -1], -1, -1⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], 1, 1⟩, ⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 1, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 1, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

private def w1 : Witness :=
  { divisorCore := [1, 0, 0, 1, 0, 1]
    chips := []
    anchors := [
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [0, -1, 0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, -1, 0, 0, 0, 0, 0, 0, 0, 1], []]
        blocks := [[⟨[0, 1], [0, -1, 0, 0, 0, 0, 0, 0, 0, 1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [0, -1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, -1, 0, 0, 1], []]
        blocks := [[⟨[0, 1], [0, -1, 0, 0, 1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 1, 0, 0, -1, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [0, -1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, -1, 0, 0, 1], []]
        blocks := [[⟨[0, 1], [0, -1, 0, 0, 1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 1, 0, 0, -1, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, -1], []]
        blocks := [[⟨[0, 1], [0, -1], -1, -1⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

private def rw2 : RichWitness :=
  { divisorCore := [1, 0, 0, 0, 0, 1]
    chips := [(6, [0, -1, 0, 0, 1, 0, 0, 1, 0, 1], 1)]
    anchors := [
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, -1, 0, 0, 1, 0, 0, 1, 0, 1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 1], [], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 1], [], [0, 1]]
        blocks := [[⟨[0, 1], [0, -1], -1, -1⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, -1, 0, 0, 1, 0, 0, 1, 0, 1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 1, 0, 0, 0, 0, 1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 1, 0, 0, 0, 0, 1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 1⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, -1, 0, 0, 1, 0, 0, 1, 0, 1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, -1, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, -1, 0, 0, 1], [0, -1, 0, 0, 1], []]
        blocks := [[⟨[0, 1], [0, -1, 0, 0, 1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, -1, 0, 0, 1, 0, 0, 1, 0, 1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 1, 0, 0, 0, 0, 1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 1, 0, 0, 0, 0, 1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 1⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 1], [], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 1], [], [0, 1]]
        blocks := [[⟨[0, 1], [0, -1], -1, -1⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, -1, 0, 0, 1, 0, 0, 1, 0, 1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 1, 0, 0, 0, 0, 1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 1, 0, 0, 0, 0, 1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 1⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, -1, 0, 0, 1, 0, 0, 1, 0, 1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(11, 1)], [], 1⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(11, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

private def rw3 : RichWitness :=
  { divisorCore := [1, 0, 0, 0, 0, 1]
    chips := [(6, [0, 0, 0, 0, 0, 0, 0, 1, -1], 1)]
    anchors := [
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1, 1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, -1, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(3, 1), (7, 1), (8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(3, 1), (13, 1)], [], 0⟩, ⟨1, [(7, 1), (8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 1], [], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, -1, -1], [], [0, 1]]
        blocks := [[⟨[0, 1], [0, -1], -1, -1⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, -1, -1], 1, 2⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

private def rw4 : RichWitness :=
  { divisorCore := [1, 0, 0, 0, 0, 1]
    chips := [(6, [0, 0, 0, 0, 0, 0, 0, 1, -1], 1)]
    anchors := [
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(16, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1, 1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, -1, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(3, 1), (13, 1)], [], 0⟩, ⟨1, [(3, 1), (7, 1), (8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(16, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(16, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(3, 2), (13, 1)], [], 0⟩, ⟨1, [(7, 1), (8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(16, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 1], [0, 1, 0, 0, -2, 0, 0, 0, -1, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, -1, -1], [], [0, 1]]
        blocks := [[⟨[0, 1], [0, -1], -1, -1⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 2], 2, 2⟩], [⟨[0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 2, 0, 0, 0, 1, 1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 2, 0, 0, 0, 1, 1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [(14, 1), (15, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(16, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(16, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

private def rw5 : RichWitness :=
  { divisorCore := [1, 0, 0, 0, 0, 1]
    chips := [(6, [0, 0, 0, 0, 0, 0, 0, 1, -1], 1)]
    anchors := [
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1, 1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, -1, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(3, 1), (4, 1), (13, 1)], [], 0⟩, ⟨1, [(3, 1), (7, 1), (8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(3, 2), (4, 1), (13, 1)], [], 0⟩, ⟨1, [(7, 1), (8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 2, 1, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 0, 2, 1], [], [0, 0, 0, 0, 2, 1, 0, 0, 1, 1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, -2, -1, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 2], 2, 2⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(3, 2), (4, 1), (7, 1), (8, 1)], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 0, 0, 0, 0, 1, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(2, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(12, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

private def w6 : Witness :=
  { divisorCore := [1, 0, 0, 1, 0, 1]
    chips := []
    anchors := [
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1, 1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, -1, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(3, 1), (7, 1), (8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(3, 1), (13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(7, 1), (8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 1], [], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, -1, -1], [], [0, 1]]
        blocks := [[⟨[0, 1], [0, -1], -1, -1⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 0, 0, -1, -1], 1, 2⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

private def w7 : Witness :=
  { divisorCore := [1, 0, 0, 1, 0, 1]
    chips := []
    anchors := [
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1, 1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, -1, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(3, 1), (13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(16, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(3, 1), (7, 1), (8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(3, 2), (13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(16, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(7, 1), (8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 1], [0, 1, 0, 0, -2, 0, 0, 0, -1, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, -1, -1], [], [0, 1]]
        blocks := [[⟨[0, 1], [0, -1], -1, -1⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 2], 2, 2⟩], [⟨[0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 2, 0, 0, 0, 1, 1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 2, 0, 0, 0, 1, 1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(14, 1), (15, 1)], [], 0⟩, ⟨1, [(16, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

private def w8 : Witness :=
  { divisorCore := [1, 0, 0, 1, 0, 1]
    chips := []
    anchors := [
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 1], [], [0, 0, 0, 0, 1, 0, 0, 0, 1, 1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, -1, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(3, 1), (4, 1), (13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(3, 1), (7, 1), (8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], []]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(3, 2), (4, 1), (13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(7, 1), (8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 2, 1, 0, 0, 1, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 2, 1, 0, 0, 1], [0, 0, 0, 0, 2, 1], [], [0, 0, 0, 0, 2, 1, 0, 0, 1, 1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 0, -2, -1, 0, 0, -1, -1], -1, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 2], 2, 2⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, -1], -1, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(3, 2), (4, 1), (7, 1), (8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-! ## The named subtrees

One `def` per `(sub k (entry ...) body)` of the `.rpf`.  Each is checked once,
in the closed root domain extended by its entry forms; the `use` citations in
`main` re-derive those forms from their own chamber.  The entry forms are
listed alongside the body in `proof.subs` below.
-/

private def sub0 : PTree :=
  .richLeaf rw0

private def sub1 : PTree :=
  .leaf w1

private def sub2 : PTree :=
  .richLeaf rw2

private def sub3 : PTree :=
  .richLeaf rw3

private def sub4 : PTree :=
  .richLeaf rw4

private def sub5 : PTree :=
  .richLeaf rw5

private def sub6 : PTree :=
  .leaf w6

private def sub7 : PTree :=
  .leaf w7

private def sub8 : PTree :=
  .leaf w8

private def sub9 : PTree :=
  .split [0, 1, 0, 0, -2, 0, 0, 0, -1, -1]
    (.split [0, -1, 0, 0, 2, 1, 0, 0, 1, 1]
      (.use 4 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(16, 1)], [], 0⟩, ⟨1, [(17, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩])
      (.use 5 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(17, 1)], [], 1⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩]))
    (.use 3 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(16, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 0⟩])

private def sub10 : PTree :=
  .split [0, 1, 0, 0, -2, 0, 0, 0, -1, -1]
    (.split [0, -1, 0, 0, 2, 1, 0, 0, 1, 1]
      (.use 7 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(16, 1)], [], 0⟩, ⟨1, [(17, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩])
      (.use 8 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(17, 1)], [], 1⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩]))
    (.use 6 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(16, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 0⟩])

private def sub11 : PTree :=
  .split [-1, 0, 0, 0, 0, 0, 0, 0, 1]
    (.use 9 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩])
    (.use 10 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩])

private def sub12 : PTree :=
  .split [0, 1, 0, 0, -1, 0, 0, 0, -1, -1]
    (.split [0, 0, 0, 0, 0, -1, 1]
      (.use 11 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩])
      (.auto { vertex := [0, 1, 2, 3, 4, 5], vertexInv := [0, 1, 2, 3, 4, 5], slot := [0, 1, 2, 3, 5, 4, 6, 7, 8], slotInv := [0, 1, 2, 3, 5, 4, 6, 7, 8], reversed := [false, false, false, false, false, false, false, false, false] }
        (.use 11 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 1⟩])))
    (.use 2 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩])

private def sub13 : PTree :=
  .split [0, -1, 0, 0, 1, 0, 0, 0, 0, 1]
    (.split [-1, -1, 0, 0, 1, 0, 0, 0, 0, 1]
      (.use 0 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩])
      (.use 1 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩]))
    (.split [0, 0, 0, 0, 0, 0, 0, 1, -1]
      (.use 12 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩])
      (.auto { vertex := [0, 1, 2, 3, 4, 5], vertexInv := [0, 1, 2, 3, 4, 5], slot := [0, 1, 2, 3, 4, 5, 7, 6, 8], slotInv := [0, 1, 2, 3, 4, 5, 7, 6, 8], reversed := [false, false, false, false, false, false, false, false, false] }
        (.use 12 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩])))

/-- The proof of the `.rpf`, verbatim: the named subtrees with their entry
contexts, in declaration order, and the main tree.  A `use` node carries one
entailment certificate per entry form of the subtree it cites. -/
def proof : PProof where
  subs :=
    [([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, -1, 0, 0, 1, 0, 0, 0, 0, 1]], sub0),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [0, -1, 0, 0, 1, 0, 0, 0, 0, 1], [0, 1, 0, 0, -1, 0, 0, 0, 0, -1]], sub1),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [-1, -1, 0, 0, 1, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 1, -1]], sub2),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1, -1], [0, 1, 0, 0, -1, 0, 0, 0, -1, -1], [0, -1, 0, 0, 2, 0, 0, 0, 1, 1], [-1, 0, 0, 0, 0, 0, 0, 0, 1]], sub3),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1, -1], [0, 1, 0, 0, -2, 0, 0, 0, -1, -1], [0, -1, 0, 0, 2, 1, 0, 0, 1, 1], [0, 0, 0, 0, 0, -1, 1], [-1, 0, 0, 0, 0, 0, 0, 0, 1]], sub4),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1, -1], [0, 1, 0, 0, -2, -1, 0, 0, -1, -1], [0, 0, 0, 0, 0, -1, 1], [-1, 0, 0, 0, 0, 0, 0, 0, 1]], sub5),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1, -1], [0, 1, 0, 0, -1, 0, 0, 0, -1, -1], [0, -1, 0, 0, 2, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1]], sub6),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1, -1], [0, 1, 0, 0, -2, 0, 0, 0, -1, -1], [0, -1, 0, 0, 2, 1, 0, 0, 1, 1], [0, 0, 0, 0, 0, -1, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1]], sub7),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1, -1], [0, 1, 0, 0, -2, -1, 0, 0, -1, -1], [0, 0, 0, 0, 0, -1, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1]], sub8),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1, -1], [0, 1, 0, 0, -1, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, -1, 1], [-1, 0, 0, 0, 0, 0, 0, 0, 1]], sub9),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1, -1], [0, 1, 0, 0, -1, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, -1, 1], [0, 0, 0, 0, 0, 0, 0, 0, -1]], sub10),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1, -1], [0, 1, 0, 0, -1, 0, 0, 0, -1, -1], [0, 0, 0, 0, 0, -1, 1]], sub11),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1], [-1, 1, 0, 0, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1, -1]], sub12),
     ([[0, 1, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, 0, 0, -1]], sub13)]
  main :=
  .split [0, 1, 0, 0, -1]
    (.split [0, 1, 0, 0, 0, 0, 0, 0, 0, -1]
      (.use 13 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩])
      (.auto { vertex := [2, 0, 1, 4, 5, 3], vertexInv := [1, 2, 0, 5, 3, 4], slot := [8, 6, 7, 0, 1, 2, 4, 5, 3], slotInv := [3, 4, 5, 8, 6, 7, 1, 2, 0], reversed := [false, false, false, false, false, false, false, false, false] }
        (.auto { vertex := [2, 0, 1, 4, 5, 3], vertexInv := [1, 2, 0, 5, 3, 4], slot := [8, 6, 7, 0, 1, 2, 4, 5, 3], slotInv := [3, 4, 5, 8, 6, 7, 1, 2, 0], reversed := [false, false, false, false, false, false, false, false, false] }
          (.use 13 [⟨1, [(10, 1)], [], 1⟩, ⟨1, [(9, 1), (10, 1)], [], 1⟩]))))
    (.split [0, 0, 0, 0, 1, 0, 0, 0, 0, -1]
      (.auto { vertex := [2, 0, 1, 4, 5, 3], vertexInv := [1, 2, 0, 5, 3, 4], slot := [8, 6, 7, 0, 1, 2, 4, 5, 3], slotInv := [3, 4, 5, 8, 6, 7, 1, 2, 0], reversed := [false, false, false, false, false, false, false, false, false] }
        (.use 13 [⟨1, [(10, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 1⟩]))
      (.auto { vertex := [2, 0, 1, 4, 5, 3], vertexInv := [1, 2, 0, 5, 3, 4], slot := [8, 6, 7, 0, 1, 2, 4, 5, 3], slotInv := [3, 4, 5, 8, 6, 7, 1, 2, 0], reversed := [false, false, false, false, false, false, false, false, false] }
        (.auto { vertex := [2, 0, 1, 4, 5, 3], vertexInv := [1, 2, 0, 5, 3, 4], slot := [8, 6, 7, 0, 1, 2, 4, 5, 3], slotInv := [3, 4, 5, 8, 6, 7, 1, 2, 0], reversed := [false, false, false, false, false, false, false, false, false] }
          (.use 13 [⟨1, [(9, 1), (10, 1)], [], 2⟩, ⟨1, [(10, 1)], [], 1⟩]))))

/-- The deep-embedded checker accepts, by kernel reduction.

`decide +kernel` uses ordinary kernel reduction and avoids duplicate evaluation by the elaborator. -/
theorem checks :
    PProof.checks 9 core 3 (rootContextClosed 9) proof = true := by
  decide +kernel

/-- **`BNExists … 1 3` for catalog row `g4row096`, from its `.rpf` and nothing
else.**  Quantified over every length vector whose vanishing set is a non-loopy
forest -- every subdivision of the core, and every equal-genus contraction of
one. -/
theorem bnExists (ℓ : Fin 9 → ℕ)
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    BNExists (censusSpec core (by norm_num) ℓ hForest hNotLoopy).graph 1 3 :=
  proof_sound_closed_root core proof 3 (by norm_num) checks ℓ hForest hNotLoopy

/-- The object the conclusion speaks about has the row's genus at every face. -/
theorem genus_eq (ℓ : Fin 9 → ℕ)
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) :
    genus (censusSpec core (by norm_num) ℓ hForest hNotLoopy).graph = 4 := by
  rw [Utilities.Certificate.DegenerateSpec.DegSpec.genus_graph]
  norm_num

end AtanasovRanganathan.GenusFourGeneratedRows.G4Row096
