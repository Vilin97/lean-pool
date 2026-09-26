/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.Tree
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCubicAtlas

/-!
# Generated proof data for `g4row100`

This checked payload is a deep-embedded proof tree.

The module is passive: it carries the proof tree of the `.rpf` as data, one
`decide` that the public deep-embedded checker under
`Utilities/Subdivision/ClosedRowProof/` accepts it, and the row obligation its theorems
then give.  Nothing here asserts acceptance on its own authority.

Shape: 18 leaf/leaves, 34 split(s), 0 cutvertex node(s),
38 `use` citation(s) of 21 named subtree(s),
core `n = 6`, `p = 9`, goal `BNExists _ 1 3` on the **closed** length
orthant.

Everything is `List ℤ` read with `List.getD`; the representation keeps kernel reduction compact.
The entailment certificates were synthesised by exact rational Farkas and
re-verified over `ℤ` before emission; the kernel re-checks them anyway.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFourGeneratedRows.G4Row100

open Utilities

open MarkedGraphs.Certificate
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Subdivision.ClosedRowProof

/-- The public atlas core named by `g4row100.rpf`. -/
abbrev core : ExplicitPotential.Core 6 9 :=
  AtanasovRanganathan.GenusFourCubicAtlas.row100Core

/-! ## The node data

One `def` per `LEAF` witness and per `REDUCE CUTVERTEX` node of the `.rpf`, in
depth-first order.  They are split out rather than inlined into `tree` because
`maxHeartbeats` is charged per declaration..
-/
/-- Multiple-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 0]`, 1 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def rw0 : RichWitness :=
  { divisorCore := [0, 0, 0, 1, 1, 0]
    chips := [(2, [0, 0, 0, 1, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0,
          0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 1, 0, 0, 0, -1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 0, 1, 0, 0, 0,
          -1], 0, 1⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1], 1, 1⟩, ⟨[0, 0, 0,
          1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩⟩], [⟨⟨1,
          [(1, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], 1, 1⟩,
          ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1,
          [], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [],
          0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Multiple-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 0]`, 1 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def rw1 : RichWitness :=
  { divisorCore := [0, 0, 0, 1, 1, 0]
    chips := [(2, [0, 0, 0, 1, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0,
          0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 1, 0, 0, 0, -1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 0, 1, 0, 0, 0,
          -1], 0, 1⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1], 1, 1⟩, ⟨[0, 0, 0,
          1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩⟩], [⟨⟨1,
          [(1, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 1], [], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 1], [0,
          0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 1], 0, 1⟩, ⟨[0, 0, 0, 0, 0, 1],
          [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 0, 1⟩], [⟨[0,
          0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(14,
          1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)],
          [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Multiple-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 0]`, 1 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def rw2 : RichWitness :=
  { divisorCore := [0, 0, 0, 1, 1, 0]
    chips := [(2, [0, 0, 0, 1, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0,
          0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 1, 0, 0, 0, -1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 0, 1, 0, 0, 0,
          -1], 0, 1⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1], 1, 1⟩, ⟨[0, 0, 0,
          1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩⟩], [⟨⟨1,
          [(1, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1,
          1], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 0, 1], 0, 1⟩, ⟨[0, 0,
          0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0,
          0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [(5, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩,
          ⟨1, [(14, 1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Multiple-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 0]`, 1 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def rw3 : RichWitness :=
  { divisorCore := [0, 0, 0, 1, 1, 0]
    chips := [(2, [0, 0, 0, 1, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
        blocks := [[⟨[0, 1], [0, 1], 1, 1⟩], [⟨[0, 0, 1], [0, 1], 0, 1⟩], [⟨[0, 0, 0, 1, 0, 0, 0,
          -1], [0, 1], 0, 1⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [(0, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [(0, 1)],
          [], 0⟩, ⟨1, [(12, 1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], 1, 1⟩,
          ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1,
          [], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [],
          0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Multiple-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 0]`, 1 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def rw4 : RichWitness :=
  { divisorCore := [0, 0, 0, 1, 1, 0]
    chips := [(2, [0, 0, 0, 1, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
        blocks := [[⟨[0, 1], [0, 1], 1, 1⟩], [⟨[0, 0, 1], [0, 1], 0, 1⟩], [⟨[0, 0, 0, 1, 0, 0, 0,
          -1], [0, 1], 0, 1⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [(0, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [(0, 1)],
          [], 0⟩, ⟨1, [(12, 1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 1], [], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 1], [0,
          0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 1], 0, 1⟩, ⟨[0, 0, 0, 0, 0, 1],
          [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 0, 1⟩], [⟨[0,
          0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(14,
          1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)],
          [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Multiple-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 0]`, 1 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def rw5 : RichWitness :=
  { divisorCore := [0, 0, 0, 1, 1, 0]
    chips := [(2, [0, 0, 0, 1, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
        blocks := [[⟨[0, 1], [0, 1], 1, 1⟩], [⟨[0, 0, 1], [0, 1], 0, 1⟩], [⟨[0, 0, 0, 1, 0, 0, 0,
          -1], [0, 1], 0, 1⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [(0, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [(0, 1)],
          [], 0⟩, ⟨1, [(12, 1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1,
          1], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 0, 1], 0, 1⟩, ⟨[0, 0,
          0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0,
          0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [(5, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩,
          ⟨1, [(14, 1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Multiple-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 0]`, 1 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def rw6 : RichWitness :=
  { divisorCore := [0, 0, 0, 1, 1, 0]
    chips := [(2, [0, 0, 0, 1, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
        blocks := [[⟨[0, 1], [0, 0, 1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 1, 0,
          0, 0, -1], [0, 0, 1], 0, 1⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩⟩], [⟨⟨1,
          [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [(1, 1)],
          [], 0⟩, ⟨1, [(12, 1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], 1, 1⟩,
          ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1,
          [], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [],
          0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Multiple-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 0]`, 1 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def rw7 : RichWitness :=
  { divisorCore := [0, 0, 0, 1, 1, 0]
    chips := [(2, [0, 0, 0, 1, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
        blocks := [[⟨[0, 1], [0, 0, 1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 1, 0,
          0, 0, -1], [0, 0, 1], 0, 1⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩⟩], [⟨⟨1,
          [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [(1, 1)],
          [], 0⟩, ⟨1, [(12, 1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 1], [], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 1], [0,
          0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 1], 0, 1⟩, ⟨[0, 0, 0, 0, 0, 1],
          [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 0, 1⟩], [⟨[0,
          0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(14,
          1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)],
          [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Multiple-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 0]`, 1 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def rw8 : RichWitness :=
  { divisorCore := [0, 0, 0, 1, 1, 0]
    chips := [(2, [0, 0, 0, 1, 0, 0, 0, -1], 1)]
    anchors := [
      { potential := [[], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
        blocks := [[⟨[0, 1], [0, 0, 1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 1, 0,
          0, 0, -1], [0, 0, 1], 0, 1⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩⟩], [⟨⟨1,
          [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [(1, 1)],
          [], 0⟩, ⟨1, [(12, 1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1,
          1], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0,
          0, 0, 0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 0, 1], 0, 1⟩, ⟨[0, 0,
          0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0,
          0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [(5, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩,
          ⟨1, [(14, 1)], [], 0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1],
          [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 0, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(4, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩],
          [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(8, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]],
          [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]]]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1, 0, 0, 0, -1], [],
          0, 0⟩, ⟨[0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], -1, -1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩],
          [⟨[0, 0, 0, 0, 0, 1, 0, -1], [], 0, 0⟩, ⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0,
          0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩]]
        headSlack := [0, 0, 1, 0, 1, 0, 0, 0, 0]
        tailSlack := [0, 0, 0, 0, 0, 0, 0, 0, 0]
        blockCert := [[⟨⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(1, 1)], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(9, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [],
          0⟩⟩, ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(3, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩,
          ⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(5, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1,
          [(7, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩⟩], [⟨⟨1, [(8, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩⟩]]
        tailSlackCert := [Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt,
          Cert.dflt, Cert.dflt, Cert.dflt]
        headSlackCert := [Cert.dflt, Cert.dflt, ⟨1, [(15, 1)], [], 0⟩, Cert.dflt, ⟨1, [(15, 1)],
          [], 0⟩, Cert.dflt, Cert.dflt, Cert.dflt, Cert.dflt]
        separationCert := [[[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt,
          Cert.dflt], [Cert.dflt, Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt,
          Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt],
          [Cert.dflt, Cert.dflt]], [[Cert.dflt, Cert.dflt], [Cert.dflt, Cert.dflt]]]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Single-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 1]`, 0 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def w9 : Witness :=
  { divisorCore := [0, 0, 0, 1, 1, 1]
    chips := []
    anchors := [
      { potential := [[], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0,
          0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 1, 0, 0, 0, -1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 0, 1, 0, 0, 0,
          -1], 0, 1⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, -1], 1, 1⟩], [⟨[0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0,
          0, 1], [0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1], 0,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Single-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 1]`, 0 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def w10 : Witness :=
  { divisorCore := [0, 0, 0, 1, 1, 1]
    chips := []
    anchors := [
      { potential := [[], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0,
          0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 1, 0, 0, 0, -1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 0, 1, 0, 0, 0,
          -1], 0, 1⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, -1], 1, 1⟩], [⟨[0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 1], [], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 1], [0,
          0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [0,
          0, 0, 0, 1, 0, 0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 0, 1⟩], [⟨[0, 0,
          0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(3,
          1), (6, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(14,
          1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Single-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 1]`, 0 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def w11 : Witness :=
  { divisorCore := [0, 0, 0, 1, 1, 1]
    chips := []
    anchors := [
      { potential := [[], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0,
          0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1]]
        blocks := [[⟨[0, 1], [0, 0, 0, 1, 0, 0, 0, -1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 0, 1, 0, 0, 0,
          -1], 0, 1⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, -1], 1, 1⟩], [⟨[0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(9, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(11, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [],
          0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1,
          1], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0,
          1], [0, 0, 0, 0, 0, 0, 1, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1,
          [(5, 1), (6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1,
          [(14, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Single-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 1]`, 0 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def w12 : Witness :=
  { divisorCore := [0, 0, 0, 1, 1, 1]
    chips := []
    anchors := [
      { potential := [[], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
        blocks := [[⟨[0, 1], [0, 1], 1, 1⟩], [⟨[0, 0, 1], [0, 1], 0, 1⟩], [⟨[0, 0, 0, 1], [0, 1],
          0, 1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [(0, 1)], [], 0⟩, ⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(6, 1), (12, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0,
          0, 1], [0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1], 0,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Single-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 1]`, 0 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def w13 : Witness :=
  { divisorCore := [0, 0, 0, 1, 1, 1]
    chips := []
    anchors := [
      { potential := [[], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
        blocks := [[⟨[0, 1], [0, 1], 1, 1⟩], [⟨[0, 0, 1], [0, 1], 0, 1⟩], [⟨[0, 0, 0, 1], [0, 1],
          0, 1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [(0, 1)], [], 0⟩, ⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(6, 1), (12, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 1], [], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 1], [0,
          0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [0,
          0, 0, 0, 1, 0, 0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 0, 1⟩], [⟨[0, 0,
          0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(3,
          1), (6, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(14,
          1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Single-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 1]`, 0 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def w14 : Witness :=
  { divisorCore := [0, 0, 0, 1, 1, 1]
    chips := []
    anchors := [
      { potential := [[], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1]]
        blocks := [[⟨[0, 1], [0, 1], 1, 1⟩], [⟨[0, 0, 1], [0, 1], 0, 1⟩], [⟨[0, 0, 0, 1], [0, 1],
          0, 1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0,
          1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [(0, 1)], [], 0⟩, ⟨1, [(0, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩, ⟨1, [(6, 1), (12, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1,
          1], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0,
          1], [0, 0, 0, 0, 0, 0, 1, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1,
          [(5, 1), (6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1,
          [(14, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Single-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 1]`, 0 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def w15 : Witness :=
  { divisorCore := [0, 0, 0, 1, 1, 1]
    chips := []
    anchors := [
      { potential := [[], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
        blocks := [[⟨[0, 1], [0, 0, 1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 1], [0,
          0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(11, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1), (12, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1], 0, 1⟩], [⟨[0, 0, 0, 0,
          0, 1], [0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1, 0, -1], 0,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Single-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 1]`, 0 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def w16 : Witness :=
  { divisorCore := [0, 0, 0, 1, 1, 1]
    chips := []
    anchors := [
      { potential := [[], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
        blocks := [[⟨[0, 1], [0, 0, 1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 1], [0,
          0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(11, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1), (12, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 1, 0, 0, 1], [], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 1], [0,
          0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 1], [0,
          0, 0, 0, 1, 0, 0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], 0, 1⟩], [⟨[0, 0,
          0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(3,
          1), (6, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(14,
          1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-- Single-block leaf data for row 100: core divisor `[0, 0, 0, 1, 1, 1]`, 0 positioned chip
terms, and six anchor firing plans with exact entailment receipts. -/
def w17 : Witness :=
  { divisorCore := [0, 0, 0, 1, 1, 1]
    chips := []
    anchors := [
      { potential := [[], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1]]
        blocks := [[⟨[0, 1], [0, 0, 1], 0, 1⟩], [⟨[0, 0, 1], [0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 1], [0,
          0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1,
          [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [(11, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1), (12, 1)], [], 0⟩, ⟨1, [],
          [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 1, 1], [], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1,
          1], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1]]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0,
          1], [0, 0, 0, 0, 0, 0, 1, 1], 0, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], 1,
          1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0,
          0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1,
          [(5, 1), (6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1,
          [(14, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[], [], [], [], [], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [], 0, 0⟩], [⟨[0,
          0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [],
          0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0,
          0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩,
          ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      },
      { potential := [[0, 0, 0, 0, 0, 0, 0, 1], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], []]
        blocks := [[⟨[0, 1], [], 0, 0⟩], [⟨[0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, -1], 0, 0⟩], [⟨[0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
          0, 0, 1], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
          0, 0, 0, 0, 0, 1], 1, 1⟩], [⟨[0, 0, 0, 0, 0, 0, 0, 0, 1], [], 0, 0⟩], [⟨[0, 0, 0, 0, 0,
          0, 0, 0, 0, 1], [], 0, 0⟩]]
        headSlack := []
        tailSlack := []
        loCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
        hiCert := [⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [(15,
          1)], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩, ⟨1, [], [], 0⟩]
      }
    ]
    slotCert := [⟨1, [(0, 1)], [], 0⟩, ⟨1, [(1, 1)], [], 0⟩, ⟨1, [(2, 1)], [], 0⟩, ⟨1, [(3, 1)], [], 0⟩, ⟨1, [(4, 1)], [], 0⟩, ⟨1, [(5, 1)], [], 0⟩, ⟨1, [(6, 1)], [], 0⟩, ⟨1, [(7, 1)], [], 0⟩, ⟨1, [(8, 1)], [], 0⟩] }

/-! ## The named subtrees

One `def` per `(sub k (entry ...) body)` of the `.rpf`.  Each is checked once,
in the closed root domain extended by its entry forms; the `use` citations in
`main` re-derive those forms from their own chamber.  The entry forms are
listed alongside the body in `proof.subs` below.
-/

/-- Named chamber leaf using `rw0` for row 100; its entry inequalities occupy position 0 in
`proof.subs`. -/
def sub0 : PTree :=
  .richLeaf rw0

/-- Named chamber leaf using `rw1` for row 100; its entry inequalities occupy position 1 in
`proof.subs`. -/
def sub1 : PTree :=
  .richLeaf rw1

/-- Named chamber leaf using `rw2` for row 100; its entry inequalities occupy position 2 in
`proof.subs`. -/
def sub2 : PTree :=
  .richLeaf rw2

/-- Named chamber leaf using `rw3` for row 100; its entry inequalities occupy position 3 in
`proof.subs`. -/
def sub3 : PTree :=
  .richLeaf rw3

/-- Named chamber leaf using `rw4` for row 100; its entry inequalities occupy position 4 in
`proof.subs`. -/
def sub4 : PTree :=
  .richLeaf rw4

/-- Named chamber leaf using `rw5` for row 100; its entry inequalities occupy position 5 in
`proof.subs`. -/
def sub5 : PTree :=
  .richLeaf rw5

/-- Named chamber leaf using `rw6` for row 100; its entry inequalities occupy position 6 in
`proof.subs`. -/
def sub6 : PTree :=
  .richLeaf rw6

/-- Named chamber leaf using `rw7` for row 100; its entry inequalities occupy position 7 in
`proof.subs`. -/
def sub7 : PTree :=
  .richLeaf rw7

/-- Named chamber leaf using `rw8` for row 100; its entry inequalities occupy position 8 in
`proof.subs`. -/
def sub8 : PTree :=
  .richLeaf rw8

/-- Named chamber leaf using `w9` for row 100; its entry inequalities occupy position 9 in
`proof.subs`. -/
def sub9 : PTree :=
  .leaf w9

/-- Named chamber leaf using `w10` for row 100; its entry inequalities occupy position 10 in
`proof.subs`. -/
def sub10 : PTree :=
  .leaf w10

/-- Named chamber leaf using `w11` for row 100; its entry inequalities occupy position 11 in
`proof.subs`. -/
def sub11 : PTree :=
  .leaf w11

/-- Named chamber leaf using `w12` for row 100; its entry inequalities occupy position 12 in
`proof.subs`. -/
def sub12 : PTree :=
  .leaf w12

/-- Named chamber leaf using `w13` for row 100; its entry inequalities occupy position 13 in
`proof.subs`. -/
def sub13 : PTree :=
  .leaf w13

/-- Named chamber leaf using `w14` for row 100; its entry inequalities occupy position 14 in
`proof.subs`. -/
def sub14 : PTree :=
  .leaf w14

/-- Named chamber leaf using `w15` for row 100; its entry inequalities occupy position 15 in
`proof.subs`. -/
def sub15 : PTree :=
  .leaf w15

/-- Named chamber leaf using `w16` for row 100; its entry inequalities occupy position 16 in
`proof.subs`. -/
def sub16 : PTree :=
  .leaf w16

/-- Named chamber leaf using `w17` for row 100; its entry inequalities occupy position 17 in
`proof.subs`. -/
def sub17 : PTree :=
  .leaf w17

/-- Chamber subtree for row 100, first splitting on `length[0] - length[2] + length[6] ≥ 0`, then
citing earlier subtree indices 0, 1, 2, 3, 4, 5, 6, 7, 8. The other branch uses the integer
complement of the split inequality. -/
def sub18 : PTree :=
  .split [0, 1, 0, -1, 0, 0, 0, 1]
    (.split [0, 0, 1, -1, 0, 0, 0, 1]
      (.split [0, 0, 0, 0, 1, -1, 0, 1]
        (.split [0, 0, 0, 0, 0, -1, 1, 1]
          (.use 0 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 2 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(14, 1), (15, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩]))
        (.split [0, 0, 0, 0, -1, 0, 1]
          (.use 1 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 2 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 2⟩, ⟨1, [(11, 1)], [], 0⟩])))
      (.split [0, 0, 0, 0, 1, -1, 0, 1]
        (.split [0, 0, 0, 0, 0, -1, 1, 1]
          (.use 6 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 8 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩]))
        (.split [0, 0, 0, 0, -1, 0, 1]
          (.use 7 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 8 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 2⟩, ⟨1, [(11, 1)], [], 0⟩]))))
    (.split [0, -1, 1]
      (.split [0, 0, 0, 0, 1, -1, 0, 1]
        (.split [0, 0, 0, 0, 0, -1, 1, 1]
          (.use 3 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 5 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩]))
        (.split [0, 0, 0, 0, -1, 0, 1]
          (.use 4 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 5 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 2⟩, ⟨1, [(11, 1)], [], 0⟩])))
      (.split [0, 0, 0, 0, 1, -1, 0, 1]
        (.split [0, 0, 0, 0, 0, -1, 1, 1]
          (.use 6 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(12, 1), (13, 1)], [], 2⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 8 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(12, 1), (13, 1)], [], 2⟩, ⟨1, [(14, 1), (15, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩]))
        (.split [0, 0, 0, 0, -1, 0, 1]
          (.use 7 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(12, 1), (13, 1)], [], 2⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 8 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(12, 1), (13, 1)], [], 2⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 2⟩, ⟨1, [(11, 1)], [], 0⟩]))))

/-- Chamber subtree for row 100, first splitting on `length[0] - length[2] + length[6] ≥ 0`, then
citing earlier subtree indices 9, 10, 11, 12, 13, 14, 15, 16, 17. The other branch uses the
integer complement of the split inequality. -/
def sub19 : PTree :=
  .split [0, 1, 0, -1, 0, 0, 0, 1]
    (.split [0, 0, 1, -1, 0, 0, 0, 1]
      (.split [0, 0, 0, 0, 1, -1, 0, 1]
        (.split [0, 0, 0, 0, 0, -1, 1, 1]
          (.use 9 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 11 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(14, 1), (15, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩]))
        (.split [0, 0, 0, 0, -1, 0, 1]
          (.use 10 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 11 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 2⟩, ⟨1, [(11, 1)], [], 0⟩])))
      (.split [0, 0, 0, 0, 1, -1, 0, 1]
        (.split [0, 0, 0, 0, 0, -1, 1, 1]
          (.use 15 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 17 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩]))
        (.split [0, 0, 0, 0, -1, 0, 1]
          (.use 16 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 17 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(12, 1), (13, 1)], [], 1⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 2⟩, ⟨1, [(11, 1)], [], 0⟩]))))
    (.split [0, -1, 1]
      (.split [0, 0, 0, 0, 1, -1, 0, 1]
        (.split [0, 0, 0, 0, 0, -1, 1, 1]
          (.use 12 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 14 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩]))
        (.split [0, 0, 0, 0, -1, 0, 1]
          (.use 13 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 14 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 0⟩, ⟨1, [(12, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 2⟩, ⟨1, [(11, 1)], [], 0⟩])))
      (.split [0, 0, 0, 0, 1, -1, 0, 1]
        (.split [0, 0, 0, 0, 0, -1, 1, 1]
          (.use 15 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(12, 1), (13, 1)], [], 2⟩, ⟨1, [(14, 1)], [], 0⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 17 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(12, 1), (13, 1)], [], 2⟩, ⟨1, [(14, 1), (15, 1)], [], 1⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩]))
        (.split [0, 0, 0, 0, -1, 0, 1]
          (.use 16 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(12, 1), (13, 1)], [], 2⟩, ⟨1, [(15, 1)], [], 0⟩, ⟨1, [(14, 1)], [], 1⟩, ⟨1, [(11, 1)], [], 0⟩])
          (.use 17 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(13, 1)], [], 1⟩, ⟨1, [(12, 1), (13, 1)], [], 2⟩, ⟨1, [(15, 1)], [], 1⟩, ⟨1, [(14, 1), (15, 1)], [], 2⟩, ⟨1, [(11, 1)], [], 0⟩]))))

/-- Chamber subtree for row 100, first splitting on `-1 + length[6] ≥ 0`, then citing earlier
subtree indices 18, 19. The other branch uses the integer complement of the split inequality. -/
def sub20 : PTree :=
  .split [-1, 0, 0, 0, 0, 0, 0, 1]
    (.use 18 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩])
    (.use 19 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩, ⟨1, [(11, 1)], [], 0⟩])

/-- The proof of the `.rpf`, verbatim: the named subtrees with their entry
contexts, in declaration order, and the main tree.  A `use` node carries one
entailment certificate per entry form of the subtree it cites. -/
def proof : PProof where
  subs :=
    [([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, 0, -1, 0, 0, 0, 1], [0, 0, 1, -1, 0, 0, 0, 1], [0, 0, 0, 0, 1, -1, 0, 1], [0, 0, 0, 0, 0, -1, 1, 1], [-1, 0, 0, 0, 0, 0, 0, 1]], sub0),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, 0, -1, 0, 0, 0, 1], [0, 0, 1, -1, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, 1], [0, 0, 0, 0, -1, 1, 0, -1], [-1, 0, 0, 0, 0, 0, 0, 1]], sub1),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, 0, -1, 0, 0, 0, 1], [0, 0, 1, -1, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, -1, -1], [-1, 0, 0, 0, 0, 0, 0, 1]], sub2),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, -1, 1], [0, -1, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 1, -1, 0, 1], [0, 0, 0, 0, 0, -1, 1, 1], [-1, 0, 0, 0, 0, 0, 0, 1]], sub3),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, -1, 1], [0, -1, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, -1, 0, 1], [0, 0, 0, 0, -1, 1, 0, -1], [-1, 0, 0, 0, 0, 0, 0, 1]], sub4),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, -1, 1], [0, -1, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, -1, -1], [-1, 0, 0, 0, 0, 0, 0, 1]], sub5),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, -1], [0, 0, -1, 1, 0, 0, 0, -1], [0, 0, 0, 0, 1, -1, 0, 1], [0, 0, 0, 0, 0, -1, 1, 1], [-1, 0, 0, 0, 0, 0, 0, 1]], sub6),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, -1], [0, 0, -1, 1, 0, 0, 0, -1], [0, 0, 0, 0, -1, 0, 1], [0, 0, 0, 0, -1, 1, 0, -1], [-1, 0, 0, 0, 0, 0, 0, 1]], sub7),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, -1], [0, 0, -1, 1, 0, 0, 0, -1], [0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, -1, -1], [-1, 0, 0, 0, 0, 0, 0, 1]], sub8),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, 0, -1, 0, 0, 0, 1], [0, 0, 1, -1, 0, 0, 0, 1], [0, 0, 0, 0, 1, -1, 0, 1], [0, 0, 0, 0, 0, -1, 1, 1], [0, 0, 0, 0, 0, 0, 0, -1]], sub9),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, 0, -1, 0, 0, 0, 1], [0, 0, 1, -1, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, 1], [0, 0, 0, 0, -1, 1, 0, -1], [0, 0, 0, 0, 0, 0, 0, -1]], sub10),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, 0, -1, 0, 0, 0, 1], [0, 0, 1, -1, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, -1, -1], [0, 0, 0, 0, 0, 0, 0, -1]], sub11),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, -1, 1], [0, -1, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 1, -1, 0, 1], [0, 0, 0, 0, 0, -1, 1, 1], [0, 0, 0, 0, 0, 0, 0, -1]], sub12),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, -1, 1], [0, -1, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, -1, 0, 1], [0, 0, 0, 0, -1, 1, 0, -1], [0, 0, 0, 0, 0, 0, 0, -1]], sub13),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, -1, 1], [0, -1, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, -1, -1], [0, 0, 0, 0, 0, 0, 0, -1]], sub14),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, -1], [0, 0, -1, 1, 0, 0, 0, -1], [0, 0, 0, 0, 1, -1, 0, 1], [0, 0, 0, 0, 0, -1, 1, 1], [0, 0, 0, 0, 0, 0, 0, -1]], sub15),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, -1], [0, 0, -1, 1, 0, 0, 0, -1], [0, 0, 0, 0, -1, 0, 1], [0, 0, 0, 0, -1, 1, 0, -1], [0, 0, 0, 0, 0, 0, 0, -1]], sub16),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 1, -1], [0, 0, -1, 1, 0, 0, 0, -1], [0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, -1, -1], [0, 0, 0, 0, 0, 0, 0, -1]], sub17),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [-1, 0, 0, 0, 0, 0, 0, 1]], sub18),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 0, 0, -1]], sub19),
     ([[0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 1, 0, -1]], sub20)]
  main :=
  .split [0, 0, 0, 1, 0, 0, 0, -1]
    (.split [0, 0, 0, 0, 0, 1, 0, -1]
      (.use 20 [⟨1, [(9, 1)], [], 0⟩, ⟨1, [(10, 1)], [], 0⟩])
      (.auto { vertex := [1, 3, 0, 5, 2, 4], vertexInv := [2, 0, 4, 1, 5, 3], slot := [5, 3, 4, 0, 6, 8, 2, 1, 7], slotInv := [3, 7, 6, 1, 2, 0, 4, 8, 5], reversed := [false, false, false, true, true, false, false, false, true] }
        (.use 20 [⟨1, [(10, 1)], [], 1⟩, ⟨1, [(9, 1), (10, 1)], [], 1⟩])))
    (.split [0, 0, 0, 1, 0, -1]
      (.auto { vertex := [1, 3, 0, 5, 2, 4], vertexInv := [2, 0, 4, 1, 5, 3], slot := [5, 3, 4, 0, 6, 8, 2, 1, 7], slotInv := [3, 7, 6, 1, 2, 0, 4, 8, 5], reversed := [false, false, false, true, true, false, false, false, true] }
        (.use 20 [⟨1, [(9, 1), (10, 1)], [], 1⟩, ⟨1, [(10, 1)], [], 0⟩]))
      (.auto { vertex := [1, 3, 0, 5, 2, 4], vertexInv := [2, 0, 4, 1, 5, 3], slot := [5, 3, 4, 0, 6, 8, 2, 1, 7], slotInv := [3, 7, 6, 1, 2, 0, 4, 8, 5], reversed := [false, false, false, true, true, false, false, false, true] }
        (.auto { vertex := [1, 3, 0, 5, 2, 4], vertexInv := [2, 0, 4, 1, 5, 3], slot := [5, 3, 4, 0, 6, 8, 2, 1, 7], slotInv := [3, 7, 6, 1, 2, 0, 4, 8, 5], reversed := [false, false, false, true, true, false, false, false, true] }
          (.use 20 [⟨1, [(10, 1)], [], 1⟩, ⟨1, [(9, 1)], [], 1⟩]))))

/-- The deep-embedded checker accepts, by kernel reduction.

`decide +kernel` uses ordinary kernel reduction and avoids duplicate evaluation by the elaborator. -/
theorem checks :
    PProof.checks 9 core 3 (rootContextClosed 9) proof = true := by
  decide +kernel

/-- **`BNExists … 1 3` for catalog row `g4row100`, from its `.rpf` and nothing
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

end AtanasovRanganathan.GenusFourGeneratedRows.G4Row100
