/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow12
public import LeanPool.BrillNoetherGraphs.LowGenus.GuardingSet

/-!
# Row 12 as a guarding set

`LowGenus/GuardingSet.lean` claims that the closing step of an
Atanasov--Ranganathan row proof is generic: pick a core-supported chip
assignment of degree four, cover every chip-free vertex by library pictures,
and the closed-orthant construction follows.  This file cashes that claim on
the row where the composition is most visible.

Row 12's chip-free vertices are covered by **two different pictures** -- the
AR configuration-3 pair `2--7` and the AR configuration-2 tripods -- and
`GenusFiveRow12.centers_cover` is the row's hand-written statement that
between them they name every chip-free vertex.  Here that same fact is fed
straight into the `guard` field of a `GuardingSet`, and
`GuardingSet.closedConstruction` produces the row's theorem with no further
row-specific work: no divisor bookkeeping, no `fin_cases`, no separator
argument.

`coreClassDivisor_eq_fourChipDivisor` identifies the guarding set's class
divisor with the four-chip divisor the two configuration files display, so this
is a proof about AR's own divisor and not merely a similar one.  As of
2026-08-25 it is the row's **only** proof: `GenusFiveRow12`'s hand-written
`rowDivisor_reaches_coreVertex` / `row12_closedConstruction` tail has been
deleted, and `GenusFiveConstructions.row12_straightforward` points here.
-/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow12Guarding

open Utilities

open Certificate
open Certificate.ExplicitPotential
open Certificate.DegenerateSpec
open Certificate.DegenerateSpec.DegSpec
open Certificate.StrongSeparator
open Utilities.Certificate.ContractionForestCensusGeneral
open Configurations
open GenusFiveCoreAtlas
open Guarding
open GenusFiveRow12

/-- The guarding set of row 12: chips on `3, 4, 5, 6`, with the AR
configuration-3 pair and the AR configuration-2 tripods between them guarding
every chip-free vertex. -/
def row12Guard : GuardingSet row12Core where
  chips := fourChipWeight 3 4 5 6
  chips_nonneg := fourChipWeight_nonneg 3 4 5 6
  chips_deg := fourChipWeight_deg (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  guard := by
    intro v hv d hCore hRepReach
    rw [coreClassDivisor_eq_fourChipDivisor d (a := 3) (b := 4) (c := 5)
      (e := 6) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]
    have hNotChip : ¬ row12PairConfig.IsChip v :=
      fourChipWeight_eq_zero_iff.mp hv
    rcases centers_cover v hNotChip with hPair | hTripod
    · exact row12PairConfig.reaches_center d hCore (zeroSlots d.length)
        hRepReach (mem_zeroSlots d.length) hPair
    · exact GenusFiveRow12Tripod.row12TripodConfig.reaches_center d hCore
        (zeroSlots d.length) hRepReach hTripod

/-- **AR row 12, proved from a guarding set.**  Every step after "here are the
chips and here are their pictures" is generic.  This is the row's canonical
proof: `GenusFiveConstructions.row12_straightforward` points here, and the
hand-written composition that used to live in `GenusFiveRow12` is retired. -/
theorem row12_closedConstruction :
    ClosedSubdivisionDharConstruction row12Core (by norm_num) :=
  row12Guard.closedConstruction (by norm_num) row12_connected

end AtanasovRanganathan.GenusFiveRow12Guarding
