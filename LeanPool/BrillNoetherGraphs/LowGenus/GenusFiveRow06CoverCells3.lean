/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow06CoverBase

/-! **Independent generated check.** This module provides an additional generated proof of row 06
and is not imported by the main `LowGenus` root.

Generated cell chunk 3 of 5 for the AR row-06 chamber cover
(cells 291-386).  Split across modules because the kernel cost of
replaying a cell is cumulative within one Lean process. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06CoverCells3

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations
open GenusFiveRow06CoverBase

/-- Closed-cover cell 291 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 4, 30, 6]`; `cell291_check` verifies its
explicit-potential certificate. -/
def cell291 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell291_check :
    cell291.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 292 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 4, 30, 6]`; `cell292_check` verifies its
explicit-potential certificate. -/
def cell292 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell292_check :
    cell292.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 293 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 4, 30, 6]`; `cell293_check` verifies its
explicit-potential certificate. -/
def cell293 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell293_check :
    cell293.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 294 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 4, 30, 6]`; `cell294_check` verifies
its explicit-potential certificate. -/
def cell294 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell294_check :
    cell294.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 295 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 4, 30, 6]`; `cell295_check` verifies
its explicit-potential certificate. -/
def cell295 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 4, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell295_check :
    cell295.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 296 for the fixed row-06 divisor, with 18 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 17, 27, 6]`; `cell296_check` verifies
its explicit-potential certificate. -/
def cell296 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 17, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell296_check :
    cell296.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 297 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 17, 28, 6]`; `cell297_check` verifies
its explicit-potential certificate. -/
def cell297 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 17, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell297_check :
    cell297.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 298 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 17, 29, 6]`; `cell298_check` verifies
its explicit-potential certificate. -/
def cell298 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 17, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell298_check :
    cell298.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 299 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 17, 30, 6]`; `cell299_check` verifies
its explicit-potential certificate. -/
def cell299 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 17, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell299_check :
    cell299.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 300 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 18, 27, 6]`; `cell300_check` verifies
its explicit-potential certificate. -/
def cell300 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 18, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell300_check :
    cell300.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 301 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 18, 28, 6]`; `cell301_check` verifies
its explicit-potential certificate. -/
def cell301 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 18, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell301_check :
    cell301.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 302 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 18, 29, 6]`; `cell302_check` verifies
its explicit-potential certificate. -/
def cell302 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 18, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell302_check :
    cell302.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 303 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 18, 30, 6]`; `cell303_check` verifies
its explicit-potential certificate. -/
def cell303 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 18, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell303_check :
    cell303.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 304 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 19, 27, 6]`; `cell304_check` verifies
its explicit-potential certificate. -/
def cell304 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 19, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell304_check :
    cell304.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 305 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 19, 28, 6]`; `cell305_check` verifies
its explicit-potential certificate. -/
def cell305 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 19, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell305_check :
    cell305.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 306 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 19, 29, 6]`; `cell306_check` verifies
its explicit-potential certificate. -/
def cell306 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 19, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell306_check :
    cell306.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 307 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 19, 30, 6]`; `cell307_check` verifies
its explicit-potential certificate. -/
def cell307 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 19, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell307_check :
    cell307.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 308 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 21, 27, 6]`; `cell308_check` verifies
its explicit-potential certificate. -/
def cell308 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 21, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell308_check :
    cell308.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 309 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 21, 28, 6]`; `cell309_check` verifies
its explicit-potential certificate. -/
def cell309 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 21, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell309_check :
    cell309.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 310 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 21, 29, 6]`; `cell310_check` verifies
its explicit-potential certificate. -/
def cell310 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 21, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell310_check :
    cell310.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 311 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 2, 2, 3, 21, 30, 6]`; `cell311_check` verifies
its explicit-potential certificate. -/
def cell311 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 2, 2, 3, 21, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell311_check :
    cell311.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 312 for the fixed row-06 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 17, 27, 6]`; `cell312_check` verifies
its explicit-potential certificate. -/
def cell312 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 17, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell312_check :
    cell312.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 313 for the fixed row-06 divisor, with 18 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 17, 27, 6]`; `cell313_check` verifies
its explicit-potential certificate. -/
def cell313 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 17, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell313_check :
    cell313.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 314 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 17, 27, 6]`; `cell314_check` verifies
its explicit-potential certificate. -/
def cell314 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 17, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell314_check :
    cell314.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 315 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 17, 27, 6]`; `cell315_check` verifies
its explicit-potential certificate. -/
def cell315 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 17, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell315_check :
    cell315.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 316 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 17, 27, 6]`; `cell316_check` verifies
its explicit-potential certificate. -/
def cell316 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 17, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell316_check :
    cell316.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 317 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 17, 28, 6]`; `cell317_check` verifies
its explicit-potential certificate. -/
def cell317 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 17, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell317_check :
    cell317.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 318 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 17, 28, 6]`; `cell318_check` verifies
its explicit-potential certificate. -/
def cell318 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 17, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell318_check :
    cell318.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 319 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 17, 28, 6]`; `cell319_check` verifies
its explicit-potential certificate. -/
def cell319 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 17, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell319_check :
    cell319.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 320 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 17, 28, 6]`; `cell320_check` verifies
its explicit-potential certificate. -/
def cell320 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 17, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell320_check :
    cell320.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 321 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 17, 28, 6]`; `cell321_check` verifies
its explicit-potential certificate. -/
def cell321 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 17, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell321_check :
    cell321.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 322 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 17, 29, 6]`; `cell322_check` verifies
its explicit-potential certificate. -/
def cell322 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 17, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell322_check :
    cell322.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 323 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 17, 29, 6]`; `cell323_check` verifies
its explicit-potential certificate. -/
def cell323 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 17, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell323_check :
    cell323.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 324 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 17, 29, 6]`; `cell324_check` verifies
its explicit-potential certificate. -/
def cell324 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 17, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell324_check :
    cell324.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 325 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 17, 29, 6]`; `cell325_check` verifies
its explicit-potential certificate. -/
def cell325 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 17, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell325_check :
    cell325.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 326 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 17, 29, 6]`; `cell326_check` verifies
its explicit-potential certificate. -/
def cell326 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 17, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell326_check :
    cell326.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 327 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 17, 30, 6]`; `cell327_check` verifies
its explicit-potential certificate. -/
def cell327 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 17, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell327_check :
    cell327.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 328 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 17, 30, 6]`; `cell328_check` verifies
its explicit-potential certificate. -/
def cell328 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 17, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell328_check :
    cell328.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 329 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 17, 30, 6]`; `cell329_check` verifies
its explicit-potential certificate. -/
def cell329 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 17, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell329_check :
    cell329.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 330 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 17, 30, 6]`; `cell330_check` verifies
its explicit-potential certificate. -/
def cell330 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 17, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell330_check :
    cell330.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 331 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 17, 30, 6]`; `cell331_check` verifies
its explicit-potential certificate. -/
def cell331 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 17, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell331_check :
    cell331.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 332 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 18, 27, 6]`; `cell332_check` verifies
its explicit-potential certificate. -/
def cell332 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 18, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell332_check :
    cell332.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 333 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 18, 27, 6]`; `cell333_check` verifies
its explicit-potential certificate. -/
def cell333 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 18, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell333_check :
    cell333.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 334 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 18, 27, 6]`; `cell334_check` verifies
its explicit-potential certificate. -/
def cell334 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 18, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell334_check :
    cell334.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 335 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 18, 27, 6]`; `cell335_check` verifies
its explicit-potential certificate. -/
def cell335 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 18, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell335_check :
    cell335.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 336 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 18, 27, 6]`; `cell336_check` verifies
its explicit-potential certificate. -/
def cell336 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 18, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell336_check :
    cell336.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 337 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 18, 28, 6]`; `cell337_check` verifies
its explicit-potential certificate. -/
def cell337 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 18, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell337_check :
    cell337.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 338 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 18, 28, 6]`; `cell338_check` verifies
its explicit-potential certificate. -/
def cell338 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 18, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell338_check :
    cell338.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 339 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 18, 28, 6]`; `cell339_check` verifies
its explicit-potential certificate. -/
def cell339 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 18, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell339_check :
    cell339.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 340 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 18, 28, 6]`; `cell340_check` verifies
its explicit-potential certificate. -/
def cell340 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 18, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell340_check :
    cell340.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 341 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 18, 28, 6]`; `cell341_check` verifies
its explicit-potential certificate. -/
def cell341 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 18, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell341_check :
    cell341.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 342 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 18, 29, 6]`; `cell342_check` verifies
its explicit-potential certificate. -/
def cell342 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 18, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell342_check :
    cell342.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 343 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 18, 29, 6]`; `cell343_check` verifies
its explicit-potential certificate. -/
def cell343 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 18, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell343_check :
    cell343.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 344 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 18, 29, 6]`; `cell344_check` verifies
its explicit-potential certificate. -/
def cell344 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 18, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell344_check :
    cell344.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 345 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 18, 29, 6]`; `cell345_check` verifies
its explicit-potential certificate. -/
def cell345 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 18, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell345_check :
    cell345.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 346 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 18, 29, 6]`; `cell346_check` verifies
its explicit-potential certificate. -/
def cell346 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 18, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell346_check :
    cell346.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 347 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 18, 30, 6]`; `cell347_check` verifies
its explicit-potential certificate. -/
def cell347 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 18, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell347_check :
    cell347.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 348 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 18, 30, 6]`; `cell348_check` verifies
its explicit-potential certificate. -/
def cell348 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 18, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell348_check :
    cell348.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 349 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 18, 30, 6]`; `cell349_check` verifies
its explicit-potential certificate. -/
def cell349 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 18, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell349_check :
    cell349.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 350 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 18, 30, 6]`; `cell350_check` verifies
its explicit-potential certificate. -/
def cell350 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 18, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell350_check :
    cell350.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 351 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 19, 27, 6]`; `cell351_check` verifies
its explicit-potential certificate. -/
def cell351 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 19, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell351_check :
    cell351.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 352 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 19, 27, 6]`; `cell352_check` verifies
its explicit-potential certificate. -/
def cell352 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 19, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell352_check :
    cell352.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 353 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 19, 27, 6]`; `cell353_check` verifies
its explicit-potential certificate. -/
def cell353 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 19, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell353_check :
    cell353.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 354 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 19, 27, 6]`; `cell354_check` verifies
its explicit-potential certificate. -/
def cell354 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 19, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell354_check :
    cell354.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 355 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 19, 27, 6]`; `cell355_check` verifies
its explicit-potential certificate. -/
def cell355 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 19, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell355_check :
    cell355.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 356 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 19, 28, 6]`; `cell356_check` verifies
its explicit-potential certificate. -/
def cell356 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 19, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell356_check :
    cell356.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 357 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 19, 28, 6]`; `cell357_check` verifies
its explicit-potential certificate. -/
def cell357 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 19, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell357_check :
    cell357.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 358 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 19, 28, 6]`; `cell358_check` verifies
its explicit-potential certificate. -/
def cell358 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 19, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell358_check :
    cell358.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 359 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 19, 28, 6]`; `cell359_check` verifies
its explicit-potential certificate. -/
def cell359 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 19, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell359_check :
    cell359.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 360 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 19, 28, 6]`; `cell360_check` verifies
its explicit-potential certificate. -/
def cell360 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 19, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell360_check :
    cell360.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 361 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 19, 29, 6]`; `cell361_check` verifies
its explicit-potential certificate. -/
def cell361 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 19, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell361_check :
    cell361.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 362 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 19, 29, 6]`; `cell362_check` verifies
its explicit-potential certificate. -/
def cell362 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 19, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell362_check :
    cell362.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 363 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 19, 29, 6]`; `cell363_check` verifies
its explicit-potential certificate. -/
def cell363 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 19, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell363_check :
    cell363.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 364 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 19, 29, 6]`; `cell364_check` verifies
its explicit-potential certificate. -/
def cell364 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 19, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell364_check :
    cell364.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 365 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 19, 29, 6]`; `cell365_check` verifies
its explicit-potential certificate. -/
def cell365 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 19, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell365_check :
    cell365.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 366 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 19, 30, 6]`; `cell366_check` verifies
its explicit-potential certificate. -/
def cell366 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 19, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1], aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell366_check :
    cell366.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 367 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 19, 30, 6]`; `cell367_check` verifies
its explicit-potential certificate. -/
def cell367 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 19, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell367_check :
    cell367.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 368 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 19, 30, 6]`; `cell368_check` verifies
its explicit-potential certificate. -/
def cell368 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 19, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell368_check :
    cell368.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 369 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 19, 30, 6]`; `cell369_check` verifies
its explicit-potential certificate. -/
def cell369 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 19, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell369_check :
    cell369.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 370 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 19, 30, 6]`; `cell370_check` verifies
its explicit-potential certificate. -/
def cell370 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 19, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2, -1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell370_check :
    cell370.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 371 for the fixed row-06 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 21, 27, 6]`; `cell371_check` verifies
its explicit-potential certificate. -/
def cell371 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 21, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1], aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell371_check :
    cell371.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 372 for the fixed row-06 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 21, 27, 6]`; `cell372_check` verifies
its explicit-potential certificate. -/
def cell372 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 21, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell372_check :
    cell372.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 373 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 21, 27, 6]`; `cell373_check` verifies
its explicit-potential certificate. -/
def cell373 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 21, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell373_check :
    cell373.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 374 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 21, 27, 6]`; `cell374_check` verifies
its explicit-potential certificate. -/
def cell374 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 21, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell374_check :
    cell374.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 375 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 21, 27, 6]`; `cell375_check` verifies
its explicit-potential certificate. -/
def cell375 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 21, 27, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell375_check :
    cell375.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 376 for the fixed row-06 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 7, 2, 2, 3, 21, 28, 6]`; `cell376_check` verifies
its explicit-potential certificate. -/
def cell376 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 7, 2, 2, 3, 21, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell376_check :
    cell376.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 377 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 21, 28, 6]`; `cell377_check` verifies
its explicit-potential certificate. -/
def cell377 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 21, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell377_check :
    cell377.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 378 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 21, 28, 6]`; `cell378_check` verifies
its explicit-potential certificate. -/
def cell378 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 21, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell378_check :
    cell378.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 379 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 21, 28, 6]`; `cell379_check` verifies
its explicit-potential certificate. -/
def cell379 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 21, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell379_check :
    cell379.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 380 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 2, 2, 3, 21, 28, 6]`; `cell380_check` verifies
its explicit-potential certificate. -/
def cell380 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 2, 2, 3, 21, 28, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell380_check :
    cell380.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 381 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 21, 29, 6]`; `cell381_check` verifies
its explicit-potential certificate. -/
def cell381 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 21, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell381_check :
    cell381.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 382 for the fixed row-06 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 2, 2, 3, 21, 30, 6]`; `cell382_check` verifies
its explicit-potential certificate. -/
def cell382 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 2, 2, 3, 21, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell382_check :
    cell382.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 383 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 21, 29, 6]`; `cell383_check` verifies
its explicit-potential certificate. -/
def cell383 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 21, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell383_check :
    cell383.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 384 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 9, 2, 2, 3, 21, 30, 6]`; `cell384_check` verifies
its explicit-potential certificate. -/
def cell384 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 9, 2, 2, 3, 21, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell384_check :
    cell384.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 385 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 21, 29, 6]`; `cell385_check` verifies
its explicit-potential certificate. -/
def cell385 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 21, 29, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, -2, -1, 0, 2, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell385_check :
    cell385.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 386 for the fixed row-06 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 10, 2, 2, 3, 21, 30, 6]`; `cell386_check` verifies
its explicit-potential certificate. -/
def cell386 : CoordinateCell row06Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 10, 2, 2, 3, 21, 30, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 1, 0],
      aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 2, 0, 1],
      aff [0, 0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0],
      aff [0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell386_check :
    cell386.certificate.checkClosed 4 = true := by
  decide +kernel

/-- The ordered row-06 closed-cover cell block with global indices 291 through 386, used when
assembling the full 483-cell cover. -/
def chunk : List (CoordinateCell row06Core) := [cell291, cell292, cell293, cell294, cell295, cell296, cell297, cell298, cell299, cell300, cell301, cell302, cell303, cell304, cell305, cell306, cell307, cell308, cell309, cell310, cell311, cell312, cell313, cell314, cell315, cell316, cell317, cell318, cell319, cell320, cell321, cell322, cell323, cell324, cell325, cell326, cell327, cell328, cell329, cell330, cell331, cell332, cell333, cell334, cell335, cell336, cell337, cell338, cell339, cell340, cell341, cell342, cell343, cell344, cell345, cell346, cell347, cell348, cell349, cell350, cell351, cell352, cell353, cell354, cell355, cell356, cell357, cell358, cell359, cell360, cell361, cell362, cell363, cell364, cell365, cell366, cell367, cell368, cell369, cell370, cell371, cell372, cell373, cell374, cell375, cell376, cell377, cell378, cell379, cell380, cell381, cell382, cell383, cell384, cell385, cell386]

theorem chunk_check :
    chunk.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [chunk, cell291_check, cell292_check, cell293_check, cell294_check, cell295_check, cell296_check, cell297_check, cell298_check, cell299_check, cell300_check, cell301_check, cell302_check, cell303_check, cell304_check, cell305_check, cell306_check, cell307_check, cell308_check, cell309_check, cell310_check, cell311_check, cell312_check, cell313_check, cell314_check, cell315_check, cell316_check, cell317_check, cell318_check, cell319_check, cell320_check, cell321_check, cell322_check, cell323_check, cell324_check, cell325_check, cell326_check, cell327_check, cell328_check, cell329_check, cell330_check, cell331_check, cell332_check, cell333_check, cell334_check, cell335_check, cell336_check, cell337_check, cell338_check, cell339_check, cell340_check, cell341_check, cell342_check, cell343_check, cell344_check, cell345_check, cell346_check, cell347_check, cell348_check, cell349_check, cell350_check, cell351_check, cell352_check, cell353_check, cell354_check, cell355_check, cell356_check, cell357_check, cell358_check, cell359_check, cell360_check, cell361_check, cell362_check, cell363_check, cell364_check, cell365_check, cell366_check, cell367_check, cell368_check, cell369_check, cell370_check, cell371_check, cell372_check, cell373_check, cell374_check, cell375_check, cell376_check, cell377_check, cell378_check, cell379_check, cell380_check, cell381_check, cell382_check, cell383_check, cell384_check, cell385_check, cell386_check]

end AtanasovRanganathan.GenusFiveRow06CoverCells3
