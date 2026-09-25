/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveRow04CoverBase

/-! **Independent generated check.** This module provides an additional generated proof of row 04 and is not imported by the main `LowGenus` root.

Generated cell chunk 0 of 2 for the AR row-04 chamber cover
(cells 0-97).  Split across modules because the kernel cost of
replaying a cell is cumulative within one Lean process. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow04CoverCells0

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations
open GenusFiveRow04CoverBase

/-- Closed-cover cell 0 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 3, 0, 0, 4]`; `cell0_check` verifies its
explicit-potential certificate. -/
def cell0 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 3, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell0_check :
    cell0.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 1 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 3, 0, 0, 5]`; `cell1_check` verifies its
explicit-potential certificate. -/
def cell1 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 3, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell1_check :
    cell1.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 2 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 3, 0, 0, 6]`; `cell2_check` verifies its
explicit-potential certificate. -/
def cell2 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 3, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell2_check :
    cell2.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 3 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 3, 0, 0, 7]`; `cell3_check` verifies its
explicit-potential certificate. -/
def cell3 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 3, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell3_check :
    cell3.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 4 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 8, 0, 0, 4]`; `cell4_check` verifies its
explicit-potential certificate. -/
def cell4 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 8, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell4_check :
    cell4.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 5 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 9, 0, 0, 4]`; `cell5_check` verifies its
explicit-potential certificate. -/
def cell5 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 9, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell5_check :
    cell5.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 6 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 10, 0, 0, 4]`; `cell6_check` verifies its
explicit-potential certificate. -/
def cell6 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 10, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell6_check :
    cell6.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 7 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 8, 0, 0, 5]`; `cell7_check` verifies its
explicit-potential certificate. -/
def cell7 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 8, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell7_check :
    cell7.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 8 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 8, 0, 0, 6]`; `cell8_check` verifies its
explicit-potential certificate. -/
def cell8 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 8, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell8_check :
    cell8.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 9 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 8, 0, 0, 7]`; `cell9_check` verifies its
explicit-potential certificate. -/
def cell9 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 8, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell9_check :
    cell9.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 10 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 9, 0, 0, 5]`; `cell10_check` verifies its
explicit-potential certificate. -/
def cell10 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 9, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell10_check :
    cell10.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 11 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 9, 0, 0, 6]`; `cell11_check` verifies its
explicit-potential certificate. -/
def cell11 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 9, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell11_check :
    cell11.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 12 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 9, 0, 0, 7]`; `cell12_check` verifies its
explicit-potential certificate. -/
def cell12 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 9, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell12_check :
    cell12.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 13 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 10, 0, 0, 5]`; `cell13_check` verifies its
explicit-potential certificate. -/
def cell13 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 10, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell13_check :
    cell13.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 14 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 10, 0, 0, 6]`; `cell14_check` verifies its
explicit-potential certificate. -/
def cell14 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 10, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell14_check :
    cell14.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 15 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 2, 10, 0, 0, 7]`; `cell15_check` verifies its
explicit-potential certificate. -/
def cell15 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 2, 10, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell15_check :
    cell15.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 16 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 11, 0, 2, 12, 0, 0, 4]`; `cell16_check` verifies its
explicit-potential certificate. -/
def cell16 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 11, 0, 2, 12, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell16_check :
    cell16.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 17 for the fixed row-04 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 2, 8, 0, 0, 4]`; `cell17_check` verifies its
explicit-potential certificate. -/
def cell17 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 2, 8, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell17_check :
    cell17.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 18 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 2, 14, 0, 0, 4]`; `cell18_check` verifies its
explicit-potential certificate. -/
def cell18 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 2, 14, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell18_check :
    cell18.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 19 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 2, 8, 0, 0, 4]`; `cell19_check` verifies its
explicit-potential certificate. -/
def cell19 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 2, 8, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell19_check :
    cell19.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 20 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 2, 9, 0, 0, 4]`; `cell20_check` verifies its
explicit-potential certificate. -/
def cell20 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 2, 9, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell20_check :
    cell20.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 21 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 18, 0, 0, 4]`; `cell21_check` verifies its
explicit-potential certificate. -/
def cell21 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 18, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell21_check :
    cell21.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 22 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 10, 0, 0, 4]`; `cell22_check` verifies its
explicit-potential certificate. -/
def cell22 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 10, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell22_check :
    cell22.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 23 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 2, 14, 0, 0, 4]`; `cell23_check` verifies its
explicit-potential certificate. -/
def cell23 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 2, 14, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell23_check :
    cell23.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 24 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 20, 0, 2, 14, 0, 0, 4]`; `cell24_check` verifies its
explicit-potential certificate. -/
def cell24 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 20, 0, 2, 14, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, -1, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell24_check :
    cell24.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 25 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 2, 8, 0, 0, 5]`; `cell25_check` verifies its
explicit-potential certificate. -/
def cell25 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 2, 8, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell25_check :
    cell25.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 26 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 2, 8, 0, 0, 6]`; `cell26_check` verifies its
explicit-potential certificate. -/
def cell26 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 2, 8, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell26_check :
    cell26.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 27 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 2, 8, 0, 0, 7]`; `cell27_check` verifies its
explicit-potential certificate. -/
def cell27 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 2, 8, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell27_check :
    cell27.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 28 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 2, 14, 0, 0, 5]`; `cell28_check` verifies its
explicit-potential certificate. -/
def cell28 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 2, 14, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell28_check :
    cell28.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 29 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 2, 14, 0, 0, 6]`; `cell29_check` verifies its
explicit-potential certificate. -/
def cell29 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 2, 14, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell29_check :
    cell29.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 30 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 15, 0, 2, 14, 0, 0, 7]`; `cell30_check` verifies its
explicit-potential certificate. -/
def cell30 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 15, 0, 2, 14, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell30_check :
    cell30.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 31 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 2, 14, 0, 0, 5]`; `cell31_check` verifies its
explicit-potential certificate. -/
def cell31 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 2, 14, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell31_check :
    cell31.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 32 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 2, 14, 0, 0, 6]`; `cell32_check` verifies its
explicit-potential certificate. -/
def cell32 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 2, 14, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell32_check :
    cell32.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 33 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 19, 0, 2, 14, 0, 0, 7]`; `cell33_check` verifies its
explicit-potential certificate. -/
def cell33 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 19, 0, 2, 14, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell33_check :
    cell33.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 34 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 2, 8, 0, 0, 5]`; `cell34_check` verifies its
explicit-potential certificate. -/
def cell34 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 2, 8, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell34_check :
    cell34.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 35 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 2, 8, 0, 0, 6]`; `cell35_check` verifies its
explicit-potential certificate. -/
def cell35 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 2, 8, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell35_check :
    cell35.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 36 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 2, 8, 0, 0, 7]`; `cell36_check` verifies its
explicit-potential certificate. -/
def cell36 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 2, 8, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell36_check :
    cell36.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 37 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 2, 14, 0, 0, 5]`; `cell37_check` verifies its
explicit-potential certificate. -/
def cell37 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 2, 14, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell37_check :
    cell37.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 38 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 2, 14, 0, 0, 6]`; `cell38_check` verifies its
explicit-potential certificate. -/
def cell38 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 2, 14, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell38_check :
    cell38.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 39 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 13, 0, 2, 14, 0, 0, 7]`; `cell39_check` verifies its
explicit-potential certificate. -/
def cell39 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 13, 0, 2, 14, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell39_check :
    cell39.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 40 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 2, 9, 0, 0, 5]`; `cell40_check` verifies its
explicit-potential certificate. -/
def cell40 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 2, 9, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell40_check :
    cell40.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 41 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 2, 9, 0, 0, 6]`; `cell41_check` verifies its
explicit-potential certificate. -/
def cell41 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 2, 9, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell41_check :
    cell41.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 42 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 16, 0, 2, 9, 0, 0, 7]`; `cell42_check` verifies its
explicit-potential certificate. -/
def cell42 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 16, 0, 2, 9, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell42_check :
    cell42.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 43 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 18, 0, 0, 5]`; `cell43_check` verifies its
explicit-potential certificate. -/
def cell43 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 18, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell43_check :
    cell43.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 44 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 10, 0, 0, 5]`; `cell44_check` verifies its
explicit-potential certificate. -/
def cell44 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 10, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell44_check :
    cell44.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 45 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 18, 0, 0, 6]`; `cell45_check` verifies its
explicit-potential certificate. -/
def cell45 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 18, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell45_check :
    cell45.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 46 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 10, 0, 0, 6]`; `cell46_check` verifies its
explicit-potential certificate. -/
def cell46 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 10, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell46_check :
    cell46.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 47 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 18, 0, 0, 7]`; `cell47_check` verifies its
explicit-potential certificate. -/
def cell47 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 18, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 2, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell47_check :
    cell47.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 48 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 10, 0, 0, 7]`; `cell48_check` verifies its
explicit-potential certificate. -/
def cell48 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 10, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell48_check :
    cell48.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 49 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 9, 0, 0, 4]`; `cell49_check` verifies its
explicit-potential certificate. -/
def cell49 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 9, 0, 0, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1]] }

theorem cell49_check :
    cell49.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 50 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 9, 0, 0, 5]`; `cell50_check` verifies its
explicit-potential certificate. -/
def cell50 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 9, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell50_check :
    cell50.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 51 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 9, 0, 0, 6]`; `cell51_check` verifies its
explicit-potential certificate. -/
def cell51 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 9, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell51_check :
    cell51.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 52 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 17, 0, 2, 9, 0, 0, 7]`; `cell52_check` verifies its
explicit-potential certificate. -/
def cell52 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 17, 0, 2, 9, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell52_check :
    cell52.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 53 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 21, 3, 0, 0, 22]`; `cell53_check` verifies its
explicit-potential certificate. -/
def cell53 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 21, 3, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]] }

theorem cell53_check :
    cell53.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 54 for the fixed row-04 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 5, 3, 0, 0, 5]`; `cell54_check` verifies its
explicit-potential certificate. -/
def cell54 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 5, 3, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]] }

theorem cell54_check :
    cell54.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 55 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 23, 3, 0, 0, 24]`; `cell55_check` verifies its
explicit-potential certificate. -/
def cell55 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 23, 3, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell55_check :
    cell55.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 56 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 25, 3, 0, 0, 6]`; `cell56_check` verifies its
explicit-potential certificate. -/
def cell56 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 25, 3, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1]] }

theorem cell56_check :
    cell56.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 57 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 26, 3, 0, 0, 5]`; `cell57_check` verifies its
explicit-potential certificate. -/
def cell57 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 26, 3, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell57_check :
    cell57.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 58 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 3, 0, 0, 28]`; `cell58_check` verifies its
explicit-potential certificate. -/
def cell58 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 3, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

theorem cell58_check :
    cell58.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 59 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 3, 0, 0, 7]`; `cell59_check` verifies its
explicit-potential certificate. -/
def cell59 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 3, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell59_check :
    cell59.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 60 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 29, 3, 0, 0, 24]`; `cell60_check` verifies its
explicit-potential certificate. -/
def cell60 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 29, 3, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell60_check :
    cell60.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 61 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 26, 3, 0, 0, 24]`; `cell61_check` verifies its
explicit-potential certificate. -/
def cell61 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 26, 3, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell61_check :
    cell61.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 62 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 3, 0, 0, 6]`; `cell62_check` verifies its
explicit-potential certificate. -/
def cell62 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 3, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell62_check :
    cell62.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 63 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 21, 8, 0, 0, 22]`; `cell63_check` verifies its
explicit-potential certificate. -/
def cell63 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 21, 8, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]] }

theorem cell63_check :
    cell63.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 64 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 26, 8, 0, 0, 5]`; `cell64_check` verifies its
explicit-potential certificate. -/
def cell64 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 26, 8, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell64_check :
    cell64.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 65 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 26, 8, 0, 0, 24]`; `cell65_check` verifies its
explicit-potential certificate. -/
def cell65 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 26, 8, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell65_check :
    cell65.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 66 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 5, 8, 0, 0, 5]`; `cell66_check` verifies its
explicit-potential certificate. -/
def cell66 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 5, 8, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]] }

theorem cell66_check :
    cell66.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 67 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 25, 8, 0, 0, 6]`; `cell67_check` verifies its
explicit-potential certificate. -/
def cell67 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 25, 8, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1]] }

theorem cell67_check :
    cell67.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 68 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 8, 0, 0, 28]`; `cell68_check` verifies its
explicit-potential certificate. -/
def cell68 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 8, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

theorem cell68_check :
    cell68.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 69 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 8, 0, 0, 7]`; `cell69_check` verifies its
explicit-potential certificate. -/
def cell69 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 8, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell69_check :
    cell69.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 70 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 23, 8, 0, 0, 24]`; `cell70_check` verifies its
explicit-potential certificate. -/
def cell70 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 23, 8, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell70_check :
    cell70.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 71 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 29, 8, 0, 0, 24]`; `cell71_check` verifies its
explicit-potential certificate. -/
def cell71 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 29, 8, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell71_check :
    cell71.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 72 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 21, 9, 0, 0, 22]`; `cell72_check` verifies its
explicit-potential certificate. -/
def cell72 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 21, 9, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]] }

theorem cell72_check :
    cell72.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 73 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 5, 9, 0, 0, 5]`; `cell73_check` verifies its
explicit-potential certificate. -/
def cell73 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 5, 9, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0]] }

theorem cell73_check :
    cell73.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 74 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 23, 9, 0, 0, 24]`; `cell74_check` verifies its
explicit-potential certificate. -/
def cell74 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 23, 9, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell74_check :
    cell74.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 75 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 26, 9, 0, 0, 5]`; `cell75_check` verifies its
explicit-potential certificate. -/
def cell75 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 26, 9, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell75_check :
    cell75.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 76 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 25, 9, 0, 0, 6]`; `cell76_check` verifies its
explicit-potential certificate. -/
def cell76 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 25, 9, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0]] }

theorem cell76_check :
    cell76.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 77 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 9, 0, 0, 28]`; `cell77_check` verifies its
explicit-potential certificate. -/
def cell77 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 9, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

theorem cell77_check :
    cell77.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 78 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 9, 0, 0, 7]`; `cell78_check` verifies its
explicit-potential certificate. -/
def cell78 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 9, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell78_check :
    cell78.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 79 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 29, 9, 0, 0, 24]`; `cell79_check` verifies its
explicit-potential certificate. -/
def cell79 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 29, 9, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell79_check :
    cell79.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 80 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 21, 10, 0, 0, 22]`; `cell80_check` verifies
its explicit-potential certificate. -/
def cell80 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 21, 10, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]] }

theorem cell80_check :
    cell80.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 81 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 5, 10, 0, 0, 5]`; `cell81_check` verifies its
explicit-potential certificate. -/
def cell81 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 5, 10, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1]] }

theorem cell81_check :
    cell81.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 82 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 23, 10, 0, 0, 24]`; `cell82_check` verifies
its explicit-potential certificate. -/
def cell82 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 23, 10, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell82_check :
    cell82.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 83 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 26, 10, 0, 0, 5]`; `cell83_check` verifies its
explicit-potential certificate. -/
def cell83 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 26, 10, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell83_check :
    cell83.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 84 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 25, 10, 0, 0, 6]`; `cell84_check` verifies its
explicit-potential certificate. -/
def cell84 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 25, 10, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1]] }

theorem cell84_check :
    cell84.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 85 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 10, 0, 0, 28]`; `cell85_check` verifies
its explicit-potential certificate. -/
def cell85 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 10, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

theorem cell85_check :
    cell85.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 86 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 10, 0, 0, 7]`; `cell86_check` verifies its
explicit-potential certificate. -/
def cell86 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 10, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell86_check :
    cell86.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 87 for the fixed row-04 divisor, with 25 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 29, 10, 0, 0, 24]`; `cell87_check` verifies
its explicit-potential certificate. -/
def cell87 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 29, 10, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 1, 1], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell87_check :
    cell87.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 88 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 8, 0, 0, 6]`; `cell88_check` verifies its
explicit-potential certificate. -/
def cell88 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 8, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell88_check :
    cell88.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 89 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 9, 0, 0, 6]`; `cell89_check` verifies its
explicit-potential certificate. -/
def cell89 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 9, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell89_check :
    cell89.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 90 for the fixed row-04 divisor, with 24 affine cone constraints. Anchors
zero through seven use witness indices `[0, 1, 0, 27, 10, 0, 0, 6]`; `cell90_check` verifies its
explicit-potential certificate. -/
def cell90 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 1, 0, 27, 10, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1]] }

theorem cell90_check :
    cell90.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 91 for the fixed row-04 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 21, 8, 0, 0, 22]`; `cell91_check` verifies its
explicit-potential certificate. -/
def cell91 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 21, 8, 0, 0, 22] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, -1, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1]] }

theorem cell91_check :
    cell91.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 92 for the fixed row-04 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 5, 8, 0, 0, 5]`; `cell92_check` verifies its
explicit-potential certificate. -/
def cell92 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 5, 8, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell92_check :
    cell92.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 93 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 26, 8, 0, 0, 5]`; `cell93_check` verifies its
explicit-potential certificate. -/
def cell93 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 26, 8, 0, 0, 5] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1]] }

theorem cell93_check :
    cell93.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 94 for the fixed row-04 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 25, 8, 0, 0, 6]`; `cell94_check` verifies its
explicit-potential certificate. -/
def cell94 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 25, 8, 0, 0, 6] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0]] }

theorem cell94_check :
    cell94.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 95 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 27, 8, 0, 0, 28]`; `cell95_check` verifies its
explicit-potential certificate. -/
def cell95 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 27, 8, 0, 0, 28] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 2, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0]] }

theorem cell95_check :
    cell95.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 96 for the fixed row-04 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 27, 8, 0, 0, 7]`; `cell96_check` verifies its
explicit-potential certificate. -/
def cell96 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 27, 8, 0, 0, 7] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, -1]] }

theorem cell96_check :
    cell96.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 97 for the fixed row-04 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 8, 0, 23, 8, 0, 0, 24]`; `cell97_check` verifies its
explicit-potential certificate. -/
def cell97 : CoordinateCell row04Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 8, 0, 23, 8, 0, 0, 24] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1]] }

theorem cell97_check :
    cell97.certificate.checkClosed 4 = true := by
  decide +kernel

/-- The ordered row-04 closed-cover cell block with global indices 0 through 97, used when
assembling the full 195-cell cover. -/
def chunk : List (CoordinateCell row04Core) := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15, cell16, cell17, cell18, cell19, cell20, cell21, cell22, cell23, cell24, cell25, cell26, cell27, cell28, cell29, cell30, cell31, cell32, cell33, cell34, cell35, cell36, cell37, cell38, cell39, cell40, cell41, cell42, cell43, cell44, cell45, cell46, cell47, cell48, cell49, cell50, cell51, cell52, cell53, cell54, cell55, cell56, cell57, cell58, cell59, cell60, cell61, cell62, cell63, cell64, cell65, cell66, cell67, cell68, cell69, cell70, cell71, cell72, cell73, cell74, cell75, cell76, cell77, cell78, cell79, cell80, cell81, cell82, cell83, cell84, cell85, cell86, cell87, cell88, cell89, cell90, cell91, cell92, cell93, cell94, cell95, cell96, cell97]

theorem chunk_check :
    chunk.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [chunk, cell0_check, cell1_check, cell2_check, cell3_check, cell4_check, cell5_check, cell6_check, cell7_check, cell8_check, cell9_check, cell10_check, cell11_check, cell12_check, cell13_check, cell14_check, cell15_check, cell16_check, cell17_check, cell18_check, cell19_check, cell20_check, cell21_check, cell22_check, cell23_check, cell24_check, cell25_check, cell26_check, cell27_check, cell28_check, cell29_check, cell30_check, cell31_check, cell32_check, cell33_check, cell34_check, cell35_check, cell36_check, cell37_check, cell38_check, cell39_check, cell40_check, cell41_check, cell42_check, cell43_check, cell44_check, cell45_check, cell46_check, cell47_check, cell48_check, cell49_check, cell50_check, cell51_check, cell52_check, cell53_check, cell54_check, cell55_check, cell56_check, cell57_check, cell58_check, cell59_check, cell60_check, cell61_check, cell62_check, cell63_check, cell64_check, cell65_check, cell66_check, cell67_check, cell68_check, cell69_check, cell70_check, cell71_check, cell72_check, cell73_check, cell74_check, cell75_check, cell76_check, cell77_check, cell78_check, cell79_check, cell80_check, cell81_check, cell82_check, cell83_check, cell84_check, cell85_check, cell86_check, cell87_check, cell88_check, cell89_check, cell90_check, cell91_check, cell92_check, cell93_check, cell94_check, cell95_check, cell96_check, cell97_check]

end AtanasovRanganathan.GenusFiveRow04CoverCells0
