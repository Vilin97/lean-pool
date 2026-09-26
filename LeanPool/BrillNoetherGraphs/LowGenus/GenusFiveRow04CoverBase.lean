/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveClosedCover
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas

/-! **Independent generated check.** This module provides an additional generated proof of row 04
and is not imported by the main `LowGenus` root.

Generated shared data for the chamber-restricted AR row-04 cover:
the fixed divisor and the pooled anchor witnesses.  Imported by every
cell chunk and by the assembling module. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow04CoverBase

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

/-- Decode an integer coefficient list as a twelve-variable affine form: the first entry is the
constant and missing entries are zero. -/
def aff (data : List ℤ) : ExplicitPotential.AffineForm 12 where
  fixedValue := data.getD 0 0
  coefficient := fun coordinate => data.getD (coordinate.val + 1) 0

/-- The fixed degree-four row-04 divisor, with one chip at each of vertices zero, two, five, and
six. -/
def rowDivisor : Fin 8 → ℤ := fun vertex =>
  ([1, 0, 1, 0, 0, 1, 1, 0] : List ℤ).getD vertex.val 0

/-- The zero endpoint slopes and zero core potential used for an out-of-range witness-table
lookup. -/
def defaultWitness : AnchorWitness 12 8 12 :=
  { alpha := fun _ => 0, beta := fun _ => 0, potential := fun _ => 0 }

/-- Endpoint-slope witness 0 for the row-04 closed cover: `alpha` is zero. `beta` is zero. The
affine potential is zero. -/
def witness0 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [],
      []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 1 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 11, and
zero elsewhere. `beta` is -1 at slots 5; 1 at slots 0, 11, and zero elsewhere. The nonzero
affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness1 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 2 for the row-04 closed cover: `alpha` is -1 at slots 5; 1 at slots
9, 11, and zero elsewhere. `beta` is -1 at slots 9, 10, 11, and zero elsewhere. The nonzero
affine potentials occur at vertices 2, 3, 6, 7. -/
def witness2 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, -1], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 3 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 2, 11,
and zero elsewhere. `beta` is -1 at slots 5; 1 at slots 0, 2, 11, and zero elsewhere. The
nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness3 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1, 0, -1], [0, -1, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 4 for the row-04 closed cover: `alpha` is -1 at slots 5; 1 at slots
8, 9, 11, and zero elsewhere. `beta` is -1 at slots 8, 9, 10, 11, and zero elsewhere. The
nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness4 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, -1], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 5 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7; 1 at
slots 9, 11, and zero elsewhere. `beta` is -1 at slots 9, 10, 11; 1 at slots 5, 6, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness5 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, 0, 1, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 1, 0, 0, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1], [0, 0, 0, 0, 0,
      0, -1, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 6 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7; 1 at
slots 9, 11, and zero elsewhere. `beta` is -1 at slots 8, 9, 10, 11; 1 at slots 5, 6, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness6 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, 0, 1, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 1, 0, -1, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 7 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7; 1 at
slots 8, 9, 11, and zero elsewhere. `beta` is -1 at slots 8, 9, 10, 11; 1 at slots 5, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness7 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, 1, 1, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 0, 0, -1, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0,
      -1, -1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 8 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 11; 1 at
slots 3, 5, and zero elsewhere. `beta` is -1 at slots 3, 4, 5; 1 at slots 0, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness8 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, -1, 0, 0, 1, 0, 1], [0, -1, 0, 0, 1, 0, 1],
      [0, -1], [0, -1, 0, 0, 1], [0, -1, 0, 0, 1, 0, 1], [0, -1, 0, 0, 1, 0,
      1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 9 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 2, 11; 1
at slots 3, 5, and zero elsewhere. `beta` is -1 at slots 3, 4, 5; 1 at slots 0, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness9 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 10 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 2, 11; 1
at slots 5, and zero elsewhere. `beta` is -1 at slots 3, 4, 5; 1 at slots 0, 2, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness10 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 1, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1, 0, -1], [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 11 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 11, and
zero elsewhere. `beta` is -1 at slots 5; 1 at slots 1, 11, and zero elsewhere. The nonzero
affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness11 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, -1], [0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 12 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 2, 11,
and zero elsewhere. `beta` is -1 at slots 5; 1 at slots 1, 2, 11, and zero elsewhere. The
nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness12 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, -1, -1], [0, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 13 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 11; 1 at
slots 3, 5, and zero elsewhere. `beta` is -1 at slots 2, 3, 4, 5; 1 at slots 0, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness13 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 14 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 11; 1 at
slots 3, 5, and zero elsewhere. `beta` is -1 at slots 3, 4, 5; 1 at slots 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness14 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, -1,
      0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 15 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 11; 1 at
slots 2, 3, 5, and zero elsewhere. `beta` is -1 at slots 2, 3, 4, 5; 1 at slots 0, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness15 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, -1, 0, 1, 1, 0, 1], [0, -1, 0, 1, 1, 0, 1],
      [0, -1, 0, 1], [0, -1, 0, 1, 1], [0, -1, 0, 1, 1, 0, 1], [0, -1, 0, 1, 1, 0,
      1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 16 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 2, 11; 1
at slots 3, 5, and zero elsewhere. `beta` is -1 at slots 3, 4, 5; 1 at slots 0, 1, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness16 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 1, 0, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 17 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 11; 1 at
slots 5, and zero elsewhere. `beta` is -1 at slots 3, 4, 5; 1 at slots 0, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness17 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1], [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 18 for the row-04 closed cover: `alpha` is -2 at slots 2; -1 at slots
0, 1, 11; 1 at slots 3, 5, and zero elsewhere. `beta` is -1 at slots 3, 4, 5; 1 at slots 0, 1,
11, and zero elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness18 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, -2, 1, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 1, 0, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0,
      0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 19 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 11; 1 at
slots 2, 3, 5, and zero elsewhere. `beta` is -1 at slots 2, 3, 4, 5; 1 at slots 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness19 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 1, 1, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, -1,
      0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 20 for the row-04 closed cover: `alpha` is -1 at slots 0, 1, 11; 1 at
slots 3, 5, and zero elsewhere. `beta` is -1 at slots 2, 3, 4, 5; 1 at slots 1, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 1, 2, 3, 4, 5, 6, 7. -/
def witness20 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0,
      0, 0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 21 for the row-04 closed cover: `alpha` is -1 at slots 5; 1 at slots
10, 11, and zero elsewhere. `beta` is -1 at slots 9, 10, 11, and zero elsewhere. The nonzero
affine potentials occur at vertices 2, 3, 6, 7. -/
def witness21 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 22 for the row-04 closed cover: `alpha` is -1 at slots 5; 1 at slots
8, 10, 11, and zero elsewhere. `beta` is -1 at slots 8, 9, 10, 11, and zero elsewhere. The
nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness22 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 1, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1], [0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, -1, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 23 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7, 8; 1
at slots 9, 11, and zero elsewhere. `beta` is -1 at slots 9, 10, 11; 1 at slots 5, 6, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness23 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, -1, 1, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 1, 0, 0, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 24 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7; 1 at
slots 11, and zero elsewhere. `beta` is -1 at slots 9, 10, 11; 1 at slots 5, 6, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness24 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 1, 0, 0, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, -1, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 25 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7; 1 at
slots 9, 10, 11, and zero elsewhere. `beta` is -1 at slots 8, 9, 10, 11; 1 at slots 5, 6, and
zero elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness25 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, 0, 1, 1, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 1, 0, -1, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 26 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7, 8; 1
at slots 9, 11, and zero elsewhere. `beta` is -1 at slots 9, 10, 11; 1 at slots 5, 6, 8, and
zero elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness26 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, -1, 1, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 1, 0, 1, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 1], [0, 0, 0, 0, 0,
      0, -1, -1, 0, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 27 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7; 1 at
slots 9, 11, and zero elsewhere. `beta` is -1 at slots 9, 10, 11; 1 at slots 5, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness27 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, 0, 1, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 0, 0, 0, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, -1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 28 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7; 1 at
slots 9, 10, 11, and zero elsewhere. `beta` is -2 at slots 8; -1 at slots 9, 10, 11; 1 at slots
5, 6, and zero elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness28 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, 0, 1, 1, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 1, 0, -2, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, -1, 0, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 29 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7, 8; 1
at slots 11, and zero elsewhere. `beta` is -1 at slots 9, 10, 11; 1 at slots 5, 6, 8, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness29 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 1, 0, 1, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, -1, -1, 0, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 30 for the row-04 closed cover: `alpha` is -1 at slots 5, 6, 7, 8; 1
at slots 10, 11, and zero elsewhere. `beta` is -1 at slots 9, 10, 11; 1 at slots 5, 6, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 3, 6, 7. -/
def witness30 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, -1, 0, 1, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 1, 1, 0, 0, -1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, -1, -1], [], [], [0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1,
      -1]] : List (List ℤ)).getD vertex.val []) }

/-- The thirty-one endpoint-slope and affine-potential witnesses shared by the row-04
closed-cover cells. -/
def witnesses : List (AnchorWitness 12 8 12) :=
  [witness0, witness1, witness2, witness3, witness4, witness5, witness6, witness7, witness8,
  witness9, witness10, witness11, witness12, witness13, witness14, witness15, witness16, witness17,
  witness18, witness19, witness20, witness21, witness22, witness23, witness24, witness25, witness26,
  witness27, witness28, witness29, witness30]

end AtanasovRanganathan.GenusFiveRow04CoverBase
