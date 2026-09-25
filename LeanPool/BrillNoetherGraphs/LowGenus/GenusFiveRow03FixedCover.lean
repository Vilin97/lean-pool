/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveClosedCover
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas

/-! **Independent generated check.** The main row-03 proof is now
`GenusFiveTwoPoleClosed.row03_closedConstruction`; this module preserves
an additional exact replay.

Generated exact replay of the fixed AR row-03 divisor.
`cells_check` and `tree_check` replay every arithmetic obligation in the kernel. -/

@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

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

/-- The fixed degree-four row-03 divisor, with one chip at each of vertices zero, one, four, and
five. -/
def rowDivisor : Fin 8 → ℤ := fun vertex =>
  ([1, 1, 0, 0, 1, 1, 0, 0] : List ℤ).getD vertex.val 0

/-- The zero endpoint slopes and zero core potential used for an out-of-range witness-table
lookup. -/
def defaultWitness : AnchorWitness 12 8 12 :=
  { alpha := fun _ => 0, beta := fun _ => 0, potential := fun _ => 0 }

/-- Endpoint-slope witness 0 for the row-03 closed cover: `alpha` is zero. `beta` is zero. The
affine potential is zero. -/
def witness0 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 1 for the row-03 closed cover: `alpha` is 1 at slots 5, 6, 8, and
zero elsewhere. `beta` is -1 at slots 5, 6, 7, 8, and zero elsewhere. The nonzero affine
potentials occur at vertices 4, 5, 6, 7. -/
def witness1 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 2 for the row-03 closed cover: `alpha` is 1 at slots 6, 7, 8, and
zero elsewhere. `beta` is -1 at slots 5, 6, 7, 8, and zero elsewhere. The nonzero affine
potentials occur at vertices 4, 5, 6, 7. -/
def witness2 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 3 for the row-03 closed cover: `alpha` is 1 at slots 6, and zero
elsewhere. `beta` is -1 at slots 6, 8, and zero elsewhere. The nonzero affine potentials occur
at vertices 4, 5. -/
def witness3 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 4 for the row-03 closed cover: `alpha` is 1 at slots 8, and zero
elsewhere. `beta` is -1 at slots 6, 8, and zero elsewhere. The nonzero affine potentials occur
at vertices 4, 5. -/
def witness4 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 5 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
5, 8, 11, and zero elsewhere. `beta` is -1 at slots 1, 5, 6, 8, 11, and zero elsewhere. The
nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness5 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 6 for the row-03 closed cover: `alpha` is -1 at slots 2; 1 at slots
7, 8, and zero elsewhere. `beta` is -1 at slots 3, 6, 7, 8, and zero elsewhere. The nonzero
affine potentials occur at vertices 3, 4, 5. -/
def witness6 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, -1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 7 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
8, 11, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11, and zero elsewhere. The nonzero
affine potentials occur at vertices 2, 4, 5, 6. -/
def witness7 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 8 for the row-03 closed cover: `alpha` is -1 at slots 2; 1 at slots
3, 8, and zero elsewhere. `beta` is -1 at slots 3, 6, 7, 8, and zero elsewhere. The nonzero
affine potentials occur at vertices 3, 4, 5. -/
def witness8 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, -1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 9 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
1, 8, 11, and zero elsewhere. `beta` is -1 at slots 1, 5, 6, 8, 11, and zero elsewhere. The
nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness9 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 10 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
1, 8, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11, and zero elsewhere. The nonzero
affine potentials occur at vertices 2, 4, 5, 6. -/
def witness10 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 11 for the row-03 closed cover: `alpha` is -1 at slots 0, 5; 1 at
slots 1, 8, 11, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11, and zero elsewhere. The
nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness11 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, 0, 0, 0, -1, 0, 0, 1, 0, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 12 for the row-03 closed cover: `alpha` is -1 at slots 0, 5; 1 at
slots 1, 8, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11; 1 at slots 5, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness12 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, 1, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, -1, 0, 0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 13 for the row-03 closed cover: `alpha` is -1 at slots 2; 1 at slots
8, and zero elsewhere. `beta` is -1 at slots 3, 6, 7, 8; 1 at slots 2, and zero elsewhere. The
nonzero affine potentials occur at vertices 3, 4, 5. -/
def witness13 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, -1, -1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 14 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
1, 6, 8, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11, and zero elsewhere. The nonzero
affine potentials occur at vertices 2, 4, 5, 6. -/
def witness14 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 15 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
8, 11, and zero elsewhere. `beta` is -1 at slots 1, 5, 6, 8, 11; 1 at slots 0, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness15 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 16 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
1, 8, 11, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11, and zero elsewhere. The nonzero
affine potentials occur at vertices 2, 4, 5, 6. -/
def witness16 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 17 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
8, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11; 1 at slots 0, and zero elsewhere. The
nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness17 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 18 for the row-03 closed cover: `alpha` is -1 at slots 0, 5; 1 at
slots 8, 11, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11; 1 at slots 0, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness18 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 19 for the row-03 closed cover: `alpha` is -1 at slots 0, 5; 1 at
slots 8, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11; 1 at slots 0, 5, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness19 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, 1, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1, 0, 0, 0, 0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 20 for the row-03 closed cover: `alpha` is 1 at slots 5, 6, 7, 8, and
zero elsewhere. `beta` is -1 at slots 5, 6, 7, 8, and zero elsewhere. The nonzero affine
potentials occur at vertices 4, 5, 6, 7. -/
def witness20 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 21 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
6, 8, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11, and zero elsewhere. The nonzero
affine potentials occur at vertices 2, 4, 5, 6. -/
def witness21 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, 0, -1, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1, 0, 1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 22 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
1, 6, 8, and zero elsewhere. `beta` is -1 at slots 1, 5, 6, 8, 11, and zero elsewhere. The
nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness22 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1, 0, 1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 23 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
5, 6, 8, and zero elsewhere. `beta` is -1 at slots 1, 5, 6, 8, 11, and zero elsewhere. The
nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness23 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, -1, -1, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1, 0, 1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 24 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
6, 8, and zero elsewhere. `beta` is -1 at slots 1, 5, 6, 8, 11; 1 at slots 0, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness24 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1, 0, 1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 25 for the row-03 closed cover: `alpha` is -1 at slots 0, 5; 1 at
slots 6, 8, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11; 1 at slots 0, and zero
elsewhere. The nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness25 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, -1, 1, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1, 0, 1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 26 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
8, 11, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11; 1 at slots 0, and zero elsewhere.
The nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness26 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 27 for the row-03 closed cover: `alpha` is -1 at slots 0, 5; 1 at
slots 1, 6, 8, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11, and zero elsewhere. The
nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness27 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, 0, 0, 0, -1, 1, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1, 0, 1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 28 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
6, 8, and zero elsewhere. `beta` is -1 at slots 1, 6, 8, 11; 1 at slots 0, and zero elsewhere.
The nonzero affine potentials occur at vertices 2, 4, 5, 6. -/
def witness28 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, -1], [], [0, -1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, -1], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 29 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
5, 6, and zero elsewhere. `beta` is -1 at slots 1, 5, 6, 8, and zero elsewhere. The nonzero
affine potentials occur at vertices 2, 4, 5. -/
def witness29 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 30 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
6, and zero elsewhere. `beta` is -1 at slots 1, 5, 6, 8; 1 at slots 0, and zero elsewhere. The
nonzero affine potentials occur at vertices 2, 4, 5. -/
def witness30 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, -1], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 31 for the row-03 closed cover: `alpha` is -1 at slots 0; 1 at slots
1, 6, and zero elsewhere. `beta` is -1 at slots 1, 5, 6, 8, and zero elsewhere. The nonzero
affine potentials occur at vertices 2, 4, 5. -/
def witness31 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, -1], [], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], []] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 32 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 6, 7, and zero elsewhere. `beta` is -1 at slots 3, 6, 7, 8; 1 at slots 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness32 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, 1, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, -1, -1, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 33 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 8; 1 at slots 11, and zero elsewhere.
The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness33 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 34 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 3, 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 7, 8; 1 at slots 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness34 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, -1, -1, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 35 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 3, 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 8, and zero elsewhere. The nonzero
affine potentials occur at vertices 3, 4, 5, 7. -/
def witness35 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 36 for the row-03 closed cover: `alpha` is -1 at slots 2, 7, 11; 1 at
slots 3, 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 8; 1 at slots 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness36 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 1, -1, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 37 for the row-03 closed cover: `alpha` is -1 at slots 2, 7, 11; 1 at
slots 3, 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 8; 1 at slots 7, and zero elsewhere.
The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness37 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 1, -1, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, 1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, -1, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 38 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 7, 8; 1 at slots 2, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness38 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, -1, -1, -1, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 39 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 8; 1 at slots 2, and zero elsewhere.
The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness39 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, -1, 0, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 40 for the row-03 closed cover: `alpha` is -1 at slots 2, 7, 11; 1 at
slots 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 8; 1 at slots 2, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness40 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, -1, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, -1, 0, -1, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 41 for the row-03 closed cover: `alpha` is -1 at slots 2, 7, 11; 1 at
slots 3, 6, 8, and zero elsewhere. `beta` is -1 at slots 3, 6, 8, and zero elsewhere. The
nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness41 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 1, -1, 1, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 42 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 3, 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 8; 1 at slots 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness42 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 1, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 43 for the row-03 closed cover: `alpha` is -1 at slots 2, 7, 11; 1 at
slots 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 8; 1 at slots 2, 7, and zero elsewhere.
The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness43 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, -1, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, -1, 1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, -1, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 44 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 6, 7, 8, and zero elsewhere. `beta` is -1 at slots 3, 6, 7, 8, and zero elsewhere. The
nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness44 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, 1, 1, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, -1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, 0, 0, 0, 1, -1, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 45 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 6, 8, and zero elsewhere. `beta` is -1 at slots 3, 6, 8, and zero elsewhere. The nonzero
affine potentials occur at vertices 3, 4, 5, 7. -/
def witness45 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, 0, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 46 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 3, 6, 8, and zero elsewhere. `beta` is -1 at slots 3, 6, 7, 8, and zero elsewhere. The
nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness46 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 1, 0, 1, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, -1, -1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 47 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 6, 8, and zero elsewhere. `beta` is -1 at slots 3, 6, 7, 8; 1 at slots 2, and zero
elsewhere. The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness47 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, -1, -1, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 48 for the row-03 closed cover: `alpha` is -1 at slots 2, 7, 11; 1 at
slots 6, 8, and zero elsewhere. `beta` is -1 at slots 3, 6, 8; 1 at slots 2, and zero elsewhere.
The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness48 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, -1, 1, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, -1, 0, -1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, 0, 0, 0, 0, 1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- Endpoint-slope witness 49 for the row-03 closed cover: `alpha` is -1 at slots 2, 11; 1 at
slots 6, and zero elsewhere. `beta` is -1 at slots 3, 6, 8; 1 at slots 2, 11, and zero
elsewhere. The nonzero affine potentials occur at vertices 3, 4, 5, 7. -/
def witness49 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, -1, 0, -1, 0, 0, 1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [], [0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

/-- The fifty endpoint-slope and affine-potential witnesses shared by the row-03 closed-cover
cells. -/
def witnesses : List (AnchorWitness 12 8 12) := [witness0, witness1, witness2, witness3, witness4, witness5, witness6, witness7, witness8, witness9, witness10, witness11, witness12, witness13, witness14, witness15, witness16, witness17, witness18, witness19, witness20, witness21, witness22, witness23, witness24, witness25, witness26, witness27, witness28, witness29, witness30, witness31, witness32, witness33, witness34, witness35, witness36, witness37, witness38, witness39, witness40, witness41, witness42, witness43, witness44, witness45, witness46, witness47, witness48, witness49]

/-- Closed-cover cell 0 for the fixed row-03 divisor, with 16 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 1, 2, 0, 0, 3, 4]`; `cell0_check` verifies its
explicit-potential certificate. -/
def cell0 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 1, 2, 0, 0, 3, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]] }

theorem cell0_check :
    cell0.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 1 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 5, 6, 0, 0, 7, 4]`; `cell1_check` verifies its
explicit-potential certificate. -/
def cell1 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 5, 6, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell1_check :
    cell1.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 2 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 5, 8, 0, 0, 7, 4]`; `cell2_check` verifies its
explicit-potential certificate. -/
def cell2 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 5, 8, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell2_check :
    cell2.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 3 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 9, 6, 0, 0, 7, 4]`; `cell3_check` verifies its
explicit-potential certificate. -/
def cell3 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 9, 6, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell3_check :
    cell3.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 4 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 9, 8, 0, 0, 7, 4]`; `cell4_check` verifies its
explicit-potential certificate. -/
def cell4 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 9, 8, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell4_check :
    cell4.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 5 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 6, 0, 0, 11, 4]`; `cell5_check` verifies its
explicit-potential certificate. -/
def cell5 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 6, 0, 0, 11, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell5_check :
    cell5.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 6 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 8, 0, 0, 11, 4]`; `cell6_check` verifies its
explicit-potential certificate. -/
def cell6 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 8, 0, 0, 11, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell6_check :
    cell6.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 7 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 6, 0, 0, 12, 4]`; `cell7_check` verifies its
explicit-potential certificate. -/
def cell7 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 6, 0, 0, 12, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1]] }

theorem cell7_check :
    cell7.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 8 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 8, 0, 0, 12, 4]`; `cell8_check` verifies its
explicit-potential certificate. -/
def cell8 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 8, 0, 0, 12, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1]] }

theorem cell8_check :
    cell8.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 9 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 5, 13, 0, 0, 7, 4]`; `cell9_check` verifies its
explicit-potential certificate. -/
def cell9 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 5, 13, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell9_check :
    cell9.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 10 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 9, 13, 0, 0, 7, 4]`; `cell10_check` verifies its
explicit-potential certificate. -/
def cell10 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 9, 13, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell10_check :
    cell10.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 11 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 13, 0, 0, 14, 4]`; `cell11_check` verifies
its explicit-potential certificate. -/
def cell11 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 13, 0, 0, 14, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell11_check :
    cell11.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 12 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 13, 0, 0, 11, 4]`; `cell12_check` verifies
its explicit-potential certificate. -/
def cell12 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 13, 0, 0, 11, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell12_check :
    cell12.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 13 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 13, 0, 0, 12, 4]`; `cell13_check` verifies
its explicit-potential certificate. -/
def cell13 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 13, 0, 0, 12, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1]] }

theorem cell13_check :
    cell13.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 14 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 15, 6, 0, 0, 7, 4]`; `cell14_check` verifies its
explicit-potential certificate. -/
def cell14 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 15, 6, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell14_check :
    cell14.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 15 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 15, 8, 0, 0, 7, 4]`; `cell15_check` verifies its
explicit-potential certificate. -/
def cell15 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 15, 8, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell15_check :
    cell15.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 16 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 6, 0, 0, 7, 4]`; `cell16_check` verifies its
explicit-potential certificate. -/
def cell16 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 6, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell16_check :
    cell16.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 17 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 8, 0, 0, 7, 4]`; `cell17_check` verifies its
explicit-potential certificate. -/
def cell17 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 8, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell17_check :
    cell17.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 18 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 15, 13, 0, 0, 7, 4]`; `cell18_check` verifies its
explicit-potential certificate. -/
def cell18 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 15, 13, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell18_check :
    cell18.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 19 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 13, 0, 0, 7, 4]`; `cell19_check` verifies its
explicit-potential certificate. -/
def cell19 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 13, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell19_check :
    cell19.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 20 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 16, 13, 0, 0, 7, 4]`; `cell20_check` verifies its
explicit-potential certificate. -/
def cell20 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 16, 13, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell20_check :
    cell20.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 21 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 6, 0, 0, 18, 4]`; `cell21_check` verifies its
explicit-potential certificate. -/
def cell21 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 6, 0, 0, 18, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell21_check :
    cell21.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 22 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 13, 0, 0, 18, 4]`; `cell22_check` verifies
its explicit-potential certificate. -/
def cell22 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 13, 0, 0, 18, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell22_check :
    cell22.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 23 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 6, 0, 0, 16, 4]`; `cell23_check` verifies its
explicit-potential certificate. -/
def cell23 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 6, 0, 0, 16, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell23_check :
    cell23.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 24 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 6, 0, 0, 14, 4]`; `cell24_check` verifies its
explicit-potential certificate. -/
def cell24 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 6, 0, 0, 14, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell24_check :
    cell24.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 25 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 8, 0, 0, 18, 4]`; `cell25_check` verifies its
explicit-potential certificate. -/
def cell25 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 8, 0, 0, 18, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell25_check :
    cell25.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 26 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 8, 0, 0, 16, 4]`; `cell26_check` verifies its
explicit-potential certificate. -/
def cell26 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 8, 0, 0, 16, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell26_check :
    cell26.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 27 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 8, 0, 0, 14, 4]`; `cell27_check` verifies its
explicit-potential certificate. -/
def cell27 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 8, 0, 0, 14, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell27_check :
    cell27.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 28 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 6, 0, 0, 19, 4]`; `cell28_check` verifies its
explicit-potential certificate. -/
def cell28 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 6, 0, 0, 19, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1]] }

theorem cell28_check :
    cell28.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 29 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 8, 0, 0, 19, 4]`; `cell29_check` verifies its
explicit-potential certificate. -/
def cell29 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 8, 0, 0, 19, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1]] }

theorem cell29_check :
    cell29.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 30 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 13, 0, 0, 19, 4]`; `cell30_check` verifies
its explicit-potential certificate. -/
def cell30 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 13, 0, 0, 19, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1]] }

theorem cell30_check :
    cell30.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 31 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 20, 6, 0, 0, 21, 4]`; `cell31_check` verifies its
explicit-potential certificate. -/
def cell31 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 20, 6, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1]] }

theorem cell31_check :
    cell31.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 32 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 22, 6, 0, 0, 21, 4]`; `cell32_check` verifies its
explicit-potential certificate. -/
def cell32 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 22, 6, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell32_check :
    cell32.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 33 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 23, 6, 0, 0, 21, 4]`; `cell33_check` verifies its
explicit-potential certificate. -/
def cell33 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 23, 6, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell33_check :
    cell33.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 34 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 24, 6, 0, 0, 21, 4]`; `cell34_check` verifies its
explicit-potential certificate. -/
def cell34 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 24, 6, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell34_check :
    cell34.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 35 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 20, 8, 0, 0, 21, 4]`; `cell35_check` verifies its
explicit-potential certificate. -/
def cell35 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 20, 8, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1]] }

theorem cell35_check :
    cell35.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 36 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 22, 8, 0, 0, 21, 4]`; `cell36_check` verifies its
explicit-potential certificate. -/
def cell36 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 22, 8, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell36_check :
    cell36.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 37 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 23, 8, 0, 0, 21, 4]`; `cell37_check` verifies its
explicit-potential certificate. -/
def cell37 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 23, 8, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell37_check :
    cell37.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 38 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 24, 8, 0, 0, 21, 4]`; `cell38_check` verifies its
explicit-potential certificate. -/
def cell38 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 24, 8, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell38_check :
    cell38.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 39 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 6, 0, 0, 25, 4]`; `cell39_check` verifies its
explicit-potential certificate. -/
def cell39 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 6, 0, 0, 25, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1]] }

theorem cell39_check :
    cell39.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 40 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 8, 0, 0, 26, 4]`; `cell40_check` verifies its
explicit-potential certificate. -/
def cell40 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 8, 0, 0, 26, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell40_check :
    cell40.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 41 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 8, 0, 0, 25, 4]`; `cell41_check` verifies its
explicit-potential certificate. -/
def cell41 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 8, 0, 0, 25, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1]] }

theorem cell41_check :
    cell41.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 42 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 6, 0, 0, 27, 4]`; `cell42_check` verifies its
explicit-potential certificate. -/
def cell42 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 6, 0, 0, 27, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1]] }

theorem cell42_check :
    cell42.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 43 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 8, 0, 0, 27, 4]`; `cell43_check` verifies its
explicit-potential certificate. -/
def cell43 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 8, 0, 0, 27, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1]] }

theorem cell43_check :
    cell43.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 44 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 6, 0, 0, 26, 4]`; `cell44_check` verifies its
explicit-potential certificate. -/
def cell44 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 6, 0, 0, 26, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell44_check :
    cell44.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 45 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 6, 0, 0, 28, 4]`; `cell45_check` verifies its
explicit-potential certificate. -/
def cell45 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 6, 0, 0, 28, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell45_check :
    cell45.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 46 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 8, 0, 0, 28, 4]`; `cell46_check` verifies its
explicit-potential certificate. -/
def cell46 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 8, 0, 0, 28, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell46_check :
    cell46.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 47 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 20, 13, 0, 0, 21, 4]`; `cell47_check` verifies
its explicit-potential certificate. -/
def cell47 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 20, 13, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1]] }

theorem cell47_check :
    cell47.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 48 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 22, 13, 0, 0, 21, 4]`; `cell48_check` verifies
its explicit-potential certificate. -/
def cell48 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 22, 13, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell48_check :
    cell48.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 49 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 23, 13, 0, 0, 21, 4]`; `cell49_check` verifies
its explicit-potential certificate. -/
def cell49 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 23, 13, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell49_check :
    cell49.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 50 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 24, 13, 0, 0, 21, 4]`; `cell50_check` verifies
its explicit-potential certificate. -/
def cell50 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 24, 13, 0, 0, 21, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell50_check :
    cell50.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 51 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 13, 0, 0, 26, 4]`; `cell51_check` verifies
its explicit-potential certificate. -/
def cell51 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 13, 0, 0, 26, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell51_check :
    cell51.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 52 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 13, 0, 0, 25, 4]`; `cell52_check` verifies
its explicit-potential certificate. -/
def cell52 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 13, 0, 0, 25, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1]] }

theorem cell52_check :
    cell52.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 53 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 13, 0, 0, 27, 4]`; `cell53_check` verifies
its explicit-potential certificate. -/
def cell53 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 13, 0, 0, 27, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1]] }

theorem cell53_check :
    cell53.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 54 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 17, 13, 0, 0, 28, 4]`; `cell54_check` verifies
its explicit-potential certificate. -/
def cell54 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 17, 13, 0, 0, 28, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]] }

theorem cell54_check :
    cell54.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 55 for the fixed row-03 divisor, with 17 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 1, 6, 0, 0, 3, 4]`; `cell55_check` verifies its
explicit-potential certificate. -/
def cell55 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 1, 6, 0, 0, 3, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]] }

theorem cell55_check :
    cell55.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 56 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 16, 6, 0, 0, 7, 4]`; `cell56_check` verifies its
explicit-potential certificate. -/
def cell56 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 16, 6, 0, 0, 7, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell56_check :
    cell56.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 57 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 16, 6, 0, 0, 16, 4]`; `cell57_check` verifies its
explicit-potential certificate. -/
def cell57 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 16, 6, 0, 0, 16, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell57_check :
    cell57.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 58 for the fixed row-03 divisor, with 17 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 1, 8, 0, 0, 3, 4]`; `cell58_check` verifies its
explicit-potential certificate. -/
def cell58 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 1, 8, 0, 0, 3, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell58_check :
    cell58.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 59 for the fixed row-03 divisor, with 17 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 1, 13, 0, 0, 3, 4]`; `cell59_check` verifies its
explicit-potential certificate. -/
def cell59 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 1, 13, 0, 0, 3, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell59_check :
    cell59.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 60 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 22, 13, 0, 0, 11, 4]`; `cell60_check` verifies
its explicit-potential certificate. -/
def cell60 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 22, 13, 0, 0, 11, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]] }

theorem cell60_check :
    cell60.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 61 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 5, 2, 0, 0, 3, 4]`; `cell61_check` verifies its
explicit-potential certificate. -/
def cell61 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 5, 2, 0, 0, 3, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell61_check :
    cell61.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 62 for the fixed row-03 divisor, with 17 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 2, 0, 0, 3, 4]`; `cell62_check` verifies its
explicit-potential certificate. -/
def cell62 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 2, 0, 0, 3, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell62_check :
    cell62.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 63 for the fixed row-03 divisor, with 17 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 2, 0, 0, 3, 4]`; `cell63_check` verifies its
explicit-potential certificate. -/
def cell63 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 2, 0, 0, 3, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell63_check :
    cell63.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 64 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 9, 2, 0, 0, 3, 4]`; `cell64_check` verifies its
explicit-potential certificate. -/
def cell64 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 9, 2, 0, 0, 3, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell64_check :
    cell64.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 65 for the fixed row-03 divisor, with 19 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 10, 2, 0, 0, 3, 4]`; `cell65_check` verifies its
explicit-potential certificate. -/
def cell65 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 10, 2, 0, 0, 3, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell65_check :
    cell65.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 66 for the fixed row-03 divisor, with 17 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 2, 0, 0, 3, 4]`; `cell66_check` verifies its
explicit-potential certificate. -/
def cell66 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 2, 0, 0, 3, 4] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell66_check :
    cell66.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 67 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 32, 0, 0, 3, 33]`; `cell67_check` verifies
its explicit-potential certificate. -/
def cell67 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 32, 0, 0, 3, 33] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell67_check :
    cell67.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 68 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 32, 0, 0, 3, 33]`; `cell68_check` verifies
its explicit-potential certificate. -/
def cell68 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 32, 0, 0, 3, 33] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell68_check :
    cell68.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 69 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 34, 0, 0, 3, 33]`; `cell69_check` verifies
its explicit-potential certificate. -/
def cell69 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 34, 0, 0, 3, 33] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell69_check :
    cell69.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 70 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 35, 0, 0, 3, 36]`; `cell70_check` verifies
its explicit-potential certificate. -/
def cell70 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 35, 0, 0, 3, 36] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]] }

theorem cell70_check :
    cell70.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 71 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 35, 0, 0, 3, 37]`; `cell71_check` verifies
its explicit-potential certificate. -/
def cell71 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 35, 0, 0, 3, 37] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell71_check :
    cell71.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 72 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 34, 0, 0, 3, 33]`; `cell72_check` verifies
its explicit-potential certificate. -/
def cell72 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 34, 0, 0, 3, 33] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell72_check :
    cell72.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 73 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 35, 0, 0, 3, 36]`; `cell73_check` verifies
its explicit-potential certificate. -/
def cell73 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 35, 0, 0, 3, 36] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]] }

theorem cell73_check :
    cell73.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 74 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 35, 0, 0, 3, 37]`; `cell74_check` verifies
its explicit-potential certificate. -/
def cell74 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 35, 0, 0, 3, 37] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell74_check :
    cell74.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 75 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 38, 0, 0, 3, 33]`; `cell75_check` verifies
its explicit-potential certificate. -/
def cell75 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 38, 0, 0, 3, 33] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell75_check :
    cell75.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 76 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 38, 0, 0, 3, 33]`; `cell76_check` verifies
its explicit-potential certificate. -/
def cell76 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 38, 0, 0, 3, 33] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell76_check :
    cell76.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 77 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 39, 0, 0, 3, 40]`; `cell77_check` verifies
its explicit-potential certificate. -/
def cell77 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 39, 0, 0, 3, 40] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]] }

theorem cell77_check :
    cell77.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 78 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 35, 0, 0, 3, 41]`; `cell78_check` verifies
its explicit-potential certificate. -/
def cell78 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 35, 0, 0, 3, 41] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 1, 1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1]] }

theorem cell78_check :
    cell78.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 79 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 35, 0, 0, 3, 42]`; `cell79_check` verifies
its explicit-potential certificate. -/
def cell79 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 35, 0, 0, 3, 42] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell79_check :
    cell79.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 80 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 39, 0, 0, 3, 43]`; `cell80_check` verifies
its explicit-potential certificate. -/
def cell80 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 39, 0, 0, 3, 43] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, -1, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell80_check :
    cell80.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 81 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 39, 0, 0, 3, 40]`; `cell81_check` verifies
its explicit-potential certificate. -/
def cell81 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 39, 0, 0, 3, 40] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]] }

theorem cell81_check :
    cell81.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 82 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 35, 0, 0, 3, 42]`; `cell82_check` verifies
its explicit-potential certificate. -/
def cell82 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 35, 0, 0, 3, 42] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell82_check :
    cell82.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 83 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 39, 0, 0, 3, 43]`; `cell83_check` verifies
its explicit-potential certificate. -/
def cell83 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 39, 0, 0, 3, 43] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, -1, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell83_check :
    cell83.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 84 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 32, 0, 0, 3, 33]`; `cell84_check` verifies
its explicit-potential certificate. -/
def cell84 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 32, 0, 0, 3, 33] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell84_check :
    cell84.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 85 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 34, 0, 0, 3, 33]`; `cell85_check` verifies
its explicit-potential certificate. -/
def cell85 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 34, 0, 0, 3, 33] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell85_check :
    cell85.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 86 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 35, 0, 0, 3, 36]`; `cell86_check` verifies
its explicit-potential certificate. -/
def cell86 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 35, 0, 0, 3, 36] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]] }

theorem cell86_check :
    cell86.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 87 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 35, 0, 0, 3, 37]`; `cell87_check` verifies
its explicit-potential certificate. -/
def cell87 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 35, 0, 0, 3, 37] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell87_check :
    cell87.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 88 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 38, 0, 0, 3, 33]`; `cell88_check` verifies
its explicit-potential certificate. -/
def cell88 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 38, 0, 0, 3, 33] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell88_check :
    cell88.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 89 for the fixed row-03 divisor, with 22 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 39, 0, 0, 3, 40]`; `cell89_check` verifies
its explicit-potential certificate. -/
def cell89 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 39, 0, 0, 3, 40] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]] }

theorem cell89_check :
    cell89.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 90 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 35, 0, 0, 3, 42]`; `cell90_check` verifies
its explicit-potential certificate. -/
def cell90 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 35, 0, 0, 3, 42] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell90_check :
    cell90.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 91 for the fixed row-03 divisor, with 23 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 39, 0, 0, 3, 43]`; `cell91_check` verifies
its explicit-potential certificate. -/
def cell91 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 39, 0, 0, 3, 43] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, -1, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]] }

theorem cell91_check :
    cell91.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 92 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 44, 0, 0, 3, 45]`; `cell92_check` verifies
its explicit-potential certificate. -/
def cell92 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 44, 0, 0, 3, 45] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell92_check :
    cell92.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 93 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 44, 0, 0, 3, 45]`; `cell93_check` verifies
its explicit-potential certificate. -/
def cell93 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 44, 0, 0, 3, 45] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell93_check :
    cell93.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 94 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 46, 0, 0, 3, 45]`; `cell94_check` verifies
its explicit-potential certificate. -/
def cell94 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 46, 0, 0, 3, 45] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell94_check :
    cell94.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 95 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 46, 0, 0, 3, 45]`; `cell95_check` verifies
its explicit-potential certificate. -/
def cell95 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 46, 0, 0, 3, 45] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell95_check :
    cell95.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 96 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 35, 0, 0, 3, 41]`; `cell96_check` verifies
its explicit-potential certificate. -/
def cell96 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 35, 0, 0, 3, 41] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 1, 1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1]] }

theorem cell96_check :
    cell96.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 97 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 47, 0, 0, 3, 45]`; `cell97_check` verifies
its explicit-potential certificate. -/
def cell97 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 47, 0, 0, 3, 45] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell97_check :
    cell97.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 98 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 47, 0, 0, 3, 45]`; `cell98_check` verifies
its explicit-potential certificate. -/
def cell98 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 47, 0, 0, 3, 45] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell98_check :
    cell98.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 99 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 29, 39, 0, 0, 3, 48]`; `cell99_check` verifies
its explicit-potential certificate. -/
def cell99 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 29, 39, 0, 0, 3, 48] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1]] }

theorem cell99_check :
    cell99.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 100 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 31, 39, 0, 0, 3, 48]`; `cell100_check` verifies
its explicit-potential certificate. -/
def cell100 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 39, 0, 0, 3, 48] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1]] }

theorem cell100_check :
    cell100.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 101 for the fixed row-03 divisor, with 21 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 44, 0, 0, 3, 45]`; `cell101_check` verifies
its explicit-potential certificate. -/
def cell101 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 44, 0, 0, 3, 45] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell101_check :
    cell101.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Closed-cover cell 102 for the fixed row-03 divisor, with 20 affine cone constraints. Anchors
zero through seven use witness indices `[0, 0, 30, 47, 0, 0, 3, 45]`; `cell102_check` verifies
its explicit-potential certificate. -/
def cell102 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 47, 0, 0, 3, 45] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell102_check :
    cell102.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Cone 103 of the fixed row-03 degree-four divisor cover, using anchor-witness indices `0, 0,
30, 39, 0, 0, 3, 48` and the listed affine inequalities. -/
def cell103 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 39, 0, 0, 3, 48] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1]] }

theorem cell103_check :
    cell103.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Cone 104 of the fixed row-03 degree-four divisor cover, using anchor-witness indices `0, 0,
31, 39, 0, 0, 3, 49` and the listed affine inequalities. -/
def cell104 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 31, 39, 0, 0, 3, 49] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell104_check :
    cell104.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Cone 105 of the fixed row-03 degree-four divisor cover, using anchor-witness indices `0, 0,
30, 35, 0, 0, 3, 41` and the listed affine inequalities. -/
def cell105 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 35, 0, 0, 3, 41] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 1, 0, 0, 1, 1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1]] }

theorem cell105_check :
    cell105.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Cone 106 of the fixed row-03 degree-four divisor cover, using anchor-witness indices `0, 0,
30, 46, 0, 0, 3, 45` and the listed affine inequalities. -/
def cell106 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 46, 0, 0, 3, 45] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]] }

theorem cell106_check :
    cell106.certificate.checkClosed 4 = true := by
  decide +kernel

/-- Cone 107 of the fixed row-03 degree-four divisor cover, using anchor-witness indices `0, 0,
30, 39, 0, 0, 3, 49` and the listed affine inequalities. -/
def cell107 : CoordinateCell row03Core :=
  { divisor := rowDivisor
    witness := fun anchor =>
      witnesses.getD
        (([0, 0, 30, 39, 0, 0, 3, 49] : List Nat).getD anchor.val 0) defaultWitness
    cone := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]] }

theorem cell107_check :
    cell107.certificate.checkClosed 4 = true := by
  decide +kernel

/-- The 108 coordinate cells used by the independent row-03 cover replay; each carries the fixed
degree-four divisor and its anchor witnesses. -/
def cells : List (CoordinateCell row03Core) := [cell0, cell1, cell2, cell3, cell4, cell5, cell6, cell7, cell8, cell9, cell10, cell11, cell12, cell13, cell14, cell15, cell16, cell17, cell18, cell19, cell20, cell21, cell22, cell23, cell24, cell25, cell26, cell27, cell28, cell29, cell30, cell31, cell32, cell33, cell34, cell35, cell36, cell37, cell38, cell39, cell40, cell41, cell42, cell43, cell44, cell45, cell46, cell47, cell48, cell49, cell50, cell51, cell52, cell53, cell54, cell55, cell56, cell57, cell58, cell59, cell60, cell61, cell62, cell63, cell64, cell65, cell66, cell67, cell68, cell69, cell70, cell71, cell72, cell73, cell74, cell75, cell76, cell77, cell78, cell79, cell80, cell81, cell82, cell83, cell84, cell85, cell86, cell87, cell88, cell89, cell90, cell91, cell92, cell93, cell94, cell95, cell96, cell97, cell98, cell99, cell100, cell101, cell102, cell103, cell104, cell105, cell106, cell107]

/-- The twelve coordinate nonnegativity inequalities defining the ambient cone of allowed row-03
edge lengths. -/
def base : List (ExplicitPotential.AffineForm 12) := [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], aff [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- The shared affine forms whose signs split the row-03 length cone in the compact cover tree. -/
def splitForms : List (ExplicitPotential.AffineForm 12) := [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0], aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0], aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1], aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1], aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1], aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1], aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0], aff [0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0], aff [0, 0, 1, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0], aff [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, 0, 1, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0], aff [0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1], aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1], aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1], aff [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1], aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1], aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1], aff [0, 0, 0, -1, 0, 0, 0, -1, -1, 1, 0, 0, 0], aff [0, 0, 0, 0, 1, 0, 0, 1, 1, -1, 0, 0, 0], aff [0, 0, 0, 0, -1, 0, 0, -1, 1, 1, 0, 0, 0], aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1], aff [0, 0, 0, -1, 0, 0, 0, -1, 1, 1, 0, 0, 0]]

theorem splitForm0 : splitForms.getD 0 0 = aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm1 : splitForms.getD 1 0 = aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm2 : splitForms.getD 2 0 = aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm3 : splitForms.getD 3 0 = aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm4 : splitForms.getD 4 0 = aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1] := by rfl

theorem splitForm5 : splitForms.getD 5 0 = aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm6 : splitForms.getD 6 0 = aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm7 : splitForms.getD 7 0 = aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm8 : splitForms.getD 8 0 = aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm9 : splitForms.getD 9 0 = aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm10 : splitForms.getD 10 0 = aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm11 : splitForms.getD 11 0 = aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm12 : splitForms.getD 12 0 = aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm13 : splitForms.getD 13 0 = aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm14 : splitForms.getD 14 0 = aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0] := by rfl

theorem splitForm15 : splitForms.getD 15 0 = aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm16 : splitForms.getD 16 0 = aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm17 : splitForms.getD 17 0 = aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm18 : splitForms.getD 18 0 = aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm19 : splitForms.getD 19 0 = aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm20 : splitForms.getD 20 0 = aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm21 : splitForms.getD 21 0 = aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm22 : splitForms.getD 22 0 = aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm23 : splitForms.getD 23 0 = aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm24 : splitForms.getD 24 0 = aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm25 : splitForms.getD 25 0 = aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm26 : splitForms.getD 26 0 = aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm27 : splitForms.getD 27 0 = aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm28 : splitForms.getD 28 0 = aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1] := by rfl

theorem splitForm29 : splitForms.getD 29 0 = aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1] := by rfl

theorem splitForm30 : splitForms.getD 30 0 = aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1] := by rfl

theorem splitForm31 : splitForms.getD 31 0 = aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm32 : splitForms.getD 32 0 = aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1] := by rfl

theorem splitForm33 : splitForms.getD 33 0 = aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0] := by rfl

theorem splitForm34 : splitForms.getD 34 0 = aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0] := by rfl

theorem splitForm35 : splitForms.getD 35 0 = aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm36 : splitForms.getD 36 0 = aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm37 : splitForms.getD 37 0 = aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0] := by rfl

theorem splitForm38 : splitForms.getD 38 0 = aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1] := by rfl

theorem splitForm39 : splitForms.getD 39 0 = aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1] := by rfl

theorem splitForm40 : splitForms.getD 40 0 = aff [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm41 : splitForms.getD 41 0 = aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm42 : splitForms.getD 42 0 = aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm43 : splitForms.getD 43 0 = aff [0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by rfl

theorem splitForm44 : splitForms.getD 44 0 = aff [0, -1, 0, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm45 : splitForms.getD 45 0 = aff [0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0] := by rfl

theorem splitForm46 : splitForms.getD 46 0 = aff [0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0] := by rfl

theorem splitForm47 : splitForms.getD 47 0 = aff [0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm48 : splitForms.getD 48 0 = aff [0, -1, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0] := by rfl

theorem splitForm49 : splitForms.getD 49 0 = aff [0, 0, 1, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm50 : splitForms.getD 50 0 = aff [0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm51 : splitForms.getD 51 0 = aff [0, 0, 1, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm52 : splitForms.getD 52 0 = aff [0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm53 : splitForms.getD 53 0 = aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm54 : splitForms.getD 54 0 = aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 1] := by rfl

theorem splitForm55 : splitForms.getD 55 0 = aff [0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] := by rfl

theorem splitForm56 : splitForms.getD 56 0 = aff [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1] := by rfl

theorem splitForm57 : splitForms.getD 57 0 = aff [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1] := by rfl

theorem splitForm58 : splitForms.getD 58 0 = aff [0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm59 : splitForms.getD 59 0 = aff [0, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0, 0, 0] := by rfl

theorem splitForm60 : splitForms.getD 60 0 = aff [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1] := by rfl

theorem splitForm61 : splitForms.getD 61 0 = aff [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0] := by rfl

theorem splitForm62 : splitForms.getD 62 0 = aff [0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm63 : splitForms.getD 63 0 = aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 1] := by rfl

theorem splitForm64 : splitForms.getD 64 0 = aff [0, 0, 0, -1, 0, 0, 0, -1, -1, 1, 0, 0, 0] := by rfl

theorem splitForm65 : splitForms.getD 65 0 = aff [0, 0, 0, 0, 1, 0, 0, 1, 1, -1, 0, 0, 0] := by rfl

theorem splitForm66 : splitForms.getD 66 0 = aff [0, 0, 0, 0, -1, 0, 0, -1, 1, 1, 0, 0, 0] := by rfl

theorem splitForm67 : splitForms.getD 67 0 = aff [0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by rfl

theorem splitForm68 : splitForms.getD 68 0 = aff [0, 0, 0, -1, 0, 0, 0, -1, 1, 1, 0, 0, 0] := by rfl

/-- Farkas receipt entries 0 through 127 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts0 : List Certificate.AffineCover.FarkasData := [{ terms := [{ row := 0, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 16, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 11, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 11, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 17, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 17, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 17, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 26, weight := 1 }] }]

/-- Farkas receipt entries 128 through 255 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts1 : List Certificate.AffineCover.FarkasData := [{ terms := [{ row := 1, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 20, weight := 2 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 21, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 25, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 26, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 11, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 25, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 27, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 26, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 26, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 29, weight := 1 }] }]

/-- Farkas receipt entries 256 through 383 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts2 : List Certificate.AffineCover.FarkasData := [{ terms := [{ row := 25, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 28, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 27, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 27, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 27, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 29, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 28, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 28, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 24, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 26, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 25, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 14, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 14, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 15, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 14, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 14, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 24, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 15, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 24, weight := 1 }] }]

/-- Farkas receipt entries 384 through 511 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts3 : List Certificate.AffineCover.FarkasData := [{ terms := [{ row := 0, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 2 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 2 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 27, weight := 2 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 20, weight := 2 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 2 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 27, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 24, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 28, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 27, weight := 1 }, { row := 28, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 2 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 23, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 2 }] }]

/-- Farkas receipt entries 512 through 639 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts4 : List Certificate.AffineCover.FarkasData := [{ terms := [{ row := 5, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 23, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 19, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 21, weight := 1 }, { row := 23, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 2 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 23, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 28, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 23, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 2 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 25, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 30, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }, { row := 29, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 23, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 11, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 4, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 9, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 10, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 11, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 12, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 15, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 16, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 15, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 15, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 15, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 15, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 15, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 21, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 14, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 8, weight := 1 }, { row := 11, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 17, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 17, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 8, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 17, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 17, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 25, weight := 2 }] }, { terms := [{ row := 14, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 26, weight := 2 }] }, { terms := [{ row := 14, weight := 1 }, { row := 20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 14, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 25, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 23, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 26, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 22, weight := 1 }, { row := 24, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 25, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 5, weight := 1 }, { row := 12, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 21, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 8, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 0, weight := 1 }, { row := 5, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }]

/-- Farkas receipt entries 640 through 767 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts5 : List Certificate.AffineCover.FarkasData := [{ terms := [{ row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 19, weight := 1 }, { row := 27, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 8, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 1, weight := 1 }, { row := 5, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 24, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 11, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 15, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 16, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 11, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 15, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 16, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 15, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 18, weight := 2 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 15, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 17, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 22, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 17, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 15, weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 11, weight := 1 }, { row := 13, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 7, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 19, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 6, weight := 1 }, { row := 11, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 24, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 7, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 12, weight := 1 }, { row := 18, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 12, weight := 1 }, { row := 19, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 17, weight := 2 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 17, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 15, weight := 1 }, { row := 17, weight := 2 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 18, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 20, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 22, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 23, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 20, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 22, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 22, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 20, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 19, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 21, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 21, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 21, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 26, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 17, weight := 1 }, { row := 18, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 16, weight := 1 }, { row := 18, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 24, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 7, weight := 1 }, { row := 25, weight := 1 }] }]

/-- Farkas receipt entries 768 through 795 for the row-03 cover: sparse rational combinations of
active inequalities used to certify cell inclusion or exclude a branch. -/
def farkasReceipts6 : List Certificate.AffineCover.FarkasData := [{ terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 18, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 17, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 18, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 17, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 7, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 3, weight := 1 }, { row := 19, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 17, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 14, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 17, weight := 1 }, { row := 23, weight := 1 }] }, { terms := [{ row := 13, weight := 1 }, { row := 19, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 7, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 19, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 6, weight := 1 }, { row := 7, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 7, weight := 1 }, { row := 20, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 20, weight := 1 }, { row := 21, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 20, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 2, weight := 1 }, { row := 7, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }, { terms := [{ row := 7, weight := 1 }, { row := 21, weight := 1 }, { row := 22, weight := 1 }] }]

/-- The concatenated Farkas receipt table indexed by the compact row-03 cover tree. -/
def farkasReceipts : List Certificate.AffineCover.FarkasData := farkasReceipts0 ++ farkasReceipts1 ++ farkasReceipts2 ++ farkasReceipts3 ++ farkasReceipts4 ++ farkasReceipts5 ++ farkasReceipts6

/-- The leaf selecting cell zero with Farkas receipts 0 through 15 for its cone inequalities. -/
def treePart0 : CompactCellTree :=
  .cell 0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

theorem treePart0_check :
    treePart0.check splitForms farkasReceipts cells ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- The row-03 subtree selecting cells one or two according to split forms 14 and 15; receipt 60
excludes the remaining branch. -/
def treePart1 : CompactCellTree :=
  .split 14
    (.cell 1 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37])
    (.split 15
        (.cell 2 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59])
        (.absurd 60))

theorem treePart1_check :
    treePart1.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- The row-03 subtree selecting cells three through eight, with Farkas receipts excluding sign
branches outside those cell cones. -/
def treePart2 : CompactCellTree :=
  .split 19
    (.split 18
        (.split 14
            (.cell 3 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81])
            (.split 15
                (.cell 4 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102])
                (.absurd 103)))
        (.absurd 104))
    (.split 40
        (.split 18
            (.split 11
                (.split 14
                    (.cell 5 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126])
                    (.split 15
                        (.cell 6 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148])
                        (.absurd 149)))
                (.absurd 150))
            (.absurd 151))
        (.split 18
            (.split 11
                (.split 14
                    (.split 22
                        (.cell 7 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 152, 145, 144, 153, 143, 154, 146])
                        (.absurd 155))
                    (.split 15
                        (.split 22
                            (.cell 8 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
                            (.absurd 179))
                        (.absurd 149)))
                (.absurd 150))
            (.absurd 180)))

theorem treePart2_check :
    treePart2.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- The row-03 subtree selecting cells nine through thirteen; repeated leaves for cell nine
certify its inclusion from different active inequalities. -/
def treePart3 : CompactCellTree :=
  .split 19
    (.split 7
        (.cell 9 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 55, 53, 54, 52, 56, 181, 58, 57])
        (.split 18
            (.cell 10 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 79, 74, 73, 76, 77, 75, 80, 78, 81])
            (.absurd 182)))
    (.split 7
        (.cell 9 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 55, 53, 54, 52, 56, 181, 58, 183])
        (.split 18
            (.split 11
                (.split 16
                    (.cell 11 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 184, 123, 121, 122])
                    (.split 40
                        (.cell 12 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 185, 144, 152, 143, 147, 148])
                        (.split 22
                            (.cell 13 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 186, 173, 187, 175, 176, 177, 172])
                            (.absurd 188))))
                (.absurd 150))
            (.absurd 189)))

theorem treePart3_check :
    treePart3.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[11]` in the row-03 length cone, with leaves
selecting cells 2, 4, 6, 8 and Farkas receipts excluding inconsistent sign branches. -/
def treePart4 : CompactCellTree :=
  .split 19
    (.split 41
        (.split 7
            (.cell 2 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 190, 191, 79, 76, 77, 75, 80, 73, 81, 74])
            (.split 18
                (.cell 4 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 99, 95, 101, 97, 98, 96, 100, 94, 102])
                (.absurd 192)))
        (.absurd 193))
    (.split 7
        (.absurd 194)
        (.split 18
            (.split 11
                (.split 16
                    (.absurd 195)
                    (.split 41
                        (.split 40
                            (.cell 6 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 186, 173, 172, 176, 196, 197])
                            (.split 22
                                (.cell 8 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220])
                                (.absurd 221)))
                        (.absurd 222)))
                (.absurd 150))
            (.absurd 223)))

theorem treePart4_check :
    treePart4.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[11]` in the row-03 length cone, with leaves
selecting cells 14, 15 and Farkas receipts excluding inconsistent sign branches. -/
def treePart5 : CompactCellTree :=
  .split 19
    (.split 14
        (.cell 14 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 78, 190, 76, 77, 75, 79, 80, 224])
        (.split 15
            (.cell 15 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 225, 226, 97, 98, 99, 100, 101, 227])
            (.absurd 228)))
    (.absurd 60)

theorem treePart5_check :
    treePart5.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] + length[11]` in the row-03 length cone, with leaves
selecting cells 3, 4, 5, 6, 7, 8, 16, 17 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart6 : CompactCellTree :=
  .split 12
    (.split 19
        (.split 14
            (.cell 16 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 229, 118, 124, 117, 184, 122, 123, 121, 119, 125, 126])
            (.split 15
                (.cell 17 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 230, 140, 146, 139, 143, 144, 145, 152, 141, 147, 148])
                (.absurd 231)))
        (.split 16
            (.absurd 232)
            (.split 14
                (.split 40
                    (.cell 5 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 233, 169, 178, 168, 186, 172, 173, 176, 196, 197])
                    (.split 22
                        (.cell 7 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 234, 211, 235, 210, 214, 216, 215, 217, 218, 219, 220])
                        (.absurd 221)))
                (.split 15
                    (.split 40
                        (.cell 6 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 234, 211, 235, 210, 220, 215, 216, 218, 236, 237])
                        (.split 22
                            (.cell 8 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260])
                            (.absurd 261)))
                    (.absurd 262)))))
    (.split 42
        (.split 14
            (.cell 3 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 117, 119, 125, 126, 184, 122, 123, 121])
            (.split 15
                (.cell 4 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 139, 141, 147, 148, 143, 144, 145, 152])
                (.absurd 231)))
        (.absurd 263))

theorem treePart6_check :
    treePart6.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] + length[11]` in the row-03 length cone, with leaves
selecting cells 3, 4 and Farkas receipts excluding inconsistent sign branches. -/
def treePart7 : CompactCellTree :=
  .split 12
    (.absurd 264)
    (.split 42
        (.split 14
            (.cell 3 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 155, 119, 125, 126, 184, 122, 123, 121])
            (.split 15
                (.cell 4 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 179, 141, 147, 148, 143, 144, 145, 152])
                (.absurd 231)))
        (.absurd 263))

theorem treePart7_check :
    treePart7.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[11]` in the row-03 length cone, with leaves
selecting cells 15, 18 and Farkas receipts excluding inconsistent sign branches. -/
def treePart8 : CompactCellTree :=
  .split 19
    (.split 8
        (.cell 18 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 78, 190, 76, 77, 79, 80, 75, 224])
        (.split 41
            (.cell 15 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 225, 226, 97, 98, 101, 100, 99, 227])
            (.absurd 228)))
    (.absurd 60)

theorem treePart8_check :
    treePart8.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 6, 8, 11, 12, 13, 17, 19 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart9 : CompactCellTree :=
  .split 8
    (.split 19
        (.cell 19 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 229, 118, 124, 117, 119, 123, 184, 121, 122, 125, 126])
        (.split 16
            (.cell 11 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 230, 140, 146, 139, 141, 144, 185, 143])
            (.split 40
                (.cell 12 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 233, 169, 178, 168, 170, 173, 186, 176, 196, 197])
                (.split 22
                    (.cell 13 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 234, 211, 235, 210, 212, 215, 214, 217, 218, 219, 220])
                    (.absurd 221)))))
    (.split 19
        (.split 41
            (.cell 17 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 230, 140, 146, 139, 141, 144, 143, 152, 145, 147, 148])
            (.absurd 265))
        (.split 16
            (.absurd 266)
            (.split 41
                (.split 40
                    (.cell 6 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 234, 211, 235, 210, 212, 215, 220, 218, 236, 237])
                    (.split 22
                        (.cell 8 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 267, 255, 254, 257, 258, 259, 260])
                        (.absurd 261)))
                (.absurd 268))))

theorem treePart9_check :
    treePart9.check splitForms farkasReceipts cells (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 4, 10 and Farkas receipts excluding inconsistent sign branches. -/
def treePart10 : CompactCellTree :=
  .split 8
    (.split 42
        (.cell 10 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 117, 122, 125, 126, 119, 123, 184, 121])
        (.absurd 269))
    (.split 42
        (.split 41
            (.cell 4 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 139, 145, 147, 148, 141, 144, 143, 152])
            (.absurd 265))
        (.absurd 269))

theorem treePart10_check :
    treePart10.check splitForms farkasReceipts cells (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[11]` in the row-03 length cone, with leaves
selecting cells 4, 10, 20 and Farkas receipts excluding inconsistent sign branches. -/
def treePart11 : CompactCellTree :=
  .split 19
    (.split 8
        (.split 12
            (.cell 20 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 149, 117, 122, 125, 126, 119, 123, 184, 121])
            (.split 42
                (.cell 10 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 139, 143, 147, 148, 141, 144, 185, 152])
                (.absurd 270)))
        (.split 12
            (.absurd 271)
            (.split 42
                (.split 41
                    (.cell 4 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 171, 168, 172, 196, 197, 170, 173, 176, 187])
                    (.absurd 268))
                (.absurd 270))))
    (.absurd 264)

theorem treePart11_check :
    treePart11.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 21, 22 and Farkas receipts excluding inconsistent sign branches. -/
def treePart12 : CompactCellTree :=
  .split 24
    (.split 6
        (.cell 21 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 272, 101, 225, 99, 95, 100, 96, 97, 98])
        (.split 8
            (.cell 22 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 273, 117, 121, 122, 123, 119, 184, 125, 126])
            (.absurd 274)))
    (.absurd 275)

theorem treePart12_check :
    treePart12.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 5, 7, 12, 13, 23, 24 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart13 : CompactCellTree :=
  .split 11
    (.split 12
        (.split 6
            (.split 19
                (.cell 23 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 140, 139, 141, 145, 142, 144, 143, 147, 148])
                (.split 16
                    (.cell 24 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178, 169, 168, 170, 174, 171, 173, 176])
                    (.split 40
                        (.cell 5 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 235, 211, 210, 212, 276, 213, 215, 218, 236, 237])
                        (.split 22
                            (.cell 7 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 252, 251, 253, 267, 277, 278, 255, 257, 258, 259, 260])
                            (.absurd 261)))))
            (.split 19
                (.absurd 279)
                (.split 16
                    (.absurd 280)
                    (.split 8
                        (.split 40
                            (.cell 12 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 252, 251, 253, 267, 260, 255, 277, 258, 281, 282])
                            (.split 22
                                (.cell 13 [283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305])
                                (.absurd 306)))
                        (.absurd 307)))))
        (.absurd 308))
    (.absurd 309)

theorem treePart13_check :
    treePart13.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 6, 8, 25, 26, 27 and Farkas receipts excluding inconsistent sign branches. -/
def treePart14 : CompactCellTree :=
  .split 10
    (.split 24
        (.cell 25 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 272, 99, 225, 94, 100, 95, 96, 97, 98])
        (.absurd 310))
    (.split 11
        (.split 12
            (.split 19
                (.cell 26 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 145, 146, 144, 142, 143, 147, 148])
                (.split 16
                    (.cell 27 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 174, 178, 173, 171, 176])
                    (.split 40
                        (.cell 6 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 276, 235, 215, 213, 218, 236, 237])
                        (.split 22
                            (.cell 8 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 253, 251, 267, 277, 252, 255, 278, 257, 258, 259, 260])
                            (.absurd 261)))))
            (.absurd 311))
        (.absurd 312))

theorem treePart14_check :
    treePart14.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 12, 13, 22 and Farkas receipts excluding inconsistent sign branches. -/
def treePart15 : CompactCellTree :=
  .split 10
    (.split 24
        (.split 43
            (.cell 22 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 273, 119, 121, 124, 123, 122, 184, 125, 126])
            (.absurd 313))
        (.absurd 310))
    (.split 11
        (.split 12
            (.split 19
                (.absurd 229)
                (.split 16
                    (.absurd 314)
                    (.split 43
                        (.split 40
                            (.cell 12 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 253, 251, 267, 277, 252, 255, 260, 258, 281, 282])
                            (.split 22
                                (.cell 13 [283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 297, 296, 298, 301, 295, 300, 299, 302, 303, 304, 305])
                                (.absurd 306)))
                        (.absurd 315))))
            (.absurd 311))
        (.absurd 312))

theorem treePart15_check :
    treePart15.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 28, 29, 30 and Farkas receipts excluding inconsistent sign branches. -/
def treePart16 : CompactCellTree :=
  .split 24
    (.split 6
        (.split 14
            (.split 44
                (.cell 28 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 273, 124, 121, 117, 119, 123, 316, 122, 317, 184])
                (.absurd 318))
            (.split 15
                (.split 44
                    (.cell 29 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 319, 146, 152, 145, 144, 141, 320, 143, 321, 185])
                    (.absurd 322))
                (.absurd 323)))
        (.split 8
            (.split 44
                (.cell 30 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 273, 124, 121, 119, 123, 117, 316, 122, 317, 184])
                (.absurd 318))
            (.split 41
                (.split 44
                    (.cell 29 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 319, 146, 152, 141, 144, 145, 320, 143, 321, 185])
                    (.absurd 322))
                (.absurd 323))))
    (.absurd 324)

theorem treePart16_check :
    treePart16.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[11]` in the row-03 length cone, with leaves
selecting cells 5, 6, 7, 8, 12, 13 and Farkas receipts excluding inconsistent sign branches. -/
def treePart17 : CompactCellTree :=
  .split 19
    (.absurd 224)
    (.split 16
        (.absurd 325)
        (.split 6
            (.split 14
                (.split 40
                    (.cell 5 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 213, 211, 235, 210, 216, 220, 215, 218, 236, 237])
                    (.split 22
                        (.cell 7 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 278, 251, 252, 253, 256, 254, 255, 257, 258, 259, 326])
                        (.absurd 327)))
                (.split 15
                    (.split 40
                        (.cell 6 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 278, 251, 252, 253, 260, 255, 254, 258, 281, 282])
                        (.split 22
                            (.cell 8 [283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 328, 296, 295, 297, 299, 300, 329, 302, 303, 304, 330])
                            (.absurd 331)))
                    (.absurd 332)))
            (.split 8
                (.split 40
                    (.cell 12 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 213, 211, 235, 210, 220, 215, 216, 218, 236, 237])
                    (.split 22
                        (.cell 13 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 278, 251, 252, 253, 254, 255, 256, 257, 258, 259, 326])
                        (.absurd 327)))
                (.split 41
                    (.split 40
                        (.cell 6 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 278, 251, 252, 253, 254, 255, 260, 258, 281, 282])
                        (.split 22
                            (.cell 8 [283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 328, 296, 295, 297, 329, 300, 299, 302, 303, 304, 330])
                            (.absurd 331)))
                    (.absurd 332)))))

theorem treePart17_check :
    treePart17.check splitForms farkasReceipts cells (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 333 to exclude the accumulated affine constraints in
this row-03 branch. -/
def treePart18 : CompactCellTree :=
  .absurd 333

theorem treePart18_check :
    treePart18.check splitForms farkasReceipts cells (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 334 to exclude the accumulated affine constraints in
this row-03 branch. -/
def treePart19 : CompactCellTree :=
  .absurd 334

theorem treePart19_check :
    treePart19.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[5] + length[6] - length[7] - length[8]` in the row-03 length
cone, with leaves selecting cells 31, 32, 33, 34 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart20 : CompactCellTree :=
  .split 45
    (.split 46
        (.cell 31 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 79, 335, 336, 337, 190, 74, 80, 75, 78, 338])
        (.split 18
            (.split 47
                (.cell 32 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 119, 121, 122, 123, 126, 339, 120, 184])
                (.split 20
                    (.cell 33 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 143, 340, 145, 144, 148, 341, 142, 185, 152])
                    (.absurd 342)))
            (.split 48
                (.cell 34 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 119, 184, 122, 123, 126, 339, 120, 121])
                (.split 49
                    (.cell 33 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 145, 340, 143, 144, 148, 341, 142, 185, 152])
                    (.absurd 342)))))
    (.absurd 343)

theorem treePart20_check :
    treePart20.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[2] - length[3]` in the row-03 length cone, with leaves
selecting cells 35, 36, 37, 38 and Farkas receipts excluding inconsistent sign branches. -/
def treePart21 : CompactCellTree :=
  .split 15
    (.split 45
        (.split 46
            (.cell 35 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 99, 344, 345, 346, 94, 100, 95, 96, 225, 347])
            (.split 18
                (.split 47
                    (.cell 36 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 145, 152, 143, 144, 148, 146, 142, 185])
                    (.split 20
                        (.cell 37 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 176, 348, 172, 173, 197, 178, 171, 186, 187])
                        (.absurd 349)))
                (.split 48
                    (.cell 38 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 145, 185, 143, 144, 148, 146, 142, 152])
                    (.split 49
                        (.cell 37 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 172, 348, 176, 173, 197, 178, 171, 186, 187])
                        (.absurd 349)))))
        (.absurd 350))
    (.absurd 351)

theorem treePart21_check :
    treePart21.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[3] - length[7]` in the row-03 length cone, with leaves
selecting cells 28, 29, 39, 40, 41 and Farkas receipts excluding inconsistent sign branches. -/
def treePart22 : CompactCellTree :=
  .split 14
    (.split 10
        (.split 21
            (.split 27
                (.cell 39 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 272, 96, 99, 226, 95, 100, 101, 98])
                (.absurd 352))
            (.split 27
                (.split 50
                    (.cell 28 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 273, 184, 119, 339, 120, 123, 316, 117, 317, 122])
                    (.absurd 353))
                (.absurd 352)))
        (.absurd 193))
    (.split 10
        (.split 27
            (.split 15
                (.split 9
                    (.cell 40 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 273, 184, 117, 119, 123, 120, 122])
                    (.split 21
                        (.cell 41 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 319, 185, 139, 141, 144, 142, 143, 148])
                        (.split 50
                            (.cell 29 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178, 354, 186, 168, 170, 173, 171, 355, 172, 356, 176])
                            (.absurd 188))))
                (.absurd 263))
            (.absurd 357))
        (.absurd 193))

theorem treePart22_check :
    treePart22.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] + length[5] - length[6] + length[8]` in the row-03 length
cone, with leaves selecting cells 7, 8, 42, 43 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart23 : CompactCellTree :=
  .split 51
    (.split 12
        (.split 14
            (.cell 42 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 75, 358, 78, 73, 190, 79, 80, 74, 77])
            (.split 15
                (.cell 43 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 96, 359, 225, 94, 99, 100, 101, 95, 98])
                (.absurd 192)))
        (.absurd 324))
    (.split 12
        (.split 14
            (.split 52
                (.cell 7 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 96, 359, 225, 94, 226, 101, 100, 360, 95, 361, 99])
                (.absurd 150))
            (.split 15
                (.split 52
                    (.cell 8 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 184, 118, 121, 124, 119, 123, 117, 362, 120, 363, 122])
                    (.absurd 195))
                (.absurd 192)))
        (.absurd 324))

theorem treePart23_check :
    treePart23.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 28, 29, 39, 41, 44, 45, 46 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart24 : CompactCellTree :=
  .split 24
    (.split 27
        (.split 14
            (.split 9
                (.cell 44 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 96, 272, 95, 94, 226, 101, 100, 99])
                (.split 17
                    (.cell 45 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 184, 273, 120, 124, 339, 117, 123, 122])
                    (.split 21
                        (.cell 39 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 185, 319, 142, 146, 341, 139, 144, 143, 148])
                        (.split 50
                            (.cell 28 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 186, 354, 171, 178, 364, 168, 173, 355, 172, 356, 176])
                            (.absurd 188)))))
            (.split 9
                (.absurd 365)
                (.split 15
                    (.split 17
                        (.cell 46 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 185, 319, 142, 146, 145, 144, 139, 143])
                        (.split 21
                            (.cell 41 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 186, 354, 171, 178, 174, 173, 168, 176, 197])
                            (.split 50
                                (.cell 29 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 214, 366, 213, 235, 276, 215, 210, 367, 220, 368, 218])
                                (.absurd 221))))
                    (.absurd 369))))
        (.absurd 370))
    (.absurd 371)

theorem treePart24_check :
    treePart24.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[6] + length[8]` in the row-03 length cone, with
leaves selecting cells 30, 47, 48, 49, 50, 51, 52 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart25 : CompactCellTree :=
  .split 17
    (.split 45
        (.split 46
            (.cell 47 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 79, 335, 336, 337, 78, 80, 190, 74, 75, 338])
            (.split 18
                (.split 47
                    (.cell 48 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 119, 184, 122, 123, 126, 121, 339, 120])
                    (.split 20
                        (.cell 49 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 143, 340, 145, 144, 148, 152, 341, 142, 185])
                        (.absurd 342)))
                (.split 48
                    (.cell 50 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 119, 120, 122, 123, 126, 121, 339, 184])
                    (.split 49
                        (.cell 49 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 145, 340, 143, 144, 148, 152, 341, 142, 185])
                        (.absurd 342)))))
        (.absurd 343))
    (.split 18
        (.absurd 372)
        (.split 27
            (.split 9
                (.cell 51 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 373, 272, 95, 101, 225, 100, 226, 99])
                (.split 21
                    (.cell 52 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 374, 273, 120, 117, 121, 123, 339, 122, 126])
                    (.split 50
                        (.cell 30 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 375, 319, 142, 139, 152, 144, 341, 320, 145, 321, 143])
                        (.absurd 266))))
            (.absurd 376)))

theorem treePart25_check :
    treePart25.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[1]` in the row-03 length cone, with leaves
selecting cells 13, 30, 51, 52, 53, 54 and Farkas receipts excluding inconsistent sign branches. -/
def treePart26 : CompactCellTree :=
  .split 18
    (.split 12
        (.split 51
            (.cell 53 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 358, 75, 73, 78, 80, 190, 79, 77])
            (.split 52
                (.cell 13 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 359, 96, 94, 225, 100, 226, 360, 101, 361, 99])
                (.absurd 377)))
        (.absurd 378))
    (.split 24
        (.split 27
            (.split 9
                (.cell 51 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 272, 94, 101, 225, 100, 226, 99])
                (.split 17
                    (.cell 54 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 273, 124, 117, 121, 123, 339, 122])
                    (.split 21
                        (.cell 52 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 319, 146, 139, 152, 144, 341, 143, 148])
                        (.split 50
                            (.cell 30 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 171, 354, 178, 168, 187, 173, 364, 355, 172, 356, 176])
                            (.absurd 188)))))
            (.absurd 379))
        (.absurd 372))

theorem treePart26_check :
    treePart26.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[6] + length[8]` in the row-03 length cone, with
leaves selecting cells 8, 35, 36, 37, 38, 43 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart27 : CompactCellTree :=
  .split 16
    (.split 45
        (.split 41
            (.split 46
                (.cell 35 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 99, 344, 345, 346, 225, 100, 101, 96, 95, 347])
                (.split 47
                    (.split 18
                        (.cell 36 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 143, 142, 145, 144, 148, 152, 139, 185])
                        (.split 48
                            (.cell 38 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 172, 186, 176, 173, 197, 187, 168, 171])
                            (.absurd 349)))
                    (.split 20
                        (.cell 37 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 143, 340, 145, 144, 148, 152, 139, 185, 142])
                        (.split 10
                            (.cell 38 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 176, 186, 172, 173, 197, 187, 168, 171])
                            (.absurd 349)))))
            (.absurd 380))
        (.absurd 343))
    (.split 18
        (.split 12
            (.split 41
                (.split 51
                    (.cell 43 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 118, 120, 117, 121, 123, 119, 122, 126])
                    (.split 52
                        (.cell 8 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 140, 142, 139, 152, 144, 141, 153, 145, 154, 143])
                        (.absurd 266)))
                (.absurd 381))
            (.absurd 376))
        (.absurd 372))

theorem treePart27_check :
    treePart27.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 8, 29, 40, 41, 43 and Farkas receipts excluding inconsistent sign branches. -/
def treePart28 : CompactCellTree :=
  .split 10
    (.split 27
        (.split 41
            (.split 9
                (.cell 40 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 272, 96, 94, 225, 100, 101, 99])
                (.split 21
                    (.cell 41 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 273, 184, 124, 121, 123, 117, 122, 126])
                    (.split 50
                        (.cell 29 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 319, 185, 146, 152, 144, 139, 320, 145, 321, 143])
                        (.absurd 266))))
            (.absurd 380))
        (.absurd 378))
    (.split 11
        (.split 12
            (.split 16
                (.absurd 382)
                (.split 41
                    (.split 51
                        (.cell 43 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 140, 146, 139, 152, 144, 145, 143, 148])
                        (.split 52
                            (.cell 8 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 171, 169, 178, 168, 187, 173, 174, 175, 172, 177, 176])
                            (.absurd 188)))
                    (.absurd 383)))
            (.absurd 379))
        (.absurd 372))

theorem treePart28_check :
    treePart28.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Leaf selecting row-03 cell 55, with 17 Farkas receipts deriving its cone inequalities from
the active branch constraints. -/
def treePart29 : CompactCellTree :=
  .cell 55 [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400]

theorem treePart29_check :
    treePart29.check splitForms farkasReceipts cells ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5] - length[11]` in the row-03 length cone, with
leaves selecting cells 1, 3, 5, 7 and Farkas receipts excluding inconsistent sign branches. -/
def treePart30 : CompactCellTree :=
  .split 7
    (.cell 1 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 29, 34, 31, 33, 401, 32, 35, 37, 402])
    (.split 19
        (.split 18
            (.cell 3 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 79, 73, 74, 76, 78, 403, 77, 80, 404])
            (.absurd 405))
        (.split 40
            (.split 18
                (.split 11
                    (.cell 5 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 119, 118, 122, 124, 406, 126, 123, 117, 125, 121])
                    (.absurd 407))
                (.absurd 408))
            (.split 18
                (.split 11
                    (.split 22
                        (.cell 7 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 141, 140, 145, 146, 409, 148, 144, 153, 143, 154, 139])
                        (.absurd 229))
                    (.absurd 407))
                (.absurd 382))))

theorem treePart30_check :
    treePart30.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[11]` in the row-03 length cone, with leaves
selecting cells 3, 14, 21, 28, 56, 57 and Farkas receipts excluding inconsistent sign branches. -/
def treePart31 : CompactCellTree :=
  .split 9
    (.split 10
        (.cell 14 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 79, 73, 75, 76, 78, 403, 77, 80, 74])
        (.split 12
            (.cell 56 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 410, 95, 99, 97, 225, 411, 98, 100, 94])
            (.split 42
                (.cell 3 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 120, 122, 125, 121, 406, 126, 123, 124])
                (.absurd 412))))
    (.split 12
        (.split 18
            (.cell 57 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 99, 95, 101, 97, 225, 411, 98, 100])
            (.split 24
                (.split 13
                    (.cell 21 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 413, 319, 145, 146, 409, 148, 144, 143, 147, 152])
                    (.split 44
                        (.cell 28 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 315, 354, 174, 178, 414, 197, 173, 355, 176, 356, 172])
                        (.absurd 415)))
                (.absurd 407)))
        (.split 10
            (.split 24
                (.split 13
                    (.cell 21 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 141, 319, 145, 146, 409, 148, 144, 143, 147, 152])
                    (.split 44
                        (.cell 28 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 170, 354, 174, 178, 414, 197, 173, 355, 176, 356, 172])
                        (.absurd 415)))
                (.absurd 407))
            (.absurd 416)))

theorem treePart31_check :
    treePart31.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] + length[5] - length[11]` in the row-03 length cone, with
leaves selecting cells 5, 7, 21, 28 and Farkas receipts excluding inconsistent sign branches. -/
def treePart32 : CompactCellTree :=
  .split 40
    (.split 18
        (.split 11
            (.cell 5 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 359, 99, 95, 411, 98, 100, 94, 97, 225])
            (.absurd 224))
        (.split 9
            (.absurd 417)
            (.split 24
                (.split 13
                    (.cell 21 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 319, 145, 418, 409, 148, 144, 143, 147, 152])
                    (.split 44
                        (.cell 28 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 354, 174, 419, 414, 197, 173, 355, 176, 356, 172])
                        (.absurd 415)))
                (.absurd 420))))
    (.split 18
        (.split 11
            (.split 22
                (.cell 7 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 406, 126, 123, 362, 122, 363, 124])
                (.absurd 407))
            (.absurd 224))
        (.split 9
            (.absurd 417)
            (.split 24
                (.split 13
                    (.cell 21 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 319, 145, 421, 409, 148, 144, 143, 147, 152])
                    (.split 44
                        (.cell 28 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 354, 174, 422, 414, 197, 173, 355, 176, 356, 172])
                        (.absurd 423)))
                (.absurd 420))))

theorem treePart32_check :
    treePart32.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5] - length[6] + length[8]` in the row-03 length
cone, with leaves selecting cells 7, 32, 33, 42 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart33 : CompactCellTree :=
  .split 49
    (.cell 33 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 424, 34, 35, 33, 401, 32, 37, 402])
    (.split 16
        (.split 18
            (.cell 32 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 79, 73, 74, 80, 78, 403, 77, 404])
            (.absurd 405))
        (.split 18
            (.split 12
                (.split 51
                    (.cell 42 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 124, 119, 406, 126, 123, 122, 121])
                    (.split 52
                        (.cell 7 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 146, 141, 409, 148, 144, 153, 145, 154, 143])
                        (.absurd 149)))
                (.absurd 308))
            (.absurd 405)))

theorem treePart33_check :
    treePart33.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 7, 24, 32, 34, 42 and Farkas receipts excluding inconsistent sign branches. -/
def treePart34 : CompactCellTree :=
  .split 10
    (.split 16
        (.cell 34 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 80, 78, 403, 77, 425])
        (.absurd 426))
    (.split 11
        (.split 12
            (.split 16
                (.cell 24 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 427, 118, 117, 119, 406, 126, 123, 122])
                (.split 51
                    (.cell 42 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 418, 140, 139, 141, 409, 148, 144, 143, 152])
                    (.split 52
                        (.cell 7 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 419, 169, 168, 170, 414, 197, 173, 175, 172, 177, 176])
                        (.absurd 415))))
            (.absurd 103))
        (.split 47
            (.cell 32 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 101, 99, 100, 225, 411, 98, 95])
            (.absurd 428)))

theorem treePart34_check :
    treePart34.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 7, 24, 28, 39, 42, 44 and Farkas receipts excluding inconsistent sign branches. -/
def treePart35 : CompactCellTree :=
  .split 10
    (.split 27
        (.split 9
            (.cell 44 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 272, 95, 101, 411, 98, 100, 99])
            (.split 21
                (.cell 39 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 273, 120, 117, 406, 126, 123, 122, 121])
                (.split 50
                    (.cell 28 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 319, 142, 139, 409, 148, 144, 320, 145, 321, 143])
                    (.absurd 149))))
        (.absurd 333))
    (.split 11
        (.split 12
            (.split 16
                (.cell 24 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 118, 117, 119, 406, 126, 123, 122])
                (.split 51
                    (.cell 42 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 140, 139, 141, 409, 148, 144, 143, 152])
                    (.split 52
                        (.cell 7 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178, 169, 168, 170, 414, 197, 173, 175, 172, 177, 176])
                        (.absurd 415))))
            (.absurd 429))
        (.absurd 426))

theorem treePart35_check :
    treePart35.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[2] - length[3]` in the row-03 length cone, with leaves
selecting cells 58 and Farkas receipts excluding inconsistent sign branches. -/
def treePart36 : CompactCellTree :=
  .split 15
    (.cell 58 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446])
    (.absurd 447)

theorem treePart36_check :
    treePart36.check splitForms farkasReceipts cells ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[5] - length[11]` in the row-03 length cone, with
leaves selecting cells 2, 15, 25, 29 and Farkas receipts excluding inconsistent sign branches. -/
def treePart37 : CompactCellTree :=
  .split 5
    (.split 15
        (.cell 2 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 57, 51, 52, 53, 181, 55, 56, 54, 448, 59])
        (.absurd 449))
    (.split 9
        (.split 10
            (.split 15
                (.cell 15 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 94, 95, 97, 225, 99, 100, 98, 450])
                (.absurd 451))
            (.absurd 405))
        (.split 10
            (.split 24
                (.split 15
                    (.split 13
                        (.cell 25 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 319, 141, 146, 145, 144, 148, 143, 147, 152])
                        (.split 44
                            (.cell 29 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 354, 170, 178, 174, 173, 197, 355, 176, 356, 172])
                            (.absurd 415)))
                    (.absurd 452))
                (.absurd 308))
            (.absurd 405)))

theorem treePart37_check :
    treePart37.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[11]` in the row-03 length cone, with leaves
selecting cells 4, 6, 8, 15 and Farkas receipts excluding inconsistent sign branches. -/
def treePart38 : CompactCellTree :=
  .split 19
    (.split 18
        (.split 15
            (.cell 4 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 94, 96, 97, 225, 99, 100, 98, 95])
            (.absurd 451))
        (.split 15
            (.split 53
                (.cell 15 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 120, 122, 125, 121, 119, 123, 126, 124])
                (.absurd 412))
            (.absurd 451)))
    (.split 40
        (.split 18
            (.split 11
                (.split 15
                    (.cell 6 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 141, 140, 145, 146, 143, 144, 148, 139, 147, 152])
                    (.absurd 453))
                (.absurd 407))
            (.absurd 425))
        (.split 18
            (.split 11
                (.split 15
                    (.split 22
                        (.cell 8 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 170, 169, 174, 178, 172, 173, 197, 175, 176, 177, 168])
                        (.absurd 230))
                    (.absurd 453))
                (.absurd 407))
            (.absurd 425)))

theorem treePart38_check :
    treePart38.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 6, 8, 25, 29 and Farkas receipts excluding inconsistent sign branches. -/
def treePart39 : CompactCellTree :=
  .split 10
    (.split 24
        (.split 15
            (.split 13
                (.cell 25 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 273, 117, 120, 119, 123, 126, 122, 125, 121])
                (.split 44
                    (.cell 29 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 319, 139, 142, 141, 144, 148, 320, 143, 321, 145])
                    (.absurd 149)))
            (.absurd 451))
        (.absurd 333))
    (.split 19
        (.absurd 426)
        (.split 11
            (.split 16
                (.absurd 454)
                (.split 15
                    (.split 40
                        (.cell 6 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178, 169, 170, 315, 172, 173, 197, 176, 196, 187])
                        (.split 22
                            (.cell 8 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 235, 211, 212, 455, 216, 215, 237, 217, 218, 219, 220])
                            (.absurd 456)))
                    (.absurd 453)))
            (.absurd 429)))

theorem treePart39_check :
    treePart39.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[6] + length[8]` in the row-03 length cone, with
leaves selecting cells 8, 36, 37, 43 and Farkas receipts excluding inconsistent sign branches. -/
def treePart40 : CompactCellTree :=
  .split 16
    (.split 49
        (.split 15
            (.cell 37 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 75, 457, 73, 80, 78, 79, 77, 404, 74])
            (.absurd 458))
        (.split 18
            (.split 15
                (.cell 36 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 95, 94, 100, 225, 99, 98, 450])
                (.absurd 451))
            (.absurd 459)))
    (.split 51
        (.split 49
            (.absurd 460)
            (.split 18
                (.split 12
                    (.split 15
                        (.cell 43 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 141, 140, 142, 145, 143, 144, 148, 146, 152])
                        (.absurd 453))
                    (.absurd 227))
                (.absurd 461)))
        (.split 49
            (.absurd 448)
            (.split 18
                (.split 12
                    (.split 15
                        (.split 52
                            (.cell 8 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 170, 169, 171, 174, 172, 173, 197, 175, 178, 177, 176])
                            (.absurd 462))
                        (.absurd 453))
                    (.absurd 227))
                (.absurd 463))))

theorem treePart40_check :
    treePart40.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 8, 27, 36, 38, 43 and Farkas receipts excluding inconsistent sign branches. -/
def treePart41 : CompactCellTree :=
  .split 10
    (.split 16
        (.split 15
            (.cell 38 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 100, 225, 99, 98, 313])
            (.absurd 451))
        (.absurd 426))
    (.split 11
        (.split 12
            (.split 16
                (.split 15
                    (.cell 27 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 418, 140, 139, 141, 143, 144, 148, 145])
                    (.absurd 453))
                (.split 15
                    (.split 51
                        (.cell 43 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 419, 169, 168, 170, 172, 173, 197, 176, 187])
                        (.split 52
                            (.cell 8 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 464, 211, 210, 212, 216, 215, 237, 217, 220, 219, 218])
                            (.absurd 456)))
                    (.absurd 453)))
            (.absurd 103))
        (.split 15
            (.split 47
                (.cell 36 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 117, 122, 123, 121, 119, 126, 120])
                (.absurd 465))
            (.absurd 451)))

theorem treePart41_check :
    treePart41.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 8, 41, 43 and Farkas receipts excluding inconsistent sign branches. -/
def treePart42 : CompactCellTree :=
  .split 10
    (.split 27
        (.split 15
            (.cell 41 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 273, 120, 119, 122, 123, 126, 124, 121])
            (.absurd 452))
        (.absurd 224))
    (.split 11
        (.split 12
            (.split 16
                (.absurd 427)
                (.split 15
                    (.split 51
                        (.cell 43 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 276, 220, 215, 237, 218, 466])
                        (.split 52
                            (.cell 8 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 253, 251, 267, 277, 254, 255, 282, 257, 260, 259, 258])
                            (.absurd 467)))
                    (.absurd 468)))
            (.absurd 420))
        (.absurd 417))

theorem treePart42_check :
    treePart42.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 8, 29, 43 and Farkas receipts excluding inconsistent sign branches. -/
def treePart43 : CompactCellTree :=
  .split 10
    (.split 27
        (.split 15
            (.split 50
                (.cell 29 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 319, 142, 141, 145, 144, 148, 320, 146, 321, 143])
                (.absurd 279))
            (.absurd 452))
        (.absurd 224))
    (.split 11
        (.split 12
            (.split 16
                (.absurd 427)
                (.split 15
                    (.split 51
                        (.cell 43 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 276, 220, 215, 237, 218, 466])
                        (.split 52
                            (.cell 8 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 253, 251, 267, 277, 254, 255, 282, 257, 469, 259, 258])
                            (.absurd 470)))
                    (.absurd 468)))
            (.absurd 420))
        (.absurd 417))

theorem treePart43_check :
    treePart43.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Leaf selecting row-03 cell 59, with 17 Farkas receipts deriving its cone inequalities from
the active branch constraints. -/
def treePart44 : CompactCellTree :=
  .cell 59 [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 400, 399]

theorem treePart44_check :
    treePart44.check splitForms farkasReceipts cells ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[5] - length[11]` in the row-03 length cone, with
leaves selecting cells 9, 18, 22, 30 and Farkas receipts excluding inconsistent sign branches. -/
def treePart45 : CompactCellTree :=
  .split 5
    (.cell 9 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 55, 51, 57, 53, 52, 54, 56, 471, 183, 181])
    (.split 9
        (.split 10
            (.cell 18 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 99, 101, 94, 97, 96, 98, 100, 411, 225])
            (.absurd 425))
        (.split 10
            (.split 24
                (.split 13
                    (.cell 22 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 141, 319, 145, 139, 148, 144, 409, 143, 147, 185])
                    (.split 44
                        (.cell 30 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 170, 354, 174, 168, 197, 173, 414, 355, 176, 356, 172])
                        (.absurd 262)))
                (.absurd 412))
            (.absurd 425)))

theorem treePart45_check :
    treePart45.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[1]` in the row-03 length cone, with leaves
selecting cells 10, 18, 22, 30 and Farkas receipts excluding inconsistent sign branches. -/
def treePart46 : CompactCellTree :=
  .split 18
    (.split 9
        (.cell 10 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 78, 74, 76, 75, 77, 80, 403, 308])
        (.absurd 472))
    (.split 9
        (.split 53
            (.cell 18 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 101, 99, 97, 96, 98, 100, 411, 225])
            (.absurd 425))
        (.split 13
            (.split 24
                (.cell 22 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 273, 122, 117, 126, 123, 406, 119, 125, 184])
                (.absurd 412))
            (.split 24
                (.split 44
                    (.cell 30 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 319, 145, 139, 148, 144, 409, 320, 143, 321, 141])
                    (.absurd 265))
                (.absurd 473))))

theorem treePart46_check :
    treePart46.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5] - length[6] + length[8]` in the row-03 length
cone, with leaves selecting cells 48, 49 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart47 : CompactCellTree :=
  .split 49
    (.cell 49 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 57, 474, 55, 56, 52, 54, 471, 448, 183])
    (.split 18
        (.split 16
            (.cell 48 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 99, 94, 100, 96, 98, 411, 475])
            (.absurd 476))
        (.absurd 426))

theorem treePart47_check :
    treePart47.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[6] + length[8]` in the row-03 length cone, with
leaves selecting cells 11, 30, 48, 50, 51, 52 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart48 : CompactCellTree :=
  .split 17
    (.split 10
        (.split 16
            (.cell 50 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 94, 95, 100, 96, 98, 411, 477])
            (.absurd 476))
        (.split 12
            (.split 16
                (.split 11
                    (.cell 11 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 478, 140, 143, 141, 148, 144, 409, 145])
                    (.split 47
                        (.cell 48 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 174, 176, 173, 479, 197, 414, 178])
                        (.absurd 418)))
                (.absurd 480))
            (.split 16
                (.split 47
                    (.cell 48 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 145, 143, 144, 185, 148, 409, 146])
                    (.absurd 427))
                (.absurd 481))))
    (.split 10
        (.split 27
            (.split 9
                (.cell 51 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 273, 124, 119, 126, 123, 406, 122])
                (.split 21
                    (.cell 52 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 319, 146, 141, 148, 144, 409, 143, 185])
                    (.split 50
                        (.cell 30 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 354, 178, 170, 197, 173, 414, 355, 172, 356, 176])
                        (.absurd 262))))
            (.absurd 428))
        (.absurd 482))

theorem treePart48_check :
    treePart48.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[1]` in the row-03 length cone, with leaves
selecting cells 11, 30, 51, 52, 54 and Farkas receipts excluding inconsistent sign branches. -/
def treePart49 : CompactCellTree :=
  .split 18
    (.cell 11 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 55, 483, 52, 181, 54, 56, 471, 57])
    (.split 24
        (.split 27
            (.split 9
                (.cell 51 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 427, 273, 117, 119, 126, 123, 406, 122])
                (.split 17
                    (.cell 54 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 418, 319, 139, 141, 148, 144, 409, 143])
                    (.split 44
                        (.split 50
                            (.cell 30 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 464, 366, 210, 212, 237, 215, 484, 367, 220, 368, 218])
                            (.absurd 485))
                        (.split 54
                            (.cell 52 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 464, 366, 210, 212, 237, 215, 484, 220, 218])
                            (.absurd 486)))))
            (.absurd 308))
        (.absurd 459))

theorem treePart49_check :
    treePart49.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[1]` in the row-03 length cone, with leaves
selecting cells 12, 13, 22, 30, 51, 54 and Farkas receipts excluding inconsistent sign branches. -/
def treePart50 : CompactCellTree :=
  .split 18
    (.split 52
        (.cell 13 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 359, 96, 487, 98, 100, 411, 360, 94, 361, 99])
        (.split 4
            (.cell 12 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 184, 121, 126, 123, 406, 119, 125, 122])
            (.absurd 410)))
    (.split 24
        (.split 27
            (.split 9
                (.cell 51 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 319, 141, 145, 148, 144, 409, 143])
                (.split 17
                    (.cell 54 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 354, 170, 174, 197, 173, 414, 176])
                    (.split 44
                        (.split 50
                            (.cell 30 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 253, 488, 267, 277, 282, 255, 489, 490, 260, 491, 258])
                            (.split 4
                                (.cell 22 [283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 297, 492, 298, 301, 493, 300, 494, 305, 495, 303])
                                (.absurd 496)))
                        (.absurd 497))))
            (.absurd 311))
        (.absurd 417))

theorem treePart50_check :
    treePart50.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[1]` in the row-03 length cone, with leaves
selecting cells 12, 22, 30, 51, 52, 53, 54 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart51 : CompactCellTree :=
  .split 18
    (.split 54
        (.cell 53 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 359, 96, 481, 98, 100, 411, 94, 99])
        (.split 40
            (.cell 12 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 184, 121, 126, 123, 406, 122, 125, 119])
            (.absurd 410)))
    (.split 24
        (.split 27
            (.split 9
                (.cell 51 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 319, 141, 145, 148, 144, 409, 143])
                (.split 17
                    (.cell 54 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 354, 170, 174, 197, 173, 414, 176])
                    (.split 44
                        (.split 50
                            (.cell 30 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 253, 488, 267, 277, 282, 255, 489, 490, 260, 491, 258])
                            (.split 4
                                (.cell 22 [283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 297, 492, 298, 301, 493, 300, 494, 305, 495, 303])
                                (.absurd 498)))
                        (.split 54
                            (.cell 52 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 253, 488, 267, 277, 282, 255, 489, 260, 258])
                            (.split 13
                                (.cell 22 [283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 297, 492, 298, 301, 493, 300, 494, 303, 495, 305])
                                (.absurd 498))))))
            (.absurd 311))
        (.absurd 417))

theorem treePart51_check :
    treePart51.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5] - length[11]` in the row-03 length cone, with
leaves selecting cells 48, 49 and Farkas receipts excluding inconsistent sign branches. -/
def treePart52 : CompactCellTree :=
  .split 7
    (.absurd 499)
    (.split 54
        (.split 47
            (.split 18
                (.split 17
                    (.cell 48 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 500, 185, 141, 144, 139, 148, 409, 501])
                    (.absurd 502))
                (.absurd 473))
            (.split 20
                (.cell 49 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 427, 503, 119, 123, 117, 126, 406, 504, 184])
                (.absurd 505)))
        (.absurd 506))

theorem treePart52_check :
    treePart52.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 30, 49, 50, 51, 52, 54 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart53 : CompactCellTree :=
  .split 24
    (.split 27
        (.split 9
            (.cell 51 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 273, 117, 119, 126, 123, 406, 122])
            (.split 17
                (.cell 54 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 319, 139, 141, 148, 144, 409, 143])
                (.split 44
                    (.split 50
                        (.cell 30 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 235, 366, 210, 212, 237, 215, 484, 367, 220, 368, 218])
                        (.absurd 507))
                    (.split 54
                        (.cell 52 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 235, 366, 210, 212, 237, 215, 484, 220, 218])
                        (.absurd 508)))))
        (.absurd 308))
    (.split 54
        (.split 48
            (.cell 50 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 117, 122, 123, 119, 126, 406, 184])
            (.split 49
                (.cell 49 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 145, 340, 143, 144, 141, 148, 409, 139, 509])
                (.absurd 510)))
        (.absurd 476))

theorem treePart53_check :
    treePart53.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[1] - length[5] + length[11]` in the row-03 length cone, with
leaves selecting cells 13, 48, 49, 60 and Farkas receipts excluding inconsistent sign branches. -/
def treePart54 : CompactCellTree :=
  .split 52
    (.split 47
        (.split 22
            (.cell 13 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 118, 511, 512, 126, 123, 406, 362, 122, 363, 117])
            (.split 54
                (.split 17
                    (.cell 48 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178, 186, 170, 173, 172, 197, 414, 176])
                    (.absurd 513))
                (.absurd 222)))
        (.split 22
            (.cell 13 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 118, 514, 512, 126, 123, 406, 362, 122, 363, 117])
            (.split 54
                (.split 20
                    (.cell 49 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 176, 348, 170, 173, 172, 197, 414, 515, 186])
                    (.absurd 516))
                (.absurd 517))))
    (.split 47
        (.split 54
            (.split 4
                (.cell 60 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 185, 141, 144, 145, 148, 409, 518, 152, 147, 143])
                (.split 17
                    (.cell 48 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178, 186, 170, 173, 174, 197, 414, 176])
                    (.absurd 513)))
            (.absurd 480))
        (.split 54
            (.split 20
                (.cell 49 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 143, 340, 141, 144, 145, 148, 409, 509, 185])
                (.absurd 519))
            (.absurd 520)))

theorem treePart54_check :
    treePart54.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[3] + length[7]` in the row-03 length cone, with leaves
selecting cells 58 and Farkas receipts excluding inconsistent sign branches. -/
def treePart55 : CompactCellTree :=
  .split 41
    (.cell 58 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 446, 445])
    (.absurd 447)

theorem treePart55_check :
    treePart55.check splitForms farkasReceipts cells ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5] - length[11]` in the row-03 length cone, with
leaves selecting cells 2, 4, 6, 8 and Farkas receipts excluding inconsistent sign branches. -/
def treePart56 : CompactCellTree :=
  .split 7
    (.split 41
        (.cell 2 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 191, 73, 76, 78, 77, 80, 79, 75, 521])
        (.absurd 458))
    (.split 18
        (.split 19
            (.split 41
                (.cell 4 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 119, 124, 125, 121, 126, 123, 122, 184])
                (.absurd 452))
            (.split 11
                (.split 16
                    (.absurd 522)
                    (.split 41
                        (.split 40
                            (.cell 6 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 276, 212, 237, 215, 220, 218, 236, 466])
                            (.split 22
                                (.cell 8 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 253, 251, 277, 267, 282, 255, 254, 257, 258, 259, 260])
                                (.absurd 467)))
                        (.absurd 468)))
                (.absurd 523)))
        (.absurd 426))

theorem treePart56_check :
    treePart56.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 4, 6, 8, 15, 17, 27 and Farkas receipts excluding inconsistent sign branches. -/
def treePart57 : CompactCellTree :=
  .split 10
    (.split 19
        (.split 41
            (.cell 15 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 96, 95, 97, 225, 98, 100, 99, 465])
            (.absurd 451))
        (.absurd 459))
    (.split 11
        (.split 12
            (.split 41
                (.split 19
                    (.cell 17 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 268, 140, 139, 141, 148, 144, 145, 185, 143, 147, 152])
                    (.split 16
                        (.cell 27 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 524, 169, 168, 170, 197, 173, 174, 176])
                        (.split 40
                            (.cell 6 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 525, 211, 210, 212, 237, 215, 276, 218, 236, 466])
                            (.split 22
                                (.cell 8 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 526, 251, 253, 267, 282, 255, 277, 257, 258, 259, 260])
                                (.absurd 467)))))
                (.absurd 452))
            (.split 42
                (.split 41
                    (.cell 4 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 141, 145, 147, 152, 148, 144, 143, 185])
                    (.absurd 453))
                (.absurd 313)))
        (.split 12
            (.absurd 103)
            (.split 42
                (.split 41
                    (.cell 4 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 230, 145, 147, 152, 148, 144, 143, 185])
                    (.absurd 453))
                (.absurd 313))))

theorem treePart57_check :
    treePart57.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 6, 8, 25, 26, 27 and Farkas receipts excluding inconsistent sign branches. -/
def treePart58 : CompactCellTree :=
  .split 10
    (.split 24
        (.split 41
            (.cell 25 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 272, 101, 96, 98, 100, 99, 95, 97, 225])
            (.absurd 451))
        (.absurd 506))
    (.split 22
        (.split 12
            (.split 41
                (.split 52
                    (.cell 8 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 527, 140, 528, 141, 148, 144, 145, 153, 139, 154, 143])
                    (.cell 6 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 140, 528, 141, 148, 144, 145, 143, 147, 152]))
                (.absurd 452))
            (.absurd 428))
        (.split 5
            (.absurd 529)
            (.split 11
                (.split 12
                    (.split 41
                        (.split 19
                            (.cell 26 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 235, 211, 276, 216, 237, 215, 220, 218, 236, 466])
                            (.split 16
                                (.cell 27 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 252, 251, 277, 256, 282, 255, 254, 258])
                                (.split 40
                                    (.cell 6 [283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 301, 530, 493, 300, 329, 303, 495, 531])
                                    (.absurd 250))))
                        (.absurd 468))
                    (.absurd 532))
                (.absurd 533))))

theorem treePart58_check :
    treePart58.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 6, 8, 26, 27, 29 and Farkas receipts excluding inconsistent sign branches. -/
def treePart59 : CompactCellTree :=
  .split 10
    (.split 24
        (.split 41
            (.split 44
                (.cell 29 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 273, 117, 184, 126, 123, 119, 316, 122, 317, 120])
                (.absurd 227))
            (.absurd 451))
        (.absurd 506))
    (.split 5
        (.absurd 59)
        (.split 11
            (.split 12
                (.split 41
                    (.split 19
                        (.cell 26 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178, 169, 170, 174, 197, 173, 172, 176, 196, 187])
                        (.split 16
                            (.cell 27 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 235, 211, 212, 276, 237, 215, 216, 218])
                            (.split 40
                                (.cell 6 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 252, 251, 267, 277, 282, 255, 256, 258, 281, 534])
                                (.split 22
                                    (.cell 8 [283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 298, 301, 493, 300, 530, 302, 303, 304, 535])
                                    (.absurd 536)))))
                    (.absurd 453))
                (.absurd 465))
            (.absurd 537)))

theorem treePart59_check :
    treePart59.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5] - length[6] + length[8]` in the row-03 length
cone, with leaves selecting cells 8, 36, 37, 43 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart60 : CompactCellTree :=
  .split 49
    (.split 41
        (.cell 37 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 52, 474, 57, 56, 181, 54, 55, 59, 448])
        (.absurd 449))
    (.split 16
        (.split 18
            (.split 41
                (.cell 36 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 94, 95, 100, 225, 98, 99, 450])
                (.absurd 451))
            (.absurd 405))
        (.split 18
            (.split 12
                (.split 41
                    (.split 51
                        (.cell 43 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 146, 141, 148, 144, 145, 143, 152])
                        (.split 52
                            (.cell 8 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 178, 170, 197, 173, 174, 175, 172, 177, 176])
                            (.absurd 415)))
                    (.absurd 452))
                (.absurd 308))
            (.absurd 405)))

theorem treePart60_check :
    treePart60.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 8, 27, 36, 38, 43 and Farkas receipts excluding inconsistent sign branches. -/
def treePart61 : CompactCellTree :=
  .split 10
    (.split 16
        (.split 41
            (.cell 38 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 100, 225, 98, 99, 313])
            (.absurd 451))
        (.absurd 426))
    (.split 12
        (.split 16
            (.split 41
                (.split 11
                    (.cell 27 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 527, 140, 143, 139, 148, 144, 145, 141])
                    (.split 47
                        (.cell 36 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178, 170, 176, 173, 538, 197, 174, 171])
                        (.absurd 513)))
                (.absurd 452))
            (.split 41
                (.split 51
                    (.cell 43 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 140, 141, 139, 148, 144, 145, 143, 152])
                    (.split 52
                        (.cell 8 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178, 169, 170, 168, 197, 173, 174, 175, 172, 177, 176])
                        (.absurd 415)))
                (.absurd 452)))
        (.split 16
            (.split 47
                (.split 41
                    (.cell 36 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 141, 145, 144, 152, 148, 143, 142])
                    (.absurd 453))
                (.absurd 465))
            (.absurd 103)))

theorem treePart61_check :
    treePart61.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 8, 27, 41, 43 and Farkas receipts excluding inconsistent sign branches. -/
def treePart62 : CompactCellTree :=
  .split 10
    (.split 27
        (.split 41
            (.cell 41 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 273, 120, 119, 126, 123, 122, 124, 121])
            (.absurd 452))
        (.absurd 224))
    (.split 11
        (.split 12
            (.split 41
                (.split 16
                    (.cell 27 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 174, 197, 173, 172, 176])
                    (.split 51
                        (.cell 43 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 276, 237, 215, 216, 218, 466])
                        (.split 52
                            (.cell 8 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 253, 251, 267, 277, 282, 255, 256, 257, 260, 259, 258])
                            (.absurd 467))))
                (.absurd 453))
            (.absurd 420))
        (.absurd 417))

theorem treePart62_check :
    treePart62.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 8, 29, 43 and Farkas receipts excluding inconsistent sign branches. -/
def treePart63 : CompactCellTree :=
  .split 10
    (.split 27
        (.split 41
            (.split 50
                (.cell 29 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 319, 142, 141, 148, 144, 145, 320, 146, 321, 143])
                (.absurd 279))
            (.absurd 452))
        (.absurd 539))
    (.split 11
        (.split 12
            (.split 16
                (.absurd 540)
                (.split 41
                    (.split 51
                        (.cell 43 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 276, 237, 215, 220, 218, 466])
                        (.split 52
                            (.cell 8 [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 253, 251, 267, 277, 282, 255, 254, 257, 469, 259, 258])
                            (.absurd 470)))
                    (.absurd 468)))
            (.absurd 541))
        (.absurd 542))

theorem treePart63_check :
    treePart63.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[6] + length[8]` in the row-03 length cone, with leaves
selecting cells 1, 2, 9, 61 and Farkas receipts excluding inconsistent sign branches. -/
def treePart64 : CompactCellTree :=
  .split 3
    (.cell 61 [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 400, 543, 399, 544, 545, 396, 398, 397])
    (.split 6
        (.split 14
            (.cell 1 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567])
            (.split 15
                (.cell 2 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 32, 29, 401, 31, 568, 34, 35, 30, 569, 570])
                (.absurd 371)))
        (.split 8
            (.cell 9 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 564, 565, 563, 566, 567])
            (.split 41
                (.cell 2 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 32, 29, 401, 31, 568, 30, 35, 34, 569, 570])
                (.absurd 371))))

theorem treePart64_check :
    treePart64.check splitForms farkasReceipts cells (((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Leaf selecting row-03 cell 62, with 17 Farkas receipts deriving its cone inequalities from
the active branch constraints. -/
def treePart65 : CompactCellTree :=
  .cell 62 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 444, 571, 445, 442, 443]

theorem treePart65_check :
    treePart65.check splitForms farkasReceipts cells (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 14, 15, 18 and Farkas receipts excluding inconsistent sign branches. -/
def treePart66 : CompactCellTree :=
  .split 10
    (.split 6
        (.split 14
            (.cell 14 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 77, 76, 337, 73, 79, 80, 572])
            (.split 15
                (.cell 15 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 98, 97, 346, 99, 100, 101, 573])
                (.absurd 416)))
        (.split 8
            (.cell 18 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 77, 76, 337, 79, 80, 73, 572])
            (.split 41
                (.cell 15 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 98, 97, 346, 101, 100, 99, 573])
                (.absurd 416))))
    (.absurd 574)

theorem treePart66_check :
    treePart66.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] + length[5] - length[11]` in the row-03 length cone, with
leaves selecting cells 21, 22, 25, 28, 29, 30 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart67 : CompactCellTree :=
  .split 13
    (.split 6
        (.split 14
            (.cell 21 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 273, 124, 184, 119, 122, 123, 117, 125, 575])
            (.split 15
                (.cell 25 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 319, 146, 185, 143, 144, 145, 139, 147, 576])
                (.absurd 342)))
        (.split 8
            (.cell 22 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 273, 124, 184, 122, 123, 119, 117, 125, 575])
            (.split 41
                (.cell 25 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 319, 146, 185, 145, 144, 143, 139, 147, 576])
                (.absurd 342))))
    (.split 6
        (.split 14
            (.split 44
                (.cell 28 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 319, 146, 185, 141, 145, 144, 320, 143, 321, 139])
                (.absurd 577))
            (.split 15
                (.split 44
                    (.cell 29 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 171, 354, 178, 186, 172, 173, 174, 355, 176, 356, 168])
                    (.absurd 578))
                (.absurd 342)))
        (.split 8
            (.split 44
                (.cell 30 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 319, 146, 185, 145, 144, 141, 320, 143, 321, 139])
                (.absurd 577))
            (.split 41
                (.split 44
                    (.cell 29 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 171, 354, 178, 186, 174, 173, 172, 355, 176, 356, 168])
                    (.absurd 578))
                (.absurd 342))))

theorem treePart67_check :
    treePart67.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 579 to exclude the accumulated affine constraints in
this row-03 branch. -/
def treePart68 : CompactCellTree :=
  .absurd 579

theorem treePart68_check :
    treePart68.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 580 to exclude the accumulated affine constraints in
this row-03 branch. -/
def treePart69 : CompactCellTree :=
  .absurd 580

theorem treePart69_check :
    treePart69.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Leaf selecting row-03 cell 63, with 17 Farkas receipts deriving its cone inequalities from
the active branch constraints. -/
def treePart70 : CompactCellTree :=
  .cell 63 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 563, 581, 564, 582, 565]

theorem treePart70_check :
    treePart70.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[2] - length[7]` in the row-03 length cone, with leaves
selecting cells 14, 15, 18 and Farkas receipts excluding inconsistent sign branches. -/
def treePart71 : CompactCellTree :=
  .split 6
    (.split 14
        (.cell 14 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 74, 77, 76, 337, 73, 79, 80, 572])
        (.split 15
            (.cell 15 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 225, 95, 98, 97, 346, 99, 100, 101, 573])
            (.absurd 416)))
    (.split 8
        (.cell 18 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 74, 77, 76, 337, 79, 80, 73, 572])
        (.split 41
            (.cell 15 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 225, 95, 98, 97, 346, 101, 100, 99, 573])
            (.absurd 416)))

theorem treePart71_check :
    treePart71.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 21, 22, 25 and Farkas receipts excluding inconsistent sign branches. -/
def treePart72 : CompactCellTree :=
  .split 24
    (.split 6
        (.split 14
            (.cell 21 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 121, 273, 117, 120, 119, 122, 123, 124, 125, 575])
            (.split 15
                (.cell 25 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 152, 319, 139, 142, 143, 144, 145, 146, 147, 576])
                (.absurd 342)))
        (.split 8
            (.cell 22 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 121, 273, 117, 120, 122, 123, 119, 124, 125, 575])
            (.split 41
                (.cell 25 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 152, 319, 139, 142, 145, 144, 143, 146, 147, 576])
                (.absurd 342))))
    (.absurd 583)

theorem treePart72_check :
    treePart72.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 28, 29, 30 and Farkas receipts excluding inconsistent sign branches. -/
def treePart73 : CompactCellTree :=
  .split 24
    (.split 6
        (.split 14
            (.split 44
                (.cell 28 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 152, 319, 139, 142, 141, 145, 144, 320, 143, 321, 146])
                (.absurd 584))
            (.split 15
                (.split 44
                    (.cell 29 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 187, 354, 168, 171, 172, 173, 174, 355, 176, 356, 178])
                    (.absurd 585))
                (.absurd 342)))
        (.split 8
            (.split 44
                (.cell 30 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 152, 319, 139, 142, 145, 144, 141, 320, 143, 321, 146])
                (.absurd 584))
            (.split 41
                (.split 44
                    (.cell 29 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 187, 354, 168, 171, 174, 173, 172, 355, 176, 356, 178])
                    (.absurd 585))
                (.absurd 342))))
    (.absurd 586)

theorem treePart73_check :
    treePart73.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 447 to exclude the accumulated affine constraints in
this row-03 branch. -/
def treePart74 : CompactCellTree :=
  .absurd 447

theorem treePart74_check :
    treePart74.check splitForms farkasReceipts cells (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[6] + length[8]` in the row-03 length cone, with leaves
selecting cells 3, 4, 10, 64 and Farkas receipts excluding inconsistent sign branches. -/
def treePart75 : CompactCellTree :=
  .split 3
    (.cell 64 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 446, 444, 587, 588, 589, 442, 445, 443])
    (.split 14
        (.split 6
            (.split 9
                (.cell 3 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 54, 50, 471, 53, 590, 57, 52, 56, 591])
                (.absurd 592))
            (.split 9
                (.split 8
                    (.cell 10 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 77, 190, 403, 76, 337, 79, 80, 74, 593])
                    (.absurd 405))
                (.absurd 592)))
        (.split 9
            (.split 15
                (.cell 4 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 54, 50, 471, 53, 590, 55, 56, 52, 591])
                (.split 43
                    (.cell 10 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 77, 190, 403, 76, 337, 73, 80, 79, 593])
                    (.absurd 459)))
            (.absurd 594)))

theorem treePart75_check :
    treePart75.check splitForms farkasReceipts cells ((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Leaf selecting row-03 cell 65, with 19 Farkas receipts deriving its cone inequalities from
the active branch constraints. -/
def treePart76 : CompactCellTree :=
  .cell 65 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 595, 563, 596, 582, 564, 565]

theorem treePart76_check :
    treePart76.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[2] - length[7]` in the row-03 length cone, with leaves
selecting cells 5, 7, 11, 12, 13, 24 and Farkas receipts excluding inconsistent sign branches. -/
def treePart77 : CompactCellTree :=
  .split 6
    (.split 16
        (.cell 24 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 77, 358, 78, 190, 73, 74, 80, 79])
        (.split 40
            (.cell 5 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 98, 359, 225, 226, 94, 95, 100, 99, 97, 346])
            (.split 22
                (.cell 7 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 126, 118, 121, 339, 124, 120, 123, 362, 122, 363, 119])
                (.absurd 597))))
    (.split 8
        (.split 16
            (.cell 11 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 98, 359, 225, 226, 101, 100, 94, 99])
            (.split 40
                (.cell 12 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 126, 118, 121, 339, 117, 123, 124, 122, 125, 575])
                (.split 22
                    (.cell 13 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 140, 152, 341, 139, 144, 146, 153, 143, 154, 145])
                    (.absurd 598))))
        (.absurd 426))

theorem treePart77_check :
    treePart77.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[2] - length[3]` in the row-03 length cone, with leaves
selecting cells 6, 8, 11, 12, 13, 27 and Farkas receipts excluding inconsistent sign branches. -/
def treePart78 : CompactCellTree :=
  .split 15
    (.split 16
        (.cell 27 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 77, 358, 78, 190, 73, 80, 74, 79])
        (.split 40
            (.cell 6 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 98, 359, 225, 226, 94, 100, 95, 99, 97, 346])
            (.split 22
                (.cell 8 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 126, 118, 121, 339, 124, 123, 120, 362, 122, 363, 119])
                (.absurd 597))))
    (.split 43
        (.split 16
            (.cell 11 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 98, 359, 225, 226, 94, 100, 101, 99])
            (.split 40
                (.cell 12 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 126, 118, 121, 339, 124, 123, 117, 122, 125, 575])
                (.split 22
                    (.cell 13 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 140, 152, 341, 146, 144, 139, 153, 143, 154, 145])
                    (.absurd 598))))
        (.absurd 426))

theorem treePart78_check :
    treePart78.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 599 to exclude the accumulated affine constraints in
this row-03 branch. -/
def treePart79 : CompactCellTree :=
  .absurd 599

theorem treePart79_check :
    treePart79.check splitForms farkasReceipts cells (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Leaf selecting row-03 cell 63, with 17 Farkas receipts deriving its cone inequalities from
the active branch constraints. -/
def treePart80 : CompactCellTree :=
  .cell 63 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 446, 444, 445, 442, 443]

theorem treePart80_check :
    treePart80.check splitForms farkasReceipts cells (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[2] - length[7]` in the row-03 length cone, with leaves
selecting cells 14, 15, 18 and Farkas receipts excluding inconsistent sign branches. -/
def treePart81 : CompactCellTree :=
  .split 6
    (.split 14
        (.split 19
            (.cell 14 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 77, 75, 600, 76, 337, 74, 73, 80, 79])
            (.absurd 357))
        (.split 19
            (.split 15
                (.cell 15 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 98, 96, 601, 97, 346, 99, 100, 94, 101])
                (.absurd 425))
            (.absurd 357)))
    (.split 19
        (.split 8
            (.cell 18 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 77, 75, 600, 76, 337, 79, 80, 74, 73])
            (.split 41
                (.cell 15 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 98, 96, 601, 97, 346, 101, 100, 99, 94])
                (.absurd 417)))
        (.absurd 378))

theorem treePart81_check :
    treePart81.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[2] - length[7]` in the row-03 length cone, with leaves
selecting cells 21, 22, 25 and Farkas receipts excluding inconsistent sign branches. -/
def treePart82 : CompactCellTree :=
  .split 6
    (.split 14
        (.split 24
            (.cell 21 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 98, 272, 99, 96, 94, 101, 100, 95, 97, 346])
            (.absurd 602))
        (.split 24
            (.split 15
                (.cell 25 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 126, 273, 119, 184, 122, 123, 117, 120, 125, 575])
                (.absurd 477))
            (.absurd 602)))
    (.split 24
        (.split 8
            (.cell 22 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 98, 272, 101, 96, 99, 100, 94, 95, 97, 346])
            (.split 41
                (.cell 25 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 126, 273, 117, 184, 119, 123, 122, 120, 125, 575])
                (.absurd 410)))
        (.absurd 603))

theorem treePart82_check :
    treePart82.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 28, 29, 30 and Farkas receipts excluding inconsistent sign branches. -/
def treePart83 : CompactCellTree :=
  .split 24
    (.split 6
        (.split 14
            (.split 44
                (.cell 28 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 126, 273, 124, 604, 117, 119, 123, 316, 122, 317, 120])
                (.absurd 605))
            (.split 15
                (.split 44
                    (.cell 29 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 319, 146, 606, 145, 144, 141, 320, 143, 321, 142])
                    (.absurd 607))
                (.absurd 323)))
        (.split 8
            (.split 44
                (.cell 30 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 126, 273, 124, 604, 119, 123, 117, 316, 122, 317, 120])
                (.absurd 605))
            (.split 41
                (.split 44
                    (.cell 29 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 319, 146, 606, 141, 144, 145, 320, 143, 321, 142])
                    (.absurd 607))
                (.absurd 323))))
    (.absurd 608)

theorem treePart83_check :
    treePart83.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Leaf selecting row-03 cell 62, with 17 Farkas receipts deriving its cone inequalities from
the active branch constraints. -/
def treePart84 : CompactCellTree :=
  .cell 62 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 581, 563, 564, 582, 565]

theorem treePart84_check :
    treePart84.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[3] - length[7]` in the row-03 length cone, with leaves
selecting cells 21, 25, 28, 29, 40, 44 and Farkas receipts excluding inconsistent sign branches. -/
def treePart85 : CompactCellTree :=
  .split 14
    (.split 9
        (.cell 44 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 126, 273, 120, 124, 117, 119, 123, 122])
        (.split 13
            (.cell 21 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 319, 142, 146, 139, 141, 144, 143, 147, 576])
            (.split 44
                (.cell 28 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 197, 354, 171, 178, 168, 170, 173, 355, 176, 356, 172])
                (.absurd 609))))
    (.split 9
        (.split 15
            (.cell 40 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 319, 142, 146, 143, 144, 141, 145])
            (.absurd 610))
        (.split 15
            (.split 13
                (.cell 25 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 197, 354, 171, 178, 172, 173, 170, 176, 196, 611])
                (.split 44
                    (.cell 29 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 237, 366, 213, 235, 216, 215, 212, 367, 218, 368, 220])
                    (.absurd 612)))
            (.absurd 610)))

theorem treePart85_check :
    treePart85.check splitForms farkasReceipts cells (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[11]` in the row-03 length cone, with leaves
selecting cells 22, 25, 29, 30, 40, 51 and Farkas receipts excluding inconsistent sign branches. -/
def treePart86 : CompactCellTree :=
  .split 9
    (.split 8
        (.cell 51 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 126, 273, 120, 124, 122, 123, 117, 119])
        (.split 41
            (.cell 40 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 319, 142, 146, 145, 144, 143, 141])
            (.absurd 613)))
    (.split 8
        (.split 13
            (.cell 22 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 319, 142, 146, 145, 144, 139, 143, 147, 576])
            (.split 44
                (.cell 30 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 197, 354, 171, 178, 174, 173, 168, 355, 176, 356, 172])
                (.absurd 609)))
        (.split 13
            (.split 41
                (.cell 25 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 197, 354, 171, 178, 174, 173, 176, 172, 196, 611])
                (.absurd 614))
            (.split 41
                (.split 44
                    (.cell 29 [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 237, 366, 213, 235, 276, 215, 220, 367, 218, 368, 216])
                    (.absurd 615))
                (.absurd 614))))

theorem treePart86_check :
    treePart86.check splitForms farkasReceipts cells (((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[11]` in the row-03 length cone, with leaves
selecting cells 14, 15, 18 and Farkas receipts excluding inconsistent sign branches. -/
def treePart87 : CompactCellTree :=
  .split 19
    (.split 53
        (.split 6
            (.split 14
                (.cell 14 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 146, 141, 147, 576, 145, 143, 144, 139])
                (.split 15
                    (.cell 15 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 197, 178, 170, 196, 611, 176, 173, 172, 168])
                    (.absurd 349)))
            (.split 8
                (.cell 18 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 146, 141, 147, 576, 143, 144, 145, 139])
                (.split 41
                    (.cell 15 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 197, 178, 170, 196, 611, 172, 173, 176, 168])
                    (.absurd 349))))
        (.absurd 451))
    (.absurd 264)

theorem treePart87_check :
    treePart87.check splitForms farkasReceipts cells ((((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[11]` in the row-03 length cone, with leaves
selecting cells 14, 15, 18 and Farkas receipts excluding inconsistent sign branches. -/
def treePart88 : CompactCellTree :=
  .split 19
    (.split 9
        (.split 53
            (.split 6
                (.split 14
                    (.cell 14 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 139, 141, 147, 576, 145, 143, 144, 146])
                    (.split 15
                        (.cell 15 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 197, 168, 170, 196, 611, 176, 173, 172, 178])
                        (.absurd 349)))
                (.split 8
                    (.cell 18 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 148, 139, 141, 147, 576, 143, 144, 145, 146])
                    (.split 41
                        (.cell 15 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 197, 168, 170, 196, 611, 172, 173, 176, 178])
                        (.absurd 349))))
            (.absurd 451))
        (.absurd 583))
    (.absurd 616)

theorem treePart88_check :
    treePart88.check splitForms farkasReceipts cells (((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Contradiction leaf using Farkas receipt 617 to exclude the accumulated affine constraints in
this row-03 branch. -/
def treePart89 : CompactCellTree :=
  .absurd 617

theorem treePart89_check :
    treePart89.check splitForms farkasReceipts cells (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[5]` in the row-03 length cone, with leaves
selecting cells 62, 63, 66 and Farkas receipts excluding inconsistent sign branches. -/
def treePart90 : CompactCellTree :=
  .split 23
    (.split 26
        (.cell 62 [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 400, 398, 399, 396, 397])
        (.split 18
            (.cell 66 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 445, 444, 587, 442, 443])
            (.absurd 617)))
    (.split 10
        (.cell 63 [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 398, 400, 399, 396, 397])
        (.split 55
            (.cell 66 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 444, 445, 587, 442, 443])
            (.absurd 617)))

theorem treePart90_check :
    treePart90.check splitForms farkasReceipts cells ((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[3] - length[7]` in the row-03 length cone, with leaves
selecting cells 33, 34, 37, 38 and Farkas receipts excluding inconsistent sign branches. -/
def treePart91 : CompactCellTree :=
  .split 14
    (.split 48
        (.split 16
            (.cell 34 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 50, 57, 56, 590, 54, 52, 380])
            (.absurd 618))
        (.split 16
            (.split 49
                (.cell 33 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 457, 79, 80, 337, 77, 75, 190, 381])
                (.absurd 333))
            (.absurd 619)))
    (.split 16
        (.split 15
            (.split 48
                (.cell 38 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 190, 79, 80, 337, 73, 75, 381])
                (.split 49
                    (.cell 37 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 101, 620, 99, 100, 346, 94, 96, 226, 383])
                    (.absurd 103)))
            (.absurd 378))
        (.absurd 621))

theorem treePart91_check :
    treePart91.check splitForms farkasReceipts cells (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[6] + length[8]` in the row-03 length cone, with
leaves selecting cells 7, 8, 32, 36, 42, 43 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart92 : CompactCellTree :=
  .split 16
    (.split 14
        (.cell 32 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 180, 57, 59, 56, 590, 54, 55, 50])
        (.split 15
            (.cell 36 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 622, 74, 404, 80, 337, 79, 73, 190])
            (.absurd 264)))
    (.split 14
        (.split 12
            (.split 51
                (.cell 42 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 623, 359, 96, 101, 98, 94, 100, 99, 346])
                (.split 52
                    (.cell 7 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 624, 118, 184, 117, 126, 124, 123, 362, 119, 363, 122])
                    (.absurd 597)))
            (.absurd 603))
        (.split 12
            (.split 15
                (.split 51
                    (.cell 43 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 624, 118, 184, 117, 119, 123, 124, 122, 575])
                    (.split 52
                        (.cell 8 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 625, 140, 185, 139, 141, 144, 146, 153, 145, 154, 143])
                        (.absurd 598)))
                (.absurd 626))
            (.absurd 603)))

theorem treePart92_check :
    treePart92.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[3] - length[7]` in the row-03 length cone, with leaves
selecting cells 32, 33, 36, 37 and Farkas receipts excluding inconsistent sign branches. -/
def treePart93 : CompactCellTree :=
  .split 14
    (.split 47
        (.cell 32 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 52, 55, 56, 590, 54, 57, 50])
        (.split 20
            (.cell 33 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 79, 457, 73, 80, 337, 77, 74, 190, 75])
            (.absurd 472)))
    (.split 15
        (.split 47
            (.cell 36 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 75, 79, 80, 337, 73, 74, 190])
            (.split 20
                (.cell 37 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 99, 620, 101, 100, 346, 94, 95, 226, 96])
                (.absurd 103)))
        (.absurd 627))

theorem treePart93_check :
    treePart93.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 7, 24, 39, 42 and Farkas receipts excluding inconsistent sign branches. -/
def treePart94 : CompactCellTree :=
  .split 10
    (.split 27
        (.cell 39 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 57, 628, 50, 55, 54, 52, 56, 181, 590])
        (.absurd 629))
    (.split 11
        (.split 12
            (.split 16
                (.cell 24 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 359, 94, 101, 98, 96, 100, 99])
                (.split 51
                    (.cell 42 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 118, 124, 117, 126, 184, 123, 122, 575])
                    (.split 52
                        (.cell 7 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 140, 146, 139, 148, 185, 144, 153, 145, 154, 143])
                        (.absurd 598))))
            (.absurd 630))
        (.absurd 351))

theorem treePart94_check :
    treePart94.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 8, 41, 43 and Farkas receipts excluding inconsistent sign branches. -/
def treePart95 : CompactCellTree :=
  .split 10
    (.split 27
        (.split 15
            (.cell 41 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 631, 190, 73, 79, 80, 75, 78, 337])
            (.absurd 357))
        (.absurd 629))
    (.split 11
        (.split 12
            (.split 16
                (.absurd 263)
                (.split 15
                    (.split 51
                        (.cell 43 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 140, 146, 139, 145, 144, 185, 143, 576])
                        (.split 52
                            (.cell 8 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 171, 169, 178, 168, 174, 173, 186, 175, 172, 177, 176])
                            (.absurd 609)))
                    (.absurd 318)))
            (.absurd 630))
        (.absurd 351))

theorem treePart95_check :
    treePart95.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 7, 8, 28, 29, 42, 43 and Farkas receipts excluding inconsistent sign branches. -/
def treePart96 : CompactCellTree :=
  .split 10
    (.split 27
        (.split 14
            (.split 50
                (.cell 28 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 75, 631, 190, 74, 77, 73, 80, 632, 78, 633, 79])
                (.absurd 634))
            (.split 15
                (.split 50
                    (.cell 29 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 96, 272, 226, 95, 101, 100, 94, 635, 225, 636, 99])
                    (.absurd 637))
                (.absurd 264)))
        (.absurd 638))
    (.split 11
        (.split 12
            (.split 16
                (.absurd 639)
                (.split 14
                    (.split 51
                        (.cell 42 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 184, 118, 120, 124, 126, 119, 123, 122, 575])
                        (.split 52
                            (.cell 7 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 185, 140, 142, 146, 148, 141, 144, 153, 640, 154, 143])
                            (.absurd 641)))
                    (.split 15
                        (.split 51
                            (.cell 43 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 185, 140, 142, 146, 145, 144, 141, 143, 576])
                            (.split 52
                                (.cell 8 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 186, 169, 171, 178, 174, 173, 170, 175, 508, 177, 176])
                                (.absurd 642)))
                        (.absurd 232))))
            (.absurd 643))
        (.absurd 644))

theorem treePart96_check :
    treePart96.check splitForms farkasReceipts cells (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, 1, -1, 0, 1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 36, 37, 48, 49 and Farkas receipts excluding inconsistent sign branches. -/
def treePart97 : CompactCellTree :=
  .split 8
    (.split 47
        (.split 17
            (.cell 48 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 50, 57, 56, 590, 52, 54, 380])
            (.absurd 618))
        (.split 20
            (.cell 49 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 55, 474, 57, 56, 590, 52, 54, 380, 50])
            (.absurd 60)))
    (.split 47
        (.split 17
            (.split 41
                (.cell 36 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 190, 74, 80, 337, 75, 79, 381])
                (.absurd 357))
            (.absurd 618))
        (.split 20
            (.split 41
                (.cell 37 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 457, 74, 80, 337, 75, 79, 381, 190])
                (.absurd 357))
            (.absurd 60)))

theorem treePart97_check :
    treePart97.check splitForms farkasReceipts cells (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[6] + length[8]` in the row-03 length cone, with
leaves selecting cells 29, 30, 38, 40, 41, 50, 51, 52 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart98 : CompactCellTree :=
  .split 17
    (.split 8
        (.cell 50 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 180, 57, 59, 56, 590, 55, 54, 50])
        (.split 41
            (.cell 38 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 622, 74, 404, 80, 337, 73, 79, 190])
            (.absurd 264)))
    (.split 8
        (.split 27
            (.split 9
                (.cell 51 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 623, 272, 96, 101, 94, 100, 98, 99])
                (.split 21
                    (.cell 52 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 624, 273, 184, 117, 124, 123, 126, 122, 575])
                    (.split 50
                        (.cell 30 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 625, 319, 185, 139, 146, 144, 148, 320, 145, 321, 143])
                        (.absurd 598))))
            (.absurd 603))
        (.split 27
            (.split 41
                (.split 9
                    (.cell 40 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 624, 273, 184, 117, 124, 123, 119, 122])
                    (.split 21
                        (.cell 41 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 625, 319, 185, 139, 146, 144, 141, 143, 576])
                        (.split 50
                            (.cell 29 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 645, 354, 186, 168, 178, 173, 170, 355, 172, 356, 176])
                            (.absurd 609))))
                (.absurd 626))
            (.absurd 603)))

theorem treePart98_check :
    treePart98.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 37, 38, 49, 50 and Farkas receipts excluding inconsistent sign branches. -/
def treePart99 : CompactCellTree :=
  .split 8
    (.split 48
        (.cell 50 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 52, 55, 56, 590, 57, 54, 50])
        (.split 49
            (.cell 49 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 457, 79, 80, 337, 74, 77, 75, 190])
            (.absurd 472)))
    (.split 48
        (.split 41
            (.cell 38 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 75, 73, 80, 337, 74, 79, 190])
            (.absurd 376))
        (.split 49
            (.split 41
                (.cell 37 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 620, 101, 100, 346, 95, 99, 96, 226])
                (.absurd 150))
            (.absurd 472)))

theorem treePart99_check :
    treePart99.check splitForms farkasReceipts cells ((((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, -1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 8, 13, 43, 53 and Farkas receipts excluding inconsistent sign branches. -/
def treePart100 : CompactCellTree :=
  .split 8
    (.split 12
        (.split 51
            (.cell 53 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 483, 50, 57, 52, 56, 54, 55, 590])
            (.split 52
                (.cell 13 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 358, 190, 74, 75, 80, 77, 646, 73, 647, 79])
                (.absurd 648)))
        (.absurd 649))
    (.split 12
        (.split 41
            (.split 51
                (.cell 43 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 358, 190, 74, 75, 80, 73, 79, 337])
                (.split 52
                    (.cell 8 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 225, 359, 226, 95, 96, 100, 94, 360, 101, 361, 99])
                    (.absurd 650)))
            (.absurd 378))
        (.absurd 649))

theorem treePart100_check :
    treePart100.check splitForms farkasReceipts cells (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 29, 30, 41, 51, 52, 54 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart101 : CompactCellTree :=
  .split 24
    (.split 27
        (.split 8
            (.split 9
                (.cell 51 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 631, 75, 74, 73, 80, 77, 79])
                (.split 17
                    (.cell 54 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 225, 272, 96, 95, 94, 100, 98, 99])
                    (.split 21
                        (.cell 52 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 121, 273, 184, 120, 124, 123, 126, 122, 575])
                        (.split 50
                            (.cell 30 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 152, 319, 185, 142, 146, 144, 148, 320, 145, 321, 143])
                            (.absurd 598)))))
            (.split 9
                (.absurd 651)
                (.split 17
                    (.absurd 381)
                    (.split 21
                        (.split 41
                            (.cell 41 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 152, 319, 185, 142, 146, 144, 143, 145, 576])
                            (.absurd 155))
                        (.split 41
                            (.split 50
                                (.cell 29 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 187, 354, 186, 171, 178, 173, 172, 355, 174, 356, 176])
                                (.absurd 652))
                            (.absurd 155))))))
        (.absurd 653))
    (.absurd 654)

theorem treePart101_check :
    treePart101.check splitForms farkasReceipts cells (((((((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5]` in the row-03 length cone, with leaves
selecting cells 67, 68 and Farkas receipts excluding inconsistent sign branches. -/
def treePart102 : CompactCellTree :=
  .split 26
    (.cell 67 [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 545, 398, 655, 399, 656, 400, 657, 396, 658, 659])
    (.split 18
        (.cell 68 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 445, 444, 660, 587, 661, 446, 662, 442, 663, 664])
        (.absurd 599))

theorem treePart102_check :
    treePart102.check splitForms farkasReceipts cells (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[3] - length[11]` in the row-03 length cone, with leaves
selecting cells 69, 70, 71 and Farkas receipts excluding inconsistent sign branches. -/
def treePart103 : CompactCellTree :=
  .split 56
    (.split 15
        (.cell 69 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 562, 581, 665, 564, 563, 558, 666, 582, 667])
        (.absurd 668))
    (.split 57
        (.split 15
            (.split 58
                (.cell 70 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 590, 50, 669, 57, 670, 55, 181, 52, 671, 672])
                (.absurd 673))
            (.absurd 674))
        (.split 15
            (.split 58
                (.split 59
                    (.cell 71 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 337, 190, 675, 74, 676, 73, 78, 677, 79, 75, 678])
                    (.absurd 679))
                (.absurd 673))
            (.absurd 574)))

theorem treePart103_check :
    treePart103.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[3] - length[11]` in the row-03 length cone, with leaves
selecting cells 72, 73, 74 and Farkas receipts excluding inconsistent sign branches. -/
def treePart104 : CompactCellTree :=
  .split 56
    (.split 18
        (.split 15
            (.cell 72 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 28, 680, 34, 33, 32, 681, 682, 683])
            (.absurd 574))
        (.absurd 684))
    (.split 18
        (.split 15
            (.split 58
                (.split 57
                    (.cell 73 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 75, 190, 675, 74, 676, 73, 78, 79, 685, 336])
                    (.split 59
                        (.cell 74 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 96, 226, 686, 95, 687, 94, 225, 688, 99, 101, 689])
                        (.absurd 690)))
                (.absurd 673))
            (.absurd 574))
        (.absurd 684))

theorem treePart104_check :
    treePart104.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5]` in the row-03 length cone, with leaves
selecting cells 75, 76 and Farkas receipts excluding inconsistent sign branches. -/
def treePart105 : CompactCellTree :=
  .split 26
    (.split 56
        (.cell 75 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 562, 563, 665, 581, 558, 560, 666, 582, 594])
        (.absurd 691))
    (.split 18
        (.split 56
            (.cell 76 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 33, 680, 28, 32, 401, 681, 682, 592])
            (.absurd 594))
        (.absurd 692))

theorem treePart105_check :
    treePart105.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[3] - length[11]` in the row-03 length cone, with leaves
selecting cells 69, 70, 71, 72, 73, 74 and Farkas receipts excluding inconsistent sign branches. -/
def treePart106 : CompactCellTree :=
  .split 56
    (.split 26
        (.split 60
            (.cell 69 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 568, 30, 680, 28, 33, 34, 681, 682, 32])
            (.absurd 693))
        (.split 18
            (.split 60
                (.cell 72 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 57, 52, 669, 50, 181, 55, 671, 672, 54])
                (.absurd 694))
            (.absurd 695)))
    (.split 26
        (.split 57
            (.split 58
                (.cell 70 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 590, 52, 669, 50, 670, 55, 181, 57, 671, 672])
                (.absurd 673))
            (.split 58
                (.split 59
                    (.cell 71 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 337, 75, 675, 190, 676, 73, 78, 677, 79, 74, 678])
                    (.absurd 696))
                (.absurd 697)))
        (.split 18
            (.split 58
                (.split 57
                    (.cell 73 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 675, 190, 676, 73, 78, 79, 685, 336])
                    (.split 59
                        (.cell 74 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 686, 226, 687, 94, 225, 688, 99, 101, 689])
                        (.absurd 690)))
                (.absurd 673))
            (.absurd 695)))

theorem treePart106_check :
    treePart106.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 70, 71, 77, 78, 79 and Farkas receipts excluding inconsistent sign branches. -/
def treePart107 : CompactCellTree :=
  .split 8
    (.split 61
        (.cell 77 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 568, 28, 680, 30, 698, 34, 32, 33, 681, 682])
        (.absurd 699))
    (.split 59
        (.split 62
            (.split 38
                (.cell 71 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 337, 190, 675, 103, 676, 700, 73, 677, 74, 79, 678])
                (.cell 70 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 337, 190, 675, 75, 676, 700, 73, 79, 685, 336]))
            (.absurd 378))
        (.split 58
            (.split 63
                (.split 62
                    (.cell 78 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 346, 226, 686, 96, 687, 94, 477, 95, 101])
                    (.absurd 352))
                (.split 62
                    (.split 56
                        (.cell 79 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 575, 339, 701, 184, 702, 124, 119, 122])
                        (.split 57
                            (.cell 70 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 576, 341, 703, 185, 704, 146, 141, 143, 705, 706])
                            (.absurd 427)))
                    (.absurd 352)))
            (.absurd 707)))

theorem treePart107_check :
    treePart107.check splitForms farkasReceipts cells (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 70, 71, 79, 80 and Farkas receipts excluding inconsistent sign branches. -/
def treePart108 : CompactCellTree :=
  .split 8
    (.split 61
        (.split 64
            (.cell 80 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 590, 50, 669, 52, 708, 57, 54, 709, 55, 181, 710])
            (.absurd 673))
        (.absurd 699))
    (.split 58
        (.split 62
            (.split 56
                (.cell 79 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 337, 190, 675, 75, 676, 74, 73, 79])
                (.split 57
                    (.cell 70 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 346, 226, 686, 96, 687, 95, 94, 99, 711, 345])
                    (.split 59
                        (.cell 71 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 575, 339, 701, 184, 702, 120, 124, 712, 122, 222, 713])
                        (.absurd 714))))
            (.absurd 378))
        (.absurd 715))

theorem treePart108_check :
    treePart108.check splitForms farkasReceipts cells (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 73, 74, 81, 82 and Farkas receipts excluding inconsistent sign branches. -/
def treePart109 : CompactCellTree :=
  .split 8
    (.split 18
        (.split 61
            (.cell 81 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 57, 50, 669, 52, 708, 55, 54, 181, 671, 672])
            (.absurd 716))
        (.absurd 649))
    (.split 18
        (.split 58
            (.split 62
                (.split 56
                    (.cell 82 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 226, 686, 96, 687, 94, 101, 99])
                    (.split 57
                        (.cell 73 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 339, 701, 184, 702, 124, 117, 122, 717, 718])
                        (.split 59
                            (.cell 74 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 341, 703, 185, 704, 146, 139, 719, 143, 145, 720])
                            (.absurd 721))))
                (.absurd 357))
            (.absurd 707))
        (.absurd 649))

theorem treePart109_check :
    treePart109.check splitForms farkasReceipts cells (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[0] - length[1]` in the row-03 length cone, with leaves
selecting cells 73, 74, 82, 83 and Farkas receipts excluding inconsistent sign branches. -/
def treePart110 : CompactCellTree :=
  .split 18
    (.split 8
        (.split 61
            (.split 64
                (.cell 83 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 75, 190, 675, 74, 722, 73, 77, 723, 79, 78, 724])
                (.absurd 725))
            (.absurd 716))
        (.split 58
            (.split 62
                (.split 56
                    (.cell 82 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 96, 226, 686, 95, 687, 94, 101, 99])
                    (.split 57
                        (.cell 73 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 184, 339, 701, 120, 702, 124, 117, 122, 717, 718])
                        (.split 59
                            (.cell 74 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 185, 341, 703, 142, 704, 146, 139, 719, 143, 726, 720])
                            (.absurd 727))))
                (.absurd 376))
            (.absurd 728)))
    (.absurd 684)

theorem treePart110_check :
    treePart110.check splitForms farkasReceipts cells (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 68, 84 and Farkas receipts excluding inconsistent sign branches. -/
def treePart111 : CompactCellTree :=
  .split 10
    (.cell 84 [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 398, 545, 655, 399, 656, 400, 657, 396, 658, 659])
    (.split 55
        (.cell 68 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 444, 445, 660, 587, 661, 446, 662, 442, 663, 664])
        (.absurd 599))

theorem treePart111_check :
    treePart111.check splitForms farkasReceipts cells (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 72, 73, 74, 85, 86, 87 and Farkas receipts excluding inconsistent sign branches. -/
def treePart112 : CompactCellTree :=
  .split 10
    (.split 56
        (.split 15
            (.cell 85 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 581, 562, 665, 564, 563, 558, 666, 582, 667])
            (.absurd 668))
        (.split 15
            (.split 58
                (.split 57
                    (.cell 86 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 590, 669, 52, 670, 57, 181, 55, 671, 672])
                    (.split 59
                        (.cell 87 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 190, 337, 675, 75, 676, 74, 78, 677, 79, 73, 678])
                        (.absurd 729)))
                (.absurd 730))
            (.absurd 668)))
    (.split 55
        (.split 15
            (.split 56
                (.cell 72 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 33, 680, 30, 34, 32, 681, 682, 683])
                (.split 58
                    (.split 57
                        (.cell 73 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 190, 78, 675, 75, 676, 73, 74, 79, 685, 336])
                        (.split 59
                            (.cell 74 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 226, 225, 686, 96, 687, 94, 95, 688, 99, 101, 689])
                            (.absurd 690)))
                    (.absurd 731)))
            (.absurd 668))
        (.absurd 599))

theorem treePart112_check :
    treePart112.check splitForms farkasReceipts cells (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 76, 88 and Farkas receipts excluding inconsistent sign branches. -/
def treePart113 : CompactCellTree :=
  .split 10
    (.split 56
        (.cell 88 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 563, 562, 665, 581, 558, 560, 666, 582, 594])
        (.absurd 691))
    (.split 55
        (.split 56
            (.cell 76 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 33, 30, 680, 28, 32, 401, 681, 682, 592])
            (.absurd 594))
        (.absurd 692))

theorem treePart113_check :
    treePart113.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[3] - length[11]` in the row-03 length cone, with leaves
selecting cells 72, 73, 74, 85, 86, 87 and Farkas receipts excluding inconsistent sign branches. -/
def treePart114 : CompactCellTree :=
  .split 56
    (.split 10
        (.split 60
            (.cell 85 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 568, 680, 28, 33, 34, 681, 682, 32])
            (.absurd 693))
        (.split 55
            (.split 60
                (.cell 72 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 52, 57, 669, 50, 181, 55, 671, 672, 54])
                (.absurd 694))
            (.absurd 695)))
    (.split 10
        (.split 57
            (.split 58
                (.cell 86 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 52, 590, 669, 50, 670, 55, 181, 57, 671, 672])
                (.absurd 673))
            (.split 58
                (.split 59
                    (.cell 87 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 75, 337, 675, 190, 676, 73, 78, 677, 79, 74, 678])
                    (.absurd 696))
                (.absurd 697)))
        (.split 55
            (.split 58
                (.split 57
                    (.cell 73 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 75, 74, 675, 190, 676, 73, 78, 79, 685, 336])
                    (.split 59
                        (.cell 74 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 96, 95, 686, 226, 687, 94, 225, 688, 99, 101, 689])
                        (.absurd 690)))
                (.absurd 673))
            (.absurd 695)))

theorem treePart114_check :
    treePart114.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 86, 87, 89, 90 and Farkas receipts excluding inconsistent sign branches. -/
def treePart115 : CompactCellTree :=
  .split 8
    (.split 61
        (.cell 89 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 568, 680, 30, 698, 34, 32, 33, 681, 682])
        (.absurd 699))
    (.split 58
        (.split 62
            (.split 56
                (.cell 90 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 190, 337, 675, 75, 676, 74, 73, 79])
                (.split 57
                    (.cell 86 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 226, 346, 686, 96, 687, 95, 94, 99, 711, 345])
                    (.split 59
                        (.cell 87 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 339, 575, 701, 184, 702, 120, 124, 712, 122, 119, 713])
                        (.absurd 732))))
            (.absurd 378))
        (.absurd 715))

theorem treePart115_check :
    treePart115.check splitForms farkasReceipts cells (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 86, 87, 90, 91 and Farkas receipts excluding inconsistent sign branches. -/
def treePart116 : CompactCellTree :=
  .split 8
    (.split 61
        (.split 64
            (.cell 91 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 590, 669, 52, 708, 57, 54, 709, 55, 181, 710])
            (.absurd 673))
        (.absurd 699))
    (.split 58
        (.split 62
            (.split 56
                (.cell 90 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 190, 337, 675, 75, 676, 74, 73, 79])
                (.split 57
                    (.cell 86 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 226, 346, 686, 96, 687, 95, 94, 99, 711, 345])
                    (.split 59
                        (.cell 87 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 339, 575, 701, 184, 702, 120, 124, 712, 122, 222, 713])
                        (.absurd 714))))
            (.absurd 378))
        (.absurd 715))

theorem treePart116_check :
    treePart116.check splitForms farkasReceipts cells (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 73, 74, 81, 82, 83 and Farkas receipts excluding inconsistent sign branches. -/
def treePart117 : CompactCellTree :=
  .split 8
    (.split 32
        (.split 55
            (.split 61
                (.cell 81 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 57, 669, 181, 708, 55, 54, 52, 671, 672])
                (.absurd 716))
            (.absurd 649))
        (.split 55
            (.split 61
                (.split 64
                    (.cell 83 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 190, 74, 675, 78, 722, 73, 77, 723, 79, 75, 724])
                    (.absurd 679))
                (.absurd 716))
            (.absurd 649)))
    (.split 55
        (.split 58
            (.split 62
                (.split 56
                    (.cell 82 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 190, 75, 675, 78, 676, 74, 73, 79])
                    (.split 57
                        (.cell 73 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 226, 96, 686, 225, 687, 95, 94, 99, 711, 345])
                        (.split 59
                            (.cell 74 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 339, 184, 701, 121, 702, 120, 124, 712, 122, 119, 713])
                            (.absurd 732))))
                (.absurd 324))
            (.absurd 733))
        (.absurd 684))

theorem treePart117_check :
    treePart117.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1]]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5]` in the row-03 length cone, with leaves
selecting cells 92, 93 and Farkas receipts excluding inconsistent sign branches. -/
def treePart118 : CompactCellTree :=
  .split 26
    (.cell 92 [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 545, 398, 397, 399, 734, 400, 396, 658, 659])
    (.split 18
        (.cell 93 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 445, 444, 443, 587, 735, 446, 442, 663, 664])
        (.absurd 599))

theorem treePart118_check :
    treePart118.check splitForms farkasReceipts cells (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5]` in the row-03 length cone, with leaves
selecting cells 94, 95 and Farkas receipts excluding inconsistent sign branches. -/
def treePart119 : CompactCellTree :=
  .split 26
    (.split 15
        (.cell 94 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 562, 563, 565, 564, 581, 558, 582, 667])
        (.absurd 668))
    (.split 18
        (.split 15
            (.cell 95 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 33, 35, 34, 28, 32, 682, 683])
            (.absurd 574))
        (.absurd 692))

theorem treePart119_check :
    treePart119.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[3] + length[6] + length[7] - length[8]` in the row-03 length
cone, with leaves selecting cells 71, 74, 78, 96 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart120 : CompactCellTree :=
  .split 65
    (.split 26
        (.split 15
            (.split 62
                (.cell 78 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 590, 52, 56, 57, 670, 50, 55, 181, 672])
                (.absurd 736))
            (.absurd 737))
        (.split 18
            (.split 15
                (.split 62
                    (.cell 96 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 80, 73, 676, 190, 79, 78, 336])
                    (.absurd 738))
                (.absurd 739))
            (.absurd 695)))
    (.split 26
        (.split 15
            (.split 62
                (.split 38
                    (.cell 71 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 337, 75, 80, 74, 676, 190, 73, 677, 78, 79, 678])
                    (.absurd 725))
                (.absurd 736))
            (.absurd 574))
        (.split 18
            (.split 15
                (.split 62
                    (.split 38
                        (.cell 74 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 100, 94, 687, 226, 101, 688, 225, 99, 689])
                        (.absurd 740))
                    (.absurd 738))
                (.absurd 449))
            (.absurd 695)))

theorem treePart120_check :
    treePart120.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5]` in the row-03 length cone, with leaves
selecting cells 97, 98 and Farkas receipts excluding inconsistent sign branches. -/
def treePart121 : CompactCellTree :=
  .split 26
    (.split 35
        (.cell 97 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 562, 563, 565, 581, 558, 560, 582, 594])
        (.absurd 691))
    (.split 18
        (.split 35
            (.cell 98 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 33, 35, 28, 32, 401, 682, 592])
            (.absurd 594))
        (.absurd 692))

theorem treePart121_check :
    treePart121.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[3] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 71, 74, 78, 82, 94, 95, 96 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart122 : CompactCellTree :=
  .split 35
    (.split 26
        (.split 66
            (.cell 94 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 568, 30, 35, 28, 33, 34, 682, 32])
            (.absurd 693))
        (.split 18
            (.split 66
                (.cell 95 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 57, 52, 56, 50, 181, 55, 672, 54])
                (.absurd 694))
            (.absurd 695)))
    (.split 26
        (.split 65
            (.split 62
                (.cell 78 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 590, 52, 56, 50, 670, 181, 55, 57, 672])
                (.absurd 673))
            (.split 62
                (.split 38
                    (.cell 71 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 337, 75, 80, 190, 676, 78, 73, 677, 74, 79, 678])
                    (.absurd 696))
                (.absurd 697)))
        (.split 18
            (.split 62
                (.split 56
                    (.cell 82 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 80, 190, 676, 78, 73, 79])
                    (.split 65
                        (.cell 96 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 100, 226, 687, 225, 94, 99, 345])
                        (.split 38
                            (.cell 74 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 184, 123, 339, 702, 121, 124, 712, 119, 122, 713])
                            (.absurd 732))))
                (.absurd 673))
            (.absurd 695)))

theorem treePart122_check :
    treePart122.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 71, 78, 79, 99 and Farkas receipts excluding inconsistent sign branches. -/
def treePart123 : CompactCellTree :=
  .split 8
    (.split 67
        (.cell 99 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 568, 33, 35, 30, 698, 32, 34, 28, 682])
        (.absurd 699))
    (.split 58
        (.split 62
            (.split 56
                (.cell 79 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 337, 78, 741, 75, 676, 74, 73, 79])
                (.split 65
                    (.cell 78 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 346, 225, 742, 96, 687, 95, 94, 99, 345])
                    (.split 38
                        (.cell 71 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 575, 121, 743, 184, 702, 120, 124, 712, 119, 122, 713])
                        (.absurd 732))))
            (.absurd 707))
        (.absurd 744))

theorem treePart123_check :
    treePart123.check splitForms farkasReceipts cells (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0]]) ++ [aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[2] + length[3]` in the row-03 length cone, with leaves
selecting cells 74, 82, 96, 100 and Farkas receipts excluding inconsistent sign branches. -/
def treePart124 : CompactCellTree :=
  .split 8
    (.split 18
        (.split 67
            (.cell 100 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 57, 181, 56, 52, 708, 54, 55, 50, 672])
            (.absurd 716))
        (.absurd 745))
    (.split 38
        (.split 18
            (.split 58
                (.split 59
                    (.cell 74 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 225, 746, 747, 687, 101, 748, 688, 99, 95, 689])
                    (.cell 96 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 225, 746, 96, 687, 101, 748, 99, 345]))
                (.absurd 357))
            (.absurd 749))
        (.split 18
            (.split 58
                (.split 62
                    (.split 56
                        (.cell 82 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 121, 750, 184, 702, 117, 119, 122])
                        (.split 65
                            (.cell 96 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 152, 751, 185, 704, 139, 141, 143, 706])
                            (.absurd 752)))
                    (.absurd 753))
                (.absurd 357))
            (.absurd 749)))

theorem treePart124_check :
    treePart124.check splitForms farkasReceipts cells (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5]` in the row-03 length cone, with leaves
selecting cells 80, 83 and Farkas receipts excluding inconsistent sign branches. -/
def treePart125 : CompactCellTree :=
  .split 26
    (.split 67
        (.split 39
            (.cell 80 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 590, 52, 56, 181, 708, 54, 57, 709, 50, 55, 710])
            (.absurd 736))
        (.absurd 699))
    (.split 18
        (.split 67
            (.split 39
                (.cell 83 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 75, 80, 78, 722, 77, 73, 723, 190, 79, 724])
                (.absurd 738))
            (.absurd 716))
        (.absurd 695))

theorem treePart125_check :
    treePart125.check splitForms farkasReceipts cells (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[1] - length[5]` in the row-03 length cone, with leaves
selecting cells 71, 74, 78, 79, 82, 96 and Farkas receipts excluding inconsistent sign branches. -/
def treePart126 : CompactCellTree :=
  .split 26
    (.split 58
        (.split 62
            (.split 56
                (.cell 79 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 337, 75, 741, 78, 676, 74, 73, 79])
                (.split 65
                    (.cell 78 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 346, 96, 742, 225, 687, 95, 94, 99, 345])
                    (.split 38
                        (.cell 71 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 575, 184, 743, 121, 702, 120, 124, 712, 754, 122, 713])
                        (.absurd 755))))
            (.absurd 756))
        (.absurd 757))
    (.split 18
        (.split 58
            (.split 62
                (.split 56
                    (.cell 82 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 758, 225, 687, 94, 101, 99])
                    (.split 65
                        (.cell 96 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 120, 184, 759, 121, 702, 124, 117, 122, 718])
                        (.split 38
                            (.cell 74 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 142, 185, 760, 152, 704, 146, 139, 719, 761, 143, 720])
                            (.absurd 762))))
                (.absurd 763))
            (.absurd 324))
        (.absurd 695))

theorem treePart126_check :
    treePart126.check splitForms farkasReceipts cells (((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 93, 101 and Farkas receipts excluding inconsistent sign branches. -/
def treePart127 : CompactCellTree :=
  .split 10
    (.cell 101 [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 398, 545, 397, 400, 734, 399, 396, 659, 658])
    (.split 55
        (.cell 93 [430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 444, 445, 443, 446, 735, 587, 442, 664, 663])
        (.absurd 599))

theorem treePart127_check :
    treePart127.check splitForms farkasReceipts cells (((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 98, 102 and Farkas receipts excluding inconsistent sign branches. -/
def treePart128 : CompactCellTree :=
  .split 10
    (.split 8
        (.cell 102 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 563, 562, 565, 564, 581, 558, 582, 667])
        (.absurd 668))
    (.split 55
        (.split 8
            (.cell 98 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 33, 30, 35, 34, 28, 32, 682, 683])
            (.absurd 574))
        (.absurd 692))

theorem treePart128_check :
    treePart128.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 83, 91, 100, 103, 104 and Farkas receipts excluding inconsistent sign branches. -/
def treePart129 : CompactCellTree :=
  .split 10
    (.split 8
        (.split 37
            (.split 67
                (.cell 103 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 590, 56, 52, 708, 50, 55, 57, 672])
                (.absurd 736))
            (.split 67
                (.split 39
                    (.cell 91 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 337, 80, 75, 722, 190, 73, 723, 74, 79, 724])
                    (.absurd 696))
                (.absurd 736)))
        (.absurd 668))
    (.split 55
        (.split 8
            (.split 67
                (.split 31
                    (.cell 104 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 75, 80, 74, 722, 190, 73, 79])
                    (.split 37
                        (.cell 100 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 225, 96, 100, 95, 764, 226, 94, 99, 345])
                        (.split 39
                            (.cell 83 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 121, 184, 123, 120, 765, 339, 124, 766, 119, 122, 767])
                            (.absurd 732))))
                (.absurd 736))
            (.absurd 574))
        (.absurd 692))

theorem treePart129_check :
    treePart129.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[3] - length[6] - length[7] + length[8]` in the row-03 length
cone, with leaves selecting cells 74, 87, 95, 96, 105, 106 and Farkas receipts excluding
inconsistent sign branches. -/
def treePart130 : CompactCellTree :=
  .split 59
    (.split 10
        (.cell 87 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 564, 562, 768, 558, 769, 770, 771, 772, 563, 581, 773])
        (.split 55
            (.cell 74 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 30, 34, 774, 32, 775, 776, 777, 778, 33, 28, 779])
            (.absurd 695)))
    (.split 58
        (.split 10
            (.cell 105 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 34, 568, 780, 32, 775, 30, 777, 33, 682])
            (.split 55
                (.cell 96 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 57, 55, 781, 54, 670, 52, 782, 181, 672])
                (.absurd 783)))
        (.split 10
            (.split 36
                (.cell 106 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 57, 590, 56, 54, 52, 471, 672, 55])
                (.absurd 378))
            (.split 55
                (.split 36
                    (.cell 95 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74, 73, 80, 77, 75, 403, 336, 79])
                    (.absurd 357))
                (.absurd 783))))

theorem treePart130_check :
    treePart130.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 82, 90, 95, 96, 105, 106 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart131 : CompactCellTree :=
  .split 10
    (.split 35
        (.split 36
            (.cell 106 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 33, 568, 35, 32, 30, 401, 682, 378])
            (.absurd 744))
        (.split 62
            (.split 56
                (.cell 90 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 590, 56, 54, 670, 52, 57, 55])
                (.split 65
                    (.cell 105 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 337, 80, 77, 676, 75, 74, 79, 336])
                    (.absurd 738)))
            (.absurd 784)))
    (.split 35
        (.split 55
            (.split 36
                (.cell 95 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 57, 56, 54, 52, 471, 672, 357])
                (.absurd 378))
            (.absurd 745))
        (.split 55
            (.split 62
                (.split 56
                    (.cell 82 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 74, 80, 77, 676, 75, 73, 79])
                    (.split 65
                        (.cell 96 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 225, 95, 100, 98, 687, 96, 94, 99, 345])
                        (.absurd 785)))
                (.absurd 786))
            (.absurd 745)))

theorem treePart131_check :
    treePart131.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0]]) ++ [AffineForm.violation (aff [0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- Subtree splitting on `- length[0] + length[1]` in the row-03 length cone, with leaves
selecting cells 83, 91, 98, 100, 102, 103 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart132 : CompactCellTree :=
  .split 10
    (.split 64
        (.cell 91 [546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 563, 562, 787, 558, 788, 789, 771, 790, 564, 581, 791])
        (.split 61
            (.cell 103 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 33, 568, 792, 32, 698, 34, 777, 30, 682])
            (.split 35
                (.split 68
                    (.cell 102 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 78, 337, 80, 77, 74, 79, 336, 73])
                    (.absurd 458))
                (.absurd 627))))
    (.split 55
        (.split 61
            (.split 64
                (.cell 83 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 52, 793, 54, 708, 57, 782, 709, 55, 50, 710])
                (.cell 100 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 52, 793, 54, 708, 57, 782, 55, 672]))
            (.split 64
                (.cell 83 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 181, 52, 794, 54, 708, 795, 782, 709, 55, 50, 710])
                (.split 35
                    (.split 68
                        (.cell 98 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 225, 96, 100, 98, 95, 99, 345, 101])
                        (.absurd 451))
                    (.absurd 376))))
        (.absurd 692))

theorem treePart132_check :
    treePart132.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1]]) = true := by
  decide +kernel

/-- Subtree splitting on `length[2] + length[6] - length[8]` in the row-03 length cone, with
leaves selecting cells 98, 100, 102, 103, 104, 107 and Farkas receipts excluding inconsistent
sign branches. -/
def treePart133 : CompactCellTree :=
  .split 36
    (.split 10
        (.split 35
            (.split 68
                (.cell 102 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 52, 590, 56, 54, 181, 55, 672, 57])
                (.absurd 449))
            (.absurd 757))
        (.split 55
            (.split 35
                (.split 68
                    (.cell 98 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 75, 74, 80, 77, 78, 79, 336, 73])
                    (.absurd 458))
                (.absurd 324))
            (.absurd 695)))
    (.split 10
        (.split 67
            (.split 31
                (.cell 107 [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 52, 590, 56, 54, 708, 181, 57, 55])
                (.split 37
                    (.cell 103 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 75, 337, 80, 77, 722, 78, 74, 79, 336])
                    (.absurd 738)))
            (.absurd 730))
        (.split 55
            (.split 67
                (.split 31
                    (.cell 104 [61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 75, 74, 80, 77, 722, 78, 73, 79])
                    (.split 37
                        (.cell 100 [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 96, 95, 100, 98, 764, 225, 94, 99, 345])
                        (.absurd 785)))
                (.absurd 673))
            (.absurd 695)))

theorem treePart133_check :
    treePart133.check splitForms farkasReceipts cells ((((((base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, -1])]) ++ [AffineForm.violation (aff [0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 0, 1, 0, 0, 1, -1, -1, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0])]) ++ [AffineForm.violation (aff [0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1])]) = true := by
  decide +kernel

/-- A branch of the final row-03 cover assembly, starting at split form 2
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch0 : CompactCellTree :=
  .split 2
    (.split 3
      treePart0
      (.split 4
        (.split 5
          (.split 6
            (.split 7
              treePart1
              treePart2)
            (.split 8
              treePart3
              treePart4))
          (.split 9
            (.split 6
              (.split 10
                treePart5
                (.split 11
                  treePart6
                  treePart7))
              (.split 10
                treePart8
                (.split 11
                  (.split 12
                    treePart9
                    treePart10)
                  treePart11)))
            (.split 13
              (.split 14
                (.split 10
                  treePart12
                  treePart13)
                (.split 15
                  treePart14
                  treePart15))
              (.split 10
                treePart16
                (.split 11
                  (.split 12
                    treePart17
                    treePart18)
                  treePart19)))))
        (.split 6
          (.split 16
            (.split 17
              (.split 14
                treePart20
                treePart21)
              treePart22)
            (.split 18
              treePart23
              treePart24))
          (.split 8
            (.split 16
              treePart25
              treePart26)
            (.split 17
              treePart27
              treePart28)))))
    (.split 6
      (.split 14
        (.split 3
          treePart29
          (.split 4
            (.split 5
              treePart30
              (.split 19
                treePart31
                treePart32))
            (.split 20
              treePart33
              (.split 17
                treePart34
                treePart35))))
        (.split 3
          treePart36
          (.split 4
            (.split 7
              treePart37
              (.split 9
                treePart38
                treePart39))
            (.split 20
              treePart40
              (.split 17
                treePart41
                (.split 21
                  treePart42
                  treePart43))))))
      (.split 8
        (.split 3
          treePart44
          (.split 19
            (.split 4
              (.split 7
                treePart45
                treePart46)
              (.split 20
                treePart47
                treePart48))
            (.split 11
              (.split 16
                treePart49
                (.split 22
                  treePart50
                  treePart51))
              (.split 5
                treePart52
                (.split 10
                  treePart53
                  treePart54)))))
        (.split 3
          treePart55
          (.split 4
            (.split 9
              (.split 5
                treePart56
                treePart57)
              (.split 13
                treePart58
                treePart59))
            (.split 20
              treePart60
              (.split 17
                treePart61
                (.split 21
                  treePart62
                  treePart63)))))))

theorem treeAssemblyBranch0_check :
    treeAssemblyBranch0.check splitForms farkasReceipts cells
      ((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [aff [0, 0, 0, 0, 0, 0, -1,
        0, 1, 0, 0, 0, 0]]) = true := by
  simp only [treeAssemblyBranch0, CompactCellTree.check_split, Bool.and_true, splitForm2,
    splitForm3, splitForm4, splitForm5, splitForm6, splitForm7, splitForm8, splitForm9,
    splitForm10, splitForm11, splitForm12, splitForm13, splitForm14, splitForm15, splitForm16,
    splitForm17, splitForm18, splitForm19, splitForm20, splitForm21, splitForm22,
    treePart0_check, treePart1_check, treePart10_check, treePart11_check, treePart12_check,
    treePart13_check, treePart14_check, treePart15_check, treePart16_check, treePart17_check,
    treePart18_check, treePart19_check, treePart2_check, treePart20_check, treePart21_check,
    treePart22_check, treePart23_check, treePart24_check, treePart25_check, treePart26_check,
    treePart27_check, treePart28_check, treePart29_check, treePart3_check, treePart30_check,
    treePart31_check, treePart32_check, treePart33_check, treePart34_check, treePart35_check,
    treePart36_check, treePart37_check, treePart38_check, treePart39_check, treePart4_check,
    treePart40_check, treePart41_check, treePart42_check, treePart43_check, treePart44_check,
    treePart45_check, treePart46_check, treePart47_check, treePart48_check, treePart49_check,
    treePart5_check, treePart50_check, treePart51_check, treePart52_check, treePart53_check,
    treePart54_check, treePart55_check, treePart56_check, treePart57_check, treePart58_check,
    treePart59_check, treePart6_check, treePart60_check, treePart61_check, treePart62_check,
    treePart63_check, treePart7_check, treePart8_check, treePart9_check]

/-- A branch of the final row-03 cover assembly, starting at split form 4
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch1 : CompactCellTree :=
  .split 4
    (.split 7
      (.split 5
        treePart64
        (.split 23
          (.split 3
            treePart65
            (.split 9
              treePart66
              (.split 10
                (.split 24
                  treePart67
                  treePart68)
                treePart69)))
          (.split 10
            (.split 3
              treePart70
              (.split 9
                treePart71
                (.split 13
                  treePart72
                  treePart73)))
            treePart74)))
      (.split 18
        (.split 19
          treePart75
          (.split 11
            (.split 3
              treePart76
              (.split 14
                treePart77
                treePart78))
            treePart79))
        (.split 25
          (.split 3
            treePart80
            (.split 9
              treePart81
              (.split 13
                treePart82
                treePart83)))
          (.split 26
            (.split 3
              treePart84
              (.split 24
                (.split 27
                  (.split 6
                    treePart85
                    treePart86)
                  treePart87)
                treePart88))
            treePart89))))
    (.split 3
      treePart90
      (.split 6
        (.split 17
          (.split 10
            treePart91
            (.split 11
              treePart92
              treePart93))
          (.split 21
            (.split 14
              treePart94
              treePart95)
            treePart96))
        (.split 16
          (.split 18
            treePart97
            (.split 24
              treePart98
              treePart99))
          (.split 18
            treePart100
            treePart101))))

theorem treeAssemblyBranch1_check :
    treeAssemblyBranch1.check splitForms farkasReceipts cells
      ((base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) ++ [AffineForm.violation (aff
        [0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0])]) = true := by
  simp only [treeAssemblyBranch1, CompactCellTree.check_split, Bool.and_true, splitForm3,
    splitForm4, splitForm5, splitForm6, splitForm7, splitForm9, splitForm10, splitForm11,
    splitForm13, splitForm14, splitForm16, splitForm17, splitForm18, splitForm19, splitForm21,
    splitForm23, splitForm24, splitForm25, splitForm26, splitForm27, treePart100_check,
    treePart101_check, treePart64_check, treePart65_check, treePart66_check, treePart67_check,
    treePart68_check, treePart69_check, treePart70_check, treePart71_check, treePart72_check,
    treePart73_check, treePart74_check, treePart75_check, treePart76_check, treePart77_check,
    treePart78_check, treePart79_check, treePart80_check, treePart81_check, treePart82_check,
    treePart83_check, treePart84_check, treePart85_check, treePart86_check, treePart87_check,
    treePart88_check, treePart89_check, treePart90_check, treePart91_check, treePart92_check,
    treePart93_check, treePart94_check, treePart95_check, treePart96_check, treePart97_check,
    treePart98_check, treePart99_check]

/-- A branch of the final row-03 cover assembly, starting at split form 1
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch2 : CompactCellTree :=
  .split 1
    treeAssemblyBranch0
    treeAssemblyBranch1

theorem treeAssemblyBranch2_check :
    treeAssemblyBranch2.check splitForms farkasReceipts cells
      (base ++ [aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0]]) = true := by
  simp only [treeAssemblyBranch2, CompactCellTree.check_split, Bool.and_true, splitForm1,
    treeAssemblyBranch0_check, treeAssemblyBranch1_check]

/-- A branch of the final row-03 cover assembly, starting at split form 28
and combining the previously verified decision subtrees. -/
def treeAssemblyBranch3 : CompactCellTree :=
  .split 28
    (.split 23
      (.split 29
        (.split 30
          treePart102
          (.split 26
            treePart103
            treePart104))
        (.split 31
          (.split 8
            treePart105
            treePart106)
          (.split 26
            (.split 32
              treePart107
              treePart108)
            (.split 32
              treePart109
              treePart110))))
      (.split 29
        (.split 30
          treePart111
          treePart112)
        (.split 31
          (.split 8
            treePart113
            treePart114)
          (.split 10
            (.split 32
              treePart115
              treePart116)
            treePart117))))
    (.split 23
      (.split 33
        (.split 34
          treePart118
          (.split 35
            treePart119
            treePart120))
        (.split 36
          (.split 8
            treePart121
            treePart122)
          (.split 37
            (.split 26
              treePart123
              treePart124)
            (.split 8
              treePart125
              treePart126))))
      (.split 34
        (.split 33
          treePart127
          (.split 36
            treePart128
            treePart129))
        (.split 15
          (.split 38
            treePart130
            treePart131)
          (.split 39
            treePart132
            treePart133))))

theorem treeAssemblyBranch3_check :
    treeAssemblyBranch3.check splitForms farkasReceipts cells
      (base ++ [AffineForm.violation (aff [0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0])]) = true :=
        by
  simp only [treeAssemblyBranch3, CompactCellTree.check_split, Bool.and_true, splitForm8,
    splitForm10, splitForm15, splitForm23, splitForm26, splitForm28, splitForm29, splitForm30,
    splitForm31, splitForm32, splitForm33, splitForm34, splitForm35, splitForm36, splitForm37,
    splitForm38, splitForm39, treePart102_check, treePart103_check, treePart104_check,
    treePart105_check, treePart106_check, treePart107_check, treePart108_check,
    treePart109_check, treePart110_check, treePart111_check, treePart112_check,
    treePart113_check, treePart114_check, treePart115_check, treePart116_check,
    treePart117_check, treePart118_check, treePart119_check, treePart120_check,
    treePart121_check, treePart122_check, treePart123_check, treePart124_check,
    treePart125_check, treePart126_check, treePart127_check, treePart128_check,
    treePart129_check, treePart130_check, treePart131_check, treePart132_check,
    treePart133_check]

/-- The complete row-03 closed-cover decision tree, assembling the 134 checked subtrees in order
and starting with split form zero. Its leaves refer to the shared cell and Farkas-receipt
tables. -/
def tree : CompactCellTree :=
  .split 0
    treeAssemblyBranch2
    treeAssemblyBranch3

theorem cells_check :
    cells.all (fun cell => cell.certificate.checkClosed 4) = true := by
  simp [cells, cell0_check, cell1_check, cell2_check, cell3_check, cell4_check, cell5_check, cell6_check, cell7_check, cell8_check, cell9_check, cell10_check, cell11_check, cell12_check, cell13_check, cell14_check, cell15_check, cell16_check, cell17_check, cell18_check, cell19_check, cell20_check, cell21_check, cell22_check, cell23_check, cell24_check, cell25_check, cell26_check, cell27_check, cell28_check, cell29_check, cell30_check, cell31_check, cell32_check, cell33_check, cell34_check, cell35_check, cell36_check, cell37_check, cell38_check, cell39_check, cell40_check, cell41_check, cell42_check, cell43_check, cell44_check, cell45_check, cell46_check, cell47_check, cell48_check, cell49_check, cell50_check, cell51_check, cell52_check, cell53_check, cell54_check, cell55_check, cell56_check, cell57_check, cell58_check, cell59_check, cell60_check, cell61_check, cell62_check, cell63_check, cell64_check, cell65_check, cell66_check, cell67_check, cell68_check, cell69_check, cell70_check, cell71_check, cell72_check, cell73_check, cell74_check, cell75_check, cell76_check, cell77_check, cell78_check, cell79_check, cell80_check, cell81_check, cell82_check, cell83_check, cell84_check, cell85_check, cell86_check, cell87_check, cell88_check, cell89_check, cell90_check, cell91_check, cell92_check, cell93_check, cell94_check, cell95_check, cell96_check, cell97_check, cell98_check, cell99_check, cell100_check, cell101_check, cell102_check, cell103_check, cell104_check, cell105_check, cell106_check, cell107_check]

theorem cells_valid : ∀ cell ∈ cells, cell.certificate.ValidClosed 4 := by
  intro cell hCell
  have hChecks := (List.all_eq_true.mp cells_check) cell hCell
  exact (ExplicitPotential.Certificate.checkClosed_eq_true_iff _ _).mp hChecks

theorem tree_check :
    tree.check splitForms farkasReceipts cells base = true := by
  simp only [tree, CompactCellTree.check_split, Bool.and_true, splitForm0,
    treeAssemblyBranch2_check, treeAssemblyBranch3_check]

theorem base_holds (length : Fin 12 → ℕ) :
    ExplicitPotential.FormsHold base (lengthPoint length) := by
  intro form hForm
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hForm
  rcases hForm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp [aff,
    _root_.Utilities.Certificate.AffineCover.AffineForm.Holds,
    _root_.Utilities.Certificate.AffineCover.AffineForm.eval,
    lengthPoint, Fin.sum_univ_succ]

theorem closedConstruction :
    ClosedSubdivisionDharConstruction row03Core (by norm_num) :=
  closedConstruction_of_compactCellTree (by norm_num) row03_connected
    cells base splitForms farkasReceipts tree base_holds cells_valid tree_check

end AtanasovRanganathan.GenusFiveRow03FixedCover
