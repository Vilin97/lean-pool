/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveClosedCover
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFiveCoreAtlas

/-! **Independent generated check.** This module provides an additional generated proof of row 06 and is not imported by the main `LowGenus` root.

Generated shared data for the chamber-restricted AR row-06 cover:
the fixed divisor and the pooled anchor witnesses.  Imported by every
cell chunk and by the assembling module. -/

namespace AtanasovRanganathan.GenusFiveRow06CoverBase

open Utilities

open Certificate ExplicitPotential
open Certificate.ExplicitPotential
open Certificate.AffineCover
open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

def aff (data : List ℤ) : ExplicitPotential.AffineForm 12 where
  fixedValue := data.getD 0 0
  coefficient := fun coordinate => data.getD (coordinate.val + 1) 0

def rowDivisor : Fin 8 → ℤ := fun vertex =>
  ([0, 0, 2, 2, 0, 0, 0, 0] : List ℤ).getD vertex.val 0

def defaultWitness : AnchorWitness 12 8 12 :=
  { alpha := fun _ => 0, beta := fun _ => 0, potential := fun _ => 0 }

def witness0 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

def witness1 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

def witness2 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [], []] : List (List ℤ)).getD vertex.val []) }

def witness3 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], []] : List (List ℤ)).getD vertex.val []) }

def witness4 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], []] : List (List ℤ)).getD vertex.val []) }

def witness5 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

def witness6 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

def witness7 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 2], [0, 0, 0, 0, 2], [0, 0, 0, 0, 2], [0, 0, 0, 0, 2], [0, 0, 0, 0, 2], [0, 0, 0, 0, 2]] : List (List ℤ)).getD vertex.val []) }

def witness8 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -2, 1, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

def witness9 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]] : List (List ℤ)).getD vertex.val []) }

def witness10 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([1, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, -1], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]] : List (List ℤ)).getD vertex.val []) }

def witness11 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([-1, -1, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [0, 0, 0, 2, -2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2], [0, 0, 0, 2]] : List (List ℤ)).getD vertex.val []) }

def witness12 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

def witness13 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -1, 1, 0, 2, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, -1, -1, -2, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, -1, 0, -2]] : List (List ℤ)).getD vertex.val []) }

def witness14 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -2, 1, 0, 2, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, -1, -1, -2, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, -1, 0, -2]] : List (List ℤ)).getD vertex.val []) }

def witness15 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 1, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0, -1], [0, 0, 0, 1, 0, -1]] : List (List ℤ)).getD vertex.val []) }

def witness16 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 1, -1, -1, -2, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

def witness17 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -1, -2, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], []] : List (List ℤ)).getD vertex.val []) }

def witness18 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -1, -2, -1, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1], [], []] : List (List ℤ)).getD vertex.val []) }

def witness19 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -2, -2, -1, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -1], [], []] : List (List ℤ)).getD vertex.val []) }

def witness20 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 0, 0, -1, -1, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, 0, 0, 1, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 1, 0, 0, 0, 0, -1], [0, 0, 0, 1], [0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

def witness21 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -1, -2, -1, -1] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], []] : List (List ℤ)).getD vertex.val []) }

def witness22 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -2, -1, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [], []] : List (List ℤ)).getD vertex.val []) }

def witness23 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -2, -1, 1, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [], []] : List (List ℤ)).getD vertex.val []) }

def witness24 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 1, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [], []] : List (List ℤ)).getD vertex.val []) }

def witness25 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, -1, 1, 0, 0, 0, 0, -1, -1, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 1, -1, 0, 0, 0, 0, 0, 1, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 1], [0, 0, 0, 1]] : List (List ℤ)).getD vertex.val []) }

def witness26 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, -2, -1, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, 0, 2, 1, -1, -1] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, 0, -2], [], []] : List (List ℤ)).getD vertex.val []) }

def witness27 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 0, 0, -1]] : List (List ℤ)).getD vertex.val []) }

def witness28 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -2, -1, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 2, 1, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [0, 0, 0, 0, 0, -2, -1], [0, 0, 0, 0, 0, -2]] : List (List ℤ)).getD vertex.val []) }

def witness29 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -2, -1, -1, 0, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 2, 1, 0, -2, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [0, 0, 0, 0, 0, -2, -1], [0, 0, 0, 0, 0, -2]] : List (List ℤ)).getD vertex.val []) }

def witness30 : AnchorWitness 12 8 12 :=
  { alpha := fun edge => ([0, 0, 0, 0, -2, -1, -1, 1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    beta := fun edge => ([0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, 0] : List ℤ).getD edge.val 0,
    potential := fun vertex => aff (([[], [], [], [], [], [], [0, 0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, -2]] : List (List ℤ)).getD vertex.val []) }

def witnesses : List (AnchorWitness 12 8 12) := [witness0, witness1, witness2, witness3, witness4, witness5, witness6, witness7, witness8, witness9, witness10, witness11, witness12, witness13, witness14, witness15, witness16, witness17, witness18, witness19, witness20, witness21, witness22, witness23, witness24, witness25, witness26, witness27, witness28, witness29, witness30]

end AtanasovRanganathan.GenusFiveRow06CoverBase
