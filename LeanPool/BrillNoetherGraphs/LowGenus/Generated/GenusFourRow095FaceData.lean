/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow097Contractions
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedContraction
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ReorientContraction

/-!
# Passive contraction data for the twenty-four proper faces of row 095

The zero-set ledger and its mathematical dispatch live in
`LowGenus.GenusFourRow095Closed`.  This file contains only the repetitive
finite witnesses: for each proper nonloopy forest face, a quotient core,
vertex representatives, surviving slots, and slot reversals.  Every field is
rechecked by the kernel through `decide`.
-/
namespace AtanasovRanganathan.Generated.GenusFourRow095FaceData

open Utilities.Certificate
open Utilities.Certificate.ClosedContraction
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.ReorientContraction
open LowGenus.GenusFourRow095
open LowGenus.GenusFourRow097Contractions

def core002 : ExplicitPotential.Core 2 5 where
  tail := ![0, 0, 0, 0, 0]
  head := ![1, 1, 1, 1, 1]

def core009 : ExplicitPotential.Core 3 6 where
  tail := ![0, 0, 0, 1, 1, 1]
  head := ![2, 2, 2, 2, 2, 2]

def core010 : ExplicitPotential.Core 3 6 where
  tail := ![0, 0, 0, 1, 1, 1]
  head := ![1, 2, 2, 2, 2, 2]

def core029 : ExplicitPotential.Core 4 7 where
  tail := ![0, 0, 0, 1, 1, 1, 2]
  head := ![3, 3, 3, 2, 2, 3, 3]

def core069 : ExplicitPotential.Core 5 8 where
  tail := ![0, 0, 0, 1, 1, 1, 2, 3]
  head := ![3, 4, 4, 2, 2, 3, 3, 4]

/-! Each reversal vector is read on its displayed target core. -/

def rev_0 : Fin 8 → Bool := ![false, false, false, false, false, false, true, true]
def rev_3 : Fin 8 → Bool := ![true, true, true, true, true, true, false, false]
def rev_5 : Fin 8 → Bool := ![true, true, true, true, true, true, false, false]
def rev_8 : Fin 8 → Bool := ![false, false, false, false, false, false, true, true]
def rev_4 : Fin 8 → Bool := ![false, false, false, false, false, false, true, false]

def rev_0_4 : Fin 7 → Bool := ![true, true, true, false, false, false, true]
def rev_3_4 : Fin 7 → Bool := ![false, false, false, false, false, false, true]
def rev_4_5 : Fin 7 → Bool := ![false, false, false, false, false, false, true]
def rev_4_8 : Fin 7 → Bool := ![true, true, true, false, false, false, true]
def rev_0_8 : Fin 7 → Bool := ![true, true, true, true, true, true, false]
def rev_3_5 : Fin 7 → Bool := ![false, false, false, false, false, false, true]
def rev_0_3 : Fin 7 → Bool := ![false, false, false, true, true, true, true]
def rev_5_8 : Fin 7 → Bool := ![false, false, false, true, true, true, true]
def rev_0_5 : Fin 7 → Bool := ![false, false, false, true, true, false, false]
def rev_3_8 : Fin 7 → Bool := ![false, false, false, false, true, true, false]

def rev_0_3_4 : Fin 6 → Bool := ![false, false, false, true, true, true]
def rev_3_4_5 : Fin 6 → Bool := ![false, false, false, false, false, false]
def rev_0_4_8 : Fin 6 → Bool := ![true, true, true, true, true, true]
def rev_4_5_8 : Fin 6 → Bool := ![false, false, false, true, true, true]
def rev_0_3_5 : Fin 6 → Bool := ![false, false, false, false, false, true]
def rev_0_3_8 : Fin 6 → Bool := ![true, true, true, false, true, true]
def rev_0_5_8 : Fin 6 → Bool := ![true, true, true, true, true, false]
def rev_3_5_8 : Fin 6 → Bool := ![false, false, false, true, false, false]
def rev_0_3_5_8 : Fin 5 → Bool := ![false, false, true, false, false]

/-! One checked contraction witness per proper face. -/

def data_0 : ContractionData core (Core.reorient core068 rev_0) where
  F := {0}; vtx := ![2, 1, 5, 4, 3]; slot := ![8, 6, 7, 5, 4, 3, 1, 2]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_3 : ContractionData core (Core.reorient core068 rev_3) where
  F := {3}; vtx := ![5, 4, 2, 3, 0]; slot := ![5, 1, 2, 8, 4, 0, 6, 7]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_5 : ContractionData core (Core.reorient core068 rev_5) where
  F := {5}; vtx := ![3, 4, 0, 5, 2]; slot := ![3, 6, 7, 0, 4, 8, 1, 2]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_8 : ContractionData core (Core.reorient core068 rev_8) where
  F := {8}; vtx := ![0, 1, 3, 4, 5]; slot := ![0, 1, 2, 3, 4, 5, 6, 7]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_4 : ContractionData core (Core.reorient core069 rev_4) where
  F := {4}; vtx := ![0, 2, 3, 4, 5]; slot := ![0, 1, 2, 6, 7, 8, 3, 5]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_0_4 : ContractionData core (Core.reorient core029 rev_0_4) where
  F := {0, 4}; vtx := ![5, 2, 3, 4]; slot := ![1, 2, 5, 6, 7, 8, 3]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_3_4 : ContractionData core (Core.reorient core029 rev_3_4) where
  F := {3, 4}; vtx := ![2, 0, 5, 4]; slot := ![6, 7, 8, 1, 2, 0, 5]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_4_5 : ContractionData core (Core.reorient core029 rev_4_5) where
  F := {4, 5}; vtx := ![0, 2, 3, 5]; slot := ![0, 1, 2, 6, 7, 8, 3]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_4_8 : ContractionData core (Core.reorient core029 rev_4_8) where
  F := {4, 8}; vtx := ![3, 0, 5, 4]; slot := ![3, 6, 7, 1, 2, 0, 5]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_0_8 : ContractionData core (Core.reorient core031 rev_0_8) where
  F := {0, 8}; vtx := ![3, 5, 1, 4]; slot := ![3, 6, 7, 5, 1, 2, 4]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_3_5 : ContractionData core (Core.reorient core031 rev_3_5) where
  F := {3, 5}; vtx := ![0, 2, 4, 5]; slot := ![0, 1, 2, 8, 6, 7, 4]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_0_3 : ContractionData core (Core.reorient core032 rev_0_3) where
  F := {0, 3}; vtx := ![2, 5, 4, 3]; slot := ![8, 6, 7, 1, 2, 5, 4]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_5_8 : ContractionData core (Core.reorient core032 rev_5_8) where
  F := {5, 8}; vtx := ![0, 3, 4, 5]; slot := ![0, 1, 2, 6, 7, 3, 4]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_0_5 : ContractionData core (Core.reorient core034 rev_0_5) where
  F := {0, 5}; vtx := ![2, 5, 4, 3]; slot := ![8, 6, 7, 1, 2, 4, 3]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_3_8 : ContractionData core (Core.reorient core034 rev_3_8) where
  F := {3, 8}; vtx := ![0, 3, 4, 5]; slot := ![0, 1, 2, 4, 6, 7, 5]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_0_3_4 : ContractionData core (Core.reorient core009 rev_0_3_4) where
  F := {0, 3, 4}; vtx := ![2, 5, 4]; slot := ![6, 7, 8, 1, 2, 5]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_3_4_5 : ContractionData core (Core.reorient core009 rev_3_4_5) where
  F := {3, 4, 5}; vtx := ![0, 2, 5]; slot := ![0, 1, 2, 6, 7, 8]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_0_4_8 : ContractionData core (Core.reorient core009 rev_0_4_8) where
  F := {0, 4, 8}; vtx := ![3, 5, 4]; slot := ![3, 6, 7, 1, 2, 5]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_4_5_8 : ContractionData core (Core.reorient core009 rev_4_5_8) where
  F := {4, 5, 8}; vtx := ![0, 3, 5]; slot := ![0, 1, 2, 3, 6, 7]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_0_3_5 : ContractionData core (Core.reorient core010 rev_0_3_5) where
  F := {0, 3, 5}; vtx := ![2, 4, 5]; slot := ![8, 6, 7, 1, 2, 4]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_0_3_8 : ContractionData core (Core.reorient core010 rev_0_3_8) where
  F := {0, 3, 8}; vtx := ![5, 3, 4]; slot := ![5, 1, 2, 4, 6, 7]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_0_5_8 : ContractionData core (Core.reorient core010 rev_0_5_8) where
  F := {0, 5, 8}; vtx := ![3, 5, 4]; slot := ![3, 6, 7, 1, 2, 4]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_3_5_8 : ContractionData core (Core.reorient core010 rev_3_5_8) where
  F := {3, 5, 8}; vtx := ![0, 4, 5]; slot := ![0, 1, 2, 4, 6, 7]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

def data_0_3_5_8 : ContractionData core (Core.reorient core002 rev_0_3_5_8) where
  F := {0, 3, 5, 8}; vtx := ![4, 5]; slot := ![1, 2, 4, 6, 7]
  isForest := by decide
  notLoopy := by decide
  slot_inj := by decide
  slot_notMem := by decide
  slot_surj := by decide
  vtx_inj := by decide
  vtx_rep := by decide
  vtx_surj := by decide
  tail_eq := by decide
  head_eq := by decide

end AtanasovRanganathan.Generated.GenusFourRow095FaceData
