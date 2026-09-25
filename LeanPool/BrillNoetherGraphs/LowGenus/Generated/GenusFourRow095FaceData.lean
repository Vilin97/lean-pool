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

def rev0 : Fin 8 → Bool := ![false, false, false, false, false, false, true, true]
def rev3 : Fin 8 → Bool := ![true, true, true, true, true, true, false, false]
def rev5 : Fin 8 → Bool := ![true, true, true, true, true, true, false, false]
def rev8 : Fin 8 → Bool := ![false, false, false, false, false, false, true, true]
def rev4 : Fin 8 → Bool := ![false, false, false, false, false, false, true, false]

def rev04 : Fin 7 → Bool := ![true, true, true, false, false, false, true]
def rev34 : Fin 7 → Bool := ![false, false, false, false, false, false, true]
def rev45 : Fin 7 → Bool := ![false, false, false, false, false, false, true]
def rev48 : Fin 7 → Bool := ![true, true, true, false, false, false, true]
def rev08 : Fin 7 → Bool := ![true, true, true, true, true, true, false]
def rev35 : Fin 7 → Bool := ![false, false, false, false, false, false, true]
def rev03 : Fin 7 → Bool := ![false, false, false, true, true, true, true]
def rev58 : Fin 7 → Bool := ![false, false, false, true, true, true, true]
def rev05 : Fin 7 → Bool := ![false, false, false, true, true, false, false]
def rev38 : Fin 7 → Bool := ![false, false, false, false, true, true, false]

def rev034 : Fin 6 → Bool := ![false, false, false, true, true, true]
def rev345 : Fin 6 → Bool := ![false, false, false, false, false, false]
def rev048 : Fin 6 → Bool := ![true, true, true, true, true, true]
def rev458 : Fin 6 → Bool := ![false, false, false, true, true, true]
def rev035 : Fin 6 → Bool := ![false, false, false, false, false, true]
def rev038 : Fin 6 → Bool := ![true, true, true, false, true, true]
def rev058 : Fin 6 → Bool := ![true, true, true, true, true, false]
def rev358 : Fin 6 → Bool := ![false, false, false, true, false, false]
def rev0358 : Fin 5 → Bool := ![false, false, true, false, false]

/-! One checked contraction witness per proper face. -/

def data0 : ContractionData core (Core.reorient core068 rev0) where
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

def data3 : ContractionData core (Core.reorient core068 rev3) where
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

def data5 : ContractionData core (Core.reorient core068 rev5) where
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

def data8 : ContractionData core (Core.reorient core068 rev8) where
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

def data4 : ContractionData core (Core.reorient core069 rev4) where
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

def data04 : ContractionData core (Core.reorient core029 rev04) where
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

def data34 : ContractionData core (Core.reorient core029 rev34) where
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

def data45 : ContractionData core (Core.reorient core029 rev45) where
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

def data48 : ContractionData core (Core.reorient core029 rev48) where
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

def data08 : ContractionData core (Core.reorient core031 rev08) where
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

def data35 : ContractionData core (Core.reorient core031 rev35) where
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

def data03 : ContractionData core (Core.reorient core032 rev03) where
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

def data58 : ContractionData core (Core.reorient core032 rev58) where
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

def data05 : ContractionData core (Core.reorient core034 rev05) where
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

def data38 : ContractionData core (Core.reorient core034 rev38) where
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

def data034 : ContractionData core (Core.reorient core009 rev034) where
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

def data345 : ContractionData core (Core.reorient core009 rev345) where
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

def data048 : ContractionData core (Core.reorient core009 rev048) where
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

def data458 : ContractionData core (Core.reorient core009 rev458) where
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

def data035 : ContractionData core (Core.reorient core010 rev035) where
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

def data038 : ContractionData core (Core.reorient core010 rev038) where
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

def data058 : ContractionData core (Core.reorient core010 rev058) where
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

def data358 : ContractionData core (Core.reorient core010 rev358) where
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

def data0358 : ContractionData core (Core.reorient core002 rev0358) where
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
