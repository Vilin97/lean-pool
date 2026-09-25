/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow095
public import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow097Contractions
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedContraction
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ReorientContraction

/-!
# Passive contraction data for the twenty-four proper faces of row 095

The zero-set ledger and its mathematical dispatch live in
`LowGenus.GenusFourRow095Closed`.  This file contains only the repetitive
finite witnesses: for each proper nonloopy forest face, a quotient core,
vertex representatives, surviving slots, and slot reversals.  Every field is
rechecked by the kernel through `decide`.
-/

@[expose] public section
namespace AtanasovRanganathan.Generated.GenusFourRow095FaceData

open Utilities.Certificate
open Utilities.Certificate.ClosedContraction
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.ReorientContraction
open LowGenus.GenusFourRow095
open LowGenus.GenusFourRow097Contractions

/-- The two-vertex target core with five parallel edges, used by the row 095 face certificates. -/
def core002 : ExplicitPotential.Core 2 5 where
  tail := ![0, 0, 0, 0, 0]
  head := ![1, 1, 1, 1, 1]

/-- The three-vertex target core with three edges from each of vertices zero and one to vertex
two. -/
def core009 : ExplicitPotential.Core 3 6 where
  tail := ![0, 0, 0, 1, 1, 1]
  head := ![2, 2, 2, 2, 2, 2]

/-- The three-vertex target core with edge multiplicities one, two, and three between its vertex
pairs. -/
def core010 : ExplicitPotential.Core 3 6 where
  tail := ![0, 0, 0, 1, 1, 1]
  head := ![1, 2, 2, 2, 2, 2]

/-- The four-vertex, seven-slot target core used for the row 095 contraction faces. -/
def core029 : ExplicitPotential.Core 4 7 where
  tail := ![0, 0, 0, 1, 1, 1, 2]
  head := ![3, 3, 3, 2, 2, 3, 3]

/-- The five-vertex, eight-slot target core used for the row 095 contraction faces. -/
def core069 : ExplicitPotential.Core 5 8 where
  tail := ![0, 0, 0, 1, 1, 1, 2, 3]
  head := ![3, 4, 4, 2, 2, 3, 3, 4]

/-! Each reversal vector is read on its displayed target core. -/

/-- Reverse target slots six and seven in the single-slot face-zero contraction certificate. -/
def rev0 : Fin 8 → Bool := ![false, false, false, false, false, false, true, true]
/-- Reverse target slots zero through five in the single-slot face-three contraction
certificate. -/
def rev3 : Fin 8 → Bool := ![true, true, true, true, true, true, false, false]
/-- Reverse target slots zero through five in the single-slot face-five contraction certificate. -/
def rev5 : Fin 8 → Bool := ![true, true, true, true, true, true, false, false]
/-- Reverse target slots six and seven in the single-slot face-eight contraction certificate. -/
def rev8 : Fin 8 → Bool := ![false, false, false, false, false, false, true, true]
/-- Reverse only target slot six in the single-slot face-four contraction certificate. -/
def rev4 : Fin 8 → Bool := ![false, false, false, false, false, false, true, false]

/-- Reverse target slots zero, one, two, and six in the face-zero-four contraction certificate. -/
def rev04 : Fin 7 → Bool := ![true, true, true, false, false, false, true]
/-- Reverse only target slot six in the face-three-four contraction certificate. -/
def rev34 : Fin 7 → Bool := ![false, false, false, false, false, false, true]
/-- Reverse only target slot six in the face-four-five contraction certificate. -/
def rev45 : Fin 7 → Bool := ![false, false, false, false, false, false, true]
/-- Reverse target slots zero, one, two, and six in the face-four-eight contraction certificate. -/
def rev48 : Fin 7 → Bool := ![true, true, true, false, false, false, true]
/-- Reverse target slots zero through five in the face-zero-eight contraction certificate. -/
def rev08 : Fin 7 → Bool := ![true, true, true, true, true, true, false]
/-- Orientation flags for `data35`: reverse target slots 6. -/
def rev35 : Fin 7 → Bool := ![false, false, false, false, false, false, true]
/-- Orientation flags for `data03`: reverse target slots 3, 4, 5, 6. -/
def rev03 : Fin 7 → Bool := ![false, false, false, true, true, true, true]
/-- Orientation flags for `data58`: reverse target slots 3, 4, 5, 6. -/
def rev58 : Fin 7 → Bool := ![false, false, false, true, true, true, true]
/-- Orientation flags for `data05`: reverse target slots 3, 4. -/
def rev05 : Fin 7 → Bool := ![false, false, false, true, true, false, false]
/-- Orientation flags for `data38`: reverse target slots 4, 5. -/
def rev38 : Fin 7 → Bool := ![false, false, false, false, true, true, false]

/-- Orientation flags for `data034`: reverse target slots 3, 4, 5. -/
def rev034 : Fin 6 → Bool := ![false, false, false, true, true, true]
/-- Orientation flags for `data345`: keep every target slot in its displayed orientation. -/
def rev345 : Fin 6 → Bool := ![false, false, false, false, false, false]
/-- Orientation flags for `data048`: reverse target slots 0, 1, 2, 3, 4, 5. -/
def rev048 : Fin 6 → Bool := ![true, true, true, true, true, true]
/-- Orientation flags for `data458`: reverse target slots 3, 4, 5. -/
def rev458 : Fin 6 → Bool := ![false, false, false, true, true, true]
/-- Orientation flags for `data035`: reverse target slots 5. -/
def rev035 : Fin 6 → Bool := ![false, false, false, false, false, true]
/-- Orientation flags for `data038`: reverse target slots 0, 1, 2, 4, 5. -/
def rev038 : Fin 6 → Bool := ![true, true, true, false, true, true]
/-- Orientation flags for `data058`: reverse target slots 0, 1, 2, 3, 4. -/
def rev058 : Fin 6 → Bool := ![true, true, true, true, true, false]
/-- Orientation flags for `data358`: reverse target slots 3. -/
def rev358 : Fin 6 → Bool := ![false, false, false, true, false, false]
/-- Orientation flags for `data0358`: reverse target slots 2. -/
def rev0358 : Fin 5 → Bool := ![false, false, true, false, false]

/-! One checked contraction witness per proper face. -/

/-- The checked contraction of row 095 along source slots {0} onto `core068`, oriented by
`rev0`. -/
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

/-- The checked contraction of row 095 along source slots {3} onto `core068`, oriented by
`rev3`. -/
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

/-- The checked contraction of row 095 along source slots {5} onto `core068`, oriented by
`rev5`. -/
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

/-- The checked contraction of row 095 along source slots {8} onto `core068`, oriented by
`rev8`. -/
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

/-- The checked contraction of row 095 along source slots {4} onto `core069`, oriented by
`rev4`. -/
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

/-- The checked contraction of row 095 along source slots {0, 4} onto `core029`, oriented by
`rev04`. -/
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

/-- The checked contraction of row 095 along source slots {3, 4} onto `core029`, oriented by
`rev34`. -/
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

/-- The checked contraction of row 095 along source slots {4, 5} onto `core029`, oriented by
`rev45`. -/
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

/-- The checked contraction of row 095 along source slots {4, 8} onto `core029`, oriented by
`rev48`. -/
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

/-- The checked contraction of row 095 along source slots {0, 8} onto `core031`, oriented by
`rev08`. -/
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

/-- The checked contraction of row 095 along source slots {3, 5} onto `core031`, oriented by
`rev35`. -/
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

/-- The checked contraction of row 095 along source slots {0, 3} onto `core032`, oriented by
`rev03`. -/
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

/-- The checked contraction of row 095 along source slots {5, 8} onto `core032`, oriented by
`rev58`. -/
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

/-- The checked contraction of row 095 along source slots {0, 5} onto `core034`, oriented by
`rev05`. -/
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

/-- The checked contraction of row 095 along source slots {3, 8} onto `core034`, oriented by
`rev38`. -/
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

/-- The checked contraction of row 095 along source slots {0, 3, 4} onto `core009`, oriented by
`rev034`. -/
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

/-- The checked contraction of row 095 along source slots {3, 4, 5} onto `core009`, oriented by
`rev345`. -/
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

/-- The checked contraction of row 095 along source slots {0, 4, 8} onto `core009`, oriented by
`rev048`. -/
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

/-- The checked contraction of row 095 along source slots {4, 5, 8} onto `core009`, oriented by
`rev458`. -/
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

/-- The checked contraction of row 095 along source slots {0, 3, 5} onto `core010`, oriented by
`rev035`. -/
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

/-- The checked contraction of row 095 along source slots {0, 3, 8} onto `core010`, oriented by
`rev038`. -/
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

/-- The checked contraction of row 095 along source slots {0, 5, 8} onto `core010`, oriented by
`rev058`. -/
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

/-- The checked contraction of row 095 along source slots {3, 5, 8} onto `core010`, oriented by
`rev358`. -/
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

/-- The checked contraction of row 095 along source slots {0, 3, 5, 8} onto `core002`, oriented
by `rev0358`. -/
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
