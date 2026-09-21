/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourRow097Closed
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedContraction
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ReorientContraction

/-!
# Four readable genus-four faces of row 097

Rows 031, 032, 034, and 068 are obtained by contracting explicit forest
faces of the human-readable closed-orthant proof of row 097.  The statements
below deliberately name the small target cores directly, so this public proof
is self-contained.
-/

namespace LowGenus.GenusFourRow097Contractions

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open Utilities.Certificate.ClosedContraction
open Utilities.Certificate.ReorientContraction

def core031 : ExplicitPotential.Core 4 7 where
  tail := ![0, 0, 0, 1, 1, 1, 2]
  head := ![2, 3, 3, 2, 3, 3, 3]

def core032 : ExplicitPotential.Core 4 7 where
  tail := ![0, 0, 0, 1, 1, 1, 2]
  head := ![2, 3, 3, 2, 2, 3, 3]

def core034 : ExplicitPotential.Core 4 7 where
  tail := ![0, 0, 0, 1, 1, 1, 1]
  head := ![2, 3, 3, 2, 2, 2, 3]

def core068 : ExplicitPotential.Core 5 8 where
  tail := ![0, 0, 0, 1, 1, 1, 2, 2]
  head := ![3, 4, 4, 2, 3, 4, 3, 3]

def rev031 : Fin 7 → Bool := fun e => decide (4 ≤ e.val)
def rev032 : Fin 7 → Bool := fun e => decide (5 ≤ e.val)

def data031 : ContractionData GenusFourRow097Closed.core
    (Core.reorient core031 rev031) where
  F := {3, 5}
  vtx := ![0, 3, 4, 5]
  slot := ![0, 1, 2, 8, 4, 6, 7]
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

def data032 : ContractionData GenusFourRow097Closed.core
    (Core.reorient core032 rev032) where
  F := {5, 8}
  vtx := ![0, 2, 4, 5]
  slot := ![0, 1, 2, 6, 7, 3, 4]
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

def data034 : ContractionData GenusFourRow097Closed.core core034 where
  F := {3, 8}
  vtx := ![0, 2, 4, 5]
  slot := ![0, 1, 2, 4, 6, 7, 5]
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

def data068 : ContractionData GenusFourRow097Closed.core core068 where
  F := {8}
  vtx := ![0, 1, 2, 4, 5]
  slot := ![0, 1, 2, 3, 4, 5, 6, 7]
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

theorem bnExists031 (spec : SubdivisionGraph.Spec 4 7)
    (hcore : spec.core = core031) : BNExists spec.graph 1 3 :=
  bnExists_spec_of_closed_contraction_reorient GenusFourRow097Closed.core
    (by norm_num) 3 GenusFourRow097Closed.bnExists_closed
    rev031 data031 spec hcore

theorem bnExists032 (spec : SubdivisionGraph.Spec 4 7)
    (hcore : spec.core = core032) : BNExists spec.graph 1 3 :=
  bnExists_spec_of_closed_contraction_reorient GenusFourRow097Closed.core
    (by norm_num) 3 GenusFourRow097Closed.bnExists_closed
    rev032 data032 spec hcore

theorem bnExists034 (spec : SubdivisionGraph.Spec 4 7)
    (hcore : spec.core = core034) : BNExists spec.graph 1 3 :=
  bnExists_spec_of_closed_contraction GenusFourRow097Closed.core
    (by norm_num) 3 GenusFourRow097Closed.bnExists_closed data034 spec hcore

theorem bnExists068 (spec : SubdivisionGraph.Spec 5 8)
    (hcore : spec.core = core068) : BNExists spec.graph 1 3 :=
  bnExists_spec_of_closed_contraction GenusFourRow097Closed.core
    (by norm_num) 3 GenusFourRow097Closed.bnExists_closed data068 spec hcore

end LowGenus.GenusFourRow097Contractions
