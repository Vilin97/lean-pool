/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
import Mathlib.Tactic

/-!
# Finite loop-aware pseudocore certificates

This module defines finite loop-aware pseudocores and a Boolean checker for
their structural properties.  The validity API is parameterized by
cyclomatic genus; it does not contain a census or assert a completeness
theorem.

A loop-aware pseudocore stores semantic loops separately and stores nonloop
multiplicities in a full matrix.  The checker requires that matrix to be
symmetric with zero diagonal, so the redundant lower triangle cannot disagree
with the upper triangle used by `edgeCount`.  Validity then checks connected
nonloop support, stable valence at least three, and the requested genus
edge-count identity.

`SplitMetadata` is an optional second boundary matching the loopless split
cores used by explicit-potential certificates.  It gives every semantic loop
one marker vertex and checks the resulting `ExplicitPotential.Core` directly:
marker counts, looplessness, core connectivity, and every unordered edge
multiplicity are all replayed by finite Boolean folds.
-/

namespace Utilities.Certificate.GenusFourPseudocore

open Finset

/-- A labelled loop-aware multigraph on `Fin n`.  `multiplicity i j` is meant
to be an unordered nonloop multiplicity; validity checks symmetry and a zero
diagonal explicitly. -/
structure Pseudocore (n : ℕ) where
  loops : Fin n → ℕ
  multiplicity : Fin n → Fin n → ℕ

namespace Pseudocore

variable {n : ℕ} (core : Pseudocore n)

/-- Total number of semantic loop occurrences. -/
def loopCount : ℕ :=
  ∑ vertex : Fin n, core.loops vertex

/-- Number of nonloop edge occurrences, counted in the strict upper triangle. -/
def nonloopEdgeCount : ℕ :=
  ∑ first : Fin n, ∑ second : Fin n,
    if first < second then core.multiplicity first second else 0

/-- Total number of topological edge occurrences. -/
def edgeCount : ℕ :=
  core.loopCount + core.nonloopEdgeCount

/-- Loop-aware valence: a loop contributes two and a nonloop occurrence one. -/
def valence (vertex : Fin n) : ℕ :=
  2 * core.loops vertex +
    ∑ neighbor : Fin n, core.multiplicity vertex neighbor

/-- The redundant multiplicity matrix really represents unordered nonloops. -/
def MatrixWellFormed : Prop :=
  (∀ vertex : Fin n, core.multiplicity vertex vertex = 0) ∧
  ∀ first second : Fin n,
    core.multiplicity first second = core.multiplicity second first

/-- Connectedness of the nonloop support, in the same cut form used by
`graphConnected`.  Semantic loops do not cross cuts. -/
def Connected : Prop :=
  ∀ S : Finset (Fin n),
    (∃ inside outside : Fin n, inside ∈ S ∧ outside ∉ S) →
      ∃ inside ∈ S, ∃ outside ∉ S,
        0 < core.multiplicity inside outside

/-- Every topological vertex has valence at least three. -/
def Stable : Prop :=
  ∀ vertex : Fin n, 3 ≤ core.valence vertex

/-- Mathematical validity of a labelled pseudocore at cyclomatic genus `g`.

The edge equation is written without truncated natural subtraction, so it is
the exact Euler-characteristic identity at every genus. -/
def ValidAt (g : ℕ) : Prop :=
  core.MatrixWellFormed ∧
  core.Connected ∧
  core.Stable ∧
  core.edgeCount + 1 = n + g

/-- Backwards-compatible genus-four specialization of `ValidAt`. -/
def Valid : Prop :=
  core.ValidAt 4

/-- Executable exact matrix check. -/
def matrixCheck : Bool :=
  AffineCover.allFin (fun vertex : Fin n =>
    decide (core.multiplicity vertex vertex = 0)) &&
  AffineCover.allFin (fun first : Fin n =>
    AffineCover.allFin (fun second : Fin n =>
      decide (core.multiplicity first second =
        core.multiplicity second first)))

/-- Executable exact cut-connectedness check over all finite vertex subsets. -/
def connectedCheck : Bool :=
  AffineCover.allFinset (Finset.univ : Finset (Finset (Fin n))) fun S =>
    decide ((∃ inside outside : Fin n, inside ∈ S ∧ outside ∉ S) →
      ∃ inside ∈ S, ∃ outside ∉ S,
        0 < core.multiplicity inside outside)

/-- Executable exact stability check. -/
def stableCheck : Bool :=
  AffineCover.allFin fun vertex : Fin n =>
    decide (3 ≤ core.valence vertex)

/-- Complete executable checker at a requested cyclomatic genus. -/
def checkAt (g : ℕ) : Bool :=
  core.matrixCheck &&
  core.connectedCheck &&
  core.stableCheck &&
  decide (core.edgeCount + 1 = n + g)

/-- Backwards-compatible genus-four specialization of `checkAt`. -/
def check : Bool :=
  core.checkAt 4

@[simp] theorem matrixCheck_eq_true_iff :
    core.matrixCheck = true ↔ core.MatrixWellFormed := by
  simp [matrixCheck, MatrixWellFormed]

@[simp] theorem connectedCheck_eq_true_iff :
    core.connectedCheck = true ↔ core.Connected := by
  simp [connectedCheck, Connected]

@[simp] theorem stableCheck_eq_true_iff :
    core.stableCheck = true ↔ core.Stable := by
  simp [stableCheck, Stable]

/-- The finite Boolean checker at genus `g` implements `ValidAt g`. -/
@[simp] theorem checkAt_eq_true_iff (g : ℕ) :
    core.checkAt g = true ↔ core.ValidAt g := by
  simp [checkAt, ValidAt, and_assoc]

/-- The legacy validity predicate is exactly the genus-four specialization. -/
@[simp] theorem valid_iff_validAt_four :
    core.Valid ↔ core.ValidAt 4 :=
  Iff.rfl

/-- The legacy checker is exactly the genus-four specialization. -/
@[simp] theorem check_eq_true_iff :
    core.check = true ↔ core.Valid := by
  simpa only [check, Valid] using core.checkAt_eq_true_iff 4

/-- The cyclomatic genus of the loop-aware topological multigraph. -/
def topologicalGenus : ℤ :=
  (core.edgeCount : ℤ) - n + 1

/-- The checked edge-count identity is exactly the requested genus. -/
theorem topologicalGenus_eq {g : ℕ} (hValid : core.ValidAt g) :
    core.topologicalGenus = g := by
  have hEdges := hValid.2.2.2
  simp only [topologicalGenus]
  omega

/-- The legacy genus-four form of `topologicalGenus_eq`. -/
theorem topologicalGenus_eq_four (hValid : core.Valid) :
    core.topologicalGenus = 4 :=
  core.topologicalGenus_eq hValid

/-- A valid genus-four pseudocore has at least one vertex. -/
theorem vertexCount_pos_of_valid (hValid : core.Valid) : 0 < n := by
  by_contra hPositive
  have hn : n = 0 := Nat.eq_zero_of_not_pos hPositive
  subst n
  have hEdges := hValid.2.2.2
  simp [edgeCount, loopCount, nonloopEdgeCount] at hEdges

/-! ## Loopless split-core metadata -/

/-- Number of edge slots after replacing each semantic loop by two parallel
edges from its base vertex to a fresh marker. -/
def splitEdgeCount : ℕ :=
  core.nonloopEdgeCount + 2 * core.loopCount

/-- Splitting a semantic loop adds one marker vertex and one net edge. -/
theorem splitEdgeCount_eq_edgeCount_add_loopCount :
    core.splitEdgeCount = core.edgeCount + core.loopCount := by
  simp only [splitEdgeCount, edgeCount]
  omega

/-- Cyclomatic genus of the loopless split incidence data. -/
def splitTopologicalGenus : ℤ :=
  (core.splitEdgeCount : ℤ) - (n + core.loopCount : ℕ) + 1

/-- Loop splitting preserves the requested cyclomatic genus. -/
theorem splitTopologicalGenus_eq {g : ℕ} (hValid : core.ValidAt g) :
    core.splitTopologicalGenus = g := by
  rw [splitTopologicalGenus,
    core.splitEdgeCount_eq_edgeCount_add_loopCount]
  have hEdges := hValid.2.2.2
  push_cast
  omega

/-- The legacy genus-four form of `splitTopologicalGenus_eq`. -/
theorem splitTopologicalGenus_eq_four (hValid : core.Valid) :
    core.splitTopologicalGenus = 4 :=
  core.splitTopologicalGenus_eq hValid

/-- Original base vertices occupy the left summand of the split vertex type. -/
def baseVertex (vertex : Fin n) : Fin (n + core.loopCount) :=
  Fin.castAdd core.loopCount vertex

/-- Loop markers occupy the right summand of the split vertex type. -/
def markerVertex (marker : Fin core.loopCount) :
    Fin (n + core.loopCount) :=
  Fin.natAdd n marker

/-- Unordered edge multiplicity of an ordered-slot explicit-potential core. -/
def explicitCoreMultiplicity {vertexCount edgeCount : ℕ}
    (splitCore : ExplicitPotential.Core vertexCount edgeCount)
    (first second : Fin vertexCount) : ℕ :=
  (Finset.univ.filter fun edge : Fin edgeCount =>
    (splitCore.tail edge = first ∧ splitCore.head edge = second) ∨
    (splitCore.tail edge = second ∧ splitCore.head edge = first)).card

/-- Passive metadata for the canonical loopless split of a loop-aware core.
The actual marker order and edge-slot order are arbitrary and are checked from
the displayed functions. -/
structure SplitMetadata where
  markerBase : Fin core.loopCount → Fin n
  splitCore : ExplicitPotential.Core
    (n + core.loopCount) core.splitEdgeCount

namespace SplitMetadata

variable {core : Pseudocore n} (data : SplitMetadata core)

/-- Number of displayed markers attached to a base vertex. -/
def markerMultiplicity (vertex : Fin n) : ℕ :=
  (Finset.univ.filter fun marker : Fin core.loopCount =>
    data.markerBase marker = vertex).card

/-- Expected split multiplicity between two displayed split vertices. -/
def expectedMultiplicity
    (first second : Fin (n + core.loopCount)) : ℕ :=
  match (@finSumFinEquiv n core.loopCount).symm first,
      (@finSumFinEquiv n core.loopCount).symm second with
  | .inl firstBase, .inl secondBase =>
      core.multiplicity firstBase secondBase
  | .inl base, .inr marker =>
      if data.markerBase marker = base then 2 else 0
  | .inr marker, .inl base =>
      if data.markerBase marker = base then 2 else 0
  | .inr _, .inr _ => 0

/-- Exact mathematical relation between loop-aware data and its displayed
loopless ordered-slot split core at genus `g`. -/
def ValidAt (g : ℕ) : Prop :=
  core.ValidAt g ∧
  (∀ vertex : Fin n,
    data.markerMultiplicity vertex = core.loops vertex) ∧
  data.splitCore.Connected ∧
  (∀ edge : Fin core.splitEdgeCount,
    data.splitCore.tail edge ≠ data.splitCore.head edge) ∧
  ∀ first second : Fin (n + core.loopCount),
    explicitCoreMultiplicity data.splitCore first second =
      data.expectedMultiplicity first second

/-- Backwards-compatible genus-four specialization of `SplitMetadata.ValidAt`.
-/
def Valid : Prop :=
  data.ValidAt 4

/-- Exact finite checker for split-core metadata at genus `g`. -/
def checkAt (g : ℕ) : Bool :=
  core.checkAt g &&
  AffineCover.allFin (fun vertex : Fin n =>
    decide (data.markerMultiplicity vertex = core.loops vertex)) &&
  data.splitCore.connectedCheck &&
  AffineCover.allFin (fun edge : Fin core.splitEdgeCount =>
    decide (data.splitCore.tail edge ≠ data.splitCore.head edge)) &&
  AffineCover.allFin (fun first : Fin (n + core.loopCount) =>
    AffineCover.allFin (fun second : Fin (n + core.loopCount) =>
      decide (explicitCoreMultiplicity data.splitCore first second =
        data.expectedMultiplicity first second)))

/-- Backwards-compatible genus-four specialization of `SplitMetadata.checkAt`.
-/
def check : Bool :=
  data.checkAt 4

/-- The split metadata checker at genus `g` implements `ValidAt g`. -/
@[simp] theorem checkAt_eq_true_iff (g : ℕ) :
    data.checkAt g = true ↔ data.ValidAt g := by
  simp [checkAt, ValidAt, and_assoc]

/-- The legacy split validity predicate is its genus-four specialization. -/
@[simp] theorem valid_iff_validAt_four :
    data.Valid ↔ data.ValidAt 4 :=
  Iff.rfl

/-- The legacy split checker is its genus-four specialization. -/
@[simp] theorem check_eq_true_iff :
    data.check = true ↔ data.Valid := by
  simpa only [check, Valid] using data.checkAt_eq_true_iff 4

/-- A valid split certificate carries the requested genus through loop
splitting. -/
theorem splitTopologicalGenus_eq {g : ℕ} (hValid : data.ValidAt g) :
    core.splitTopologicalGenus = g :=
  core.splitTopologicalGenus_eq hValid.1

/-- Accepted split metadata is loopless as ordered edge-slot data. -/
theorem splitCore_loopless_of_valid (hValid : data.Valid)
    (edge : Fin core.splitEdgeCount) :
    data.splitCore.tail edge ≠ data.splitCore.head edge :=
  hValid.2.2.2.1 edge

/-- Accepted split metadata carries the core connectedness required by the
explicit-potential bundle checker. -/
theorem splitCore_connected_of_valid (hValid : data.Valid) :
    data.splitCore.Connected :=
  hValid.2.2.1

end SplitMetadata

end Pseudocore

/-! ## Closed regressions -/

/-- A loop-aware pseudocore with two base vertices, one loop at each, and three
nonloop parallel edges. -/
private def core005 : Pseudocore 2 where
  loops := ![1, 1]
  multiplicity := ![![0, 3], ![3, 0]]

example : core005.check = true := by decide

example : core005.Valid := by
  exact core005.check_eq_true_iff.mp (by decide)

/-- Its standard loopless split has two marker vertices and seven edge slots. -/
private def core005Split : core005.SplitMetadata where
  markerBase := ![0, 1]
  splitCore := {
    tail := ![0, 0, 0, 0, 0, 1, 1]
    head := ![1, 1, 1, 2, 2, 3, 3]
  }

example : core005Split.check = true := by decide

example : core005Split.Valid := by
  exact core005Split.check_eq_true_iff.mp (by decide)

/-- Asymmetry in the redundant full matrix is rejected. -/
private def asymmetric : Pseudocore 2 where
  loops := ![1, 1]
  multiplicity := ![![0, 3], ![2, 0]]

example : asymmetric.check = false := by decide

end Utilities.Certificate.GenusFourPseudocore
