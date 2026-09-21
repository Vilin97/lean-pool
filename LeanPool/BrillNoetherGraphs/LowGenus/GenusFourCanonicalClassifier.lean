/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.LowGenus.Generated.GenusFourCanonicalClassifierData
import LeanPool.BrillNoetherGraphs.LowGenus.GenusFourCubicAtlas
import LeanPool.BrillNoetherGraphs.Utilities.Certificate.CubicMatrixCanonical
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreRelabeling

/-!
# The public genus-four cubic classifier

Every connected loopless cubic core on six vertices is relabeled to one of
the six rows in `GenusFourCubicAtlas.atlas`.  The proof uses the generic
canonical-matrix traversal and a small generated payload table, but no replay
tree, `native_decide`, private import, or unproved hypothesis.
-/
namespace AtanasovRanganathan.GenusFourCanonicalClassifier

open Utilities
open Utilities.Certificate
open Utilities.Certificate.CubicMatrixReplay
open AtanasovRanganathan.Generated.GenusFourCanonicalClassifierData
open AtanasovRanganathan.GenusFourCubicAtlas

/-! ## The emitted atlas tables are the public rows -/
theorem atlasTable_row095 : ∀ a b : Fin 6,
    atlasTable 0 a b = row095.core.pairMultiplicity a b := by
  decide
theorem atlasTable_row096 : ∀ a b : Fin 6,
    atlasTable 1 a b = row096.core.pairMultiplicity a b := by
  decide
theorem atlasTable_row097 : ∀ a b : Fin 6,
    atlasTable 2 a b = row097.core.pairMultiplicity a b := by
  decide
theorem atlasTable_row098 : ∀ a b : Fin 6,
    atlasTable 3 a b = row098.core.pairMultiplicity a b := by
  decide
theorem atlasTable_row099 : ∀ a b : Fin 6,
    atlasTable 4 a b = row099.core.pairMultiplicity a b := by
  decide
theorem atlasTable_row100 : ∀ a b : Fin 6,
    atlasTable 5 a b = row100.core.pairMultiplicity a b := by
  decide

/-! ## Leaf checking and decoding -/

/-- Decide a payload hit by checking injectivity and all table entries; a miss
is accepted only when the leaf matrix is disconnected. -/
def payloadDecide (rows : List (List ℕ)) : Option Payload → Bool
  | some (idx, p) =>
      decide (∀ i j : Fin 6, p i = p j → i = j) &&
        decide (∀ i j : Fin 6,
          entryOf rows (i : ℕ) (j : ℕ) = atlasTable idx (p i) (p j))
  | none => decide (¬ MatrixConnected 6 (entryOf rows))

/-- Look up and check the payload belonging to a leaf's own row list. -/
def leafDecide (rows : List (List ℕ)) : Bool :=
  payloadDecide rows (List.lookup (rowKey rows) payloadTable)
/-- The entire pruned six-vertex traversal passes by kernel reduction. -/
theorem pruned_valid :
    prunedCheck canonicalPrefix leafDecide 7 (List.replicate 6 3) [] = true := by
  decide

/-- Decode an accepted connected leaf to one of the six public atlas rows. -/
theorem decode (rows : List (List ℕ)) (hLeaf : leafDecide rows = true)
    (hConnected : MatrixConnected 6 (entryOf rows)) :
    ∃ row ∈ atlas, ∃ vertexEquiv : Fin 6 ≃ Fin 6,
      ∀ i j : Fin 6, entryOf rows (i : ℕ) (j : ℕ) =
        row.core.pairMultiplicity (vertexEquiv i) (vertexEquiv j) := by
  rw [leafDecide] at hLeaf
  cases hLookup : List.lookup (rowKey rows) payloadTable with
  | none =>
      rw [hLookup] at hLeaf
      exfalso
      have hNot : ¬ MatrixConnected 6 (entryOf rows) := by
        simpa [payloadDecide] using hLeaf
      exact hNot hConnected
  | some pair =>
      obtain ⟨idx, p⟩ := pair
      rw [hLookup] at hLeaf
      rw [payloadDecide, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        at hLeaf
      obtain ⟨hInjective, hMatch⟩ := hLeaf
      have hBij : Function.Bijective p :=
        Finite.injective_iff_bijective.mp (fun i j hij => hInjective i j hij)
      fin_cases idx
      · refine ⟨row095, by simp [atlas], Equiv.ofBijective p hBij, fun i j => ?_⟩
        rw [hMatch i j]
        exact atlasTable_row095 (p i) (p j)
      · refine ⟨row096, by simp [atlas], Equiv.ofBijective p hBij, fun i j => ?_⟩
        rw [hMatch i j]
        exact atlasTable_row096 (p i) (p j)
      · refine ⟨row097, by simp [atlas], Equiv.ofBijective p hBij, fun i j => ?_⟩
        rw [hMatch i j]
        exact atlasTable_row097 (p i) (p j)
      · refine ⟨row098, by simp [atlas], Equiv.ofBijective p hBij, fun i j => ?_⟩
        rw [hMatch i j]
        exact atlasTable_row098 (p i) (p j)
      · refine ⟨row099, by simp [atlas], Equiv.ofBijective p hBij, fun i j => ?_⟩
        rw [hMatch i j]
        exact atlasTable_row099 (p i) (p j)
      · refine ⟨row100, by simp [atlas], Equiv.ofBijective p hBij, fun i j => ?_⟩
        rw [hMatch i j]
        exact atlasTable_row100 (p i) (p j)

/-! ## Public completeness theorems -/

/-- Every connected loopless cubic core on six vertices has the unordered
multiplicity table of one of the six public atlas rows. -/
theorem genusFourCubicPairMultiplicityComplete
    (candidate : Utilities.Certificate.ExplicitPotential.Core 6 9)
    (hConnected : candidate.Connected)
    (hLoopless : ∀ edge : Fin 9, candidate.tail edge ≠ candidate.head edge)
    (hCubic : candidate.Cubic) :
    ∃ row ∈ atlas, ∃ vertexEquiv : Fin 6 ≃ Fin 6,
      ∀ i j : Fin 6, candidate.pairMultiplicity i j =
        row.core.pairMultiplicity (vertexEquiv i) (vertexEquiv j) := by
  obtain ⟨sigma, hCanonicalConnected, hCanonicalDegree, hCanonical,
      hRelabel⟩ :=
    exists_canonical_relabel candidate hConnected hCubic
  let other := candidate.relabel sigma
  have hOtherLoopless :
      ∀ edge : Fin 9, other.tail edge ≠ other.head edge :=
    Utilities.Certificate.ExplicitPotential.Core.relabel_loopless
      candidate sigma hLoopless
  have hConditions : Conditions 6 3 (matrixOf other) :=
    conditions_matrixOf other hOtherLoopless hCanonicalDegree
  have hFollows :
      Follows (List.replicate 6 3) (rowsOf (matrixOf other) 0 6) := by
    have h := follows_capsOf_rowsOf hConditions 6 0 (by omega)
    simpa [capsOf_zero] using h
  have hLeaf :=
    prunedCheck_sound canonicalPrefix leafDecide hFollows 7 [] pruned_valid
      (acceptsAlong_canonicalPrefix _ hCanonical)
  rw [List.nil_append] at hLeaf
  have hEntries : ∀ i j, i < 6 → j < 6 →
      matrixOf other i j = entryOf (rowsOf (matrixOf other) 0 6) i j :=
    fun i j hi hj => (entryOf_rowsOf hConditions i j hi hj).symm
  obtain ⟨row, hRow, vertexEquiv, hMatch⟩ :=
    decode _ hLeaf
      (matrixConnected_congr hEntries
        (matrixConnected_matrixOf other hCanonicalConnected))
  refine ⟨row, hRow, sigma.trans vertexEquiv, fun i j => ?_⟩
  rw [hRelabel i j]
  have hij := hMatch (sigma i) (sigma j)
  rw [entryOf_rowsOf hConditions (sigma i : ℕ) (sigma j : ℕ)
    (sigma i).isLt (sigma j).isLt] at hij
  simpa [other, matrixOf, (sigma i).isLt, (sigma j).isLt] using hij

/-- The multiplicity match lifts to an occurrence-sensitive core relabeling,
the form used by closed-face transport. -/
theorem genusFourCubicRelabelingComplete
    (candidate : Utilities.Certificate.ExplicitPotential.Core 6 9)
    (hConnected : candidate.Connected)
    (hLoopless : ∀ edge : Fin 9, candidate.tail edge ≠ candidate.head edge)
    (hCubic : candidate.Cubic) :
    ∃ row ∈ atlas, Nonempty (candidate.Relabeling row.core) := by
  obtain ⟨row, hRow, vertexEquiv, hMultiplicity⟩ :=
    genusFourCubicPairMultiplicityComplete candidate hConnected hLoopless hCubic
  exact ⟨row, hRow,
    Utilities.Certificate.ExplicitPotential.Core.nonempty_relabeling_of_pairMultiplicity_eq
      candidate row.core hLoopless vertexEquiv hMultiplicity⟩

end AtanasovRanganathan.GenusFourCanonicalClassifier
