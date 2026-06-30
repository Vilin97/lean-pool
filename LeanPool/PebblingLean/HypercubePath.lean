/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import LeanPool.PebblingLean.Hypercube
import LeanPool.PebblingLean.Delivery

/-!
# Paths in hypercubes

This file connects Hamming distance to the graph-walk API: vertices at Hamming
distance `d` are joined by a walk of length `d`.  This is the geometric input
needed for direct delivery in the upper-bound proof.
-/

namespace PebblingLean

namespace Hypercube

open Pebbling

@[simp]
theorem fromDiffSet_empty {n : ℕ} (base : HypercubeVertex n) :
    fromDiffSet base ∅ = base := by
  funext i
  simp [fromDiffSet]

theorem diffSet_fromDiffSet_insert {n : ℕ} (base : HypercubeVertex n)
    {s : Finset (Fin n)} {i : Fin n} (hi : i ∉ s) :
    diffSet (fromDiffSet base s) (fromDiffSet base (insert i s)) = {i} := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [diffSet, fromDiffSet, hi]
  · have hj_insert : j ∈ insert i s ↔ j ∈ s := by
      simp [hji]
    by_cases hjs : j ∈ s
    · simp [diffSet, fromDiffSet, hji, hjs]
    · simp [diffSet, fromDiffSet, hji, hjs]

/-- Flipping one new coordinate gives an adjacent hypercube vertex. -/
theorem adj_fromDiffSet_insert {n : ℕ} (base : HypercubeVertex n)
    {s : Finset (Fin n)} {i : Fin n} (hi : i ∉ s) :
    (graph n).Adj (fromDiffSet base s) (fromDiffSet base (insert i s)) := by
  simp [graph, dist_eq_card_diffSet, diffSet_fromDiffSet_insert base hi]

/-- Flipping the coordinates in `s`, one at a time, gives a walk back to the
base vertex of length `s.card`. -/
theorem exists_walk_fromDiffSet_to_base {n : ℕ} (base : HypercubeVertex n)
    (s : Finset (Fin n)) :
    ∃ walk : (graph n).Walk (fromDiffSet base s) base, walk.length = s.card := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · refine ⟨Graph.Walk.nil base, ?_⟩
    simp [Graph.Walk.length]
  · intro i s hi ih
    rcases ih with ⟨tail, htail⟩
    refine ⟨Graph.Walk.cons ((graph n).symm (adj_fromDiffSet_insert base hi)) tail, ?_⟩
    simp [Graph.Walk.length, htail, Finset.card_insert_of_notMem hi]

/-- Hypercube Hamming distance is realized by a graph walk of the same length. -/
theorem exists_walk_length_dist {n : ℕ} (x y : HypercubeVertex n) :
    ∃ walk : (graph n).Walk x y, walk.length = dist x y := by
  classical
  rcases exists_walk_fromDiffSet_to_base x (diffSet x y) with ⟨walkToBase, hlen⟩
  have htarget : fromDiffSet x (diffSet x y) = y := fromDiffSet_diffSet x y
  rw [← htarget]
  refine ⟨Graph.Walk.reverse (graph n) walkToBase, ?_⟩
  simp [Graph.Walk.length_reverse, hlen, dist_eq_card_diffSet]

/-- A single pile of `T * 2^d` pebbles can directly deliver `T` pebbles across
Hamming distance `d`. -/
theorem canReachAtLeast_single_dist {n : ℕ} (center target : HypercubeVertex n)
    (T : ℕ) :
    CanReachAtLeast (graph n)
      (Pebbling.single center (T * 2 ^ dist center target)) target T := by
  rcases exists_walk_length_dist center target with ⟨walk, hwalk⟩
  simpa [hwalk] using Pebbling.canReachAtLeast_single_of_walk walk T

end Hypercube

end PebblingLean
