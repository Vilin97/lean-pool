/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.Basic
import LeanPool.Erdos132ConvexK3.Majorants
import LeanPool.Erdos132ConvexK3.RegressionWitnesses
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

/-!
# Global ErLV reduction interface

This file starts the missing global bridge in draft Section 3.  It fixes the
cyclic notions used by the Erdos--Lovasz--Vesztergombi maximal-gap choice and
states cover moves with squared distances, whose strict order agrees with the
underlying Euclidean distances.

The primary-source convention is oriented: for an edge `ij`, a left cover
retreats `i` by one polygon side and a right cover advances `j` by one side.
The number of such moves is therefore exactly the side-count convention used
by `K3Majorant.leftMoves/rightMoves`.
-/

namespace LeanPool.Erdos132ConvexK3

/-- Advance by `k` polygon sides in the fixed cyclic labelling. -/
def cyclicAdvance {n : ℕ} [NeZero n] (i : Fin n) (k : ℕ) : Fin n :=
  i + Fin.ofNat n k

/-- Retreat by `k` polygon sides in the fixed cyclic labelling. -/
def cyclicRetreat {n : ℕ} [NeZero n] (i : Fin n) (k : ℕ) : Fin n :=
  i - Fin.ofNat n k

@[simp] theorem cyclicAdvance_zero {n : ℕ} [NeZero n] (i : Fin n) :
    cyclicAdvance i 0 = i := by
  simp [cyclicAdvance]

@[simp] theorem cyclicRetreat_zero {n : ℕ} [NeZero n] (i : Fin n) :
    cyclicRetreat i 0 = i := by
  simp [cyclicRetreat]

theorem cyclicAdvance_add {n : ℕ} [NeZero n] (i : Fin n) (a b : ℕ) :
    cyclicAdvance (cyclicAdvance i a) b = cyclicAdvance i (a + b) := by
  have hof : Fin.ofNat n (a + b) = Fin.ofNat n a + Fin.ofNat n b := by
    apply Fin.ext
    simp [Fin.ofNat, Fin.val_add, Nat.add_mod]
  simp only [cyclicAdvance, hof]
  abel

theorem cyclicRetreat_add {n : ℕ} [NeZero n] (i : Fin n) (a b : ℕ) :
    cyclicRetreat (cyclicRetreat i a) b = cyclicRetreat i (a + b) := by
  have hof : Fin.ofNat n (a + b) = Fin.ofNat n a + Fin.ofNat n b := by
    apply Fin.ext
    simp [Fin.ofNat, Fin.val_add, Nat.add_mod]
  simp only [cyclicRetreat, hof]
  abel

/-- Nonzero counterclockwise offsets from `v` that lead to a neighbor in
`G(S,3)`.  The order on `Fin n` is the order of representatives
`0,1,...,n-1`, so its minimum is the first counterclockwise neighbor. -/
noncomputable def ccwNeighborOffsets
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) (v : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k ↦
    k ≠ 0 ∧ TopThreeAdjacent P d₁ d₂ d₃ v (cyclicAdvance v k.val)

/-- Nonzero clockwise offsets from `v` that lead to a graph neighbor. -/
noncomputable def cwNeighborOffsets
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) (v : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun k ↦
    k ≠ 0 ∧ TopThreeAdjacent P d₁ d₂ d₃ v (cyclicRetreat v k.val)

/-- First counterclockwise neighbor offset; zero is the explicit sentinel
when the vertex is isolated. -/
noncomputable def firstNeighborOffset
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) (v : Fin n) : Fin n := by
  classical
  let S := ccwNeighborOffsets P d₁ d₂ d₃ v
  exact if h : S.Nonempty then S.min' h else 0

/-- First clockwise neighbor offset, with zero as the isolated sentinel. -/
noncomputable def firstClockwiseNeighborOffset
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) (v : Fin n) : Fin n := by
  classical
  let S := cwNeighborOffsets P d₁ d₂ d₃ v
  exact if h : S.Nonempty then S.min' h else 0

/-- The first-neighbor gap `g(v)`, measured in polygon sides. -/
noncomputable def firstNeighborGap
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) (v : Fin n) : ℕ :=
  (firstNeighborOffset P d₁ d₂ d₃ v).val

/-- First counterclockwise graph neighbor, with the vertex itself as the
isolated-vertex sentinel. -/
noncomputable def firstCounterclockwiseNeighbor
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) (v : Fin n) : Fin n :=
  cyclicAdvance v (firstNeighborGap P d₁ d₂ d₃ v)

/-- First clockwise graph neighbor, with the vertex itself as the
isolated-vertex sentinel. -/
noncomputable def firstClockwiseNeighbor
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) (v : Fin n) : Fin n :=
  cyclicRetreat v (firstClockwiseNeighborOffset P d₁ d₂ d₃ v).val

/-- Strictly increasing a top-three edge produces another top-three edge.
This is the rank fact behind termination of the primary-source cover process. -/
theorem top_three_adjacent_of_strictly_longer
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j p q : Fin n}
    (hij : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (hgrow : sqDist (P i) (P j) < sqDist (P p) (P q)) :
    TopThreeAdjacent P d₁ d₂ d₃ p q := by
  have hpq : p ≠ q := by
    intro hpq
    subst q
    have hself : sqDist (P p) (P p) = 0 := by simp [sqDist]
    rw [hself] at hgrow
    exact (not_lt_of_ge (sqDist_nonneg (P i) (P j)) hgrow)
  have hnew := top_three_class_bounds_of_ne hClasses hpq
  refine ⟨hpq, ?_⟩
  rcases hij.2 with hold | hold | hold
  · exfalso
    linarith [hnew.1]
  · by_cases h1 : sqDist (P p) (P q) = d₁
    · exact Or.inl h1
    · have hlt1 : sqDist (P p) (P q) < d₁ := lt_of_le_of_ne hnew.1 h1
      exact (not_lt_of_ge (hnew.2.1 hlt1) (by linarith)).elim
  · by_cases h1 : sqDist (P p) (P q) = d₁
    · exact Or.inl h1
    · have hlt1 : sqDist (P p) (P q) < d₁ := lt_of_le_of_ne hnew.1 h1
      have hle2 := hnew.2.1 hlt1
      by_cases h2 : sqDist (P p) (P q) = d₂
      · exact Or.inr (Or.inl h2)
      · have hlt2 : sqDist (P p) (P q) < d₂ := lt_of_le_of_ne hle2 h2
        exact (not_lt_of_ge (hnew.2.2 hlt2) (by linarith)).elim

theorem topThreeAdjacent_symm
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {i j : Fin n}
    (h : TopThreeAdjacent P d₁ d₂ d₃ i j) :
    TopThreeAdjacent P d₁ d₂ d₃ j i :=
  (topThreeGraph P d₁ d₂ d₃).symm.symm i j h

/-- Positive degree makes the first-neighbor offset set nonempty. -/
theorem ccwNeighborOffsets_nonempty_of_degree_pos
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (hdegree : 0 < vertexDegree P d₁ d₂ d₃ v) :
    (ccwNeighborOffsets P d₁ d₂ d₃ v).Nonempty := by
  classical
  unfold vertexDegree at hdegree
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hdegree
  have hjData := Finset.mem_filter.mp hj
  have hjErase := Finset.mem_erase.mp hjData.1
  let k : Fin n := j - v
  have hk0 : k ≠ 0 := by
    dsimp [k]
    exact sub_ne_zero.mpr hjErase.1
  have hkCast : Fin.ofNat n k.val = k := by
    apply Fin.ext
    simp
  have hvk : cyclicAdvance v k.val = j := by
    rw [cyclicAdvance, hkCast]
    dsimp [k]
    abel
  refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0, ?_⟩⟩
  rw [hvk]
  exact ⟨hjErase.1.symm, hjData.2⟩

theorem cwNeighborOffsets_nonempty_of_degree_pos
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (hdegree : 0 < vertexDegree P d₁ d₂ d₃ v) :
    (cwNeighborOffsets P d₁ d₂ d₃ v).Nonempty := by
  classical
  unfold vertexDegree at hdegree
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hdegree
  have hjData := Finset.mem_filter.mp hj
  have hjErase := Finset.mem_erase.mp hjData.1
  let k : Fin n := v - j
  have hk0 : k ≠ 0 := by
    dsimp [k]
    exact sub_ne_zero.mpr hjErase.1.symm
  have hkCast : Fin.ofNat n k.val = k := by
    apply Fin.ext
    simp
  have hvk : cyclicRetreat v k.val = j := by
    rw [cyclicRetreat, hkCast]
    dsimp [k]
    abel
  refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0, ?_⟩⟩
  rw [hvk]
  exact ⟨hjErase.1.symm, hjData.2⟩

/-- With a nonempty neighbor-offset set, the selected offset is one of its
members and therefore is the genuine first counterclockwise graph neighbor. -/
theorem firstNeighborOffset_mem
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (h : (ccwNeighborOffsets P d₁ d₂ d₃ v).Nonempty) :
    firstNeighborOffset P d₁ d₂ d₃ v ∈ ccwNeighborOffsets P d₁ d₂ d₃ v := by
  classical
  unfold firstNeighborOffset
  dsimp only
  rw [dite_eq_left h]
  exact Finset.min'_mem _ _

theorem firstClockwiseNeighborOffset_mem
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (h : (cwNeighborOffsets P d₁ d₂ d₃ v).Nonempty) :
    firstClockwiseNeighborOffset P d₁ d₂ d₃ v ∈ cwNeighborOffsets P d₁ d₂ d₃ v := by
  classical
  unfold firstClockwiseNeighborOffset
  dsimp only
  rw [dite_eq_left h]
  exact Finset.min'_mem _ _

/-- Positive degree gives a nonzero first-neighbor gap and an actual graph
neighbor at that cyclic offset. -/
theorem firstNeighborOffset_spec_of_degree_pos
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (hdegree : 0 < vertexDegree P d₁ d₂ d₃ v) :
    firstNeighborOffset P d₁ d₂ d₃ v ≠ 0 ∧
      TopThreeAdjacent P d₁ d₂ d₃ v
        (cyclicAdvance v (firstNeighborGap P d₁ d₂ d₃ v)) := by
  classical
  have hnonempty := ccwNeighborOffsets_nonempty_of_degree_pos hdegree
  have hmem := firstNeighborOffset_mem hnonempty
  exact (Finset.mem_filter.mp hmem).2

theorem firstCounterclockwiseNeighbor_adjacent_of_degree_pos
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (hdegree : 0 < vertexDegree P d₁ d₂ d₃ v) :
    TopThreeAdjacent P d₁ d₂ d₃ v
      (firstCounterclockwiseNeighbor P d₁ d₂ d₃ v) := by
  exact (firstNeighborOffset_spec_of_degree_pos hdegree).2

theorem firstClockwiseNeighbor_adjacent_of_degree_pos
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {v : Fin n}
    (hdegree : 0 < vertexDegree P d₁ d₂ d₃ v) :
    TopThreeAdjacent P d₁ d₂ d₃ v
      (firstClockwiseNeighbor P d₁ d₂ d₃ v) := by
  classical
  have hnonempty := cwNeighborOffsets_nonempty_of_degree_pos hdegree
  have hmem := firstClockwiseNeighborOffset_mem hnonempty
  exact (Finset.mem_filter.mp hmem).2.2

/-- Every finite cyclic configuration admits a vertex maximizing the chosen
first-neighbor gap (including the isolated-vertex sentinel convention). -/
theorem exists_maximal_firstNeighborGap
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ) :
    ∃ x : Fin n, ∀ v : Fin n,
      firstNeighborGap P d₁ d₂ d₃ v ≤ firstNeighborGap P d₁ d₂ d₃ x := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.exists_max_image Finset.univ
    (firstNeighborGap P d₁ d₂ d₃) ⟨0, Finset.mem_univ _⟩
  exact ⟨x, fun v ↦ hx v (Finset.mem_univ _)⟩

/-- A primary-source left cover of the oriented edge `ij`: retreating the
left endpoint by one side strictly increases the squared distance. -/
def IsLeftCover
    {K : Type*} [Ring K] [LT K] {n : ℕ} [NeZero n]
    (P : Fin n → Point K) (i j : Fin n) : Prop :=
  sqDist (P i) (P j) < sqDist (P (cyclicRetreat i 1)) (P j)

/-- A primary-source right cover of the oriented edge `ij`: advancing the
right endpoint by one side strictly increases the squared distance. -/
def IsRightCover
    {K : Type*} [Ring K] [LT K] {n : ℕ} [NeZero n]
    (P : Fin n → Point K) (i j : Fin n) : Prop :=
  sqDist (P i) (P j) < sqDist (P i) (P (cyclicAdvance j 1))

/-- An oriented edge is a majorant when neither legal endpoint cover raises
its distance. -/
def IsMajorant
    {K : Type*} [Ring K] [LT K] {n : ℕ} [NeZero n]
    (P : Fin n → Point K) (i j : Fin n) : Prop :=
  ¬IsLeftCover P i j ∧ ¬IsRightCover P i j

/-- An actual sequence of strict ErLV cover moves.  The indices count moves
at the left and right endpoints; their order is retained by the proof tree.
This prevents a terminal edge with compatible endpoint counts from being
mistaken for a majorant reached from the stated starting edge. -/
inductive K3CoverSequence
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) :
    Fin n → Fin n → ℕ → ℕ → Prop where
  | nil (i j : Fin n) : K3CoverSequence P i j 0 0
  | left {i j : Fin n} {leftMoves rightMoves : ℕ}
      (hCover : IsLeftCover P i j)
      (tail : K3CoverSequence P (cyclicRetreat i 1) j leftMoves rightMoves) :
      K3CoverSequence P i j (leftMoves + 1) rightMoves
  | right {i j : Fin n} {leftMoves rightMoves : ℕ}
      (hCover : IsRightCover P i j)
      (tail : K3CoverSequence P i (cyclicAdvance j 1) leftMoves rightMoves) :
      K3CoverSequence P i j leftMoves (rightMoves + 1)

/-- Kernel counterexample to the stronger but non-source claim that every
non-diameter top-three edge admits a cover.  In the exact attempt-2 heptagon,
the `d₂` edge `(0,5)` is already a majorant: both permitted endpoint moves
strictly shorten it.  ErLV majorant existence therefore uses finite rank
ascent with a terminal case; it does not use such a universal extension
lemma. -/
theorem heptagon_nondiameter_edge_is_majorant :
    CyclicStrictConvex Witnesses.heptagon ∧
      HasTopThreeDistanceClasses Witnesses.heptagon 7225 6649 5353 ∧
      sqDist (Witnesses.heptagon 0) (Witnesses.heptagon 5) = 6649 ∧
      (6649 : ℚ) ≠ 7225 ∧ IsMajorant Witnesses.heptagon 0 5 := by
  have hcur : sqDist (Witnesses.heptagon 0) (Witnesses.heptagon 5) = 6649 :=
    Witnesses.heptagon_double_ladder.2.1
  have hright : sqDist (Witnesses.heptagon 0) (Witnesses.heptagon 6) = 5353 :=
    Witnesses.heptagon_double_ladder.1
  have hleft : sqDist (Witnesses.heptagon 6) (Witnesses.heptagon 5) = 74 := by
    change ((32 : ℚ) - 27) ^ 2 + (75 - 68) ^ 2 = 74
    norm_num
  refine ⟨Witnesses.heptagon_strict_convex, Witnesses.heptagon_top_three,
    hcur, by norm_num, ?_⟩
  constructor
  · intro hCover
    change sqDist (Witnesses.heptagon 0) (Witnesses.heptagon 5) <
      sqDist (Witnesses.heptagon 6) (Witnesses.heptagon 5) at hCover
    linarith
  · intro hCover
    change sqDist (Witnesses.heptagon 0) (Witnesses.heptagon 5) <
      sqDist (Witnesses.heptagon 0) (Witnesses.heptagon 6) at hCover
    linarith

/-- Endpoint counts and terminal edge produced by the cover process. -/
structure K3MajorantWitness
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (i j : Fin n) where
  /-- Number of cover moves made at the left endpoint. -/
  leftMoves : ℕ
  /-- Number of cover moves made at the right endpoint. -/
  rightMoves : ℕ
  coverBudget : leftMoves + rightMoves ≤ 2
  path : K3CoverSequence P i j leftMoves rightMoves
  adjacent : TopThreeAdjacent P d₁ d₂ d₃
    (cyclicRetreat i leftMoves) (cyclicAdvance j rightMoves)
  terminal : IsMajorant P
    (cyclicRetreat i leftMoves) (cyclicAdvance j rightMoves)

/-- A left cover preserves membership in the top-three graph. -/
theorem left_cover_top_three_adjacent
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hAdj : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (hCover : IsLeftCover P i j) :
    TopThreeAdjacent P d₁ d₂ d₃ (cyclicRetreat i 1) j :=
  top_three_adjacent_of_strictly_longer hClasses hAdj hCover

/-- A right cover preserves membership in the top-three graph. -/
theorem right_cover_top_three_adjacent
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hAdj : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (hCover : IsRightCover P i j) :
    TopThreeAdjacent P d₁ d₂ d₃ i (cyclicAdvance j 1) :=
  top_three_adjacent_of_strictly_longer hClasses hAdj hCover

/-- Two strict cover moves among exactly three distance ranks must end in
the largest class. -/
theorem two_covers_end_at_d₁
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i₀ j₀ i₁ j₁ i₂ j₂ : Fin n}
    (h₀ : TopThreeAdjacent P d₁ d₂ d₃ i₀ j₀)
    (h₁ : TopThreeAdjacent P d₁ d₂ d₃ i₁ j₁)
    (h₂ : TopThreeAdjacent P d₁ d₂ d₃ i₂ j₂)
    (hgrow₁ : sqDist (P i₀) (P j₀) < sqDist (P i₁) (P j₁))
    (hgrow₂ : sqDist (P i₁) (P j₁) < sqDist (P i₂) (P j₂)) :
    sqDist (P i₂) (P j₂) = d₁ := by
  rcases hClasses with ⟨hd₃d₂, hd₂d₁, _, _, _, _⟩
  rcases h₀.2 with h₀ | h₀ | h₀ <;>
    rcases h₁.2 with h₁ | h₁ | h₁ <;>
      rcases h₂.2 with h₂ | h₂ | h₂ <;> linarith

/-- A diameter-class edge is terminal for the cover process because every
interpoint squared distance is at most `d₁`. -/
theorem d₁_edge_is_majorant
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hAdj : TopThreeAdjacent P d₁ d₂ d₃ i j)
    (hd₁ : sqDist (P i) (P j) = d₁) : IsMajorant P i j := by
  constructor
  · intro hCover
    have hNext := left_cover_top_three_adjacent hClasses hAdj hCover
    have hBound := top_three_class_bounds_of_ne hClasses hNext.1
    unfold IsLeftCover at hCover
    dsimp only at hBound
    linarith [hBound.1]
  · intro hCover
    have hNext := right_cover_top_three_adjacent hClasses hAdj hCover
    have hBound := top_three_class_bounds_of_ne hClasses hNext.1
    unfold IsRightCover at hCover
    dsimp only at hBound
    linarith [hBound.1]

theorem left_or_right_cover_of_not_majorant
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {i j : Fin n}
    (h : ¬IsMajorant P i j) : IsLeftCover P i j ∨ IsRightCover P i j := by
  unfold IsMajorant at h
  tauto

/-- Primary-source majorant existence for `G(S,3)`: strict covers stay in
the top-three graph and at most two such rank raises are possible. -/
theorem exists_k3_majorant
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    {i j : Fin n} (hStart : TopThreeAdjacent P d₁ d₂ d₃ i j) :
    Nonempty (K3MajorantWitness P d₁ d₂ d₃ i j) := by
  classical
  by_cases hMajorant₀ : IsMajorant P i j
  · exact ⟨{
      leftMoves := 0
      rightMoves := 0
      coverBudget := by omega
      path := .nil i j
      adjacent := by simpa using hStart
      terminal := by simpa using hMajorant₀ }⟩
  rcases left_or_right_cover_of_not_majorant hMajorant₀ with hLeft₀ | hRight₀
  · have hAdj₁ := left_cover_top_three_adjacent hClasses hStart hLeft₀
    by_cases hMajorant₁ : IsMajorant P (cyclicRetreat i 1) j
    · exact ⟨{
        leftMoves := 1
        rightMoves := 0
        coverBudget := by omega
        path := .left hLeft₀ (.nil _ _)
        adjacent := by simpa using hAdj₁
        terminal := by simpa using hMajorant₁ }⟩
    rcases left_or_right_cover_of_not_majorant hMajorant₁ with hLeft₁ | hRight₁
    · have hAdj₂ := left_cover_top_three_adjacent hClasses hAdj₁ hLeft₁
      have hd₁ := two_covers_end_at_d₁ hClasses hStart hAdj₁ hAdj₂ hLeft₀ hLeft₁
      have hMajorant₂ := d₁_edge_is_majorant hClasses hAdj₂ hd₁
      exact ⟨{
        leftMoves := 2
        rightMoves := 0
        coverBudget := by omega
        path := .left hLeft₀ (.left hLeft₁ (.nil _ _))
        adjacent := by
          simpa [cyclicRetreat_add] using hAdj₂
        terminal := by
          simpa [cyclicRetreat_add] using hMajorant₂ }⟩
    · have hAdj₂ := right_cover_top_three_adjacent hClasses hAdj₁ hRight₁
      have hd₁ := two_covers_end_at_d₁ hClasses hStart hAdj₁ hAdj₂ hLeft₀ hRight₁
      have hMajorant₂ := d₁_edge_is_majorant hClasses hAdj₂ hd₁
      exact ⟨{
        leftMoves := 1
        rightMoves := 1
        coverBudget := by omega
        path := .left hLeft₀ (.right hRight₁ (.nil _ _))
        adjacent := hAdj₂
        terminal := hMajorant₂ }⟩
  · have hAdj₁ := right_cover_top_three_adjacent hClasses hStart hRight₀
    by_cases hMajorant₁ : IsMajorant P i (cyclicAdvance j 1)
    · exact ⟨{
        leftMoves := 0
        rightMoves := 1
        coverBudget := by omega
        path := .right hRight₀ (.nil _ _)
        adjacent := by simpa using hAdj₁
        terminal := by simpa using hMajorant₁ }⟩
    rcases left_or_right_cover_of_not_majorant hMajorant₁ with hLeft₁ | hRight₁
    · have hAdj₂ := left_cover_top_three_adjacent hClasses hAdj₁ hLeft₁
      have hd₁ := two_covers_end_at_d₁ hClasses hStart hAdj₁ hAdj₂ hRight₀ hLeft₁
      have hMajorant₂ := d₁_edge_is_majorant hClasses hAdj₂ hd₁
      exact ⟨{
        leftMoves := 1
        rightMoves := 1
        coverBudget := by omega
        path := .right hRight₀ (.left hLeft₁ (.nil _ _))
        adjacent := hAdj₂
        terminal := hMajorant₂ }⟩
    · have hAdj₂ := right_cover_top_three_adjacent hClasses hAdj₁ hRight₁
      have hd₁ := two_covers_end_at_d₁ hClasses hStart hAdj₁ hAdj₂ hRight₀ hRight₁
      have hMajorant₂ := d₁_edge_is_majorant hClasses hAdj₂ hd₁
      exact ⟨{
        leftMoves := 0
        rightMoves := 2
        coverBudget := by omega
        path := .right hRight₀ (.right hRight₁ (.nil _ _))
        adjacent := by
          simpa [cyclicAdvance_add] using hAdj₂
        terminal := by
          simpa [cyclicAdvance_add] using hMajorant₂ }⟩

/-- A jointly selected pair of actual majorant paths.  The objective is the
number of moves made by the two facing endpoints in ErLV Figure 4. -/
structure CoordinatedK3MajorantPair
    {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ)
    (z x t u : Fin n) where
  /-- Majorant path starting from the first oriented edge `zx`. -/
  first : K3MajorantWitness P d₁ d₂ d₃ z x
  /-- Majorant path starting from the second oriented edge `tu`. -/
  second : K3MajorantWitness P d₁ d₂ d₃ t u
  minimalInnerMoves : ∀
    (first' : K3MajorantWitness P d₁ d₂ d₃ z x)
    (second' : K3MajorantWitness P d₁ d₂ d₃ t u),
    first.rightMoves + second.leftMoves ≤
      first'.rightMoves + second'.leftMoves

/-- The nonempty Cartesian pool of actual majorant paths has a pair
minimizing the total number of moves at the two facing endpoints. -/
theorem exists_coordinated_k3_majorant_pair
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {z x t u : Fin n}
    (hFirst : Nonempty (K3MajorantWitness P d₁ d₂ d₃ z x))
    (hSecond : Nonempty (K3MajorantWitness P d₁ d₂ d₃ t u)) :
    Nonempty (CoordinatedK3MajorantPair P d₁ d₂ d₃ z x t u) := by
  classical
  let HasCost : ℕ → Prop := fun cost ↦
    ∃ first : K3MajorantWitness P d₁ d₂ d₃ z x,
      ∃ second : K3MajorantWitness P d₁ d₂ d₃ t u,
        first.rightMoves + second.leftMoves = cost
  have hCost : ∃ cost, HasCost cost := by
    obtain ⟨first⟩ := hFirst
    obtain ⟨second⟩ := hSecond
    exact ⟨first.rightMoves + second.leftMoves, first, second, rfl⟩
  obtain ⟨first, second, hmin⟩ := Nat.find_spec hCost
  refine ⟨{
    first := first
    second := second
    minimalInnerMoves := ?_ }⟩
  intro first' second'
  rw [hmin]
  exact Nat.find_min' hCost ⟨first', second', rfl⟩

/-- If no degree-six vertex exists, every vertex has degree at least seven. -/
theorem all_degrees_at_least_seven_of_no_degree_six
    {n : ℕ} [_nonzero : NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hNoLow : ¬∃ v, vertexDegree P d₁ d₂ d₃ v ≤ 6) :
    ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v := by
  intro v
  have hnot : ¬vertexDegree P d₁ d₂ d₃ v ≤ 6 := by
    intro hv
    exact hNoLow ⟨v, hv⟩
  omega

/-- In the high-minimum-degree branch, a maximal-gap vertex and both
primary-source majorants exist.  The first witness is oriented `z ⟶ x`, so
its endpoint counts are reversed when compared with the draft's `(a,b)`
convention. -/
theorem exists_maximal_gap_two_majorants
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (hHigh : ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v) :
    ∃ x : Fin n,
      (∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤ firstNeighborGap P d₁ d₂ d₃ x) ∧
      Nonempty (K3MajorantWitness P d₁ d₂ d₃
        (firstClockwiseNeighbor P d₁ d₂ d₃ x) x) ∧
      Nonempty (K3MajorantWitness P d₁ d₂ d₃
        (cyclicAdvance x 3)
        (firstCounterclockwiseNeighbor P d₁ d₂ d₃ (cyclicAdvance x 3))) := by
  obtain ⟨x, hx⟩ := exists_maximal_firstNeighborGap P d₁ d₂ d₃
  refine ⟨x, hx, ?_, ?_⟩
  · apply exists_k3_majorant hClasses
    apply topThreeAdjacent_symm
    apply firstClockwiseNeighbor_adjacent_of_degree_pos
    have hxHigh := hHigh x
    omega
  · apply exists_k3_majorant hClasses
    apply firstCounterclockwiseNeighbor_adjacent_of_degree_pos
    have htHigh := hHigh (cyclicAdvance x 3)
    omega

/-- The high-minimum-degree branch admits a maximal-gap vertex together with
a jointly minimal pair of actual cover paths. -/
theorem exists_maximal_gap_coordinated_majorants
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (hClasses : HasTopThreeDistanceClasses P d₁ d₂ d₃)
    (hHigh : ∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v) :
    ∃ x : Fin n,
      (∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤
        firstNeighborGap P d₁ d₂ d₃ x) ∧
      Nonempty (CoordinatedK3MajorantPair P d₁ d₂ d₃
        (firstClockwiseNeighbor P d₁ d₂ d₃ x) x
        (cyclicAdvance x 3)
        (firstCounterclockwiseNeighbor P d₁ d₂ d₃
          (cyclicAdvance x 3))) := by
  obtain ⟨x, hMax, hFirst, hSecond⟩ :=
    exists_maximal_gap_two_majorants hClasses hHigh
  exact ⟨x, hMax, exists_coordinated_k3_majorant_pair hFirst hSecond⟩

namespace K3MajorantWitness

/-- Convert a witness without changing endpoint orientation. -/
def toK3Majorant
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {i j : Fin n}
    (W : K3MajorantWitness P d₁ d₂ d₃ i j) : K3Majorant where
  leftMoves := W.leftMoves
  rightMoves := W.rightMoves
  coverBudget := W.coverBudget

/-- Convert the first source majorant `z ⟶ x` to the draft convention:
`a` counts moves at `x`, while `b` counts moves at `z`. -/
def toFirstK3Majorant
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ} {i j : Fin n}
    (W : K3MajorantWitness P d₁ d₂ d₃ i j) : K3Majorant where
  leftMoves := W.rightMoves
  rightMoves := W.leftMoves
  coverBudget := by simpa [Nat.add_comm] using W.coverBudget

end K3MajorantWitness

/-- Build the arithmetic record once the source's arc-nesting conclusion
`s = u+M`, `M≤β` has been supplied. -/
noncomputable def erlvK3MaximalGapSetupOfMajorants
    {n : ℕ} [NeZero n] {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    {x z t u : Fin n}
    (first : K3MajorantWitness P d₁ d₂ d₃ z x)
    (second : K3MajorantWitness P d₁ d₂ d₃ t u)
    (hgap : firstNeighborGap P d₁ d₂ d₃ t ≤ firstNeighborGap P d₁ d₂ d₃ x)
    (M : ℕ) (hM : M ≤ second.rightMoves) : ErLVK3MaximalGapSetup where
  first := first.toFirstK3Majorant
  second := second.toK3Majorant
  gapX := firstNeighborGap P d₁ d₂ d₃ x
  gapT := firstNeighborGap P d₁ d₂ d₃ t
  gapT_le_gapX := hgap
  M := M
  M_le_secondRight := hM

/-- Exact first unresolved source fact.  If `x` maximizes the first-neighbor
gap, `z` is its first clockwise neighbor, `t=x+3`, and `u` is the first
counterclockwise neighbor of `t`, then a jointly minimal pair of actual
majorant paths can be chosen so that the terminal endpoint `s` of the
majorant of `zx` lies on the arc from `u` to the terminal endpoint `s'` of
the majorant of `tu`.  In side-count form this is precisely
`s = cyclicAdvance u M` for some `M≤β`.

The acute-angle/nonavoiding-majorants implication is proved in
`MajorantArcNesting.lean`.  What remains is ErLV's undisplayed strict order of
the two inner majorant endpoints: under the draft's side-count convention it
is `first.rightMoves + second.leftMoves < 3`. -/
def ErLVMajorantArcNestingComplete : Prop :=
  ∀ {n : ℕ} [NeZero n] (P : Fin n → Point ℝ) (d₁ d₂ d₃ : ℝ),
    CyclicStrictConvex P → HasTopThreeDistanceClasses P d₁ d₂ d₃ →
    (∀ v, 7 ≤ vertexDegree P d₁ d₂ d₃ v) →
    ∀ x : Fin n,
      (∀ v, firstNeighborGap P d₁ d₂ d₃ v ≤ firstNeighborGap P d₁ d₂ d₃ x) →
      let z := firstClockwiseNeighbor P d₁ d₂ d₃ x
      let t := cyclicAdvance x 3
      let u := firstCounterclockwiseNeighbor P d₁ d₂ d₃ t
      ∃ pair : CoordinatedK3MajorantPair P d₁ d₂ d₃ z x t u,
        ∃ M : ℕ, M ≤ pair.second.rightMoves ∧
          cyclicRetreat z pair.first.leftMoves = cyclicAdvance u M

end LeanPool.Erdos132ConvexK3
