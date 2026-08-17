/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

/-!
# The convex three-largest-distance graph

Definitions for the internal convex `k = 3` Erdős 132 draft.  Geometry is
expressed through exact signed areas, while the graph uses squared distances;
this keeps the rational campaign witnesses kernel-reducible.

The open Erdős 132 conjecture is not asserted here.  Recon:
`~/Knowledge/Construct/recon/erdos_132.md`.
-/

namespace LeanPool.Erdos132ConvexK3

/-- A Cartesian point over an ordered coordinate ring. -/
abbrev Point (K : Type*) := K × K

/-- Signed two-dimensional cross product. -/
def cross {K : Type*} [Ring K] (u v : Point K) : K :=
  u.1 * v.2 - u.2 * v.1

/-- Cartesian dot product.  Keeping this polynomial form explicit lets the
majorant angle argument stay over exact ordered rings. -/
def dot {K : Type*} [Ring K] (u v : Point K) : K :=
  u.1 * v.1 + u.2 * v.2

/-- Signed turn from the ray `a ⟶ b` to the ray `a ⟶ c`. -/
def turn {K : Type*} [Ring K] (a b c : Point K) : K :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Squared Euclidean distance, used to compare distance classes exactly. -/
def sqDist {K : Type*} [Ring K] (a b : Point K) : K :=
  (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2

theorem sqDist_comm {K : Type*} [CommRing K] (a b : Point K) :
    sqDist a b = sqDist b a := by
  simp [sqDist]
  ring

/-- The next index in a cyclic labelling. -/
def cyclicNext {n : ℕ} [NeZero n] (i : Fin n) : Fin n := i + 1

/-- Strict convex position in a specified cyclic order.

Every vertex other than the endpoints of a boundary edge lies strictly in
that oriented edge's left open half-plane.  This signed-area formulation is
stronger and less ambiguous than checking consecutive turns alone.
-/
def CyclicStrictConvex
    {K : Type*} [Ring K] [LinearOrder K] [_strictOrder : IsStrictOrderedRing K]
    {n : ℕ} [NeZero n]
    (P : Fin n → Point K) : Prop :=
  ∀ i j, j ≠ i → j ≠ cyclicNext i → 0 < turn (P i) (P (cyclicNext i)) (P j)

/-- Four vertices in positive cyclic order, in the exact form needed for the
diagonal-crossing proof. -/
def StrictConvexQuad
    {K : Type*} [Ring K] [LinearOrder K] [_strictOrder : IsStrictOrderedRing K]
    (a b c d : Point K) : Prop :=
  0 < turn a b c ∧ 0 < turn a b d ∧ 0 < turn b c d ∧ 0 < turn c d a

/-- Membership in the open left half-plane of the oriented line `a ⟶ b`. -/
def InLeftOpenHalfPlane
    {K : Type*} [Ring K] [LinearOrder K] [_strictOrder : IsStrictOrderedRing K]
    (a b p : Point K) : Prop :=
  0 < turn a b p

/-- Executable increasing representatives of unordered pairs of labels. -/
def unorderedPairList (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i ↦
    ((List.finRange n).filter fun j ↦ decide (i < j)).map fun j ↦ (i, j)

/-- Increasing representatives of unordered pairs of labels. -/
def unorderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (unorderedPairList n).toFinset

/-- The squared distance classes realized by a labelled configuration. -/
def realizedSquaredDistances
    {K : Type*} [Ring K] [DecidableEq K] {n : ℕ} (P : Fin n → Point K) : Finset K :=
  (unorderedPairs n).image fun e ↦ sqDist (P e.1) (P e.2)

/-- `d₁ > d₂ > d₃` are exactly the three largest squared distance classes. -/
def HasTopThreeDistanceClasses
    {K : Type*} [Ring K] [LinearOrder K] [_strictOrder : IsStrictOrderedRing K] {n : ℕ}
    (P : Fin n → Point K) (d₁ d₂ d₃ : K) : Prop :=
  d₃ < d₂ ∧ d₂ < d₁ ∧
    (∃ e ∈ unorderedPairList n, sqDist (P e.1) (P e.2) = d₁) ∧
    (∃ e ∈ unorderedPairList n, sqDist (P e.1) (P e.2) = d₂) ∧
    (∃ e ∈ unorderedPairList n, sqDist (P e.1) (P e.2) = d₃) ∧
    ∀ e ∈ unorderedPairList n,
      let d := sqDist (P e.1) (P e.2)
      d ≤ d₁ ∧ (d < d₁ → d ≤ d₂) ∧ (d < d₂ → d ≤ d₃)

/-- Executable checker for `CyclicStrictConvex`. -/
def cyclicStrictConvexCheck
    {K : Type*} [Ring K] [LinearOrder K] [_strictOrder : IsStrictOrderedRing K]
    {n : ℕ} [NeZero n] (P : Fin n → Point K) : Bool :=
  (List.finRange n).all fun i ↦
    (List.finRange n).all fun j ↦
      decide (j = i ∨ j = cyclicNext i ∨ 0 < turn (P i) (P (cyclicNext i)) (P j))

theorem cyclicStrictConvex_of_check
    {K : Type*} [Ring K] [LinearOrder K] [_strictOrder : IsStrictOrderedRing K]
    {n : ℕ} [NeZero n] {P : Fin n → Point K}
    (h : cyclicStrictConvexCheck P = true) : CyclicStrictConvex P := by
  rw [cyclicStrictConvexCheck, List.all_eq_true] at h
  intro i j hji hjnext
  have hi := h i (List.mem_finRange i)
  rw [List.all_eq_true] at hi
  have hij := of_decide_eq_true (hi j (List.mem_finRange j))
  rcases hij with hij | hij | hij
  · exact (hji hij).elim
  · exact (hjnext hij).elim
  · exact hij

/-- Executable checker for the exact top-three distance-class predicate. -/
def hasTopThreeDistanceClassesCheck
    {K : Type*} [Ring K] [LinearOrder K] [_strictOrder : IsStrictOrderedRing K]
    {n : ℕ} (P : Fin n → Point K) (d₁ d₂ d₃ : K) : Bool :=
  decide (d₃ < d₂) && decide (d₂ < d₁) &&
    (unorderedPairList n).any (fun e ↦ decide (sqDist (P e.1) (P e.2) = d₁)) &&
    (unorderedPairList n).any (fun e ↦ decide (sqDist (P e.1) (P e.2) = d₂)) &&
    (unorderedPairList n).any (fun e ↦ decide (sqDist (P e.1) (P e.2) = d₃)) &&
    (unorderedPairList n).all (fun e ↦
      let d := sqDist (P e.1) (P e.2)
      decide (d ≤ d₁ ∧ (d < d₁ → d ≤ d₂) ∧ (d < d₂ → d ≤ d₃)))

theorem hasTopThreeDistanceClasses_of_check
    {K : Type*} [Ring K] [LinearOrder K] [_strictOrder : IsStrictOrderedRing K]
    {n : ℕ} {P : Fin n → Point K} {d₁ d₂ d₃ : K}
    (h : hasTopThreeDistanceClassesCheck P d₁ d₂ d₃ = true) :
    HasTopThreeDistanceClasses P d₁ d₂ d₃ := by
  simp only [hasTopThreeDistanceClassesCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, List.all_eq_true] at h
  rcases h with ⟨h, hall⟩
  rcases h with ⟨h, h₃⟩
  rcases h with ⟨h, h₂⟩
  rcases h with ⟨h, h₁⟩
  rcases h with ⟨hd₃d₂, hd₂d₁⟩
  refine ⟨hd₃d₂, hd₂d₁, h₁, h₂, h₃, ?_⟩
  · intro e he
    exact hall e he

/-- Adjacency in the union of the three named largest distance classes. -/
def TopThreeAdjacent
    {K : Type*} [Ring K] {n : ℕ}
    (P : Fin n → Point K) (d₁ d₂ d₃ : K) (i j : Fin n) : Prop :=
  i ≠ j ∧
    (sqDist (P i) (P j) = d₁ ∨ sqDist (P i) (P j) = d₂ ∨
      sqDist (P i) (P j) = d₃)

/-- The graph `G(S,3)` for three explicitly identified distance classes. -/
def topThreeGraph
    {K : Type*} [CommRing K] {n : ℕ}
    (P : Fin n → Point K) (d₁ d₂ d₃ : K) : SimpleGraph (Fin n) where
  Adj i j := TopThreeAdjacent P d₁ d₂ d₃ i j
  symm := ⟨by
    intro i j hij
    refine ⟨hij.1.symm, ?_⟩
    simpa only [sqDist_comm] using hij.2
    ⟩
  loopless := ⟨by
    intro i hii
    exact hii.1 rfl⟩

/-- Vertex degree in `G(S,3)`, executable for exact coordinate fields. -/
def vertexDegree
    {K : Type*} [CommRing K] [DecidableEq K] {n : ℕ}
    (P : Fin n → Point K) (d₁ d₂ d₃ : K) (i : Fin n) : ℕ :=
  ((Finset.univ.erase i).filter fun j ↦
    sqDist (P i) (P j) = d₁ ∨ sqDist (P i) (P j) = d₂ ∨
      sqDist (P i) (P j) = d₃).card

theorem vertexDegree_eq_of_neighbors
    {K : Type*} [CommRing K] [DecidableEq K] {n : ℕ}
    (P : Fin n → Point K) (d₁ d₂ d₃ : K) (i : Fin n) (N : Finset (Fin n))
    (hN : ∀ j, j ∈ N ↔ j ≠ i ∧
      (sqDist (P i) (P j) = d₁ ∨ sqDist (P i) (P j) = d₂ ∨
        sqDist (P i) (P j) = d₃)) :
    vertexDegree P d₁ d₂ d₃ i = N.card := by
  unfold vertexDegree
  congr 1
  ext j
  simpa only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] using
    (hN j).symm

end LeanPool.Erdos132ConvexK3
