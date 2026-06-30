/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import Mathlib.Data.Fintype.Powerset
import LeanPool.PebblingLean.Basic

/-!
# Hypercubes

The `n`-dimensional hypercube is represented as Boolean coordinate functions
`Fin n → Bool`. Two vertices are adjacent when they differ in exactly one
coordinate.
-/

namespace PebblingLean

/-- Vertices of the `n`-cube. -/
abbrev HypercubeVertex (n : ℕ) := Fin n → Bool

namespace Hypercube

theorem card_vertex (n : ℕ) : Fintype.card (HypercubeVertex n) = 2 ^ n := by
  simp [HypercubeVertex]

/-- Hamming distance on Boolean coordinate functions. -/
def dist {n : ℕ} (x y : HypercubeVertex n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card

/-- Coordinates on which two hypercube vertices differ. -/
def diffSet {n : ℕ} (x y : HypercubeVertex n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => x i ≠ y i)

theorem dist_eq_card_diffSet {n : ℕ} (x y : HypercubeVertex n) :
    dist x y = (diffSet x y).card := by
  rfl

/-- Hamming distance in `Q_n` is at most `n`. -/
theorem dist_le {n : ℕ} (x y : HypercubeVertex n) : dist x y ≤ n := by
  unfold dist
  calc
    (Finset.univ.filter fun i : Fin n => x i ≠ y i).card ≤
        (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by
      simp

/-- The vertex obtained from `base` by flipping exactly the coordinates in
`s`. -/
def fromDiffSet {n : ℕ} (base : HypercubeVertex n) (s : Finset (Fin n)) :
    HypercubeVertex n :=
  fun i => if i ∈ s then Bool.not (base i) else base i

@[simp]
theorem diffSet_fromDiffSet {n : ℕ} (base : HypercubeVertex n) (s : Finset (Fin n)) :
    diffSet base (fromDiffSet base s) = s := by
  ext i
  by_cases hi : i ∈ s <;> simp [diffSet, fromDiffSet, hi]

@[simp]
theorem fromDiffSet_diffSet {n : ℕ} (base v : HypercubeVertex n) :
    fromDiffSet base (diffSet base v) = v := by
  funext i
  by_cases hsame : base i = v i
  · have hnot : i ∉ diffSet base v := by
      simp [diffSet, hsame]
    simp [fromDiffSet, hnot, hsame]
  · have hin : i ∈ diffSet base v := by
      simp [diffSet, hsame]
    have hflip : Bool.not (base i) = v i := by
      exact (Bool.eq_not_iff.mpr (Ne.symm hsame)).symm
    simp [fromDiffSet, hin, hflip]

/-- Vertices of `Q_n` are equivalent to subsets of coordinates, by recording
where they differ from a fixed base vertex. -/
def diffSetEquiv {n : ℕ} (base : HypercubeVertex n) :
    HypercubeVertex n ≃ Finset (Fin n) where
  toFun := diffSet base
  invFun := fromDiffSet base
  left_inv := fromDiffSet_diffSet base
  right_inv := diffSet_fromDiffSet base

/-- The Hamming sphere of radius `k` around any fixed hypercube vertex has
cardinality `n choose k`. -/
theorem card_sphere {n : ℕ} (base : HypercubeVertex n) (k : ℕ) :
    Fintype.card {v : HypercubeVertex n // dist base v = k} = Nat.choose n k := by
  classical
  let e :
      {v : HypercubeVertex n // dist base v = k} ≃
        {s : Finset (Fin n) // s.card = k} :=
    (diffSetEquiv base).subtypeEquiv (fun v => by
      change dist base v = k ↔ (diffSet base v).card = k
      simp [dist_eq_card_diffSet])
  calc
    Fintype.card {v : HypercubeVertex n // dist base v = k}
        = Fintype.card {s : Finset (Fin n) // s.card = k} := by
          exact Fintype.card_congr e
    _ = Nat.choose n k := by
          simp

@[simp]
theorem dist_self {n : ℕ} (x : HypercubeVertex n) : dist x x = 0 := by
  simp [dist]

theorem dist_eq_zero_iff {n : ℕ} {x y : HypercubeVertex n} :
    dist x y = 0 ↔ x = y := by
  constructor
  · intro hdist
    funext i
    by_contra hne
    have hempty :
        (Finset.univ.filter fun i : Fin n => x i ≠ y i) = ∅ := by
      exact Finset.card_eq_zero.mp hdist
    have hi : i ∈ (Finset.univ.filter fun i : Fin n => x i ≠ y i) := by
      simp [hne]
    rw [hempty] at hi
    simp at hi
  · intro h
    subst y
    exact dist_self x

theorem dist_comm {n : ℕ} (x y : HypercubeVertex n) : dist x y = dist y x := by
  simp [dist, ne_comm]

/-- Hamming distance satisfies the triangle inequality. -/
theorem dist_triangle {n : ℕ} (x y z : HypercubeVertex n) :
    dist x z ≤ dist x y + dist y z := by
  classical
  unfold dist
  apply (Finset.card_mono ?_).trans
  · exact Finset.card_union_le _ _
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  by_cases hxy : x i = y i
  · right
    refine ⟨Finset.mem_univ i, ?_⟩
    intro hyz
    exact hi.2 (hxy.trans hyz)
  · left
    exact ⟨Finset.mem_univ i, hxy⟩

/-- The `n`-dimensional hypercube graph. -/
def graph (n : ℕ) : Graph (HypercubeVertex n) where
  Adj x y := dist x y = 1
  symm := by
    intro x y h
    rw [dist_comm x y] at h
    exact h
  loopless := by
    intro x h
    simp at h

/-- Adjacent hypercube vertices have distances to any third vertex that differ
by at most one in this direction. -/
theorem dist_adj_le_succ {n : ℕ} {x y t : HypercubeVertex n}
    (hxy : (graph n).Adj x y) : dist x t ≤ dist y t + 1 := by
  have h := dist_triangle x y t
  rw [hxy] at h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

end Hypercube

end PebblingLean
