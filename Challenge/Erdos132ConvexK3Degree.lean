/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic

/-!
# Degree six for the three largest distances in convex position

Source: doi:10.1007/BF02187746, url:https://www.erdosproblems.com/132
Proposed by: Egor Lyfar
Open declarations: `Challenge.Erdos132ConvexK3Degree.degree_le_six`
Tags: combinatorial-geometry, distance-graphs, convex-position, erdos-problems
MSC: 52C10, 05C12
Estimated size: ~15329 lines of Lean

Informal statement:
* `Challenge.Erdos132ConvexK3Degree.degree_le_six` — For every injectively labelled finite set of
  points in the real Euclidean plane, listed in counterclockwise strictly convex position and having
  at least three distinct interpoint distances, and for its explicitly named three largest
  squared-distance classes, the graph joining pairs in those classes has a vertex of degree at most
  six. Squaring preserves equality and order of Euclidean distances.
-/

namespace Challenge.Erdos132ConvexK3Degree

/-- A point in the real Euclidean plane, represented by Cartesian coordinates. -/
abbrev Point := ℝ × ℝ

/-- Twice the signed area of the oriented triangle `abc`. -/
def orientedArea (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Squared Euclidean distance between two Cartesian points. -/
def squaredDistance (a b : Point) : ℝ :=
  (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2

/-- The successor of an index in its cyclic order. -/
def cyclicNext {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- An injectively labelled finite set in strictly convex position, listed in
counterclockwise boundary order. Every point other than the endpoints of a
boundary edge lies strictly to the left of that oriented edge. -/
def StrictlyConvexPosition {n : ℕ} (points : Fin n → Point) : Prop :=
  Function.Injective points ∧
    ∀ i j, j ≠ i → j ≠ cyclicNext i →
      0 < orientedArea (points i) (points (cyclicNext i)) (points j)

/-- `d₁ > d₂ > d₃` are exactly the three largest squared-distance
classes realized by distinct pairs of points. The witnesses force at least
three distinct interpoint distances. -/
def AreThreeLargestSquaredDistances
    {n : ℕ} (points : Fin n → Point) (d₁ d₂ d₃ : ℝ) : Prop :=
  d₃ < d₂ ∧ d₂ < d₁ ∧
    (∃ i j, i < j ∧ squaredDistance (points i) (points j) = d₁) ∧
    (∃ i j, i < j ∧ squaredDistance (points i) (points j) = d₂) ∧
    (∃ i j, i < j ∧ squaredDistance (points i) (points j) = d₃) ∧
    ∀ i j, i < j →
      let d := squaredDistance (points i) (points j)
      d ≤ d₁ ∧ (d < d₁ → d ≤ d₂) ∧ (d < d₂ → d ≤ d₃)

/-- The degree of a vertex in the graph joining pairs whose squared distance
is one of the three named largest classes. -/
noncomputable def topThreeDistanceDegree
    {n : ℕ} (points : Fin n → Point) (d₁ d₂ d₃ : ℝ) (i : Fin n) : ℕ :=
  ((Finset.univ.erase i).filter fun j ↦
    squaredDistance (points i) (points j) = d₁ ∨
      squaredDistance (points i) (points j) = d₂ ∨
        squaredDistance (points i) (points j) = d₃).card

/-- The `k = 3` case of the "perhaps degree at most `2k`" question posed by
Erdős--Lovász--Vesztergombi (printed p. 542), which their Theorem 2.7
(printed p. 548) answers only with the weaker bound `3k - 1`: the graph of
the three largest distance classes
of a finite strictly convex planar set has a vertex of degree at most six.
Distances are represented by their squares, which preserves equality and
order for Euclidean distances. -/
theorem degree_le_six
    {n : ℕ} (points : Fin n → Point) (d₁ d₂ d₃ : ℝ)
    (hPosition : StrictlyConvexPosition points)
    (hDistances : AreThreeLargestSquaredDistances points d₁ d₂ d₃) :
    ∃ i, topThreeDistanceDegree points d₁ d₂ d₃ i ≤ 6 := sorry

end Challenge.Erdos132ConvexK3Degree
