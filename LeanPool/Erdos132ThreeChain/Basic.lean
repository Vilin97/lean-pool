/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Planar squared distances and geometric 3-chains

This file sets up the elementary objects used throughout the project: points of the Euclidean
plane together with their squared distance, squared diameters and non-diameter distance
supports, and the geometric 3-chain

`L h a = {a, 3a, 9a, …, 3 ^ (h - 1) * a}`

that the main theorem forbids as a non-diameter distance support.

Everything is deliberately self-contained and coordinate-based: `Point` is `ℝ × ℝ` and
`sqDist` is the explicit sum of two squares, so that every planarity identity used later
(Heron, the anchored Gram determinant) is provable by `ring` from coordinates.
-/

namespace Erdos132ThreeChain

/-- A point of the Euclidean plane. -/
abbrev Point : Type := ℝ × ℝ

/-- The squared Euclidean distance between two points of the plane. -/
def sqDist (p q : Point) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

@[simp]
theorem sqDist_self (p : Point) : sqDist p p = 0 := by simp [sqDist]

theorem sqDist_comm (p q : Point) : sqDist p q = sqDist q p := by
  simp only [sqDist]; ring

theorem sqDist_nonneg (p q : Point) : 0 ≤ sqDist p q := by
  simp only [sqDist]; positivity

theorem sqDist_eq_zero_iff {p q : Point} : sqDist p q = 0 ↔ p = q := by
  simp only [sqDist]
  refine ⟨fun h => ?_, fun h => by rw [h]; ring⟩
  have h1 : (p.1 - q.1) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  have h2 : (p.2 - q.2) ^ 2 = 0 := by nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  have e1 : p.1 = q.1 := by
    have := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h1
    linarith
  have e2 : p.2 = q.2 := by
    have := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
    linarith
  exact Prod.ext e1 e2

theorem sqDist_pos {p q : Point} (h : p ≠ q) : 0 < sqDist p q :=
  lt_of_le_of_ne (sqDist_nonneg p q) fun hc => h (sqDist_eq_zero_iff.mp hc.symm)

/-- `IsSqDiameter X D` says that `D` is the squared diameter of `X`: it is realised by two
distinct points of `X`, and it dominates every squared distance inside `X`. -/
def IsSqDiameter (X : Finset Point) (D : ℝ) : Prop :=
  (∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ sqDist p q = D) ∧ ∀ p ∈ X, ∀ q ∈ X, sqDist p q ≤ D

/-- The geometric 3-chain of length `h` and base `a`: the set `{a * 3 ^ j | j < h}`. -/
def chain (a : ℝ) (h : ℕ) : Set ℝ := {x : ℝ | ∃ j < h, x = a * 3 ^ j}

theorem mem_chain_iff {a x : ℝ} {h : ℕ} : x ∈ chain a h ↔ ∃ j < h, x = a * 3 ^ j := Iff.rfl

theorem base_mem_chain {a : ℝ} {h : ℕ} (hh : 0 < h) : a ∈ chain a h :=
  ⟨0, hh, by simp⟩

theorem triple_base_mem_chain {a : ℝ} {h : ℕ} (hh : 2 ≤ h) : a * 3 ∈ chain a h :=
  ⟨1, hh, by norm_num⟩

/-- The set of squared distances realised by distinct points of `X` that are not the squared
diameter `D`. -/
def nonDiameterSqDists (X : Finset Point) (D : ℝ) : Set ℝ :=
  {d : ℝ | ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ sqDist p q = d ∧ d ≠ D}

/-- `IsChainValue c x` records that `x` is `c` times a nonnegative power of three.  It is the
scale-free shadow of `chain`: if `c` is the smallest value of a chain that `x` belongs to,
then `x = c * 3 ^ j` for some `j : ℕ`. -/
def IsChainValue (c x : ℝ) : Prop := ∃ j : ℕ, x = c * 3 ^ j

theorem IsChainValue.pos {c x : ℝ} (hc : 0 < c) (h : IsChainValue c x) : 0 < x := by
  obtain ⟨j, rfl⟩ := h
  positivity

end Erdos132ThreeChain
