/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Foundation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Euclidean geometry on `Point n`

`Point n = Fin n → ℝ` carries the sup norm, but the Laplace barriers are
radial for the Euclidean distance. This file records the squared Euclidean
distance `eucSq x y = (x - y) ⬝ᵥ (x - y)` and the uniform exterior sphere
condition phrased with it.
-/

@[expose] public noncomputable section

namespace ViscositySolns

variable {n : Nat}

/-- Squared Euclidean distance on `Point n`. -/
def eucSq (x y : Point n) : Real :=
  dotProduct (x - y) (x - y)

theorem eucSq_nonneg (x y : Point n) : 0 <= eucSq x y := by
  unfold eucSq
  simpa [dotProduct, ← sq] using Finset.sum_nonneg fun i _ => sq_nonneg ((x - y) i)

theorem eucSq_comm (x y : Point n) : eucSq x y = eucSq y x := by
  unfold eucSq
  rw [← neg_sub, neg_dotProduct, dotProduct_neg, neg_neg]

theorem eucSq_self (x : Point n) : eucSq x x = 0 := by
  simp [eucSq]

theorem continuous_eucSq : Continuous fun q : Point n × Point n => eucSq q.1 q.2 := by
  unfold eucSq
  fun_prop

/--
Uniform exterior sphere condition with radius `R`, in squared Euclidean
distance: every frontier point `x₀` of `C` lies on a sphere of radius `R`
centred at some `y`, and `closure C` lies outside the open ball.
-/
def UniformExteriorSphereSq (C : Set (Point n)) (R : Real) : Prop :=
  0 < R ∧ ∀ x₀ ∈ frontier C, ∃ y : Point n,
    eucSq x₀ y = R ^ 2 ∧ ∀ x ∈ closure C, R ^ 2 <= eucSq x y

end ViscositySolns
