/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.Basic

/-!
# The normalized Markoff rotation

This file isolates the elementary two-dimensional linear algebra behind the fundamental
rotation. The parameter of `rho` is a normalized trace coordinate. Thus the rotation fixing an
original Markoff coordinate `x.x1` is obtained by specializing the parameter to `3 * x.x1`.
-/

@[expose] public section

namespace BGS.Markoff

universe u

open scoped Matrix

section

variable {R : Type u} [CommRing R]

/-- The normalized rotation matrix `rho(t) = [[0, 1], [-1, t]]`. -/
def rho (t : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; -1, t]

/-- Every normalized rotation matrix has determinant one. -/
@[simp]
theorem rho_det (t : R) : (rho t).det = 1 := by
  simp [rho, Matrix.det_fin_two_of]

/-- The matrix parameter is exactly the trace of the normalized rotation. -/
@[simp]
theorem rho_trace (t : R) : (rho t).trace = t := by
  simp [rho, Matrix.trace_fin_two_of]

/-- The characteristic polynomial is `T² - tT + 1`. -/
@[simp]
theorem rho_charpoly [Nontrivial R] (t : R) :
    (rho t).charpoly = Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + 1 := by
  simpa using Matrix.charpoly_fin_two (rho t)

/-- On a coordinate pair, `rho(t)` sends `(a, b)` to `(b, t * b - a)`. -/
@[simp]
theorem rho_mulVec (t a b : R) : rho t *ᵥ ![a, b] = ![b, t * b - a] := by
  ext i
  fin_cases i
  · simp [rho, Matrix.mulVec, dotProduct]
  · simp [rho, Matrix.mulVec, dotProduct]
    ring

/-- The normalized rotation, regarded as an element of the special linear group. -/
def rhoSL (t : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨rho t, rho_det t⟩

@[simp]
theorem rhoSL_coe (t : R) : (rhoSL t : Matrix (Fin 2) (Fin 2) R) = rho t :=
  rfl

/-- The group-theoretic order of the normalized rotation.

By the convention of `orderOf`, this is zero when the rotation has infinite order.
-/
noncomputable def rotationOrder (t : R) : ℕ :=
  orderOf (rhoSL t)

/-- Raising the rotation to `rotationOrder` gives the identity in `SL₂`. -/
theorem rhoSL_pow_rotationOrder (t : R) : rhoSL t ^ rotationOrder t = 1 := by
  simp [rotationOrder]

/-- Over a finite coefficient ring, every normalized rotation has positive order. -/
theorem rotationOrder_pos [Finite R] (t : R) : 0 < rotationOrder t := by
  exact (isOfFinOrder_of_finite (rhoSL t)).orderOf_pos

/-- The two coordinates moved by the fundamental rotation fixing the first coordinate. -/
def movingCoordinates (x : Point R) : Fin 2 → R :=
  ![x.x2, x.x3]

/-- The fundamental rotation is the action of `rho(3 * x.x1)` on the moving coordinates. -/
theorem rho_mulVec_movingCoordinates (x : Point R) :
    rho (3 * x.x1) *ᵥ movingCoordinates x = movingCoordinates (rotate1 x) := by
  simp [movingCoordinates, rotate1] using rho_mulVec (3 * x.x1) x.x2 x.x3

/-- The normalized trace parameter for the fundamental rotation is `3 * x.x1`. -/
theorem rho_trace_fundamentalRotation (x : Point R) : (rho (3 * x.x1)).trace = 3 * x.x1 := by
  simp

/-- Reconstruct the full fundamental rotation from the fixed coordinate and the matrix action. -/
theorem rotate1_eq_rho (x : Point R) :
    rotate1 x =
      ⟨x.x1,
        (rho (3 * x.x1) *ᵥ movingCoordinates x) 0,
        (rho (3 * x.x1) *ᵥ movingCoordinates x) 1⟩ := by
  ext
  · rfl
  · simp [rotate1, movingCoordinates] using
      congrFun (rho_mulVec_movingCoordinates x).symm 0
  · simp [rotate1, movingCoordinates] using
      congrFun (rho_mulVec_movingCoordinates x).symm 1

end

end BGS.Markoff
