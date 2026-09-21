/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.Tactic.Linarith

/-! # Scalarization -/

namespace Homogenization

/-- The diagonal sign-flip matrix that changes the sign of the `i`-th coordinate. -/
noncomputable def signFlipMatrix {d : ℕ} (i : Fin d) : Mat d :=
  Matrix.diagonal fun j => if j = i then (-1 : ℝ) else 1

/-- Invariance under conjugation by every coordinate sign flip. -/
def IsSignFlipInvariant {d : ℕ} (A : Mat d) : Prop :=
  ∀ i : Fin d, signFlipMatrix i * A * signFlipMatrix i = A

/-- Invariance under conjugation by every coordinate transposition matrix. -/
def IsSwapInvariant {d : ℕ} (A : Mat d) : Prop :=
  ∀ i j : Fin d, Matrix.swap ℝ i j * A * Matrix.swap ℝ i j = A

/-- Scalar matrices over `Fin d`, written as multiples of the identity. -/
def IsScalarMatrix {d : ℕ} (A : Mat d) : Prop :=
  ∃ c : ℝ, A = c • 1

theorem signFlipMatrix_mul_mul_signFlipMatrix_apply {d : ℕ} (i r c : Fin d) (A : Mat d) :
    (signFlipMatrix i * A * signFlipMatrix i) r c =
      (if r = i then (-1 : ℝ) else 1) * A r c * (if c = i then (-1 : ℝ) else 1) := by
  simp [signFlipMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem signFlipMatrix_sq {d : ℕ} (i : Fin d) :
    signFlipMatrix i * signFlipMatrix i = 1 := by
  ext r c
  by_cases hrc : r = c
  · subst c
    by_cases hri : r = i <;> simp [signFlipMatrix, hri]
  · simp [signFlipMatrix, hrc]

theorem offDiag_eq_zero_of_isSignFlipInvariant {d : ℕ} {A : Mat d}
    (hA : IsSignFlipInvariant A) {i j : Fin d} (hij : i ≠ j) :
    A i j = 0 := by
  have hji : j ≠ i := fun h => hij h.symm
  have hentry := congrArg (fun M => M i j) (hA i)
  have hneg : -A i j = A i j := by
    simpa [signFlipMatrix_mul_mul_signFlipMatrix_apply, hij, hji] using hentry
  linarith

theorem diag_eq_of_isSwapInvariant {d : ℕ} {A : Mat d} (hA : IsSwapInvariant A)
    (i j : Fin d) : A i i = A j j := by
  have hentry := congrArg (fun M => M i i) (hA i j)
  simpa using hentry.symm

theorem isScalarMatrix_of_isSignFlipInvariant_of_isSwapInvariant {d : ℕ} [NeZero d]
    {A : Mat d} (hFlip : IsSignFlipInvariant A) (hSwap : IsSwapInvariant A) :
    IsScalarMatrix A := by
  refine ⟨A 0 0, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    have hdiag : A i i = A 0 0 := diag_eq_of_isSwapInvariant hSwap i 0
    simpa [Matrix.one_apply] using hdiag
  · have hzero : A i j = 0 := offDiag_eq_zero_of_isSignFlipInvariant hFlip hij
    simp [hij, hzero]

theorem isSignFlipInvariant_of_isScalarMatrix {d : ℕ} {A : Mat d}
    (hA : IsScalarMatrix A) :
    IsSignFlipInvariant A := by
  rcases hA with ⟨c, rfl⟩
  intro i
  calc
    signFlipMatrix i * (c • (1 : Mat d)) * signFlipMatrix i
      = c • (signFlipMatrix i * (1 : Mat d) * signFlipMatrix i) := by
          simp
    _ = c • (1 : Mat d) := by
          simp [signFlipMatrix_sq]

theorem isSwapInvariant_of_isScalarMatrix {d : ℕ} {A : Mat d}
    (hA : IsScalarMatrix A) :
    IsSwapInvariant A := by
  rcases hA with ⟨c, rfl⟩
  intro i j
  calc
    Matrix.swap ℝ i j * (c • (1 : Mat d)) * Matrix.swap ℝ i j
      = c • (Matrix.swap ℝ i j * (1 : Mat d) * Matrix.swap ℝ i j) := by
          simp
    _ = c • (1 : Mat d) := by
          simp [Matrix.swap_mul_self (R := ℝ)]

theorem isScalarMatrix_inv {d : ℕ} {A : Mat d} (hA : IsScalarMatrix A) :
    IsScalarMatrix A⁻¹ := by
  rcases hA with ⟨c, hc⟩
  by_cases hc0 : c = 0
  · refine ⟨0, ?_⟩
    simp [hc, hc0]
  · refine ⟨c⁻¹, ?_⟩
    rw [hc]
    let : Invertible c := invertibleOfNonzero hc0
    have hInv :
        (c • (1 : Mat d))⁻¹ = ⅟c • ((1 : Mat d)⁻¹) :=
      Matrix.inv_smul (A := (1 : Mat d)) c (by simp)
    calc
      (c • (1 : Mat d))⁻¹ = ⅟c • ((1 : Mat d)⁻¹) := hInv
      _ = c⁻¹ • (1 : Mat d) := by simp

theorem skewPart_eq_zero_of_isScalarMatrix {d : ℕ} {A : Mat d} (hA : IsScalarMatrix A) :
    skewPart A = 0 := by
  rcases hA with ⟨c, rfl⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp [skewPart]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [skewPart, hij, hji]

end Homogenization
