/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Complex.Basic

/-!
# The Hilbert–Schmidt inner product on matrices

The **Hilbert–Schmidt (Frobenius) inner product** of two complex matrices is
`⟪A, B⟫ = Tr[Aᴴ B]`. Mathlib equips `Matrix` with the Frobenius *norm* but not (as a
global instance) with this inner product, so this quantum-free helper records the
plain bilinear data needed downstream: conjugate symmetry, sesquilinearity, and — the
key fact for the Lie-algebraic variance formula — **multiplicativity over the
Kronecker product**, `⟪A ⊗ C, B ⊗ D⟫ = ⟪A, B⟫ · ⟪C, D⟫`.

(The genuine `InnerProductSpace` structure, when needed for Gram–Schmidt / orthonormal
bases, is obtained separately by transport along the linear isometry to
`EuclideanSpace ℂ (m × m)`.)
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

variable {m : Type*} [Fintype m]

/-- The Hilbert–Schmidt (Frobenius) inner product `⟪A, B⟫ = Tr[Aᴴ B]`. Conjugate-linear
in the first argument, linear in the second. -/
def hsInner (A B : Matrix m m ℂ) : ℂ := (Aᴴ * B).trace

@[simp] theorem hsInner_def (A B : Matrix m m ℂ) : hsInner A B = (Aᴴ * B).trace := rfl

/-- Conjugate symmetry: `⟪A, B⟫ = conj ⟪B, A⟫`. -/
theorem hsInner_conj_symm (A B : Matrix m m ℂ) :
    hsInner A B = (starRingEnd ℂ) (hsInner B A) := by
  rw [hsInner, hsInner, starRingEnd_apply, ← Matrix.trace_conjTranspose,
    conjTranspose_mul, conjTranspose_conjTranspose]

/-- Additivity in the second argument. -/
theorem hsInner_add_right (A B C : Matrix m m ℂ) :
    hsInner A (B + C) = hsInner A B + hsInner A C := by
  simp [hsInner, Matrix.mul_add, Matrix.trace_add]

/-- Additivity in the first argument. -/
theorem hsInner_add_left (A B C : Matrix m m ℂ) :
    hsInner (A + B) C = hsInner A C + hsInner B C := by
  simp [hsInner, conjTranspose_add, Matrix.add_mul, Matrix.trace_add]

/-- Subtractivity in the second argument. -/
theorem hsInner_sub_right (A B C : Matrix m m ℂ) :
    hsInner A (B - C) = hsInner A B - hsInner A C := by
  simp [hsInner, Matrix.mul_sub, Matrix.trace_sub]

/-- Subtractivity in the first argument. -/
theorem hsInner_sub_left (A B C : Matrix m m ℂ) :
    hsInner (A - B) C = hsInner A C - hsInner B C := by
  simp [hsInner, conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub]

/-- Linearity in the second argument. -/
theorem hsInner_smul_right (c : ℂ) (A B : Matrix m m ℂ) :
    hsInner A (c • B) = c * hsInner A B := by
  simp [hsInner, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- Conjugate-linearity in the first argument. -/
theorem hsInner_smul_left (c : ℂ) (A B : Matrix m m ℂ) :
    hsInner (c • A) B = (starRingEnd ℂ) c * hsInner A B := by
  simp [hsInner, conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- Additivity over a finite sum in the second argument. -/
theorem hsInner_sum_right {ι : Type*} (A : Matrix m m ℂ) (s : Finset ι)
    (f : ι → Matrix m m ℂ) :
    hsInner A (∑ i ∈ s, f i) = ∑ i ∈ s, hsInner A (f i) := by
  simp only [hsInner, Matrix.mul_sum, Matrix.trace_sum]

/-- Additivity over a finite sum in the first argument. -/
theorem hsInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → Matrix m m ℂ)
    (B : Matrix m m ℂ) :
    hsInner (∑ i ∈ s, f i) B = ∑ i ∈ s, hsInner (f i) B := by
  simp only [hsInner, conjTranspose_sum, Matrix.sum_mul, Matrix.trace_sum]

/-- **Multiplicativity over the Kronecker product** — the key identity for assembling
the quadratic Casimir's inner products: `⟪A ⊗ C, B ⊗ D⟫ = ⟪A, B⟫ · ⟪C, D⟫`. -/
theorem hsInner_kronecker {n : Type*} [Fintype n]
    (A B : Matrix m m ℂ) (C D : Matrix n n ℂ) :
    hsInner (A ⊗ₖ C) (B ⊗ₖ D) = hsInner A B * hsInner C D := by
  rw [hsInner, hsInner, hsInner, conjTranspose_kronecker, ← mul_kronecker_mul,
    trace_kronecker]

/-- For Hermitian arguments the Hilbert–Schmidt inner product is symmetric. -/
theorem hsInner_comm_of_isHermitian {A B : Matrix m m ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    hsInner A B = hsInner B A := by
  rw [hsInner, hsInner, hA, hB, Matrix.trace_mul_comm]

/-- For Hermitian arguments the Hilbert–Schmidt inner product is real. -/
theorem hsInner_conj_of_isHermitian {A B : Matrix m m ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (starRingEnd ℂ) (hsInner A B) = hsInner A B := by
  rw [← hsInner_conj_symm]
  exact hsInner_comm_of_isHermitian hB hA

/-- The matrix units `single i j 1` are Hilbert–Schmidt orthonormal. -/
theorem hsInner_single [DecidableEq m] (i j k l : m) :
    hsInner (Matrix.single i j (1 : ℂ)) (Matrix.single k l 1)
      = if i = k ∧ j = l then 1 else 0 := by
  rw [hsInner, Matrix.conjTranspose_single, star_one, Matrix.trace_single_mul, one_smul]
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    rw [Matrix.single_apply_same, if_pos ⟨rfl, rfl⟩]
  · rw [if_neg h]
    apply Matrix.single_apply_of_ne
    rintro ⟨hki, hlj⟩
    exact h ⟨hki.symm, hlj.symm⟩

end QuantumAlg
