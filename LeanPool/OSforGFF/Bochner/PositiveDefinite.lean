/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/


import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Positive Definite Functions

A function φ : α → ℂ on an additive group is **positive definite** if:
1. φ(-x) = conj(φ(x)) for all x (Hermitian symmetry), and
2. For any finite collection of points x₁, ..., xₘ and complex coefficients
   c₁, ..., cₘ, the quadratic form ∑ᵢⱼ cbarᵢ cⱼ φ(xᵢ - xⱼ) ≥ 0.

Condition (1) ensures that the matrix [φ(xᵢ-xⱼ)] is Hermitian, so the
quadratic form in (2) is automatically real-valued. Together they say the
matrix is Hermitian positive semidefinite.

This is the standard definition in harmonic analysis (Rudin, *Fourier Analysis
on Groups*, §1.4). Note: some references define PD using only `.re ≥ 0`,
but that weaker condition does not imply Hermitian symmetry.

## Main definitions

- `IsPositiveDefinite`: positive definiteness for functions on additive groups

## Main results

- `IsPositiveDefinite.conj_symm`: φ(-x) = conj(φ(x))
- `IsPositiveDefinite.nonneg`: the quadratic form is nonneg
- `IsPositiveDefinite.eval_zero_nonneg`: φ(0) ≥ 0
- `IsPositiveDefinite.bounded_by_zero`: ‖φ(x)‖ ≤ φ(0).re for all x
- `IsPositiveDefinite.mul`: pointwise product of PD functions is PD (Schur)
- `isPositiveDefinite_precomp_linear`: composition with linear maps preserves PD
-/

open Complex BigOperators
open scoped Kronecker
open scoped ComplexOrder

/-- A function φ : α → ℂ is positive definite if the matrix [φ(xᵢ-xⱼ)] is
    Hermitian positive semidefinite for every finite set of points.

    This bundles two conditions:
    - `hermitian`: φ(-x) = conj(φ(x)) (ensures the matrix is Hermitian)
    - `nonneg`: Re(∑ᵢⱼ cbarᵢ cⱼ φ(xᵢ - xⱼ)) ≥ 0 (positive semidefiniteness)

    The Hermitian condition ensures the quadratic form is real, so Re ≥ 0
    is equivalent to the full condition ≥ 0.
-/
structure IsPositiveDefinite {α : Type*} [AddGroup α] (φ : α → ℂ) : Prop where
  hermitian : ∀ x : α, φ (-x) = starRingEnd ℂ (φ x)
  nonneg : ∀ (m : ℕ) (x : Fin m → α) (c : Fin m → ℂ),
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * φ (x i - x j)).re

/-- Composition preserves positive definiteness: if ψ is positive definite on H and
    T : E →ₗ[ℝ] H is linear, then ψ ∘ T is positive definite on E.
-/
lemma isPositiveDefinite_precomp_linear
    {E H : Type*} [AddCommGroup E] [AddCommGroup H]
    [Module ℝ E] [Module ℝ H]
    (ψ : H → ℂ) (hPD : IsPositiveDefinite ψ) (T : E →ₗ[ℝ] H) :
    IsPositiveDefinite (fun f : E => ψ (T f)) where
  hermitian x := by simp [map_neg, hPD.hermitian]
  nonneg m x c := by simpa using hPD.nonneg m (fun i => T (x i)) c

namespace IsPositiveDefinite

variable {α : Type*} [AddGroup α] {φ : α → ℂ}

private lemma kernelMatrix_posSemidef {m : ℕ} (hpd : IsPositiveDefinite φ) (x : Fin m → α) :
    (((Matrix.of fun i j => φ (x i - x j)) : Matrix (Fin m) (Fin m) ℂ).PosSemidef) := by
  let M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => φ (x i - x j)
  have hM_herm : M.IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    change starRingEnd ℂ (φ (x j - x i)) = φ (x i - x j)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (hpd.hermitian (x j - x i)).symm
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hM_herm, ?_⟩
  intro c
  have hre : 0 ≤ (dotProduct (star c) (M.mulVec c)).re := by
    simpa [M, dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
      using hpd.nonneg m x c
  have him : (dotProduct (star c) (M.mulVec c)).im = 0 := by
    simpa [M] using hM_herm.im_star_dotProduct_mulVec_self c
  exact Complex.nonneg_iff.mpr ⟨hre, him.symm⟩

/-- φ(-x) = conj(φ(x)). -/
lemma conj_symm (hpd : IsPositiveDefinite φ) (x : α) :
    φ (-x) = starRingEnd ℂ (φ x) := hpd.hermitian x

/-- φ(0) is real and nonneg. (Test with m = 1, c₁ = 1.) -/
lemma eval_zero_nonneg (hpd : IsPositiveDefinite φ) : 0 ≤ (φ 0).re := by
  have h := hpd.nonneg 1 (fun _ => 0) (fun _ => 1)
  simpa [starRingEnd_apply, star_one] using h

/-- φ(0) is real (imaginary part is zero). -/
lemma eval_zero_real (hpd : IsPositiveDefinite φ) : (φ 0).im = 0 := by
  have h := hpd.hermitian 0
  simp only [neg_zero] at h
  -- h : φ 0 = starRingEnd ℂ (φ 0), i.e., φ 0 = conj(φ 0)
  -- This means Im(φ 0) = 0
  have := congr_arg Complex.im h
  simp [Complex.conj_im] at this
  linarith

/-- Helper: expand the PD condition for m=2. -/
private lemma pd_two (hpd : IsPositiveDefinite φ) (a b : α) (c₀ c₁ : ℂ) :
    0 ≤ (starRingEnd ℂ c₀ * c₀ * φ (a - a) + starRingEnd ℂ c₀ * c₁ * φ (a - b) +
     (starRingEnd ℂ c₁ * c₀ * φ (b - a) + starRingEnd ℂ c₁ * c₁ * φ (b - b))).re := by
  have h := hpd.nonneg 2 ![a, b] ![c₀, c₁]
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- ‖φ(x)‖ ≤ φ(0).re for all x. (Cauchy-Schwarz on the 2×2 PD matrix.) -/
lemma bounded_by_zero (hpd : IsPositiveDefinite φ) (x : α) :
    ‖φ x‖ ≤ (φ 0).re := by
  -- Handle the case φ x = 0
  by_cases hφx : φ x = 0
  · have : ‖φ x‖ = 0 := by rw [hφx]; simp
    linarith [hpd.eval_zero_nonneg]
  -- Use the 2×2 PD condition with c = ![1, -φ(x)/‖φ(x)‖]
  -- which gives φ(0).re - ‖φ(x)‖ ≥ 0
  set t : ℂ := -(φ x / (‖φ x‖ : ℂ))
  have h := pd_two hpd 0 x 1 t
  simp only [sub_self, sub_zero, zero_sub] at h
  -- Now h : 0 ≤ (conj(1)·1·φ(0) + conj(1)·t·φ(-x) + conj(t)·1·φ(x) + conj(t)·t·φ(0)).re
  simp only [map_one, one_mul, mul_one] at h
  rw [hpd.hermitian x] at h
  -- h now has conj(φ x) in place of φ(-x)
  -- t = -φ(x)/‖φ(x)‖, so conj(t) = -conj(φ x)/‖φ(x)‖
  simp only [t, map_neg, map_div₀, conj_ofReal] at h
  -- Simplify conj(z)*z and z*conj(z) terms using normSq
  have hnorm_pos : (‖φ x‖ : ℝ) ≠ 0 := by positivity
  have hnorm_pos' : (‖φ x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm_pos
  -- Key: φ(x) * conj(φ(x)) = ‖φ(x)‖²  and  conj(φ(x)) * φ(x) = ‖φ(x)‖²
  have hns : (starRingEnd ℂ) (φ x) * φ x = ↑(‖φ x‖ ^ 2) := by
    rw [mul_comm, Complex.mul_conj, normSq_eq_norm_sq]
  have hns' : φ x * (starRingEnd ℂ) (φ x) = ↑(‖φ x‖ ^ 2) := by
    rw [Complex.mul_conj, normSq_eq_norm_sq]
  -- Rewrite the three non-trivial terms in h
  -- Term 1: -(φ x / ↑‖φ x‖) * conj(φ x) = -‖φ x‖² / ‖φ x‖ = -‖φ x‖
  have ht1 : -(φ x / ↑‖φ x‖) * (starRingEnd ℂ) (φ x) = -(↑‖φ x‖) := by
    rw [neg_mul, neg_inj, div_mul_eq_mul_div, hns', Complex.ofReal_pow,
      sq, mul_div_cancel_right₀ _ hnorm_pos']
  -- Term 2: -(conj(φ x) / ↑‖φ x‖) * φ x = -‖φ x‖
  have ht2 : -((starRingEnd ℂ) (φ x) / ↑‖φ x‖) * φ x = -(↑‖φ x‖) := by
    rw [neg_mul, neg_inj, div_mul_eq_mul_div, hns, Complex.ofReal_pow,
      sq, mul_div_cancel_right₀ _ hnorm_pos']
  -- Term 3: -(conj(φ x)/‖φ x‖) * -(φ x/‖φ x‖) = ‖φ x‖²/‖φ x‖² = 1
  have ht3 : -((starRingEnd ℂ) (φ x) / ↑‖φ x‖) * -(φ x / ↑‖φ x‖) = 1 := by
    rw [neg_mul_neg, div_mul_div_comm, hns, Complex.ofReal_pow, sq,
      div_self (mul_ne_zero hnorm_pos' hnorm_pos')]
  rw [ht1, ht2, ht3, one_mul] at h
  -- h : 0 ≤ (φ 0 + -↑‖φ x‖ + (-↑‖φ x‖ + φ 0)).re
  -- = 2 * (φ 0).re - 2 * ‖φ x‖
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re] at h
  have him : (φ 0).im = 0 := hpd.eval_zero_real
  linarith

/-- Pointwise product of PD functions is PD (Schur product theorem for functions).
    This is the key fact used in Phase 2 (Gaussian regularization).

    Proof idea: The Hadamard (entrywise) product of two PSD Hermitian matrices
    is PSD. For the Hermitian condition, use conj(φψ) = conj(φ)conj(ψ).
-/
lemma mul (hpd : IsPositiveDefinite φ) {ψ : α → ℂ} (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (fun x => φ x * ψ x) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [map_mul, hpd.hermitian x, hψ.hermitian x]
  · intro m x c
    let A : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => φ (x i - x j)
    let B : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => ψ (x i - x j)
    let e : Fin m → Fin m × Fin m := fun i => (i, i)
    have hA : A.PosSemidef := by simpa [A] using kernelMatrix_posSemidef hpd x
    have hB : B.PosSemidef := by simpa [B] using kernelMatrix_posSemidef hψ x
    have hK : (A ⊗ₖ B).PosSemidef := hA.kronecker hB
    have hSub : ((A ⊗ₖ B).submatrix e e).PosSemidef := hK.submatrix e
    have hnonneg := hSub.dotProduct_mulVec_nonneg c
    exact (RCLike.nonneg_iff.mp hnonneg).1.trans_eq <| by
      simp [A, B, e, dotProduct, Matrix.mulVec,
        Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

end IsPositiveDefinite
