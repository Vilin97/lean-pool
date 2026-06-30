/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Tactic.Common
/-!
# Embedding quantum kernels: density-matrix realization (expressivity)

The genuine core of Gil-Fuster, Eisert, Dunjko (2023) Theorem 1: every feature-map kernel is
realizable, up to a positive affine transform, by valid density matrices via the embedding
quantum kernel `tr{ρ(x)ρ(x')}`. Converse of `quantumKernel_gram_posSemidef`. No assumptions.
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped ComplexOrder BigOperators

variable {r : ℕ}

/-- Off-diagonal Hermitian embedding of a feature vector `v` into `Fin 1 ⊕ Fin r`. -/
noncomputable def offDiagEmb (v : Fin r → ℂ) : Matrix (Fin 1 ⊕ Fin r) (Fin 1 ⊕ Fin r) ℂ :=
  Matrix.fromBlocks 0 (Matrix.of fun _ k => v k) (Matrix.of fun k _ => starRingEnd ℂ (v k)) 0

/-- A local trace-of-block-matrix helper (`trace_fromBlocks` is not in Mathlib). -/
theorem trace_fromBlocks' {A : Matrix (Fin 1) (Fin 1) ℂ} {B : Matrix (Fin 1) (Fin r) ℂ}
    {C : Matrix (Fin r) (Fin 1) ℂ} {D : Matrix (Fin r) (Fin r) ℂ} :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type]
  congr 1

theorem offDiagEmb_isHermitian (v : Fin r → ℂ) : (offDiagEmb v).IsHermitian := by
  have hB : (Matrix.of fun (_ : Fin 1) (k : Fin r) => v k)ᴴ
      = (Matrix.of fun (k : Fin r) (_ : Fin 1) => starRingEnd ℂ (v k)) := by
    ext k i; simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  have hC : (Matrix.of fun (k : Fin r) (_ : Fin 1) => starRingEnd ℂ (v k))ᴴ
      = (Matrix.of fun (_ : Fin 1) (k : Fin r) => v k) := by
    ext i k; simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  unfold Matrix.IsHermitian offDiagEmb
  rw [Matrix.fromBlocks_conjTranspose, hB, hC]
  simp

theorem offDiagEmb_trace_zero (v : Fin r → ℂ) : (offDiagEmb v).trace = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  rintro (i | i) _ <;> simp [offDiagEmb, Matrix.diag_apply, Matrix.fromBlocks]

/-- The HS inner product of two off-diagonal embeddings: `tr(offDiagEmb v * offDiagEmb w)
= 2·Re⟨v,w⟩` (a real number). -/
theorem trace_offDiagEmb_mul (v w : Fin r → ℂ) :
    (offDiagEmb v * offDiagEmb w).trace = 2 * (∑ k, starRingEnd ℂ (v k) * w k).re := by
  rw [offDiagEmb, offDiagEmb, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [trace_fromBlocks']
  have h1 : (Matrix.of (fun (_ : Fin 1) (k : Fin r) => v k)
        * Matrix.of (fun (k : Fin r) (_ : Fin 1) => starRingEnd ℂ (w k))).trace
      = ∑ k, v k * starRingEnd ℂ (w k) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Fin.sum_univ_one, Matrix.mul_apply, Matrix.of_apply]
  have h2 : (Matrix.of (fun (k : Fin r) (_ : Fin 1) => starRingEnd ℂ (v k))
        * Matrix.of (fun (_ : Fin 1) (k : Fin r) => w k)).trace
      = ∑ k, starRingEnd ℂ (v k) * w k := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one]
  rw [h1, h2]
  have hconj : (∑ k, v k * starRingEnd ℂ (w k))
      = starRingEnd ℂ (∑ k, starRingEnd ℂ (v k) * w k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, Complex.conj_conj]
  rw [hconj, add_comm, Complex.add_conj]
  push_cast
  ring

/-- `1 + offDiagEmb v` written as a bordered block matrix. -/
theorem one_add_offDiagEmb_eq (v : Fin r → ℂ) :
    1 + offDiagEmb v
      = Matrix.fromBlocks 1 (Matrix.of fun _ k => v k)
          (Matrix.of fun k _ => starRingEnd ℂ (v k)) 1 := by
  rw [offDiagEmb,
    show (1 : Matrix (Fin 1 ⊕ Fin r) (Fin 1 ⊕ Fin r) ℂ) = Matrix.fromBlocks 1 0 0 1 from
      Matrix.fromBlocks_one.symm,
    Matrix.fromBlocks_add]
  simp

/-- **Validity crux:** `1 + offDiagEmb v` is positive semidefinite when `∑ ‖v k‖² ≤ 1`.
Proved by the `fromBlocks₂₂` Schur complement, which collapses to the `1×1` matrix
`[1 - ∑ normSq (v k)]`. -/
theorem one_add_offDiagEmb_posSemidef (v : Fin r → ℂ)
    (hv : ∑ k, Complex.normSq (v k) ≤ 1) : (1 + offDiagEmb v).PosSemidef := by
  have hBh : (Matrix.of fun (k : Fin r) (_ : Fin 1) => starRingEnd ℂ (v k))
      = (Matrix.of fun (_ : Fin 1) (k : Fin r) => v k)ᴴ := by
    ext k i; simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  haveI : Invertible (1 : Matrix (Fin r) (Fin r) ℂ) := invertibleOne
  rw [one_add_offDiagEmb_eq, hBh, Matrix.PosDef.fromBlocks₂₂ _ _ Matrix.PosDef.one]
  simp only [inv_one, Matrix.mul_one]
  -- goal: (1 - B * Bᴴ).PosSemidef, a 1×1 matrix [1 - ∑ normSq (v k)]
  have hc : (1 : Matrix (Fin 1) (Fin 1) ℂ)
        - (Matrix.of fun (_ : Fin 1) (k : Fin r) => v k)
          * (Matrix.of fun (_ : Fin 1) (k : Fin r) => v k)ᴴ
      = ((1 - ∑ k, Complex.normSq (v k) : ℝ)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i; fin_cases j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply_eq, Matrix.smul_apply]
    rw [Complex.real_smul, mul_one, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show star (v x) = (starRingEnd ℂ) (v x) from rfl, Complex.mul_conj]
  rw [hc]
  exact Matrix.PosSemidef.one.smul
    (by linarith [hv] : (0 : ℝ) ≤ 1 - ∑ k, Complex.normSq (v k))

/-- The maximally-mixed-plus-perturbation density operator for feature vector `v`. -/
noncomputable def densityOf (v : Fin r → ℂ) : Matrix (Fin 1 ⊕ Fin r) (Fin 1 ⊕ Fin r) ℂ :=
  ((r : ℝ) + 1)⁻¹ • (1 + offDiagEmb v)

theorem densityOf_posSemidef (v : Fin r → ℂ) (hv : ∑ k, Complex.normSq (v k) ≤ 1) :
    (densityOf v).PosSemidef :=
  (one_add_offDiagEmb_posSemidef v hv).smul (by positivity : (0 : ℝ) ≤ ((r : ℝ) + 1)⁻¹)

theorem densityOf_isHermitian (v : Fin r → ℂ) (hv : ∑ k, Complex.normSq (v k) ≤ 1) :
    (densityOf v).IsHermitian :=
  (densityOf_posSemidef v hv).isHermitian

theorem densityOf_trace_one (v : Fin r → ℂ) : (densityOf v).trace = 1 := by
  rw [densityOf, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, offDiagEmb_trace_zero,
    add_zero, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Complex.real_smul,
    show ((1 + r : ℕ) : ℂ) = (((r : ℝ) + 1 : ℝ) : ℂ) by
      push_cast
      ring,
    ← Complex.ofReal_mul,
    inv_mul_cancel₀ (ne_of_gt (by positivity : (0 : ℝ) < (r : ℝ) + 1)), Complex.ofReal_one]

/-- **EQK trace identity:** the embedding quantum kernel of two feature vectors is a positive
affine image of `Re⟨v,w⟩` (here in the raw form `c²·(D + 2·Re⟨v,w⟩)`,
`c = 1/D`, `D = r+1`). -/
theorem densityOf_mul_trace (v w : Fin r → ℂ) :
    (densityOf v * densityOf w).trace
      = ((((r : ℝ) + 1)⁻¹ : ℂ)) ^ 2
        * (((1 + r : ℕ) : ℂ) + 2 * (∑ k, starRingEnd ℂ (v k) * w k).re) := by
  have hT : ((1 + offDiagEmb v) * (1 + offDiagEmb w)).trace
      = ((1 + r : ℕ) : ℂ) + 2 * (∑ k, starRingEnd ℂ (v k) * w k).re := by
    have hexp : (1 + offDiagEmb v) * (1 + offDiagEmb w)
        = 1 + offDiagEmb w + offDiagEmb v + offDiagEmb v * offDiagEmb w := by noncomm_ring
    rw [hexp, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_one,
      offDiagEmb_trace_zero, offDiagEmb_trace_zero, trace_offDiagEmb_mul, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    ring
  rw [densityOf, densityOf, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
    hT, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- **Approximate universality (finite, positive-affine form), Gil-Fuster 2023 Thm 1.** Any
normalized feature map `φ` is realized by a family of genuine density matrices whose embedding
quantum kernel equals `c²·(D + 2·Re⟨φ_i,φ_j⟩)` — a positive affine image of the
feature kernel `Re⟨φ_i,φ_j⟩` (exact for real feature maps). -/
theorem eqk_realizes {ι : Type*} (φ : ι → (Fin r → ℂ))
    (hφ : ∀ i, ∑ k, Complex.normSq (φ i k) ≤ 1) :
    (∀ i, (densityOf (φ i)).IsHermitian ∧ (densityOf (φ i)).trace = 1
        ∧ (densityOf (φ i)).PosSemidef)
    ∧ ∀ i j, (densityOf (φ i) * densityOf (φ j)).trace
        = ((((r : ℝ) + 1)⁻¹ : ℂ)) ^ 2
          * (((1 + r : ℕ) : ℂ) + 2 * (∑ k, starRingEnd ℂ (φ i k) * φ j k).re) :=
  ⟨fun i =>
      ⟨densityOf_isHermitian _ (hφ i), densityOf_trace_one _,
        densityOf_posSemidef _ (hφ i)⟩,
    fun _ _ => densityOf_mul_trace _ _⟩

/-- Non-vacuity: a concrete two-input feature map gives valid density matrices realizing a
non-constant embedding quantum kernel. -/
theorem eqk_nonempty :
    ∃ (r : ℕ) (φ : Fin 2 → (Fin r → ℂ)),
      (∀ i, (densityOf (φ i)).PosSemidef ∧ (densityOf (φ i)).trace = 1)
      ∧ (densityOf (φ 0) * densityOf (φ 0)).trace
          ≠ (densityOf (φ 0) * densityOf (φ 1)).trace := by
  refine ⟨1, ![![1], ![0]], ?_, ?_⟩
  · intro i
    refine ⟨densityOf_posSemidef _ ?_, densityOf_trace_one _⟩
    fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [densityOf_mul_trace, densityOf_mul_trace]
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, map_one, mul_zero,
      mul_one]
    norm_num

end QuantumAlg
