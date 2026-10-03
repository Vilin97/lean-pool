/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Construction
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Rat.Star
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # The degree of `Δ_K` and `F_K` — formula (2.9) of the paper

The entries of `G_K(X)` are affine in `X`; the coefficient of `X^h` in `Δ_K = det G_K` is the
determinant of the matrix of `X`-coefficients, which is `Vᵀ diag(w) V` for the Vandermonde
matrix `V` of the nodes `-j²`, `N < j ≤ K`, with nonzero weights `w`. Hence `deg Δ_K = h`.
-/

public section

open Polynomial Matrix Finset

namespace Zeta5Irrational

lemma coeff_det_of_natDegree_le_one {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R[X]) (hM : ∀ i j, (M i j).natDegree ≤ 1) :
    (M.det).coeff n = (Matrix.of fun i j => (M i j).coeff 1).det ∧ M.det.natDegree ≤ n := by
  constructor
  · rw [det_apply', det_apply', finsetSum_coeff]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hc :=
      coeff_prod_of_natDegree_le (s := Finset.univ) (f := fun i => M (σ i) i) (n := 1)
        (fun i _ => hM _ _)
    simp only [Finset.card_univ, Fintype.card_fin, mul_one] at hc
    rw [← C_eq_intCast, coeff_C_mul, hc]
    simp
  · rw [det_apply']
    refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_intCast, zero_add]
    refine (natDegree_prod_le _ _).trans ?_
    calc
      ∑ i : Fin n, (M (σ i) i).natDegree ≤ ∑ i : Fin n, 1 := Finset.sum_le_sum fun i _ => hM _ _
      _ = n := by simp

/-- Residue coefficient at the pole `-j²` of `P / D K`, for `1 ≤ j ≤ K`. -/
@[expose] noncomputable def res (K : ℕ) (P : ℚ[X]) (j : ℕ) : ℚ :=
  P.eval (-(j : ℚ) ^ 2) / (derivative (D K)).eval (-(j : ℚ) ^ 2)

lemma poleValue_eq (j : ℕ) :
    poleValue j = C ((j : ℚ) ^ 4) * X + C (-(j : ℚ) ^ 4 * H5 j - 1 / 4 + 1 / (2 * (j : ℚ))) := by
  simp only [poleValue, C_add, C_sub, C_mul, C_neg, C_pow]
  ring

lemma μX_eq (K : ℕ) (P : ℚ[X]) :
    μX K P =
      C (∑ j ∈ Icc 1 K, res K P j * (j : ℚ) ^ 4) * X +
        C
          (μpoly (P /ₘ D K) +
            ∑ j ∈ Icc 1 K, res K P j * (-(j : ℚ) ^ 4 * H5 j - 1 / 4 + 1 / (2 * (j : ℚ)))) := by
  simp only [μX, res, poleValue_eq, mul_add, ← mul_assoc, ← C_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← map_sum, C_add]
  ring

lemma natDegree_μX_le (K : ℕ) (P : ℚ[X]) : (μX K P).natDegree ≤ 1 := by
  rw [μX_eq]
  compute_degree!

lemma coeff_μX_one (K : ℕ) (P : ℚ[X]) :
    (μX K P).coeff 1 = ∑ j ∈ Icc 1 K, res K P j * (j : ℚ) ^ 4 := by
  rw [μX_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C, mul_one, one_ne_zero, ite_false,
    add_zero]

lemma eval_D (m : ℕ) (x : ℚ) : (D m).eval x = ∏ j ∈ Icc 1 m, (x + (j : ℚ) ^ 2) := by
  simp [D, eval_prod]

lemma eval_D_eq_zero {m j : ℕ} (hj : j ∈ Icc 1 m) : (D m).eval (-(j : ℚ) ^ 2) = 0 := by
  rw [eval_D]
  exact Finset.prod_eq_zero hj (by ring)

lemma eval_D_ne_zero {m j : ℕ} (hj : m < j) : (D m).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [eval_D]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  have h1 : (i : ℚ) < j := by exact_mod_cast (by omega : i < j)
  have h2 : (0 : ℚ) ≤ i := by positivity
  nlinarith

lemma eval_derivative_D {K j : ℕ} (hj : j ∈ Icc 1 K) :
    (derivative (D K)).eval (-(j : ℚ) ^ 2) =
      ∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) := by
  rw [D, derivative_prod_finset, eval_finsetSum, Finset.sum_eq_single j]
  · simp only [derivative_add, derivative_X, derivative_C, add_zero, mul_one, eval_prod, eval_add,
      eval_X, eval_C]
    exact Finset.prod_congr rfl fun i _ => by ring
  · intro b _ hb
    rw [eval_mul, eval_prod]
    exact
      mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb.symm, hj⟩) (by simp)) _
  · intro h; exact absurd hj h

lemma eval_derivative_D_ne_zero {K j : ℕ} (hj : j ∈ Icc 1 K) :
    (derivative (D K)).eval (-(j : ℚ) ^ 2) ≠ 0 := by
  rw [eval_derivative_D hj]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  have : (i : ℚ) ≠ j := by exact_mod_cast hij
  have h0i : (0 : ℚ) ≤ i := by positivity
  have h0j : (0 : ℚ) ≤ j := by positivity
  intro h
  have hfac : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact this (by linarith)
  · have hj1 : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    linarith

/-- Reindexing: a sum over `Icc 1 K` whose terms vanish on `Icc 1 N` is a sum over
`k : Fin (K - N)` of the terms at `N + 1 + k`. -/
lemma sum_Icc_eq_sum_fin (N K : ℕ) (hNK : N ≤ K) (f : ℕ → ℚ) (hf : ∀ j ∈ Icc 1 N, f j = 0) :
    ∑ j ∈ Icc 1 K, f j = ∑ k : Fin (K - N), f (N + 1 + k) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => f (N + 1 + k)) (K - N)]
  have h1 := Finset.sum_Ico_eq_sum_range f (N + 1) (K + 1)
  rw [show K + 1 - (N + 1) = K - N by omega] at h1
  rw [← h1]
  have h2 : Icc 1 K = Ico 1 (K + 1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h2, ← Finset.sum_Ico_consecutive f (show 1 ≤ N + 1 by omega) (show N + 1 ≤ K + 1 by omega)]
  rw [Finset.sum_eq_zero (fun j hj => hf j ?_), zero_add]
  rw [Finset.mem_Ico] at hj
  rw [Finset.mem_Icc]; omega

/-- The nodes `x_k = -(N + 1 + k)²`, `k < h`. -/
noncomputable def node (n : ℕ) (k : Fin (37 * n)) : ℚ :=
  -((3 * n + 1 + (k : ℕ) : ℕ) : ℚ) ^ 2

/-- The weights `w_k = D_N(x_k)^6 (N + 1 + k)^4 / D_K'(x_k)`. -/
noncomputable def weight (n : ℕ) (k : Fin (37 * n)) : ℚ :=
  (D (3 * n)).eval (node n k) ^ 6 * ((3 * n + 1 + (k : ℕ) : ℕ) : ℚ) ^ 4 /
    (derivative (D (40 * n))).eval (node n k)

lemma natDegree_G_le (n : ℕ) (i j : Fin (37 * n)) : (G n i j).natDegree ≤ 1 :=
  natDegree_μX_le _ _

/-- The matrix of `X`-coefficients of `G_K(X)` is `Vᵀ diag(w) V` with `V` the Vandermonde
matrix of the nodes. -/
lemma coeff_G_one (n : ℕ) :
    (Matrix.of fun i j : Fin (37 * n) => (G n i j).coeff 1) =
      (vandermonde (node n))ᵀ * diagonal (weight n) * vandermonde (node n) := by
  ext i j
  simp only [Matrix.of_apply, G, coeff_μX_one, res]
  rw [sum_Icc_eq_sum_fin (3 * n) (40 * n) (by omega)
      (fun j' =>
        eval (-(j' : ℚ) ^ 2) (D (3 * n) ^ 6 * X ^ ((i : ℕ) + (j : ℕ))) /
            eval (-(j' : ℚ) ^ 2) (derivative (D (40 * n))) *
          (j' : ℚ) ^ 4)
      (fun j' hj' => by rw [eval_mul, eval_pow, eval_D_eq_zero hj']; simp)]
  rw [show 40 * n - 3 * n = 37 * n by omega]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, vandermonde_apply, weight, node,
    eval_mul, eval_pow, eval_X]
  rw [pow_add]
  ring

lemma node_injective (n : ℕ) : Function.Injective (node n) := by
  intro k₁ k₂ h
  simp only [node, neg_inj] at h
  have h' : (3 * n + 1 + (k₁ : ℕ)) ^ 2 = (3 * n + 1 + (k₂ : ℕ)) ^ 2 := by exact_mod_cast h
  have := Nat.pow_left_injective (by norm_num : 2 ≠ 0) h'
  exact Fin.ext (by omega)

lemma weight_ne_zero (n : ℕ) (k : Fin (37 * n)) : weight n k ≠ 0 := by
  have hk := k.isLt
  have h1 : (D (3 * n)).eval (node n k) ≠ 0 := eval_D_ne_zero (by omega)
  have h2 : (derivative (D (40 * n))).eval (node n k) ≠ 0 :=
    eval_derivative_D_ne_zero (by rw [Finset.mem_Icc]; omega)
  have h3 : ((3 * n + 1 + (k : ℕ) : ℕ) : ℚ) ≠ 0 := by positivity
  unfold weight
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h3)) h2

lemma det_coeff_G_one_ne_zero (n : ℕ) :
    (Matrix.of fun i j : Fin (37 * n) => (G n i j).coeff 1).det ≠ 0 := by
  rw [coeff_G_one, det_mul, det_mul, det_transpose, det_diagonal]
  have hV : (vandermonde (node n)).det ≠ 0 := det_vandermonde_ne_zero_iff.mpr (node_injective n)
  exact
    mul_ne_zero (mul_ne_zero hV (Finset.prod_ne_zero_iff.mpr fun k _ => weight_ne_zero n k)) hV

/-- **(2.9)**: `Δ_K` has degree exactly `h = 37 n`. -/
theorem natDegree_Δ (n : ℕ) : (Δ n).natDegree = 37 * n := by
  obtain ⟨hc, hd⟩ := coeff_det_of_natDegree_le_one (G n) (natDegree_G_le n)
  exact natDegree_eq_of_le_of_coeff_ne_zero hd (hc ▸ det_coeff_G_one_ne_zero n)

lemma S_pos (n : ℕ) : 0 < S n := by
  unfold S
  positivity

/-- **(2.9)**: `F_K` has degree exactly `h = 37 n`. -/
theorem natDegree_F (n : ℕ) : (F n).natDegree = 37 * n := by
  rw [F, natDegree_C_mul (S_pos n).ne', natDegree_Δ]

end Zeta5Irrational
