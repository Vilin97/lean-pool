/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Differentiation

/-!
# The resolvent `(I + Δ)⁻¹` on momentum space

With the positive Laplacian `Δ = -∑ⱼ ∂ⱼ²` (Wassermann's sign convention), the
Fourier coefficients satisfy `(Δf)^(m) = |m|² f̂(m)`, so `(I + Δ)⁻¹` is the
Fourier multiplier `1 / (1 + |m|²) = weight n (-1) m`. On weighted `ℓ²` it is an
isometry `ℓ²_(s) → ℓ²_(s+2)` and commutes with the formal derivatives
`partialCoeff`. These are the coefficient-side facts used by Günther's
fixed-point operator in Theorem B.
-/

open scoped BigOperators
open NashEmbedding.Sobolev

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-- The (positive) Laplacian on coefficients: `(Δa)ₘ = |m|² aₘ`. -/
def laplacianCoeff (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) : ℂ :=
  ((∑ i : Fin n, ((m i : ℝ) ^ 2) : ℝ) : ℂ) * a m

/-- The resolvent `(I + Δ)⁻¹` on coefficients: `aₘ / (1 + |m|²)`. -/
def resolventCoeff (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) : ℂ :=
  a m / ((1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) : ℝ) : ℂ)

lemma weight_one (m : Fin n → ℤ) : weight n 1 m = 1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) := by
  unfold weight; simp

lemma one_add_sum_sq_pos (m : Fin n → ℤ) : 0 < 1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) := by
  positivity

lemma norm_resolventCoeff (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) :
    ‖resolventCoeff a m‖ = ‖a m‖ / weight n 1 m := by
  unfold resolventCoeff
  rw [norm_div, weight_one, Complex.norm_real, Real.norm_of_nonneg (one_add_sum_sq_pos m).le]

/-- `(I + Δ) ∘ (I + Δ)⁻¹ = I`. -/
lemma resolventCoeff_add_laplacianCoeff (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) :
    resolventCoeff a m + laplacianCoeff (resolventCoeff a) m = a m := by
  unfold resolventCoeff laplacianCoeff
  have h : ((1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (one_add_sum_sq_pos m).ne'
  field_simp
  push_cast
  ring

/-- `(I + Δ)⁻¹ ∘ (I + Δ) = I`. -/
lemma resolventCoeff_of_add_laplacianCoeff (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) :
    resolventCoeff (fun k => a k + laplacianCoeff a k) m = a m := by
  unfold resolventCoeff laplacianCoeff
  have h : ((1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (one_add_sum_sq_pos m).ne'
  field_simp
  push_cast
  ring

/-- The resolvent commutes with formal partial derivatives. -/
lemma resolventCoeff_partialCoeff (a : (Fin n → ℤ) → ℂ) (j : Fin n) :
    resolventCoeff (partialCoeff j a) = partialCoeff j (resolventCoeff a) := by
  funext m
  unfold resolventCoeff partialCoeff
  ring

/-- Weighted-norm identity: `weight (s+2) · |(I+Δ)⁻¹ a|² = weight s · |a|²` termwise. -/
lemma weight_norm_resolventCoeff_sq (s : ℝ) (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) :
    weight n (s + 2) m * ‖resolventCoeff a m‖ ^ 2 = weight n s m * ‖a m‖ ^ 2 := by
  rw [norm_resolventCoeff, div_pow, show (s + 2 : ℝ) = s + 1 + 1 by ring,
    ← weight_mul, ← weight_mul]
  have h := (weight_pos (n := n) 1 m).ne'
  field_simp

/-- `(I + Δ)⁻¹ : ℓ²_(s) → ℓ²_(s+2)`. -/
lemma memSobolev_resolventCoeff {s : ℝ} {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) :
    MemSobolev n (s + 2) (resolventCoeff a) := by
  unfold MemSobolev at *
  simpa only [weight_norm_resolventCoeff_sq] using ha

/-- `(I + Δ)⁻¹` is an isometry `ℓ²_(s) → ℓ²_(s+2)`. -/
lemma sobolevNormSq_resolventCoeff (s : ℝ) (a : (Fin n → ℤ) → ℂ) :
    sobolevNormSq n (s + 2) (resolventCoeff a) = sobolevNormSq n s a := by
  unfold sobolevNormSq
  simp only [weight_norm_resolventCoeff_sq]

/-- Termwise bound for the Laplacian: `weight s · |Δa|² ≤ weight (s+2) · |a|²`. -/
lemma weight_norm_laplacianCoeff_sq_le (s : ℝ) (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) :
    weight n s m * ‖laplacianCoeff a m‖ ^ 2 ≤ weight n (s + 2) m * ‖a m‖ ^ 2 := by
  unfold laplacianCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow,
    show (s + 2 : ℝ) = s + 1 + 1 by ring, ← weight_mul, ← weight_mul, weight_one]
  have hw := weight_nonneg (n := n) s m
  have hS : 0 ≤ ∑ i : Fin n, ((m i : ℝ) ^ 2) := by positivity
  have h1 : (∑ i : Fin n, ((m i : ℝ) ^ 2)) ^ 2 ≤ (1 + ∑ i : Fin n, ((m i : ℝ) ^ 2)) *
      (1 + ∑ i : Fin n, ((m i : ℝ) ^ 2)) := by nlinarith
  have hn2 := sq_nonneg ‖a m‖
  calc weight n s m * ((∑ i : Fin n, ((m i : ℝ) ^ 2)) ^ 2 * ‖a m‖ ^ 2)
      ≤ weight n s m * ((1 + ∑ i : Fin n, ((m i : ℝ) ^ 2)) *
          (1 + ∑ i : Fin n, ((m i : ℝ) ^ 2)) * ‖a m‖ ^ 2) := by gcongr
    _ = _ := by ring

/-- `Δ : ℓ²_(s+2) → ℓ²_(s)`. -/
lemma memSobolev_laplacianCoeff {s : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n (s + 2) a) : MemSobolev n s (laplacianCoeff a) := by
  unfold MemSobolev at *
  exact Summable.of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg _ _) (sq_nonneg _))
    (fun m => weight_norm_laplacianCoeff_sq_le s a m) ha

lemma sobolevNormSq_laplacianCoeff_le {s : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : MemSobolev n (s + 2) a) :
    sobolevNormSq n s (laplacianCoeff a) ≤ sobolevNormSq n (s + 2) a := by
  unfold sobolevNormSq
  exact Summable.tsum_le_tsum (fun m => weight_norm_laplacianCoeff_sq_le s a m)
    (memSobolev_laplacianCoeff ha) ha

end NashEmbedding.Sobolev

end
