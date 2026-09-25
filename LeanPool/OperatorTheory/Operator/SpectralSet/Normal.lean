/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module


public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import LeanPool.OperatorTheory.Operator.Crouzeix.VonNeumann

/-!
# Polynomials in a normal element — the sup-norm bound

For a normal element `a` of a C*-algebra and a compact set `K ⊇ σ(a)`,
`‖p(a)‖ ≤ sup_{z ∈ K} ‖p(z)‖` for every polynomial `p`: `p(a)` is normal, so its norm is its
spectral radius, and `σ(p(a)) = p(σ(a)) ⊆ p(K)` by the spectral mapping theorem.

## Main declarations

* `norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval` — the same bound under the
  weaker hypothesis that the single element `p(a)` is normal.
* `norm_aeval_le_polynomialSupNorm_of_isStarNormal` — the bound above, in any C*-algebra.

Consumers: unitaries with `K` the closed unit disk (`Crouzeix/VonNeumann.lean`), and normal
operators on a Hilbert space with `K = closure W(A)` (`Crouzeix/Palencia.lean`).
-/

@[expose] public section

open Polynomial

/-- If the single element `p(a)` is normal and `K` is compact with `K ⊇ σ(a)`, then
`‖p(a)‖ ≤ polynomialSupNorm p K`.  Normality of `a` itself is not needed. -/
theorem norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval {A : Type*} [CStarAlgebra A]
    (a : A) {K : Set ℂ} (hK : IsCompact K) (hσ : spectrum ℂ a ⊆ K)
    (p : ℂ[X]) [IsStarNormal (aeval a p)] :
    ‖aeval a p‖ ≤ polynomialSupNorm p K := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (aeval a p) 0, norm_zero]
    exact polynomialSupNorm_nonneg p _
  have hM0 : 0 ≤ polynomialSupNorm p K := polynomialSupNorm_nonneg p _
  have hbound : spectralRadius ℂ (aeval a p) ≤ ((polynomialSupNorm p K).toNNReal : ENNReal) := by
    rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun k hk => ?_
    rw [spectrum.map_polynomial_aeval] at hk
    obtain ⟨z, hz, rfl⟩ := hk
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM0]
    exact norm_eval_le_polynomialSupNorm p (bddAbove_norm_eval_image_of_isCompact p hK) (hσ hz)
  rw [IsStarNormal.spectralRadius_eq_nnnorm (aeval a p), ENNReal.coe_le_coe,
    ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM0] at hbound
  exact hbound

/-- For a normal element `a` of a C*-algebra and a compact `K ⊇ σ(a)`,
`‖p(a)‖ ≤ polynomialSupNorm p K`: `p(a)` is normal, so `‖p(a)‖` is its spectral radius, and
`σ(p(a)) = p(σ(a))` by the spectral mapping theorem. -/
theorem norm_aeval_le_polynomialSupNorm_of_isStarNormal {A : Type*} [CStarAlgebra A]
    (a : A) [IsStarNormal a] {K : Set ℂ} (hK : IsCompact K) (hσ : spectrum ℂ a ⊆ K)
    (p : ℂ[X]) : ‖aeval a p‖ ≤ polynomialSupNorm p K := by
  have hnormal : IsStarNormal (aeval a p) := by
    rw [← cfc_polynomial p a]
    exact cfc_predicate _ a
  let _ := hnormal
  exact norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval a hK hσ p

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
