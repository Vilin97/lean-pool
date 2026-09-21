/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T19.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/PiL2.lean`
(the `ℓ¹ ≤ √card · ℓ²` bound) and `Mathlib/Analysis/Matrix/Normed.lean` (the
entrywise → `ℓ²`-operator-norm bound).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Chebyshev


/-! # `ℓ¹`–`ℓ²` and entrywise–operator norm comparisons

Two elementary norm comparisons that are absent from Mathlib (which has the
`ℓ²`-operator-norm API in `Mathlib/Analysis/CStarAlgebra/Matrix.lean` but no
bound of it by the entrywise norm):

* on `EuclideanSpace 𝕜 ι`, `∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖` (Cauchy–Schwarz /
  Chebyshev);
* for an `RCLike` `n × n` matrix with entries bounded by `ε`, the induced Euclidean
  operator `Matrix.toEuclideanLin A` has `‖A x‖ ≤ n ε ‖x‖`.

## Main results

* `TauCeti.sum_norm_le_sqrt_card_mul_norm`
* `TauCeti.norm_toEuclideanLin_le_of_entry_le`

The matrix estimate uses the scalar norm over any `RCLike` field. Apply the triangle
inequality in each row, then the two `l1`-to-`l2` estimates. For an `n` by `n`
matrix with every entry bounded by `epsilon`, the resulting constant is `n * epsilon`.
This includes `n = 0` without a nonnegativity assumption on the entry bound.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.Matrix.EntrywiseOpNorm`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `7366186`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped BigOperators
open Matrix

/--
**`ℓ¹ ≤ √card · ℓ²` on Euclidean space.** For `x : EuclideanSpace 𝕜 ι`,
`∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖`.
-/
theorem sum_norm_le_sqrt_card_mul_norm {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    (x : EuclideanSpace 𝕜 ι) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  have hcs : (∑ i, ‖x i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
    simpa [Finset.card_univ] using
      sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖x i‖)
  have hnorm : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  have hsum_nonneg : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hrhs_nonneg : 0 ≤ Real.sqrt (Fintype.card ι) * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq : (∑ i, ‖x i‖) ^ 2 ≤ (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 := by
    have hrw : (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 = (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Fintype.card ι : ℝ))]
    rw [hrw, hnorm]; exact hcs
  exact (abs_le_of_sq_le_sq' hsq hrhs_nonneg).2

/-- An entrywise scalar-norm bound gives a Euclidean operator bound, over `RCLike`. -/
theorem norm_toEuclideanLin_le_of_entry_le {𝕜 : Type*} [RCLike 𝕜]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜}
    {ε : ℝ} (hentry : ∀ i j, ‖A i j‖ ≤ ε)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * ε * ‖x‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : Matrix.toEuclideanLin A x = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    simp
  · have heps : 0 ≤ ε := (norm_nonneg _).trans (hentry ⟨0, hn⟩ ⟨0, hn⟩)
    have hrow : ∀ i : Fin n,
        ‖(Matrix.toEuclideanLin A x) i‖ ≤ ε * (Real.sqrt n * ‖x‖) := by
      intro i
      have happ : (Matrix.toEuclideanLin A x) i = ∑ j : Fin n, A i j * x j := by
        change (A.mulVec (WithLp.ofLp x)) i = _
        simp [Matrix.mulVec, dotProduct]
      calc
        ‖(Matrix.toEuclideanLin A x) i‖ = ‖∑ j : Fin n, A i j * x j‖ := by rw [happ]
        _ ≤ ∑ j : Fin n, ‖A i j * x j‖ := norm_sum_le _ _
        _ = ∑ j : Fin n, ‖A i j‖ * ‖x j‖ := by simp only [norm_mul]
        _ ≤ ∑ j : Fin n, ε * ‖x j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hentry i j) (norm_nonneg _)
        _ = ε * ∑ j : Fin n, ‖x j‖ := by rw [Finset.mul_sum]
        _ ≤ ε * (Real.sqrt n * ‖x‖) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa using sum_norm_le_sqrt_card_mul_norm x) heps
    have hnorm_sq : ‖Matrix.toEuclideanLin A x‖ ^ 2
        ≤ (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc
        ∑ i : Fin n, ‖(Matrix.toEuclideanLin A x) i‖ ^ 2
            ≤ ∑ _i : Fin n, (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
        _ = (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have hsq_eq : ((n : ℝ) * ε * ‖x‖) ^ 2 =
        (n : ℝ) * (ε * (Real.sqrt n * ‖x‖)) ^ 2 := by
      simp only [mul_pow, hs]
      ring
    have hle : ‖Matrix.toEuclideanLin A x‖ ^ 2
        ≤ ((n : ℝ) * ε * ‖x‖) ^ 2 := by
      rw [hsq_eq]
      exact hnorm_sq
    exact (abs_le_of_sq_le_sq' hle (by positivity)).2

end TauCeti
