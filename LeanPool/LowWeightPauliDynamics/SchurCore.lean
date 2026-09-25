/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Shared finite Schur test

The finite rectangular Schur test over an `RCLike` field, together with its rowwise,
sum-of-squares, and continuous-linear-map formulations. Empty index types are allowed.

Moved from `LeanPool.LowWeightPauliDynamics.Schur` and its matrix-map abbreviation from
`LeanPool.LowWeightPauliDynamics.BlockNorm`, preserving Jue Xu's proofs and public names.
This lightweight module depends only on Mathlib and is shared by the Pauli-dynamics and
block/spectral-sensitivity developments.
-/

public section

namespace Lean4LPD

open Finset Matrix WithLp
open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The continuous linear map on `EuclideanSpace` attached to a (possibly rectangular) matrix.
This is the map whose operator norm *is* `‖A‖` for the scoped ℓ² operator norm, by
`Matrix.l2_opNorm_def`; for square matrices it agrees with `Matrix.toEuclideanCLM`. -/
noncomputable abbrev clm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m :=
  (Matrix.toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans LinearMap.toContinuousLinearMap A

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
/-- Weighted Cauchy–Schwarz for one row: if row `i` of `A` has absolute sum at most `R`, then
`‖(A *ᵥ y) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2`. This is the row step of the Schur test used
in `apd:thm:layer_inflow`. Zero entries and empty sums need no separate case. -/
theorem schur_row_sq_le (A : Matrix ι κ 𝕜) (y : κ → 𝕜) (i : ι) (R : ℝ)
    (hrow : ∑ j, ‖A i j‖ ≤ R) :
    ‖(A *ᵥ y) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2 := by
  have habs : ‖(A *ᵥ y) i‖ ≤ ∑ j, ‖A i j‖ * ‖y j‖ := by
    simpa only [Matrix.mulVec, dotProduct, norm_mul] using
      (norm_sum_le univ (fun j => A i j * y j))
  have hcs : (∑ j, ‖A i j‖ * ‖y j‖) ^ 2 ≤
      (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul univ
      (f := fun j => ‖A i j‖) (g := fun j => ‖A i j‖ * ‖y j‖ ^ 2)
    · intro j _; exact norm_nonneg _
    · intro j _; positivity
    · intro j _; exact le_of_eq (by ring)
  exact ((pow_le_pow_left₀ (norm_nonneg _) habs 2).trans hcs).trans
    (mul_le_mul_of_nonneg_right hrow (Finset.sum_nonneg fun j _ => by positivity))

/-- Squared form of the finite Schur test used in `apd:thm:layer_inflow`: if every row of `A`
has absolute sum at most `R` and every column at most `C`, then
`∑ i, ‖(A *ᵥ y) i‖ ^ 2 ≤ R * C * ∑ j, ‖y j‖ ^ 2`. -/
theorem schur_mulVec_sq_le (A : Matrix ι κ 𝕜) (y : κ → 𝕜) {R C : ℝ}
    (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    (∑ i, ‖(A *ᵥ y) i‖ ^ 2) ≤ R * C * ∑ j, ‖y j‖ ^ 2 := by
  have h1 : (∑ i, ‖(A *ᵥ y) i‖ ^ 2) ≤
      ∑ i, R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => schur_row_sq_le A y i R (hrow i)
  have h2 : (∑ i, R * ∑ j, ‖A i j‖ * ‖y j‖ ^ 2) =
      R * ∑ j, (∑ i, ‖A i j‖) * ‖y j‖ ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
  calc (∑ i, ‖(A *ᵥ y) i‖ ^ 2)
      ≤ R * ∑ j, (∑ i, ‖A i j‖) * ‖y j‖ ^ 2 := h1.trans_eq h2
    _ ≤ R * ∑ j, C * ‖y j‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)) hR
    _ = R * C * ∑ j, ‖y j‖ ^ 2 := by rw [← Finset.mul_sum, mul_assoc]

variable [DecidableEq κ]

/-- The Schur test as a bound on the action of `clm A`, the continuous linear map of Euclidean
spaces attached to `A` in `BlockNorm`: `‖clm A y‖ ≤ √(R * C) * ‖y‖` (`apd:thm:layer_inflow`). -/
theorem schur_clm_le (A : Matrix ι κ 𝕜) (y : EuclideanSpace 𝕜 κ) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖clm A y‖ ≤ Real.sqrt (R * C) * ‖y‖ := by
  have hsq : ‖clm A y‖ ^ 2 ≤ (Real.sqrt (R * C) * ‖y‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hR hC)]
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact schur_mulVec_sq_le A y.ofLp hR hrow hcol
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))] at h

omit [DecidableEq κ] in
/-- The same bound for `Matrix.mulVec`, without the bundled map `clm A`. The norm is the
Euclidean norm that Pauli coefficient vectors carry (`apd:thm:layer_inflow`). -/
theorem schur_mulVec_le (A : Matrix ι κ 𝕜) (y : EuclideanSpace 𝕜 κ) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖toLp 2 (A *ᵥ y.ofLp)‖ ≤ Real.sqrt (R * C) * ‖y‖ := by
  classical
  exact schur_clm_le A y hR hC hrow hcol

/-- **The finite Schur test**, in the form used by `apd:thm:layer_inflow`: row sums at most `R`
and column sums at most `C` give `‖A‖ ≤ √(R * C)`. Here `‖A‖` is the scoped **ℓ² operator norm**
(`Matrix.Norms.L2Operator`), not an entrywise matrix norm. -/
theorem l2_opNorm_le_schur (A : Matrix ι κ 𝕜) {R C : ℝ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) : ‖A‖ ≤ Real.sqrt (R * C) := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (fun y => schur_clm_le A y hR hC hrow hcol)

/-- If `B` bounds every row sum and every column sum, then `‖A‖ ≤ B`: the case `R = C = B` of
`l2_opNorm_le_schur`. This is the form `Pauli/LayerFlow` applies to the layer inflow matrices
(`apd:thm:layer_inflow`). -/
theorem l2_opNorm_le_of_row_col_bound (A : Matrix ι κ 𝕜) {B : ℝ}
    (hB : 0 ≤ B) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ B)
    (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ B) : ‖A‖ ≤ B := by
  have h := l2_opNorm_le_schur A hB hB hrow hcol
  simpa only [← sq, Real.sqrt_sq hB] using h

end Lean4LPD
