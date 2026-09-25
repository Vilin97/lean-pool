/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Foundation
public import LeanPool.ParameterFreeGradient.O3.Stage2RouteC
public import LeanPool.ParameterFreeGradient.O3.Stage2RouteD

/-!
# Stage 8: the canonical Euclidean estimate potential

This module gives the literal finite-dimensional quadratic potential used in
Phase A of the Euclidean branch.  Its minimizer and exact strong lower bound
are derived from the project's explicit `lpNorm 2`; no ambient-norm shortcut
or minimizer certificate is used.
-/

@[expose] public section

namespace O3
namespace Stage8EuclideanMinimizer

/-- The canonical representation of the recursive Euclidean estimate
potential.  The vector `s` is the accumulated weighted gradient and `c`
contains the accumulated affine offsets. -/
noncomputable def euclideanPsi (M : ℝ) {d : ℕ}
    (x₀ s : Point d) (c : ℝ) (x : Point d) : ℝ :=
  M / 2 * (lpNorm 2 (x - x₀)) ^ (2 : ℕ) + c + pairing s (x - x₀)

/-- The explicit minimizer `x₀ - M⁻¹ s` of the canonical potential. -/
noncomputable def euclideanPsiMinimizer (M : ℝ) {d : ℕ}
    (x₀ s : Point d) : Point d :=
  x₀ - M⁻¹ • s

/-- Polarization for the literal O3 `lpNorm 2`. -/
theorem lpNorm_two_sq_sub_decomposition {d : ℕ} (x z x₀ : Point d) :
    (lpNorm 2 (x - x₀)) ^ (2 : ℕ) =
      (lpNorm 2 (z - x₀)) ^ (2 : ℕ) +
        2 * pairing (z - x₀) (x - z) +
        (lpNorm 2 (x - z)) ^ (2 : ℕ) := by
  simp_rw [Stage2RouteC.lpNorm_two_sq]
  simp only [pairing, Pi.sub_apply]
  calc
    (∑ i, (x i - x₀ i) ^ (2 : ℕ)) =
        ∑ i, ((z i - x₀ i) ^ (2 : ℕ) +
          2 * ((z i - x₀ i) * (x i - z i)) +
          (x i - z i) ^ (2 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, (z i - x₀ i) ^ (2 : ℕ)) +
          (∑ i, 2 * ((z i - x₀ i) * (x i - z i))) +
          ∑ i, (x i - z i) ^ (2 : ℕ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = _ := by rw [Finset.mul_sum]

/-- Affine displacement identity for the coordinate pairing. -/
theorem pairing_sub_decomposition {d : ℕ} (s x z x₀ : Point d) :
    pairing s (x - x₀) = pairing s (z - x₀) + pairing s (x - z) := by
  simp only [pairing, Pi.sub_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The explicit point satisfies the exact first-order cancellation equation. -/
theorem euclideanPsiMinimizer_firstOrder {M : ℝ} (hM : M ≠ 0) {d : ℕ}
    (x₀ s : Point d) :
    M • (euclideanPsiMinimizer M x₀ s - x₀) + s = 0 := by
  funext i
  simp only [euclideanPsiMinimizer, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply]
  field_simp [hM]
  ring

/-- Pairing form of the first-order cancellation, used by the exact square
completion. -/
theorem euclideanPsiMinimizer_pairing_cancel {M : ℝ} (hM : M ≠ 0)
    {d : ℕ} (x₀ s x : Point d) :
    M * pairing (euclideanPsiMinimizer M x₀ s - x₀)
        (x - euclideanPsiMinimizer M x₀ s) +
      pairing s (x - euclideanPsiMinimizer M x₀ s) = 0 := by
  rw [← Stage2RouteD.pairing_smul_left, ← Stage2RouteD.pairing_add_left]
  rw [euclideanPsiMinimizer_firstOrder hM]
  simp [pairing]

/-- Exact completion-of-the-square identity.  This is stronger than the
needed lower bound and exposes the precise `M / 2` coefficient. -/
theorem euclideanPsi_eq_min_add_sq {M : ℝ} (hM : M ≠ 0) {d : ℕ}
    (x₀ s : Point d) (c : ℝ) (x : Point d) :
    euclideanPsi M x₀ s c x =
      euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) +
        M / 2 *
          (lpNorm 2 (x - euclideanPsiMinimizer M x₀ s)) ^ (2 : ℕ) := by
  let z := euclideanPsiMinimizer M x₀ s
  have hsq := lpNorm_two_sq_sub_decomposition x z x₀
  have hlin := pairing_sub_decomposition s x z x₀
  have hcancel := euclideanPsiMinimizer_pairing_cancel hM x₀ s x
  have hcancelz :
      M * pairing (z - x₀) (x - z) + pairing s (x - z) = 0 := by
    simpa only [z] using hcancel
  change M / 2 * lpNorm 2 (x - x₀) ^ (2 : ℕ) + c + pairing s (x - x₀) =
    (M / 2 * lpNorm 2 (z - x₀) ^ (2 : ℕ) + c + pairing s (z - x₀)) +
      M / 2 * lpNorm 2 (x - z) ^ (2 : ℕ)
  rw [hsq, hlin]
  linear_combination hcancelz

/-- Exact `M`-strong lower bound at the explicit minimizer. -/
theorem euclideanPsi_strongLower_at_minimizer {M : ℝ} (hM : 0 < M) {d : ℕ}
    (x₀ s : Point d) (c : ℝ) (x : Point d) :
    euclideanPsi M x₀ s c x ≥
      euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) +
        M / 2 *
          (lpNorm 2 (x - euclideanPsiMinimizer M x₀ s)) ^ (2 : ℕ) := by
  exact (euclideanPsi_eq_min_add_sq hM.ne' x₀ s c x).ge

/-- Genuine global minimality of the explicit point. -/
theorem euclideanPsiMinimizer_isMin {M : ℝ} (hM : 0 < M) {d : ℕ}
    (x₀ s : Point d) (c : ℝ) (x : Point d) :
    euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) ≤
      euclideanPsi M x₀ s c x := by
  have hsquare : 0 ≤
      (lpNorm 2 (x - euclideanPsiMinimizer M x₀ s)) ^ (2 : ℕ) := sq_nonneg _
  have hcoef : 0 ≤ M / 2 := div_nonneg hM.le (by norm_num)
  have heq := euclideanPsi_eq_min_add_sq hM.ne' x₀ s c x
  calc
    euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) ≤
        euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) +
          M / 2 *
            (lpNorm 2 (x - euclideanPsiMinimizer M x₀ s)) ^ (2 : ℕ) :=
      le_add_of_nonneg_right (mul_nonneg hcoef hsquare)
    _ = euclideanPsi M x₀ s c x := heq.symm

/-- Adding one weighted oracle linearization preserves the canonical form,
with the accumulated gradient and affine constant updated exactly. -/
theorem euclideanPsi_add_linearization {M a fy : ℝ} {d : ℕ}
    (x₀ s g y : Point d) (c : ℝ) (x : Point d) :
    euclideanPsi M x₀ s c x + a * (fy + pairing g (x - y)) =
      euclideanPsi M x₀ (s + a • g)
        (c + a * (fy + pairing g (x₀ - y))) x := by
  unfold euclideanPsi
  simp only [Stage2RouteD.pairing_add_left, Stage2RouteD.pairing_smul_left]
  have hsplit : pairing g (x - y) =
      pairing g (x₀ - y) + pairing g (x - x₀) := by
    exact pairing_sub_decomposition g x x₀ y
  rw [hsplit]
  ring

end Stage8EuclideanMinimizer
end O3
