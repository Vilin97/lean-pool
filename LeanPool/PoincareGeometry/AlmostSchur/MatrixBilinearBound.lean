/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.CoordinateEllipticity
public import Mathlib.Analysis.Matrix.Normed

/-! # Explicit bilinear coefficient bounds

An entrywise bound controls mixed gradient terms. No symmetry or positivity
is needed, so the estimate also applies to coefficient difference quotients.
-/

@[expose] public noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
namespace AlmostSchur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An entrywise coefficient bound controls the mixed form in Euclidean norm. -/
theorem abs_matrix_bilinear_le (A : Matrix ι ι ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i j, |A i j| ≤ C) (u v : EuclideanSpace ℝ ι) :
    |∑ i, ∑ j, A i j * u i * v j| ≤
      (Fintype.card ι : ℝ) ^ 2 * C * ‖u‖ * ‖v‖ := by
  have hu (i : ι) : |u i| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
  have hv (j : ι) : |v j| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
  have ht (i j : ι) : |A i j * u i * v j| ≤ C * ‖u‖ * ‖v‖ := by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul (hA i j) (hu i) (abs_nonneg _) hC)
      (hv j) (abs_nonneg _) (mul_nonneg hC (norm_nonneg _))
  calc
    _ ≤ ∑ i, |∑ j, A i j * u i * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |A i j * u i * v j| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ∑ _j : ι, C * ‖u‖ * ‖v‖ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
    _ = _ := by simp; ring

/-- Continuous coefficient families have a compact uniform mixed-form bound. -/
theorem exists_uniform_matrix_bilinear_bound
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (A : X → Matrix ι ι ℝ) (hA : ContinuousOn A K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ∀ u v : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * u i * v j| ≤ B * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := A) hA
  refine ⟨(Fintype.card ι : ℝ) ^ 2 * max C 0,
    mul_nonneg (sq_nonneg _) (le_max_right _ _), fun x hx u v => ?_⟩
  apply abs_matrix_bilinear_le _ (le_max_right C 0)
  intro i j
  exact (Matrix.norm_entry_le_entrywise_sup_norm _).trans
    ((hC x hx).trans (le_max_left _ _))

end AlmostSchur
