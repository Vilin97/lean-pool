/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.L2FiniteFamily

/-! # Integrated matrix forms on genuine Euclidean L² fields

The hypotheses concern the measurable matrices used in a pairing. In local
applications these may be masked interior coefficient values; no derivative
of the mask is taken.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace AlmostSchur

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def l2MatrixForm (A : α → Matrix ι ι ℝ)
    (u v : Lp (EuclideanSpace ℝ ι) 2 μ) : ℝ :=
  ∫ x, ∑ i, ∑ j, A x i j * u x i * v x j ∂μ

theorem integrable_matrix_L2_pairing (A : α → Matrix ι ι ℝ)
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ)
    (u v : Lp (EuclideanSpace ℝ ι) 2 μ) {C : ℝ}
    (hb : ∀ᵐ x ∂μ, ∀ r s : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * r i * s j| ≤ C * ‖r‖ * ‖s‖) :
    Integrable (fun x => ∑ i, ∑ j, A x i j * u x i * v x j) μ := by
  apply (((Lp.memLp u).norm.integrable_mul (Lp.memLp v).norm).const_mul C).mono'
  · convert (Finset.aestronglyMeasurable_sum Finset.univ fun i _ =>
      Finset.aestronglyMeasurable_sum Finset.univ fun j _ =>
        ((hA i j).mul ((Lp.memLp u).eval_piLp i).aestronglyMeasurable).mul
          ((Lp.memLp v).eval_piLp j).aestronglyMeasurable) using 1
    ext x
    simp only [Finset.sum_apply, Pi.mul_apply]
  · filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs, mul_assoc, Pi.mul_apply] using hx (u x) (v x)

theorem abs_l2MatrixForm_le (A : α → Matrix ι ι ℝ)
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ)
    (u v : Lp (EuclideanSpace ℝ ι) 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ∀ r s : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * r i * s j| ≤ C * ‖r‖ * ‖s‖) :
    |l2MatrixForm A u v| ≤ C * ‖u‖ * ‖v‖ := by
  apply abs_integral_le_bilinear_L2 u v (integrable_matrix_L2_pairing A hA u v hb) hC
  filter_upwards [hb] with x hx
  exact hx (u x) (v x)

/-- Pointwise ellipticity only on the actual field gives integrated coercivity. -/
theorem l2MatrixForm_self_lower (A : α → Matrix ι ι ℝ)
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ)
    (u : Lp (EuclideanSpace ℝ ι) 2 μ) {C ell : ℝ}
    (hb : ∀ᵐ x ∂μ, ∀ r s : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * r i * s j| ≤ C * ‖r‖ * ‖s‖)
    (he : ∀ᵐ x ∂μ, ell * ‖u x‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * u x i * u x j) :
    ell * ‖u‖ ^ 2 ≤ l2MatrixForm A u u := by
  have hn : Integrable (fun x => ‖u x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) u u
  have hi : (∫ x, ‖u x‖ ^ 2 ∂μ) = ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [← hi, ← integral_const_mul]
  exact integral_mono_ae (hn.const_mul ell) (integrable_matrix_L2_pairing A hA u u hb) he

end AlmostSchur
