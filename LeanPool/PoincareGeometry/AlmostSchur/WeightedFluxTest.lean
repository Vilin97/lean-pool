/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.L2MatrixForm

/-! # The actual weighted-flux test expansion

Only weighted flux identities are required: they are valid on the interior
support without differentiating the zero-extended coefficients.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace AlmostSchur

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cutoff derivative graph has the expected norm bound. -/
theorem norm_weighted_testGraph_le (q : ι → Lp ℝ 2 μ)
    (r s : Lp (EuclideanSpace ℝ ι) 2 μ) (η : α → ℝ)
    (hη : ∀ᵐ x ∂μ, |η x| ≤ 1)
    (hq : ∀ᵐ x ∂μ, ∀ i, q i x = η x * (r x i + 2 * s x i)) :
    Real.sqrt (∑ i, ‖q i‖ ^ 2) ≤ ‖r‖ + 2 * ‖s‖ := by
  rw [← norm_l2FiniteFamily]
  have hn : ‖l2FiniteFamily q‖ ≤ ‖r + (2 : ℝ) • s‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [l2FiniteFamily_ae_eq q, hη, hq,
      Lp.coeFn_add r ((2 : ℝ) • s), Lp.coeFn_smul (2 : ℝ) s] with x hx hη hq ha hs
    have he : l2FiniteFamily q x = η x • (r x + (2 : ℝ) • s x) := by
      rw [hx]
      ext i
      exact hq i
    rw [he, ha, Pi.add_apply, hs, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hη (norm_nonneg _)).trans_eq (one_mul _)
  exact hn.trans ((norm_add_le _ _).trans_eq (by rw [norm_smul]; norm_num))

/-- Expand the weighted test into the principal, cutoff, and two commutator terms. -/
theorem weighted_flux_test_expansion
    (A B : α → Matrix ι ι ℝ)
    (hA : ∀ i j, AEStronglyMeasurable (fun x => A x i j) μ)
    (hB : ∀ i j, AEStronglyMeasurable (fun x => B x i j) μ)
    {CA CB : ℝ}
    (hbA : ∀ᵐ x ∂μ, ∀ u v : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * u i * v j| ≤ CA * ‖u‖ * ‖v‖)
    (hbB : ∀ᵐ x ∂μ, ∀ u v : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, B x i j * u i * v j| ≤ CB * ‖u‖ * ‖v‖)
    (J q : ι → Lp ℝ 2 μ) (r s D : Lp (EuclideanSpace ℝ ι) 2 μ) (η : α → ℝ)
    (hq : ∀ᵐ x ∂μ, ∀ j, q j x = η x * (r x j + 2 * s x j))
    (hJ : ∀ᵐ x ∂μ, ∀ j, η x * J j x = ∑ i, (A x i j * r x i + B x i j * D x i)) :
    (∑ j, inner ℝ (J j) (q j)) = l2MatrixForm A r r + 2 * l2MatrixForm A r s +
      l2MatrixForm B D r + 2 * l2MatrixForm B D s := by
  have h1 := integrable_matrix_L2_pairing A hA r r hbA
  have h2 := integrable_matrix_L2_pairing A hA r s hbA
  have h3 := integrable_matrix_L2_pairing B hB D r hbB
  have h4 := integrable_matrix_L2_pairing B hB D s hbB
  simp_rw [L2.inner_def]
  rw [← integral_finsetSum _ (fun j _ => L2.integrable_inner (J j) (q j))]
  let e1 := fun x => ∑ i, ∑ j, A x i j * r x i * r x j
  let e2 := fun x => ∑ i, ∑ j, A x i j * r x i * s x j
  let e3 := fun x => ∑ i, ∑ j, B x i j * D x i * r x j
  let e4 := fun x => ∑ i, ∑ j, B x i j * D x i * s x j
  have hi : (∫ x, ((e1 x + 2 * e2 x) + e3 x) + 2 * e4 x ∂μ) =
      l2MatrixForm A r r + 2 * l2MatrixForm A r s +
        l2MatrixForm B D r + 2 * l2MatrixForm B D s := by
    rw [integral_add (f := fun x => e1 x + 2 * e2 x + e3 x) (g := fun x => 2 * e4 x)
        ((h1.add (h2.const_mul 2)).add h3) (h4.const_mul 2),
      integral_add (f := fun x => e1 x + 2 * e2 x) (g := e3) (h1.add (h2.const_mul 2)) h3,
      integral_add (f := e1) (g := fun x => 2 * e2 x) h1 (h2.const_mul 2),
      integral_const_mul, integral_const_mul]
    rfl
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [hq, hJ] with x hq hJ
  simp only [Pi.add_apply, RCLike.inner_apply, conj_trivial]
  calc
    _ = ∑ j, ∑ i, (A x i j * r x i * r x j + 2 * (A x i j * r x i * s x j) +
        B x i j * D x i * r x j + 2 * (B x i j * D x i * s x j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hq j]
      calc
        _ = (η x * J j x) * (r x j + 2 * s x j) := by ring
        _ = _ := by
          rw [hJ j, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i, ∑ j, (A x i j * r x i * r x j + 2 * (A x i j * r x i * s x j) +
        B x i j * D x i * r x j + 2 * (B x i j * D x i * s x j)) := Finset.sum_comm
    _ = _ := by simp only [e1, e2, e3, e4, Finset.sum_add_distrib, ← Finset.mul_sum]

end AlmostSchur
