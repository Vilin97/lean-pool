/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.DifferenceQuotientProduct
public import Mathlib.Analysis.Calculus.MeanValue

/-! # From weighted derivative quotients to localized weak derivatives

The backward weighted quotient controls the shifted principal product term.
Only the smooth scalar cutoff is differentiated; the L² field is not.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The product estimate uses a weighted backwards quotient, not an unweighted
derivative quotient that might have no uniform bound. -/
theorem norm_differenceQuotient_cutoff_le
    (a : E → ℝ) (ha : AEStronglyMeasurable a (volume : Measure E))
    (C : ℝ) (hb : ∀ᵐ x ∂(volume : Measure E), ‖a x‖ ≤ C)
    (u : Lp ℝ 2 (volume : Measure E)) (v : E) (h L : ℝ)
    (hL : ∀ᵐ x ∂(volume : Measure E), ‖h⁻¹ * (a (x + h • v) - a x)‖ ≤ L) :
    ‖directionalDifferenceQuotient (boundedL2Multiplier a ha C hb u) v h‖ ≤
      ‖boundedL2Multiplier a ha C hb (directionalDifferenceQuotient u v (-h))‖ + L * ‖u‖ := by
  let R := boundedL2Multiplier a ha C hb (directionalDifferenceQuotient u v (-h))
  have ht := bounded_coefficient_translate a ha C hb (h • v)
  let B := boundedL2Multiplier (fun x => a (x + h • v)) ht.1 C ht.2
    (directionalDifferenceQuotient u v h)
  have he : B = translationL2 (h • v) R := by
    apply Lp.ext
    have hr := boundedL2Multiplier_ae_eq a ha C hb (directionalDifferenceQuotient u v (-h))
    have hrt := (measurePreserving_add_right (volume : Measure E) (h • v)).quasiMeasurePreserving.ae hr
    have hd := (measurePreserving_add_right (volume : Measure E) (h • v)).quasiMeasurePreserving.ae
      (directionalDifferenceQuotient_ae_eq u v (-h))
    filter_upwards [boundedL2Multiplier_ae_eq _ _ C _ (directionalDifferenceQuotient u v h),
      Lp.coeFn_compMeasurePreserving R (measurePreserving_add_right (volume : Measure E) (h • v)),
      hrt, hd, directionalDifferenceQuotient_ae_eq u v h] with x hb ht hr hd hδ
    change B x = (Lp.compMeasurePreserving (fun x => x + h • v)
      (measurePreserving_add_right (volume : Measure E) (h • v)) R) x
    rw [hb, ht, Function.comp_apply]
    rw [hr, hd, hδ]
    simp only [neg_smul, add_neg_cancel_right, neg_inv]
    ring
  rw [directionalDifferenceQuotient_bounded_mul a ha C hb u v h L hL]
  change ‖B + _‖ ≤ _
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [he, (translationL2 (h • v)).norm_map]
  · exact norm_boundedL2Multiplier_apply_le _ _ L hL u

/-- The scalar cutoff has a genuinely uniform global quotient bound from the mean-value theorem. -/
theorem exists_cutoff_differenceQuotient_bound (a : E → ℝ)
    (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x v : E) (h : ℝ), h ≠ 0 →
      ‖h⁻¹ * (a (x + h • v) - a x)‖ ≤ L * ‖v‖ := by
  obtain ⟨L, hL⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (ha.continuous_fderiv (by norm_num))
  refine ⟨max L 0, le_max_right _ _, fun x v h hh => ?_⟩
  have ht : ‖a (x + h • v) - a x‖ ≤ max L 0 * ‖(x + h • v) - x‖ :=
    (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => ha.differentiable (by norm_num) z)
      (fun z _ => (hL z).trans (le_max_left _ _)) (mem_univ x) (mem_univ (x + h • v))
  rw [add_sub_cancel_left, norm_smul] at ht
  rw [norm_mul]
  calc
    _ ≤ ‖h⁻¹‖ * (max L 0 * (‖h‖ * ‖v‖)) := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = _ := by rw [norm_inv]; field_simp

end AlmostSchur
