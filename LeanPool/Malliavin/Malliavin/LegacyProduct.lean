/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The original totalization of product measures

The upstream Malliavin development used Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d` (v4.33.0). Its product measure was the bind
of `x ↦ ν.map (Prod.mk x)`, with zero as the value of a nonmeasurable outer map.
`legacyProduct` records that convention explicitly. It agrees with the standard product
when the right factor is s-finite, including every use in the main Fubini theory.

The estimates below adapt the corresponding proofs from that Mathlib revision's
`MeasureTheory/Measure/Prod.lean` and `MeasureTheory/Integral/Prod.lean`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace Malliavin

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- A direct s-finiteness witness for a probability measure, independent of topology. -/
theorem probability_sFinite (μ : Measure α) [IsProbabilityMeasure μ] : SFinite μ := by
  let : SigmaFinite μ := IsFiniteMeasure.toSigmaFinite μ
  infer_instance

/-- The product measure with the zero fallback used by upstream Mathlib v4.33.0. -/
@[irreducible] noncomputable def legacyProduct (μ : Measure α) (ν : Measure β) :
    Measure (α × β) := by
  classical
  exact if AEMeasurable (fun x : α => ν.map (Prod.mk x)) μ then μ.prod ν else 0

/-- For an s-finite right factor, the legacy and current product measures coincide. -/
@[simp] theorem legacyProduct_eq_prod [SFinite ν] : legacyProduct μ ν = μ.prod ν := by
  classical
  simp only [legacyProduct, Measurable.map_prodMk_left.aemeasurable, ite_true]

private theorem legacyProduct_apply_le {s : Set (α × β)} (hs : MeasurableSet s) :
    legacyProduct μ ν s ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := by
  classical
  by_cases h : AEMeasurable (fun x : α => ν.map (Prod.mk x)) μ
  · simp only [legacyProduct, h, ite_true, Measure.prod]
    simpa only [map_apply measurable_prodMk_left hs] using bind_apply_le h hs
  · simp [legacyProduct, h]

private theorem legacyProduct_rectangle_le (s : Set α) (t : Set β) :
    legacyProduct μ ν (s ×ˢ t) ≤ μ s * ν t := by
  let S := toMeasurable μ s
  let T := toMeasurable ν t
  calc
    legacyProduct μ ν (s ×ˢ t) ≤ legacyProduct μ ν (S ×ˢ T) := by
      gcongr <;> apply subset_toMeasurable
    _ ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' (S ×ˢ T)) ∂μ :=
      legacyProduct_apply_le (by measurability)
    _ = μ S * ν T := by
      classical
      simp_rw [S, mk_preimage_prod_right_eq_if, measure_if,
        lintegral_indicator (measurableSet_toMeasurable _ _), lintegral_const,
        restrict_apply_univ, mul_comm]
    _ = μ s * ν t := by rw [measure_toMeasurable, measure_toMeasurable]

/-- First-coordinate projection preserves null sets for the legacy product. -/
theorem legacyProduct_quasiMeasurePreserving_fst :
    QuasiMeasurePreserving Prod.fst (legacyProduct μ ν) μ := by
  refine ⟨measurable_fst, AbsolutelyContinuous.mk fun s hs hzero => ?_⟩
  rw [map_apply measurable_fst hs, ← prod_univ, ← nonpos_iff_eq_zero]
  exact (legacyProduct_rectangle_le _ _).trans_eq (by rw [hzero, zero_mul])

/-- Second-coordinate projection preserves null sets for the legacy product. -/
theorem legacyProduct_quasiMeasurePreserving_snd :
    QuasiMeasurePreserving Prod.snd (legacyProduct μ ν) ν := by
  refine ⟨measurable_snd, AbsolutelyContinuous.mk fun s hs hzero => ?_⟩
  rw [map_apply measurable_snd hs, ← univ_prod, ← nonpos_iff_eq_zero]
  exact (legacyProduct_rectangle_le _ _).trans_eq (by rw [hzero, mul_zero])

private theorem lintegral_legacyProduct_le (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z ∂legacyProduct μ ν ≤ ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  classical
  by_cases h : AEMeasurable (fun x : α => ν.map (Prod.mk x)) μ
  · simp only [legacyProduct, h, ite_true, Measure.prod]
    exact (lintegral_bind_le _ _ h).trans <|
      lintegral_mono fun a => lintegral_map_le _ measurable_prodMk_left.aemeasurable
  · simp [legacyProduct, h]

/-- Products of integrable real functions are integrable for the original product convention. -/
theorem integrable_mul_legacyProduct {f : α → ℝ} {g : β → ℝ}
    (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z : α × β => f z.1 * g z.2) (legacyProduct μ ν) := by
  refine ⟨(hf.aestronglyMeasurable.comp_quasiMeasurePreserving
    legacyProduct_quasiMeasurePreserving_fst).mul
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving
        legacyProduct_quasiMeasurePreserving_snd), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    ∫⁻ z, ‖f z.1 * g z.2‖ₑ ∂legacyProduct μ ν ≤
        ∫⁻ x, ∫⁻ y, ‖f x * g y‖ₑ ∂ν ∂μ := lintegral_legacyProduct_le _
    _ = (∫⁻ x, ‖f x‖ₑ ∂μ) * ∫⁻ y, ‖g y‖ₑ ∂ν := by
      simp [enorm_mul, lintegral_const_mul', lintegral_mul_const', hg.2.ne]
    _ < ∞ := ENNReal.mul_lt_top hf.2 hg.2

end Malliavin
