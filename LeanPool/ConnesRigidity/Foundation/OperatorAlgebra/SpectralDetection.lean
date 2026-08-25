/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 34332-34470.
Modifications: extracted the measure-counting lemmas and made the paper-specific
exhaustion an input. See the upstream PORT_MAP.md.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.CompletePartialOrder

/-!
The spectral detection component of the Connes rigidity formalization.
-/

namespace Connes

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators


/- Uniform primitive detection counts bound the active spectral mass. Paper: §4. -/
theorem measure_detection_gap_of_uniform_primitive_counts
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (primitive : Finset ι)
    (detect : ι → Set α) [DecidableRel (fun x v ↦ x ∈ detect v)]
    (active : Set α) (e : ι)
    (he : e ∈ primitive)
    (hdetect : ∀ v ∈ primitive, MeasurableSet (detect v))
    (hactive : MeasurableSet active)
    (hpointwise : ∀ x ∈ active,
      primitive.card ≤ 7 * (primitive.filter (fun v ↦ x ∈ detect v)).card)
    (huniform : ∀ v ∈ primitive, μ (detect v) = μ (detect e)) :
    μ active ≤ 7 * μ (detect e) := by
  classical
  have hpoint : ∀ x : α,
      (primitive.card : ℝ≥0∞) * active.indicator 1 x ≤
        7 * ∑ v ∈ primitive, (detect v).indicator 1 x := by
    intro x
    by_cases hx : x ∈ active
    · have hcard : (primitive.card : ℝ≥0∞) ≤
          7 * ((primitive.filter (fun v ↦ x ∈ detect v)).card : ℝ≥0∞) := by
        exact_mod_cast hpointwise x hx
      simpa only [hx, indicator_of_mem, Pi.one_apply, mul_one, indicator_apply,
        Finset.sum_boole, ge_iff_le] using hcard
    · simp only [hx, not_false_eq_true, indicator_of_notMem, mul_zero,
        indicator_apply, Pi.one_apply, Finset.sum_boole, zero_le]
  have hweighted := lintegral_mono (μ := μ) hpoint
  rw [lintegral_const_mul (primitive.card : ℝ≥0∞)
      (measurable_one.indicator hactive)] at hweighted
  rw [lintegral_indicator_one hactive] at hweighted
  rw [lintegral_const_mul (7 : ℝ≥0∞)
      (Finset.measurable_fun_sum primitive
        (fun v hv ↦ measurable_one.indicator (hdetect v hv)))] at hweighted
  have hsplit :
      (∫⁻ x, ∑ v ∈ primitive, (detect v).indicator 1 x ∂μ) =
        ∑ v ∈ primitive, μ (detect v) := by
    rw [lintegral_finsetSum primitive
      (fun v hv ↦ measurable_one.indicator (hdetect v hv))]
    apply Finset.sum_congr rfl
    intro v hv
    exact lintegral_indicator_one (hdetect v hv)
  rw [hsplit] at hweighted
  have hsum : (∑ v ∈ primitive, μ (detect v)) =
      (primitive.card : ℝ≥0∞) * μ (detect e) := by
    calc
      (∑ v ∈ primitive, μ (detect v)) = ∑ _v ∈ primitive, μ (detect e) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact huniform v hv
      _ = (primitive.card : ℝ≥0∞) * μ (detect e) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hsum] at hweighted
  have hcardzero : (primitive.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨e, he⟩
  have hcardtop : (primitive.card : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.mul_le_mul_iff_left hcardzero hcardtop).mp
  simpa only [mul_comm, mul_left_comm] using hweighted

/- Finite-measure form of the uniform primitive-count estimate. Paper: §4. -/
theorem measureReal_detection_gap_of_uniform_primitive_counts
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (primitive : Finset ι)
    (detect : ι → Set α) [DecidableRel (fun x v ↦ x ∈ detect v)]
    (active : Set α) (e : ι)
    (he : e ∈ primitive)
    (hdetect : ∀ v ∈ primitive, MeasurableSet (detect v))
    (hactive : MeasurableSet active)
    (hpointwise : ∀ x ∈ active,
      primitive.card ≤ 7 * (primitive.filter (fun v ↦ x ∈ detect v)).card)
    (huniform : ∀ v ∈ primitive, μ (detect v) = μ (detect e)) :
    μ.real active ≤ 7 * μ.real (detect e) := by
  have hgap := measure_detection_gap_of_uniform_primitive_counts
    μ primitive detect active e he hdetect hactive hpointwise huniform
  have hfinite : (7 : ℝ≥0∞) * μ (detect e) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top μ _)
  have hreal :=
    (ENNReal.toReal_le_toReal (measure_ne_top μ _) hfinite).2 hgap
  simpa only [measureReal_def, ge_iff_le, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat] using hreal

/- Monotone exhaustion bounds the complement of a distinguished point. Paper: §4. -/
theorem measureReal_iUnion_le_of_monotone
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (U : ℕ → Set α)
    (hmono : Monotone U)
    {c : ℝ} (hbound : ∀ n, μ.real (U n) ≤ c) :
    μ.real (⋃ n, U n) ≤ c := by
  have hfinite : μ (⋃ n, U n) ≠ ⊤ := measure_ne_top μ _
  have hlim : Tendsto (fun n ↦ μ.real (U n)) atTop
      (𝓝 (μ.real (⋃ n, U n))) := by
    exact (ENNReal.tendsto_toReal hfinite).comp
      (tendsto_measure_iUnion_atTop (μ := μ) hmono)
  exact le_of_tendsto' hlim hbound

/- An exhaustion detection gap yields a positive distinguished atom. Paper: §4. -/
theorem probability_detection_gap_of_exhaustion
    {α : Type*} [MeasurableSpace α]
    (μ : ProbabilityMeasure α) (zero : α) (U : ℕ → Set α)
    (hzero : MeasurableSet ({zero} : Set α))
    (hmono : Monotone U)
    (hunion : (⋃ n, U n) = ({zero} : Set α)ᶜ)
    {p : ℝ} (hbound : ∀ n, (μ : Measure α).real (U n) ≤ 7 * p) :
    (1 / 7 : ℝ) * (1 - (μ : Measure α).real {zero}) ≤ p := by
  have h := measureReal_iUnion_le_of_monotone
    (μ : Measure α) U hmono hbound
  rw [hunion, measureReal_compl hzero, probReal_univ] at h
  linarith

end

end Connes
