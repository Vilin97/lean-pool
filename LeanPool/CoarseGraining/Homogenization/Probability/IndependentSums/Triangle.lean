/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiCalculus

/-! # Triangle -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*}

/-!
Finite-sum reduction lemmas for the Chapter 4 weak-Orlicz triangle inequality.

This file formalizes the deterministic truncation step and the finite-family
Markov reduction from Step 5 of the notes. The one-variable tail integral bound
will plug into these lemmas downstream.
-/

/-- The truncated upper-tail variable `X 1_{X > r}` used in the Step 5 proof
of the generalized triangle inequality. -/
def upperTailIndicator (X : Ω → ℝ) (r : ℝ) : Ω → ℝ :=
  (upperTailEvent X r).indicator X

@[simp] theorem upperTailIndicator_apply (X : Ω → ℝ) (r : ℝ) (ω : Ω) :
    upperTailIndicator X r ω = if r < X ω then X ω else 0 :=
  rfl

@[simp] theorem upperTailIndicator_of_lt {X : Ω → ℝ} {r : ℝ} {ω : Ω}
    (h : r < X ω) :
    upperTailIndicator X r ω = X ω := by
  simp [upperTailIndicator, upperTailEvent, h]

@[simp] theorem upperTailIndicator_of_not_lt {X : Ω → ℝ} {r : ℝ} {ω : Ω}
    (h : ¬ r < X ω) :
    upperTailIndicator X r ω = 0 := by
  simp [upperTailIndicator, upperTailEvent, h]

theorem upperTailIndicator_nonneg {X : Ω → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (ω : Ω) :
    0 ≤ upperTailIndicator X r ω := by
  by_cases h : r < X ω
  · simpa [upperTailIndicator, upperTailEvent, h] using le_trans hr (le_of_lt h)
  · simp [upperTailIndicator, upperTailEvent, h]

theorem le_upperTailIndicator_add {X : Ω → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (ω : Ω) :
    X ω ≤ upperTailIndicator X r ω + r := by
  by_cases h : r < X ω
  · simp [upperTailIndicator, upperTailEvent, h, hr]
  · simp [upperTailIndicator, upperTailEvent, h]
    exact not_lt.mp h

theorem sum_le_sum_upperTailIndicator_add_sum
    (s : Finset ι) {X : ι → Ω → ℝ} {r : ι → ℝ}
    (hr : ∀ i ∈ s, 0 ≤ r i) (ω : Ω) :
    Finset.sum s (fun i => X i ω) ≤
      Finset.sum s (fun i => upperTailIndicator (X i) (r i) ω) + Finset.sum s r := by
  calc
    Finset.sum s (fun i => X i ω) ≤
        Finset.sum s (fun i => upperTailIndicator (X i) (r i) ω + r i) := by
      exact Finset.sum_le_sum fun i hi => le_upperTailIndicator_add (hr i hi) ω
    _ = Finset.sum s (fun i => upperTailIndicator (X i) (r i) ω) + Finset.sum s r := by
      rw [Finset.sum_add_distrib]

/-- If a finite sum exceeds `b + Σ rᵢ`, then the sum of the corresponding
upper-tail truncations exceeds `b`. -/
theorem upperTailEvent_finset_sum_subset_upperTailIndicator_finset_sum
    (s : Finset ι) {X : ι → Ω → ℝ} {r : ι → ℝ} {b : ℝ}
    (hr : ∀ i ∈ s, 0 ≤ r i) :
    upperTailEvent (fun ω => Finset.sum s (fun i => X i ω)) (b + Finset.sum s r) ⊆
      upperTailEvent (fun ω => Finset.sum s (fun i => upperTailIndicator (X i) (r i) ω)) b := by
  intro ω hω
  have hle :=
    sum_le_sum_upperTailIndicator_add_sum (Ω := Ω) (ι := ι) (X := X) (r := r) s hr ω
  change b < Finset.sum s (fun i => upperTailIndicator (X i) (r i) ω)
  change b + Finset.sum s r < Finset.sum s (fun i => X i ω) at hω
  linarith

/-- The absolute tail of a finite sum is controlled by the one-sided tail of
the sum of the absolute values. -/
theorem absTailEvent_finset_sum_subset_upperTailEvent_sum_abs
    (s : Finset ι) {X : ι → Ω → ℝ} {b : ℝ} :
    absTailEvent (fun ω => Finset.sum s (fun i => X i ω)) b ⊆
      upperTailEvent (fun ω => Finset.sum s (fun i => |X i ω|)) b := by
  intro ω hω
  change b < Finset.sum s (fun i => |X i ω|)
  change b < |Finset.sum s (fun i => X i ω)| at hω
  exact lt_of_lt_of_le hω (Finset.abs_sum_le_sum_abs (fun i => X i ω) s)

theorem upperTailEvent_upperTailIndicator_eq_upperTailEvent_left
    {X : Ω → ℝ} {c s : ℝ} (hs : 0 < s) (hsc : s ≤ c) :
    upperTailEvent (upperTailIndicator X c) s = upperTailEvent X c := by
  ext ω
  by_cases hω : c < X ω
  · have hsX : s < X ω := lt_of_le_of_lt hsc hω
    simp [upperTailIndicator, upperTailEvent, hω, hsX]
  · have hs0 : ¬ s < (0 : ℝ) := not_lt.mpr hs.le
    simp [upperTailIndicator, upperTailEvent, hω, hs0]

theorem upperTailEvent_upperTailIndicator_eq_upperTailEvent_right
    {X : Ω → ℝ} {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s) :
    upperTailEvent (upperTailIndicator X c) s = upperTailEvent X s := by
  ext ω
  by_cases hω : c < X ω
  · simp [upperTailIndicator, upperTailEvent, hω]
  · have hs0 : ¬ s < (0 : ℝ) := not_lt.mpr (le_trans hc hcs)
    have hsX : ¬ s < X ω := by
      exact not_lt_of_ge ((not_lt.mp hω).trans hcs)
    simp [upperTailIndicator, upperTailEvent, hω, hs0, hsX]

section Measure

variable [MeasurableSpace Ω]
variable {μ : Measure Ω}

theorem upperTailIndicator_measurable {X : Ω → ℝ} {r : ℝ}
    (hX : Measurable X) :
    Measurable (upperTailIndicator X r) := by
  exact hX.indicator (measurableSet_lt measurable_const hX)

theorem measureReal_upperTailEvent_upperTailIndicator_eq_upperTailEvent_left
    {X : Ω → ℝ} {c s : ℝ} (hs : 0 < s) (hsc : s ≤ c) :
    μ.real (upperTailEvent (upperTailIndicator X c) s) =
      μ.real (upperTailEvent X c) := by
  rw [upperTailEvent_upperTailIndicator_eq_upperTailEvent_left hs hsc]

theorem measureReal_upperTailEvent_upperTailIndicator_eq_upperTailEvent_right
    {X : Ω → ℝ} {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s) :
    μ.real (upperTailEvent (upperTailIndicator X c) s) =
      μ.real (upperTailEvent X s) := by
  rw [upperTailEvent_upperTailIndicator_eq_upperTailEvent_right hc hcs]

theorem lintegral_upperTailIndicator_le_of_isBigOWith
    [IsFiniteMeasure μ]
    {Ψ : ℝ → ℝ} {X : Ω → ℝ} {a q C₀ t : ℝ}
    (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 1 < q) (ha : 0 < a) (ht : 1 ≤ t)
    (hX : IsBigOWith μ Ψ X a) (hXm : Measurable X) :
    ∫⁻ ω, ENNReal.ofReal (upperTailIndicator X (a * t) ω) ∂μ ≤
      ENNReal.ofReal (a * t * (1 + C₀ / (q - 1)) * (Ψ t)⁻¹) := by
  let c : ℝ := a * t
  let Y : Ω → ℝ := upperTailIndicator X c
  let C : ℝ := C₀ * (Ψ t)⁻¹
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hc_pos : 0 < c := by
    simp [c, mul_pos ha ht_pos]
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hq_sub_pos : 0 < q - 1 := sub_pos.mpr hq
  have hq_sub_ne : q - 1 ≠ 0 := hq_sub_pos.ne'
  have hC₀_one : 1 ≤ C₀ := hasPsiAbstractDoubling_one_le_const hD hAdmissible
  have hΨt_one : 1 ≤ Ψ t := hAdmissible.2 (le_trans zero_le_one ht)
  have hΨt_pos : 0 < Ψ t := lt_of_lt_of_le zero_lt_one hΨt_one
  have hΨt_inv_nonneg : 0 ≤ (Ψ t)⁻¹ := inv_nonneg.mpr (le_of_lt hΨt_pos)
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg (le_trans zero_le_one hC₀_one) hΨt_inv_nonneg
  have hY_nonneg : 0 ≤ᵐ[μ] Y := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    simpa [Y, c] using upperTailIndicator_nonneg (X := X) (r := c) hc_nonneg ω
  have hY_meas : Measurable Y := by
    simpa [Y, c] using upperTailIndicator_measurable (X := X) (r := c) hXm
  have hLayer :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt (μ := μ) (f := Y) hY_nonneg hY_meas.aemeasurable
  have hLayer' :
      ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ =
        ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (μ.real (upperTailEvent Y s)) := by
    rw [hLayer]
    refine setLIntegral_congr_fun measurableSet_Ioi ?_
    intro s hs
    have htail_ne_top : μ (upperTailEvent Y s) ≠ ⊤ := by finiteness
    change μ (upperTailEvent Y s) = ENNReal.ofReal (μ.real (upperTailEvent Y s))
    simp [Measure.real, htail_ne_top]
  have hIoc_eq :
      ∫⁻ s in Set.Ioc 0 c, ENNReal.ofReal (μ.real (upperTailEvent Y s)) ∂volume =
        ENNReal.ofReal (c * μ.real (upperTailEvent X c)) := by
    calc
      ∫⁻ s in Set.Ioc 0 c, ENNReal.ofReal (μ.real (upperTailEvent Y s)) ∂volume
        = ∫⁻ _ in Set.Ioc 0 c, ENNReal.ofReal (μ.real (upperTailEvent X c)) ∂volume := by
            refine setLIntegral_congr_fun measurableSet_Ioc ?_
            intro s hs
            change ENNReal.ofReal (μ.real (upperTailEvent Y s)) =
              ENNReal.ofReal (μ.real (upperTailEvent X c))
            rw [measureReal_upperTailEvent_upperTailIndicator_eq_upperTailEvent_left
              (μ := μ) (X := X) (c := c) hs.1 hs.2]
      _ = ENNReal.ofReal (μ.real (upperTailEvent X c)) * volume (Set.Ioc 0 c) := by
            rw [setLIntegral_const]
      _ = ENNReal.ofReal (μ.real (upperTailEvent X c)) * ENNReal.ofReal c := by
            congr 1
            simp [Real.volume_Ioc]
      _ = ENNReal.ofReal (c * μ.real (upperTailEvent X c)) := by
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ μ.real (upperTailEvent X c))]
            ring_nf
  have hpow_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi c)] fun s : ℝ => (s / c) ^ (-q) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro s hs
    exact Real.rpow_nonneg (div_nonneg (le_of_lt (lt_trans hc_pos hs)) hc_nonneg) _
  have hpow_integrable_base :
      IntegrableOn (fun s : ℝ => s ^ (-q)) (Set.Ioi c) volume := by
    exact integrableOn_Ioi_rpow_of_lt (a := -q) (by linarith) hc_pos
  have hpow_integrable :
      IntegrableOn (fun s : ℝ => (s / c) ^ (-q)) (Set.Ioi c) volume := by
    have hscaled :
        IntegrableOn (fun s : ℝ => c ^ q * s ^ (-q)) (Set.Ioi c) volume :=
      hpow_integrable_base.const_mul _
    refine hscaled.congr_fun ?_ measurableSet_Ioi
    intro s hs
    have hs_pos : 0 < s := lt_trans hc_pos hs
    have hdiv :
        (s / c) ^ (-q) = c ^ q * s ^ (-q) := by
      calc
        (s / c) ^ (-q) = s ^ (-q) / c ^ (-q) := by
          rw [Real.div_rpow (le_of_lt hs_pos) hc_nonneg]
        _ = s ^ (-q) / (c ^ q)⁻¹ := by
          rw [Real.rpow_neg hc_nonneg]
        _ = s ^ (-q) * c ^ q := by
          rw [div_eq_mul_inv, inv_inv]
        _ = c ^ q * s ^ (-q) := by ring
    simp [hdiv]
  have htail_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi c)] fun s : ℝ => C * (s / c) ^ (-q) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro s hs
    exact mul_nonneg hC_nonneg <|
      Real.rpow_nonneg (div_nonneg (le_of_lt (lt_trans hc_pos hs)) hc_nonneg) _
  have htail_integrable :
      IntegrableOn (fun s : ℝ => C * (s / c) ^ (-q)) (Set.Ioi c) volume :=
    hpow_integrable.const_mul C
  have hIoi_bound :
      ∫⁻ s in Set.Ioi c, ENNReal.ofReal (μ.real (upperTailEvent Y s)) ∂volume ≤
        ENNReal.ofReal (C * (c / (q - 1))) := by
    have hmono :
        ∀ s ∈ Set.Ioi c,
          ENNReal.ofReal (μ.real (upperTailEvent Y s)) ≤
            ENNReal.ofReal (C * (s / c) ^ (-q)) := by
      intro s hs
      have hs' : c < s := hs
      have hs_tail :
          μ.real (upperTailEvent X s) ≤ (Ψ (s / a))⁻¹ := by
        have hs_div_one : 1 ≤ s / a := by
          rw [one_le_div_iff]
          left
          constructor
          · exact ha
          · nlinarith [ht, hs'.le]
        have hs_mul : a * (s / a) = s := by
          field_simp [ha.ne']
        simpa [hs_mul] using hX hs_div_one
      have hscaled :=
        hasPsiAbstractDoubling_scaledInvTail (hD := hD) (hAdmissible := hAdmissible)
          (a := a) (t := 2 * t) (s := s) ha (by nlinarith [ht]) ?_
      · have hratio : (2 * s) / (a * (2 * t)) = s / c := by
          field_simp [c, ha.ne', ht_pos.ne']
          ring
        have hratio' : s * 2 / (a * (t * 2)) = s / c := by
          field_simp [c, ha.ne', ht_pos.ne']
          ring
        have htail :
            μ.real (upperTailEvent Y s) ≤ C * (s / c) ^ (-q) := by
          calc
            μ.real (upperTailEvent Y s) = μ.real (upperTailEvent X s) := by
              rw [measureReal_upperTailEvent_upperTailIndicator_eq_upperTailEvent_right
                (μ := μ) (X := X) (c := c) hc_nonneg hs'.le]
            _ ≤ (Ψ (s / a))⁻¹ := hs_tail
            _ ≤ C₀ * ((Ψ t)⁻¹ * (s / c) ^ (-q)) := by
              simpa [c, hratio', mul_assoc, mul_left_comm, mul_comm] using hscaled
            _ = C * (s / c) ^ (-q) := by
              simp [C, mul_assoc]
        exact ENNReal.ofReal_le_ofReal htail
      · nlinarith [hs'.le]
    refine (setLIntegral_mono' measurableSet_Ioi hmono).trans ?_
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (show Integrable (fun s : ℝ => C * (s / c) ^ (-q)) (volume.restrict (Set.Ioi c)) by
        simpa [IntegrableOn] using htail_integrable)
      htail_nonneg]
    rw [integral_const_mul, integral_Ioi_div_rpow_neg hq hc_pos]
  have hfirst :
      ENNReal.ofReal (c * μ.real (upperTailEvent X c)) ≤
        ENNReal.ofReal (c * (Ψ t)⁻¹) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have htail : μ.real (upperTailEvent X c) ≤ (Ψ t)⁻¹ := by
      simpa [c] using hX ht
    exact mul_le_mul_of_nonneg_left htail hc_nonneg
  have hsplit :
      ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (μ.real (upperTailEvent Y s)) ∂volume =
        ∫⁻ s in Set.Ioc 0 c, ENNReal.ofReal (μ.real (upperTailEvent Y s)) ∂volume
          + ∫⁻ s in Set.Ioi c, ENNReal.ofReal (μ.real (upperTailEvent Y s)) ∂volume := by
    have hUnion : Set.Ioi 0 = Set.Ioc 0 c ∪ Set.Ioi c := by
      ext s
      constructor
      · intro hs
        by_cases hsc : s ≤ c
        · exact Or.inl ⟨hs, hsc⟩
        · exact Or.inr (lt_of_not_ge hsc)
      · intro hs
        rcases hs with hs | hs
        · exact hs.1
        · exact lt_trans hc_pos hs
    rw [hUnion]
    rw [MeasureTheory.lintegral_union (μ := volume)
      (f := fun s : ℝ => ENNReal.ofReal (μ.real (upperTailEvent Y s)))
      measurableSet_Ioi
      (Set.disjoint_left.2 fun s hs hIoi => hs.2.not_gt hIoi)]
  calc
    ∫⁻ ω, ENNReal.ofReal (upperTailIndicator X (a * t) ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ := by simp [Y, c]
    _ = ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (μ.real (upperTailEvent Y s)) ∂volume := hLayer'
    _ = ∫⁻ s in Set.Ioc 0 c, ENNReal.ofReal (μ.real (upperTailEvent Y s)) ∂volume
          + ∫⁻ s in Set.Ioi c, ENNReal.ofReal (μ.real (upperTailEvent Y s)) ∂volume := hsplit
    _ ≤ ENNReal.ofReal (c * (Ψ t)⁻¹) + ENNReal.ofReal (C * (c / (q - 1))) := by
          gcongr
          exact hIoc_eq.trans_le hfirst
    _ = ENNReal.ofReal (a * t * (1 + C₀ / (q - 1)) * (Ψ t)⁻¹) := by
          have hterm1_nonneg : 0 ≤ c * (Ψ t)⁻¹ := mul_nonneg hc_nonneg hΨt_inv_nonneg
          have hterm2_nonneg : 0 ≤ C * (c / (q - 1)) := by
            refine mul_nonneg hC_nonneg ?_
            positivity
          rw [← ENNReal.ofReal_add hterm1_nonneg hterm2_nonneg]
          congr 1
          simp [C, c]
          field_simp [hΨt_pos.ne', hq_sub_ne]

theorem integrable_upperTailIndicator_of_isBigOWith
    [IsFiniteMeasure μ]
    {Ψ : ℝ → ℝ} {X : Ω → ℝ} {a q C₀ t : ℝ}
    (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 1 < q) (ha : 0 < a) (ht : 1 ≤ t)
    (hX : IsBigOWith μ Ψ X a) (hXm : Measurable X) :
    Integrable (upperTailIndicator X (a * t)) μ := by
  have hY_nonneg :
      0 ≤ᵐ[μ] fun ω => upperTailIndicator X (a * t) ω := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    exact upperTailIndicator_nonneg (X := X) (r := a * t) (by positivity) ω
  refine ⟨(upperTailIndicator_measurable (X := X) (r := a * t) hXm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hY_nonneg]
  exact lt_of_le_of_lt
    (lintegral_upperTailIndicator_le_of_isBigOWith (μ := μ) hD hAdmissible hq ha ht hX hXm)
    ENNReal.ofReal_lt_top

theorem integral_upperTailIndicator_le_of_isBigOWith
    [IsFiniteMeasure μ]
    {Ψ : ℝ → ℝ} {X : Ω → ℝ} {a q C₀ t : ℝ}
    (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 1 < q) (ha : 0 < a) (ht : 1 ≤ t)
    (hX : IsBigOWith μ Ψ X a) (hXm : Measurable X) :
    ∫ ω, upperTailIndicator X (a * t) ω ∂μ ≤
      a * t * (1 + C₀ / (q - 1)) * (Ψ t)⁻¹ := by
  have hInt :=
    integrable_upperTailIndicator_of_isBigOWith (μ := μ) hD hAdmissible hq ha ht hX hXm
  have hY_nonneg :
      0 ≤ᵐ[μ] fun ω => upperTailIndicator X (a * t) ω := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    exact upperTailIndicator_nonneg (X := X) (r := a * t) (by positivity) ω
  have hlin :=
    lintegral_upperTailIndicator_le_of_isBigOWith
      (μ := μ) hD hAdmissible hq ha ht hX hXm
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hY_nonneg] at hlin
  have hbound_nonneg : 0 ≤ a * t * (1 + C₀ / (q - 1)) * (Ψ t)⁻¹ := by
    have hC₀_one : 1 ≤ C₀ := hasPsiAbstractDoubling_one_le_const hD hAdmissible
    have hΨt_one : 1 ≤ Ψ t := hAdmissible.2 (le_trans zero_le_one ht)
    have hq_sub_pos : 0 < q - 1 := sub_pos.mpr hq
    have hinner_nonneg : 0 ≤ 1 + C₀ / (q - 1) := by
      positivity
    have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht
    have hat_nonneg : 0 ≤ a * t := mul_nonneg ha.le ht_nonneg
    have htail_nonneg : 0 ≤ (1 + C₀ / (q - 1)) * (Ψ t)⁻¹ := by
      exact mul_nonneg hinner_nonneg (inv_nonneg.mpr (le_trans zero_le_one hΨt_one))
    exact mul_nonneg (mul_nonneg hat_nonneg hinner_nonneg)
      (inv_nonneg.mpr (le_trans zero_le_one hΨt_one))
  exact (ENNReal.ofReal_le_ofReal_iff hbound_nonneg).1 hlin

theorem mul_measureReal_upperTailEvent_finset_sum_le_integral_finset_sum
    (s : Finset ι) {Y : ι → Ω → ℝ} {b : ℝ}
    [IsFiniteMeasure μ]
    (hb : 0 ≤ b)
    (hY_nonneg : ∀ i ∈ s, ∀ ω, 0 ≤ Y i ω)
    (hY_int : ∀ i ∈ s, Integrable (Y i) μ) :
    b * μ.real (upperTailEvent (fun ω => Finset.sum s (fun i => Y i ω)) b) ≤
      Finset.sum s (fun i => ∫ ω, Y i ω ∂μ) := by
  let F : Ω → ℝ := Finset.sum s Y
  have hF_eq : F = fun ω => Finset.sum s (fun i => Y i ω) := by
    funext ω
    simp [F]
  have hF_nonneg : 0 ≤ᵐ[μ] F := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    show 0 ≤ F ω
    simpa [F] using Finset.sum_nonneg (fun i hi => hY_nonneg i hi ω)
  have hF_int : Integrable F μ := by
    simpa [F] using integrable_finsetSum' s hY_int
  have hmono :
      μ.real (upperTailEvent F b) ≤ μ.real {ω | b ≤ F ω} := by
    refine measureReal_mono ?_
    intro ω hω
    show b ≤ F ω
    exact le_of_lt hω
  have hmain : b * μ.real (upperTailEvent F b) ≤ Finset.sum s (fun i => ∫ ω, Y i ω ∂μ) := by
    calc
      b * μ.real (upperTailEvent F b) ≤ b * μ.real {ω | b ≤ F ω} := by
        exact mul_le_mul_of_nonneg_left hmono hb
      _ ≤ ∫ ω, F ω ∂μ := by
        simpa [F, upperTailEvent] using
          (mul_meas_ge_le_integral_of_nonneg (μ := μ) hF_nonneg hF_int b)
      _ = Finset.sum s (fun i => ∫ ω, Y i ω ∂μ) := by
        rw [hF_eq]
        rw [integral_finsetSum s hY_int]
  simpa [hF_eq] using hmain

theorem measureReal_upperTailEvent_finset_sum_le_div
    (s : Finset ι) {Y : ι → Ω → ℝ} {b : ℝ}
    [IsFiniteMeasure μ]
    (hb : 0 < b)
    (hY_nonneg : ∀ i ∈ s, ∀ ω, 0 ≤ Y i ω)
    (hY_int : ∀ i ∈ s, Integrable (Y i) μ) :
    μ.real (upperTailEvent (fun ω => Finset.sum s (fun i => Y i ω)) b) ≤
      (Finset.sum s (fun i => ∫ ω, Y i ω ∂μ) / b) := by
  exact (le_div_iff₀' hb).2
    (mul_measureReal_upperTailEvent_finset_sum_le_integral_finset_sum
      (μ := μ) s hb.le hY_nonneg hY_int)

/-- The finite-sum Step 5 reduction: after truncating each variable at level
`rᵢ`, the upper tail of the original sum is controlled by Markov's inequality
applied to the truncated sum. -/
theorem measureReal_upperTailEvent_finset_sum_le_div_of_upperTailIndicator
    (s : Finset ι) {X : ι → Ω → ℝ} {r : ι → ℝ} {b : ℝ}
    [IsFiniteMeasure μ]
    (hr : ∀ i ∈ s, 0 ≤ r i) (hb : 0 < b)
    (hInt : ∀ i ∈ s, Integrable (upperTailIndicator (X i) (r i)) μ) :
    μ.real (upperTailEvent (fun ω => Finset.sum s (fun i => X i ω)) (b + Finset.sum s r)) ≤
      (Finset.sum s (fun i => ∫ ω, upperTailIndicator (X i) (r i) ω ∂μ) / b) := by
  have hsubset :
      upperTailEvent (fun ω => Finset.sum s (fun i => X i ω)) (b + Finset.sum s r) ⊆
        upperTailEvent (fun ω => Finset.sum s (fun i => upperTailIndicator (X i) (r i) ω)) b :=
    upperTailEvent_finset_sum_subset_upperTailIndicator_finset_sum
      (Ω := Ω) (ι := ι) s hr
  refine (measureReal_mono hsubset).trans ?_
  refine measureReal_upperTailEvent_finset_sum_le_div (μ := μ) s hb ?_ hInt
  intro i hi ω
  exact upperTailIndicator_nonneg (hr i hi) ω

/-- Step 5 pre-triangle estimate in weak-Orlicz form: after truncating each
variable at level `aᵢ * (t / 2)`, the finite-sum Markov reduction and the
one-variable truncation bound combine into the tail estimate at scale
`(∑ aᵢ) * t`. -/
theorem measureReal_upperTailEvent_finset_sum_le_of_isBigOWith
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {Ψ : ℝ → ℝ} {q C₀ t : ℝ}
    [IsFiniteMeasure μ]
    (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 1 < q)
    (hs : s.Nonempty) (ht : 2 ≤ t)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigOWith μ Ψ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    μ.real (upperTailEvent (fun ω => Finset.sum s (fun i => X i ω)) ((Finset.sum s a) * t)) ≤
      (1 + C₀ / (q - 1)) * (Ψ (t / 2))⁻¹ := by
  let r : ι → ℝ := fun i => a i * (t / 2)
  let b : ℝ := (Finset.sum s a) * (t / 2)
  let K : ℝ := (1 + C₀ / (q - 1)) * (Ψ (t / 2))⁻¹
  have ht_half : 1 ≤ t / 2 := by
    nlinarith
  have ht_half_pos : 0 < t / 2 := by
    nlinarith
  have hr : ∀ i ∈ s, 0 ≤ r i := by
    intro i hi
    simpa [r] using mul_nonneg (ha i hi).le ht_half_pos.le
  have hsuma_pos : 0 < Finset.sum s a := by
    rcases hs with ⟨i₀, hi₀⟩
    exact Finset.sum_pos' (fun i hi => (ha i hi).le) ⟨i₀, hi₀, ha i₀ hi₀⟩
  have hb : 0 < b := by
    exact mul_pos hsuma_pos ht_half_pos
  have hInt : ∀ i ∈ s, Integrable (upperTailIndicator (X i) (r i)) μ := by
    intro i hi
    simpa [r] using
      integrable_upperTailIndicator_of_isBigOWith
        (μ := μ) (Ψ := Ψ) (X := X i) (a := a i) (q := q) (C₀ := C₀) (t := t / 2)
        hD hAdmissible hq (ha i hi) ht_half (hX i hi) (hXm i hi)
  have hmain :=
    measureReal_upperTailEvent_finset_sum_le_div_of_upperTailIndicator
      (μ := μ) (s := s) (X := X) (r := r) (b := b) hr hb hInt
  have hsum_r : Finset.sum s r = b := by
    simp [b, r, Finset.sum_mul]
  have hthreshold : b + Finset.sum s r = (Finset.sum s a) * t := by
    rw [hsum_r]
    change (Finset.sum s a * (t / 2)) + (Finset.sum s a * (t / 2)) = (Finset.sum s a) * t
    ring_nf
  rw [hthreshold] at hmain
  have hsum_bound :
      Finset.sum s (fun i => ∫ ω, upperTailIndicator (X i) (r i) ω ∂μ) ≤ b * K := by
    calc
      Finset.sum s (fun i => ∫ ω, upperTailIndicator (X i) (r i) ω ∂μ)
        ≤ Finset.sum s (fun i => a i * (t / 2) * K) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            simpa [r, K, mul_assoc, mul_left_comm, mul_comm] using
              integral_upperTailIndicator_le_of_isBigOWith
                (μ := μ) (Ψ := Ψ) (X := X i) (a := a i) (q := q) (C₀ := C₀) (t := t / 2)
                hD hAdmissible hq (ha i hi) ht_half (hX i hi) (hXm i hi)
      _ = (Finset.sum s (fun i => a i * (t / 2))) * K := by
            rw [Finset.sum_mul]
      _ = b * K := by
            simp [b, Finset.sum_mul]
  have hquot :
      (Finset.sum s (fun i => ∫ ω, upperTailIndicator (X i) (r i) ω ∂μ) / b) ≤ K := by
    calc
      (Finset.sum s (fun i => ∫ ω, upperTailIndicator (X i) (r i) ω ∂μ) / b)
        ≤ (b * K) / b := by
            exact div_le_div_of_nonneg_right hsum_bound hb.le
      _ = K := by
            field_simp [hb.ne']
  exact hmain.trans hquot

/-- The symmetric Step 5 estimate used for the weak-Orlicz triangle
inequality: control the absolute tail of a finite sum from `IsBigO` data on
the summands. -/
theorem measureReal_absTailEvent_finset_sum_le_of_isBigO
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {Ψ : ℝ → ℝ} {q C₀ t : ℝ}
    [IsFiniteMeasure μ]
    (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 1 < q)
    (hs : s.Nonempty) (ht : 2 ≤ t)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    μ.real (absTailEvent (fun ω => Finset.sum s (fun i => X i ω)) ((Finset.sum s a) * t)) ≤
      (1 + C₀ / (q - 1)) * (Ψ (t / 2))⁻¹ := by
  have hsubset :
      absTailEvent (fun ω => Finset.sum s (fun i => X i ω)) ((Finset.sum s a) * t) ⊆
        upperTailEvent (fun ω => Finset.sum s (fun i => |X i ω|)) ((Finset.sum s a) * t) :=
    absTailEvent_finset_sum_subset_upperTailEvent_sum_abs (Ω := Ω) (ι := ι) (s := s)
  refine (measureReal_mono hsubset).trans ?_
  simpa [IsBigO] using
      measureReal_upperTailEvent_finset_sum_le_of_isBigOWith
        (μ := μ) (s := s) (X := fun i ω => |X i ω|) (a := a)
        (Ψ := Ψ) (q := q) (C₀ := C₀) (t := t)
        hD hAdmissible hq hs ht ha hX
        (fun i hi => by
          simpa [Real.norm_eq_abs] using (hXm i hi).norm)

/-- The explicit Chapter 4 dilation constant produced by the abstract
doubling-based triangle inequality. -/
def psiTriangleConst (q C₀ : ℝ) : ℝ :=
  2 * (C₀ * (1 + C₀ / (q - 1))) ^ (1 / q)

theorem psiTriangleConst_two_le_four_mul {C : ℝ} (hC : 1 ≤ C) :
    psiTriangleConst 2 C ≤ 4 * C := by
  have hC_nonneg : 0 ≤ C := le_trans zero_le_one hC
  have hinner_nonneg : 0 ≤ C * (1 + C) := by positivity
  have hinner :
      C * (1 + C) ≤ (2 * C) ^ 2 := by
    nlinarith
  have hrpow_two : ((2 * C) ^ (2 : ℝ)) = (2 * C) ^ 2 := by
    simp
  calc
    psiTriangleConst 2 C = 2 * (C * (1 + C)) ^ (1 / 2 : ℝ) := by
      norm_num [psiTriangleConst]
    _ ≤ 2 * ((2 * C) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Real.rpow_le_rpow hinner_nonneg (by simpa [hrpow_two] using hinner) (by positivity)
    _ = 2 * (2 * C) := by
      rw [hrpow_two, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    _ = 4 * C := by ring

/-- A prefactor in front of an inverse `Ψ` tail can be absorbed into a
dilation witness `σ`, provided the abstract doubling estimate makes the factor
small enough. -/
theorem prefactor_mul_inv_le_inv_of_hasPsiAbstractDoubling
    {Ψ : ℝ → ℝ} {q C₀ B σ t : ℝ}
    (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (ht : 1 ≤ t) (hσ : 1 ≤ σ)
    (hB_nonneg : 0 ≤ B) (hfac : B * (C₀ * σ ^ (-q)) ≤ 1) :
    B * (Ψ (σ * t))⁻¹ ≤ (Ψ t)⁻¹ := by
  have htail :
      (Ψ (σ * t))⁻¹ ≤ C₀ * σ ^ (-q) * (Ψ t)⁻¹ := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      hasPsiAbstractDoubling_inv_mul_le (hD := hD) (hAdmissible := hAdmissible)
        (u := t) (v := σ) ht hσ
  have hΨt_one : 1 ≤ Ψ t := hAdmissible.2 (le_trans zero_le_one ht)
  have hΨt_inv_nonneg : 0 ≤ (Ψ t)⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hΨt_one)
  calc
    B * (Ψ (σ * t))⁻¹ ≤ B * (C₀ * σ ^ (-q) * (Ψ t)⁻¹) := by
      exact mul_le_mul_of_nonneg_left htail hB_nonneg
    _ = (B * (C₀ * σ ^ (-q))) * (Ψ t)⁻¹ := by ring
    _ ≤ 1 * (Ψ t)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hfac hΨt_inv_nonneg
    _ = (Ψ t)⁻¹ := by ring

/-- The finite-family weak-Orlicz triangle inequality with an explicit
dilation witness `σ`. The witness is carried as data rather than hidden inside
the scale, so later model-specific choices of `σ` can be formalized
independently. -/
theorem isBigO_finset_sum_of_hasPsiAbstractDoubling
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {Ψ : ℝ → ℝ} {q C₀ σ : ℝ}
    [IsFiniteMeasure μ]
    (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 1 < q)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i))
    (hσ : 1 ≤ σ)
    (hσ_small : (1 + C₀ / (q - 1)) * (C₀ * σ ^ (-q)) ≤ 1) :
    IsBigO μ Ψ (fun ω => Finset.sum s (fun i => X i ω)) ((2 * σ) * Finset.sum s a) := by
  intro t ht
  have ht_pre : 2 ≤ 2 * σ * t := by
    nlinarith
  have hpre :=
    measureReal_absTailEvent_finset_sum_le_of_isBigO
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := Ψ) (q := q) (C₀ := C₀) (t := 2 * σ * t)
      hD hAdmissible hq hs ht_pre ha hX hXm
  have hthreshold :
      (Finset.sum s a) * (2 * σ * t) = (((2 * σ) * Finset.sum s a) * t) := by
    ring
  have hhalf : (2 * σ * t) / 2 = σ * t := by
    ring
  rw [hthreshold, hhalf] at hpre
  have hB_nonneg : 0 ≤ 1 + C₀ / (q - 1) := by
    have hC₀_one : 1 ≤ C₀ := hasPsiAbstractDoubling_one_le_const hD hAdmissible
    have hq_sub_pos : 0 < q - 1 := sub_pos.mpr hq
    have hfrac_nonneg : 0 ≤ C₀ / (q - 1) := by
      exact div_nonneg (le_trans zero_le_one hC₀_one) hq_sub_pos.le
    nlinarith
  have habsorb :
      (1 + C₀ / (q - 1)) * (Ψ (σ * t))⁻¹ ≤ (Ψ t)⁻¹ := by
    exact prefactor_mul_inv_le_inv_of_hasPsiAbstractDoubling
      (hD := hD) (hAdmissible := hAdmissible) (q := q) (C₀ := C₀)
      (B := 1 + C₀ / (q - 1)) (σ := σ) (t := t) ht hσ hB_nonneg hσ_small
  exact hpre.trans habsorb

/-- The first finished finite-family weak-Orlicz triangle theorem. The scale
constant is expressed explicitly in terms of the abstract doubling data, while
the witness-based theorem above remains available for later refinements. -/
theorem isBigO_finset_sum_of_isBigO
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {Ψ : ℝ → ℝ} {q C₀ : ℝ}
    [IsFiniteMeasure μ]
    (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 1 < q)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ Ψ (fun ω => Finset.sum s (fun i => X i ω))
      (psiTriangleConst q C₀ * Finset.sum s a) := by
  let B : ℝ := 1 + C₀ / (q - 1)
  let σ : ℝ := (C₀ * B) ^ (1 / q)
  have hq_ne : q ≠ 0 := by
    linarith
  have hC₀_one : 1 ≤ C₀ := hasPsiAbstractDoubling_one_le_const hD hAdmissible
  have hq_sub_pos : 0 < q - 1 := sub_pos.mpr hq
  have hfrac_nonneg : 0 ≤ C₀ / (q - 1) := by
    exact div_nonneg (le_trans zero_le_one hC₀_one) hq_sub_pos.le
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    nlinarith
  have hB_one : 1 ≤ B := by
    dsimp [B]
    nlinarith
  have hA_nonneg : 0 ≤ C₀ * B := mul_nonneg (le_trans zero_le_one hC₀_one) hB_nonneg
  have hA_one : 1 ≤ C₀ * B := by
    exact one_le_mul_of_one_le_of_one_le hC₀_one hB_one
  have hA_pos : 0 < C₀ * B := lt_of_lt_of_le zero_lt_one hA_one
  have hσ : 1 ≤ σ := by
    dsimp [σ]
    exact Real.one_le_rpow hA_one (by positivity : 0 ≤ (1 / q : ℝ))
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have hσ_pow : σ ^ q = C₀ * B := by
    dsimp [σ]
    rw [show (1 / q : ℝ) = q⁻¹ by field_simp [hq_ne]]
    simpa using (Real.rpow_inv_rpow hA_nonneg hq_ne)
  have hσ_small : B * (C₀ * σ ^ (-q)) ≤ 1 := by
    have hσ_negq : σ ^ (-q) = (C₀ * B)⁻¹ := by
      rw [Real.rpow_neg hσ_pos.le, hσ_pow]
    calc
      B * (C₀ * σ ^ (-q)) = B * (C₀ * (C₀ * B)⁻¹) := by rw [hσ_negq]
      _ = 1 := by
            field_simp [hA_pos.ne']
      _ ≤ 1 := by rfl
  have hmain :=
    isBigO_finset_sum_of_hasPsiAbstractDoubling
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := Ψ) (q := q) (C₀ := C₀) (σ := σ)
      hD hAdmissible hq hs ha hX hXm hσ hσ_small
  simpa [psiTriangleConst, B, σ, mul_assoc, mul_left_comm, mul_comm] using hmain

/-- Growth-hypothesis specialization of the finite-family weak-Orlicz triangle
inequality, using the abstract doubling constant already derived in
`PsiCalculus.lean`. -/
theorem isBigO_finset_sum_of_isBigO_growth
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {Ψ : ℝ → ℝ} {K : ℝ}
    [IsFiniteMeasure μ]
    (hK : 2 ≤ K) (hGrowth : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ Ψ (fun ω => Finset.sum s (fun i => X i ω))
      (psiTriangleConst 2 (K ^ (12 : ℝ)) * Finset.sum s a) := by
  have hD : HasPsiAbstractDoubling Ψ 2 (K ^ (12 : ℝ)) := by
    simpa using admissiblePsi_hasPsiAbstractDoubling_two
      (K := K) hK hGrowth hAdmissible
  simpa using
    isBigO_finset_sum_of_isBigO
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := Ψ) (q := (2 : ℝ))
      (C₀ := K ^ (12 : ℝ)) hD hAdmissible (by norm_num) hs ha hX hXm

/-- A note-facing simplification of the growth-based triangle theorem:
the explicit abstract constant is bounded by `4 K^12`. -/
theorem isBigO_finset_sum_of_isBigO_growth_four_mul
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {Ψ : ℝ → ℝ} {K : ℝ}
    [IsFiniteMeasure μ]
    (hK : 2 ≤ K) (hGrowth : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ Ψ (fun ω => Finset.sum s (fun i => X i ω))
      ((4 * K ^ (12 : ℝ)) * Finset.sum s a) := by
  have hmain :=
    isBigO_finset_sum_of_isBigO_growth
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := Ψ) (K := K)
      hK hGrowth hAdmissible hs ha hX hXm
  have hK_one : 1 ≤ K := le_trans one_le_two hK
  have hKpow_one : 1 ≤ K ^ (12 : ℝ) := by
    exact Real.one_le_rpow hK_one (by positivity : 0 ≤ (12 : ℝ))
  have hsuma_nonneg : 0 ≤ Finset.sum s a := by
    exact Finset.sum_nonneg fun i hi => (ha i hi).le
  refine IsBigO.mono_scale (μ := μ) (Ψ := Ψ)
    (X := fun ω => Finset.sum s (fun i => X i ω))
    (A := psiTriangleConst 2 (K ^ (12 : ℝ)) * Finset.sum s a)
    (B := (4 * K ^ (12 : ℝ)) * Finset.sum s a) hmain ?_
  exact mul_le_mul_of_nonneg_right (psiTriangleConst_two_le_four_mul hKpow_one) hsuma_nonneg

/-- Average version of the finite-family weak-Orlicz triangle theorem. -/
theorem isBigO_finsetAverage_of_isBigO
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {Ψ : ℝ → ℝ} {q C₀ : ℝ}
    [IsFiniteMeasure μ]
    (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 1 < q)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ Ψ
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (psiTriangleConst q C₀ * (((s.card : ℝ)⁻¹) * Finset.sum s a)) := by
  have hsum :=
    isBigO_finset_sum_of_isBigO
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := Ψ) (q := q) (C₀ := C₀)
      hD hAdmissible hq hs ha hX hXm
  have hcard_inv_nonneg : 0 ≤ (s.card : ℝ)⁻¹ := by positivity
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    IsBigO.const_mul (μ := μ) (Ψ := Ψ)
      (X := fun ω => Finset.sum s (fun i => X i ω))
      (A := psiTriangleConst q C₀ * Finset.sum s a)
      (c := (s.card : ℝ)⁻¹) hcard_inv_nonneg hsum

/-- Note-facing average version of the growth-based triangle theorem with the
coarse constant simplified to `4 K^12`. -/
theorem isBigO_finsetAverage_of_isBigO_growth_four_mul
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {Ψ : ℝ → ℝ} {K : ℝ}
    [IsFiniteMeasure μ]
    (hK : 2 ≤ K) (hGrowth : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ Ψ
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      ((4 * K ^ (12 : ℝ)) * (((s.card : ℝ)⁻¹) * Finset.sum s a)) := by
  have hsum :=
    isBigO_finset_sum_of_isBigO_growth_four_mul
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := Ψ) (K := K)
      hK hGrowth hAdmissible hs ha hX hXm
  have hcard_inv_nonneg : 0 ≤ (s.card : ℝ)⁻¹ := by positivity
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    IsBigO.const_mul (μ := μ) (Ψ := Ψ)
      (X := fun ω => Finset.sum s (fun i => X i ω))
      (A := (4 * K ^ (12 : ℝ)) * Finset.sum s a)
      (c := (s.card : ℝ)⁻¹) hcard_inv_nonneg hsum

/-- The explicit stretched-exponential triangle constant obtained by feeding
the concrete `Γ_σ` growth witness into the general `O_Ψ` calculus. -/
noncomputable def gammaTriangleConst (σ : ℝ) : ℝ :=
  4 * gammaGrowthConst σ ^ (12 : ℝ)

/-- Finite-family generalized triangle inequality specialized to the
stretched-exponential class `Γ_σ`. -/
theorem isBigO_finset_sum_of_isBigO_gammaSigma
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 0 < σ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (gammaSigma σ) (fun ω => Finset.sum s (fun i => X i ω))
      (gammaTriangleConst σ * Finset.sum s a) := by
  have hK : 2 ≤ gammaGrowthConst σ := two_le_gammaGrowthConst σ
  have hGrowth : HasPsiGrowth (gammaSigma σ) (gammaGrowthConst σ) :=
    hasPsiGrowth_gammaSigma hσ
  have hAdmissible : AdmissiblePsi (gammaSigma σ) :=
    admissiblePsi_gammaSigma hσ.le
  simpa [gammaTriangleConst, mul_assoc, mul_left_comm, mul_comm] using
    isBigO_finset_sum_of_isBigO_growth_four_mul
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := gammaSigma σ)
      (K := gammaGrowthConst σ) hK hGrowth hAdmissible hs ha hX hXm

/-- Average version of the stretched-exponential generalized triangle
inequality. -/
theorem isBigO_finsetAverage_of_isBigO_gammaSigma
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 0 < σ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (gammaSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (gammaTriangleConst σ * (((s.card : ℝ)⁻¹) * Finset.sum s a)) := by
  have hK : 2 ≤ gammaGrowthConst σ := two_le_gammaGrowthConst σ
  have hGrowth : HasPsiGrowth (gammaSigma σ) (gammaGrowthConst σ) :=
    hasPsiGrowth_gammaSigma hσ
  have hAdmissible : AdmissiblePsi (gammaSigma σ) :=
    admissiblePsi_gammaSigma hσ.le
  simpa [gammaTriangleConst, mul_assoc, mul_left_comm, mul_comm] using
    isBigO_finsetAverage_of_isBigO_growth_four_mul
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := gammaSigma σ)
      (K := gammaGrowthConst σ) hK hGrowth hAdmissible hs ha hX hXm

/-- The explicit Chapter 4 triangle constant for the log-normal model class
`Ψ_σ`, obtained from the growth constant `K_{Ψ_σ} = 2 exp(2σ²)`. -/
noncomputable def psiSigmaTriangleConst (σ : ℝ) : ℝ :=
  4 * psiGrowthConst σ ^ (12 : ℝ)

/-- Finite-family generalized triangle inequality specialized to the
log-normal class `Ψ_σ`. -/
theorem isBigO_finset_sum_of_isBigO_psiSigma
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 1 ≤ σ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (psiSigma σ) (fun ω => Finset.sum s (fun i => X i ω))
      (psiSigmaTriangleConst σ * Finset.sum s a) := by
  have hK : 2 ≤ psiGrowthConst σ := two_le_psiGrowthConst σ
  have hGrowth : HasPsiGrowth (psiSigma σ) (psiGrowthConst σ) :=
    hasPsiGrowth_psiSigma hσ
  have hAdmissible : AdmissiblePsi (psiSigma σ) :=
    admissiblePsi_psiSigma (le_trans zero_le_one hσ)
  simpa [psiSigmaTriangleConst, mul_assoc, mul_left_comm, mul_comm] using
    isBigO_finset_sum_of_isBigO_growth_four_mul
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := psiSigma σ)
      (K := psiGrowthConst σ) hK hGrowth hAdmissible hs ha hX hXm

/-- Average version of the log-normal generalized triangle inequality. -/
theorem isBigO_finsetAverage_of_isBigO_psiSigma
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 1 ≤ σ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ (psiSigma σ) (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IsBigO μ (psiSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (psiSigmaTriangleConst σ * (((s.card : ℝ)⁻¹) * Finset.sum s a)) := by
  have hK : 2 ≤ psiGrowthConst σ := two_le_psiGrowthConst σ
  have hGrowth : HasPsiGrowth (psiSigma σ) (psiGrowthConst σ) :=
    hasPsiGrowth_psiSigma hσ
  have hAdmissible : AdmissiblePsi (psiSigma σ) :=
    admissiblePsi_psiSigma (le_trans zero_le_one hσ)
  simpa [psiSigmaTriangleConst, mul_assoc, mul_left_comm, mul_comm] using
    isBigO_finsetAverage_of_isBigO_growth_four_mul
      (μ := μ) (s := s) (X := X) (a := a) (Ψ := psiSigma σ)
      (K := psiGrowthConst σ) hK hGrowth hAdmissible hs ha hX hXm

end Measure

end

end IndependentSums
end Homogenization
