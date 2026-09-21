/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiConcentration.Truncation

/-! # Tail Kernel -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Primitive used in the weighted layer-cake estimate for
`t ↦ t² e^{λt}`. -/
theorem integral_sq_exp_weight (l s : ℝ) :
    ∫ t in 0..s, ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) =
      s ^ (2 : ℕ) * Real.exp (l * s) := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) s,
        HasDerivAt (fun u : ℝ => u ^ (2 : ℕ) * Real.exp (l * u))
          (((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t))) t := by
    intro t ht
    have hpow : HasDerivAt (fun u : ℝ => u ^ (2 : ℕ)) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have hexp : HasDerivAt (fun u : ℝ => Real.exp (l * u)) (l * Real.exp (l * t)) t := by
      simpa [mul_comm] using ((hasDerivAt_id t).const_mul l).exp
    convert hpow.mul hexp using 1
    all_goals first | rfl | ring
  have hint :
      IntervalIntegrable
        (fun t : ℝ => ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)))
        volume 0 s := by
    refine Continuous.intervalIntegrable ?_ 0 s
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp

omit [MeasurableSpace Ω] in
/-- On the positive slice `0 < t ≤ L`, the event
`{t ≤ max(min(X, L), 0)}` agrees exactly with `{t ≤ X}`. -/
theorem upperTruncation_posPart_tailSet_eq
    {X : Ω → ℝ} {t L : ℝ}
    (ht : 0 < t) (htL : t ≤ L) :
    {ω | t ≤ max (upperTruncation X L ω) 0} = {ω | t ≤ X ω} := by
  ext ω
  constructor
  · intro hω
    change t ≤ max (upperTruncation X L ω) 0 at hω
    have htrunc_pos : 0 < upperTruncation X L ω := by
      by_contra hnonpos
      have hmaxeq : max (upperTruncation X L ω) 0 = 0 := max_eq_right (le_of_not_gt hnonpos)
      rw [hmaxeq] at hω
      exact not_le_of_gt ht hω
    have hmaxeq : max (upperTruncation X L ω) 0 = upperTruncation X L ω := max_eq_left htrunc_pos.le
    rw [hmaxeq] at hω
    exact hω.trans (upperTruncation_le_self X L ω)
  · intro hω
    change t ≤ max (upperTruncation X L ω) 0
    have htrunc : t ≤ upperTruncation X L ω := by
      simpa [upperTruncation] using (show t ≤ min (X ω) L from le_min hω htL)
    exact htrunc.trans (le_max_left _ _)

omit [MeasurableSpace Ω] in
theorem upperTruncation_posPart_le
    {X : Ω → ℝ} {L : ℝ} {ω : Ω}
    (hL : 0 ≤ L) :
    max (upperTruncation X L ω) 0 ≤ L := by
  exact max_le (upperTruncation_le X L ω) hL

omit [MeasurableSpace Ω] in
theorem abs_upperTruncation_le_abs_self
    {X : Ω → ℝ} {L : ℝ} {ω : Ω}
    (hL : 0 ≤ L) :
    |upperTruncation X L ω| ≤ |X ω| := by
  by_cases hω : X ω ≤ L
  · rw [upperTruncation_of_le hω]
  · have hω' : L < X ω := lt_of_not_ge hω
    rw [upperTruncation_of_lt hω']
    have hX_nonneg : 0 ≤ X ω := le_trans hL hω'.le
    simpa [abs_of_nonneg hL, abs_of_nonneg hX_nonneg] using hω'.le

omit [MeasurableSpace Ω] in
theorem upperTruncation_sq_mul_exp_max_le_abs_sq_add_posPart_sq_mul_exp
    {X : Ω → ℝ} {l L : ℝ} {ω : Ω}
    (hL : 0 ≤ L) :
    upperTruncation X L ω ^ (2 : ℕ) * Real.exp (l * max (upperTruncation X L ω) 0) ≤
      |X ω| ^ (2 : ℕ) +
        (max (upperTruncation X L ω) 0) ^ (2 : ℕ) *
          Real.exp (l * max (upperTruncation X L ω) 0) := by
  by_cases hpos : 0 ≤ upperTruncation X L ω
  · have hmax : max (upperTruncation X L ω) 0 = upperTruncation X L ω := max_eq_left hpos
    rw [hmax]
    exact le_add_of_nonneg_left (by positivity)
  · have hneg : upperTruncation X L ω < 0 := lt_of_not_ge hpos
    have hmax : max (upperTruncation X L ω) 0 = 0 := max_eq_right hneg.le
    have habs :
        |upperTruncation X L ω| ≤ |X ω| := abs_upperTruncation_le_abs_self (X := X) (L := L) (ω := ω) hL
    have hsq :
        upperTruncation X L ω ^ (2 : ℕ) ≤ |X ω| ^ (2 : ℕ) := by
      exact sq_le_sq.2 (by simpa using habs)
    rw [hmax]
    simpa using hsq

/-- Layer-cake identity for the weighted positive part of the upper truncation
`max(min(X, L), 0)`. This is the natural `Set.Ioc 0 L` version that precedes
the note-facing `[1, L]` estimate. -/
theorem integral_upperTruncation_posPart_sq_mul_exp_eq_integral_Ioc_tail
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {l L : ℝ}
    (hXm : Measurable X) (hl : 0 ≤ l) (hL : 0 ≤ L) :
    ∫ ω,
        (max (upperTruncation X L ω) 0) ^ (2 : ℕ) *
          Real.exp (l * max (upperTruncation X L ω) 0) ∂μ =
      ∫ t in Set.Ioc 0 L,
        ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
          μ.real {ω | t ≤ X ω} ∂volume := by
  let Yp : Ω → ℝ := fun ω => max (upperTruncation X L ω) 0
  let g : ℝ → ℝ := fun t => ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t))
  have hYpm : Measurable Yp := by
    exact (upperTruncation_measurable (X := X) (L := L) hXm).max measurable_const
  have hYp_nonneg : ∀ ω, 0 ≤ Yp ω := by
    intro ω
    exact le_max_right _ _
  have hYp_nonneg_ae : 0 ≤ᵐ[μ] Yp := Filter.Eventually.of_forall hYp_nonneg
  have hYpae : AEMeasurable Yp μ := hYpm.aemeasurable
  have hYp_le : ∀ ω, Yp ω ≤ L := by
    intro ω
    simpa [Yp] using upperTruncation_posPart_le (X := X) (L := L) (ω := ω) hL
  have hweight_nonneg :
      0 ≤ᵐ[μ] fun ω =>
        Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    positivity
  have hweight_meas :
      AEStronglyMeasurable
        (fun ω => Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω)) μ := by
    exact ((hYpm.pow_const 2).mul ((hYpm.const_mul l).exp)).aemeasurable.aestronglyMeasurable
  have hg_nonneg_of_pos : ∀ {t : ℝ}, 0 < t → 0 ≤ g t := by
    intro t ht0
    have hpoly : 0 ≤ 2 * t + l * t ^ (2 : ℕ) := by
      nlinarith [sq_nonneg t, ht0, hl]
    exact mul_nonneg hpoly (Real.exp_pos _).le
  have hleft_enn :
      ∫⁻ ω, ENNReal.ofReal (Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω)) ∂μ =
        ∫⁻ ω, ENNReal.ofReal (∫ t in 0..Yp ω, g t) ∂μ := by
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall fun ω => by
      simpa [Yp, g] using (congrArg ENNReal.ofReal (integral_sq_exp_weight l (Yp ω))).symm
  have hleft :
      ∫ ω, Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω) ∂μ =
        ENNReal.toReal (∫⁻ ω, ENNReal.ofReal (∫ t in 0..Yp ω, g t) ∂μ) := by
    rw [integral_eq_lintegral_of_nonneg_ae hweight_nonneg hweight_meas, hleft_enn]
  have hg_intble : ∀ t > 0, IntervalIntegrable g volume 0 t := by
    intro t ht
    refine Continuous.intervalIntegrable ?_ 0 t
    fun_prop
  have hg_nonneg : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), 0 ≤ g t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht0 : 0 < t := by simpa using ht
    have hpoly : 0 ≤ 2 * t + l * t ^ (2 : ℕ) := by
      nlinarith [ht0, hl]
    exact mul_nonneg hpoly (Real.exp_pos _).le
  have hlayer :
      ∫⁻ ω, ENNReal.ofReal (∫ t in 0..Yp ω, g t) ∂μ =
        ∫⁻ t in Set.Ioi 0, μ {ω | t ≤ Yp ω} * ENNReal.ofReal (g t) ∂volume := by
    exact lintegral_comp_eq_lintegral_meas_le_mul μ hYp_nonneg_ae hYpae hg_intble hg_nonneg
  have htail_meas_enn : Measurable fun t : ℝ => μ {ω | t ≤ Yp ω} := by
    refine Antitone.measurable ?_
    intro s t hst
    exact measure_mono fun ω hω => hst.trans hω
  have htail_meas : Measurable fun t : ℝ => μ.real {ω | t ≤ Yp ω} := by
    simpa [Measure.real] using htail_meas_enn.ennreal_toReal
  have hg_meas : Measurable g := by
    fun_prop
  have htail_real_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi 0)] fun t => g t * μ.real {ω | t ≤ Yp ω} := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro t ht
    exact mul_nonneg (hg_nonneg_of_pos ht) (by positivity)
  have htail_real_meas :
      AEStronglyMeasurable (fun t => g t * μ.real {ω | t ≤ Yp ω})
        (volume.restrict (Set.Ioi 0)) := by
    exact (hg_meas.mul htail_meas).aestronglyMeasurable
  have hright_Ioi :
      ∫ t in Set.Ioi 0, g t * μ.real {ω | t ≤ Yp ω} ∂volume =
        ENNReal.toReal (∫⁻ t in Set.Ioi 0, μ {ω | t ≤ Yp ω} * ENNReal.ofReal (g t) ∂volume) := by
    have aux := @integral_eq_lintegral_of_nonneg_ae _ _
      ((volume : Measure ℝ).restrict (Set.Ioi 0))
      (fun t => g t * μ.real {ω | t ≤ Yp ω}) htail_real_nonneg htail_real_meas
    rw [aux]
    congr 1
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hmeasure_eq :
        ENNReal.ofReal (μ.real {ω | t ≤ Yp ω}) = μ {ω | t ≤ Yp ω} := by
      simp [measureReal_def, (measure_lt_top μ {ω | t ≤ Yp ω}).ne]
    calc
      ENNReal.ofReal (g t * μ.real {ω | t ≤ Yp ω}) =
          ENNReal.ofReal (g t) * ENNReal.ofReal (μ.real {ω | t ≤ Yp ω}) := by
            rw [ENNReal.ofReal_mul (hg_nonneg_of_pos ht)]
      _ = ENNReal.ofReal (g t) * μ {ω | t ≤ Yp ω} := by rw [hmeasure_eq]
      _ = μ {ω | t ≤ Yp ω} * ENNReal.ofReal (g t) := by rw [mul_comm]
  have hIoi :
      ∫ ω, Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω) ∂μ =
        ∫ t in Set.Ioi 0, g t * μ.real {ω | t ≤ Yp ω} ∂volume := by
    calc
      ∫ ω, Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω) ∂μ =
          ENNReal.toReal (∫⁻ ω, ENNReal.ofReal (∫ t in 0..Yp ω, g t) ∂μ) := hleft
      _ = ENNReal.toReal
          (∫⁻ t in Set.Ioi 0, μ {ω | t ≤ Yp ω} * ENNReal.ofReal (g t) ∂volume) := by
            rw [hlayer]
      _ = ∫ t in Set.Ioi 0, g t * μ.real {ω | t ≤ Yp ω} ∂volume := hright_Ioi.symm
  have hrestrict :
      ∫ t in Set.Ioi 0, g t * μ.real {ω | t ≤ Yp ω} ∂volume =
        ∫ t in Set.Ioc 0 L, g t * μ.real {ω | t ≤ Yp ω} ∂volume := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Ioi Set.Ioc_subset_Ioi_self]
    intro t ht
    have ht0 : 0 < t := ht.1
    have htL : L < t := by
      by_contra hle
      exact ht.2 ⟨ht0, le_of_not_gt hle⟩
    have hsubset : {ω | t ≤ Yp ω} ⊆ ∅ := by
      intro ω hω
      exact False.elim (not_le_of_gt htL (hω.trans (hYp_le ω)))
    have hmeas0 : μ {ω | t ≤ Yp ω} = 0 := measure_mono_null hsubset (by simp)
    have hzero : μ.real {ω | t ≤ Yp ω} = 0 := by
      simp [measureReal_def, hmeas0]
    simp [g, hzero]
  have hreplace :
      ∫ t in Set.Ioc 0 L, g t * μ.real {ω | t ≤ Yp ω} ∂volume =
        ∫ t in Set.Ioc 0 L, g t * μ.real {ω | t ≤ X ω} ∂volume := by
    apply integral_congr_ae
    refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht0 : 0 < t := by simpa using ht.1
    have htL : t ≤ L := ht.2
    have htail_eq : μ.real {ω | t ≤ Yp ω} = μ.real {ω | t ≤ X ω} := by
      simpa [Yp] using congrArg μ.real (upperTruncation_posPart_tailSet_eq (X := X) ht0 htL)
    simpa using congrArg (fun s : ℝ => g t * s) htail_eq
  simpa [Yp, g] using hIoi.trans (hrestrict.trans hreplace)

/-- The weighted positive-part term in the heavy-tail Taylor remainder is
integrable on a finite measure space because `max(min(X, L), 0)` is bounded by
`L`. -/
theorem integrable_upperTruncation_posPart_sq_mul_exp
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {l L : ℝ}
    (hXm : Measurable X) (hl : 0 ≤ l) (hL : 0 ≤ L) :
    Integrable
      (fun ω =>
        (max (upperTruncation X L ω) 0) ^ (2 : ℕ) *
          Real.exp (l * max (upperTruncation X L ω) 0)) μ := by
  let Yp : Ω → ℝ := fun ω => max (upperTruncation X L ω) 0
  have hYpm : Measurable Yp := by
    exact (upperTruncation_measurable (X := X) (L := L) hXm).max measurable_const
  refine Integrable.mono'
    (integrable_const (L ^ (2 : ℕ) * Real.exp (l * L)))
    (((hYpm.pow_const 2).mul ((hYpm.const_mul l).exp)).aemeasurable.aestronglyMeasurable)
    ?_
  filter_upwards with ω
  have hYp_nonneg : 0 ≤ Yp ω := le_max_right _ _
  have hYp_le : Yp ω ≤ L := by
    simpa [Yp] using upperTruncation_posPart_le (X := X) (L := L) (ω := ω) hL
  have hsq_le : Yp ω ^ (2 : ℕ) ≤ L ^ (2 : ℕ) := by
    exact (sq_le_sq₀ hYp_nonneg hL).2 hYp_le
  have hexp_le : Real.exp (l * Yp ω) ≤ Real.exp (l * L) := by
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_left hYp_le hl
  have hbound :
      Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω) ≤ L ^ (2 : ℕ) * Real.exp (l * L) := by
    exact mul_le_mul hsq_le hexp_le (by positivity) (by positivity)
  have hnonneg :
      0 ≤ Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω) := by
    positivity
  simpa [Yp, Real.norm_of_nonneg hnonneg] using hbound

/-- The weighted truncation term is controlled by the square moment of `X` plus
the weighted positive-part term, hence by the natural `Set.Ioc 0 L` tail
integral from the layer-cake formula. -/
theorem integral_upperTruncation_sq_mul_exp_max_le_integral_abs_sq_add_integral_Ioc_tail
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {l L : ℝ}
    (hXm : Measurable X)
    (hXsq : Integrable (fun ω => |X ω| ^ (2 : ℕ)) μ)
    (hl : 0 ≤ l) (hL : 0 ≤ L) :
    ∫ ω,
        upperTruncation X L ω ^ (2 : ℕ) *
          Real.exp (l * max (upperTruncation X L ω) 0) ∂μ ≤
      ∫ ω, |X ω| ^ (2 : ℕ) ∂μ +
        ∫ t in Set.Ioc 0 L,
          ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
            μ.real {ω | t ≤ X ω} ∂volume := by
  let Y : Ω → ℝ := upperTruncation X L
  let Yp : Ω → ℝ := fun ω => max (Y ω) 0
  let W : Ω → ℝ := fun ω => Y ω ^ (2 : ℕ) * Real.exp (l * Yp ω)
  let Wp : Ω → ℝ := fun ω => Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω)
  have hYm : Measurable Y := upperTruncation_measurable (X := X) (L := L) hXm
  have hYpm : Measurable Yp := by
    exact hYm.max measurable_const
  have hWp_int : Integrable Wp μ := by
    simpa [Y, Yp, Wp] using
      integrable_upperTruncation_posPart_sq_mul_exp (μ := μ) (X := X) (l := l) (L := L) hXm hl hL
  have hsum_int : Integrable (fun ω => |X ω| ^ (2 : ℕ) + Wp ω) μ :=
    hXsq.add hWp_int
  have hW_meas : AEStronglyMeasurable W μ := by
    exact ((hYm.pow_const 2).mul ((hYpm.const_mul l).exp)).aemeasurable.aestronglyMeasurable
  have hW_int : Integrable W μ := by
    refine Integrable.mono' hsum_int hW_meas ?_
    filter_upwards with ω
    have hbound :
        W ω ≤ |X ω| ^ (2 : ℕ) + Wp ω := by
      simpa [Y, Yp, W, Wp] using
        upperTruncation_sq_mul_exp_max_le_abs_sq_add_posPart_sq_mul_exp
          (X := X) (l := l) (L := L) (ω := ω) hL
    have hnonneg : 0 ≤ W ω := by
      positivity
    simpa [Real.norm_of_nonneg hnonneg] using hbound
  have hmono :
      ∀ᵐ ω ∂μ, W ω ≤ |X ω| ^ (2 : ℕ) + Wp ω :=
    Filter.Eventually.of_forall fun ω => by
      simpa [Y, Yp, W, Wp] using
        upperTruncation_sq_mul_exp_max_le_abs_sq_add_posPart_sq_mul_exp
          (X := X) (l := l) (L := L) (ω := ω) hL
  calc
    ∫ ω, W ω ∂μ ≤ ∫ ω, |X ω| ^ (2 : ℕ) + Wp ω ∂μ :=
      integral_mono_ae hW_int hsum_int hmono
    _ = ∫ ω, |X ω| ^ (2 : ℕ) ∂μ + ∫ ω, Wp ω ∂μ := by
      simpa [Pi.add_apply] using integral_add hXsq hWp_int
    _ = ∫ ω, |X ω| ^ (2 : ℕ) ∂μ +
          ∫ t in Set.Ioc 0 L,
            ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
              μ.real {ω | t ≤ X ω} ∂volume := by
      rw [integral_upperTruncation_posPart_sq_mul_exp_eq_integral_Ioc_tail
        (μ := μ) (X := X) (l := l) (L := L) hXm hl hL]

/-- The full weighted truncation term is integrable once `|X|²` is integrable,
because it is pointwise dominated by `|X|²` plus the bounded positive-part
weight. -/
theorem integrable_upperTruncation_sq_mul_exp_max_of_integrable_abs_sq
    [IsFiniteMeasure μ]
    {X : Ω → ℝ} {l L : ℝ}
    (hXm : Measurable X)
    (hXsq : Integrable (fun ω => |X ω| ^ (2 : ℕ)) μ)
    (hl : 0 ≤ l) (hL : 0 ≤ L) :
    Integrable
      (fun ω =>
        upperTruncation X L ω ^ (2 : ℕ) *
          Real.exp (l * max (upperTruncation X L ω) 0)) μ := by
  let Y : Ω → ℝ := upperTruncation X L
  let Yp : Ω → ℝ := fun ω => max (Y ω) 0
  let W : Ω → ℝ := fun ω => Y ω ^ (2 : ℕ) * Real.exp (l * Yp ω)
  let Wp : Ω → ℝ := fun ω => Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω)
  have hYm : Measurable Y := upperTruncation_measurable (X := X) (L := L) hXm
  have hYpm : Measurable Yp := by
    exact hYm.max measurable_const
  have hWp_int : Integrable Wp μ := by
    simpa [Y, Yp, Wp] using
      integrable_upperTruncation_posPart_sq_mul_exp (μ := μ) (X := X) (l := l) (L := L) hXm hl hL
  have hsum_int : Integrable (fun ω => |X ω| ^ (2 : ℕ) + Wp ω) μ :=
    hXsq.add hWp_int
  have hW_meas : AEStronglyMeasurable W μ := by
    exact ((hYm.pow_const 2).mul ((hYpm.const_mul l).exp)).aemeasurable.aestronglyMeasurable
  refine Integrable.mono' hsum_int hW_meas ?_
  filter_upwards with ω
  have hbound :
      W ω ≤ |X ω| ^ (2 : ℕ) + Wp ω := by
    simpa [Y, Yp, W, Wp] using
      upperTruncation_sq_mul_exp_max_le_abs_sq_add_posPart_sq_mul_exp
        (X := X) (l := l) (L := L) (ω := ω) hL
  have hnonneg : 0 ≤ W ω := by
    positivity
  simpa [Real.norm_of_nonneg hnonneg] using! hbound


end

end IndependentSums

end Homogenization
