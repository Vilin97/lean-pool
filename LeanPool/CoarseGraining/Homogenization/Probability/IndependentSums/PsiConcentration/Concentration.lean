/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.PsiConcentration.TailKernel

/-! # Concentration -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Taylor plus the nonpositive mean of the truncation gives the one-variable
mgf bound in the natural `1 + A` form before the note-facing tail estimates
are inserted. -/
theorem mgf_upperTruncation_le_one_add_half_mul_sq_mul_integral_abs_sq_add_integral_Ioc_tail_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {l L : ℝ}
    (hXm : Measurable X)
    (hXint : Integrable X μ)
    (hXsq : Integrable (fun ω => |X ω| ^ (2 : ℕ)) μ)
    (hXmean : ∫ ω, X ω ∂μ = 0)
    (hl : 0 ≤ l) (hL : 0 ≤ L) :
    mgf (upperTruncation X L) μ l ≤
      1 + (l ^ (2 : ℕ) / 2) *
        (∫ ω, |X ω| ^ (2 : ℕ) ∂μ +
          ∫ t in Set.Ioc 0 L,
            ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
              μ.real {ω | t ≤ X ω} ∂volume) := by
  let Y : Ω → ℝ := upperTruncation X L
  let Yp : Ω → ℝ := fun ω => max (Y ω) 0
  let W : Ω → ℝ := fun ω => Y ω ^ (2 : ℕ) * Real.exp (l * Yp ω)
  let c : ℝ := l ^ (2 : ℕ) / 2
  have hYint : Integrable Y μ := by
    simpa [Y] using integrable_upperTruncation_of_integrable (μ := μ) (X := X) (L := L) hXm hXint
  have hWint : Integrable W μ := by
    simpa [Y, Yp, W] using
      integrable_upperTruncation_sq_mul_exp_max_of_integrable_abs_sq
        (μ := μ) (X := X) (l := l) (L := L) hXm hXsq hl hL
  have hExp_int : Integrable (fun ω => Real.exp (l * Y ω)) μ := by
    simpa [Y] using integrable_exp_mul_upperTruncation (μ := μ) (X := X) (l := l) (L := L) hXm hl
  have hlin_int : Integrable (fun ω => l * Y ω) μ := hYint.const_mul l
  have hquad_int : Integrable (fun ω => c * W ω) μ := hWint.const_mul c
  have hrhs_int : Integrable (fun ω => 1 + l * Y ω + c * W ω) μ := by
    have hsplit :
        (fun ω => 1 + l * Y ω + c * W ω) =
          (fun _ : Ω => (1 : ℝ)) + ((fun ω => l * Y ω) + fun ω => c * W ω) := by
      funext ω
      simp [add_assoc]
    rw [hsplit]
    exact (integrable_const (1 : ℝ)).add (hlin_int.add hquad_int)
  have hpoint :
      ∀ᵐ ω ∂μ, Real.exp (l * Y ω) ≤ 1 + l * Y ω + c * W ω := by
    filter_upwards with ω
    simpa [Y, Yp, W, c, mul_assoc, mul_left_comm, mul_comm] using
      exp_mul_le_one_add_mul_add_half_mul_sq_mul_exp_max_zero_of_nonneg
        (l := l) (x := Y ω) hl
  have hYmean_nonpos : ∫ ω, Y ω ∂μ ≤ 0 := by
    simpa [Y] using
      integral_upperTruncation_le_zero_of_integral_eq_zero
        (μ := μ) (X := X) (L := L) hXm hXint hXmean
  have hc_nonneg : 0 ≤ c := by
    positivity
  calc
    mgf (upperTruncation X L) μ l = ∫ ω, Real.exp (l * Y ω) ∂μ := by
      rfl
    _ ≤ ∫ ω, 1 + l * Y ω + c * W ω ∂μ :=
      integral_mono_ae hExp_int hrhs_int hpoint
    _ = 1 + l * ∫ ω, Y ω ∂μ + c * ∫ ω, W ω ∂μ := by
      calc
        ∫ ω, 1 + l * Y ω + c * W ω ∂μ
            = ∫ ω, ((fun _ : Ω => (1 : ℝ)) + (fun ω => l * Y ω) + fun ω => c * W ω) ω ∂μ := by
                simp [add_assoc]
        _ = ∫ ω, (1 : ℝ) + l * Y ω ∂μ + ∫ ω, c * W ω ∂μ := by
              simpa [Pi.add_apply] using
                integral_add ((integrable_const (1 : ℝ)).add hlin_int) hquad_int
        _ = (∫ ω, (fun _ : Ω => (1 : ℝ)) ω ∂μ + ∫ ω, l * Y ω ∂μ) + ∫ ω, c * W ω ∂μ := by
              congr 1
              simpa [Pi.add_apply] using integral_add (integrable_const (1 : ℝ)) hlin_int
        _ = 1 + l * ∫ ω, Y ω ∂μ + c * ∫ ω, W ω ∂μ := by
              have hscaled : ∫ ω, c * W ω ∂μ = c * ∫ ω, W ω ∂μ := by
                simpa using integral_const_mul c W
              rw [integral_const, integral_const_mul, hscaled]
              simp [smul_eq_mul, c, add_assoc]
    _ ≤ 1 + c * ∫ ω, W ω ∂μ := by
      nlinarith
    _ ≤ 1 + c *
          (∫ ω, |X ω| ^ (2 : ℕ) ∂μ +
            ∫ t in Set.Ioc 0 L,
              ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
                μ.real {ω | t ≤ X ω} ∂volume) := by
      have hscaled :=
        add_le_add_left
          (mul_le_mul_of_nonneg_left
            (integral_upperTruncation_sq_mul_exp_max_le_integral_abs_sq_add_integral_Ioc_tail
              (μ := μ) (X := X) (l := l) (L := L) hXm hXsq hl hL)
            hc_nonneg)
          1
      simpa [Y, W, add_assoc] using! hscaled

/-- Exponential form of the one-variable truncated mgf bound. This is the
direct input used by the generic Chernoff reduction for sums of truncated
variables. -/
theorem mgf_upperTruncation_le_exp_of_integral_abs_sq_add_integral_Ioc_tail_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {l L : ℝ}
    (hXm : Measurable X)
    (hXint : Integrable X μ)
    (hXsq : Integrable (fun ω => |X ω| ^ (2 : ℕ)) μ)
    (hXmean : ∫ ω, X ω ∂μ = 0)
    (hl : 0 ≤ l) (hL : 0 ≤ L) :
    mgf (upperTruncation X L) μ l ≤
      Real.exp
        ((l ^ (2 : ℕ) / 2) *
          (∫ ω, |X ω| ^ (2 : ℕ) ∂μ +
            ∫ t in Set.Ioc 0 L,
              ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
                μ.real {ω | t ≤ X ω} ∂volume)) := by
  calc
    mgf (upperTruncation X L) μ l
        ≤ 1 + (l ^ (2 : ℕ) / 2) *
            (∫ ω, |X ω| ^ (2 : ℕ) ∂μ +
              ∫ t in Set.Ioc 0 L,
                ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
                  μ.real {ω | t ≤ X ω} ∂volume) :=
      mgf_upperTruncation_le_one_add_half_mul_sq_mul_integral_abs_sq_add_integral_Ioc_tail_of_integral_eq_zero
        (μ := μ) (X := X) (l := l) (L := L) hXm hXint hXsq hXmean hl hL
    _ ≤ Real.exp
          ((l ^ (2 : ℕ) / 2) *
            (∫ ω, |X ω| ^ (2 : ℕ) ∂μ +
              ∫ t in Set.Ioc 0 L,
                ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
                  μ.real {ω | t ≤ X ω} ∂volume)) := by
      simpa [add_comm] using
        (Real.add_one_le_exp
          ((l ^ (2 : ℕ) / 2) *
            (∫ ω, |X ω| ^ (2 : ℕ) ∂μ +
              ∫ t in Set.Ioc 0 L,
                ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
                  μ.real {ω | t ≤ X ω} ∂volume)))

/-- A symmetric `O_Ψ(1)` tail bound together with the integrability of
`t / Ψ(t)` controls the second moment. This is the scalar moment estimate used
later in the heavy-tail Chernoff argument. -/
theorem lintegral_abs_sq_le_two_add_two_mul_of_isBigO_of_lintegral_tail
    [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {X : Ω → ℝ} {CΨ : ℝ}
    (hXm : Measurable X)
    (hAdmissible : AdmissiblePsi Ψ)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / Ψ t) ∂volume ≤ ENNReal.ofReal CΨ)
    (hX : IsBigO μ Ψ X 1) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 : ℕ)) ∂μ ≤ ENNReal.ofReal (2 + 2 * CΨ) := by
  let Y : Ω → ℝ := fun ω => |X ω|
  let g : ℝ → ENNReal := fun t => μ {ω | t < Y ω} * ENNReal.ofReal t
  have hY_nonneg : ∀ ω, 0 ≤ Y ω := by
    intro ω
    simp [Y]
  have hY_nonneg_ae : 0 ≤ᵐ[μ] Y := Filter.Eventually.of_forall hY_nonneg
  have hYm : AEMeasurable Y μ := (hXm.aemeasurable.norm : AEMeasurable Y μ)
  have hLayer :=
    MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
      (μ := μ) hY_nonneg_ae hYm (p := (2 : ℝ)) (by positivity : 0 < (2 : ℝ))
  have hLayer' :
      ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 : ℕ)) ∂μ =
        ENNReal.ofReal (2 : ℝ) * ∫⁻ t in Set.Ioi 0, g t ∂volume := by
    simpa [Y, g, Real.rpow_natCast, show (2 : ℝ) - 1 = 1 by norm_num] using hLayer
  have hsplit :
      ∫⁻ t in Set.Ioi 0, g t ∂volume =
        ∫⁻ t in Set.Ioc 0 1, g t ∂volume + ∫⁻ t in Set.Ioi 1, g t ∂volume := by
    have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
      ext t
      constructor
      · intro ht
        rcases ht with ht | ht
        · exact ht.1
        · exact lt_trans zero_lt_one (by simpa using ht)
      · intro ht
        by_cases ht1 : t ≤ 1
        · exact Or.inl ⟨ht, ht1⟩
        · exact Or.inr (lt_of_not_ge ht1)
    rw [← hunion]
    exact MeasureTheory.lintegral_union measurableSet_Ioi
      (Set.disjoint_left.2 fun t ht0 ht1 => not_lt_of_ge ht0.2 ht1)
  have hpart0 :
      ∫⁻ t in Set.Ioc 0 1, g t ∂volume ≤ 1 := by
    have hmono :
        g ≤ᵐ[volume.restrict (Set.Ioc 0 1)] fun _ => (1 : ENNReal) := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall ?_
      intro t ht
      have hmeasure_le : μ {ω | t < Y ω} ≤ 1 := by
        calc
          μ {ω | t < Y ω} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := by simp
      have ht_le_one : ENNReal.ofReal t ≤ 1 := by
        exact le_trans (ENNReal.ofReal_le_ofReal ht.2) (by simp)
      calc
        g t = μ {ω | t < Y ω} * ENNReal.ofReal t := by rfl
        _ ≤ 1 * 1 := by
              exact mul_le_mul hmeasure_le ht_le_one (by positivity) (by positivity)
        _ = 1 := by simp
    calc
      ∫⁻ t in Set.Ioc 0 1, g t ∂volume ≤ ∫⁻ t : ℝ in Set.Ioc 0 1, (1 : ENNReal) ∂volume := by
            exact lintegral_mono_ae hmono
      _ = 1 * volume (Set.Ioc (0 : ℝ) 1) := by simp
      _ = 1 := by norm_num [Real.volume_Ioc]
  have hpart1 :
      ∫⁻ t in Set.Ioi 1, g t ∂volume ≤ ENNReal.ofReal CΨ := by
    have hmono :
        g ≤ᵐ[volume.restrict (Set.Ioi 1)] fun t => ENNReal.ofReal (t / Ψ t) := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall ?_
      intro t ht
      have htail_real :
          μ.real {ω | t < Y ω} ≤ (Ψ t)⁻¹ := by
        simpa [IsBigO, IsBigOWith, Y, upperTailEvent] using hX ht.le
      have hmeasure_eq :
          μ {ω | t < Y ω} = ENNReal.ofReal (μ.real {ω | t < Y ω}) := by
        simp [Measure.real, (measure_lt_top μ {ω | t < Y ω}).ne]
      have hmeasure_le :
          μ {ω | t < Y ω} ≤ ENNReal.ofReal ((Ψ t)⁻¹) := by
        rw [hmeasure_eq]
        exact ENNReal.ofReal_le_ofReal htail_real
      have ht_one : 1 < t := by simpa using ht
      have ht_nonneg : 0 ≤ t := le_of_lt (lt_trans zero_lt_one ht_one)
      have hΨ_one : 1 ≤ Ψ t := hAdmissible.2 ht_nonneg
      have hΨ_inv_nonneg : 0 ≤ (Ψ t)⁻¹ := by
        exact inv_nonneg.mpr (le_trans zero_le_one hΨ_one)
      calc
        g t = μ {ω | t < Y ω} * ENNReal.ofReal t := by rfl
        _ ≤ ENNReal.ofReal ((Ψ t)⁻¹) * ENNReal.ofReal t := by
              exact mul_le_mul_of_nonneg_right hmeasure_le (by positivity)
        _ = ENNReal.ofReal (((Ψ t)⁻¹) * t) := by
              rw [← ENNReal.ofReal_mul hΨ_inv_nonneg]
        _ = ENNReal.ofReal (t / Ψ t) := by
              rw [div_eq_mul_inv, mul_comm]
    exact (lintegral_mono_ae hmono).trans hCΨ
  calc
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 : ℕ)) ∂μ
      = ENNReal.ofReal (2 : ℝ) * ∫⁻ t in Set.Ioi 0, g t ∂volume := hLayer'
    _ ≤ ENNReal.ofReal (2 : ℝ) * (1 + ENNReal.ofReal CΨ) := by
          gcongr
          rw [hsplit]
          exact add_le_add hpart0 hpart1
    _ = ENNReal.ofReal (2 : ℝ) * (ENNReal.ofReal 1 + ENNReal.ofReal CΨ) := by
          norm_num
    _ = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (1 + CΨ) := by
          rw [← ENNReal.ofReal_add (show 0 ≤ (1 : ℝ) by norm_num) hCΨ_nonneg]
    _ = ENNReal.ofReal ((2 : ℝ) * (1 + CΨ)) := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ))]
    _ = ENNReal.ofReal (2 + 2 * CΨ) := by
          congr 1
          ring

/-- Real-integral version of
`lintegral_abs_sq_le_two_add_two_mul_of_isBigO_of_lintegral_tail`. -/
theorem integral_abs_sq_le_two_add_two_mul_of_isBigO_of_lintegral_tail
    [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {X : Ω → ℝ} {CΨ : ℝ}
    (hXm : Measurable X)
    (hAdmissible : AdmissiblePsi Ψ)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / Ψ t) ∂volume ≤ ENNReal.ofReal CΨ)
    (hX : IsBigO μ Ψ X 1) :
    ∫ ω, |X ω| ^ (2 : ℕ) ∂μ ≤ 2 + 2 * CΨ := by
  have hlin :=
    lintegral_abs_sq_le_two_add_two_mul_of_isBigO_of_lintegral_tail
      (μ := μ) (Ψ := Ψ) (X := X) (CΨ := CΨ)
      hXm hAdmissible hCΨ_nonneg hCΨ hX
  have hsq_meas : AEStronglyMeasurable (fun ω => |X ω| ^ (2 : ℕ)) μ :=
    ((hXm.aemeasurable.norm.pow_const 2).aestronglyMeasurable)
  have hsq_nonneg :
      0 ≤ᵐ[μ] fun ω => |X ω| ^ (2 : ℕ) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    positivity
  have hlin_ne_top :
      ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 : ℕ)) ∂μ ≠ (⊤ : ENNReal) := by
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hlin (by simp))
  have hbound_nonneg : 0 ≤ 2 + 2 * CΨ := by
    nlinarith
  calc
    ∫ ω, |X ω| ^ (2 : ℕ) ∂μ
      = ENNReal.toReal (∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 : ℕ)) ∂μ) := by
          exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hsq_nonneg hsq_meas
    _ ≤ ENNReal.toReal (ENNReal.ofReal (2 + 2 * CΨ)) := by
          exact ENNReal.toReal_mono (by simp) hlin
    _ = 2 + 2 * CΨ := by
          simpa using ENNReal.toReal_ofReal hbound_nonneg

/-- Generic Chernoff reduction for a finite independent family once each
one-variable mgf is bounded by `exp (vᵢ)`. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_of_iIndepFun_of_mgf_le_exp
    [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} {v : ι → ℝ} {s : Finset ι} {a l : ℝ}
    (h_indep : iIndepFun Y μ)
    (h_meas : ∀ i, Measurable (Y i))
    (hl : 0 ≤ l)
    (h_int : ∀ i ∈ s, Integrable (fun ω => Real.exp (l * Y i ω)) μ)
    (hmgf : ∀ i ∈ s, mgf (Y i) μ l ≤ Real.exp (v i)) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, Y i ω) a) ≤
      Real.exp (-l * a + ∑ i ∈ s, v i) := by
  have h_int_sum : Integrable (fun ω => Real.exp (l * (∑ i ∈ s, Y i ω))) μ := by
    have hsumfun : (fun ω => ∑ i ∈ s, Y i ω) = ∑ i ∈ s, Y i := by
      funext ω
      simp [Finset.sum_apply]
    simpa [hsumfun] using h_indep.integrable_exp_mul_sum (t := l) h_meas h_int
  have hsubset :
      upperTailEvent (fun ω => ∑ i ∈ s, Y i ω) a ⊆ {ω | a ≤ ∑ i ∈ s, Y i ω} := by
    intro ω hω
    exact le_of_lt (by simpa [upperTailEvent] using hω)
  calc
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, Y i ω) a)
      ≤ Real.exp (-l * a) * mgf (fun ω => ∑ i ∈ s, Y i ω) μ l := by
          refine (measureReal_mono hsubset).trans ?_
          simpa using measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i ∈ s, Y i ω)
            (ε := a) (t := l) hl h_int_sum
    _ = Real.exp (-l * a) * ∏ i ∈ s, mgf (Y i) μ l := by
          have hsumfun : (fun ω => ∑ i ∈ s, Y i ω) = ∑ i ∈ s, Y i := by
            funext ω
            simp [Finset.sum_apply]
          rw [hsumfun, h_indep.mgf_sum (t := l) h_meas s]
    _ ≤ Real.exp (-l * a) * ∏ i ∈ s, Real.exp (v i) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine Finset.prod_le_prod₀ ?_ hmgf
          intro i hi
          exact mgf_nonneg
    _ = Real.exp (-l * a) * Real.exp (∑ i ∈ s, v i) := by
          rw [← Real.exp_sum]
    _ = Real.exp (-l * a + ∑ i ∈ s, v i) := by
          rw [← Real.exp_add]

/-- Chernoff reduction specialized to the one-sided upper truncation
`min (Xᵢ, L)`. -/
theorem measureReal_upperTailEvent_finset_sum_upperTruncation_le_exp_of_iIndepFun_of_mgf_le_exp
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {v : ι → ℝ} {s : Finset ι} {a l L : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hl : 0 ≤ l)
    (hmgf : ∀ i ∈ s, mgf (upperTruncation (X i) L) μ l ≤ Real.exp (v i)) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) ≤
      Real.exp (-l * a + ∑ i ∈ s, v i) := by
  let Y : ι → Ω → ℝ := fun i => upperTruncation (X i) L
  have h_indepY : iIndepFun Y μ := by
    simpa [Y] using! iIndepFun_upperTruncation (μ := μ) (X := X) (L := L) h_indep
  have h_measY : ∀ i, Measurable (Y i) := by
    intro i
    simpa [Y] using upperTruncation_measurable (X := X i) (L := L) (h_meas i)
  have h_intY : ∀ i ∈ s, Integrable (fun ω => Real.exp (l * Y i ω)) μ := by
    intro i hi
    simpa [Y] using
      integrable_exp_mul_upperTruncation (μ := μ) (X := X i) (l := l) (L := L) (h_meas i) hl
  simpa [Y] using
    measureReal_upperTailEvent_finset_sum_le_exp_of_iIndepFun_of_mgf_le_exp
      (μ := μ)
      (Y := Y)
      (v := v)
      (s := s)
      (a := a)
      (l := l)
      h_indepY
      h_measY
      hl
      h_intY
      hmgf

/-- Uniform one-variable mgf bounds produce the expected `card(s)` factor in
the exponent for the truncated sum. -/
theorem measureReal_upperTailEvent_finset_sum_upperTruncation_le_exp_card_mul_of_iIndepFun_of_mgf_le_exp
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {a l L v : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hl : 0 ≤ l)
    (hmgf : ∀ i ∈ s, mgf (upperTruncation (X i) L) μ l ≤ Real.exp v) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) ≤
      Real.exp (-l * a + (s.card : ℝ) * v) := by
  let w : ι → ℝ := fun _ => v
  have hmain :=
    measureReal_upperTailEvent_finset_sum_upperTruncation_le_exp_of_iIndepFun_of_mgf_le_exp
      (μ := μ)
      (X := X)
      (v := w)
      (s := s)
      (a := a)
      (l := l)
      (L := L)
      h_indep
      h_meas
      hl
      (by
        intro i hi
        simpa [w] using hmgf i hi)
  calc
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a)
      ≤ Real.exp (-l * a + ∑ i ∈ s, w i) := hmain
    _ = Real.exp (-l * a + (s.card : ℝ) * v) := by
          congr 1
          rw [Finset.sum_const, nsmul_eq_mul]

/-- The symmetric `O_Ψ(1)` hypothesis immediately controls the one-sided upper
tail needed by the truncation split. -/
theorem measureReal_upperTailEvent_le_inv_of_isBigO
    [IsFiniteMeasure μ]
    {Ψ : ℝ → ℝ} {X : Ω → ℝ} {t : ℝ}
    (hX : IsBigO μ Ψ X 1) (ht : 1 ≤ t) :
    μ.real (upperTailEvent X t) ≤ (Ψ t)⁻¹ := by
  have hsubset : upperTailEvent X t ⊆ absTailEvent X t := by
    intro ω hω
    exact lt_of_lt_of_le hω (le_abs_self (X ω))
  have hfinite : μ (absTailEvent X t) ≠ (⊤ : ENNReal) :=
    ne_of_lt (measure_lt_top _ _)
  exact (measureReal_mono hsubset hfinite).trans <| by
    simpa [IsBigO, IsBigOWith, absTailEvent] using hX ht

/-- The natural `Set.Ioc 0 L` tail integrand is integrable on finite intervals,
because the tail factor is bounded by `1` and the polynomial-exponential weight
is bounded on `[0, L]`. -/
theorem integrableOn_integrand_Ioc_tail
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {l L : ℝ}
    (hl : 0 ≤ l) (hL : 0 ≤ L) :
    IntegrableOn
      (fun t =>
        ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
          μ.real {ω | t ≤ X ω})
      (Set.Ioc 0 L) volume := by
  let f : ℝ → ℝ := fun t =>
    ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
      μ.real {ω | t ≤ X ω}
  let C : ℝ := ((2 * L + l * L ^ (2 : ℕ)) * Real.exp (l * L))
  have htail_meas_enn : Measurable fun t : ℝ => μ {ω | t ≤ X ω} := by
    refine Antitone.measurable ?_
    intro s t hst
    exact measure_mono fun ω hω => hst.trans hω
  have htail_meas : Measurable fun t : ℝ => μ.real {ω | t ≤ X ω} := by
    simpa [Measure.real] using htail_meas_enn.ennreal_toReal
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioc 0 L)) := by
    refine (((measurable_id.const_mul 2).add
        ((measurable_id.pow_const 2).const_mul l)).mul
      ((measurable_id.const_mul l).exp)).mul htail_meas |>.aestronglyMeasurable
  have hC_nonneg : 0 ≤ C := by
    have hpoly_nonneg : 0 ≤ 2 * L + l * L ^ (2 : ℕ) := by
      nlinarith [sq_nonneg L, hL, hl]
    exact mul_nonneg hpoly_nonneg (Real.exp_pos _).le
  change Integrable f (volume.restrict (Set.Ioc 0 L))
  refine Integrable.mono' (integrable_const C) hf_meas ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  refine Filter.Eventually.of_forall ?_
  intro t ht
  have ht_nonneg : 0 ≤ t := le_of_lt ht.1
  have ht_le_L : t ≤ L := ht.2
  have hmeasure_le : μ.real {ω | t ≤ X ω} ≤ 1 := by
    calc
      μ.real {ω | t ≤ X ω} ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hpoly_nonneg : 0 ≤ 2 * t + l * t ^ (2 : ℕ) := by
    nlinarith [sq_nonneg t, ht_nonneg, hl]
  have hsq_le : t ^ (2 : ℕ) ≤ L ^ (2 : ℕ) := by
    nlinarith [ht_nonneg, hL, ht_le_L]
  have hpoly_le : 2 * t + l * t ^ (2 : ℕ) ≤ 2 * L + l * L ^ (2 : ℕ) := by
    nlinarith
  have hexp_le : Real.exp (l * t) ≤ Real.exp (l * L) := by
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht_le_L hl)
  have hnonneg : 0 ≤ f t := by
    have hmeasure_nonneg : 0 ≤ μ.real {ω | t ≤ X ω} := by positivity
    exact mul_nonneg (mul_nonneg hpoly_nonneg (Real.exp_pos _).le) hmeasure_nonneg
  have hweight_le :
      ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t))
        ≤ ((2 * L + l * L ^ (2 : ℕ)) * Real.exp (l * L)) := by
    exact mul_le_mul hpoly_le hexp_le (by positivity) (by positivity)
  have hbound :
      f t ≤ C := by
    calc
      f t
          ≤ ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) * 1 := by
            exact mul_le_mul_of_nonneg_left hmeasure_le
              (mul_nonneg hpoly_nonneg (Real.exp_pos _).le)
      _ ≤ ((2 * L + l * L ^ (2 : ℕ)) * Real.exp (l * L)) * 1 := by
            gcongr
      _ = C := by simp [C]
  simpa [f, C, Real.norm_of_nonneg hnonneg] using hbound

/-- The small interval `(0, 1]` contributes a universal bounded term to the
truncated mgf exponent. -/
theorem integral_Ioc_zero_one_tail_le_exp_one
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {l : ℝ}
    (hXm : Measurable X) (hl : 0 ≤ l) (hl1 : l ≤ 1) :
    ∫ t in Set.Ioc 0 1,
      ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
        μ.real {ω | t ≤ X ω} ∂volume ≤
      Real.exp 1 := by
  let Yp : Ω → ℝ := fun ω => max (upperTruncation X 1 ω) 0
  have hYp_int :
      Integrable
        (fun ω =>
          Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω)) μ := by
    simpa [Yp] using
      integrable_upperTruncation_posPart_sq_mul_exp
        (μ := μ) (X := X) (l := l) (L := 1) hXm hl zero_le_one
  calc
    ∫ t in Set.Ioc 0 1,
        ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
          μ.real {ω | t ≤ X ω} ∂volume
      = ∫ ω, Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω) ∂μ := by
          simpa [Yp] using
            (integral_upperTruncation_posPart_sq_mul_exp_eq_integral_Ioc_tail
              (μ := μ) (X := X) (l := l) (L := 1) hXm hl zero_le_one).symm
    _ ≤ ∫ ω, Real.exp 1 ∂μ := by
          refine integral_mono_ae hYp_int (integrable_const (Real.exp 1)) ?_
          filter_upwards with ω
          have hYp_nonneg : 0 ≤ Yp ω := by
            exact le_max_right _ _
          have hYp_le_one : Yp ω ≤ 1 := by
            change max (upperTruncation X 1 ω) 0 ≤ (1 : ℝ)
            exact upperTruncation_posPart_le (X := X) (L := 1) (ω := ω) zero_le_one
          have hsq_le : Yp ω ^ (2 : ℕ) ≤ 1 := by
            have hsq_le' : Yp ω ^ (2 : ℕ) ≤ (1 : ℝ) ^ (2 : ℕ) := by
              exact (sq_le_sq₀ hYp_nonneg zero_le_one).2 hYp_le_one
            simpa using hsq_le'
          have hmul_le_one : l * Yp ω ≤ 1 := by
            nlinarith
          have hexp_le : Real.exp (l * Yp ω) ≤ Real.exp 1 := by
            exact Real.exp_le_exp.2 hmul_le_one
          have hbound :
              Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω) ≤ Real.exp 1 := by
            calc
              Yp ω ^ (2 : ℕ) * Real.exp (l * Yp ω)
                  ≤ 1 * Real.exp 1 := by
                    exact mul_le_mul hsq_le hexp_le (by positivity) (by positivity)
              _ = Real.exp 1 := by simp
          exact hbound
    _ = Real.exp 1 := by simp

/-- The Chapter 4 logarithmic constraint implies the deterministic kernel
bound `exp (λ t) / Ψ(t) ≤ M t^{-4}` on `[1, L]`. -/
theorem exp_mul_div_psi_le_mul_rpow_neg_four_of_log_constraint
    {Ψ : ℝ → ℝ} {l L M t : ℝ}
    (hAdmissible : AdmissiblePsi Ψ)
    (hM : 1 ≤ M)
    (ht : t ∈ Set.Icc 1 L)
    (hconstraint :
      l * t ≤ Real.log (Ψ t) - 4 * Real.log t + Real.log M) :
    Real.exp (l * t) / Ψ t ≤ M * t ^ (-4 : ℝ) := by
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have hΨ_pos : 0 < Ψ t := lt_of_lt_of_le zero_lt_one (hAdmissible.2 (le_trans zero_le_one ht.1))
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  rw [div_le_iff₀ hΨ_pos]
  calc
    Real.exp (l * t)
      ≤ Real.exp (Real.log (Ψ t) - 4 * Real.log t + Real.log M) := by
          exact Real.exp_le_exp.2 hconstraint
    _ = M * t ^ (-4 : ℝ) * Ψ t := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hΨ_pos, Real.exp_log hM_pos]
          rw [show Real.exp (-(4 * Real.log t)) = t ^ (-4 : ℝ) by
            rw [show -(4 * Real.log t) = Real.log t * (-4 : ℝ) by ring,
              Real.exp_mul, Real.exp_log ht_pos]]
          ring

/-- The large interval `[1, L]` tail contribution is controlled by the
deterministic kernel coming from the Chapter 4 logarithmic constraint. -/
theorem integral_Ioc_one_L_tail_le_two_mul_M_of_isBigO_of_log_constraint
    [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {X : Ω → ℝ} {l L M : ℝ}
    (hAdmissible : AdmissiblePsi Ψ)
    (hX : IsBigO μ Ψ X 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hM : 1 ≤ M)
    (hconstraint : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 1 L →
      l * t ≤ Real.log (Ψ t) - 4 * Real.log t + Real.log M) :
    ∫ t in Set.Ioc 1 L,
      ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
        μ.real {ω | t ≤ X ω} ∂volume ≤
      2 * M := by
  let f : ℝ → ℝ := fun t =>
    ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
      μ.real {ω | t ≤ X ω}
  let g : ℝ → ℝ := fun t => M * (2 * t ^ (-3 : ℝ) + t ^ (-2 : ℝ))
  have htail_eq :
      (fun t : ℝ => μ.real {ω | t ≤ X ω}) =ᵐ[volume.restrict (Set.Ioc 1 L)]
        fun t => μ.real {ω | t < X ω} := by
    refine (MeasureTheory.meas_le_ae_eq_meas_lt μ (volume.restrict (Set.Ioc 1 L)) X).mono ?_
    intro t ht
    exact congrArg ENNReal.toReal ht
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioc 1 L)) := by
    have htail_meas_enn : Measurable fun t : ℝ => μ {ω | t ≤ X ω} := by
      refine Antitone.measurable ?_
      intro s t hst
      exact measure_mono fun ω hω => hst.trans hω
    have htail_meas : Measurable fun t : ℝ => μ.real {ω | t ≤ X ω} := by
      simpa [Measure.real] using htail_meas_enn.ennreal_toReal
    refine (((measurable_id.const_mul 2).add
        ((measurable_id.pow_const 2).const_mul l)).mul
      ((measurable_id.const_mul l).exp)).mul htail_meas |>.aestronglyMeasurable
  have hpow3_Ioi : IntegrableOn (fun t : ℝ => t ^ (-3 : ℝ)) (Set.Ioi 1) volume :=
    integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) zero_lt_one
  have hpow2_Ioi : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi 1) volume :=
    integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) zero_lt_one
  have hg_Ioi : IntegrableOn g (Set.Ioi 1) volume := by
    refine ((hpow3_Ioi.const_mul 2).add hpow2_Ioi).const_mul M
  have hg_nonneg_Ioi :
      0 ≤ᵐ[volume.restrict (Set.Ioi 1)] g := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht_nonneg : 0 ≤ t := le_trans zero_le_one (le_of_lt ht)
    have hrpow_nonneg3 : 0 ≤ t ^ (-3 : ℝ) := Real.rpow_nonneg ht_nonneg _
    have hrpow_nonneg2 : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht_nonneg _
    have hinner_nonneg : 0 ≤ 2 * t ^ (-3 : ℝ) + t ^ (-2 : ℝ) := by
      positivity
    exact mul_nonneg (le_trans zero_le_one hM) hinner_nonneg
  have hg : IntegrableOn g (Set.Ioc 1 L) volume := hg_Ioi.mono_set Set.Ioc_subset_Ioi_self
  have hf_bound :
      ∀ᵐ t ∂volume.restrict (Set.Ioc 1 L), f t ≤ g t := by
    filter_upwards [htail_eq, self_mem_ae_restrict measurableSet_Ioc] with t htail ht
    have ht_mem : t ∈ Set.Icc 1 L := ⟨ht.1.le, ht.2⟩
    have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht.1.le
    have ht_pos : 0 < t := lt_trans zero_lt_one ht.1
    have htail_le :
        μ.real {ω | t < X ω} ≤ (Ψ t)⁻¹ := by
      simpa [upperTailEvent] using
        measureReal_upperTailEvent_le_inv_of_isBigO (μ := μ) (Ψ := Ψ) (X := X) hX ht.1.le
    have hpoly_nonneg : 0 ≤ 2 * t + l * t ^ (2 : ℕ) := by
      nlinarith [sq_nonneg t, ht_nonneg, hl]
    have hkernel :
        Real.exp (l * t) / Ψ t ≤ M * t ^ (-4 : ℝ) := by
      exact exp_mul_div_psi_le_mul_rpow_neg_four_of_log_constraint
        (Ψ := Ψ) (l := l) (L := L) (M := M) hAdmissible hM ht_mem (hconstraint ht_mem)
    have hpoly_le : 2 * t + l * t ^ (2 : ℕ) ≤ 2 * t + t ^ (2 : ℕ) := by
      nlinarith [sq_nonneg t, ht_nonneg, hl1]
    have hkernel_nonneg : 0 ≤ M * t ^ (-4 : ℝ) := by
      exact mul_nonneg (le_trans zero_le_one hM) (Real.rpow_nonneg ht_nonneg _)
    have hrpow_mul₁ : t * t ^ (-4 : ℝ) = t ^ (-3 : ℝ) := by
      calc
        t * t ^ (-4 : ℝ) = t ^ (1 : ℝ) * t ^ (-4 : ℝ) := by simp [Real.rpow_one]
        _ = t ^ ((1 : ℝ) + (-4 : ℝ)) := by
              rw [← Real.rpow_add ht_pos]
        _ = t ^ (-3 : ℝ) := by norm_num
    have hrpow_mul₂ : t ^ (2 : ℕ) * t ^ (-4 : ℝ) = t ^ (-2 : ℝ) := by
      calc
        t ^ (2 : ℕ) * t ^ (-4 : ℝ) = t * (t * t ^ (-4 : ℝ)) := by ring
        _ = t * t ^ (-3 : ℝ) := by rw [hrpow_mul₁]
        _ = t ^ (1 : ℝ) * t ^ (-3 : ℝ) := by simp [Real.rpow_one]
        _ = t ^ ((1 : ℝ) + (-3 : ℝ)) := by
              rw [← Real.rpow_add ht_pos]
        _ = t ^ (-2 : ℝ) := by norm_num
    have hPsi_nonneg : 0 ≤ Ψ t := by
      exact le_trans zero_le_one (hAdmissible.2 (le_trans zero_le_one ht_mem.1))
    have hexp_div_nonneg : 0 ≤ Real.exp (l * t) / Ψ t := by
      exact div_nonneg (Real.exp_pos _).le hPsi_nonneg
    calc
      f t = ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) * μ.real {ω | t ≤ X ω} := by
            rfl
      _ = ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) * μ.real {ω | t < X ω} := by
            rw [htail]
      _ ≤ ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) * (Ψ t)⁻¹ := by
            exact mul_le_mul_of_nonneg_left htail_le (mul_nonneg hpoly_nonneg (Real.exp_pos _).le)
      _ = (2 * t + l * t ^ (2 : ℕ)) * (Real.exp (l * t) / Ψ t) := by
            rw [div_eq_mul_inv]
            ring
      _ ≤ (2 * t + t ^ (2 : ℕ)) * (M * t ^ (-4 : ℝ)) := by
            exact mul_le_mul hpoly_le hkernel hexp_div_nonneg
              (by nlinarith [sq_nonneg t, ht_nonneg])
      _ = g t := by
            calc
              (2 * t + t ^ (2 : ℕ)) * (M * t ^ (-4 : ℝ))
                  = M * ((2 * t) * t ^ (-4 : ℝ) + t ^ (2 : ℕ) * t ^ (-4 : ℝ)) := by
                      ring
              _ = M * (2 * (t * t ^ (-4 : ℝ)) + t ^ (2 : ℕ) * t ^ (-4 : ℝ)) := by
                      ring
              _ = M * (2 * t ^ (-3 : ℝ) + t ^ (-2 : ℝ)) := by
                      rw [hrpow_mul₁, hrpow_mul₂]
              _ = g t := by
                      rfl
  have hf : IntegrableOn f (Set.Ioc 1 L) volume := by
    change Integrable f (volume.restrict (Set.Ioc 1 L))
    refine Integrable.mono' hg hf_meas ?_
    filter_upwards [hf_bound, self_mem_ae_restrict measurableSet_Ioc] with t ht ht_mem
    have ht_nonneg : 0 ≤ t := le_trans zero_le_one ht_mem.1.le
    have hf_nonneg : 0 ≤ f t := by
      have hmeasure_nonneg : 0 ≤ μ.real {ω | t ≤ X ω} := by positivity
      have hpoly_nonneg : 0 ≤ 2 * t + l * t ^ (2 : ℕ) := by
        nlinarith [sq_nonneg t, ht_nonneg, hl]
      exact mul_nonneg (mul_nonneg hpoly_nonneg (Real.exp_pos _).le) hmeasure_nonneg
    simpa [Real.norm_of_nonneg hf_nonneg] using ht
  have hmono_set :
      ∫ t in Set.Ioc 1 L, g t ∂volume ≤ ∫ t in Set.Ioi 1, g t ∂volume := by
    exact setIntegral_mono_set hg_Ioi hg_nonneg_Ioi Set.Ioc_subset_Ioi_self.eventuallyLE
  have hI3 := integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) zero_lt_one
  have hI2 := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) zero_lt_one
  calc
    ∫ t in Set.Ioc 1 L,
        ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
          μ.real {ω | t ≤ X ω} ∂volume
      = ∫ t in Set.Ioc 1 L, f t ∂volume := by rfl
    _ ≤ ∫ t in Set.Ioc 1 L, g t ∂volume := by
          exact setIntegral_mono_on_ae hf hg measurableSet_Ioc
            ((ae_restrict_iff' measurableSet_Ioc).1 hf_bound)
    _ ≤ ∫ t in Set.Ioi 1, g t ∂volume := hmono_set
    _ = 2 * M := by
          rw [show ∫ t in Set.Ioi 1, g t ∂volume =
              M * ∫ t in Set.Ioi 1, (2 * t ^ (-3 : ℝ) + t ^ (-2 : ℝ)) ∂volume by
            simp [g, integral_const_mul]]
          rw [integral_add (hpow3_Ioi.const_mul 2) hpow2_Ioi, integral_const_mul, hI3, hI2]
          ring

/-- Exact one-variable truncated mgf estimate under the Chapter 4 admissible
weak-Orlicz hypotheses. The constant reflects the currently formalized
`Set.Ioc 0 1` cleanup term. -/
theorem mgf_upperTruncation_le_exp_of_isBigO_of_lintegral_tail_of_log_constraint
    [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {X : Ω → ℝ} {CΨ l L M : ℝ}
    (hXm : Measurable X)
    (hXint : Integrable X μ)
    (hXmean : ∫ ω, X ω ∂μ = 0)
    (hAdmissible : AdmissiblePsi Ψ)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / Ψ t) ∂volume ≤ ENNReal.ofReal CΨ)
    (hX : IsBigO μ Ψ X 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hconstraint : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 1 L →
      l * t ≤ Real.log (Ψ t) - 4 * Real.log t + Real.log M) :
    mgf (upperTruncation X L) μ l ≤
      Real.exp (l ^ (2 : ℕ) * (1 + Real.exp 1 / 2 + M + CΨ)) := by
  let tailIntegrand : ℝ → ℝ := fun t =>
    ((2 * t + l * t ^ (2 : ℕ)) * Real.exp (l * t)) *
      μ.real {ω | t ≤ X ω}
  have hsq_nonneg :
      0 ≤ᵐ[μ] fun ω => |X ω| ^ (2 : ℕ) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    positivity
  have hlin_sq :=
    lintegral_abs_sq_le_two_add_two_mul_of_isBigO_of_lintegral_tail
      (μ := μ) (Ψ := Ψ) (X := X) (CΨ := CΨ)
      hXm hAdmissible hCΨ_nonneg hCΨ hX
  have hlin_sq_ne_top :
      ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (2 : ℕ)) ∂μ ≠ (⊤ : ENNReal) := by
    exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hlin_sq (by simp))
  have hXsq :
      Integrable (fun ω => |X ω| ^ (2 : ℕ)) μ := by
    exact (lintegral_ofReal_ne_top_iff_integrable
      ((hXm.aemeasurable.norm.pow_const 2).aestronglyMeasurable) hsq_nonneg).1 hlin_sq_ne_top
  have htail_int :
      IntegrableOn tailIntegrand (Set.Ioc 0 L) volume :=
    integrableOn_integrand_Ioc_tail (μ := μ) (X := X) (l := l) (L := L) hl (le_trans zero_le_one hL)
  have htail_split :
      ∫ t in Set.Ioc 0 L, tailIntegrand t ∂volume =
        ∫ t in Set.Ioc 0 1, tailIntegrand t ∂volume +
          ∫ t in Set.Ioc 1 L, tailIntegrand t ∂volume := by
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioc 1 L) := by
      refine Set.disjoint_left.2 ?_
      intro t ht0 ht1
      exact not_lt_of_ge ht0.2 ht1.1
    have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioc 1 L = Set.Ioc 0 L := by
      exact Set.Ioc_union_Ioc_eq_Ioc zero_le_one hL
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioc
      (htail_int.mono_set (by
        intro t ht
        exact ⟨ht.1, le_trans ht.2 hL⟩))
      (htail_int.mono_set (by
        intro t ht
        exact ⟨lt_trans zero_lt_one ht.1, ht.2⟩))
  have hmoment :
      ∫ ω, |X ω| ^ (2 : ℕ) ∂μ ≤ 2 + 2 * CΨ :=
    integral_abs_sq_le_two_add_two_mul_of_isBigO_of_lintegral_tail
      (μ := μ) (Ψ := Ψ) (X := X) (CΨ := CΨ)
      hXm hAdmissible hCΨ_nonneg hCΨ hX
  have hsmall :
      ∫ t in Set.Ioc 0 1, tailIntegrand t ∂volume ≤ Real.exp 1 :=
    integral_Ioc_zero_one_tail_le_exp_one (μ := μ) (X := X) (l := l) hXm hl hl1
  have hlarge :
      ∫ t in Set.Ioc 1 L, tailIntegrand t ∂volume ≤ 2 * M :=
    integral_Ioc_one_L_tail_le_two_mul_M_of_isBigO_of_log_constraint
      (μ := μ) (Ψ := Ψ) (X := X) (l := l) (L := L) (M := M)
      hAdmissible hX hl hl1 hM hconstraint
  have htail_total :
      ∫ t in Set.Ioc 0 L, tailIntegrand t ∂volume ≤ Real.exp 1 + 2 * M := by
    rw [htail_split]
    exact add_le_add hsmall hlarge
  calc
    mgf (upperTruncation X L) μ l
      ≤ Real.exp
          ((l ^ (2 : ℕ) / 2) *
            (∫ ω, |X ω| ^ (2 : ℕ) ∂μ +
              ∫ t in Set.Ioc 0 L, tailIntegrand t ∂volume)) :=
        by
          simpa [tailIntegrand] using
            mgf_upperTruncation_le_exp_of_integral_abs_sq_add_integral_Ioc_tail_of_integral_eq_zero
              (μ := μ) (X := X) (l := l) (L := L) hXm hXint hXsq hXmean hl (le_trans zero_le_one hL)
    _ ≤ Real.exp
          ((l ^ (2 : ℕ) / 2) *
            ((2 + 2 * CΨ) + (Real.exp 1 + 2 * M))) := by
          apply Real.exp_le_exp.2
          exact mul_le_mul_of_nonneg_left
            (add_le_add hmoment htail_total) (by positivity)
    _ = Real.exp (l ^ (2 : ℕ) * (1 + Real.exp 1 / 2 + M + CΨ)) := by
          congr 1
          ring

/-- Rounded one-variable truncated mgf estimate with the cleaner constant
`3 + M + C_Ψ`. -/
theorem mgf_upperTruncation_le_exp_of_isBigO_of_lintegral_tail_of_log_constraint_rounded
    [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {X : Ω → ℝ} {CΨ l L M : ℝ}
    (hXm : Measurable X)
    (hXint : Integrable X μ)
    (hXmean : ∫ ω, X ω ∂μ = 0)
    (hAdmissible : AdmissiblePsi Ψ)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / Ψ t) ∂volume ≤ ENNReal.ofReal CΨ)
    (hX : IsBigO μ Ψ X 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hconstraint : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 1 L →
      l * t ≤ Real.log (Ψ t) - 4 * Real.log t + Real.log M) :
    mgf (upperTruncation X L) μ l ≤
      Real.exp (l ^ (2 : ℕ) * (3 + M + CΨ)) := by
  have hmain :=
    mgf_upperTruncation_le_exp_of_isBigO_of_lintegral_tail_of_log_constraint
      (μ := μ) (Ψ := Ψ) (X := X) (CΨ := CΨ) (l := l) (L := L) (M := M)
      hXm hXint hXmean hAdmissible hCΨ_nonneg hCΨ hX hl hl1 hL hM hconstraint
  have hexp_half_le_two : Real.exp 1 / 2 ≤ 2 := by
    have hexp_lt_four : Real.exp 1 < 4 := by
      exact lt_trans Real.exp_one_lt_d9 (by norm_num)
    nlinarith
  refine hmain.trans ?_
  apply Real.exp_le_exp.2
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith

/-- Generic heavy-tail concentration estimate for centered finite independent
families under the Chapter 4 admissibility and logarithmic-kernel hypotheses. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_log_constraint
    [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {X : ι → Ω → ℝ} {s : Finset ι} {a l L CΨ M : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hAdmissible : AdmissiblePsi Ψ)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / Ψ t) ∂volume ≤ ENNReal.ofReal CΨ)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hconstraint : ∀ i ∈ s, ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 1 L →
      l * t ≤ Real.log (Ψ t) - 4 * Real.log t + Real.log M) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      Real.exp
        (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * (1 + Real.exp 1 / 2 + M + CΨ))) +
        (s.card : ℝ) * (Ψ L)⁻¹ := by
  let v : ℝ := l ^ (2 : ℕ) * (1 + Real.exp 1 / 2 + M + CΨ)
  have hX_with : ∀ i ∈ s, IsBigOWith μ Ψ (X i) 1 := by
    intro i hi
    exact IsBigOWith.of_le (μ := μ) (Ψ := Ψ) (X := fun ω => |X i ω|) (Y := X i) (A := 1)
      (by simpa [IsBigO] using hX i hi) (fun ω => le_abs_self (X i ω))
  have hsplit :=
    measureReal_upperTailEvent_finset_sum_le_upperTruncation_add_card_mul_of_isBigOWith
      (μ := μ) (Ψ := Ψ) (X := X) (s := s) (L := L) (a := a) hX_with hL
  have htrunc :
      μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) ≤
        Real.exp (-l * a + (s.card : ℝ) * v) := by
    refine measureReal_upperTailEvent_finset_sum_upperTruncation_le_exp_card_mul_of_iIndepFun_of_mgf_le_exp
      (μ := μ) (X := X) (s := s) (a := a) (l := l) (L := L) (v := v)
      h_indep h_meas hl ?_
    intro i hi
    exact mgf_upperTruncation_le_exp_of_isBigO_of_lintegral_tail_of_log_constraint
      (μ := μ) (Ψ := Ψ) (X := X i) (CΨ := CΨ) (l := l) (L := L) (M := M)
      (h_meas i) (h_int i hi) (h_mean i hi) hAdmissible hCΨ_nonneg hCΨ (hX i hi)
      hl hl1 hL hM (hconstraint i hi)
  calc
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a)
      ≤ μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) +
          (s.card : ℝ) * (Ψ L)⁻¹ := hsplit
    _ ≤ Real.exp (-l * a + (s.card : ℝ) * v) + (s.card : ℝ) * (Ψ L)⁻¹ := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left htrunc ((s.card : ℝ) * (Ψ L)⁻¹)
    _ = Real.exp
          (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * (1 + Real.exp 1 / 2 + M + CΨ))) +
          (s.card : ℝ) * (Ψ L)⁻¹ := by
          simp [v]

/-- Rounded generic heavy-tail concentration estimate with the cleaner
constant `3 + M + C_Ψ`. -/
theorem measureReal_upperTailEvent_finset_sum_le_exp_card_mul_add_card_mul_invPsi_of_iIndepFun_of_isBigO_of_integral_eq_zero_of_log_constraint_rounded
    [IsProbabilityMeasure μ]
    {Ψ : ℝ → ℝ} {X : ι → Ω → ℝ} {s : Finset ι} {a l L CΨ M : ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    (hAdmissible : AdmissiblePsi Ψ)
    (hCΨ_nonneg : 0 ≤ CΨ)
    (hCΨ :
      ∫⁻ t in Set.Ioi 1, ENNReal.ofReal (t / Ψ t) ∂volume ≤ ENNReal.ofReal CΨ)
    (hX : ∀ i ∈ s, IsBigO μ Ψ (X i) 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hconstraint : ∀ i ∈ s, ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 1 L →
      l * t ≤ Real.log (Ψ t) - 4 * Real.log t + Real.log M) :
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a) ≤
      Real.exp (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * (3 + M + CΨ))) +
        (s.card : ℝ) * (Ψ L)⁻¹ := by
  let v : ℝ := l ^ (2 : ℕ) * (3 + M + CΨ)
  have hX_with : ∀ i ∈ s, IsBigOWith μ Ψ (X i) 1 := by
    intro i hi
    exact IsBigOWith.of_le (μ := μ) (Ψ := Ψ) (X := fun ω => |X i ω|) (Y := X i) (A := 1)
      (by simpa [IsBigO] using hX i hi) (fun ω => le_abs_self (X i ω))
  have hsplit :=
    measureReal_upperTailEvent_finset_sum_le_upperTruncation_add_card_mul_of_isBigOWith
      (μ := μ) (Ψ := Ψ) (X := X) (s := s) (L := L) (a := a) hX_with hL
  have htrunc :
      μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) ≤
        Real.exp (-l * a + (s.card : ℝ) * v) := by
    refine measureReal_upperTailEvent_finset_sum_upperTruncation_le_exp_card_mul_of_iIndepFun_of_mgf_le_exp
      (μ := μ) (X := X) (s := s) (a := a) (l := l) (L := L) (v := v)
      h_indep h_meas hl ?_
    intro i hi
    exact mgf_upperTruncation_le_exp_of_isBigO_of_lintegral_tail_of_log_constraint_rounded
      (μ := μ) (Ψ := Ψ) (X := X i) (CΨ := CΨ) (l := l) (L := L) (M := M)
      (h_meas i) (h_int i hi) (h_mean i hi) hAdmissible hCΨ_nonneg hCΨ (hX i hi)
      hl hl1 hL hM (hconstraint i hi)
  calc
    μ.real (upperTailEvent (fun ω => ∑ i ∈ s, X i ω) a)
      ≤ μ.real (upperTailEvent (fun ω => ∑ i ∈ s, upperTruncation (X i) L ω) a) +
          (s.card : ℝ) * (Ψ L)⁻¹ := hsplit
    _ ≤ Real.exp (-l * a + (s.card : ℝ) * v) + (s.card : ℝ) * (Ψ L)⁻¹ := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left htrunc ((s.card : ℝ) * (Ψ L)⁻¹)
    _ = Real.exp (-l * a + (s.card : ℝ) * (l ^ (2 : ℕ) * (3 + M + CΨ))) +
          (s.card : ℝ) * (Ψ L)⁻¹ := by
          simp [v]

end

end IndependentSums

end Homogenization
