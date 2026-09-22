/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.Endpoint

/-! # Corollaries -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open Set
open scoped Topology

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

private theorem integrable_sum_abs_pow
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℕ}
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ) :
    Integrable (fun ω => ∑ i ∈ s, |X i ω| ^ p) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi hs =>
      have hi_int : Integrable (fun ω => |X i ω| ^ p) μ := hLp_int i (by simp)
      have hs_int : Integrable (fun ω => ∑ j ∈ s, |X j ω| ^ p) μ := by
        exact hs (fun j hj => hLp_int j (by simp [hj]))
      simpa [Finset.sum_insert, hi] using! hi_int.add hs_int

omit [MeasurableSpace Ω] in
private theorem sup'_abs_pow_le_sum_abs_pow
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (ω : Ω) :
    (s.sup' hs (fun i => |X i ω|)) ^ p ≤ ∑ i ∈ s, |X i ω| ^ p := by
  obtain ⟨i, hi, hi_le⟩ :
      ∃ i ∈ s, s.sup' hs (fun i => |X i ω|) ≤ |X i ω| := by
    simpa only [Finset.le_sup'_iff] using
      (show s.sup' hs (fun i => |X i ω|) ≤ s.sup' hs (fun i => |X i ω|) by exact le_rfl)
  have hi_ge : |X i ω| ≤ s.sup' hs (fun i => |X i ω|) := by
    exact Finset.le_sup' (f := fun j => |X j ω|) hi
  have hEq : s.sup' hs (fun i => |X i ω|) = |X i ω| := le_antisymm hi_le hi_ge
  calc
    (s.sup' hs (fun i => |X i ω|)) ^ p = |X i ω| ^ p := by rw [hEq]
    _ ≤ ∑ i ∈ s, |X i ω| ^ p := by
          exact Finset.single_le_sum (f := fun j => |X j ω| ^ p) (fun j hj => by positivity) hi

private theorem integrable_sup'_abs_pow_of_integrable_abs_pow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ) :
    Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ := by
  have hsum_int :
      Integrable (fun ω => ∑ i ∈ s, |X i ω| ^ p) μ :=
    integrable_sum_abs_pow (μ := μ) (X := X) (s := s) (p := p) hLp_int
  refine Integrable.mono' hsum_int ?_ ?_
  ·
    have hsup_meas : Measurable (fun ω => s.sup' hs (fun i => |X i ω|)) := by
      convert
        (Finset.measurable_sup' (s := s) (hs := hs) (f := fun i => abs ∘ X i)
          (fun i _ => continuous_abs.measurable.comp (h_meas i))) using 1
      ext ω
      simp [Function.comp_apply]
    exact (hsup_meas.pow_const p).aemeasurable.aestronglyMeasurable
  · filter_upwards with ω
    have hsup_base_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω|) := by
      exact le_trans (abs_nonneg _) (Finset.le_sup' (f := fun i => |X i ω|) hs.choose_spec)
    have hsup_nonneg : 0 ≤ (s.sup' hs (fun i => |X i ω|)) ^ p := by
      exact pow_nonneg hsup_base_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hsup_nonneg, abs_of_nonneg hsup_base_nonneg] using
      sup'_abs_pow_le_sum_abs_pow (X := X) (s := s) hs (p := p) ω

private theorem integral_sup'_abs_pow_le_sum_integral_abs_pow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ) :
    ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ ≤
      ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ := by
  have hsup_int :
      Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ :=
    integrable_sup'_abs_pow_of_integrable_abs_pow
      (μ := μ) (X := X) (s := s) hs (p := p) h_meas hLp_int
  have hsum_int :
      Integrable (fun ω => ∑ i ∈ s, |X i ω| ^ p) μ :=
    integrable_sum_abs_pow (μ := μ) (X := X) (s := s) (p := p) hLp_int
  calc
    ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ
        ≤ ∫ ω, ∑ i ∈ s, |X i ω| ^ p ∂μ := by
            refine integral_mono hsup_int hsum_int ?_
            intro ω
            exact sup'_abs_pow_le_sum_abs_pow (X := X) (s := s) hs (p := p) ω
    _ = ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ := by
          simpa using integral_finsetSum (μ := μ) s hLp_int

private theorem abs_le_one_add_abs_pow {x : ℝ} {p : ℕ} (hp : 1 ≤ p) :
    |x| ≤ 1 + |x| ^ p := by
  by_cases hx : |x| ≤ 1
  · have hpow_nonneg : 0 ≤ |x| ^ p := by positivity
    linarith
  · have h1 : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    have hpow : |x| ≤ |x| ^ p := by
      simpa [pow_one] using (pow_le_pow_right₀ h1 hp)
    have hpow_nonneg : 0 ≤ |x| ^ p := by positivity
    linarith

private theorem sq_le_one_add_abs_pow {x : ℝ} {p : ℕ} (hp : 2 ≤ p) :
    x ^ (2 : ℕ) ≤ 1 + |x| ^ p := by
  by_cases hx : |x| ≤ 1
  · have hsq : x ^ (2 : ℕ) ≤ 1 := by
      simpa [sq_abs] using (pow_le_pow_left₀ (abs_nonneg x) hx 2)
    have hpow_nonneg : 0 ≤ |x| ^ p := by positivity
    linarith
  · have h1 : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    have hsq : x ^ (2 : ℕ) ≤ |x| ^ p := by
      simpa [sq_abs] using (pow_le_pow_right₀ h1 hp)
    have hpow_nonneg : 0 ≤ |x| ^ p := by positivity
    linarith

private theorem integrable_of_integrable_abs_pow
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℕ}
    (hp : 1 ≤ p)
    (h_meas : Measurable X)
    (hLp_int : Integrable (fun ω => |X ω| ^ p) μ) :
    Integrable X μ := by
  have hdom : Integrable (fun ω => (1 : ℝ) + |X ω| ^ p) μ :=
    (integrable_const (1 : ℝ)).add hLp_int
  have habs_int : Integrable (fun ω => |X ω|) μ := by
    refine Integrable.mono' hdom ?_ ?_
    · exact (continuous_abs.measurable.comp h_meas).aemeasurable.aestronglyMeasurable
    · filter_upwards with ω
      simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] using
        abs_le_one_add_abs_pow (x := X ω) hp
  rw [← integrable_norm_iff h_meas.aestronglyMeasurable]
  simpa [Real.norm_eq_abs] using habs_int

private theorem integrable_sq_of_integrable_abs_pow
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (h_meas : Measurable X)
    (hLp_int : Integrable (fun ω => |X ω| ^ p) μ) :
    Integrable (fun ω => X ω ^ (2 : ℕ)) μ := by
  have hdom : Integrable (fun ω => (1 : ℝ) + |X ω| ^ p) μ :=
    (integrable_const (1 : ℝ)).add hLp_int
  have habs_sq_int : Integrable (fun ω => |X ω| ^ (2 : ℕ)) μ := by
    refine Integrable.mono' hdom ?_ ?_
    · exact
        (((continuous_abs.measurable.comp h_meas).pow_const 2).aemeasurable.aestronglyMeasurable)
    · filter_upwards with ω
      have hnonneg : 0 ≤ |X ω| ^ (2 : ℕ) := by positivity
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
        sq_le_one_add_abs_pow (x := X ω) hp
  simpa [sq_abs] using habs_sq_int

private theorem integral_abs_sq_rpow_half_le_integral_abs_pow_rpow_inv
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (h_meas : Measurable X)
    (hLp_int : Integrable (fun ω => |X ω| ^ p) μ) :
    (∫ ω, |X ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) ≤
      (∫ ω, |X ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
  have hp_ne_zero : p ≠ 0 := by omega
  have hX_ae : AEStronglyMeasurable X μ := h_meas.aestronglyMeasurable
  have h_memLp_p : MemLp X (p : ENNReal) μ := by
    rw [← integrable_norm_rpow_iff hX_ae (by exact_mod_cast hp_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hLp_int
  have h_memLp_two : MemLp X (2 : ENNReal) μ := by
    exact h_memLp_p.mono_exponent (by exact_mod_cast hp)
  have hcmp :
      eLpNorm X (2 : ENNReal) μ ≤ eLpNorm X (p : ENNReal) μ := by
    exact eLpNorm_le_eLpNorm_of_exponent_le
      (μ := μ) (f := X) (by exact_mod_cast hp)
  rw [h_memLp_two.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp),
    h_memLp_p.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hp_ne_zero) (by simp)] at hcmp
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (by
    simpa [Real.norm_eq_abs, one_div] using hcmp)

private theorem moment_two_le_sq_of_integral_abs_pow_rpow_inv_le
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (h_meas : Measurable X)
    (hLp_int : Integrable (fun ω => |X ω| ^ p) μ)
    {K : ℝ}
    (hK : (∫ ω, |X ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤ K) :
    ProbabilityTheory.moment X 2 μ ≤ K ^ 2 := by
  have hroot :
      (ProbabilityTheory.moment X 2 μ) ^ (1 / (2 : ℝ)) ≤ K := by
    have hLp :
        (∫ ω, |X ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) ≤
          (∫ ω, |X ω| ^ p ∂μ) ^ (1 / (p : ℝ)) :=
      integral_abs_sq_rpow_half_le_integral_abs_pow_rpow_inv
        (μ := μ) (X := X) hp h_meas hLp_int
    have hmoment_lp :
        (ProbabilityTheory.moment X 2 μ) ^ (1 / (2 : ℝ)) ≤
          (∫ ω, |X ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
      simpa [ProbabilityTheory.moment, sq_abs] using hLp
    exact hmoment_lp.trans hK
  have hmoment_nonneg : 0 ≤ ProbabilityTheory.moment X 2 μ := by
    simp [ProbabilityTheory.moment]
    positivity
  have hpow :
      ((ProbabilityTheory.moment X 2 μ) ^ (1 / (2 : ℝ))) ^ (2 : ℕ) ≤ K ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hroot 2
  have hmoment_eq :
      ((ProbabilityTheory.moment X 2 μ) ^ (1 / (2 : ℝ))) ^ (2 : ℕ) =
        ProbabilityTheory.moment X 2 μ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmoment_nonneg]
    norm_num
  exact hmoment_eq ▸ hpow

private theorem integral_sum_abs_pow_rpow_inv_le_card_rpow_mul
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℕ}
    (hp : 1 ≤ p)
    {K : ℝ} (hK_nonneg : 0 ≤ K)
    (hK : ∀ i ∈ s, (∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤ K) :
    (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      (s.card : ℝ) ^ (1 / (p : ℝ)) * K := by
  have hp_ne_zero : p ≠ 0 := by omega
  have hsum_le :
      ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ ≤ (s.card : ℝ) * K ^ p := by
    calc
      ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ ≤ ∑ i ∈ s, K ^ p := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hroot := hK i hi
        have hroot_nonneg : 0 ≤ (∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by positivity
        have hpow : ((∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ))) ^ p ≤ K ^ p := by
          exact pow_le_pow_left₀ hroot_nonneg hroot p
        have hint_nonneg : 0 ≤ ∫ ω, |X i ω| ^ p ∂μ := by positivity
        have hint_eq :
            ((∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ))) ^ p =
              ∫ ω, |X i ω| ^ p ∂μ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hint_nonneg, one_div,
            inv_mul_cancel₀ (show (p : ℝ) ≠ 0 by exact_mod_cast hp_ne_zero), Real.rpow_one]
        exact hint_eq ▸ hpow
      _ = (s.card : ℝ) * K ^ p := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ := by
    refine Finset.sum_nonneg ?_
    intro i hi
    positivity
  have hroot :
      (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
        ((s.card : ℝ) * K ^ p) ^ (1 / (p : ℝ)) := by
    exact Real.rpow_le_rpow hsum_nonneg hsum_le (by positivity)
  have htarget_eq :
      ((s.card : ℝ) * K ^ p) ^ (1 / (p : ℝ)) =
        (s.card : ℝ) ^ (1 / (p : ℝ)) * K := by
    rw [one_div, Real.mul_rpow (by positivity) (pow_nonneg hK_nonneg _),
      Real.pow_rpow_inv_natCast hK_nonneg hp_ne_zero]
  exact hroot.trans_eq htarget_eq

private theorem sum_moment_two_le_card_mul_sq_of_integral_abs_pow_rpow_inv_le
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℕ}
    (hp : 2 ≤ p)
    (h_meas : ∀ i, Measurable (X i))
    {K : ℝ}
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ)
    (hK : ∀ i ∈ s, (∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤ K) :
    ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ ≤ (s.card : ℝ) * K ^ 2 := by
  calc
    ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ ≤ ∑ i ∈ s, K ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact moment_two_le_sq_of_integral_abs_pow_rpow_inv_le
        (μ := μ) (X := X i) hp (h_meas i) (hLp_int i hi) (hK i hi)
    _ = (s.card : ℝ) * K ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- Note-facing polynomial-moment Rosenthal bound with the maximal term
replaced by the sum of the individual `L^p` moments. -/
theorem integral_abs_centeredFinsetSum_pow_rpow_inv_le_rosenthal_polynomial
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ) :
    (∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      2 * (p : ℝ) * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
  have hp_one : 1 ≤ p := by omega
  have h_int : ∀ i ∈ s, Integrable (X i) μ := by
    intro i hi
    exact integrable_of_integrable_abs_pow
      (μ := μ) (X := X i) hp_one (h_meas i) (hLp_int i hi)
  have h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ := by
    intro i hi
    exact integrable_sq_of_integrable_abs_pow
      (μ := μ) (X := X i) hp (h_meas i) (hLp_int i hi)
  have hbase :
      (∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
        2 * (p : ℝ) * (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ (1 / (p : ℝ)) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
    exact integral_abs_centeredFinsetSum_pow_rpow_inv_le_rosenthal
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_int h_sq_int
      (integrable_sup'_abs_pow_of_integrable_abs_pow
        (μ := μ) (X := X) (s := s) hs (p := p) h_meas hLp_int)
  have hsup_le :
      ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ ≤
        ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ := by
    exact integral_sup'_abs_pow_le_sum_integral_abs_pow
      (μ := μ) (X := X) (s := s) hs (p := p) h_meas hLp_int
  have hsup_nonneg : 0 ≤ ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
    refine integral_nonneg ?_
    intro ω
    have hsup_base_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω|) := by
      exact le_trans (abs_nonneg _) (Finset.le_sup' (f := fun i => |X i ω|) hs.choose_spec)
    exact pow_nonneg hsup_base_nonneg _
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ := by
    refine Finset.sum_nonneg ?_
    intro i hi
    positivity
  have hsup_root_le :
      (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
        (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
    exact Real.rpow_le_rpow hsup_nonneg hsup_le (by positivity)
  calc
    (∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ) ^ (1 / (p : ℝ))
        ≤ 2 * (p : ℝ) * (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ (1 / (p : ℝ)) +
            4 * rosenthalBennettIntegralConst *
              (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := hbase
    _ ≤ 2 * (p : ℝ) * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
          refine add_le_add ?_ le_rfl
          exact mul_le_mul_of_nonneg_left hsup_root_le (by positivity)

/-- Rosenthal's polynomial-moment corollary for finite sums of centered
independent real random variables. -/
theorem integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_polynomial_of_iIndepFun_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ)
    (hXmean : ∀ i ∈ s, μ[X i] = 0) :
    (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      2 * (p : ℝ) * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
  have hcenter_eq : centeredFinsetSum X μ s = fun ω => ∑ i ∈ s, X i ω := by
    have hmean_sum : ∑ i ∈ s, μ[X i] = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      exact hXmean i hi
    funext ω
    rw [centeredFinsetSum, Finset.sum_sub_distrib, hmean_sum, sub_zero]
  simpa [hcenter_eq] using
    integral_abs_centeredFinsetSum_pow_rpow_inv_le_rosenthal_polynomial
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas hLp_int

/-- Uniform-`K` polynomial-moment Rosenthal corollary in the note-facing
finite-sum form. -/
theorem integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ} {K : ℝ}
    (hp : 2 ≤ p)
    (hK_nonneg : 0 ≤ K)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ)
    (hXmean : ∀ i ∈ s, μ[X i] = 0)
    (hK : ∀ i ∈ s, (∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤ K) :
    (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      2 * (p : ℝ) * ((s.card : ℝ) ^ (1 / (p : ℝ)) * K) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * (Real.sqrt (s.card : ℝ) * K)) := by
  have hpoly :
      (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
        2 * (p : ℝ) * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
    exact integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_polynomial_of_iIndepFun_of_integral_eq_zero
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas hLp_int hXmean
  have hLp_sum :
      (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
        (s.card : ℝ) ^ (1 / (p : ℝ)) * K := by
    exact integral_sum_abs_pow_rpow_inv_le_card_rpow_mul
      (μ := μ) (X := X) (s := s) (p := p) (by omega) hK_nonneg hK
  have hmoment_sum :
      ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ ≤ (s.card : ℝ) * K ^ 2 := by
    exact sum_moment_two_le_card_mul_sq_of_integral_abs_pow_rpow_inv_le
      (μ := μ) (X := X) (s := s) (p := p) hp h_meas hLp_int hK
  have hsqrt_sum_le :
      Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) ≤
        Real.sqrt (s.card : ℝ) * K := by
    have hsqrt :
        Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) ≤
          Real.sqrt ((s.card : ℝ) * K ^ 2) := by
      exact Real.sqrt_le_sqrt hmoment_sum
    have hsqrt_eq :
        Real.sqrt ((s.card : ℝ) * K ^ 2) = Real.sqrt (s.card : ℝ) * K := by
      rw [Real.sqrt_mul (by positivity) (K ^ 2), Real.sqrt_sq hK_nonneg]
    exact hsqrt.trans_eq hsqrt_eq
  calc
    (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ (1 / (p : ℝ))
        ≤ 2 * (p : ℝ) * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) +
            4 * rosenthalBennettIntegralConst *
              (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := hpoly
    _ ≤ 2 * (p : ℝ) * ((s.card : ℝ) ^ (1 / (p : ℝ)) * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * (Real.sqrt (s.card : ℝ) * K)) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hLp_sum (by positivity)
          · refine mul_le_mul_of_nonneg_left ?_ ?_
            · exact mul_le_mul_of_nonneg_left hsqrt_sum_le (by positivity)
            ·
              have hRB_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
                dsimp [rosenthalBennettIntegralConst]
                positivity
              positivity

private theorem integrable_sum_abs_rpow
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℝ}
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ) :
    Integrable (fun ω => ∑ i ∈ s, |X i ω| ^ p) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
      have hi_int : Integrable (fun ω => |X i ω| ^ p) μ := hLp_int i (by simp)
      have hs_int : Integrable (fun ω => ∑ j ∈ s, |X j ω| ^ p) μ := by
        exact hs (fun j hj => hLp_int j (by simp [hj]))
      simpa [Finset.sum_insert, hi] using! hi_int.add hs_int

omit [MeasurableSpace Ω] in
private theorem sup'_abs_rpow_le_sum_abs_rpow
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (ω : Ω) :
    (s.sup' hs (fun i => |X i ω|)) ^ p ≤ ∑ i ∈ s, |X i ω| ^ p := by
  obtain ⟨i, hi, hi_le⟩ :
      ∃ i ∈ s, s.sup' hs (fun i => |X i ω|) ≤ |X i ω| := by
    simpa only [Finset.le_sup'_iff] using
      (show s.sup' hs (fun i => |X i ω|) ≤ s.sup' hs (fun i => |X i ω|) by exact le_rfl)
  have hi_ge : |X i ω| ≤ s.sup' hs (fun i => |X i ω|) := by
    exact Finset.le_sup' (f := fun j => |X j ω|) hi
  have hEq : s.sup' hs (fun i => |X i ω|) = |X i ω| := le_antisymm hi_le hi_ge
  calc
    (s.sup' hs (fun i => |X i ω|)) ^ p = |X i ω| ^ p := by rw [hEq]
    _ ≤ ∑ i ∈ s, |X i ω| ^ p := by
      exact Finset.single_le_sum (f := fun j => |X j ω| ^ p)
        (fun j hj => Real.rpow_nonneg (abs_nonneg _) _) hi

private theorem integrable_sup'_abs_rpow_of_integrable_abs_rpow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 0 ≤ p) (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ) :
    Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ := by
  have hsum_int : Integrable (fun ω => ∑ i ∈ s, |X i ω| ^ p) μ :=
    integrable_sum_abs_rpow (μ := μ) (X := X) (s := s) (p := p) hLp_int
  refine Integrable.mono' hsum_int ?_ ?_
  · have hsup_meas : Measurable (fun ω => s.sup' hs (fun i => |X i ω|)) := by
      convert
        (Finset.measurable_sup' (s := s) (hs := hs) (f := fun i => abs ∘ X i)
          (fun i _ => continuous_abs.measurable.comp (h_meas i))) using 1
      ext ω
      simp [Function.comp_apply]
    exact ((Real.continuous_rpow_const hp).measurable.comp hsup_meas).aemeasurable.aestronglyMeasurable
  · filter_upwards with ω
    have hsup_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω|) := by
      exact le_trans (abs_nonneg _) (Finset.le_sup' (f := fun i => |X i ω|) hs.choose_spec)
    have hrpow_nonneg : 0 ≤ (s.sup' hs (fun i => |X i ω|)) ^ p :=
      Real.rpow_nonneg hsup_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hrpow_nonneg] using
      sup'_abs_rpow_le_sum_abs_rpow (X := X) (s := s) hs ω

private theorem integral_sup'_abs_rpow_le_sum_integral_abs_rpow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 0 ≤ p) (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ) :
    ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ ≤
      ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ := by
  have hsup_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ :=
    integrable_sup'_abs_rpow_of_integrable_abs_rpow
      (μ := μ) (X := X) (s := s) hs hp h_meas hLp_int
  have hsum_int : Integrable (fun ω => ∑ i ∈ s, |X i ω| ^ p) μ :=
    integrable_sum_abs_rpow (μ := μ) (X := X) (s := s) (p := p) hLp_int
  calc
    ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ
        ≤ ∫ ω, ∑ i ∈ s, |X i ω| ^ p ∂μ := by
            refine integral_mono hsup_int hsum_int ?_
            intro ω
            exact sup'_abs_rpow_le_sum_abs_rpow (X := X) (s := s) hs ω
    _ = ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ := by
          simpa using integral_finsetSum (μ := μ) s hLp_int

private theorem memLp_of_integrable_abs_rpow
    {X : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (h_meas : Measurable X)
    (hLp_int : Integrable (fun ω => |X ω| ^ p) μ) :
    MemLp X (ENNReal.ofReal p) μ := by
  rw [← integrable_norm_rpow_iff h_meas.aestronglyMeasurable
    (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hp]) ENNReal.ofReal_ne_top]
  simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le] using hLp_int

private theorem integrable_of_integrable_abs_rpow
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (h_meas : Measurable X)
    (hLp_int : Integrable (fun ω => |X ω| ^ p) μ) :
    Integrable X μ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h_memLp : MemLp X (ENNReal.ofReal p) μ :=
    memLp_of_integrable_abs_rpow (μ := μ) hp_pos h_meas hLp_int
  refine h_memLp.integrable ?_
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hp

private theorem integrable_sq_of_integrable_abs_rpow
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℝ} (hp : 2 ≤ p)
    (h_meas : Measurable X)
    (hLp_int : Integrable (fun ω => |X ω| ^ p) μ) :
    Integrable (fun ω => X ω ^ (2 : ℕ)) μ := by
  have hp_pos : 0 < p := by linarith
  have h_memLp_p : MemLp X (ENNReal.ofReal p) μ :=
    memLp_of_integrable_abs_rpow (μ := μ) hp_pos h_meas hLp_int
  have h_memLp_two : MemLp X (2 : ENNReal) μ := by
    apply h_memLp_p.mono_exponent
    calc
      (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp
  have htwo_int := h_memLp_two.integrable_norm_rpow (by norm_num) (by simp)
  simpa [Real.norm_eq_abs, Real.rpow_natCast, sq_abs] using htwo_int

private theorem integral_abs_sq_rpow_half_le_integral_abs_rpow_rpow_inv
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℝ} (hp : 2 ≤ p)
    (h_meas : Measurable X)
    (hLp_int : Integrable (fun ω => |X ω| ^ p) μ) :
    (∫ ω, |X ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) ≤
      (∫ ω, |X ω| ^ p ∂μ) ^ p⁻¹ := by
  have hp_pos : 0 < p := by linarith
  have h_memLp_p : MemLp X (ENNReal.ofReal p) μ :=
    memLp_of_integrable_abs_rpow (μ := μ) hp_pos h_meas hLp_int
  have h_memLp_two : MemLp X (2 : ENNReal) μ := by
    apply h_memLp_p.mono_exponent
    calc
      (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp
  have hcmp : eLpNorm X (2 : ENNReal) μ ≤ eLpNorm X (ENNReal.ofReal p) μ :=
    eLpNorm_le_eLpNorm_of_exponent_le
      (μ := μ) (f := X) (by
        calc
          (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
          _ ≤ ENNReal.ofReal p := ENNReal.ofReal_le_ofReal hp)
  rw [h_memLp_two.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp),
    h_memLp_p.eLpNorm_eq_integral_rpow_norm
      (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hp_pos]) ENNReal.ofReal_ne_top] at hcmp
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (by
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le, one_div] using hcmp)

private theorem moment_two_le_sq_of_integral_abs_rpow_rpow_inv_le
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {p : ℝ} (hp : 2 ≤ p)
    (h_meas : Measurable X)
    (hLp_int : Integrable (fun ω => |X ω| ^ p) μ)
    {K : ℝ} (hK : (∫ ω, |X ω| ^ p ∂μ) ^ p⁻¹ ≤ K) :
    ProbabilityTheory.moment X 2 μ ≤ K ^ 2 := by
  have hroot : (ProbabilityTheory.moment X 2 μ) ^ (1 / (2 : ℝ)) ≤ K := by
    have hLp := integral_abs_sq_rpow_half_le_integral_abs_rpow_rpow_inv
      (μ := μ) (X := X) hp h_meas hLp_int
    have hmoment_lp :
        (ProbabilityTheory.moment X 2 μ) ^ (1 / (2 : ℝ)) ≤
          (∫ ω, |X ω| ^ p ∂μ) ^ p⁻¹ := by
      simpa [ProbabilityTheory.moment, sq_abs] using hLp
    exact hmoment_lp.trans hK
  have hmoment_nonneg : 0 ≤ ProbabilityTheory.moment X 2 μ := by
    simp [ProbabilityTheory.moment]
    positivity
  have hpow : ((ProbabilityTheory.moment X 2 μ) ^ (1 / (2 : ℝ))) ^ (2 : ℕ) ≤ K ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hroot 2
  have hmoment_eq :
      ((ProbabilityTheory.moment X 2 μ) ^ (1 / (2 : ℝ))) ^ (2 : ℕ) =
        ProbabilityTheory.moment X 2 μ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hmoment_nonneg]
    norm_num
  exact hmoment_eq ▸ hpow

private theorem integral_sum_abs_rpow_rpow_inv_le_card_rpow_mul
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℝ} (hp : 1 ≤ p)
    {K : ℝ} (hK_nonneg : 0 ≤ K)
    (hK : ∀ i ∈ s, (∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ ≤ K) :
    (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ ≤
      (s.card : ℝ) ^ p⁻¹ * K := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hsum_le :
      ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ ≤ (s.card : ℝ) * K ^ p := by
    calc
      ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ ≤ ∑ i ∈ s, K ^ p := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hroot := hK i hi
        have hroot_nonneg : 0 ≤ (∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ := by positivity
        have hpow : ((∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹) ^ p ≤ K ^ p :=
          Real.rpow_le_rpow hroot_nonneg hroot hp_pos.le
        have hint_nonneg : 0 ≤ ∫ ω, |X i ω| ^ p ∂μ := by positivity
        simpa [one_div] using (Real.rpow_inv_rpow hint_nonneg hp_pos.ne') ▸ hpow
      _ = (s.card : ℝ) * K ^ p := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ := by
    refine Finset.sum_nonneg ?_
    intro i hi
    positivity
  have hroot := Real.rpow_le_rpow hsum_nonneg hsum_le (by positivity : 0 ≤ p⁻¹)
  have htarget_eq : ((s.card : ℝ) * K ^ p) ^ p⁻¹ = (s.card : ℝ) ^ p⁻¹ * K := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hK_nonneg _),
      ← Real.rpow_mul hK_nonneg]
    field_simp
    simp
  exact hroot.trans_eq htarget_eq

private theorem sum_moment_two_le_card_mul_sq_of_integral_abs_rpow_rpow_inv_le
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℝ} (hp : 2 ≤ p)
    (h_meas : ∀ i, Measurable (X i))
    {K : ℝ} (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ)
    (hK : ∀ i ∈ s, (∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ ≤ K) :
    ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ ≤ (s.card : ℝ) * K ^ 2 := by
  calc
    ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ ≤ ∑ i ∈ s, K ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact moment_two_le_sq_of_integral_abs_rpow_rpow_inv_le
        (μ := μ) (X := X i) hp (h_meas i) (hLp_int i hi) (hK i hi)
    _ = (s.card : ℝ) * K ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Real-exponent polynomial-moment Rosenthal bound with the maximal term
replaced by the sum of the individual `L^p` moments. -/
theorem integral_abs_centeredFinsetSum_rpow_rpow_inv_le_rosenthal_polynomial
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ) :
    (∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ) ^ p⁻¹ ≤
      2 * p * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp_one
  have h_int : ∀ i ∈ s, Integrable (X i) μ := by
    intro i hi
    exact integrable_of_integrable_abs_rpow
      (μ := μ) (X := X i) hp_one (h_meas i) (hLp_int i hi)
  have h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ := by
    intro i hi
    exact integrable_sq_of_integrable_abs_rpow
      (μ := μ) (X := X i) hp (h_meas i) (hLp_int i hi)
  have hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ :=
    integrable_sup'_abs_rpow_of_integrable_abs_rpow
      (μ := μ) (X := X) (s := s) hs hp_nonneg h_meas hLp_int
  have hbase :
      (∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ) ^ p⁻¹ ≤
        2 * p * (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
    simpa [one_div] using
      integral_abs_centeredFinsetSum_rpow_rpow_inv_le_rosenthal
        (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_int h_sq_int hmax_int
  have hsup_le :
      ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ ≤
        ∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ :=
    integral_sup'_abs_rpow_le_sum_integral_abs_rpow
      (μ := μ) (X := X) (s := s) hs hp_nonneg h_meas hLp_int
  have hsup_nonneg : 0 ≤ ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
    refine integral_nonneg fun ω => ?_
    have hsup_nonneg : 0 ≤ s.sup' hs (fun i => |X i ω|) := by
      exact le_trans (abs_nonneg _) (Finset.le_sup' (f := fun i => |X i ω|) hs.choose_spec)
    exact Real.rpow_nonneg hsup_nonneg _
  have hsup_root_le :
      (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ p⁻¹ ≤
        (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ := by
    exact Real.rpow_le_rpow hsup_nonneg hsup_le (by positivity)
  calc
    (∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ) ^ p⁻¹
        ≤ 2 * p * (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ p⁻¹ +
            4 * rosenthalBennettIntegralConst *
              (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := hbase
    _ ≤ 2 * p * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
      refine add_le_add ?_ le_rfl
      exact mul_le_mul_of_nonneg_left hsup_root_le (by positivity)

/-- Real-exponent Rosenthal polynomial-moment corollary for centered
independent finite sums. -/
theorem integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_polynomial_of_iIndepFun_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ)
    (hXmean : ∀ i ∈ s, μ[X i] = 0) :
    (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ p⁻¹ ≤
      2 * p * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
  have hcenter_eq : centeredFinsetSum X μ s = fun ω => ∑ i ∈ s, X i ω := by
    have hmean_sum : ∑ i ∈ s, μ[X i] = 0 := by
      refine Finset.sum_eq_zero fun i hi => hXmean i hi
    funext ω
    rw [centeredFinsetSum, Finset.sum_sub_distrib, hmean_sum, sub_zero]
  simpa [hcenter_eq] using
    integral_abs_centeredFinsetSum_rpow_rpow_inv_le_rosenthal_polynomial
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas hLp_int

/-- Uniform real-exponent polynomial-moment Rosenthal corollary in the
finite-sum form. -/
theorem integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p K : ℝ}
    (hp : 2 ≤ p)
    (hK_nonneg : 0 ≤ K)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ p) μ)
    (hXmean : ∀ i ∈ s, μ[X i] = 0)
    (hK : ∀ i ∈ s, (∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ ≤ K) :
    (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ p⁻¹ ≤
      2 * p * ((s.card : ℝ) ^ p⁻¹ * K) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * (Real.sqrt (s.card : ℝ) * K)) := by
  have hpoly :
      (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ p⁻¹ ≤
        2 * p * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) :=
    integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_polynomial_of_iIndepFun_of_integral_eq_zero
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas hLp_int hXmean
  have hLp_sum :
      (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ ≤ (s.card : ℝ) ^ p⁻¹ * K :=
    integral_sum_abs_rpow_rpow_inv_le_card_rpow_mul
      (μ := μ) (X := X) (s := s) (p := p) (le_trans (by norm_num) hp) hK_nonneg hK
  have hmoment_sum :
      ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ ≤ (s.card : ℝ) * K ^ 2 :=
    sum_moment_two_le_card_mul_sq_of_integral_abs_rpow_rpow_inv_le
      (μ := μ) (X := X) (s := s) (p := p) hp h_meas hLp_int hK
  have hsqrt_sum_le :
      Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) ≤
        Real.sqrt (s.card : ℝ) * K := by
    have hsqrt := Real.sqrt_le_sqrt hmoment_sum
    have hsqrt_eq : Real.sqrt ((s.card : ℝ) * K ^ 2) = Real.sqrt (s.card : ℝ) * K := by
      rw [Real.sqrt_mul (by positivity) (K ^ 2), Real.sqrt_sq hK_nonneg]
    exact hsqrt.trans_eq hsqrt_eq
  calc
    (∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ) ^ p⁻¹
        ≤ 2 * p * (∑ i ∈ s, ∫ ω, |X i ω| ^ p ∂μ) ^ p⁻¹ +
            4 * rosenthalBennettIntegralConst *
              (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := hpoly
    _ ≤ 2 * p * ((s.card : ℝ) ^ p⁻¹ * K) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * (Real.sqrt (s.card : ℝ) * K)) := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul_of_nonneg_left hLp_sum (by positivity)
      · refine mul_le_mul_of_nonneg_left ?_ ?_
        · exact mul_le_mul_of_nonneg_left hsqrt_sum_le (by positivity)
        · have hRB_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
            dsimp [rosenthalBennettIntegralConst]
            positivity
          positivity

end
end IndependentSums
end Homogenization
