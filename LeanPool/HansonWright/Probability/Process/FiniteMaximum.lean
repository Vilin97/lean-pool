/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import LeanPool.HansonWright.Probability.Moments.Exponential

/-!
# Finite Maxima of Sub-Gaussian Variables

Deterministic soft-max inequalities and the expected maximum bound for a finite sub-Gaussian
family.

## Main definitions

This module introduces no new definitions.

## Main results

* `abs_sup'_le_sum`: absolute supremum bounded by a finite sum.
* `expected_max_subGaussian`: expected maximum of a finite sub-Gaussian family.
-/

namespace LeanPool

open MeasureTheory Set Real Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Union bound for maximum over finset: P(max_i X_i ≥ u) ≤ Σ_i P(X_i ≥ u). -/
theorem measure_finset_sup_ge_le_sum {ι : Type*} {μ : Measure Ω}
    {X : ι → Ω → ℝ} {u : ℝ} {s : Finset ι} (hs : s.Nonempty) :
    μ {ω | u ≤ s.sup' hs (fun i => X i ω)} ≤ ∑ i ∈ s, μ {ω | u ≤ X i ω} := by
  -- {ω | u ≤ sup_i X_i ω} ⊆ ⋃_i {ω | u ≤ X_i ω}
  have h_subset : {ω | u ≤ s.sup' hs (fun i => X i ω)} ⊆ ⋃ i ∈ s, {ω | u ≤ X i ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    rw [mem_iUnion₂]
    by_contra h_neg
    push Not at h_neg
    have h_bound : ∀ i ∈ s, X i ω < u := by
      intro i hi
      simp only [mem_ofPred_eq, not_le] at h_neg
      exact h_neg i hi
    have h_sup_lt : s.sup' hs (fun i => X i ω) < u := by
      rw [Finset.sup'_lt_iff]
      exact h_bound
    exact absurd hω (not_le.mpr h_sup_lt)
  calc μ {ω | u ≤ s.sup' hs (fun i => X i ω)}
    _ ≤ μ (⋃ i ∈ s, {ω | u ≤ X i ω}) := measure_mono h_subset
    _ ≤ ∑ i ∈ s, μ {ω | u ≤ X i ω} := measure_biUnion_finset_le s _

/-!
## MGF-Based Bounds for Expected Maximum
-/

/-- Scaled soft-max: `exp(t · sup' f) ≤ ∑ exp(t · fᵢ)`. -/
theorem exp_mul_sup'_le_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) :
    exp (t * s.sup' hs f) ≤ ∑ i ∈ s, exp (t * f i) := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' hs f
  rw [hmax]
  apply Finset.single_le_sum _ hj
  intro i _
  exact (exp_pos _).le

/-- Soft-max bound: `exp(sup' f) ≤ ∑ exp(fᵢ)`. -/
theorem exp_sup'_le_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    exp (s.sup' hs f) ≤ ∑ i ∈ s, exp (f i) := by
  simpa using exp_mul_sup'_le_sum hs f 1

/-- Bound `|sup' f| ≤ ∑ |fᵢ|` for finite sets. -/
theorem abs_sup'_le_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    |s.sup' hs f| ≤ ∑ i ∈ s, |f i| := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' hs f
  rw [hmax]
  apply Finset.single_le_sum _ hj
  intro i _
  exact abs_nonneg _

/-- Upper bound `sup' f ≤ ∑ |fᵢ|` for finite sets. -/
lemma sup'_le_sum_abs {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → ℝ} :
    s.sup' hs f ≤ ∑ i ∈ s, |f i| :=
  (le_abs_self _).trans (abs_sup'_le_sum hs f)

/-- Expected maximum over finset of sub-Gaussian random variables via MGF method.
    E[max_i X_i] ≤ σ · √(2 log n) where n = |s|. -/
theorem expected_max_subGaussian {ι : Type*}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {s : Finset ι} (hs : s.Nonempty) (hs_card : 2 ≤ s.card)
    (hX_int_basic : ∀ i ∈ s, Integrable (X i) μ)
    (hX_sgb : ∀ i ∈ s, ∀ t, ProbabilityTheory.cgf (X i) μ t ≤ t ^ 2 * σ ^ 2 / 2)
    (hX_int_exp : ∀ i ∈ s, ∀ t, Integrable (fun ω => exp (t * X i ω)) μ) :
    ∫ ω, s.sup' hs (fun i => X i ω) ∂μ ≤ σ * sqrt (2 * log s.card) := by
  -- Setup: n = |s|, t_opt = √(2 log n) / σ
  set n := s.card with hn_def
  have hn_pos : 0 < n := Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hs_card
  have hn_ge2 : 2 ≤ n := hs_card
  have hlogn_pos : 0 < log n := log_pos (by exact_mod_cast hn_ge2)
  set t_opt := sqrt (2 * log n) / σ with ht_def
  have ht_pos : 0 < t_opt := div_pos (sqrt_pos.mpr (by positivity)) hσ
  -- Algebraic identity: (1/t_opt) * (log n + t_opt²σ²/2) = σ√(2 log n)
  have h_algebra : (1 / t_opt) * (log n + t_opt ^ 2 * σ ^ 2 / 2) =
      σ * sqrt (2 * log n) := by
    rw [ht_def]
    have h1 : (sqrt (2 * log n) / σ) ^ 2 = (2 * log n) / σ ^ 2 := by
      rw [div_pow, sq_sqrt (by positivity : 0 ≤ 2 * log n)]
    calc (1 / (sqrt (2 * log n) / σ)) *
          (log n + (sqrt (2 * log n) / σ) ^ 2 * σ ^ 2 / 2)
      _ = (σ / sqrt (2 * log n)) * (log n + (2 * log n) / σ ^ 2 * σ ^ 2 / 2) := by
          rw [one_div, inv_div, h1]
      _ = (σ / sqrt (2 * log n)) * (log n + log n) := by
          congr 1
          field_simp
      _ = (σ / sqrt (2 * log n)) * (2 * log n) := by ring
      _ = σ * (2 * log n / sqrt (2 * log n)) := by ring
      _ = σ * sqrt (2 * log n) := by
          congr 1
          have h2logn_pos : 0 < 2 * log n := by positivity
          have h2logn_nonneg : 0 ≤ 2 * log n := le_of_lt h2logn_pos
          rw [div_eq_iff (sqrt_ne_zero'.mpr h2logn_pos)]
          exact (mul_self_sqrt h2logn_nonneg).symm
  -- Step 1: Integrability of sup'
  have hsup_int : Integrable (fun ω => s.sup' hs (fun i => X i ω)) μ := by
    refine Integrable.mono (integrable_finsetSum s (fun i hi => (hX_int_basic i hi).abs)) ?_ ?_
    · rw [aestronglyMeasurable_iff_aemeasurable]
      convert Finset.sup'_induction (p := fun f : Ω → ℝ => AEMeasurable f μ)
        hs _ (fun _ hf _ hg => hf.sup hg)
        (fun i hi => aestronglyMeasurable_iff_aemeasurable.mp
          (hX_int_basic i hi).aestronglyMeasurable) using 1
      funext ω
      simp only [Finset.sup'_apply]
    · refine ae_of_all μ (fun ω => ?_)
      simp only [Real.norm_eq_abs]
      have h_sum_nonneg : 0 ≤ ∑ i ∈ s, |X i ω| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
      rw [abs_of_nonneg h_sum_nonneg]
      convert abs_sup'_le_sum hs (fun i => X i ω) using 2
  -- Step 2: MGF bound E[exp(t·Xᵢ)] ≤ exp(t²σ²/2)
  have hMGF_bound : ∀ i ∈ s,
      ∫ ω, exp (t_opt * X i ω) ∂μ ≤ exp (t_opt ^ 2 * σ ^ 2 / 2) := by
    intro i hi
    have hcgf := hX_sgb i hi t_opt
    unfold ProbabilityTheory.cgf at hcgf
    have h_exp_bound := exp_le_exp.mpr hcgf
    unfold ProbabilityTheory.mgf at h_exp_bound
    simp only [exp_log (integral_exp_pos (hX_int_exp i hi t_opt))] at h_exp_bound
    exact h_exp_bound
  -- Step 3: Sum bound via soft-max
  have hsum_int : Integrable (fun ω => ∑ i ∈ s, exp (t_opt * X i ω)) μ :=
    integrable_finsetSum s (fun i hi => hX_int_exp i hi t_opt)
  have hsup_exp_bound : ∫ ω, exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ ≤
      n * exp (t_opt ^ 2 * σ ^ 2 / 2) := by
    calc ∫ ω, exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ
      _ ≤ ∫ ω, ∑ i ∈ s, exp (t_opt * X i ω) ∂μ := by
          apply integral_mono_of_nonneg
          · exact ae_of_all μ (fun ω => (exp_pos _).le)
          · exact hsum_int
          · exact ae_of_all μ (fun ω => exp_mul_sup'_le_sum hs (fun i => X i ω) t_opt)
      _ = ∑ i ∈ s, ∫ ω, exp (t_opt * X i ω) ∂μ :=
        integral_finsetSum s (fun i hi => hX_int_exp i hi t_opt)
      _ ≤ ∑ i ∈ s, exp (t_opt ^ 2 * σ ^ 2 / 2) :=
        Finset.sum_le_sum (fun i hi => hMGF_bound i hi)
      _ = n * exp (t_opt ^ 2 * σ ^ 2 / 2) := by simp [Finset.sum_const, hn_def]
  -- Step 4: Integrability of exp(t·sup')
  have hsup_exp_int : Integrable (fun ω => exp (t_opt * s.sup' hs (fun i => X i ω))) μ := by
    apply Integrable.mono' hsum_int
    · rw [aestronglyMeasurable_iff_aemeasurable]
      exact (aestronglyMeasurable_iff_aemeasurable.mp
        (hsup_int.const_mul t_opt).aestronglyMeasurable).exp
    · refine ae_of_all μ (fun ω => ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos (exp_pos _)]
      exact exp_mul_sup'_le_sum hs (fun i => X i ω) t_opt
  have hsup_exp_pos : 0 < ∫ ω, exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ :=
    integral_exp_pos hsup_exp_int
  have h_MGF_chain := mean_le_log_mgf hsup_int ht_pos hsup_exp_int
  -- Step 5: Log bound
  have hlog_bound : log (∫ ω, exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ) ≤
      log n + t_opt ^ 2 * σ ^ 2 / 2 := by
    calc log (∫ ω, exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ)
      _ ≤ log (n * exp (t_opt ^ 2 * σ ^ 2 / 2)) :=
        log_le_log hsup_exp_pos hsup_exp_bound
      _ = log n + log (exp (t_opt ^ 2 * σ ^ 2 / 2)) := by
          rw [log_mul (by exact_mod_cast hn_pos.ne') (exp_pos _).ne']
      _ = log n + t_opt ^ 2 * σ ^ 2 / 2 := by rw [log_exp]
  -- Step 6: Combine to get the final bound
  calc ∫ ω, s.sup' hs (fun i => X i ω) ∂μ
    _ ≤ (1 / t_opt) * log (∫ ω, exp (t_opt * s.sup' hs (fun i => X i ω)) ∂μ) :=
      h_MGF_chain
    _ ≤ (1 / t_opt) * (log n + t_opt ^ 2 * σ ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left hlog_bound
        exact le_of_lt (one_div_pos.mpr ht_pos)
    _ = σ * sqrt (2 * log n) := h_algebra


end

end LeanPool
