/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.MultipointPV

/-!
# Multi-point PV: Dominated Convergence

The dominated convergence machinery for decomposing multi-point principal
values into sums of single-point principal values. Contains the pointwise
a.e. limit, norm bounds, measurability, and the main convergence theorems.

## Main Results

* `dominated_convergence_multipoint_helper` — core DCT for multi-point PV
* `multipointPV_diff_tendsto` — difference integrand converges
* `multipointPV_eq_sum_of_integral_zero` — multi-point PV equals sum of
  single-point PVs when regular integral vanishes
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

/-! ## Dominated Convergence Helpers -/

private lemma continuousOn_deriv_off_partition (γ : PiecewiseC1Immersion) :
    ContinuousOn (deriv γ.toFun) (Icc γ.a γ.b \ γ.partition) := by
  intro t ⟨ht_Icc, ht_notP⟩
  by_cases ht_Ioo : t ∈ Ioo γ.a γ.b
  · exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
        t ht_Ioo ht_notP).continuousWithinAt
  · have ha_in_P := γ.toPiecewiseC1Curve.endpoints_in_partition.1
    have hb_in_P := γ.toPiecewiseC1Curve.endpoints_in_partition.2
    have ht_endpoint : t = γ.a ∨ t = γ.b := by
      simp only [Set.mem_Ioo, not_and, not_lt] at ht_Ioo
      rcases ht_Icc.1.lt_or_eq with h | h
      · right; exact le_antisymm ht_Icc.2 (ht_Ioo h)
      · left; exact h.symm
    rcases ht_endpoint with rfl | rfl
    <;> exact (ht_notP (by assumption)).elim

private lemma uIoc_subset_Icc_of_lt {a b : ℝ} (hab : a < b) : Set.uIoc a b ⊆ Icc a b :=
  Set.uIoc_of_le (le_of_lt hab) ▸ Set.Ioc_subset_Icc_self

private lemma γt_not_mem_S0_of_all_far {S0 : Finset ℂ} {γ : ℝ → ℂ} {t : ℝ} {ε : ℝ}
    (hε : 0 < ε) (hall : ∀ s ∈ S0, ε < ‖γ t - s‖) :
    γ t ∉ (S0 : Set ℂ) := by
  intro h_in; simp only [Finset.mem_coe] at h_in
  have := hall (γ t) h_in; simp only [sub_self, norm_zero] at this; linarith

private lemma residue_sum_ifs_eq_mul_deriv {S0 : Finset ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ}
    {t : ℝ} {ε : ℝ} (hall : ∀ s ∈ S0, ε < ‖γ t - s‖) :
    ∑ s ∈ S0, (if ε < ‖γ t - s‖ then residueSimplePole f s / (γ t - s) * deriv γ t
      else 0) = (∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t := by
  rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s hs; rw [if_pos (hall s hs)]

private lemma A_int_eq_greg_mul_deriv {S0 : Finset ℂ} {f g_reg : ℂ → ℂ} {γ : ℝ → ℂ} {t : ℝ}
    {ε : ℝ} (hε : 0 < ε) (hall : ∀ s ∈ S0, ε < ‖γ t - s‖)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s)) :
    f (γ t) * deriv γ t - (∑ s ∈ S0, residueSimplePole f s / (γ t - s)) * deriv γ t =
      g_reg (γ t) * deriv γ t := by
  have h_not_in := γt_not_mem_S0_of_all_far hε hall
  have h_eq : f (γ t) - ∑ s ∈ S0, residueSimplePole f s / (γ t - s) = g_reg (γ t) := by
    rw [hg_decomp (γ t) h_not_in]; ring
  rw [← sub_mul, h_eq]

private lemma residueSimplePole_norm_bound (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hS0_ne : S0.Nonempty) :
    ∃ Mc : ℝ, ∀ s ∈ S0, ‖residueSimplePole f s‖ ≤ Mc := by
  use S0.sup' hS0_ne (fun s => ‖residueSimplePole f s‖)
  intro s hs; exact Finset.le_sup' (fun s => ‖residueSimplePole f s‖) hs

/-! ## Dominated Convergence: Empty Case -/

private lemma dominated_convergence_empty_case (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hg_decomp : ∀ z, z ∉ (∅ : Finset ℂ) → f z = g_reg z + ∑ s ∈ (∅ : Finset ℂ),
      residueSimplePole f s / (z - s)) :
    let M := fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn ∅ f γ.toFun ε t
    let S' := fun ε => ∑ s ∈ (∅ : Finset ℂ).attach,
      ∫ t in γ.a..γ.b, if ‖γ.toFun t - s.val‖ > ε
        then (residueSimplePole f s.val / (γ.toFun t - s.val)) * deriv γ.toFun t else 0
    let A := fun ε => M ε - S' ε
    let G := ∫ t in γ.a..γ.b, g_reg (γ.toFun t) * deriv γ.toFun t
    Tendsto A (𝓝[>] 0) (𝓝 G) := by
  intro M S' A G
  have hA_eq_M : ∀ ε, A ε = M ε := by
    intro ε; simp only [A, S', Finset.attach_empty, Finset.sum_empty, sub_zero]
  have hM_eq : ∀ ε > 0, M ε = ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t := by
    intro ε _hε; apply intervalIntegral.integral_congr; intro t _
    simp only [cauchyPrincipalValueIntegrandOn, Finset.notMem_empty, false_and,
      exists_false, ↓reduceIte]
  have hf_eq_g : ∀ z, f z = g_reg z := by
    intro z; have h := hg_decomp z (Finset.notMem_empty z)
    simp only [Finset.sum_empty, add_zero] at h; exact h
  have hM_eq_G : ∀ ε > 0, M ε = G := by
    intro ε hε; rw [hM_eq ε hε]
    apply intervalIntegral.integral_congr; intro t _; simp only [hf_eq_g (γ.toFun t)]
  apply Filter.Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with ε hε; rw [hA_eq_M, hM_eq_G ε hε]
  · exact tendsto_const_nhds

/-! ## Dominated Convergence: Pointwise A.E. Limit -/

private lemma pointwise_ae_limit_off_crossing (S0 : Finset ℂ) (f g_reg : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hS0_ne : S0 ≠ ∅)
    (h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} = 0)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s)) :
    let A_int : ℝ → ℝ → ℂ := fun ε t =>
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t -
        ∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0
    let f_lim : ℝ → ℂ := fun t => g_reg (γ.toFun t) * deriv γ.toFun t
    ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      Tendsto (fun ε => A_int ε t) (𝓝[>] 0) (𝓝 (f_lim t)) := by
  intro A_int f_lim
  rw [ae_iff]; apply le_antisymm _ zero_le
  calc volume {t | ¬(t ∈ Ι γ.a γ.b →
          Tendsto (fun ε => A_int ε t) (𝓝[>] 0) (𝓝 (f_lim t)))}
      ≤ volume {t | t ∈ Icc γ.a γ.b ∧ γ.toFun t ∈ (S0 : Set ℂ)} := by
        apply MeasureTheory.measure_mono; intro t ht
        simp only [Set.mem_setOf_eq] at ht; rw [Classical.not_imp] at ht
        obtain ⟨ht_in, ht_not_tendsto⟩ := ht
        constructor
        · have h1 : t ∈ Set.uIcc γ.a γ.b := Set.uIoc_subset_uIcc ht_in
          rw [Set.uIcc_of_le (le_of_lt γ.hab)] at h1; exact h1
        · by_contra ht_not_in_S0
          apply ht_not_tendsto
          have hγt_not_in_S0 : γ.toFun t ∉ (S0 : Set ℂ) := ht_not_in_S0
          have hS0_nonempty : S0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0_ne
          have hdist_pos : ∀ s ∈ S0, (0 : ℝ) < ‖γ.toFun t - s‖ := by
            intro s hs; simp only [norm_pos_iff, sub_ne_zero]
            intro heq; exact hγt_not_in_S0 (heq ▸ hs)
          let δ := S0.inf' hS0_nonempty (fun s => ‖γ.toFun t - s‖)
          have hδ_pos : 0 < δ := by
            simp only [δ, Finset.lt_inf'_iff]; intro s hs; exact hdist_pos s hs
          apply Filter.Tendsto.congr' _ tendsto_const_nhds
          filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε ⟨hε_pos, hε_small⟩
          simp only [A_int, f_lim]
          have hall_far : ∀ s ∈ S0, ε < ‖γ.toFun t - s‖ := by
            intro s hs
            calc ε < δ := hε_small
              _ ≤ ‖γ.toFun t - s‖ := Finset.inf'_le _ hs
          have hM_eval : cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t =
              f (γ.toFun t) * deriv γ.toFun t := by
            simp only [cauchyPrincipalValueIntegrandOn]; rw [if_neg]; push Not; exact hall_far
          rw [hM_eval, residue_sum_ifs_eq_mul_deriv hall_far, ← sub_mul]
          have hdecomp := hg_decomp (γ.toFun t) hγt_not_in_S0
          rw [show f (γ.toFun t) - ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s) =
            g_reg (γ.toFun t) from by rw [hdecomp]; ring]
    _ = 0 := h_crossing_null

/-! ## Dominated Convergence: Norm Bounds -/

private lemma norm_A_int_bound_all_far (S0 : Finset ℂ) (f g_reg : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (Mg Mγ' : ℝ)
    (hMg : ∀ z ∈ γ.toFun '' Icc γ.a γ.b, ‖g_reg z‖ ≤ Mg)
    (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    {t ε : ℝ} (hε : 0 < ε) (ht : t ∈ Icc γ.a γ.b)
    (hall : ∀ s ∈ S0, ε < ‖γ.toFun t - s‖) (B : ℝ)
    (hB : max 0 Mg * max 0 Mγ' ≤ B) :
    ‖cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t -
      ∑ s ∈ S0, (if ‖γ.toFun t - s‖ > ε
        then residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t else 0)‖ ≤ B := by
  simp only [cauchyPrincipalValueIntegrandOn]
  have h_neg : ¬∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε := by push Not; exact hall
  rw [if_neg h_neg, residue_sum_ifs_eq_mul_deriv hall, ← sub_mul]
  have h_not_in := γt_not_mem_S0_of_all_far hε hall
  rw [show f (γ.toFun t) - ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s) =
    g_reg (γ.toFun t) from by rw [hg_decomp (γ.toFun t) h_not_in]; ring]
  have h_g_bound : ‖g_reg (γ.toFun t)‖ ≤ Mg := hMg (γ.toFun t) ⟨t, ht, rfl⟩
  have h_γ'_bound : ‖deriv γ.toFun t‖ ≤ Mγ' := hMγ' t ht
  calc ‖g_reg (γ.toFun t) * deriv γ.toFun t‖
      ≤ ‖g_reg (γ.toFun t)‖ * ‖deriv γ.toFun t‖ := norm_mul_le _ _
    _ ≤ Mg * Mγ' := mul_le_mul h_g_bound h_γ'_bound (norm_nonneg _)
        (le_trans (norm_nonneg _) h_g_bound)
    _ ≤ max 0 Mg * max 0 Mγ' := by
        apply mul_le_mul (le_max_right 0 Mg) (le_max_right 0 Mγ')
          (le_trans (norm_nonneg _) h_γ'_bound) (le_max_left 0 Mg)
    _ ≤ B := hB

private lemma residue_sum_norm_le_singular_bound {S0 : Finset ℂ} {f : ℂ → ℂ} {z : ℂ}
    {Mc δ ε : ℝ} (hδ_pos : 0 < δ)
    (hMc : ∀ s ∈ S0, ‖residueSimplePole f s‖ ≤ Mc)
    (hδ_sep : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖)
    {s₀ : ℂ} (hs₀ : s₀ ∈ S0) (hs₀_near : ‖z - s₀‖ ≤ ε) :
    ∀ s ∈ S0, ‖if ‖z - s‖ > ε then residueSimplePole f s / (z - s) else 0‖ ≤
      2 * Mc / δ := by
  intro s hs
  by_cases h_inc : ‖z - s‖ > ε
  · simp only [h_inc, ↓reduceIte]
    have h_dist : δ / 2 ≤ ‖z - s‖ := by
      by_cases hs_eq : s = s₀
      · subst hs_eq; exact absurd h_inc (not_lt.mpr hs₀_near)
      · have h_sep : δ ≤ ‖s - s₀‖ := by
          have := hδ_sep s hs s₀ hs₀ hs_eq; rw [norm_sub_rev] at this; exact this
        have h_tri : ‖s - s₀‖ - ‖z - s₀‖ ≤ ‖z - s‖ := by
          have := norm_sub_norm_le (s - s₀) (z - s₀)
          calc ‖s - s₀‖ - ‖z - s₀‖ ≤ ‖(s - s₀) - (z - s₀)‖ := this
            _ = ‖s - z‖ := by ring_nf
            _ = ‖z - s‖ := norm_sub_rev _ _
        by_cases hε_small' : ε ≤ δ / 2
        · calc δ / 2 ≤ δ - ε := by linarith
            _ ≤ ‖s - s₀‖ - ‖z - s₀‖ := by linarith [h_sep, hs₀_near]
            _ ≤ ‖z - s‖ := h_tri
        · push Not at hε_small'; linarith [h_inc]
    have hMc_nonneg : 0 ≤ Mc := le_trans (norm_nonneg _) (hMc s hs)
    calc ‖residueSimplePole f s / (z - s)‖
        = ‖residueSimplePole f s‖ / ‖z - s‖ := norm_div _ _
      _ ≤ Mc / ‖z - s‖ := div_le_div_of_nonneg_right (hMc s hs) (norm_nonneg _)
      _ ≤ Mc / (δ / 2) := div_le_div_of_nonneg_left hMc_nonneg (by linarith) h_dist
      _ = 2 * Mc / δ := by ring
  · simp only [h_inc, ↓reduceIte, norm_zero]
    refine div_nonneg (mul_nonneg ?_ ?_) ?_
    · linarith
    · exact le_trans (norm_nonneg _) (hMc s₀ hs₀)
    · linarith

private lemma norm_A_int_bound_some_near (S0 : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (Mc Mγ' δ : ℝ) (hδ_pos : 0 < δ)
    (hMc : ∀ s ∈ S0, ‖residueSimplePole f s‖ ≤ Mc)
    (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (hδ_sep : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖)
    {t ε : ℝ} (ht : t ∈ Icc γ.a γ.b) {s₀ : ℂ} (hs₀ : s₀ ∈ S0) (hs₀_near : ‖γ.toFun t - s₀‖ ≤ ε)
    (B : ℝ) (hB : max 0 (2 * (S0.card : ℝ) * Mc / δ) * max 0 Mγ' ≤ B) :
    ‖cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t -
      ∑ s ∈ S0, (if ‖γ.toFun t - s‖ > ε
        then residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t else 0)‖ ≤ B := by
  simp only [cauchyPrincipalValueIntegrandOn]
  rw [if_pos ⟨s₀, hs₀, hs₀_near⟩]; simp only [zero_sub, norm_neg]
  have h_γ'_bound : ‖deriv γ.toFun t‖ ≤ Mγ' := hMγ' t ht
  -- Factor out deriv from sum
  have h_factor :
      ∑ s ∈ S0, (if ‖γ.toFun t - s‖ > ε
        then residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t else 0) =
      (∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
        then residueSimplePole f s / (γ.toFun t - s) else 0) * deriv γ.toFun t := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _
    by_cases h : ‖γ.toFun t - s‖ > ε
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, zero_mul]
  rw [h_factor]
  let singularBound := 2 * (S0.card : ℝ) * Mc / δ
  -- Bound the sum of residue quotients
  have h_sum_bound : ‖∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
      then residueSimplePole f s / (γ.toFun t - s) else 0‖ ≤ singularBound := by
    calc ‖∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
            then residueSimplePole f s / (γ.toFun t - s) else 0‖
        ≤ ∑ s ∈ S0, ‖if ‖γ.toFun t - s‖ > ε
            then residueSimplePole f s / (γ.toFun t - s) else 0‖ := norm_sum_le _ _
      _ ≤ ∑ _s ∈ S0, (2 * Mc / δ) :=
          Finset.sum_le_sum (residue_sum_norm_le_singular_bound hδ_pos hMc hδ_sep hs₀ hs₀_near)
      _ = singularBound := by simp only [Finset.sum_const]; ring
  have h_sb_nonneg : 0 ≤ singularBound := by
    refine div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_
    · linarith
    · exact Nat.cast_nonneg _
    · exact le_trans (norm_nonneg _) (hMc s₀ hs₀)
    · linarith
  calc ‖(∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
          then residueSimplePole f s / (γ.toFun t - s) else 0) * deriv γ.toFun t‖
      ≤ singularBound * Mγ' :=
        (norm_mul_le _ _).trans (mul_le_mul h_sum_bound h_γ'_bound (norm_nonneg _) h_sb_nonneg)
    _ ≤ max 0 singularBound * max 0 Mγ' := by
        have h0_le_Mγ' : 0 ≤ Mγ' := le_trans (norm_nonneg _) h_γ'_bound
        exact mul_le_mul (le_max_right 0 singularBound) (le_max_right 0 Mγ')
          h0_le_Mγ' (le_max_left 0 singularBound)
    _ ≤ B := hB

private lemma A_int_norm_bound (S0 : Finset ℂ) (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (Mg Mγ' Mc δ : ℝ) (hδ_pos : 0 < δ)
    (hMg : ∀ z ∈ γ.toFun '' Icc γ.a γ.b, ‖g_reg z‖ ≤ Mg)
    (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (hMc : ∀ s ∈ S0, ‖residueSimplePole f s‖ ≤ Mc)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hδ_sep : ∀ s ∈ S0, ∀ s' ∈ S0, s ≠ s' → δ ≤ ‖s' - s‖) :
    let B := max 1 (max (max 0 Mg) (max 0 (2 * (S0.card : ℝ) * Mc / δ)) * max 0 Mγ')
    ∀ ε > 0, ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      ‖cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t -
        ∑ s ∈ S0, (if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t
          else 0)‖ ≤ B := by
  intro B ε _hε; apply ae_of_all; intro t ht
  have ht_Icc : t ∈ Icc γ.a γ.b := uIoc_subset_Icc_of_lt γ.hab ht
  by_cases hall : ∀ s ∈ S0, ε < ‖γ.toFun t - s‖
  · exact norm_A_int_bound_all_far S0 f g_reg γ Mg Mγ' hMg hMγ' hg_decomp _hε ht_Icc hall B
      (le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_max_left 0 Mγ'))
        (le_max_right _ _))
  · push Not at hall; obtain ⟨s₀, hs₀, hs₀_near⟩ := hall
    exact norm_A_int_bound_some_near S0 f γ Mc Mγ' δ hδ_pos hMc hMγ' hδ_sep ht_Icc hs₀
      hs₀_near B (le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_max_left 0 Mγ'))
        (le_max_right _ _))

/-! ## Dominated Convergence: Measurability of A_int -/

private lemma A_int_aEStronglyMeasurable (S0 : Finset ℂ) (f g_reg : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hg_cont : ContinuousOn g_reg (γ.toFun '' Icc γ.a γ.b)) {ε : ℝ} (hε : 0 < ε) :
    AEStronglyMeasurable
      (fun t => cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t -
        ∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0)
      (volume.restrict (Ι γ.a γ.b)) := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hγ'_off_P := continuousOn_deriv_off_partition γ
  have huIcc : Set.uIcc γ.a γ.b = Icc γ.a γ.b := Set.uIcc_of_le (le_of_lt γ.hab)
  have h_eq_decomposed : ∀ t,
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t =
      (if ∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε then 0
        else (g_reg (γ.toFun t) + ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)) *
          deriv γ.toFun t) := by
    intro t; simp only [cauchyPrincipalValueIntegrandOn]
    split_ifs with h_near
    · rfl
    · push Not at h_near
      have h_not_in_S0 : γ.toFun t ∉ (S0 : Set ℂ) := by
        intro h_in; have := h_near (γ.toFun t) h_in
        simp only [sub_self, norm_zero] at this; linarith
      rw [hg_decomp (γ.toFun t) h_not_in_S0]
  have h_meas1 := aEStronglyMeasurable_pv_integrand_decomposed S0
    (residueSimplePole f) hε hg_cont hγ_cont hγ'_off_P
  have h_meas_pv : AEStronglyMeasurable (cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε)
      (volume.restrict (Icc γ.a γ.b)) :=
    h_meas1.congr (ae_of_all _ (fun t => (h_eq_decomposed t).symm))
  have h_meas_sum := aEStronglyMeasurable_pv_sum_residue S0 f γ.toFun ε hε γ.a γ.b hγ_cont
    hγ'_off_P
  exact (h_meas_pv.sub h_meas_sum).mono_measure
    (Measure.restrict_mono (uIoc_subset_Icc_of_lt γ.hab) le_rfl)

/-! ## Dominated Convergence: Integrability and Integral Identity -/

private lemma pvIntegrand_intervalIntegrable_of_nonempty (S0 : Finset ℂ) (f g_reg : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hS0_ne : S0 ≠ ∅)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hg_cont : ContinuousOn g_reg (γ.toFun '' Icc γ.a γ.b)) {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε)
      volume γ.a γ.b := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hγ'_off_P := continuousOn_deriv_off_partition γ
  obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
  obtain ⟨Mg, hMg⟩ := continuousOn_image_bounded hγ_cont hg_cont
  have hS0_nonempty : S0.Nonempty := Finset.nonempty_of_ne_empty hS0_ne
  let res_bound := S0.sup' hS0_nonempty (fun s => ‖residueSimplePole f s‖)
  have h_res_nonneg : 0 ≤ res_bound := by
    simp only [res_bound]; have hs := hS0_nonempty.choose_spec
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun s => ‖residueSimplePole f s‖) hs)
  let Mb := (|Mg| + S0.card * res_bound / ε) * |Mγ'| + 1
  have hMb_pos : 0 < Mb := by simp only [Mb]; positivity
  have h_bound : ∀ t ∈ Icc γ.a γ.b,
      ‖cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t‖ ≤ Mb := by
    intro t ht; simp only [cauchyPrincipalValueIntegrandOn]; split_ifs with h
    · simp only [norm_zero]; linarith
    · push Not at h
      have hγt_notin : γ.toFun t ∉ (S0 : Set ℂ) := by
        intro hmem; simp only [Finset.mem_coe] at hmem
        have hdist := h (γ.toFun t) hmem
        simp only [sub_self, norm_zero] at hdist; linarith
      rw [hg_decomp (γ.toFun t) hγt_notin]
      calc ‖(g_reg (γ.toFun t) + ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)) *
              deriv γ.toFun t‖
          = ‖g_reg (γ.toFun t) + ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)‖ *
              ‖deriv γ.toFun t‖ := norm_mul _ _
        _ ≤ (|Mg| + S0.card * res_bound / ε) * |Mγ'| := by
            apply mul_le_mul _ (le_trans (hMγ' t ht) (le_abs_self _)) (norm_nonneg _)
            · positivity
            calc ‖g_reg (γ.toFun t) + ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)‖
                ≤ ‖g_reg (γ.toFun t)‖ +
                    ‖∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)‖ := norm_add_le _ _
              _ ≤ |Mg| + ∑ s ∈ S0, ‖residueSimplePole f s / (γ.toFun t - s)‖ := by
                  gcongr; · exact le_trans (hMg _ (Set.mem_image_of_mem _ ht)) (le_abs_self _)
                  · exact norm_sum_le _ _
              _ ≤ |Mg| + ∑ _s ∈ S0, res_bound / ε := by
                  gcongr with s hs; rw [norm_div]
                  calc ‖residueSimplePole f s‖ / ‖γ.toFun t - s‖
                      ≤ res_bound / ‖γ.toFun t - s‖ := by
                        gcongr; exact Finset.le_sup' (fun s => ‖residueSimplePole f s‖) hs
                    _ ≤ res_bound / ε := by gcongr; exact le_of_lt (h s hs)
              _ = |Mg| + S0.card * res_bound / ε := by simp only [Finset.sum_const]; ring
        _ ≤ Mb := by simp only [Mb]; linarith
  have h_meas_decomposed := aEStronglyMeasurable_pv_integrand_decomposed S0
    (residueSimplePole f) hε hg_cont hγ_cont hγ'_off_P
  have h_eq_ae : (fun t => cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
      =ᵐ[volume.restrict (Icc γ.a γ.b)]
      (fun t => if ∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε then (0 : ℂ)
        else (g_reg (γ.toFun t) + ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s)) *
          deriv γ.toFun t) := by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t _
    simp only [cauchyPrincipalValueIntegrandOn]; split_ifs with h_near
    · rfl
    · push Not at h_near
      rw [hg_decomp (γ.toFun t) (γt_not_mem_S0_of_all_far hε h_near)]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt γ.hab)]
  exact (integrableOn_of_bounded_aeMeasurable Mb
    (h_meas_decomposed.congr h_eq_ae.symm) h_bound).mono_set Ioc_subset_Icc_self

private lemma A_eq_integral_A_int (S0 : Finset ℂ) (f g_reg : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hS0_ne : S0 ≠ ∅)
    (hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z + ∑ s ∈ S0, residueSimplePole f s / (z - s))
    (hg_cont : ContinuousOn g_reg (γ.toFun '' Icc γ.a γ.b)) :
    let A_int : ℝ → ℝ → ℂ := fun ε t =>
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t -
        ∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0
    let M := fun ε => ∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t
    let S' := fun ε => ∑ s ∈ S0, ∫ t in γ.a..γ.b,
      if ‖γ.toFun t - s‖ > ε then (residueSimplePole f s / (γ.toFun t - s)) *
        deriv γ.toFun t else 0
    ∀ ε > 0, M ε - S' ε = ∫ t in γ.a..γ.b, A_int ε t := by
  intro A_int M S' ε hε
  simp only [A_int, M, S']
  let S_int_fun : ℂ → ℝ → ℂ := fun s t =>
    if ‖γ.toFun t - s‖ > ε
    then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0
  have hM_int := pvIntegrand_intervalIntegrable_of_nonempty S0 f g_reg γ hS0_ne hg_decomp
    hg_cont hε
  -- Integrability of each residue term
  have hS_int : ∀ s ∈ S0, IntervalIntegrable (S_int_fun s) volume γ.a γ.b := by
    intro s _hs; exact intervalIntegrable_residueTerm hε
  -- Sum of integrals = integral of sum
  have h_sum_eq : ∑ s ∈ S0, ∫ t in γ.a..γ.b, S_int_fun s t =
      ∫ t in γ.a..γ.b, ∑ s ∈ S0, S_int_fun s t :=
    (intervalIntegral.integral_finsetSum hS_int).symm
  -- Integrability of sum
  have hSum_int : IntervalIntegrable (fun t => ∑ s ∈ S0, S_int_fun s t)
      volume γ.a γ.b := by
    have : ∀ (S : Finset ℂ), (∀ s ∈ S, IntervalIntegrable (S_int_fun s) volume γ.a γ.b) →
        IntervalIntegrable (fun t => ∑ s ∈ S, S_int_fun s t) volume γ.a γ.b := by
      intro S; induction S using Finset.induction_on with
      | empty => intro _; simp only [Finset.sum_empty]; exact intervalIntegrable_const
      | insert s' S'' hs'' ih =>
        intro h_all; simp only [Finset.sum_insert hs'']
        apply IntervalIntegrable.add
        · exact h_all s' (Finset.mem_insert_self s' S'')
        · exact ih (fun s hs => h_all s (Finset.mem_insert_of_mem hs))
    exact this S0 hS_int
  rw [h_sum_eq, ← intervalIntegral.integral_sub hM_int hSum_int]

/-! ## Dominated Convergence: Main Theorem -/

/-- Core dominated convergence for multi-point PV
decomposition. -/
lemma dominated_convergence_multipoint_helper
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (g_reg : ℂ → ℂ)
    (_h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧
        γ.toFun t ∈ (S0 : Set ℂ)} = 0)
    (_hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z +
        ∑ s ∈ S0,
          residueSimplePole f s / (z - s))
    (_hg_cont : ContinuousOn g_reg
      (γ.toFun '' Icc γ.a γ.b))
    (hS0_sep : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0,
      s ≠ s' → δ ≤ ‖s' - s‖) :
    let M := fun ε =>
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f
          γ.toFun ε t
    let S' := fun ε =>
      ∑ s ∈ S0.attach,
        ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s.val‖ > ε
          then (residueSimplePole f s.val /
            (γ.toFun t - s.val)) *
              deriv γ.toFun t
          else 0
    let A := fun ε => M ε - S' ε
    let G := ∫ t in γ.a..γ.b,
      g_reg (γ.toFun t) * deriv γ.toFun t
    Tendsto A (𝓝[>] 0) (𝓝 G) := by
  intro M S' A G
  by_cases hS0_empty : S0 = ∅
  case pos =>
    subst hS0_empty; exact dominated_convergence_empty_case f g_reg γ _hg_decomp
  case neg =>
    let A_int : ℝ → ℝ → ℂ := fun ε t =>
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t -
        ∑ s ∈ S0, if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s / (γ.toFun t - s)) * deriv γ.toFun t else 0
    let f_lim : ℝ → ℂ := fun t => g_reg (γ.toFun t) * deriv γ.toFun t
    have hG_eq : G = ∫ t in γ.a..γ.b, f_lim t := rfl
    -- Rewrite S' using detach
    have h_S'_eq : ∀ ε, S' ε = ∑ s ∈ S0, ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε then (residueSimplePole f s / (γ.toFun t - s)) *
          deriv γ.toFun t else 0 := by
      intro ε; simp only [S']; rw [Finset.sum_attach S0 (fun s => ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε then (residueSimplePole f s / (γ.toFun t - s)) *
          deriv γ.toFun t else 0)]
    -- A ε = ∫ A_int ε t
    have h_A_eq_int : ∀ ε > 0, A ε = ∫ t in γ.a..γ.b, A_int ε t := by
      intro ε hε; simp only [A, M, h_S'_eq, A_int]
      exact A_eq_integral_A_int S0 f g_reg γ hS0_empty _hg_decomp _hg_cont ε hε
    -- Obtain bound constants
    have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
    obtain ⟨Mg, hMg⟩ := continuousOn_image_bounded hγ_cont _hg_cont
    obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
    have hS0_nonempty : S0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS0_empty
    obtain ⟨Mc, hMc⟩ := residueSimplePole_norm_bound S0 f hS0_nonempty
    obtain ⟨δ, hδ_pos, hδ_sep⟩ := hS0_sep
    -- Apply dominated convergence
    rw [hG_eq]; apply Filter.Tendsto.congr'
    · filter_upwards [self_mem_nhdsWithin] with ε hε; exact (h_A_eq_int ε hε).symm
    · exact tendsto_integral_of_dominated'
        (fun ε hε => A_int_aEStronglyMeasurable S0 f g_reg γ _hg_decomp _hg_cont hε)
        (A_int_norm_bound S0 f g_reg γ Mg Mγ' Mc δ hδ_pos hMg hMγ' hMc _hg_decomp hδ_sep)
        intervalIntegrable_const
        (pointwise_ae_limit_off_crossing S0 f g_reg γ hS0_empty _h_crossing_null _hg_decomp)

/-- Difference integrand converges to regular
part integral. -/
lemma multipointPV_diff_tendsto
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (_h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧
        γ.toFun t ∈ (S0 : Set ℂ)} = 0)
    (g_reg : ℂ → ℂ)
    (_hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = g_reg z +
        ∑ s ∈ S0,
          residueSimplePole f s / (z - s))
    (hg_cont : ContinuousOn g_reg
      (γ.toFun '' Icc γ.a γ.b))
    (hS0_sep : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0,
      s ≠ s' → δ ≤ ‖s' - s‖) :
    let M := fun ε =>
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f
          γ.toFun ε t
    let S' := fun ε =>
      ∑ s ∈ S0.attach,
        ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s.val‖ > ε
          then (residueSimplePole f s.val /
            (γ.toFun t - s.val)) *
              deriv γ.toFun t
          else 0
    let A := fun ε => M ε - S' ε
    let G := ∫ t in γ.a..γ.b,
      g_reg (γ.toFun t) * deriv γ.toFun t
    Tendsto A (𝓝[>] 0) (𝓝 G) := by
  intro M S' A G
  have h_S'_eq :
      S' = fun ε =>
        ∑ s ∈ S0,
          ∫ t in γ.a..γ.b,
            if ‖γ.toFun t - s‖ > ε
            then (residueSimplePole f s /
              (γ.toFun t - s)) *
                deriv γ.toFun t
            else 0 := by
    ext ε
    simp only [S']
    rw [Finset.sum_attach S0
      (fun s => ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε
        then (residueSimplePole f s /
          (γ.toFun t - s)) * deriv γ.toFun t
        else 0)]
  exact
    dominated_convergence_multipoint_helper S0 f γ
      g_reg _h_crossing_null _hg_decomp hg_cont
      hS0_sep

/-- Multi-point PV equals sum of single-point PVs
when the regular part integral vanishes. -/
lemma multipointPV_eq_sum_of_integral_zero
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (_h_crossing_null : MeasureTheory.volume
      {t | t ∈ Icc γ.a γ.b ∧
        γ.toFun t ∈ (S0 : Set ℂ)} = 0)
    (_g_reg : ℂ → ℂ)
    (_hg_decomp : ∀ z, z ∉ (S0 : Set ℂ) →
      f z = _g_reg z +
        ∑ s ∈ S0,
          residueSimplePole f s / (z - s))
    (_hg_cont : ContinuousOn _g_reg
      (γ.toFun '' Icc γ.a γ.b))
    (_hS0_sep : ∃ δ > 0, ∀ s ∈ S0, ∀ s' ∈ S0,
      s ≠ s' → δ ≤ ‖s' - s‖)
    (_hg_zero : ∫ t in γ.a..γ.b,
      _g_reg (γ.toFun t) * deriv γ.toFun t = 0)
    (_hPV_exists : CauchyPrincipalValueExistsOn
      S0 f γ.toFun γ.a γ.b)
    (_hPV_each_tendsto : Tendsto
      (fun ε => ∑ s ∈ S0,
        ∫ t in γ.a..γ.b,
          if ‖γ.toFun t - s‖ > ε
          then (residueSimplePole f s /
            (γ.toFun t - s)) * deriv γ.toFun t
          else 0)
      (𝓝[>] 0)
      (𝓝 (∑ s ∈ S0,
        cauchyPrincipalValue'
          (fun z =>
            residueSimplePole f s / (z - s))
          γ.toFun γ.a γ.b s))) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      ∑ s ∈ S0,
        cauchyPrincipalValue'
          (fun z =>
            residueSimplePole f s / (z - s))
          γ.toFun γ.a γ.b s := by
  obtain ⟨L, hL⟩ := _hPV_exists
  have h_pv_eq_L :
      cauchyPrincipalValueOn S0 f γ.toFun
        γ.a γ.b = L :=
    hL.limUnder_eq
  have h_G_zero :
      ∫ t in γ.a..γ.b,
        _g_reg (γ.toFun t) *
          deriv γ.toFun t = 0 :=
    _hg_zero
  have h_A_tendsto :=
    multipointPV_diff_tendsto S0 f γ
      _h_crossing_null _g_reg _hg_decomp _hg_cont
      _hS0_sep
  simp only [h_G_zero] at h_A_tendsto
  let S'_attach := fun ε =>
    ∑ s ∈ S0.attach,
      ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s.val‖ > ε
        then (residueSimplePole f s.val /
          (γ.toFun t - s.val)) * deriv γ.toFun t
        else 0
  let S' := fun ε =>
    ∑ s ∈ S0,
      ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε
        then (residueSimplePole f s /
          (γ.toFun t - s)) * deriv γ.toFun t
        else 0
  have h_S'_eq : S' = S'_attach := by
    ext ε
    simp only [S', S'_attach]
    rw [Finset.sum_attach S0
      (fun s => ∫ t in γ.a..γ.b,
        if ‖γ.toFun t - s‖ > ε
        then (residueSimplePole f s /
          (γ.toFun t - s)) * deriv γ.toFun t
        else 0)]
  let Mf := fun ε =>
    ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 f
        γ.toFun ε t
  let Af := fun ε => Mf ε - S'_attach ε
  have h_S'_attach_tendsto :
      Tendsto S'_attach (𝓝[>] 0) (𝓝 L) := by
    have h_eq : S'_attach =
        fun ε => Mf ε - Af ε := by
      ext ε
      simp only [Mf, Af, S'_attach]
      ring
    have h_sub :
        Tendsto (fun ε => Mf ε - Af ε) (𝓝[>] 0)
          (𝓝 (L - 0)) :=
      hL.sub h_A_tendsto
    simp only [sub_zero] at h_sub
    rw [h_eq]
    exact h_sub
  have h_S'_tendsto :
      Tendsto S' (𝓝[>] 0) (𝓝 L) := by
    rw [h_S'_eq]
    exact h_S'_attach_tendsto
  have h_L_eq_sum :
      L = ∑ s ∈ S0,
        cauchyPrincipalValue'
          (fun z =>
            residueSimplePole f s / (z - s))
          γ.toFun γ.a γ.b s :=
    tendsto_nhds_unique h_S'_tendsto
      _hPV_each_tendsto
  rw [h_pv_eq_L, h_L_eq_sum]

end
