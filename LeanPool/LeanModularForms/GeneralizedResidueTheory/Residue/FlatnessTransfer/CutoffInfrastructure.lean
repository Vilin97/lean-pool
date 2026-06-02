/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.BoundaryVanishing

/-!
# Cutoff zpow Infrastructure

Direction rate from flatness, cutoff integral splitting, and the FTC-based
proof infrastructure for per-term PV vanishing. Builds on the boundary
vanishing foundations to provide the `cutoff_zpow_infrastructure` lemma.

## Main Results

* `direction_rate_from_flatness_right` — direction rate for right exit
* `direction_rate_from_flatness_left` — direction rate for left exit
* `cutoff_zpow_infrastructure` — combined FTC + direction infrastructure
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

namespace GeneralizedResidueTheory

private lemma direction_rate_from_flatness_right
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (L_R : ℂ) (hL_R_ne : L_R ≠ 0)
    (htend_R : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_R))
    (σ : ℝ → ℝ) (_hσ_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t₀ < σ ε)
    (_hσ_le_b : ∀ᶠ ε in 𝓝[>] (0 : ℝ), σ ε ≤ γ.b)
    (hσ_norm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ.toFun (σ ε) - s‖ = ε)
    (hσ_tendsto : Tendsto σ (𝓝[>] 0) (𝓝[>] t₀)) :
    (fun ε => ‖(γ.toFun (σ ε) - s) / (↑‖γ.toFun (σ ε) - s‖ : ℂ) -
      L_R / ↑‖L_R‖‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (m - 1 : ℕ) := by
  set v₀ := L_R / (↑‖L_R‖ : ℂ) with hv₀_def
  have hL_pos : (0 : ℝ) < ‖L_R‖ := norm_pos_iff.mpr hL_R_ne
  have hL_ne : ‖L_R‖ ≠ 0 := ne_of_gt hL_pos
  have hv₀_norm : ‖v₀‖ = 1 := by
    rw [hv₀_def]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL_pos, div_self hL_ne]
  have h_flat_eps : (fun ε => ‖tangentDeviation (γ.toFun (σ ε) - s) L_R‖) =o[𝓝[>] 0]
      (fun ε => ε ^ m) := by
    have h1 := (h_flat.right_flat L_R hL_R_ne htend_R).congr
      (fun t => by rw [hcross]) (fun t => by rw [hcross])
    exact ((h1.comp_tendsto hσ_tendsto).congr (fun _ => rfl) (fun _ => rfl)).trans_eventuallyEq
      (by filter_upwards [hσ_norm] with ε hε; simp only [Function.comp_def]; rw [hε])
  have h_re_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ((γ.toFun (σ ε) - s) * starRingEnd ℂ L_R).re :=
    hσ_tendsto.eventually (re_pos_right_of_slope γ s t₀ ht₀ hcross L_R hL_R_ne htend_R)
  rw [Asymptotics.isLittleO_iff]; intro c hc_pos
  have hcsq : (0 : ℝ) < c / Real.sqrt 2 := div_pos hc_pos (Real.sqrt_pos.mpr two_pos)
  filter_upwards [(Asymptotics.isLittleO_iff.mp h_flat_eps) hcsq, hσ_norm, h_re_pos] with
    ε h_td_bound hε_norm h_re
  set w := γ.toFun (σ ε) - s
  have hw_ne : w ≠ 0 := by intro h; simp [h] at h_re
  have hw_ne' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw_ne
  have hε_pos : 0 < ε := by rw [← hε_norm]; exact norm_pos_iff.mpr hw_ne
  set u := w / (↑‖w‖ : ℂ)
  have hu_norm : ‖u‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hw_ne']
  have hR_pos : 0 < (u * starRingEnd ℂ v₀).re := by
    change 0 < (w / (↑‖w‖ : ℂ) * starRingEnd ℂ (L_R / (↑‖L_R‖ : ℂ))).re
    rw [map_div₀ (starRingEnd ℂ), Complex.conj_ofReal,
      div_mul_div_comm, ← Complex.ofReal_mul, Complex.div_ofReal_re]
    exact div_pos h_re (mul_pos (by rw [hε_norm]; exact hε_pos) hL_pos)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have h_td_bound' : ‖tangentDeviation w L_R‖ ≤ c / Real.sqrt 2 * ε ^ m := by
    rwa [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (pow_nonneg hε_pos.le _)] at h_td_bound
  exact direction_rate_final_calc m c ε hε_pos hm w L_R u v₀ hu_norm hv₀_norm hR_pos
    (tangentDeviation_scale_eq w L_R hw_ne' hL_ne) hε_norm h_td_bound'

private lemma tangentDeviation_scale_neg_eq
    (w L : ℂ) (_hw_ne : ‖w‖ ≠ 0) (hL_ne : ‖L‖ ≠ 0) :
    ‖tangentDeviation (w / (↑‖w‖ : ℂ)) (-L / (↑‖L‖ : ℂ))‖ =
      ‖tangentDeviation w (-L)‖ / ‖w‖ := by
  rw [show (w / (↑‖w‖ : ℂ) : ℂ) = (‖w‖⁻¹ : ℝ) • w from by
      simp [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div],
    show -L / (↑‖L‖ : ℂ) = (‖L‖⁻¹ : ℝ) • (-L) from by
      rw [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div, neg_div],
    tangentDeviation_real_smul_right _ (inv_ne_zero hL_ne),
    tangentDeviation_real_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_eq_div]

private lemma direction_rate_from_flatness_left
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (L_L : ℂ) (hL_L_ne : L_L ≠ 0)
    (htend_L : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_L))
    (σ : ℝ → ℝ) (_hσ_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), σ ε < t₀)
    (_hσ_ge_a : ∀ᶠ ε in 𝓝[>] (0 : ℝ), γ.a ≤ σ ε)
    (hσ_norm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ.toFun (σ ε) - s‖ = ε)
    (hσ_tendsto : Tendsto σ (𝓝[>] 0) (𝓝[<] t₀)) :
    (fun ε => ‖(γ.toFun (σ ε) - s) / (↑‖γ.toFun (σ ε) - s‖ : ℂ) -
      (-L_L / ↑‖L_L‖)‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (m - 1 : ℕ) := by
  set v₀ := -L_L / (↑‖L_L‖ : ℂ) with hv₀_def
  have hL_pos : (0 : ℝ) < ‖L_L‖ := norm_pos_iff.mpr hL_L_ne
  have hL_ne : ‖L_L‖ ≠ 0 := ne_of_gt hL_pos
  have hv₀_norm : ‖v₀‖ = 1 := by
    rw [hv₀_def]
    simp only [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL_pos,
      div_self hL_ne]
  have h_flat_eps : (fun ε => ‖tangentDeviation (γ.toFun (σ ε) - s) (-L_L)‖) =o[𝓝[>] 0]
      (fun ε => ε ^ m) := by
    have h1 := (h_flat.left_flat L_L hL_L_ne htend_L).congr
      (fun t => by rw [hcross]) (fun t => by rw [hcross])
    have h_neg_eq : (fun ε => ‖tangentDeviation (γ.toFun (σ ε) - s) (-L_L)‖) =
        (fun ε => ‖tangentDeviation (γ.toFun (σ ε) - s) L_L‖) :=
      funext fun ε => by
        rw [show -L_L = (-1 : ℝ) • L_L from by erw [neg_smul, one_smul],
          tangentDeviation_real_smul_right _ (show (-1 : ℝ) ≠ 0 by norm_num)]
    rw [h_neg_eq]
    exact ((h1.comp_tendsto hσ_tendsto).congr (fun _ => rfl) (fun _ => rfl)).trans_eventuallyEq
      (by filter_upwards [hσ_norm] with ε hε; simp only [Function.comp_def]; rw [hε])
  have h_re_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ((γ.toFun (σ ε) - s) * starRingEnd ℂ (-L_L)).re :=
    hσ_tendsto.eventually (re_pos_left_of_slope γ s t₀ ht₀ hcross L_L hL_L_ne htend_L)
  rw [Asymptotics.isLittleO_iff]; intro c hc_pos
  have hcsq : (0 : ℝ) < c / Real.sqrt 2 := div_pos hc_pos (Real.sqrt_pos.mpr two_pos)
  filter_upwards [(Asymptotics.isLittleO_iff.mp h_flat_eps) hcsq, hσ_norm, h_re_pos] with
    ε h_td_bound hε_norm h_re
  set w := γ.toFun (σ ε) - s
  have hw_ne : w ≠ 0 := by intro h; simp [h] at h_re
  have hw_ne' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw_ne
  have hε_pos : 0 < ε := by rw [← hε_norm]; exact norm_pos_iff.mpr hw_ne
  set u := w / (↑‖w‖ : ℂ)
  have hu_norm : ‖u‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hw_ne']
  have hR_pos : 0 < (u * starRingEnd ℂ v₀).re := by
    change 0 < (w / (↑‖w‖ : ℂ) * starRingEnd ℂ (-L_L / (↑‖L_L‖ : ℂ))).re
    rw [map_div₀ (starRingEnd ℂ), map_neg, Complex.conj_ofReal,
      div_mul_div_comm, show w * -(starRingEnd ℂ L_L) = w * starRingEnd ℂ (-L_L) from by
        rw [map_neg], ← Complex.ofReal_mul, Complex.div_ofReal_re]
    exact div_pos h_re (mul_pos (by rw [hε_norm]; exact hε_pos) hL_pos)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have h_td_bound' : ‖tangentDeviation w (-L_L)‖ ≤ c / Real.sqrt 2 * ε ^ m := by
    rwa [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (pow_nonneg hε_pos.le _)] at h_td_bound
  exact direction_rate_final_calc m c ε hε_pos hm w (-L_L) u v₀ hu_norm hv₀_norm hR_pos
    (tangentDeviation_scale_neg_eq w L_L hw_ne' hL_ne) hε_norm h_td_bound'

private lemma cutoff_integral_split_to_sides
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (σ₁ σ₂ ε : ℝ)
    (hσ₁_ge : γ.a ≤ σ₁) (hσ₁_lt : σ₁ < σ₂) (hσ₂_le : σ₂ ≤ γ.b)
    (h_left : ∀ t ∈ Ico γ.a σ₁, ε < ‖γ.toFun t - s‖)
    (h_right : ∀ t ∈ Ioc σ₂ γ.b, ε < ‖γ.toFun t - s‖)
    (h_middle : ∀ t ∈ Icc σ₁ σ₂, ‖γ.toFun t - s‖ ≤ ε)
    (h_int_l : IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume γ.a σ₁)
    (h_int_r : IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume σ₂ γ.b) :
    ∫ t in γ.a..γ.b,
      (if ‖γ.toFun t - s‖ > ε
       then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0) =
      (∫ t in γ.a..σ₁, (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t) +
      (∫ t in σ₂..γ.b, (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t) := by
  set F : ℝ → ℂ := fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t with hF_def
  have hae_left_raw : ∀ᵐ t ∂(volume.restrict (Ι γ.a σ₁)),
      (if ‖γ.toFun t - s‖ > ε then F t else 0) = F t := by
    rw [Set.uIoc_of_le hσ₁_ge, ← restrict_Ioo_eq_restrict_Ioc]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact MeasureTheory.ae_of_all _ fun t ht => by
      simp [show ‖γ.toFun t - s‖ > ε from h_left t ⟨ht.1.le, ht.2⟩]
  have hae_left : (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      =ᶠ[ae (volume.restrict (Ι γ.a σ₁))] F := hae_left_raw
  have hae_right_raw : ∀ᵐ t ∂(volume.restrict (Ι σ₂ γ.b)),
      (if ‖γ.toFun t - s‖ > ε then F t else 0) = F t := by
    rw [Set.uIoc_of_le hσ₂_le, ← restrict_Ioo_eq_restrict_Ioc]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact MeasureTheory.ae_of_all _ fun t ht => by
      simp [show ‖γ.toFun t - s‖ > ε from h_right t ⟨ht.1, ht.2.le⟩]
  have hae_right : (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      =ᶠ[ae (volume.restrict (Ι σ₂ γ.b))] F := hae_right_raw
  have heq_mid : EqOn (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      (fun _ => (0 : ℂ)) [[σ₁, σ₂]] := by
    intro t ht
    rw [Set.uIcc_of_le hσ₁_lt.le] at ht
    simp [show ¬(‖γ.toFun t - s‖ > ε) from not_lt.mpr (h_middle t ht)]
  have hint_l := h_int_l.congr_ae hae_left.symm
  have hint_m : IntervalIntegrable
      (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      volume σ₁ σ₂ :=
    (intervalIntegrable_const (c := (0 : ℂ))).congr
      (heq_mid.symm.mono Set.uIoc_subset_uIcc)
  have hint_r := h_int_r.congr_ae hae_right.symm
  have hsplit : ∫ t in γ.a..γ.b, (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) t =
      (∫ t in γ.a..σ₁, (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) t) +
      (∫ t in σ₁..σ₂, (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) t) +
      (∫ t in σ₂..γ.b, (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) t) := by
    have h_σ₁_b := intervalIntegral.integral_add_adjacent_intervals hint_m hint_r
    have h_a_b := intervalIntegral.integral_add_adjacent_intervals hint_l (hint_m.trans hint_r)
    rw [← h_σ₁_b] at h_a_b; rw [← h_a_b, add_assoc]
  rw [hsplit]
  have h_mid_zero : ∫ t in σ₁..σ₂,
      (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) t = 0 := by
    rw [intervalIntegral.integral_congr heq_mid, intervalIntegral.integral_zero]
  rw [h_mid_zero, add_zero,
    intervalIntegral.integral_congr_ae_restrict hae_left,
    intervalIntegral.integral_congr_ae_restrict hae_right]

private lemma cutoff_zpow_integral_eq_boundary
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (σ₁ σ₂ ε : ℝ)
    (hσ₁_ge : γ.a ≤ σ₁) (hσ₁_lt : σ₁ < σ₂) (hσ₂_le : σ₂ ≤ γ.b)
    (hε_pos : 0 < ε)
    (hσ₁_val : ‖γ.toFun σ₁ - s‖ = ε) (hσ₂_val : ‖γ.toFun σ₂ - s‖ = ε)
    (h_left : ∀ t ∈ Ico γ.a σ₁, ε < ‖γ.toFun t - s‖)
    (h_right : ∀ t ∈ Ioc σ₂ γ.b, ε < ‖γ.toFun t - s‖)
    (h_middle : ∀ t ∈ Icc σ₁ σ₂, ‖γ.toFun t - s‖ ≤ ε)
    (h_int_l : IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume γ.a σ₁)
    (h_int_r : IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume σ₂ γ.b) :
    ∫ t in γ.a..γ.b,
      (if ‖γ.toFun t - s‖ > ε
       then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0) =
      ((γ.toFun σ₁ - s) ^ (1 - (m : ℤ)) - (γ.toFun σ₂ - s) ^ (1 - (m : ℤ))) /
        ((1 : ℂ) - ↑(m : ℤ)) := by
  have hn_ne : (-(m : ℤ) : ℤ) ≠ -1 := by omega
  have hne_left : ∀ t ∈ Icc γ.a σ₁, γ.toFun t ≠ s := by
    intro t ht habs
    rcases eq_or_lt_of_le ht.2 with rfl | ht_lt
    · rw [habs, sub_self, norm_zero] at hσ₁_val; linarith
    · have := h_left t ⟨ht.1, ht_lt⟩; rw [habs, sub_self, norm_zero] at this; linarith
  have hne_right : ∀ t ∈ Icc σ₂ γ.b, γ.toFun t ≠ s := by
    intro t ht habs
    rcases eq_or_lt_of_le ht.1 with rfl | ht_gt
    · rw [habs, sub_self, norm_zero] at hσ₂_val; linarith
    · have := h_right t ⟨ht_gt, ht.2⟩; rw [habs, sub_self, norm_zero] at this; linarith
  set F : ℝ → ℂ := fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t
  have hsplit := cutoff_integral_split_to_sides γ s m σ₁ σ₂ ε
    hσ₁_ge hσ₁_lt hσ₂_le h_left h_right h_middle h_int_l h_int_r
  rw [hsplit]
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  set E := (γ.toPiecewiseC1Curve.partition : Set ℝ)
  have hE_count : E.Countable := γ.toPiecewiseC1Curve.partition.countable_toSet
  have hγ_diff : ∀ t ∈ Icc γ.a γ.b, t ∉ E → DifferentiableAt ℝ γ.toFun t :=
    fun t ht hne => γ.toPiecewiseC1Curve.smooth_off_partition t ht hne
  have hftc_l := integral_zpow_comp_sub_mul_deriv hn_ne hσ₁_ge
    (hγ_cont.mono (Icc_subset_Icc le_rfl (hσ₁_lt.le.trans hσ₂_le))) hne_left
    E hE_count (Set.inter_subset_right) (fun t ht hne =>
      hγ_diff t ⟨ht.1.le, ht.2.le.trans (hσ₁_lt.le.trans hσ₂_le)⟩ hne) h_int_l
  have hftc_r := integral_zpow_comp_sub_mul_deriv hn_ne hσ₂_le
    (hγ_cont.mono (Icc_subset_Icc (hσ₁_ge.trans hσ₁_lt.le) le_rfl)) hne_right
    E hE_count (Set.inter_subset_right) (fun t ht hne =>
      hγ_diff t ⟨(hσ₁_ge.trans hσ₁_lt.le).trans ht.1.le, ht.2.le⟩ hne) h_int_r
  rw [hftc_l, hftc_r, hγ_closed]
  have hint_eq : (-(m : ℤ) + 1 : ℤ) = 1 - (m : ℤ) := by omega
  simp only [hint_eq]
  have hcast : (↑(1 - (m : ℤ)) : ℂ) = 1 - ↑↑m := by push_cast; ring
  simp only [hcast, Int.cast_natCast]; ring

private lemma exit_time_tendsto_right
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (_h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (σ₂ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hσ₂_props : ∀ ε ∈ Ioo 0 δ, t₀ < σ₂ ε ∧ σ₂ ε ≤ γ.b ∧
      ‖γ.toFun (σ₂ ε) - s‖ = ε ∧
      ∀ t ∈ Icc t₀ (σ₂ ε), ‖γ.toFun t - s‖ ≤ ε) :
    Tendsto σ₂ (𝓝[>] 0) (𝓝[>] t₀) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨l, r, hl_lt, hr_gt, hl_ge_a, hr_le_b, _, hg_mono⟩ :=
      _root_.piecewiseC1Immersion_norm_strictMono_near_crossing γ s t₀ ht₀ hcross
    have hη_r : 0 < min η (r - t₀) := lt_min hη (by linarith)
    set t₁ := t₀ + min η (r - t₀) / 2 with ht₁_def
    have ht₁_gt : t₀ < t₁ := by simp only [ht₁_def]; linarith
    have ht₁_lt_r : t₁ < r := by simp only [ht₁_def]; linarith [min_le_right η (r - t₀)]
    have ht₁_mem : t₁ ∈ Icc t₀ r := ⟨ht₁_gt.le, ht₁_lt_r.le⟩
    have hg_t₁ : 0 < ‖γ.toFun t₁ - s‖ := by
      have h_lt := hg_mono ⟨le_rfl, hr_gt.le⟩ ht₁_mem ht₁_gt
      have : ‖γ.toFun t₀ - s‖ = 0 := by rw [hcross, sub_self, norm_zero]
      linarith
    set ε₀ := min ‖γ.toFun t₁ - s‖ δ
    have hε₀_pos : 0 < ε₀ := lt_min hg_t₁ hδ
    filter_upwards [Ioo_mem_nhdsGT hε₀_pos] with ε ⟨hε_pos, hε_lt⟩
    have hε_Ioo : ε ∈ Ioo 0 δ := ⟨hε_pos, lt_of_lt_of_le hε_lt (min_le_right _ _)⟩
    obtain ⟨hσ₂_gt, hσ₂_le, hσ₂_norm, hσ₂_mid⟩ := hσ₂_props ε hε_Ioo
    rw [dist_eq_norm, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ₂_gt)]
    have hε_lt_t₁ : ε < ‖γ.toFun t₁ - s‖ := lt_of_lt_of_le hε_lt (min_le_left _ _)
    by_contra h_not_lt
    push Not at h_not_lt
    have ht₁_le_σ₂ : t₁ ≤ σ₂ ε := by
      simp only [ht₁_def]; linarith [min_le_left η (r - t₀)]
    have := hσ₂_mid t₁ ⟨ht₁_gt.le, ht₁_le_σ₂⟩
    linarith
  · filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact (hσ₂_props ε hε).1

private lemma exit_time_tendsto_left
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (_h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (σ₁ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hσ₁_props : ∀ ε ∈ Ioo 0 δ, σ₁ ε < t₀ ∧ γ.a ≤ σ₁ ε ∧
      ‖γ.toFun (σ₁ ε) - s‖ = ε ∧
      ∀ t ∈ Icc (σ₁ ε) t₀, ‖γ.toFun t - s‖ ≤ ε) :
    Tendsto σ₁ (𝓝[>] 0) (𝓝[<] t₀) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨l, r, hl_lt, hr_gt, hl_ge_a, hr_le_b, hg_anti, _⟩ :=
      _root_.piecewiseC1Immersion_norm_strictMono_near_crossing γ s t₀ ht₀ hcross
    have hη_l : 0 < min η (t₀ - l) := lt_min hη (by linarith)
    set t₁ := t₀ - min η (t₀ - l) / 2 with ht₁_def
    have ht₁_lt : t₁ < t₀ := by simp only [ht₁_def]; linarith
    have ht₁_gt_l : l < t₁ := by simp only [ht₁_def]; linarith [min_le_right η (t₀ - l)]
    have ht₁_mem : t₁ ∈ Icc l t₀ := ⟨ht₁_gt_l.le, ht₁_lt.le⟩
    have hg_t₁ : 0 < ‖γ.toFun t₁ - s‖ := by
      have h1 := hg_anti ht₁_mem ⟨hl_lt.le, le_rfl⟩ ht₁_lt
      simp only [hcross, sub_self, norm_zero] at h1; exact h1
    set ε₀ := min ‖γ.toFun t₁ - s‖ δ
    have hε₀_pos : 0 < ε₀ := lt_min hg_t₁ hδ
    filter_upwards [Ioo_mem_nhdsGT hε₀_pos] with ε ⟨hε_pos, hε_lt⟩
    have hε_Ioo : ε ∈ Ioo 0 δ := ⟨hε_pos, lt_of_lt_of_le hε_lt (min_le_right _ _)⟩
    obtain ⟨hσ₁_lt, hσ₁_ge, hσ₁_norm, hσ₁_mid⟩ := hσ₁_props ε hε_Ioo
    rw [dist_comm, dist_eq_norm, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ₁_lt)]
    have hε_lt_t₁ : ε < ‖γ.toFun t₁ - s‖ := lt_of_lt_of_le hε_lt (min_le_left _ _)
    by_contra h_not_lt
    push Not at h_not_lt
    have hσ₁_le_t₁ : σ₁ ε ≤ t₁ := by
      simp only [ht₁_def]; linarith [min_le_left η (t₀ - l)]
    have := hσ₁_mid t₁ ⟨hσ₁_le_t₁, ht₁_lt.le⟩
    linarith
  · filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact (hσ₁_props ε hε).1

private lemma zpow_mul_deriv_intervalIntegrable
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (c d : ℝ) (hcd : c ≤ d)
    (hc_ge : γ.a ≤ c) (hd_le : d ≤ γ.b)
    (hne : ∀ t ∈ Icc c d, γ.toFun t ≠ s) :
    IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume c d := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hcont_zpow : ContinuousOn (fun t => (γ.toFun t - s) ^ (-(m : ℤ)))
      (Set.uIcc c d) := by
    rw [Set.uIcc_of_le hcd]
    exact continuousOn_zpow_comp_sub
      (hγ_cont.mono (Icc_subset_Icc hc_ge hd_le)) hne
  have hderiv_int : IntervalIntegrable (deriv γ.toFun) MeasureTheory.volume c d :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
      (piecewiseC1Immersion_deriv_bounded γ)).mono_set
      ((Set.uIcc_of_le hcd ▸ Set.uIcc_of_le (le_of_lt γ.hab) ▸
        Icc_subset_Icc hc_ge hd_le) : [[c, d]] ⊆ [[γ.a, γ.b]])
  exact hderiv_int.continuousOn_mul hcont_zpow

private lemma immersion_right_deriv_limit
    (γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L) := by
  by_cases h : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · exact γ.right_deriv_limit t₀ h ht₀.2
  · exact ⟨_, γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) h,
      (γ.toPiecewiseC1Curve.deriv_continuous_off_partition t₀ ht₀ h).tendsto.mono_left
        nhdsWithin_le_nhds⟩

private lemma immersion_left_deriv_limit
    (γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L) := by
  by_cases h : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · exact γ.left_deriv_limit t₀ h ht₀.1
  · exact ⟨_, γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) h,
      (γ.toPiecewiseC1Curve.deriv_continuous_off_partition t₀ ht₀ h).tendsto.mono_left
        nhdsWithin_le_nhds⟩

private lemma angle_at_crossing_arg_relation
    (γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (L_R L_L : ℂ) (_hL_R_ne : L_R ≠ 0) (hL_L_ne : L_L ≠ 0)
    (htend_R : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_R))
    (htend_L : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_L)) :
    ∃ n_angle : ℤ, L_R.arg - (-L_L).arg =
      _root_.angleAtCrossing γ t₀ ht₀ + ↑n_angle * (2 * Real.pi) := by
  by_cases hp : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · refine ⟨0, ?_⟩
    simp only [Int.cast_zero, zero_mul, add_zero]
    unfold angleAtCrossing
    rw [dif_pos hp]
    have hL_R_eq := tendsto_nhds_unique htend_R
      (Classical.choose_spec (γ.right_deriv_limit t₀ hp ht₀.2)).2
    have hL_L_eq := tendsto_nhds_unique htend_L
      (Classical.choose_spec (γ.left_deriv_limit t₀ hp ht₀.1)).2
    rw [hL_R_eq, hL_L_eq]
  · rw [angleAtCrossing_smooth γ t₀ ht₀ hp]
    have hL_eq : L_R = L_L := by
      have hcont := γ.toPiecewiseC1Curve.deriv_continuous_off_partition t₀ ht₀ hp
      exact (tendsto_nhds_unique htend_R
        (hcont.tendsto.mono_left nhdsWithin_le_nhds)).trans
        (tendsto_nhds_unique htend_L
          (hcont.tendsto.mono_left nhdsWithin_le_nhds)).symm
    rw [hL_eq]
    by_cases him : 0 < L_L.im
    · exact ⟨0, by rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him]; push_cast; ring⟩
    · by_cases him' : L_L.im < 0
      · exact ⟨-1, by rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him']; push_cast; ring⟩
      · have him_eq : L_L.im = 0 := le_antisymm (not_lt.mp him) (not_lt.mp him')
        have hre_ne : L_L.re ≠ 0 := fun h => hL_L_ne (Complex.ext h him_eq)
        rcases lt_or_gt_of_ne hre_ne with hre | hre
        · exact ⟨0, by rw [Complex.arg_neg_eq_arg_sub_pi_iff.mpr (Or.inr ⟨him_eq, hre⟩)]
                       push_cast; ring⟩
        · exact ⟨-1, by rw [Complex.arg_neg_eq_arg_add_pi_iff.mpr (Or.inr ⟨him_eq, hre⟩)]
                        push_cast; ring⟩

private lemma cutoff_zpow_direction_and_ftc
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (L_R L_L : ℂ) (hL_R_ne : L_R ≠ 0) (hL_L_ne : L_L ≠ 0)
    (htend_R : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_R))
    (htend_L : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_L))
    (σ₁ σ₂ : ℝ → ℝ) (δ : ℝ) (hδ_pos : 0 < δ)
    (hprops : ∀ ε, ε ∈ Ioo 0 δ →
      γ.a ≤ σ₁ ε ∧ σ₁ ε < t₀ ∧ t₀ < σ₂ ε ∧ σ₂ ε ≤ γ.b ∧
      ‖γ.toFun (σ₁ ε) - s‖ = ε ∧ ‖γ.toFun (σ₂ ε) - s‖ = ε ∧
      (∀ t ∈ Ico γ.a (σ₁ ε), ε < ‖γ.toFun t - s‖) ∧
      (∀ t ∈ Ioc (σ₂ ε) γ.b, ε < ‖γ.toFun t - s‖) ∧
      (∀ t ∈ Icc (σ₁ ε) (σ₂ ε), ‖γ.toFun t - s‖ ≤ ε))
    (hIoo_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 δ) :
    ((fun ε => ‖(γ.toFun (σ₂ ε) - s) / (↑‖γ.toFun (σ₂ ε) - s‖ : ℂ) -
        L_R / ↑‖L_R‖‖) =o[𝓝[>] (0 : ℝ)] fun ε => ε ^ (m - 1 : ℕ)) ∧
    ((fun ε => ‖(γ.toFun (σ₁ ε) - s) / (↑‖γ.toFun (σ₁ ε) - s‖ : ℂ) -
        (-L_L / ↑‖L_L‖)‖) =o[𝓝[>] (0 : ℝ)] fun ε => ε ^ (m - 1 : ℕ)) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in γ.a..γ.b,
        (if ‖γ.toFun t - s‖ > ε
         then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0) =
        ((γ.toFun (σ₁ ε) - s) ^ (1 - (m : ℤ)) -
          (γ.toFun (σ₂ ε) - s) ^ (1 - (m : ℤ))) /
          ((1 : ℂ) - ↑(m : ℤ))) := by
  have hσ₂_tendsto : Tendsto σ₂ (𝓝[>] 0) (𝓝[>] t₀) :=
    exit_time_tendsto_right γ s t₀ ht₀ hcross h_unique σ₂ δ hδ_pos
      (fun ε hε => ⟨(hprops ε hε).2.2.1, (hprops ε hε).2.2.2.1,
        (hprops ε hε).2.2.2.2.2.1,
        fun t ht => (hprops ε hε).2.2.2.2.2.2.2.2
          t ⟨le_trans (le_of_lt (hprops ε hε).2.1) ht.1, ht.2⟩⟩)
  have hσ₁_tendsto : Tendsto σ₁ (𝓝[>] 0) (𝓝[<] t₀) :=
    exit_time_tendsto_left γ s t₀ ht₀ hcross h_unique σ₁ δ hδ_pos
      (fun ε hε => ⟨(hprops ε hε).2.1, (hprops ε hε).1,
        (hprops ε hε).2.2.2.2.1,
        fun t ht => (hprops ε hε).2.2.2.2.2.2.2.2
          t ⟨ht.1, le_trans ht.2 (le_of_lt (hprops ε hε).2.2.1)⟩⟩)
  refine ⟨?_, ?_, ?_⟩
  · exact direction_rate_from_flatness_right γ s m hm t₀ ht₀ hcross h_flat
      L_R hL_R_ne htend_R σ₂
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.2.1)
      hσ₂_tendsto
  · exact direction_rate_from_flatness_left γ s m hm t₀ ht₀ hcross h_flat
      L_L hL_L_ne htend_L σ₁
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.1)
      hσ₁_tendsto
  · filter_upwards [hIoo_ev] with ε hε
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hprops ε hε
    have hne_left : ∀ t ∈ Icc γ.a (σ₁ ε), γ.toFun t ≠ s := by
      intro t ht habs
      rcases eq_or_lt_of_le ht.2 with rfl | ht_lt
      · rw [habs, sub_self, norm_zero] at h5; linarith [hε.1]
      · have := h7 t ⟨ht.1, ht_lt⟩; rw [habs, sub_self, norm_zero] at this; linarith [hε.1]
    have hne_right : ∀ t ∈ Icc (σ₂ ε) γ.b, γ.toFun t ≠ s := by
      intro t ht habs
      rcases eq_or_lt_of_le ht.1 with rfl | ht_gt
      · rw [habs, sub_self, norm_zero] at h6; linarith [hε.1]
      · have := h8 t ⟨ht_gt, ht.2⟩; rw [habs, sub_self, norm_zero] at this; linarith [hε.1]
    exact cutoff_zpow_integral_eq_boundary γ s m hm hγ_closed
      (σ₁ ε) (σ₂ ε) ε h1 (lt_trans h2 h3) h4 hε.1 h5 h6 h7 h8 h9
      (zpow_mul_deriv_intervalIntegrable γ s m γ.a (σ₁ ε) h1 le_rfl
        ((lt_trans h2 h3).le.trans h4) hne_left)
      (zpow_mul_deriv_intervalIntegrable γ s m (σ₂ ε) γ.b h4
        (h1.trans (lt_trans h2 h3).le) le_rfl hne_right)

/-- Infrastructure for the FTC-based proof of L4. Given a piecewise C¹ immersion
crossing `s` at `t₀` with flatness of order `m`, this provides:
- Exit time functions `wR, wL` with `‖w(ε)‖ = ε` on the ε-sphere
- Direction limits `uR, uL` on the unit circle related to `angleAtCrossing`
- Direction convergence rates `o(ε^{m-1})` from flatness
- FTC reduction: the cutoff integral equals `(wL^{1-m} - wR^{1-m}) / (1-m)` -/
lemma cutoff_zpow_infrastructure
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m) :
    ∃ (wR wL : ℝ → ℂ) (uR uL : ℂ),
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖wR ε‖ = ε) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖wL ε‖ = ε) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), wR ε ≠ 0) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), wL ε ≠ 0) ∧
      (‖uR‖ = 1) ∧ (‖uL‖ = 1) ∧
      (∃ n_angle : ℤ, arg uR - arg uL =
        _root_.angleAtCrossing γ t₀ ht₀ + ↑n_angle * (2 * Real.pi)) ∧
      ((fun ε => ‖wR ε / (↑‖wR ε‖ : ℂ) - uR‖) =o[𝓝[>] (0 : ℝ)]
        fun ε => ε ^ (m - 1 : ℕ)) ∧
      ((fun ε => ‖wL ε / (↑‖wL ε‖ : ℂ) - uL‖) =o[𝓝[>] (0 : ℝ)]
        fun ε => ε ^ (m - 1 : ℕ)) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∫ t in γ.a..γ.b,
          (if ‖γ.toFun t - s‖ > ε
           then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0) =
          (wL ε ^ (1 - (m : ℤ)) - wR ε ^ (1 - (m : ℤ))) /
            ((1 : ℂ) - ↑(m : ℤ))) := by
  obtain ⟨L_R, hL_R_ne, htend_R⟩ := immersion_right_deriv_limit γ t₀ ht₀
  obtain ⟨L_L, hL_L_ne, htend_L⟩ := immersion_left_deriv_limit γ t₀ ht₀
  obtain ⟨δ, hδ_pos, h_exit⟩ :=
    _root_.exists_cutoff_boundary_times γ s t₀ ht₀ hcross h_unique
  let σ₁ := fun ε => if h : ε ∈ Ioo 0 δ then (h_exit ε h).choose else t₀
  let σ₂ := fun ε => if h : ε ∈ Ioo 0 δ then (h_exit ε h).choose_spec.choose else t₀
  have hprops : ∀ ε (hε : ε ∈ Ioo 0 δ),
      γ.a ≤ σ₁ ε ∧ σ₁ ε < t₀ ∧ t₀ < σ₂ ε ∧ σ₂ ε ≤ γ.b ∧
      ‖γ.toFun (σ₁ ε) - s‖ = ε ∧ ‖γ.toFun (σ₂ ε) - s‖ = ε ∧
      (∀ t ∈ Ico γ.a (σ₁ ε), ε < ‖γ.toFun t - s‖) ∧
      (∀ t ∈ Ioc (σ₂ ε) γ.b, ε < ‖γ.toFun t - s‖) ∧
      (∀ t ∈ Icc (σ₁ ε) (σ₂ ε), ‖γ.toFun t - s‖ ≤ ε) := by
    intro ε hε
    simp only [σ₁, σ₂, hε, dif_pos]
    exact (h_exit ε hε).choose_spec.choose_spec
  have hIoo_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ_pos
  let wR : ℝ → ℂ := fun ε => γ.toFun (σ₂ ε) - s
  let wL : ℝ → ℂ := fun ε => γ.toFun (σ₁ ε) - s
  let uR : ℂ := L_R / ↑‖L_R‖
  let uL : ℂ := -L_L / ↑‖L_L‖
  obtain ⟨h_rate_R, h_rate_L, h_ftc⟩ :=
    cutoff_zpow_direction_and_ftc γ s m hm t₀ ht₀ hcross
    h_unique hγ_closed h_flat L_R L_L hL_R_ne hL_L_ne htend_R htend_L σ₁ σ₂ δ hδ_pos
    hprops hIoo_ev
  refine ⟨wR, wL, uR, uL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_rate_R, h_rate_L, h_ftc⟩
  · exact hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.2.1
  · exact hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.1
  · filter_upwards [hIoo_ev] with ε hε
    change γ.toFun (σ₂ ε) - s ≠ 0
    have h_norm := (hprops ε hε).2.2.2.2.2.1
    exact sub_ne_zero.mpr (fun h => by rw [h, sub_self, norm_zero] at h_norm; linarith [hε.1])
  · filter_upwards [hIoo_ev] with ε hε
    change γ.toFun (σ₁ ε) - s ≠ 0
    have h_norm := (hprops ε hε).2.2.2.2.1
    exact sub_ne_zero.mpr (fun h => by rw [h, sub_self, norm_zero] at h_norm; linarith [hε.1])
  · change ‖L_R / ↑‖L_R‖‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hL_R_ne),
      div_self (norm_ne_zero_iff.mpr hL_R_ne)]
  · change ‖-L_L / ↑‖L_L‖‖ = 1
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (norm_pos_iff.mpr hL_L_ne), div_self (norm_ne_zero_iff.mpr hL_L_ne)]
  · have h_arg_uR : uR.arg = L_R.arg := by
      change (L_R / ↑‖L_R‖).arg = L_R.arg
      rw [div_eq_inv_mul, ← Complex.ofReal_inv,
        Complex.arg_real_mul L_R (inv_pos.mpr (norm_pos_iff.mpr hL_R_ne))]
    have h_arg_uL : uL.arg = (-L_L).arg := by
      change (-L_L / ↑‖L_L‖).arg = (-L_L).arg
      rw [div_eq_inv_mul, ← Complex.ofReal_inv,
        Complex.arg_real_mul (-L_L) (inv_pos.mpr (norm_pos_iff.mpr hL_L_ne))]
    rw [h_arg_uR, h_arg_uL]
    exact angle_at_crossing_arg_relation γ t₀ ht₀ L_R L_L hL_R_ne hL_L_ne htend_R htend_L

end GeneralizedResidueTheory
