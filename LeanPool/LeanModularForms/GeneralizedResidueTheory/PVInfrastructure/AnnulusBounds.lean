/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.GammaAnalysis
import LeanPool.LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.RemainderAnalysis
import LeanPool.LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.StepBounds

/-!
# PV Infrastructure: Annulus Bounds

Measure-theoretic and analytic bounds on annular regions around
crossing points, used in the dyadic PV convergence proof.

## Main Results

* `annulus_t_measure_bound` — t-measure of gamma-annulus
* `remainder_integral_bound_on_annulus` — remainder integral
    over annulus is O(epsilon)
* `annulus_symmDiff_measure_bound` — symmetric difference
    between gamma-annulus and linear-model annulus
* `singular_annulus_bound_explicit` — epsilon-independent
    bound on singular annulus integral
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

private instance : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass

noncomputable section

lemma annulus_t_measure_bound {γ : ℝ → ℂ}
    {a b t₀ : ℝ} {L : ℂ} {ε₁ ε₂ δ₁ : ℝ}
    (hL : L ≠ 0) (hε₁_pos : 0 < ε₁)
    (h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ →
      ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (h_localize : ∀ t ∈ Set.Icc a b,
      ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₁ δ₁)
    (t : ℝ) (ht_ab : t ∈ Set.Icc a b)
    (ht_ne : t ≠ t₀)
    (_hγ_lower : ε₂ < ‖γ t - γ t₀‖)
    (hγ_upper : ‖γ t - γ t₀‖ ≤ ε₁) :
    |t - t₀| ≤ 2 * ε₁ / ‖L‖ := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have ht_local := h_localize t ht_ab hγ_upper
  have ht_pos : 0 < |t - t₀| :=
    abs_pos.mpr (sub_ne_zero.mpr ht_ne)
  have ht_lt_δ₁ : |t - t₀| < δ₁ :=
    lt_of_lt_of_le ht_local (min_le_right _ _)
  exact t_bound_from_gamma_annulus hL hε₁_pos
    h_lower t ht_pos ht_lt_δ₁ hγ_upper

/-- Points in the annulus `{t | ε₂ < ‖γ t - γ t₀‖ ≤ ε₁}` within `[a,b]` have
    `|t - t₀| ≤ 2ε₁/‖L‖`, so the indicator integrand is zero far from `t₀`. -/
private lemma remainder_annulus_zero_of_far
    {γ : ℝ → ℂ} {a b t₀ : ℝ}
    {δ₁ ε₁ ε₂ : ℝ} {L : ℂ}
    (hL : L ≠ 0) (hε₁_pos : 0 < ε₁) (hε₂_pos : 0 < ε₂)
    (h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ →
      ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (h_localize : ∀ t ∈ Set.Icc a b,
      ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₁ δ₁)
    (hab : a < b) {r : ℝ → ℂ}
    (t : ℝ) (ht : t ∈ Set.uIoc a b)
    (h_far : 2 * ε₁ / ‖L‖ < |t - t₀|) :
    (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
      then r t else 0) = 0 := by
  by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
  · exfalso
    have ht_in_Icc : t ∈ Set.Icc a b := by
      rw [Set.uIoc_eq_union] at ht
      rcases ht with ht_ab | ht_ba
      · exact Set.Ioc_subset_Icc_self ht_ab
      · rw [Set.Ioc_eq_empty_of_le hab.le] at ht_ba
        exact absurd ht_ba (Set.notMem_empty t)
    by_cases ht_eq : t = t₀
    · simp only [ht_eq, sub_self, norm_zero] at hcond
      exact absurd hcond.1 (not_lt.mpr hε₂_pos.le)
    exact not_lt.mpr
      (annulus_t_measure_bound hL hε₁_pos h_lower
        (fun s hs hγs => by simp only [min_self]
                            exact lt_of_lt_of_le (h_localize s hs hγs) (min_le_right _ _))
        t ht_in_Icc ht_eq hcond.1 hcond.2) h_far
  · simp only [hcond, ↓reduceIte]

/-- Pointwise bound: the indicator integrand is bounded by `max 0 C` on `Ι a b`. -/
private lemma remainder_annulus_pw_bound
    {γ : ℝ → ℂ} {a b t₀ : ℝ}
    {C δ₀ δ₁ ε₁ ε₂ : ℝ}
    (hε₂_pos : 0 < ε₂)
    (hr_bounded : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₀ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ C)
    (h_localize : ∀ t ∈ Set.Icc a b,
      ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ₁)
    (hab : a < b) (t : ℝ) (ht : t ∈ Set.uIoc a b) :
    ‖if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
      then (γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹
      else 0‖ ≤ max 0 C := by
  by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
  · rw [if_pos hcond]
    have ht_in_Icc : t ∈ Set.Icc a b := by
      rw [Set.uIoc_eq_union] at ht; rcases ht with h | h
      · exact Set.Ioc_subset_Icc_self h
      · exact absurd (Set.Ioc_eq_empty_of_le hab.le ▸ h) (Set.notMem_empty t)
    by_cases ht_eq : t = t₀
    · simp only [ht_eq, sub_self, norm_zero] at hcond
      exact absurd hcond.1 (not_lt.mpr hε₂_pos.le)
    have ht_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr ht_eq)
    exact le_trans (hr_bounded t ht_pos
      (lt_of_lt_of_le (h_localize t ht_in_Icc hcond.2) (min_le_left _ _)))
      (le_max_right 0 C)
  · simp only [hcond, ↓reduceIte, norm_zero, le_max_iff, le_refl, true_or]

lemma remainder_integral_bound_on_annulus
    {γ : ℝ → ℂ} {a b t₀ : ℝ}
    {C δ₀ δ₁ ε₁ ε₂ : ℝ} {L : ℂ}
    (hL : L ≠ 0) (hε₁_pos : 0 < ε₁)
    (hε₂_pos : 0 < ε₂)
    (hr_bounded : ∀ t, 0 < |t - t₀| →
      |t - t₀| < δ₀ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t -
        (↑(t - t₀))⁻¹‖ ≤ C)
    (h_lower : ∀ t, 0 < |t - t₀| →
      |t - t₀| < δ₁ →
      ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (h_localize : ∀ t ∈ Set.Icc a b,
      ‖γ t - γ t₀‖ ≤ ε₁ →
      |t - t₀| < min δ₀ δ₁)
    (hat₀ : t₀ ∈ Set.Ioo a b) :
    let r := fun t =>
      (γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹
    ‖∫ t in a..b,
      if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
        then r t else 0‖ ≤
      max 0 C * (4 * ε₁ / ‖L‖) := by
  intro r
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hab : a < b :=
    (Set.mem_Ioo.mp hat₀).1.trans_le (le_of_lt (Set.mem_Ioo.mp hat₀).2)
  have h_loc_δ₁ : ∀ t ∈ Set.Icc a b,
      ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₁ δ₁ := by
    intro s hs hγs; simp only [min_self]
    exact lt_of_lt_of_le (h_localize s hs hγs) (min_le_right _ _)
  set R := 2 * ε₁ / ‖L‖
  have hR_pos : 0 < R := by positivity
  set Icontain := Set.Icc (t₀ - R) (t₀ + R)
  set g_comp : ℝ → ℝ := Icontain.indicator (fun _ => max 0 C)
  have hg_int : IntervalIntegrable g_comp volume a b := by
    constructor <;>
      exact (MeasureTheory.integrableOn_const
        (hs := measure_Ioc_lt_top.ne)).indicator measurableSet_Icc
  have h_pw_le : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b →
      ‖if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
        then r t else 0‖ ≤ g_comp t := by
    apply Filter.Eventually.of_forall; intro t ht
    simp only [g_comp, Set.indicator]
    by_cases ht_in : t ∈ Icontain
    · simp only [ht_in, ↓reduceIte]
      exact remainder_annulus_pw_bound hε₂_pos hr_bounded h_localize hab
        t (Set.uIoc_of_le hab.le ▸ ht)
    · simp only [ht_in, ↓reduceIte]
      have h_far : R < |t - t₀| := by
        simp only [Icontain, Set.mem_Icc, not_and_or, not_le] at ht_in
        rcases ht_in with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [remainder_annulus_zero_of_far hL hε₁_pos hε₂_pos h_lower h_loc_δ₁ hab
        t (Set.uIoc_of_le hab.le ▸ ht) h_far, norm_zero]
  calc ‖∫ t in a..b,
      if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
        then r t else 0‖
      ≤ ∫ t in a..b, g_comp t :=
        intervalIntegral.norm_integral_le_of_norm_le hab.le h_pw_le hg_int
    _ ≤ max 0 C * (4 * ε₁ / ‖L‖) := by
        rw [intervalIntegral.integral_of_le hab.le,
          MeasureTheory.integral_indicator measurableSet_Icc,
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
        apply mul_le_mul_of_nonneg_left _ (le_max_left 0 C)
        unfold MeasureTheory.Measure.real
        apply ENNReal.toReal_le_of_le_ofReal (by positivity)
        calc (volume.restrict (Set.Ioc a b)) Icontain
            ≤ volume Icontain := MeasureTheory.Measure.restrict_apply_le _ _
          _ = ENNReal.ofReal ((t₀ + R) - (t₀ - R)) := Real.volume_Icc
          _ = ENNReal.ofReal (4 * ε₁ / ‖L‖) := by simp only [R]; ring_nf

lemma norm_linear_approx_bound {γ : ℝ → ℂ}
    {t₀ : ℝ} {L : ℂ} {K₀ δ₀ : ℝ}
    (h_quad : ∀ t, |t - t₀| < δ₀ →
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤
        K₀ * |t - t₀| ^ 2)
    {t : ℝ} (ht : |t - t₀| < δ₀) :
    abs (‖γ t - γ t₀‖ - ‖L‖ * |t - t₀|) ≤
      K₀ * |t - t₀|^2 := by
  have h1 :
    ‖γ t - γ t₀ - (t - t₀) • L‖ ≤
      K₀ * |t - t₀|^2 := h_quad t ht
  have h2 :
    |‖γ t - γ t₀‖ - ‖(t - t₀) • L‖| ≤
      ‖γ t - γ t₀ - (t - t₀) • L‖ :=
    abs_norm_sub_norm_le _ _
  have h3 : ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ :=
    norm_smul (t - t₀) L
  rw [h3, mul_comm] at h2
  exact le_trans h2 h1

lemma volume_shell_le {t₀ r₁ r₂ : ℝ}
    (hr : r₁ ≤ r₂) :
    volume {t : ℝ |
      r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ≤
      ENNReal.ofReal (2 * (r₂ - r₁)) := by
  have h_sub :
      {t : ℝ |
        r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ⊆
      Set.Ico (t₀ - r₂) (t₀ - r₁) ∪
      Set.Ioc (t₀ + r₁) (t₀ + r₂) := by
    intro t ⟨h_lower, h_upper⟩
    by_cases ht : t ≥ t₀
    · right
      have habs : |t - t₀| = t - t₀ :=
        abs_of_nonneg (sub_nonneg.mpr ht)
      rw [habs] at h_lower h_upper
      exact ⟨by linarith, by linarith⟩
    · left
      push Not at ht
      have habs : |t - t₀| = -(t - t₀) :=
        abs_of_neg (sub_neg.mpr ht)
      rw [habs] at h_lower h_upper
      exact ⟨by linarith, by linarith⟩
  calc volume {t : ℝ |
      r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂}
      ≤ volume (Set.Ico (t₀ - r₂) (t₀ - r₁) ∪
          Set.Ioc (t₀ + r₁) (t₀ + r₂)) :=
        MeasureTheory.measure_mono h_sub
    _ ≤ volume (Set.Ico (t₀ - r₂) (t₀ - r₁)) +
        volume (Set.Ioc (t₀ + r₁) (t₀ + r₂)) :=
        MeasureTheory.measure_union_le _ _
    _ = ENNReal.ofReal (r₂ - r₁) +
        ENNReal.ofReal (r₂ - r₁) := by
        simp only [Real.volume_Ico,
          Real.volume_Ioc]; ring_nf
    _ = ENNReal.ofReal (2 * (r₂ - r₁)) := by
        rw [← ENNReal.ofReal_add
          (by linarith) (by linarith)]; ring_nf

/-- If `g` and `x` are within `e` and straddle a threshold `ε`, then `|x - ε| ≤ e`. -/
private lemma abs_sub_threshold_le {g x ε e : ℝ} (h_approx : |g - x| ≤ e)
    (h_between : (g ≤ ε ∧ ε ≤ x) ∨ (x ≤ ε ∧ ε ≤ g)) : |x - ε| ≤ e := by
  rw [abs_le] at h_approx ⊢
  rcases h_between with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

lemma symmDiff_subset_boundaryLayers
    {g x e ε₁ ε₂ : ℝ}
    (h_approx : |g - x| ≤ e)
    (h_xor :
      Xor (ε₂ < g ∧ g ≤ ε₁)
           (ε₂ < x ∧ x ≤ ε₁)) :
    |x - ε₂| ≤ e ∨ |x - ε₁| ≤ e := by
  rcases h_xor with
    ⟨⟨hg_lower, hg_upper⟩, hnotB⟩ |
    ⟨⟨hx_lower, hx_upper⟩, hnotA⟩
  · by_cases hx_le_ε₂ : x ≤ ε₂
    · exact Or.inl (abs_sub_threshold_le h_approx (Or.inr ⟨hx_le_ε₂, by linarith⟩))
    · push Not at hx_le_ε₂
      have hx_gt_ε₁ : ε₁ < x := by
        by_contra h_not
        push Not at h_not
        exact hnotB ⟨hx_le_ε₂, h_not⟩
      exact Or.inr (abs_sub_threshold_le h_approx (Or.inl ⟨hg_upper, by linarith⟩))
  · by_cases hg_le_ε₂ : g ≤ ε₂
    · exact Or.inl (abs_sub_threshold_le h_approx (Or.inl ⟨hg_le_ε₂, by linarith⟩))
    · push Not at hg_le_ε₂
      have hg_gt_ε₁ : ε₁ < g := by
        by_contra h_not
        push Not at h_not
        exact hnotA ⟨hg_le_ε₂, h_not⟩
      exact Or.inr (abs_sub_threshold_le h_approx (Or.inr ⟨hx_upper, by linarith⟩))

lemma tAnnLin_implies_r_le
    {L_norm r ε₁ : ℝ} (hL_pos : 0 < L_norm)
    (h_in : L_norm * r ≤ ε₁) :
    r ≤ ε₁ / L_norm := by rw [le_div_iff₀ hL_pos, mul_comm]; exact h_in

lemma near_threshold_implies_r_in_shell
    {L_norm r ε K₀ R_max : ℝ}
    (hL_pos : 0 < L_norm)
    (hK₀_nonneg : 0 ≤ K₀)
    (hR_max_nonneg : 0 ≤ R_max)
    (hr_le : r ≤ R_max) (hr_nonneg : 0 ≤ r)
    (h_near : |L_norm * r - ε| ≤ K₀ * r ^ 2) :
    (ε - K₀ * R_max^2) / L_norm ≤ r ∧
    r ≤ (ε + K₀ * R_max^2) / L_norm := by
  have h_abs := abs_le.mp h_near
  have h_lower : ε - K₀ * r^2 ≤ L_norm * r := by linarith [h_abs.1]
  have h_upper : L_norm * r ≤ ε + K₀ * r^2 := by linarith [h_abs.2]
  have hr2_le : r^2 ≤ R_max^2 :=
    sq_le_sq' (by linarith) hr_le
  have hK_r2_le : K₀ * r^2 ≤ K₀ * R_max^2 :=
    mul_le_mul_of_nonneg_left hr2_le hK₀_nonneg
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hL_pos]; linarith
  · rw [le_div_iff₀ hL_pos]; linarith

/-- When `ε ≤ Δ` (small epsilon), the shell is contained in a ball of radius `(ε+Δ)/L_norm`. -/
private lemma shell_vol_le_of_small_eps {t₀ ε Δ L_norm : ℝ}
    (hL_pos : 0 < L_norm) (_hΔ_nonneg : 0 ≤ Δ) (h : ε ≤ Δ) :
    volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ≤
      ENNReal.ofReal (4 * Δ / L_norm) := by
  have h_sub : {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ⊆
      {t : ℝ | |t - t₀| ≤ (ε + Δ) / L_norm} := by
    intro t ht; simp only [Set.mem_setOf_eq] at ht ⊢
    calc |t - t₀| = (L_norm * |t - t₀|) / L_norm := by field_simp
      _ ≤ (ε + Δ) / L_norm := div_le_div_of_nonneg_right
          (by linarith [(abs_le.mp ht).2]) hL_pos.le
  calc volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ}
      ≤ volume {t : ℝ | |t - t₀| ≤ (ε + Δ) / L_norm} :=
        MeasureTheory.measure_mono h_sub
    _ = volume (Set.Icc (t₀ - (ε + Δ) / L_norm) (t₀ + (ε + Δ) / L_norm)) := by
        congr 1; ext t; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
        constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
    _ = ENNReal.ofReal (2 * (ε + Δ) / L_norm) := by rw [Real.volume_Icc]; ring_nf
    _ ≤ ENNReal.ofReal (4 * Δ / L_norm) := by
        apply ENNReal.ofReal_le_ofReal
        calc 2 * (ε + Δ) / L_norm ≤ 2 * (2 * Δ) / L_norm :=
              div_le_div_of_nonneg_right (by linarith) hL_pos.le
          _ = 4 * Δ / L_norm := by ring

/-- The level set `{|t - t₀| = r₁}` for `r₁ > 0` has measure zero (it's at most 2 points). -/
private lemma volume_abs_eq_null {t₀ r₁ : ℝ} (hr₁_pos : 0 < r₁) :
    volume {t : ℝ | |t - t₀| = r₁} = 0 := by
  have h_sub : {t : ℝ | |t - t₀| = r₁} ⊆ {t₀ - r₁, t₀ + r₁} := by
    intro t ht; simp only [Set.mem_setOf_eq] at ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (abs_eq hr₁_pos.le).mp ht with h1 | h1
    · right; linarith
    · left; linarith
  exact le_antisymm (le_of_le_of_eq
    (MeasureTheory.measure_mono h_sub)
    ((Set.toFinite _).measure_zero volume)) (zero_le)

/-- When `Δ < ε` (large epsilon), the shell is an annulus with width `2Δ/L_norm`. -/
private lemma shell_vol_le_of_large_eps {t₀ ε Δ L_norm : ℝ}
    (hL_pos : 0 < L_norm) (hΔ_nonneg : 0 ≤ Δ) (h : Δ < ε) :
    volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ≤
      ENNReal.ofReal (4 * Δ / L_norm) := by
  let r₁ := (ε - Δ) / L_norm; let r₂ := (ε + Δ) / L_norm
  have hr₁_pos : 0 < r₁ := div_pos (by linarith) hL_pos
  have hr₁_le_r₂ : r₁ ≤ r₂ :=
    div_le_div_of_nonneg_right (by linarith) hL_pos.le
  have h_sub : {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ⊆
      {t : ℝ | r₁ ≤ |t - t₀| ∧ |t - t₀| ≤ r₂} := by
    intro t ht; simp only [Set.mem_setOf_eq] at ht
    have h_abs := abs_le.mp ht
    exact ⟨by calc r₁ = (ε - Δ) / L_norm := rfl
              _ ≤ (L_norm * |t - t₀|) / L_norm :=
                  div_le_div_of_nonneg_right (by linarith [h_abs.1]) hL_pos.le
              _ = |t - t₀| := by field_simp,
           by calc |t - t₀| = (L_norm * |t - t₀|) / L_norm := by field_simp
              _ ≤ (ε + Δ) / L_norm :=
                  div_le_div_of_nonneg_right (by linarith [h_abs.2]) hL_pos.le⟩
  calc volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ}
      ≤ volume {t : ℝ | r₁ ≤ |t - t₀| ∧ |t - t₀| ≤ r₂} :=
        MeasureTheory.measure_mono h_sub
    _ ≤ volume ({t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ∪ {t : ℝ | |t - t₀| = r₁}) :=
        MeasureTheory.measure_mono (fun t ⟨h1, h2⟩ => by
          by_cases heq : |t - t₀| = r₁
          · right; exact heq
          · left; exact ⟨lt_of_le_of_ne h1 (Ne.symm heq), h2⟩)
    _ ≤ volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} +
        volume {t : ℝ | |t - t₀| = r₁} := MeasureTheory.measure_union_le _ _
    _ = volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} := by
        rw [volume_abs_eq_null hr₁_pos, add_zero]
    _ ≤ ENNReal.ofReal (2 * (r₂ - r₁)) := volume_shell_le hr₁_le_r₂
    _ = ENNReal.ofReal (4 * Δ / L_norm) := by
        congr 1; show 2 * (r₂ - r₁) = 4 * Δ / L_norm
        simp only [r₁, r₂]; field_simp; ring

lemma shell_vol_le {t₀ ε Δ L_norm : ℝ}
    (hL_pos : 0 < L_norm)
    (hΔ_nonneg : 0 ≤ Δ) (_hε_pos : 0 < ε) :
    volume {t : ℝ |
      |L_norm * |t - t₀| - ε| ≤ Δ} ≤
      ENNReal.ofReal (4 * Δ / L_norm) := by
  by_cases h : ε ≤ Δ
  · exact shell_vol_le_of_small_eps hL_pos hΔ_nonneg h
  · exact shell_vol_le_of_large_eps hL_pos hΔ_nonneg (not_le.mp h)

/-- Near `t₀`, the curve increment dominates half the linear part: a quadratic-remainder bound. -/
private lemma annulus_lower_bound {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {K₀ δ₀ δ₁ : ℝ}
    (hK₀_pos : 0 < K₀) (hL_norm_pos : 0 < ‖L‖) (hδ₁_le_δ₀ : δ₁ ≤ δ₀)
    (hδ₁_le_L_over_2K : δ₁ ≤ ‖L‖ / (2 * K₀))
    (h_quad : ∀ t, |t - t₀| < δ₀ → ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ K₀ * |t - t₀| ^ 2) :
    ∀ t, |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ ‖L‖ / 2 * |t - t₀| := by
  intro t ht_lt
  have ht_lt_δ₀ : |t - t₀| < δ₀ := lt_of_lt_of_le ht_lt hδ₁_le_δ₀
  have ht_lt_L_over_2K : |t - t₀| < ‖L‖ / (2 * K₀) :=
    lt_of_lt_of_le ht_lt hδ₁_le_L_over_2K
  have h_approx := h_quad t ht_lt_δ₀
  have h_smul_norm : ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ := norm_smul (t - t₀) L
  have h1 : ‖γ t - γ t₀‖ ≥ ‖(t - t₀) • L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ := by
    have := abs_norm_sub_norm_le (γ t - γ t₀) ((t - t₀) • L)
    linarith [abs_le.mp this]
  have h2 : ‖γ t - γ t₀‖ ≥ |t - t₀| * ‖L‖ - K₀ * |t - t₀|^2 := by
    rw [h_smul_norm] at h1
    linarith [h_approx]
  have h4 : K₀ * |t - t₀| < ‖L‖ / 2 := by
    have : K₀ * (‖L‖ / (2 * K₀)) = ‖L‖ / 2 := by field_simp
    linarith [mul_lt_mul_of_pos_left ht_lt_L_over_2K hK₀_pos]
  nlinarith [h2, h4, abs_nonneg (t - t₀),
    mul_nonneg (abs_nonneg (t - t₀)) (le_of_lt (by linarith : (0 : ℝ) < ‖L‖ / 2 - K₀ * |t - t₀|))]

lemma annulus_symmDiff_measure_bound
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (_hab : a < b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀)
    (hγ_deriv : deriv γ t₀ = L) (hL : L ≠ 0) :
    ∃ K > 0, ∃ δ₀' > 0, ∃ δ > 0,
    ∀ ε₁ ε₂ : ℝ,
    0 < ε₂ → ε₂ ≤ ε₁ → ε₁ < δ →
    let γAnn := {t : ℝ |
      t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
      ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
    let tAnnLin := {t : ℝ |
      t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
      ε₂ < ‖L‖ * |t - t₀| ∧
      ‖L‖ * |t - t₀| ≤ ε₁}
    volume (symmDiff γAnn tAnnLin) ≤
      ENNReal.ofReal (K * ε₁^2 / ‖L‖^3) := by
  obtain ⟨K₀, δ₀, hδ₀_pos, hK₀_pos, h_quad⟩ :=
    quadratic_approx_of_contDiffAt_two hγ_C2
      hγ_deriv
  have ht₀_dist_pos :
      0 < min (t₀ - a) (b - t₀) := by
    simp only [lt_min_iff, Set.mem_Ioo] at ht₀ ⊢
    constructor <;> linarith
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  let δ₁ := min δ₀ (‖L‖ / (4 * K₀))
  have hδ₁_pos : 0 < δ₁ :=
    lt_min hδ₀_pos
      (div_pos hL_norm_pos (by linarith))
  have hδ₁_le_δ₀ : δ₁ ≤ δ₀ := min_le_left _ _
  have hδ₁_le_L_over_4K : δ₁ ≤ ‖L‖ / (4 * K₀) :=
    min_le_right _ _
  have hδ₁_le_L_over_2K :
      δ₁ ≤ ‖L‖ / (2 * K₀) :=
    hδ₁_le_L_over_4K.trans (div_le_div_of_nonneg_left
      (le_of_lt hL_norm_pos) (by linarith) (by linarith))
  have h_quad_small :
      ∀ r, r < δ₁ → K₀ * r ≤ ‖L‖ / 4 := by
    intro r hr
    calc K₀ * r
        ≤ K₀ * δ₁ := mul_le_mul_of_nonneg_left
          (le_of_lt hr) (le_of_lt hK₀_pos)
      _ ≤ K₀ * (‖L‖ / (4 * K₀)) :=
          mul_le_mul_of_nonneg_left
            hδ₁_le_L_over_4K (le_of_lt hK₀_pos)
      _ = ‖L‖ / 4 := by field_simp
  let δ := ‖L‖ * δ₁ / 2
  have hδ_pos : 0 < δ := by simp only [δ]; positivity
  use 32 * K₀, by linarith, δ₁, hδ₁_pos, δ, hδ_pos
  intro ε₁ ε₂ hε₂_pos hε₂_le hε₁_lt γAnn tAnnLin
  have hε₁_pos : 0 < ε₁ :=
    lt_of_lt_of_le hε₂_pos hε₂_le
  have hK₀_nonneg : 0 ≤ K₀ := le_of_lt hK₀_pos
  have hε₁_over_L_lt_δ₁ : ε₁ / ‖L‖ < δ₁ := by
    calc ε₁ / ‖L‖
        < (‖L‖ * δ₁ / 2) / ‖L‖ :=
          div_lt_div_of_pos_right hε₁_lt hL_norm_pos
      _ = δ₁ / 2 := by field_simp
      _ < δ₁ := by linarith [hδ₁_pos]
  have hε₁_over_L_lt_δ₀ : ε₁ / ‖L‖ < δ₀ :=
    lt_of_lt_of_le hε₁_over_L_lt_δ₁ hδ₁_le_δ₀
  have h2ε₁_over_L_lt_δ₁ :
      2 * ε₁ / ‖L‖ < δ₁ := by
    have h2 : 2 * ε₁ < ‖L‖ * δ₁ := by
      have : ε₁ < ‖L‖ * δ₁ / 2 := hε₁_lt
      linarith
    linarith [div_lt_div_of_pos_right h2 hL_norm_pos,
      show ‖L‖ * δ₁ / ‖L‖ = δ₁ from by field_simp]
  have h2ε₁_over_L_lt_δ₀ : 2 * ε₁ / ‖L‖ < δ₀ :=
    lt_of_lt_of_le h2ε₁_over_L_lt_δ₁ hδ₁_le_δ₀
  have h_lower_bound : ∀ t, |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ ‖L‖ / 2 * |t - t₀| :=
    annulus_lower_bound hK₀_pos hL_norm_pos hδ₁_le_δ₀ hδ₁_le_L_over_2K h_quad
  have h_localize_γAnn :
      ∀ t, t ∈ γAnn → |t - t₀| < δ₁ := by
    intro t ⟨_, ht_local, _, _⟩
    exact ht_local
  have h_localize_tAnnLin :
      ∀ t, t ∈ tAnnLin → |t - t₀| < δ₁ := by
    intro t ⟨_, ht_local, _, _⟩
    exact ht_local
  let R_max := 2 * ε₁ / ‖L‖
  let Δ := K₀ * R_max^2
  have hR_max_pos : 0 < R_max := by simp only [R_max]; positivity
  have hΔ_nonneg : 0 ≤ Δ :=
    mul_nonneg hK₀_nonneg (sq_nonneg _)
  let shell₁_lo := (ε₁ - Δ) / ‖L‖
  let shell₁_hi := (ε₁ + Δ) / ‖L‖
  let shell₂_lo := (ε₂ - Δ) / ‖L‖
  let shell₂_hi := (ε₂ + Δ) / ‖L‖
  let g : ℝ → ℝ := fun t => ‖γ t - γ t₀‖
  let x : ℝ → ℝ := fun t => ‖L‖ * |t - t₀|
  let e : ℝ → ℝ := fun t => K₀ * |t - t₀|^2
  let shell₁ := {t : ℝ | |x t - ε₁| ≤ Δ}
  let shell₂ := {t : ℝ | |x t - ε₂| ≤ Δ}
  have h_subset :
      symmDiff γAnn tAnnLin ⊆ shell₁ ∪ shell₂ := by
    intro t ht
    rw [Set.mem_symmDiff] at ht
    have hxor : Xor (t ∈ γAnn) (t ∈ tAnnLin) := ht
    have ht_localized : |t - t₀| < δ₁ := by
      rcases hxor with ⟨ht_γAnn, _⟩ | ⟨ht_tAnn, _⟩
      · exact h_localize_γAnn t ht_γAnn
      · exact h_localize_tAnnLin t ht_tAnn
    have ht_lt_δ₀ : |t - t₀| < δ₀ :=
      lt_of_lt_of_le ht_localized (min_le_left _ _)
    have h_gx_bound : |g t - x t| ≤ e t :=
      norm_linear_approx_bound h_quad ht_lt_δ₀
    have ht_Icc : t ∈ Set.Icc a b := by
      rcases hxor with
        ⟨⟨ht_Icc, _, _, _⟩, _⟩ |
        ⟨⟨ht_Icc, _, _, _⟩, _⟩ <;>
        exact ht_Icc
    have hxor' :
        Xor (ε₂ < g t ∧ g t ≤ ε₁)
             (ε₂ < x t ∧ x t ≤ ε₁) := by
      rcases hxor with
        ⟨⟨_, _, hγ_lo, hγ_hi⟩, ht_not_tAnn⟩ |
        ⟨⟨_, _, ht_lo, ht_hi⟩, ht_not_γAnn⟩
      · left; constructor
        · exact ⟨hγ_lo, hγ_hi⟩
        · intro ⟨ht_lo', ht_hi'⟩
          exact ht_not_tAnn
            ⟨ht_Icc, ht_localized, ht_lo', ht_hi'⟩
      · right; constructor
        · exact ⟨ht_lo, ht_hi⟩
        · intro ⟨hγ_lo', hγ_hi'⟩
          exact ht_not_γAnn
            ⟨ht_Icc, ht_localized, hγ_lo', hγ_hi'⟩
    have hR_bound : |t - t₀| ≤ R_max := by
      rcases hxor with ⟨ht_γAnn, _⟩ | ⟨ht_tAnn, _⟩
      · have h_lb := h_lower_bound t ht_localized
        have ⟨_, _, _, ht_upper⟩ := ht_γAnn
        have h1 : |t - t₀| * (‖L‖ / 2) ≤ ε₁ := by rw [mul_comm]; exact le_trans h_lb ht_upper
        have hL2_pos : 0 < ‖L‖ / 2 := by linarith
        have h2 : |t - t₀| ≤ ε₁ / (‖L‖ / 2) := (le_div_iff₀ hL2_pos).mpr h1
        simp only [R_max, show ε₁ / (‖L‖ / 2) = 2 * ε₁ / ‖L‖ from by field_simp] at h2 ⊢
        exact h2
      · have ⟨_, _, _, ht_upper⟩ := ht_tAnn
        have h1 : ‖L‖ * |t - t₀| ≤ ε₁ := ht_upper
        have h1' :
            |t - t₀| * ‖L‖ ≤ ε₁ := by rw [mul_comm]; exact h1
        have hL_nonneg : 0 ≤ ‖L‖ :=
          le_of_lt hL_norm_pos
        calc |t - t₀|
            ≤ ε₁ / ‖L‖ := by rw [le_div_iff₀ hL_norm_pos]; exact h1'
          _ ≤ 2 * ε₁ / ‖L‖ := by
              apply div_le_div_of_nonneg_right _
                hL_nonneg; linarith
    have he_le_Δ : e t ≤ Δ := by
      simp only [e, Δ, R_max]
      apply mul_le_mul_of_nonneg_left _ hK₀_nonneg
      exact sq_le_sq'
        (by linarith [abs_nonneg (t - t₀)]) hR_bound
    rcases symmDiff_subset_boundaryLayers h_gx_bound hxor' with h_near₂ | h_near₁
    · right
      change |x t - ε₂| ≤ Δ
      exact le_trans h_near₂ he_le_Δ
    · left
      change |x t - ε₁| ≤ Δ
      exact le_trans h_near₁ he_le_Δ
  have h_shell₁_eq : shell₁ = {t : ℝ | |‖L‖ * |t - t₀| - ε₁| ≤ Δ} := by simp only [shell₁, x]
  have h_shell₂_eq : shell₂ = {t : ℝ | |‖L‖ * |t - t₀| - ε₂| ≤ Δ} := by simp only [shell₂, x]
  have h_shell₁_vol : volume shell₁ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) := by
    rw [h_shell₁_eq]; exact shell_vol_le hL_norm_pos hΔ_nonneg hε₁_pos
  have h_shell₂_vol : volume shell₂ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) := by
    rw [h_shell₂_eq]; exact shell_vol_le hL_norm_pos hΔ_nonneg hε₂_pos
  have h_total_vol :
      volume (shell₁ ∪ shell₂) ≤
      ENNReal.ofReal (8 * Δ / ‖L‖) :=
    calc volume (shell₁ ∪ shell₂)
        ≤ volume shell₁ + volume shell₂ :=
          MeasureTheory.measure_union_le _ _
      _ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) +
          ENNReal.ofReal (4 * Δ / ‖L‖) :=
          add_le_add h_shell₁_vol h_shell₂_vol
      _ = ENNReal.ofReal
            (4 * Δ / ‖L‖ + 4 * Δ / ‖L‖) := by rw [← ENNReal.ofReal_add] <;> positivity
      _ = ENNReal.ofReal (8 * Δ / ‖L‖) := by ring_nf
  calc volume (symmDiff γAnn tAnnLin)
      ≤ volume (shell₁ ∪ shell₂) :=
        MeasureTheory.measure_mono h_subset
    _ ≤ ENNReal.ofReal (8 * Δ / ‖L‖) := h_total_vol
    _ = ENNReal.ofReal (32 * K₀ * ε₁^2 / ‖L‖^3) := by
        congr 1; simp only [Δ, R_max]; field_simp; ring


end
