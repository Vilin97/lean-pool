/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.WindingNumber.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Winding Number: Crossing Analysis

Technical analysis of curve crossings for generalized winding numbers.
Contains the core monotonicity, cutoff boundary, and direction convergence lemmas.

## Main Results

* `piecewiseC1Immersion_norm_strictMono_near_crossing` — local monotonicity at crossings
* `exists_cutoff_boundary_times` — existence of cutoff boundary times
* `exp_cutoff_integral_eq_ratio` — exponential of cutoff integral equals direction ratio
* `crossing_ratio_tendsto` — direction convergence as ε → 0
* `tendsto_exp_cutoff_integral_crossing` — exp(R(ε)) → exp(-iα)
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- The derivative of `s ↦ ‖f s - z₀‖`, via the `sqrt ∘ norm_sq` chain rule. -/
private lemma hasDerivAt_norm_sub_const (z₀ : ℂ) (f : ℝ → ℂ) (t : ℝ) (L : ℂ)
    (hf : HasDerivAt f L t) (hne : f t ≠ z₀) :
    HasDerivAt (fun s => ‖f s - z₀‖) (inner ℝ (f t - z₀) L / ‖f t - z₀‖) t := by
  have hne' : f t - z₀ ≠ 0 := sub_ne_zero.mpr hne
  have hpos : (0 : ℝ) < ‖f t - z₀‖ := norm_pos_iff.mpr hne'
  have hgsq := (hf.sub_const z₀).norm_sq
  convert (Real.hasDerivAt_sqrt (by positivity)).comp t hgsq using 1
  · ext s; simp only [Function.comp, Real.sqrt_sq (norm_nonneg _)]
  · rw [Real.sqrt_sq hpos.le]; field_simp [ne_of_gt hpos]

/-- The identity `⟪a, b⟫ / ‖a‖ = ⟪a / ‖a‖, b⟫` for the real inner product on `ℂ`,
valid even when `a = 0`. -/
private lemma inner_div_norm_complex (a b : ℂ) :
    inner (𝕜 := ℝ) a b / ‖a‖ = inner (𝕜 := ℝ) (a / ↑‖a‖) b := by
  have ha : a / ↑‖a‖ = (‖a‖⁻¹ : ℝ) • a := by
    simp only [div_eq_mul_inv, Complex.real_smul, Complex.ofReal_inv]; ring
  rw [ha]; erw [real_inner_smul_left]; ring

/-- Polar form: a nonzero complex number divided by its norm equals `exp(arg · I)`. -/
private lemma complex_div_norm_eq_exp_arg {w : ℂ} (hw : (‖w‖ : ℂ) ≠ 0) :
    w / ↑‖w‖ = Complex.exp (↑(Complex.arg w) * I) := by
  have key := Complex.norm_mul_exp_arg_mul_I w
  calc w / ↑‖w‖
      = (↑‖w‖ * Complex.exp (↑(Complex.arg w) * I)) / ↑‖w‖ := by rw [key]
    _ = Complex.exp (↑(Complex.arg w) * I) := by field_simp [hw]

/-- Helper: g = ‖γ(·) - z₀‖ is strictly decreasing on a left neighborhood of t₀ and
strictly increasing on a right neighborhood, when γ is an immersion at t₀.
This is the key "local monotonicity" fact that makes the cutoff boundary well-defined. -/
lemma piecewiseC1Immersion_norm_strictMono_near_crossing
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀) :
    ∃ l r : ℝ, l < t₀ ∧ t₀ < r ∧ γ.a ≤ l ∧ r ≤ γ.b ∧
      StrictAntiOn (fun t => ‖γ.toFun t - z₀‖) (Icc l t₀) ∧
      StrictMonoOn (fun t => ‖γ.toFun t - z₀‖) (Icc t₀ r) := by
  have hasDerivAt_norm_sub := hasDerivAt_norm_sub_const z₀
  have inner_div_norm := inner_div_norm_complex
  -- Step 1: Get right and left one-sided derivative limits (nonzero)
  obtain ⟨L_R, hL_R_ne, htend_R⟩ :
      ∃ L : ℂ, L ≠ 0 ∧ Filter.Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L) := by
    by_cases h : t₀ ∈ γ.partition
    · exact γ.right_deriv_limit t₀ h ht₀.2
    · exact ⟨_, γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) h,
        (γ.deriv_continuous_off_partition t₀ ht₀ h).tendsto.mono_left nhdsWithin_le_nhds⟩
  obtain ⟨L_L, hL_L_ne, htend_L⟩ :
      ∃ L : ℂ, L ≠ 0 ∧ Filter.Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L) := by
    by_cases h : t₀ ∈ γ.partition
    · exact γ.left_deriv_limit t₀ h ht₀.1
    · exact ⟨_, γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) h,
        (γ.deriv_continuous_off_partition t₀ ht₀ h).tendsto.mono_left nhdsWithin_le_nhds⟩
  -- Step 2: Get partition-free open neighborhoods (t₀, r₀) and (l₀, t₀)
  obtain ⟨r₀, hr₀, hr₀b, hno_R⟩ :
      ∃ r₀ > t₀, r₀ ≤ γ.b ∧ ∀ s ∈ Set.Ioo t₀ r₀, s ∉ γ.partition := by
    let Q := γ.partition.filter (fun x => t₀ < x)
    by_cases hQ : Q.Nonempty
    · have hmem := Finset.mem_filter.mp (Finset.min'_mem Q hQ)
      exact ⟨Q.min' hQ, hmem.2,
        le_trans (γ.partition_subset hmem.1).2 (le_refl _),
        fun s hs hc => by
          linarith [Finset.min'_le Q s (Finset.mem_filter.mpr ⟨hc, hs.1⟩), hs.2]⟩
    · exact ⟨γ.b, ht₀.2, le_refl _,
        fun s hs hc => hQ ⟨s, Finset.mem_filter.mpr ⟨hc, hs.1⟩⟩⟩
  obtain ⟨l₀, hl₀, hl₀a, hno_L⟩ :
      ∃ l₀ < t₀, γ.a ≤ l₀ ∧ ∀ s ∈ Set.Ioo l₀ t₀, s ∉ γ.partition := by
    let Q := γ.partition.filter (fun x => x < t₀)
    by_cases hQ : Q.Nonempty
    · have hmem := Finset.mem_filter.mp (Finset.max'_mem Q hQ)
      exact ⟨Q.max' hQ, hmem.2,
        le_trans (γ.partition_subset hmem.1).1 (le_refl _),
        fun s hs hc => by
          linarith [Finset.le_max' Q s (Finset.mem_filter.mpr ⟨hc, hs.2⟩), hs.1]⟩
    · exact ⟨γ.a, ht₀.1, le_refl _,
        fun s hs hc => hQ ⟨s, Finset.mem_filter.mpr ⟨hc, hs.2⟩⟩⟩
  -- Step 3: HasDerivWithinAt on Ici/Iic from one-sided tendsto (using FDeriv.Extend)
  have hHDWA_R : HasDerivWithinAt γ.toFun L_R (Set.Ici t₀) t₀ :=
    hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo t₀ r₀)
      (fun s hs => (γ.smooth_off_partition s
        ⟨le_trans ht₀.1.le (le_of_lt hs.1), le_trans hs.2.le hr₀b⟩
        (hno_R s hs)).differentiableWithinAt)
      (γ.continuous_toFun.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)).continuousWithinAt
      (Ioo_mem_nhdsGT hr₀) htend_R
  have hHDWA_L : HasDerivWithinAt γ.toFun L_L (Set.Iic t₀) t₀ :=
    hasDerivWithinAt_Iic_of_tendsto_deriv (s := Set.Ioo l₀ t₀)
      (fun s hs => (γ.smooth_off_partition s
        ⟨le_trans hl₀a (le_of_lt hs.1), le_trans hs.2.le ht₀.2.le⟩
        (hno_L s hs)).differentiableWithinAt)
      (γ.continuous_toFun.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)).continuousWithinAt
      (Ioo_mem_nhdsLT hl₀) htend_L
  -- Step 4: Slope tendsto (γ t - z₀)/(t - t₀) → L_R (right) and L_L (left)
  have hslope_R : Filter.Tendsto
      (fun t => (γ.toFun t - z₀) / ((t - t₀ : ℝ) : ℂ)) (𝓝[>] t₀) (𝓝 L_R) := by
    rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ici_diff_left] at hHDWA_R
    convert hHDWA_R using 1; ext t; simp only [slope, vsub_eq_sub, hcross, div_eq_mul_inv, mul_comm]
    erw [Complex.real_smul]; simp only [Complex.ofReal_inv]
  have hslope_L : Filter.Tendsto
      (fun t => (γ.toFun t - z₀) / ((t - t₀ : ℝ) : ℂ)) (𝓝[<] t₀) (𝓝 L_L) := by
    rw [hasDerivWithinAt_iff_tendsto_slope, Set.Iic_diff_right] at hHDWA_L
    convert hHDWA_L using 1; ext t; simp only [slope, vsub_eq_sub, hcross, div_eq_mul_inv, mul_comm]
    erw [Complex.real_smul]; simp only [Complex.ofReal_inv]
  have hL_R_pos : ‖L_R‖ > 0 := norm_pos_iff.mpr hL_R_ne
  have hL_L_pos : ‖L_L‖ > 0 := norm_pos_iff.mpr hL_L_ne
  -- Step 5: Direction (γ t - z₀)/‖γ t - z₀‖ → L_R/‖L_R‖ (right) and
  -- -L_L/‖L_L‖ (left)
  have hdir_R : Filter.Tendsto (fun t => (γ.toFun t - z₀) / ↑‖γ.toFun t - z₀‖)
      (𝓝[>] t₀) (𝓝 (L_R / ↑‖L_R‖)) := by
    have hLne : (‖L_R‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL_R_pos
    -- Explicit type annotation prevents beta-reduction issue in filter_upwards
    have hnorm_tend : Filter.Tendsto (fun t => ‖(γ.toFun t - z₀) / ((t - t₀ : ℝ) : ℂ)‖)
        (𝓝[>] t₀) (𝓝 ‖L_R‖) := continuous_norm.continuousAt.tendsto.comp hslope_R
    apply (hslope_R.div hnorm_tend.ofReal hLne).congr'
    filter_upwards [hnorm_tend.eventually (Ioi_mem_nhds (by linarith : ‖L_R‖ / 2 < ‖L_R‖)),
                    self_mem_nhdsWithin] with t hpos htgt
    simp only [Set.mem_Ioi] at htgt
    have hd : t - t₀ > 0 := sub_pos.mpr htgt
    simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hd.le] at hpos
    have hfne : γ.toFun t - z₀ ≠ 0 := by
      intro h
      simp only [h, norm_zero, zero_div] at hpos
      linarith
    change (γ.toFun t - z₀) / ↑(t - t₀) / ↑‖(γ.toFun t - z₀) / ↑(t - t₀)‖ =
         (γ.toFun t - z₀) / ↑‖γ.toFun t - z₀‖
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hd.le]; push_cast
    field_simp [show (t : ℂ) - t₀ ≠ 0 from by exact_mod_cast ne_of_gt hd,
      norm_ne_zero_iff.mpr hfne, ne_of_gt hd]
  have hdir_L : Filter.Tendsto (fun t => (γ.toFun t - z₀) / ↑‖γ.toFun t - z₀‖)
      (𝓝[<] t₀) (𝓝 (-L_L / ↑‖L_L‖)) := by
    have hLne : (‖L_L‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL_L_pos
    have hnorm_tend : Filter.Tendsto (fun t => ‖(γ.toFun t - z₀) / ((t - t₀ : ℝ) : ℂ)‖)
        (𝓝[<] t₀) (𝓝 ‖L_L‖) := continuous_norm.continuousAt.tendsto.comp hslope_L
    rw [neg_div]
    apply (hslope_L.div hnorm_tend.ofReal hLne).neg.congr'
    filter_upwards [hnorm_tend.eventually (Ioi_mem_nhds (by linarith : ‖L_L‖ / 2 < ‖L_L‖)),
                    self_mem_nhdsWithin] with t hpos htlt
    simp only [Set.mem_Iio] at htlt
    have hd : t - t₀ < 0 := sub_neg.mpr htlt
    simp only [norm_div, Complex.norm_real, Real.norm_of_nonpos hd.le] at hpos
    have hfne : γ.toFun t - z₀ ≠ 0 := by
      intro h
      simp only [h, norm_zero, zero_div] at hpos
      linarith
    change -((γ.toFun t - z₀) / ↑(t - t₀) / ↑‖(γ.toFun t - z₀) / ↑(t - t₀)‖) =
         (γ.toFun t - z₀) / ↑‖γ.toFun t - z₀‖
    rw [norm_div, Complex.norm_real, Real.norm_of_nonpos hd.le]; push_cast
    field_simp [show (t : ℂ) - t₀ ≠ 0 from by exact_mod_cast ne_of_lt hd,
      norm_ne_zero_iff.mpr hfne, ne_of_lt hd]
  -- Step 6: inner ℝ (γ t - z₀) (γ' t) / ‖γ t - z₀‖ → ‖L_R‖ (right)
  -- and -‖L_L‖ (left)
  -- Key: as t → t₀, direction → L/‖L‖ and deriv → L, so inner product → ‖L‖
  have hinner_tend_R : Filter.Tendsto
      (fun t => inner ℝ (γ.toFun t - z₀) (deriv γ.toFun t) / ‖γ.toFun t - z₀‖)
      (𝓝[>] t₀) (𝓝 ‖L_R‖) := by
    rw [show (fun t => inner ℝ (γ.toFun t - z₀) (deriv γ.toFun t) /
            ‖γ.toFun t - z₀‖) =
           (fun t => inner ℝ ((γ.toFun t - z₀) / ↑‖γ.toFun t - z₀‖)
            (deriv γ.toFun t)) from funext (fun t => inner_div_norm _ _)]
    have hLR_inner :
        ‖L_R‖ = inner (𝕜 := ℝ) (L_R / ↑‖L_R‖) L_R := by
      have hsmul : L_R / ↑‖L_R‖ = (‖L_R‖⁻¹ : ℝ) • L_R := by
        simp only [div_eq_mul_inv, Complex.real_smul, Complex.ofReal_inv]; ring
      rw [hsmul]; erw [real_inner_smul_left]; rw [real_inner_self_eq_norm_sq]
      field_simp
    rw [hLR_inner]
    convert (continuous_inner (E := ℂ) (𝕜 := ℝ)).continuousAt.tendsto.comp
        (hdir_R.prodMk_nhds htend_R) using 1
  have hinner_tend_L : Filter.Tendsto
      (fun t => inner ℝ (γ.toFun t - z₀) (deriv γ.toFun t) /
        ‖γ.toFun t - z₀‖) (𝓝[<] t₀) (𝓝 (-‖L_L‖)) := by
    rw [show (fun t => inner ℝ (γ.toFun t - z₀) (deriv γ.toFun t) /
            ‖γ.toFun t - z₀‖) =
           (fun t => inner ℝ ((γ.toFun t - z₀) / ↑‖γ.toFun t - z₀‖)
            (deriv γ.toFun t)) from funext (fun t => inner_div_norm _ _)]
    have hLL_inner :
        -‖L_L‖ = inner (𝕜 := ℝ) (-L_L / ↑‖L_L‖) L_L := by
      have hsmul : -(L_L / ↑‖L_L‖) = -(‖L_L‖⁻¹ : ℝ) • L_L := by
        simp only [div_eq_mul_inv, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_inv]; ring
      rw [neg_div, hsmul]; erw [real_inner_smul_left]; rw [real_inner_self_eq_norm_sq]; field_simp
    rw [hLL_inner]
    convert (continuous_inner (E := ℂ) (𝕜 := ℝ)).continuousAt.tendsto.comp
        (hdir_L.prodMk_nhds htend_L) using 1
  -- Step 7: Eventually positive/negative inner product ratio near t₀
  have hev_R : ∀ᶠ t in 𝓝[>] t₀,
      0 < inner ℝ (γ.toFun t - z₀) (deriv γ.toFun t) / ‖γ.toFun t - z₀‖ :=
    hinner_tend_R.eventually (Ioi_mem_nhds hL_R_pos)
  have hev_L : ∀ᶠ t in 𝓝[<] t₀,
      inner ℝ (γ.toFun t - z₀) (deriv γ.toFun t) / ‖γ.toFun t - z₀‖ < 0 :=
    hinner_tend_L.eventually (Iio_mem_nhds (by linarith))
  -- Extract concrete radii εR, εL from eventual properties
  rw [Filter.Eventually, nhdsWithin, Filter.mem_inf_principal, Metric.mem_nhds_iff] at hev_R hev_L
  obtain ⟨εR, hεR_pos, hεR⟩ := hev_R
  obtain ⟨εL, hεL_pos, hεL⟩ := hev_L
  -- Set the final interval endpoints
  set r₁ := min (t₀ + εR / 2) r₀
  set l₁ := max (t₀ - εL / 2) l₀
  have hr₁_gt : t₀ < r₁ := lt_min (by linarith) hr₀
  have hl₁_lt : l₁ < t₀ := max_lt (by linarith) hl₀
  have hr₁_le_b : r₁ ≤ γ.b := le_trans (min_le_right _ _) hr₀b
  have hl₁_ge_a : γ.a ≤ l₁ := le_trans hl₀a (le_max_right _ _)
  have hno_R₁ : ∀ s ∈ Set.Ioo t₀ r₁, s ∉ γ.partition :=
    fun s hs => hno_R s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
  have hno_L₁ : ∀ s ∈ Set.Ioo l₁ t₀, s ∉ γ.partition :=
    fun s hs => hno_L s ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, hs.2⟩
  -- Sign properties on the final intervals
  have hpos_R : ∀ t ∈ Set.Ioo t₀ r₁,
      0 < inner ℝ (γ.toFun t - z₀) (deriv γ.toFun t) / ‖γ.toFun t - z₀‖ := by
    intro t ht
    apply hεR
    · simp only [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
      linarith [ht.2, min_le_left (t₀ + εR / 2) r₀]
    · exact ht.1
  have hneg_L : ∀ t ∈ Set.Ioo l₁ t₀,
      inner ℝ (γ.toFun t - z₀) (deriv γ.toFun t) / ‖γ.toFun t - z₀‖ < 0 := by
    intro t ht
    apply hεL
    · simp only [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]
      linarith [ht.1, le_max_left (t₀ - εL / 2) l₀]
    · exact ht.2
  refine ⟨l₁, r₁, hl₁_lt, hr₁_gt, hl₁_ge_a, hr₁_le_b, ?_, ?_⟩
  · -- StrictAntiOn ‖γ · - z₀‖ on [l₁, t₀]: deriv is negative on interior (l₁, t₀)
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact continuous_norm.comp_continuousOn
        ((γ.continuous_toFun.mono (Icc_subset_Icc hl₁_ge_a ht₀.2.le)).sub continuousOn_const)
    · intro t ht
      rw [interior_Icc] at ht
      have hdiff := γ.smooth_off_partition t
        ⟨le_trans hl₁_ge_a (le_of_lt ht.1), le_trans ht.2.le ht₀.2.le⟩ (hno_L₁ t ht)
      have hne : γ.toFun t ≠ z₀ := by
        intro heq; have := hneg_L t ht; simp only [heq, sub_self, inner_zero_left, norm_zero,
          zero_div, lt_irrefl] at this
      rw [(hasDerivAt_norm_sub γ.toFun t _ hdiff.hasDerivAt hne).deriv]
      exact hneg_L t ht
  · -- StrictMonoOn ‖γ · - z₀‖ on [t₀, r₁]: deriv is positive on interior (t₀, r₁)
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact continuous_norm.comp_continuousOn
        ((γ.continuous_toFun.mono (Icc_subset_Icc ht₀.1.le hr₁_le_b)).sub continuousOn_const)
    · intro t ht
      rw [interior_Icc] at ht
      have hdiff := γ.smooth_off_partition t
        ⟨le_trans ht₀.1.le (le_of_lt ht.1), le_trans ht.2.le hr₁_le_b⟩ (hno_R₁ t ht)
      have hne : γ.toFun t ≠ z₀ := by
        intro heq; have := hpos_R t ht; simp only [heq, sub_self, inner_zero_left, norm_zero,
          zero_div, lt_irrefl] at this
      rw [(hasDerivAt_norm_sub γ.toFun t _ hdiff.hasDerivAt hne).deriv]
      exact hpos_R t ht

lemma exists_cutoff_boundary_times
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀) :
    ∃ δ > 0, ∀ ε ∈ Ioo 0 δ,
      ∃ σ₁ σ₂ : ℝ, γ.a ≤ σ₁ ∧ σ₁ < t₀ ∧ t₀ < σ₂ ∧ σ₂ ≤ γ.b ∧
        ‖γ.toFun σ₁ - z₀‖ = ε ∧ ‖γ.toFun σ₂ - z₀‖ = ε ∧
        (∀ t ∈ Ico γ.a σ₁, ε < ‖γ.toFun t - z₀‖) ∧
        (∀ t ∈ Ioc σ₂ γ.b, ε < ‖γ.toFun t - z₀‖) ∧
        (∀ t ∈ Icc σ₁ σ₂, ‖γ.toFun t - z₀‖ ≤ ε) := by
  -- g t = ‖γ(t) - z₀‖ is continuous on [a,b], g(t₀) = 0.
  set g : ℝ → ℝ := fun t => ‖γ.toFun t - z₀‖ with hg_def
  have hg_cont : ContinuousOn g (Icc γ.a γ.b) :=
    continuous_norm.comp_continuousOn (γ.continuous_toFun.sub continuousOn_const)
  have hg_t₀ : g t₀ = 0 := by simp only [hg_def, hcross, sub_self, norm_zero]
  -- Step 1: Get local strict monotonicity of g near t₀ from the immersion property.
  -- g is strictly decreasing on [l, t₀] and strictly increasing on [t₀, r].
  obtain ⟨l, r, hl_lt, hr_gt, hl_ge_a, hr_le_b, hg_anti, hg_mono⟩ :=
    piecewiseC1Immersion_norm_strictMono_near_crossing γ z₀ t₀ ht₀ hcross
  -- Step 2: Compactness gives positive minimum of g on [a, l] and [r, b].
  -- (Since g = 0 only at t₀, and t₀ ∉ [a,l] ∪ [r,b].)
  -- Minimum on [a, l]:
  have h_left_ne : (Icc γ.a l).Nonempty := ⟨γ.a, left_mem_Icc.mpr hl_ge_a⟩
  have h_left_sub : Icc γ.a l ⊆ Icc γ.a γ.b :=
    Icc_subset_Icc_right (le_trans (le_of_lt hl_lt) (le_of_lt ht₀.2))
  obtain ⟨xm₁, hxm₁_mem, hxm₁_min⟩ :=
    isCompact_Icc.exists_isMinOn h_left_ne (hg_cont.mono h_left_sub)
  have hm₁_pos : 0 < g xm₁ := by
    apply norm_pos_iff.mpr; apply sub_ne_zero.mpr
    intro h
    have := honly xm₁ (h_left_sub hxm₁_mem) h
    linarith [hxm₁_mem.2]
  -- Minimum on [r, b]:
  have h_right_ne : (Icc r γ.b).Nonempty := ⟨γ.b, right_mem_Icc.mpr hr_le_b⟩
  have h_right_sub : Icc r γ.b ⊆ Icc γ.a γ.b :=
    Icc_subset_Icc_left (le_trans (le_of_lt ht₀.1) (le_of_lt hr_gt))
  obtain ⟨xm₂, hxm₂_mem, hxm₂_min⟩ :=
    isCompact_Icc.exists_isMinOn h_right_ne (hg_cont.mono h_right_sub)
  have hm₂_pos : 0 < g xm₂ := by
    apply norm_pos_iff.mpr; apply sub_ne_zero.mpr
    intro h
    have := honly xm₂ (h_right_sub hxm₂_mem) h
    linarith [hxm₂_mem.1]
  -- Step 3: g(l) > 0 and g(r) > 0 (from strict antitonicity / monotonicity at t₀).
  have hg_l_pos : 0 < g l := by
    apply norm_pos_iff.mpr; apply sub_ne_zero.mpr
    intro h; have := honly l (h_left_sub (right_mem_Icc.mpr hl_ge_a)) h; linarith
  have hg_r_pos : 0 < g r := by
    apply norm_pos_iff.mpr; apply sub_ne_zero.mpr
    intro h; have := honly r (h_right_sub (left_mem_Icc.mpr hr_le_b)) h; linarith
  -- Step 4: Set δ = min of all positive values.
  set δ := min (min (g xm₁) (g xm₂)) (min (g l) (g r))
  refine ⟨δ, by apply lt_min (lt_min hm₁_pos hm₂_pos) (lt_min hg_l_pos hg_r_pos),
    fun ε hε => ?_⟩
  have hε_pos : 0 < ε := hε.1
  have hε_lt_m₁ : ε < g xm₁ := lt_of_lt_of_le hε.2 (min_le_of_left_le (min_le_left _ _))
  have hε_lt_m₂ : ε < g xm₂ := lt_of_lt_of_le hε.2 (min_le_of_left_le (min_le_right _ _))
  have hε_lt_l : ε < g l := lt_of_lt_of_le hε.2 (min_le_of_right_le (min_le_left _ _))
  have hε_lt_r : ε < g r := lt_of_lt_of_le hε.2 (min_le_of_right_le (min_le_right _ _))
  -- Step 5: IVT on [l, t₀]: g(l) > ε and g(t₀) = 0 < ε,
  -- so there exists σ₁ in [l, t₀] with g(σ₁) = ε.
  have hg_cont_l_t₀ : ContinuousOn g (Icc l t₀) :=
    hg_cont.mono (fun x ⟨hx₁, hx₂⟩ =>
      ⟨le_trans hl_ge_a hx₁, le_trans hx₂ (le_of_lt ht₀.2)⟩)
  have h_ivt₁ : ε ∈ g '' Icc l t₀ :=
    intermediate_value_Icc' (le_of_lt hl_lt) hg_cont_l_t₀
      ⟨by rw [hg_t₀]; exact le_of_lt hε_pos, le_of_lt hε_lt_l⟩
  obtain ⟨σ₁, hσ₁_mem, hσ₁_val⟩ := h_ivt₁
  -- σ₁ < t₀ since g(t₀) = 0 ≠ ε = g(σ₁)
  have hσ₁_ne_t₀ : σ₁ ≠ t₀ := fun h => by rw [h, hg_t₀] at hσ₁_val; linarith
  have hσ₁_lt_t₀ : σ₁ < t₀ := lt_of_le_of_ne hσ₁_mem.2 hσ₁_ne_t₀
  -- By strict antitonicity of g on [l, t₀]: σ₁ is UNIQUE in (l, t₀)
  -- with g(σ₁) = ε, and g < ε on (σ₁, t₀) and g > ε on (l, σ₁).
  -- More precisely: for s ∈ [l, t₀] with s < σ₁: g(s) > g(σ₁) = ε (strict antitonicity)
  -- For s ∈ [l, t₀] with s > σ₁: g(s) < g(σ₁) = ε (strict antitonicity)
  -- Step 6: IVT on [t₀, r]: g(t₀) = 0 < ε and g(r) > ε,
  -- so there exists σ₂ in [t₀, r] with g(σ₂) = ε.
  have hg_cont_t₀_r : ContinuousOn g (Icc t₀ r) :=
    hg_cont.mono (fun x ⟨hx₁, hx₂⟩ =>
      ⟨le_trans (le_of_lt ht₀.1) hx₁, le_trans hx₂ hr_le_b⟩)
  have h_ivt₂ : ε ∈ g '' Icc t₀ r :=
    intermediate_value_Icc (le_of_lt hr_gt) hg_cont_t₀_r
      ⟨by rw [hg_t₀]; exact le_of_lt hε_pos, le_of_lt hε_lt_r⟩
  obtain ⟨σ₂, hσ₂_mem, hσ₂_val⟩ := h_ivt₂
  have hσ₂_ne_t₀ : σ₂ ≠ t₀ := fun h => by rw [h, hg_t₀] at hσ₂_val; linarith
  have hσ₂_gt_t₀ : t₀ < σ₂ := lt_of_le_of_ne hσ₂_mem.1 (Ne.symm hσ₂_ne_t₀)
  -- Step 7: We want σ₁ to be the UNIQUE point in [l, t₀) with g(σ₁) = ε.
  -- Since g is strictly antitone on [l, t₀], there is exactly one such point.
  -- Use the strict antitonicity to get the canonical σ₁:
  -- Actually, our σ₁ from IVT already works because g is strictly antitone:
  -- - g > ε on [l, σ₁) (since g(σ₁) = ε and g is strictly decreasing)
  -- - g < ε on (σ₁, t₀] (since g(σ₁) = ε and g is strictly decreasing)
  -- Therefore g ≤ ε on [σ₁, t₀].
  -- Similarly for σ₂.
  -- However, σ₁ might not be unique from IVT alone; but since g is STRICT antitone,
  -- if g(s) = ε for s ∈ [l, t₀] then s = σ₁ (uniqueness by strict antitonicity).
  -- So any σ₁ from IVT with g(σ₁) = ε is the same.
  -- For t ∈ [l, σ₁): hg_anti gives g(t) > g(σ₁) = ε.
  have h_l_σ₁_gt : ∀ t ∈ Ico l σ₁, ε < g t := by
    intro t ⟨hlt, htσ₁⟩
    have ht_Icc : t ∈ Icc l t₀ := ⟨hlt, le_trans (le_of_lt htσ₁) hσ₁_mem.2⟩
    calc ε = g σ₁ := hσ₁_val.symm
      _ < g t := hg_anti ht_Icc hσ₁_mem htσ₁
  -- For t ∈ (σ₁, t₀]: hg_anti gives g(t) < g(σ₁) = ε.
  have h_σ₁_t₀_lt : ∀ t ∈ Ioc σ₁ t₀, g t < ε := by
    intro t ⟨hσ₁t, htt₀⟩
    have ht_Icc : t ∈ Icc l t₀ := ⟨le_trans hσ₁_mem.1 (le_of_lt hσ₁t), htt₀⟩
    calc g t < g σ₁ := hg_anti hσ₁_mem ht_Icc hσ₁t
      _ = ε := hσ₁_val
  -- For t ∈ [t₀, σ₂): hg_mono gives g(t) < g(σ₂) = ε.
  have h_t₀_σ₂_lt : ∀ t ∈ Ico t₀ σ₂, g t < ε := by
    intro t ⟨htt₀, htσ₂⟩
    have ht_Icc : t ∈ Icc t₀ r := ⟨htt₀, le_trans (le_of_lt htσ₂) hσ₂_mem.2⟩
    calc g t < g σ₂ := hg_mono ht_Icc hσ₂_mem htσ₂
      _ = ε := hσ₂_val
  -- For t ∈ (σ₂, r]: hg_mono gives g(t) > g(σ₂) = ε.
  have h_σ₂_r_gt : ∀ t ∈ Ioc σ₂ r, ε < g t := by
    intro t ⟨hσ₂t, htr⟩
    have ht_Icc : t ∈ Icc t₀ r := ⟨le_trans hσ₂_mem.1 (le_of_lt hσ₂t), htr⟩
    calc ε = g σ₂ := hσ₂_val.symm
      _ < g t := hg_mono hσ₂_mem ht_Icc hσ₂t
  -- Now provide the witnesses σ₁ and σ₂.
  refine ⟨σ₁, σ₂, le_trans hl_ge_a hσ₁_mem.1, hσ₁_lt_t₀, hσ₂_gt_t₀,
    le_trans hσ₂_mem.2 hr_le_b, hσ₁_val, hσ₂_val, ?_, ?_, ?_⟩
  · -- g > ε on [a, σ₁)
    intro t ⟨hat, htσ₁⟩
    rcases le_or_gt t l with htl | hlt
    · -- t ∈ [a, l]: use minimum on [a, l]
      exact lt_of_lt_of_le hε_lt_m₁ (hxm₁_min ⟨hat, htl⟩)
    · -- t ∈ (l, σ₁) ⊆ [l, t₀): use h_l_σ₁_gt
      exact h_l_σ₁_gt t ⟨le_of_lt hlt, htσ₁⟩
  · -- g > ε on (σ₂, b]
    intro t ⟨hσ₂t, htb⟩
    rcases le_or_gt r t with hrlt | htr
    · -- t ∈ [r, b]: use minimum on [r, b]
      exact lt_of_lt_of_le hε_lt_m₂ (hxm₂_min ⟨hrlt, htb⟩)
    · -- t ∈ (σ₂, r) ⊆ (σ₂, r]: use h_σ₂_r_gt
      exact h_σ₂_r_gt t ⟨hσ₂t, le_of_lt htr⟩
  · -- g ≤ ε on [σ₁, σ₂]
    intro t ⟨hσ₁t, htσ₂⟩
    rcases le_or_gt t t₀ with htt₀ | ht₀t
    · -- t ∈ [σ₁, t₀]: either t = σ₁ (g = ε) or t ∈ (σ₁, t₀] (g < ε)
      rcases eq_or_lt_of_le hσ₁t with rfl | hlt
      · exact le_of_eq hσ₁_val
      · exact le_of_lt (h_σ₁_t₀_lt t ⟨hlt, htt₀⟩)
    · -- t ∈ (t₀, σ₂]: either t = σ₂ (g = ε) or t ∈ [t₀, σ₂) (g < ε)
      rcases eq_or_lt_of_le htσ₂ with rfl | hlt
      · exact le_of_eq hσ₂_val
      · exact le_of_lt (h_t₀_σ₂_lt t ⟨le_of_lt ht₀t, hlt⟩)

/-- Extended version of `exists_cutoff_boundary_times` that also exposes the
strict monotonicity interval and the bounds `δ ≤ ‖γ(l) - z₀‖`,
`δ ≤ ‖γ(r) - z₀‖`. -/
lemma exists_cutoff_boundary_times_with_mono
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀) :
    ∃ δ > 0, ∃ l r : ℝ, l < t₀ ∧ t₀ < r ∧ γ.a ≤ l ∧ r ≤ γ.b ∧
      StrictAntiOn (fun t => ‖γ.toFun t - z₀‖) (Icc l t₀) ∧
      StrictMonoOn (fun t => ‖γ.toFun t - z₀‖) (Icc t₀ r) ∧
      δ ≤ ‖γ.toFun l - z₀‖ ∧ δ ≤ ‖γ.toFun r - z₀‖ ∧
      (∀ ε ∈ Ioo 0 δ, ∃ σ₁ σ₂ : ℝ,
        γ.a ≤ σ₁ ∧ σ₁ < t₀ ∧ t₀ < σ₂ ∧ σ₂ ≤ γ.b ∧
        ‖γ.toFun σ₁ - z₀‖ = ε ∧ ‖γ.toFun σ₂ - z₀‖ = ε ∧
        (∀ t ∈ Ico γ.a σ₁, ε < ‖γ.toFun t - z₀‖) ∧
        (∀ t ∈ Ioc σ₂ γ.b, ε < ‖γ.toFun t - z₀‖) ∧
        (∀ t ∈ Icc σ₁ σ₂, ‖γ.toFun t - z₀‖ ≤ ε)) := by
  obtain ⟨l, r, hl_lt, hr_gt, hl_ge_a, hr_le_b, hg_anti, hg_mono⟩ :=
    piecewiseC1Immersion_norm_strictMono_near_crossing γ z₀ t₀ ht₀ hcross
  obtain ⟨δ₁, hδ₁, hbnd₁⟩ :=
    exists_cutoff_boundary_times γ z₀ t₀ ht₀ hcross honly
  have hg_l_pos : 0 < ‖γ.toFun l - z₀‖ := by
    apply norm_pos_iff.mpr; apply sub_ne_zero.mpr
    intro heq; have := honly l ⟨hl_ge_a, le_trans hl_lt.le (le_of_lt ht₀.2)⟩ heq; linarith
  have hg_r_pos : 0 < ‖γ.toFun r - z₀‖ := by
    apply norm_pos_iff.mpr; apply sub_ne_zero.mpr
    intro heq; have := honly r ⟨le_trans (le_of_lt ht₀.1) hr_gt.le, hr_le_b⟩ heq; linarith
  exact ⟨min δ₁ (min ‖γ.toFun l - z₀‖ ‖γ.toFun r - z₀‖),
    lt_min hδ₁ (lt_min hg_l_pos hg_r_pos),
    l, r, hl_lt, hr_gt, hl_ge_a, hr_le_b, hg_anti, hg_mono,
    le_trans (min_le_right _ _) (min_le_left _ _),
    le_trans (min_le_right _ _) (min_le_right _ _),
    fun ε hε => hbnd₁ ε ⟨hε.1, lt_of_lt_of_le hε.2 (min_le_left _ _)⟩⟩

/-- On a sub-interval `[c,d]` of `[a,b]` where `ε < ‖γ-z₀‖`, the auxiliary function
`G t = (γ t - z₀)·exp(-F t)` is constant. This is the core constancy argument shared by the
left and right regions in `exp_cutoff_integral_eq_ratio`. -/
private lemma exp_cutoff_G_const_on
    (γ : PiecewiseC1Immersion) (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε)
    (f F : ℝ → ℂ) (P : Finset ℝ)
    (G : ℝ → ℂ) (hG_def : G = fun t => (γ.toFun t - z₀) * cexp (-F t))
    (hG_cont : ContinuousOn G (Icc γ.a γ.b))
    (hf_val : ∀ t, ε < ‖γ.toFun t - z₀‖ →
      f t = (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t)
    (hF_deriv : ∀ t ∈ Ioo γ.a γ.b, t ∉ (↑P : Set ℝ) →
      ε < ‖γ.toFun t - z₀‖ → HasDerivAt F (f t) t)
    {c d : ℝ} (hcd : c < d) (hac : γ.a ≤ c) (hdb : d ≤ γ.b)
    (hP_eq : P = γ.partition)
    (h_pos : ∀ t ∈ Ioo c d, ε < ‖γ.toFun t - z₀‖) :
    ∀ t ∈ Icc c d, G t = G c := by
  refine constant_of_has_deriv_right_zero
    (hG_cont.mono (Icc_subset_Icc hac hdb))
    (hasDerivWithinAt_zero_of_deriv_zero_off_finite G c d P hcd
      (hG_cont.mono (Icc_subset_Icc hac hdb))
      (fun t ht htP => ?_) (fun t ht htP => ?_))
  · have ht_ab : t ∈ Ioo γ.a γ.b := ⟨lt_of_le_of_lt hac ht.1, lt_of_lt_of_le ht.2 hdb⟩
    have h_gt : ε < ‖γ.toFun t - z₀‖ := h_pos t ht
    rw [hG_def]
    exact ((γ.smooth_off_partition t (Ioo_subset_Icc_self ht_ab) (hP_eq ▸ htP)).sub
      (differentiableAt_const _)).mul
      (hF_deriv t ht_ab htP h_gt).differentiableAt.neg.cexp
  · have ht_ab : t ∈ Ioo γ.a γ.b := ⟨lt_of_le_of_lt hac ht.1, lt_of_lt_of_le ht.2 hdb⟩
    have h_gt : ε < ‖γ.toFun t - z₀‖ := h_pos t ht
    have hne : γ.toFun t - z₀ ≠ 0 := by intro h; rw [h, norm_zero] at h_gt; linarith
    have hG_at : HasDerivAt G
        (deriv γ.toFun t * cexp (-F t) + (γ.toFun t - z₀) * (cexp (-F t) * -f t)) t := by
      rw [hG_def]
      exact ((γ.smooth_off_partition t (Ioo_subset_Icc_self ht_ab)
        (hP_eq ▸ htP)).hasDerivAt.sub_const z₀).mul (hF_deriv t ht_ab htP h_gt).neg.cexp
    rw [hG_at.deriv, hf_val t h_gt]; field_simp [hne]; ring

/-- For a closed piecewise C¹ immersion, when the cutoff integral is split
at boundary times where ‖γ-z₀‖ = ε with strict inequality outside, the
exponential equals the ratio (γ(σ₁)-z₀)/(γ(σ₂)-z₀) by FTC + closedness. -/
lemma exp_cutoff_integral_eq_ratio
    (γ : PiecewiseC1Immersion) (hclosed : γ.toPiecewiseC1Curve.IsClosed)
    (z₀ : ℂ) (σ₁ σ₂ ε : ℝ)
    (hσ₁ : γ.a ≤ σ₁) (hσ₁₂ : σ₁ < σ₂) (hσ₂ : σ₂ ≤ γ.b)
    (hε : 0 < ε)
    (hσ₁_val : ‖γ.toFun σ₁ - z₀‖ = ε) (hσ₂_val : ‖γ.toFun σ₂ - z₀‖ = ε)
    (h_left : ∀ t ∈ Ico γ.a σ₁, ε < ‖γ.toFun t - z₀‖)
    (h_right : ∀ t ∈ Ioc σ₂ γ.b, ε < ‖γ.toFun t - z₀‖)
    (h_middle : ∀ t ∈ Icc σ₁ σ₂, ‖γ.toFun t - z₀‖ ≤ ε) :
    Complex.exp (∫ t in γ.a..γ.b,
      if ‖γ.toFun t - z₀‖ > ε
      then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) =
    (γ.toFun σ₁ - z₀) / (γ.toFun σ₂ - z₀) := by
  let f : ℝ → ℂ := fun t =>
    if ‖γ.toFun t - z₀‖ > ε then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0
  -- The middle integral [σ₁,σ₂] is 0 since ‖γ-z₀‖ ≤ ε there
  have h_mid_zero : ∫ t in σ₁..σ₂, f t = 0 := by
    apply intervalIntegral.integral_zero_ae
    exact Filter.Eventually.of_forall fun t ht => by
      simp only [f]
      have ht_Icc : t ∈ Icc σ₁ σ₂ := by
        rw [Set.uIoc_of_le hσ₁₂.le] at ht; exact Ioc_subset_Icc_self ht
      rw [if_neg (not_lt.mpr (h_middle t ht_Icc))]
  -- === G-function proof: adapted from exp_integral_eq_endpoint_ratio_piecewise ===
  change cexp (∫ t in γ.a..γ.b, f t) = _
  obtain ⟨Md, hMd⟩ := piecewiseC1Immersion_deriv_bounded γ
  let P := γ.partition
  -- Key non-vanishing facts
  have hne_σ₁ : γ.toFun σ₁ - z₀ ≠ 0 := sub_ne_zero.mpr (by
    intro h; rw [h, sub_self, norm_zero] at hσ₁_val; linarith)
  have hne_σ₂ : γ.toFun σ₂ - z₀ ≠ 0 := sub_ne_zero.mpr (by
    intro h; rw [h, sub_self, norm_zero] at hσ₂_val; linarith)
  have hne_a : γ.toFun γ.a - z₀ ≠ 0 := by
    rw [sub_ne_zero]; intro h
    rcases eq_or_lt_of_le hσ₁ with rfl | h'
    · rw [h, sub_self, norm_zero] at hσ₁_val; linarith
    · have := h_left γ.a ⟨le_refl _, h'⟩; rw [h, sub_self, norm_zero] at this; linarith
  -- f equals γ'/(γ-z₀) wherever ‖γ-z₀‖ > ε
  have hf_val : ∀ t, ε < ‖γ.toFun t - z₀‖ →
      f t = (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t := by
    intro t h; simp only [f]; exact if_pos h
  -- Membership helpers
  have hσ₁_mem : σ₁ ∈ Set.uIcc γ.a γ.b := by
    rw [Set.uIcc_of_le γ.hab.le]; exact ⟨hσ₁, hσ₁₂.le.trans hσ₂⟩
  have hσ₂_mem : σ₂ ∈ Set.uIcc γ.a γ.b := by
    rw [Set.uIcc_of_le γ.hab.le]; exact ⟨hσ₁.trans hσ₁₂.le, hσ₂⟩
  -- f is bounded
  have hf_bnd : ∀ t ∈ Icc γ.a γ.b, ‖f t‖ ≤ Md / ε := by
    intro t ht; simp only [f]; split_ifs with h
    · rw [norm_mul, norm_inv, show Md / ε = ε⁻¹ * Md from by ring]
      exact mul_le_mul (inv_anti₀ hε h.le) (hMd t ht) (norm_nonneg _)
        (inv_nonneg.mpr hε.le)
    · rw [norm_zero]; exact div_nonneg
        (le_trans (norm_nonneg _) (hMd γ.a (left_mem_Icc.mpr γ.hab.le))) hε.le
  -- f piecewise continuous off Q = partition ∪ {σ₁, σ₂}
  let Q : Finset ℝ := P ∪ {σ₁, σ₂}
  have hf_cont_off : ContinuousOn f (Icc γ.a γ.b \ ↑Q) := by
    intro t ⟨ht, htQ⟩
    simp only [Q, Finset.coe_union, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_union, Finset.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at htQ
    have htP : t ∉ (↑P : Set ℝ) := htQ.1
    have ht_ne_σ₁ : t ≠ σ₁ := htQ.2.1
    have ht_ne_σ₂ : t ≠ σ₂ := htQ.2.2
    have ht_Ioo : t ∈ Ioo γ.a γ.b :=
      ⟨lt_of_le_of_ne ht.1 (fun h => htP (h ▸ γ.endpoints_in_partition.1)),
       lt_of_le_of_ne ht.2 (fun h => htP (h ▸ γ.endpoints_in_partition.2))⟩
    by_cases h₁ : t < σ₁
    · -- Region (a,σ₁): f = γ'/(γ-z₀) locally
      have h_gt : ε < ‖γ.toFun t - z₀‖ := h_left t ⟨ht.1, h₁⟩
      have hne : γ.toFun t - z₀ ≠ 0 := by intro h; rw [h, norm_zero] at h_gt; linarith
      have h_nhds : (fun s => (γ.toFun s - z₀)⁻¹ * deriv γ.toFun s) =ᶠ[𝓝 t] f := by
        filter_upwards [((continuous_norm.continuousAt.comp
          (γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
            continuousAt_const)).eventually (isOpen_Ioi.mem_nhds h_gt))]
        intro s hs; exact (hf_val s hs).symm
      exact (ContinuousAt.mul
        ((γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
          continuousAt_const).inv₀ hne)
        (γ.deriv_continuous_off_partition t ht_Ioo htP)).congr h_nhds |>.continuousWithinAt
    · by_cases h₂ : σ₂ < t
      · -- Region (σ₂,b): f = γ'/(γ-z₀) locally
        have h_gt : ε < ‖γ.toFun t - z₀‖ := h_right t ⟨h₂, ht.2⟩
        have hne : γ.toFun t - z₀ ≠ 0 := by intro h; rw [h, norm_zero] at h_gt; linarith
        have h_nhds : (fun s => (γ.toFun s - z₀)⁻¹ * deriv γ.toFun s) =ᶠ[𝓝 t] f := by
          filter_upwards [((continuous_norm.continuousAt.comp
            (γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
              continuousAt_const)).eventually (isOpen_Ioi.mem_nhds h_gt))]
          intro s hs; exact (hf_val s hs).symm
        exact (ContinuousAt.mul
          ((γ.continuous_toFun.continuousAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2) |>.sub
            continuousAt_const).inv₀ hne)
          (γ.deriv_continuous_off_partition t ht_Ioo htP)).congr h_nhds |>.continuousWithinAt
      · -- Region (σ₁,σ₂): f = 0 locally
        have ht_mid : t ∈ Ioo σ₁ σ₂ :=
          ⟨lt_of_le_of_ne (not_lt.mp h₁) (Ne.symm ht_ne_σ₁),
           lt_of_le_of_ne (not_lt.mp h₂) ht_ne_σ₂⟩
        have h_nhds : ∀ᶠ s in 𝓝 t, f s = 0 :=
          Filter.eventually_of_mem (Ioo_mem_nhds ht_mid.1 ht_mid.2) fun s hs => by
            simp only [f]; exact if_neg (not_lt.mpr (h_middle s ⟨hs.1.le, hs.2.le⟩))
        exact continuousWithinAt_const.congr_of_eventuallyEq
          (h_nhds.filter_mono nhdsWithin_le_nhds)
          (by simp only [f]; exact if_neg (not_lt.mpr (h_middle t ⟨ht_mid.1.le, ht_mid.2.le⟩)))
  -- f integrable
  have h_int : IntervalIntegrable f volume γ.a γ.b :=
    intervalIntegrable_of_piecewise_continuousOn_bounded (Md / ε) γ.hab.le hf_cont_off hf_bnd
  -- Define F and G
  let F : ℝ → ℂ := fun t => ∫ s in γ.a..t, f s
  let G : ℝ → ℂ := fun t => (γ.toFun t - z₀) * cexp (-F t)
  have hFa : F γ.a = 0 := intervalIntegral.integral_same
  have hGa : G γ.a = γ.toFun γ.a - z₀ := by
    simp only [G, hFa, neg_zero, Complex.exp_zero, mul_one]
  -- F continuous
  have hF_cont : ContinuousOn F (Icc γ.a γ.b) := by
    have := intervalIntegral.continuousOn_primitive_interval' h_int left_mem_uIcc
    rwa [Set.uIcc_of_le γ.hab.le] at this
  -- G continuous
  have hG_cont : ContinuousOn G (Icc γ.a γ.b) :=
    (γ.continuous_toFun.sub continuousOn_const).mul
      (Complex.continuous_exp.comp_continuousOn hF_cont.neg)
  -- F(σ₂) = F(σ₁) (middle integral is 0)
  have hF_mid : F σ₂ = F σ₁ := by
    change ∫ s in γ.a..σ₂, f s = ∫ s in γ.a..σ₁, f s
    have h1 := h_int.mono_set (Set.uIcc_subset_uIcc_left hσ₁_mem)
    have h2 := h_int.mono_set (Set.uIcc_subset_uIcc hσ₁_mem hσ₂_mem)
    have h := intervalIntegral.integral_add_adjacent_intervals h1 h2
    rw [h_mid_zero, add_zero] at h; exact h.symm
  -- Helper: HasDerivAt for F at t ∈ (a,b) off partition where ‖γ-z₀‖ > ε
  -- (includes ContinuousAt and StronglyMeasurableAtFilter construction)
  have hF_deriv : ∀ t ∈ Ioo γ.a γ.b, t ∉ (↑P : Set ℝ) →
      ε < ‖γ.toFun t - z₀‖ → HasDerivAt F (f t) t := by
    intro t ht htP h_gt
    -- Find open ball around t avoiding partition (finite sets are closed)
    obtain ⟨δP, hδP, hδP_avoid⟩ := Metric.isOpen_iff.mp
      (P.finite_toSet.isClosed.isOpen_compl) t htP
    have h_norm_cont : ContinuousAt (fun s => ‖γ.toFun s - z₀‖) t :=
      continuous_norm.continuousAt.comp
        (γ.continuous_toFun.continuousAt (Icc_mem_nhds ht.1 ht.2) |>.sub continuousAt_const)
    obtain ⟨δN, hδN, hδN_ball⟩ := Metric.eventually_nhds_iff.mp
      (h_norm_cont.eventually (isOpen_Ioi.mem_nhds h_gt))
    let δ := min δP δN
    have hδ : 0 < δ := lt_min hδP hδN
    let p₁ := max γ.a (t - δ / 2)
    let p₂ := min γ.b (t + δ / 2)
    have hp₁p₂ : p₁ < p₂ := by
      simp only [p₁, p₂, lt_min_iff, max_lt_iff]
      exact ⟨⟨lt_trans ht.1 ht.2, by linarith [ht.2, hδ]⟩,
             ⟨by linarith [ht.1, hδ], by linarith⟩⟩
    have h_sub : Ioo p₁ p₂ ⊆ Ioo γ.a γ.b := fun x hx => by
      simp only [p₁, p₂, mem_Ioo] at hx ⊢
      exact ⟨lt_of_le_of_lt (le_max_left γ.a _) hx.1,
             lt_of_lt_of_le hx.2 (min_le_left γ.b _)⟩
    have ht_in : t ∈ Ioo p₁ p₂ := by
      simp only [p₁, p₂, mem_Ioo, lt_min_iff, max_lt_iff]
      exact ⟨⟨ht.1, by linarith [hδ]⟩, ⟨ht.2, by linarith [hδ]⟩⟩
    -- All points in Ioo p₁ p₂ avoid P and have ‖γ-z₀‖ > ε
    have h_avoid : ∀ x ∈ Ioo p₁ p₂, x ∉ (↑P : Set ℝ) := fun x hx =>
      hδP_avoid (by
        simp only [Metric.mem_ball, Real.dist_eq, p₁, p₂, mem_Ioo] at hx ⊢
        rw [abs_lt]
        exact ⟨by linarith [le_max_right γ.a (t - δ / 2), min_le_left δP δN],
               by linarith [min_le_right γ.b (t + δ / 2), min_le_left δP δN]⟩)
    have h_gt_all : ∀ x ∈ Ioo p₁ p₂, ε < ‖γ.toFun x - z₀‖ :=
      fun x hx => hδN_ball (by
      simp only [p₁, p₂, mem_Ioo, Real.dist_eq] at hx ⊢
      rw [abs_lt]
      exact ⟨by linarith [le_max_right γ.a (t - δ / 2), min_le_right δP δN],
             by linarith [min_le_right γ.b (t + δ / 2), min_le_right δP δN]⟩)
    -- f is ContinuousAt at all points of Ioo p₁ p₂
    have hf_ca_all : ∀ x ∈ Ioo p₁ p₂, ContinuousAt f x := fun x hx => by
      have hx_gt := h_gt_all x hx
      have hx_ne : γ.toFun x - z₀ ≠ 0 := by intro h; rw [h, norm_zero] at hx_gt; linarith
      have hx_eq : (fun s => (γ.toFun s - z₀)⁻¹ * deriv γ.toFun s) =ᶠ[𝓝 x] f := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with s hs
        exact (hf_val s (h_gt_all s hs)).symm
      exact (ContinuousAt.mul
        ((γ.continuous_toFun.continuousAt (Icc_mem_nhds (h_sub hx).1 (h_sub hx).2) |>.sub
          continuousAt_const).inv₀ hx_ne)
        (γ.deriv_continuous_off_partition x (h_sub hx) (h_avoid x hx))).congr hx_eq
    exact intervalIntegral.integral_hasDerivAt_right
      (h_int.mono_set (Set.uIcc_subset_uIcc_left
        (Set.uIcc_of_le γ.hab.le ▸ Ioo_subset_Icc_self ht)))
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hf_ca_all t ht_in)
      (hf_ca_all t ht_in)
  -- G constant on [a,σ₁]: G' = 0 since f = γ'/(γ-z₀) there
  have hG_const₁ : ∀ t ∈ Icc γ.a σ₁, G t = G γ.a := by
    rcases eq_or_lt_of_le hσ₁ with rfl | hlt
    · intro t ht; rw [show t = γ.a from le_antisymm ht.2 ht.1]
    · exact exp_cutoff_G_const_on γ z₀ ε hε f F P G rfl hG_cont hf_val hF_deriv hlt
        le_rfl (hσ₁₂.le.trans hσ₂) rfl (fun t ht => h_left t ⟨ht.1.le, ht.2⟩)
  -- G constant on [σ₂,b]: same argument
  have hG_const₂ : ∀ t ∈ Icc σ₂ γ.b, G t = G σ₂ := by
    rcases eq_or_lt_of_le hσ₂ with rfl | hlt
    · intro t ht; rw [show t = γ.b from le_antisymm ht.2 ht.1]
    · exact exp_cutoff_G_const_on γ z₀ ε hε f F P G rfl hG_cont hf_val hF_deriv hlt
        (hσ₁.trans hσ₁₂.le) le_rfl rfl (fun t ht => h_right t ⟨ht.1, ht.2.le⟩)
  -- Extract endpoint relations from G constant
  have h1 : (γ.toFun σ₁ - z₀) * cexp (-F σ₁) = γ.toFun γ.a - z₀ := by
    calc (γ.toFun σ₁ - z₀) * cexp (-F σ₁)
        = G σ₁ := rfl
      _ = G γ.a := hG_const₁ σ₁ ⟨hσ₁, le_refl _⟩
      _ = γ.toFun γ.a - z₀ := hGa
  have h2 : (γ.toFun γ.b - z₀) * cexp (-F γ.b) =
      (γ.toFun σ₂ - z₀) * cexp (-F σ₁) := by
    calc (γ.toFun γ.b - z₀) * cexp (-F γ.b)
        = G γ.b := rfl
      _ = G σ₂ := hG_const₂ γ.b ⟨hσ₂, le_refl _⟩
      _ = (γ.toFun σ₂ - z₀) * cexp (-F σ₂) := rfl
      _ = (γ.toFun σ₂ - z₀) * cexp (-F σ₁) := by rw [hF_mid]
  -- Algebra: from h1 and h2 with closedness, derive exp(F b) = ratio
  have h_expF₁ : cexp (-F σ₁) = (γ.toFun γ.a - z₀) / (γ.toFun σ₁ - z₀) := by
    rw [eq_div_iff hne_σ₁, mul_comm]; exact h1
  rw [← hclosed] at h2  -- γ(b) = γ(a)
  rw [h_expF₁] at h2
  -- h2 : (γ a - z₀) * exp(-F b) = (γ σ₂ - z₀) * ((γ a - z₀) / (γ σ₁ - z₀))
  have h_expFb : cexp (-F γ.b) = (γ.toFun σ₂ - z₀) / (γ.toFun σ₁ - z₀) := by
    rw [mul_div_assoc', mul_comm (γ.toFun σ₂ - z₀), mul_div_assoc] at h2
    exact mul_left_cancel₀ hne_a h2
  -- exp(F b) = (γ σ₁ - z₀) / (γ σ₂ - z₀)
  rw [show ∫ t_1 in γ.a..γ.b, f t_1 = F γ.b from rfl]
  have h_inv : cexp (F γ.b) = (cexp (-F γ.b))⁻¹ := by rw [Complex.exp_neg, inv_inv]
  rw [h_inv]
  rw [h_expFb, inv_div]

/-- If `σ ε ∈ [a,b]` eventually and `‖γ(σ ε) - z₀‖ = ε` eventually, then `σ ε → t₀` as `ε → 0⁺`,
since `t₀` is the unique zero of `γ - z₀` on `[a,b]` (compactness gives a positive lower bound
on the norm away from `t₀`). -/
private lemma crossing_sigma_tendsto_t₀
    (γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (σ : ℝ → ℝ)
    (hσ_Icc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), σ ε ∈ Icc γ.a γ.b)
    (hσ_val : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ.toFun (σ ε) - z₀‖ = ε) :
    Filter.Tendsto σ (𝓝[>] (0 : ℝ)) (𝓝 t₀) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  let K := Icc γ.a γ.b \ Metric.ball t₀ (δ/2)
  have hK_compact : IsCompact K := isCompact_Icc.diff Metric.isOpen_ball
  have hK_nonzero : ∀ t ∈ K, γ.toFun t ≠ z₀ := by
    intro t ⟨ht_Icc, ht_ball⟩ hγt
    have heq := honly t ht_Icc hγt
    simp only [Metric.mem_ball, Real.dist_eq] at ht_ball
    push Not at ht_ball
    subst heq; simp only [sub_self, abs_zero] at ht_ball; linarith
  by_cases hK_ne : K.Nonempty
  · have hcont_norm : ContinuousOn (fun t => ‖γ.toFun t - z₀‖) K :=
      continuous_norm.comp_continuousOn
        (γ.continuous_toFun.mono diff_subset |>.sub continuousOn_const)
    obtain ⟨tm, htm, htm_min⟩ := hK_compact.exists_isMinOn hK_ne hcont_norm
    have hm_pos : 0 < ‖γ.toFun tm - z₀‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hK_nonzero tm htm))
    filter_upwards [hσ_Icc, hσ_val, Ioo_mem_nhdsGT hm_pos] with ε hε_in hε_norm hε_lt
    simp only [Real.dist_eq]
    by_contra h; push Not at h
    have hσK : σ ε ∈ K := by
      refine ⟨hε_in, ?_⟩
      simp only [Metric.mem_ball, Real.dist_eq]
      push Not
      linarith
    have hmle : ‖γ.toFun tm - z₀‖ ≤ ‖γ.toFun (σ ε) - z₀‖ := htm_min hσK
    linarith [hε_lt.2, hmle.trans_eq hε_norm]
  · rw [not_nonempty_iff_eq_empty] at hK_ne
    filter_upwards [hσ_Icc] with ε hε_in
    simp only [Real.dist_eq]
    have hσ_ball : σ ε ∈ Metric.ball t₀ (δ/2) := by
      by_contra hball
      exact absurd (show σ ε ∈ (∅ : Set ℝ) from hK_ne ▸ ⟨hε_in, hball⟩)
        (Set.notMem_empty _)
    simp only [Metric.mem_ball, Real.dist_eq] at hσ_ball
    linarith

/-- Direction convergence: as ε → 0, the ratio (γ(σ₁(ε))-z₀)/(γ(σ₂(ε))-z₀)
(where σ₁(ε), σ₂(ε) are the boundary times from `exists_cutoff_boundary_times`)
converges to exp(-i·angleAtCrossing). This follows from the immersion property:
γ(σ₁)-z₀ ≈ L_left·(σ₁-t₀) with σ₁-t₀ < 0, so direction → -L_left/|L_left|,
and γ(σ₂)-z₀ ≈ L_right·(σ₂-t₀) with σ₂-t₀ > 0,
so direction → L_right/|L_right|.
The ratio of directions is exp(-i·α) where α = arg(L_right) - arg(-L_left). -/
lemma crossing_ratio_tendsto
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (σ₁ σ₂ : ℝ → ℝ)
    (hσ₁_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), σ₁ ε < t₀)
    (hσ₂_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t₀ < σ₂ ε)
    (hσ₁_val : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ.toFun (σ₁ ε) - z₀‖ = ε)
    (hσ₂_val : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ.toFun (σ₂ ε) - z₀‖ = ε)
    (hσ₁_in : ∀ᶠ ε in 𝓝[>] (0 : ℝ), γ.a ≤ σ₁ ε)
    (hσ₂_in : ∀ᶠ ε in 𝓝[>] (0 : ℝ), σ₂ ε ≤ γ.b) :
    Tendsto (fun ε => (γ.toFun (σ₁ ε) - z₀) / (γ.toFun (σ₂ ε) - z₀))
      (𝓝[>] 0)
      (𝓝 (Complex.exp (-(I * ↑(angleAtCrossing γ t₀ ht₀))))) := by
  -- ============================================================
  -- Step 1: Extract one-sided derivative limits L_L (left) and L_R (right)
  -- ============================================================
  obtain ⟨L_R, hL_R_ne, htend_R⟩ :
      ∃ L : ℂ, L ≠ 0 ∧ Filter.Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L) := by
    by_cases h : t₀ ∈ γ.partition
    · exact γ.right_deriv_limit t₀ h ht₀.2
    · exact ⟨_, γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) h,
             (γ.deriv_continuous_off_partition t₀ ht₀ h).tendsto.mono_left
               nhdsWithin_le_nhds⟩
  obtain ⟨L_L, hL_L_ne, htend_L⟩ :
      ∃ L : ℂ, L ≠ 0 ∧ Filter.Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L) := by
    by_cases h : t₀ ∈ γ.partition
    · exact γ.left_deriv_limit t₀ h ht₀.1
    · exact ⟨_, γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) h,
             (γ.deriv_continuous_off_partition t₀ ht₀ h).tendsto.mono_left
               nhdsWithin_le_nhds⟩
  have hL_R_pos : ‖L_R‖ > 0 := norm_pos_iff.mpr hL_R_ne
  have hL_L_pos : ‖L_L‖ > 0 := norm_pos_iff.mpr hL_L_ne
  -- ============================================================
  -- Step 2: Slope convergence: (γ(t)-z₀)/(t-t₀) → L
  -- ============================================================
  -- Get partition-free neighborhoods around t₀
  obtain ⟨r₀, hr₀, hr₀b, hno_R⟩ :
      ∃ r₀ > t₀, r₀ ≤ γ.b ∧ ∀ s ∈ Set.Ioo t₀ r₀, s ∉ γ.partition := by
    let Q := γ.partition.filter (fun x => t₀ < x)
    by_cases hQ : Q.Nonempty
    · have hmem := Finset.mem_filter.mp (Finset.min'_mem Q hQ)
      exact ⟨Q.min' hQ, hmem.2,
        le_trans (γ.partition_subset hmem.1).2 (le_refl _),
        fun s hs hc =>
          by linarith [Finset.min'_le Q s (Finset.mem_filter.mpr ⟨hc, hs.1⟩), hs.2]⟩
    · exact ⟨γ.b, ht₀.2, le_refl _,
        fun s hs hc => hQ ⟨s, Finset.mem_filter.mpr ⟨hc, hs.1⟩⟩⟩
  obtain ⟨l₀, hl₀, hl₀a, hno_L⟩ :
      ∃ l₀ < t₀, γ.a ≤ l₀ ∧ ∀ s ∈ Set.Ioo l₀ t₀, s ∉ γ.partition := by
    let Q := γ.partition.filter (fun x => x < t₀)
    by_cases hQ : Q.Nonempty
    · have hmem := Finset.mem_filter.mp (Finset.max'_mem Q hQ)
      exact ⟨Q.max' hQ, hmem.2,
        le_trans (γ.partition_subset hmem.1).1 (le_refl _),
        fun s hs hc =>
          by linarith [Finset.le_max' Q s (Finset.mem_filter.mpr ⟨hc, hs.2⟩), hs.1]⟩
    · exact ⟨γ.a, ht₀.1, le_refl _,
        fun s hs hc => hQ ⟨s, Finset.mem_filter.mpr ⟨hc, hs.2⟩⟩⟩
  -- HasDerivWithinAt on Ici/Iic
  have hHDWA_R : HasDerivWithinAt γ.toFun L_R (Set.Ici t₀) t₀ :=
    hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioo t₀ r₀)
      (fun s hs => (γ.smooth_off_partition s
        ⟨le_trans ht₀.1.le (le_of_lt hs.1), le_trans hs.2.le hr₀b⟩
        (hno_R s hs)).differentiableWithinAt)
      (γ.continuous_toFun.continuousAt
        (Icc_mem_nhds ht₀.1 ht₀.2)).continuousWithinAt
      (Ioo_mem_nhdsGT hr₀) htend_R
  have hHDWA_L : HasDerivWithinAt γ.toFun L_L (Set.Iic t₀) t₀ :=
    hasDerivWithinAt_Iic_of_tendsto_deriv (s := Set.Ioo l₀ t₀)
      (fun s hs => (γ.smooth_off_partition s
        ⟨le_trans hl₀a (le_of_lt hs.1), le_trans hs.2.le ht₀.2.le⟩
        (hno_L s hs)).differentiableWithinAt)
      (γ.continuous_toFun.continuousAt
        (Icc_mem_nhds ht₀.1 ht₀.2)).continuousWithinAt
      (Ioo_mem_nhdsLT hl₀) htend_L
  -- Slope tendsto: (γ(t) - z₀)/(t - t₀) → L
  have hslope_R : Filter.Tendsto
      (fun t => (γ.toFun t - z₀) / ((t - t₀ : ℝ) : ℂ)) (𝓝[>] t₀) (𝓝 L_R) := by
    rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ici_diff_left] at hHDWA_R
    convert hHDWA_R using 1
    ext t; simp only [slope, vsub_eq_sub, hcross, div_eq_mul_inv, mul_comm]
    erw [Complex.real_smul]; simp only [Complex.ofReal_inv]
  have hslope_L : Filter.Tendsto
      (fun t => (γ.toFun t - z₀) / ((t - t₀ : ℝ) : ℂ)) (𝓝[<] t₀) (𝓝 L_L) := by
    rw [hasDerivWithinAt_iff_tendsto_slope, Set.Iic_diff_right] at hHDWA_L
    convert hHDWA_L using 1
    ext t; simp only [slope, vsub_eq_sub, hcross, div_eq_mul_inv, mul_comm]
    erw [Complex.real_smul]; simp only [Complex.ofReal_inv]
  -- ============================================================
  -- Step 3: Direction convergence
  -- (γ(t)-z₀)/‖γ(t)-z₀‖ → L_R/‖L_R‖ as t→t₀⁺
  -- (γ(t)-z₀)/‖γ(t)-z₀‖ → -L_L/‖L_L‖ as t→t₀⁻
  -- ============================================================
  have hdir_R : Filter.Tendsto (fun t => (γ.toFun t - z₀) / ↑‖γ.toFun t - z₀‖)
      (𝓝[>] t₀) (𝓝 (L_R / ↑‖L_R‖)) := by
    have hLne : (‖L_R‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL_R_pos
    have hnorm_tend : Filter.Tendsto (fun t => ‖(γ.toFun t - z₀) / ((t - t₀ : ℝ) : ℂ)‖)
        (𝓝[>] t₀) (𝓝 ‖L_R‖) :=
      continuous_norm.continuousAt.tendsto.comp hslope_R
    apply (hslope_R.div hnorm_tend.ofReal hLne).congr'
    filter_upwards [hnorm_tend.eventually (Ioi_mem_nhds (by linarith : ‖L_R‖ / 2 < ‖L_R‖)),
                    self_mem_nhdsWithin] with t hpos htgt
    simp only [Set.mem_Ioi] at htgt
    have hd : t - t₀ > 0 := sub_pos.mpr htgt
    simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hd.le] at hpos
    have hfne : γ.toFun t - z₀ ≠ 0 := by
      intro h
      simp only [h, norm_zero, zero_div] at hpos
      linarith
    change (γ.toFun t - z₀) / ↑(t - t₀) / ↑‖(γ.toFun t - z₀) / ↑(t - t₀)‖ =
         (γ.toFun t - z₀) / ↑‖γ.toFun t - z₀‖
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hd.le]; push_cast
    field_simp [show (t : ℂ) - t₀ ≠ 0 from by exact_mod_cast ne_of_gt hd,
      norm_ne_zero_iff.mpr hfne, ne_of_gt hd]
  have hdir_L : Filter.Tendsto (fun t => (γ.toFun t - z₀) / ↑‖γ.toFun t - z₀‖)
      (𝓝[<] t₀) (𝓝 (-L_L / ↑‖L_L‖)) := by
    have hLne : (‖L_L‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL_L_pos
    have hnorm_tend : Filter.Tendsto (fun t => ‖(γ.toFun t - z₀) / ((t - t₀ : ℝ) : ℂ)‖)
        (𝓝[<] t₀) (𝓝 ‖L_L‖) :=
      continuous_norm.continuousAt.tendsto.comp hslope_L
    rw [neg_div]
    apply (hslope_L.div hnorm_tend.ofReal hLne).neg.congr'
    filter_upwards [hnorm_tend.eventually (Ioi_mem_nhds (by linarith : ‖L_L‖ / 2 < ‖L_L‖)),
                    self_mem_nhdsWithin] with t hpos htlt
    simp only [Set.mem_Iio] at htlt
    have hd : t - t₀ < 0 := sub_neg.mpr htlt
    simp only [norm_div, Complex.norm_real, Real.norm_of_nonpos hd.le] at hpos
    have hfne : γ.toFun t - z₀ ≠ 0 := by
      intro h
      simp only [h, norm_zero, zero_div] at hpos
      linarith
    change -((γ.toFun t - z₀) / ↑(t - t₀) / ↑‖(γ.toFun t - z₀) / ↑(t - t₀)‖) =
         (γ.toFun t - z₀) / ↑‖γ.toFun t - z₀‖
    rw [norm_div, Complex.norm_real, Real.norm_of_nonpos hd.le]; push_cast
    field_simp [show (t : ℂ) - t₀ ≠ 0 from by exact_mod_cast ne_of_lt hd,
      norm_ne_zero_iff.mpr hfne, ne_of_lt hd]
  -- ============================================================
  -- Step 4: σ₁(ε) → t₀ and σ₂(ε) → t₀ in nhds t₀
  -- ============================================================
  -- σ₁(ε) ∈ Icc a b eventually
  have hσ₁_Icc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), σ₁ ε ∈ Icc γ.a γ.b := by
    filter_upwards [hσ₁_in, hσ₁_lt] with ε ha hlt
    exact ⟨ha, le_of_lt (lt_trans hlt ht₀.2)⟩
  -- σ₂(ε) ∈ Icc a b eventually
  have hσ₂_Icc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), σ₂ ε ∈ Icc γ.a γ.b := by
    filter_upwards [hσ₂_in, hσ₂_gt] with ε hb hgt
    exact ⟨le_of_lt (lt_trans ht₀.1 hgt), hb⟩
  have hσ₁_tendsto := crossing_sigma_tendsto_t₀ γ z₀ t₀ honly σ₁ hσ₁_Icc hσ₁_val
  have hσ₂_tendsto := crossing_sigma_tendsto_t₀ γ z₀ t₀ honly σ₂ hσ₂_Icc hσ₂_val
  -- σ₁(ε) → t₀⁻ (i.e., in 𝓝[<] t₀)
  have hσ₁_nhds_lt : Filter.Tendsto σ₁ (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within σ₁
      hσ₁_tendsto
      (hσ₁_lt.mono fun ε h => h)
  -- σ₂(ε) → t₀⁺ (i.e., in 𝓝[>] t₀)
  have hσ₂_nhds_gt : Filter.Tendsto σ₂ (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within σ₂
      hσ₂_tendsto
      (hσ₂_gt.mono fun ε h => h)
  -- ============================================================
  -- Step 5: Direction limits after composing with σ₁, σ₂
  -- ============================================================
  -- (γ(σ₁(ε)) - z₀)/‖γ(σ₁(ε)) - z₀‖ → -L_L/‖L_L‖
  have hdir_σ₁ : Filter.Tendsto
      (fun ε => (γ.toFun (σ₁ ε) - z₀) / ↑‖γ.toFun (σ₁ ε) - z₀‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (-L_L / ↑‖L_L‖)) :=
    hdir_L.comp hσ₁_nhds_lt
  -- (γ(σ₂(ε)) - z₀)/‖γ(σ₂(ε)) - z₀‖ → L_R/‖L_R‖
  have hdir_σ₂ : Filter.Tendsto
      (fun ε => (γ.toFun (σ₂ ε) - z₀) / ↑‖γ.toFun (σ₂ ε) - z₀‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (L_R / ↑‖L_R‖)) :=
    hdir_R.comp hσ₂_nhds_gt
  -- ============================================================
  -- Step 6: Show ratio = direction ratio (using equal norms = ε)
  -- ============================================================
  have hL_L_ne' : (‖L_L‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL_L_pos
  have hL_R_ne' : (‖L_R‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL_R_pos
  -- The limit of the direction ratio
  have hdir_ratio : Filter.Tendsto
      (fun ε => (γ.toFun (σ₁ ε) - z₀) / ↑‖γ.toFun (σ₁ ε) - z₀‖ /
               ((γ.toFun (σ₂ ε) - z₀) / ↑‖γ.toFun (σ₂ ε) - z₀‖))
      (𝓝[>] (0 : ℝ)) (𝓝 ((-L_L / ↑‖L_L‖) / (L_R / ↑‖L_R‖))) := by
    apply hdir_σ₁.div hdir_σ₂
    intro h
    rw [div_eq_zero_iff] at h
    rcases h with h1 | h2
    · exact hL_R_ne h1
    · exact hL_R_ne' h2
  -- ============================================================
  -- Step 7: Algebraic identity: (-L_L/‖L_L‖)/(L_R/‖L_R‖) = exp(-I * α)
  -- ============================================================
  have halg : (-L_L / ↑‖L_L‖) / (L_R / ↑‖L_R‖) =
      Complex.exp (-(I * ↑(angleAtCrossing γ t₀ ht₀))) := by
    unfold angleAtCrossing
    by_cases h : t₀ ∈ γ.toPiecewiseC1Curve.partition
    · simp only [h, dite_true]
      set L_left := Classical.choose (γ.left_deriv_limit t₀ h ht₀.1)
      set L_right := Classical.choose (γ.right_deriv_limit t₀ h ht₀.2)
      have hL_left_spec := Classical.choose_spec (γ.left_deriv_limit t₀ h ht₀.1)
      have hL_right_spec := Classical.choose_spec (γ.right_deriv_limit t₀ h ht₀.2)
      have hL_L_eq : L_L = L_left :=
        tendsto_nhds_unique htend_L hL_left_spec.2
      have hL_R_eq : L_R = L_right :=
        tendsto_nhds_unique htend_R hL_right_spec.2
      rw [hL_L_eq, hL_R_eq]
      have hL_left_ne' : (‖L_left‖ : ℂ) ≠ 0 := by
        exact_mod_cast norm_ne_zero_iff.mpr hL_left_spec.1
      have hL_right_ne' : (‖L_right‖ : ℂ) ≠ 0 := by
        exact_mod_cast norm_ne_zero_iff.mpr hL_right_spec.1
      -- Polar form: -L_left / ‖L_left‖ = exp(arg(-L_left) * I)
      -- (Note: ‖-L_left‖ = ‖L_left‖ by norm_neg)
      have h_L_left_polar : -L_left / ↑‖L_left‖ =
          Complex.exp (↑(Complex.arg (-L_left)) * I) := by
        rw [← norm_neg L_left]
        exact complex_div_norm_eq_exp_arg (by rwa [norm_neg])
      have h_L_right_polar : L_right / ↑‖L_right‖ =
          Complex.exp (↑(Complex.arg L_right) * I) :=
        complex_div_norm_eq_exp_arg hL_right_ne'
      -- The goal after rw [hL_L_eq, hL_R_eq] is:
      -- -L_left / ↑‖L_left‖ / (L_right / ↑‖L_right‖)
      -- = exp(-(I * (arg L_right - arg(-L_left))))
      rw [h_L_left_polar, h_L_right_polar, ← Complex.exp_sub]
      congr 1; push_cast; ring
    · simp only [h, dite_false]
      -- Both L_L and L_R equal the derivative at t₀ (smooth point)
      have hcont := (γ.deriv_continuous_off_partition t₀ ht₀ h).tendsto
      have hL_L_eq_LR : L_L = L_R := by
        have hL_L : L_L = deriv γ.toFun t₀ :=
          tendsto_nhds_unique htend_L (hcont.mono_left nhdsWithin_le_nhds)
        have hL_R : L_R = deriv γ.toFun t₀ :=
          tendsto_nhds_unique htend_R (hcont.mono_left nhdsWithin_le_nhds)
        rw [hL_L, hL_R]
      rw [← hL_L_eq_LR]
      have hne : (‖L_L‖ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hL_L_pos
      have hratio : (-L_L / ↑‖L_L‖) / (L_L / ↑‖L_L‖) = -1 := by
        field_simp [hne, hL_L_ne]
      rw [hratio, show -(I * ↑Real.pi) = -(↑Real.pi * I) by ring,
          Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
  -- ============================================================
  -- Step 6 (final): Combine direction ratio convergence with algebraic identity
  -- ============================================================
  -- Rewrite target using the algebraic identity
  rw [← halg]
  -- Use Tendsto.congr' to switch the function to the direction ratio form
  apply hdir_ratio.congr'
  -- Eventually, ratio = direction ratio (since ‖γ(σ₁)-z₀‖ = ε = ‖γ(σ₂)-z₀‖)
  filter_upwards [hσ₁_val, hσ₂_val, self_mem_nhdsWithin] with ε hε₁ hε₂ hε_pos
  simp only [Set.mem_Ioi] at hε_pos
  set a₁ := γ.toFun (σ₁ ε) - z₀
  set b₁ := γ.toFun (σ₂ ε) - z₀
  have ha_ne : (‖a₁‖ : ℂ) ≠ 0 := by exact_mod_cast hε₁ ▸ ne_of_gt hε_pos
  have hb_ne : (‖b₁‖ : ℂ) ≠ 0 := by exact_mod_cast hε₂ ▸ ne_of_gt hε_pos
  have hb_ne' : b₁ ≠ 0 := by intro h; rw [h, norm_zero] at hε₂; linarith
  field_simp [ha_ne, hb_ne, hb_ne']
  congr 1; rw [hε₁, hε₂]

/-- **Core analysis**: `exp(R(ε)) → exp(-iα)` as `ε → 0`, where `R(ε)` is the
cutoff integral `∫ 1_{‖γ-z₀‖>ε} (γ-z₀)⁻¹ γ'` and `α` is the crossing angle.

**Proof strategy** (H-W Proposition 2.2):
1. For each small `ε`, the set `{t : ‖γ(t)-z₀‖ ≤ ε}` is a single
   interval `(σ₁(ε), σ₂(ε))`
   containing `t₀` (by continuity + isolated crossing).
2. By piecewise FTC on segments where `‖γ-z₀‖ > ε` (using the G-function technique from
   `exp_integral_eq_endpoint_ratio_piecewise`):
   `exp(R(ε)) = (γ(σ₁)-z₀)/(γ(a)-z₀) · (γ(b)-z₀)/(γ(σ₂)-z₀)`.
3. By closedness `γ(a) = γ(b)`: `exp(R(ε)) = (γ(σ₁)-z₀)/(γ(σ₂)-z₀)`.
4. Since `‖γ(σ₁)-z₀‖ = ε = ‖γ(σ₂)-z₀‖`, this ratio has modulus 1.
5. By the immersion property: as `ε → 0`, `σ₁ → t₀⁻` and `σ₂ → t₀⁺`, and
   `arg(γ(σ₁)-z₀) → arg(-L_left)`, `arg(γ(σ₂)-z₀) → arg(L_right)`.
6. Therefore `exp(R(ε)) → exp(i(arg(-L_left) - arg(L_right))) = exp(-iα)`. -/
lemma tendsto_exp_cutoff_integral_crossing
    (γ : PiecewiseC1Immersion)
    (hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀) :
    Tendsto (fun ε => Complex.exp (∫ t in γ.a..γ.b,
      if ‖γ.toFun t - z₀‖ > ε
      then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0))
      (𝓝[>] 0)
      (𝓝 (Complex.exp (-(I * ↑(angleAtCrossing γ t₀ ht₀))))) := by
  -- Step 1: Get boundary times
  obtain ⟨δ, hδ, hbnd⟩ := exists_cutoff_boundary_times γ z₀ t₀ ht₀ hcross honly
  -- Step 2: Define σ₁(ε) and σ₂(ε) via Classical.choose
  let σ₁ : ℝ → ℝ := fun ε =>
    if h : ε ∈ Ioo 0 δ then (hbnd ε h).choose else t₀
  let σ₂ : ℝ → ℝ := fun ε =>
    if h : ε ∈ Ioo 0 δ then (hbnd ε h).choose_spec.choose else t₀
  -- Helper: extract properties for ε in (0,δ)
  have hprops : ∀ ε (hε : ε ∈ Ioo 0 δ),
      γ.a ≤ σ₁ ε ∧ σ₁ ε < t₀ ∧ t₀ < σ₂ ε ∧ σ₂ ε ≤ γ.b ∧
      ‖γ.toFun (σ₁ ε) - z₀‖ = ε ∧ ‖γ.toFun (σ₂ ε) - z₀‖ = ε ∧
      (∀ t ∈ Ico γ.a (σ₁ ε), ε < ‖γ.toFun t - z₀‖) ∧
      (∀ t ∈ Ioc (σ₂ ε) γ.b, ε < ‖γ.toFun t - z₀‖) ∧
      (∀ t ∈ Icc (σ₁ ε) (σ₂ ε), ‖γ.toFun t - z₀‖ ≤ ε) := by
    intro ε hε
    simp only [σ₁, σ₂, hε, dif_pos]
    exact (hbnd ε hε).choose_spec.choose_spec
  have hIoo_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ
  -- Step 3: For ε ∈ (0,δ), exp(R(ε)) = (γ(σ₁)-z₀)/(γ(σ₂)-z₀)
  have h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Complex.exp (∫ t in γ.a..γ.b,
        if ‖γ.toFun t - z₀‖ > ε
        then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0) =
      (γ.toFun (σ₁ ε) - z₀) / (γ.toFun (σ₂ ε) - z₀) := by
    exact hIoo_ev.mono fun ε hε => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hprops ε hε
      exact exp_cutoff_integral_eq_ratio γ hclosed z₀ _ _ ε
        h1 (lt_trans h2 h3) h4 hε.1 h5 h6 h7 h8 h9
  -- Step 4: The ratio converges to exp(-iα) by direction analysis
  have h_lim : Tendsto (fun ε => (γ.toFun (σ₁ ε) - z₀) / (γ.toFun (σ₂ ε) - z₀))
      (𝓝[>] 0)
      (𝓝 (Complex.exp (-(I * ↑(angleAtCrossing γ t₀ ht₀))))) := by
    exact crossing_ratio_tendsto γ z₀ t₀ ht₀ hcross honly σ₁ σ₂
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.1)
  -- Step 5: Conclude by Tendsto.congr'
  exact Filter.Tendsto.congr'
    (Filter.Eventually.mono h_eq fun _ h => h.symm) h_lim


end
