/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.GammaAnalysis
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# PV Infrastructure: Remainder Analysis

Taylor expansion and C² remainder bounds for the PV integrand.
The key result `remainder_bounded_of_C2` shows that the remainder
`r(t) = (γ-γ₀)⁻¹γ' - (t-t₀)⁻¹` is bounded (O(1)) near t₀.

## Main Results

* `remainder_bounded_of_C2` — bounded remainder from C² smoothness
* `numerator_quadratic_bound` — numerator is O(|t-t₀|²)
* `quadratic_approx_of_contDiffAt_two` — quadratic Taylor approximation
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

private lemma taylor_one_eq_linear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (s : Set ℝ) (a x : ℝ) :
    taylorWithinEval f 1 s a x =
      f a + (x - a) • derivWithin f s a := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton]
  simp [iteratedDerivWithin_zero, iteratedDerivWithin_one,
    Nat.factorial]

private lemma contDiffOn_Icc_of_contDiffAt
    {γ : ℝ → ℂ} {t₀ : ℝ} {n : ℕ}
    (hγ : ContDiffAt ℝ n γ t₀) :
    ∃ δ > 0,
      ContDiffOn ℝ n γ (Set.Icc (t₀ - δ) (t₀ + δ)) := by
  obtain ⟨u, hu_mem, hγ_on⟩ :=
    hγ.contDiffOn (m := n) le_rfl
      (by simp only [ENat.natCast_ne_coe_top, WithTop.natCast_ne_top, imp_self])
  obtain ⟨r, hr_pos, hball_sub⟩ :=
    Metric.mem_nhds_iff.mp hu_mem
  use r / 2, by linarith
  apply hγ_on.mono
  intro x hx
  apply hball_sub
  simp only [Metric.mem_ball, Real.dist_eq]
  have h1 : t₀ - r / 2 ≤ x := hx.1
  have h2 : x ≤ t₀ + r / 2 := hx.2
  rw [abs_sub_lt_iff]; constructor <;> linarith

private lemma bound_iteratedDerivWithin_two_on_Icc
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ContDiffOn ℝ 2 γ (Set.Icc a b)) :
    ∃ C ≥ 0, ∀ y ∈ Set.Icc a b,
      ‖iteratedDerivWithin 2 γ (Set.Icc a b) y‖ ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ.continuousOn_iteratedDerivWithin (by norm_cast) (uniqueDiffOn_Icc hab))
  by_cases hM_neg : M < 0
  · use 0, le_refl 0
    intro y hy
    have := hM y hy
    linarith [norm_nonneg
      (iteratedDerivWithin 2 γ (Set.Icc a b) y)]
  · exact ⟨M, le_of_not_gt hM_neg, hM⟩

/-- C¹ regularity of `deriv γ` from C² regularity of `γ`. -/
lemma contDiffAt_one_deriv_of_contDiffAt_two
    {γ : ℝ → ℂ} {t₀ : ℝ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) :
    ContDiffAt ℝ 1 (deriv γ) t₀ := by
  have h_apply := (show ContDiffAt ℝ (1 + 1) γ t₀ from hγ_C2).fderiv_right_succ.clm_apply
    (contDiffAt_const (c := (1 : ℝ)))
  rw [show (fun t => (fderiv ℝ γ t) 1) = deriv γ from by
    ext t; exact fderiv_apply_one_eq_deriv.symm] at h_apply
  exact h_apply

/-- Lipschitz-type bound on `deriv γ` deviation from C². -/
lemma deriv_deviation_bound_of_C2
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀)
    (hγ_deriv : deriv γ t₀ = L) :
    ∃ K δ, 0 < δ ∧ ∀ t, |t - t₀| < δ →
      ‖deriv γ t - L‖ ≤ K * |t - t₀| := by
  obtain ⟨K, s, hs_nhds, h_lip⟩ :=
    (contDiffAt_one_deriv_of_contDiffAt_two hγ_C2).exists_lipschitzOnWith
  obtain ⟨δ, hδ_pos, hball_sub⟩ := Metric.mem_nhds_iff.mp hs_nhds
  refine ⟨K, δ, hδ_pos, fun t ht => ?_⟩
  have h := h_lip.dist_le_mul t
    (hball_sub (Metric.mem_ball.mpr (by rwa [Real.dist_eq])))
    t₀ (hball_sub (Metric.mem_ball.mpr (by simp [hδ_pos])))
  rwa [dist_eq_norm, hγ_deriv, Real.dist_eq] at h

/-- Quadratic Taylor approximation from C² smoothness. -/
lemma quadratic_approx_of_contDiffAt_two
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀)
    (hγ_deriv : deriv γ t₀ = L) :
    ∃ K δ, 0 < δ ∧ 0 < K ∧ ∀ t, |t - t₀| < δ →
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤
        K * |t - t₀| ^ 2 := by
  obtain ⟨M, δ₁, hδ₁_pos, h_deriv_dev⟩ :=
    deriv_deviation_bound_of_C2 hγ_C2 hγ_deriv
  have h_C1_at : ContDiffAt ℝ 1 γ t₀ :=
    hγ_C2.of_le one_le_two
  have h_diff_at : DifferentiableAt ℝ γ t₀ :=
    h_C1_at.differentiableAt one_ne_zero
  have h1_ne_top : (1 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞) := by
    intro heq
    have : (1 : ℕ∞) = ⊤ := WithTop.coe_injective heq
    exact ENat.one_ne_top this
  have h_evt_C1 : ∀ᶠ s in 𝓝 t₀, ContDiffAt ℝ 1 γ s :=
    h_C1_at.eventually h1_ne_top
  have h_evt_diff :
      ∀ᶠ s in 𝓝 t₀, DifferentiableAt ℝ γ s :=
    h_evt_C1.mono (fun s hs => hs.differentiableAt one_ne_zero)
  obtain ⟨δ₂, hδ₂_pos, h_diff_ball⟩ :=
    Metric.eventually_nhds_iff.mp h_evt_diff
  let δ := min δ₁ δ₂
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  let K := M + 1
  have hM_nonneg : 0 ≤ M := by
    by_contra hM_neg
    push Not at hM_neg
    have ⟨t, ht_pos, ht_lt⟩ :
        ∃ t, 0 < |t - t₀| ∧ |t - t₀| < δ₁ := by
      use t₀ + δ₁ / 2
      simp only [add_sub_cancel_left,
        abs_of_pos (half_pos hδ₁_pos)]
      exact ⟨half_pos hδ₁_pos, half_lt_self hδ₁_pos⟩
    have h := h_deriv_dev t ht_lt
    have h_neg : M * |t - t₀| < 0 :=
      mul_neg_of_neg_of_pos hM_neg ht_pos
    linarith [norm_nonneg (deriv γ t - L)]
  have hK_pos : 0 < K := by linarith
  use K, δ, hδ_pos, hK_pos
  intro t ht
  by_cases ht_eq : t = t₀
  · simp [ht_eq]
  let f₁ : ℝ → ℂ := γ
  let f₂ : ℝ → ℂ := fun _ => γ t₀
  let f₃ : ℝ → ℂ := fun s => (s - t₀) • L
  let h := fun s => f₁ s - f₂ s - f₃ s
  have ht_lt_δ₁ : |t - t₀| < δ₁ :=
    lt_of_lt_of_le ht (min_le_left _ _)
  have ht_lt_δ₂ : |t - t₀| < δ₂ :=
    lt_of_lt_of_le ht (min_le_right _ _)
  have h_uIcc_sub_ball :
      Set.uIcc t₀ t ⊆ Metric.ball t₀ δ₂ := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq]
    exact lt_of_le_of_lt
      (Set.abs_sub_left_of_mem_uIcc hs) ht_lt_δ₂
  have h_γ_diff_on :
      ∀ s ∈ Set.uIcc t₀ t,
        DifferentiableAt ℝ γ s := by
    intro s hs
    exact h_diff_ball (h_uIcc_sub_ball hs)
  have h_f₂_diff :
      ∀ s, DifferentiableAt ℝ f₂ s :=
    fun _ => differentiableAt_const _
  have h_f₃_diff :
      ∀ s, DifferentiableAt ℝ f₃ s := fun _ =>
    (differentiableAt_id.sub
      (differentiableAt_const _)).smul_const _
  have h_diff :
      ∀ s ∈ Set.uIcc t₀ t,
        DifferentiableAt ℝ h s := by
    intro s hs
    exact ((h_γ_diff_on s hs).sub
      (h_f₂_diff s)).sub (h_f₃_diff s)
  have h_deriv_f₂ : ∀ s, deriv f₂ s = 0 :=
    fun s => deriv_const s (γ t₀)
  have h_deriv_f₃ : ∀ s, deriv f₃ s = L :=
    fun s => by
    simp only [f₃]
    have hid : deriv (fun x : ℝ => x) s = 1 :=
      deriv_id s
    have hsub : deriv (fun x => x - t₀) s = 1 := by
      rw [deriv_sub_const, hid]
    have : deriv (fun s => (s - t₀) • L) s = deriv (fun s => s - t₀) s • L :=
      deriv_smul_const (differentiableAt_id.sub (differentiableAt_const _)) L
    rw [this, hsub]; simp
  have h_deriv :
      ∀ s ∈ Set.uIcc t₀ t,
        deriv h s = deriv γ s - L := by
    intro s hs
    have hs_diff : DifferentiableAt ℝ γ s :=
      h_γ_diff_on s hs
    have h_eq_sub :
        h = fun s => (f₁ s - f₂ s) - f₃ s := by
      ext; simp [h, f₁, f₂, f₃]
    have h_diff_f1f2 :
        DifferentiableAt ℝ (fun s => f₁ s - f₂ s) s :=
      hs_diff.sub (h_f₂_diff s)
    have step1 :
        deriv h s =
          deriv (fun s => (f₁ s - f₂ s) - f₃ s) s := by
      rw [← h_eq_sub]
    have step2 :
        deriv (fun s => (f₁ s - f₂ s) - f₃ s) s =
          deriv (fun s => f₁ s - f₂ s) s -
            deriv f₃ s :=
      deriv_sub h_diff_f1f2 (h_f₃_diff s)
    have step3 :
        deriv (fun s => f₁ s - f₂ s) s =
          deriv f₁ s - deriv f₂ s :=
      deriv_sub hs_diff (h_f₂_diff s)
    simp only [step1, step2, step3,
      h_deriv_f₂, h_deriv_f₃, sub_zero, f₁]
  have h_at_t₀ : h t₀ = 0 := by
    simp only [h, f₁, f₂, f₃, sub_self]; simp
  have h_deriv_bound :
      ∀ s ∈ Set.uIcc t₀ t,
        ‖deriv h s‖ ≤ M * |t - t₀| := by
    intro s hs
    rw [h_deriv s hs]
    have hs_bound : |s - t₀| ≤ |t - t₀| :=
      Set.abs_sub_left_of_mem_uIcc hs
    have hs_lt : |s - t₀| < δ₁ :=
      lt_of_le_of_lt hs_bound ht_lt_δ₁
    calc ‖deriv γ s - L‖
        ≤ M * |s - t₀| := h_deriv_dev s hs_lt
      _ ≤ M * |t - t₀| :=
        mul_le_mul_of_nonneg_left hs_bound hM_nonneg
  have h_bound :=
    Convex.norm_image_sub_le_of_norm_deriv_le h_diff
      h_deriv_bound (convex_uIcc t₀ t)
      Set.left_mem_uIcc Set.right_mem_uIcc
  rw [h_at_t₀, sub_zero, Real.norm_eq_abs] at h_bound
  have h_eq : h t = γ t - γ t₀ - (t - t₀) • L := by
    simp only [h, f₁, f₂, f₃]
  calc ‖γ t - γ t₀ - (t - t₀) • L‖
      = ‖h t‖ := by rw [h_eq]
    _ ≤ M * |t - t₀| * |t - t₀| := h_bound
    _ = M * |t - t₀| ^ 2 := by ring
    _ ≤ K * |t - t₀| ^ 2 := by
        nlinarith [sq_nonneg |t - t₀|]

/-- Bounded slope deviation from C² smoothness. -/
lemma bounded_slope_deviation_of_contDiffAt_two
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀)
    (hγ_deriv : deriv γ t₀ = L) :
    ∃ K δ, 0 < δ ∧ 0 < K ∧
      ∀ t, 0 < |t - t₀| → |t - t₀| < δ →
        ‖(γ t - γ t₀) / (↑(t - t₀)) - L‖ ≤
          K * |t - t₀| := by
  obtain ⟨K₁, δ₁, hδ₁_pos, hK₁_pos, h_quad⟩ :=
    quadratic_approx_of_contDiffAt_two hγ_C2 hγ_deriv
  refine ⟨K₁, δ₁, hδ₁_pos, hK₁_pos,
    fun t ht_pos ht_lt => ?_⟩
  have ht_ne : (↑(t - t₀) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_pos.mp ht_pos)
  rw [show (γ t - γ t₀) / (↑(t - t₀)) - L =
      (γ t - γ t₀ - (t - t₀) • L) / (↑(t - t₀)) from by
    rw [Complex.real_smul]; field_simp [ht_ne],
    norm_div, Complex.norm_real _]
  calc ‖γ t - γ t₀ - (t - t₀) • L‖ / |t - t₀|
      ≤ K₁ * |t - t₀| ^ 2 / |t - t₀| :=
        div_le_div_of_nonneg_right (h_quad t ht_lt) ht_pos.le
    _ = K₁ * |t - t₀| := by field_simp

/-- Numerator quadratic bound for `(t-t₀)γ'(t) - (γt - γt₀)`. -/
lemma numerator_quadratic_bound
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀)
    (hγ_deriv : deriv γ t₀ = L) :
    ∃ K δ, 0 < δ ∧ ∀ t, |t - t₀| < δ →
      ‖(↑(t - t₀) : ℂ) * deriv γ t -
        (γ t - γ t₀)‖ ≤ K * |t - t₀| ^ 2 := by
  obtain ⟨K₁, δ₁, hδ₁_pos, _, h_quad⟩ :=
    quadratic_approx_of_contDiffAt_two hγ_C2 hγ_deriv
  obtain ⟨K₂, δ₂, hδ₂_pos, h_deriv⟩ :=
    deriv_deviation_bound_of_C2 hγ_C2 hγ_deriv
  let δ := min δ₁ δ₂
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  use K₁ + K₂ + 1, δ, hδ_pos
  intro t ht
  have ht₁ : |t - t₀| < δ₁ :=
    lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : |t - t₀| < δ₂ :=
    lt_of_lt_of_le ht (min_le_right _ _)
  have h_identity :
      (↑(t - t₀) : ℂ) * deriv γ t - (γ t - γ t₀) =
        (↑(t - t₀) : ℂ) * (deriv γ t - L) -
          (γ t - γ t₀ - (t - t₀) • L) := by
    rw [Complex.real_smul]; ring
  rw [h_identity]
  have h1 :
      ‖(↑(t - t₀) : ℂ) * (deriv γ t - L)‖ ≤
        |t - t₀| * (K₂ * |t - t₀|) := by
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left
      (h_deriv t ht₂) (abs_nonneg _)
  have h2 :
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤
        K₁ * |t - t₀| ^ 2 :=
    h_quad t ht₁
  calc ‖(↑(t - t₀) : ℂ) * (deriv γ t - L) -
        (γ t - γ t₀ - (t - t₀) • L)‖
      ≤ ‖(↑(t - t₀) : ℂ) * (deriv γ t - L)‖ +
        ‖γ t - γ t₀ - (t - t₀) • L‖ :=
        norm_sub_le _ _
    _ ≤ |t - t₀| * (K₂ * |t - t₀|) +
        K₁ * |t - t₀| ^ 2 :=
        add_le_add h1 h2
    _ = (K₁ + K₂) * |t - t₀| ^ 2 := by ring
    _ ≤ (K₁ + K₂ + 1) * |t - t₀| ^ 2 := by
        nlinarith [sq_nonneg |t - t₀|]

/-- Bounded remainder from C² smoothness. -/
lemma remainder_bounded_of_C2
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀)
    (hγ_deriv : deriv γ t₀ = L) :
    ∃ C δ, 0 < δ ∧ ∀ t,
      0 < |t - t₀| → |t - t₀| < δ →
        ‖(γ t - γ t₀)⁻¹ * deriv γ t -
          (↑(t - t₀))⁻¹‖ ≤ C := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hγ_diff : DifferentiableAt ℝ γ t₀ :=
    hγ_C2.differentiableAt two_ne_zero
  have hγ_hasderiv : HasDerivAt γ L t₀ := by
    rw [← hγ_deriv]; exact hγ_diff.hasDerivAt
  obtain ⟨δ₁, hδ₁_pos, h_lower⟩ :=
    gamma_lower_bound_of_hasDerivAt hL hγ_hasderiv
  obtain ⟨K, δ₂, hδ₂_pos, h_numer⟩ :=
    numerator_quadratic_bound hγ_C2 hγ_deriv
  let δ := min δ₁ δ₂
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  refine ⟨2 * K / ‖L‖, δ, hδ_pos,
    fun t ht_pos ht_lt => ?_⟩
  have ht₁ : |t - t₀| < δ₁ :=
    lt_of_lt_of_le ht_lt (min_le_left _ _)
  have ht₂ : |t - t₀| < δ₂ :=
    lt_of_lt_of_le ht_lt (min_le_right _ _)
  have h_Δγ_ne : γ t - γ t₀ ≠ 0 := by
    have h := h_lower t ht_pos ht₁
    intro heq; rw [heq, norm_zero] at h
    linarith [mul_pos (half_pos hL_norm_pos) ht_pos]
  have ht_ne : (↑(t - t₀) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_pos.mp ht_pos)
  have h_identity :
      (γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹ =
        ((↑(t - t₀) : ℂ) * deriv γ t -
          (γ t - γ t₀)) /
        ((γ t - γ t₀) * (↑(t - t₀))) := by
    field_simp [h_Δγ_ne, ht_ne]
  rw [h_identity, norm_div]
  have h_numer_bound :
      ‖(↑(t - t₀) : ℂ) * deriv γ t -
        (γ t - γ t₀)‖ ≤ K * |t - t₀| ^ 2 :=
    h_numer t ht₂
  have h_denom_lower :
      (‖L‖ / 2) * |t - t₀| ^ 2 ≤
        ‖(γ t - γ t₀) * (↑(t - t₀))‖ := by
    rw [norm_mul, Complex.norm_real]
    have h := h_lower t ht_pos ht₁
    calc (‖L‖ / 2) * |t - t₀| ^ 2
        = (‖L‖ / 2 * |t - t₀|) * |t - t₀| := by
          ring
      _ ≤ ‖γ t - γ t₀‖ * |t - t₀| :=
          mul_le_mul_of_nonneg_right h (abs_nonneg _)
  have h_denom_pos :
      0 < ‖(γ t - γ t₀) * (↑(t - t₀))‖ := by
    rw [norm_mul, Complex.norm_real]
    exact mul_pos (norm_pos_iff.mpr h_Δγ_ne) ht_pos
  have h_sq_pos : 0 < |t - t₀| ^ 2 :=
    sq_pos_of_pos ht_pos
  have h_K_nonneg : 0 ≤ K * |t - t₀| ^ 2 :=
    le_trans (norm_nonneg _) h_numer_bound
  have h_d_pos : 0 < (‖L‖ / 2) * |t - t₀| ^ 2 :=
    mul_pos (half_pos hL_norm_pos) h_sq_pos
  calc ‖(↑(t - t₀) : ℂ) * deriv γ t -
        (γ t - γ t₀)‖ /
      ‖(γ t - γ t₀) * (↑(t - t₀))‖
      ≤ (K * |t - t₀| ^ 2) /
        ((‖L‖ / 2) * |t - t₀| ^ 2) :=
        div_le_div₀ h_K_nonneg h_numer_bound
          h_d_pos h_denom_lower
    _ = 2 * K / ‖L‖ := by
        field_simp [ne_of_gt h_sq_pos,
          ne_of_gt hL_norm_pos]

end
