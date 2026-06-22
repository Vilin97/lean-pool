/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.OnCurvePV.Basic

/-!
# On-Curve PV: Endpoint and Corner CPV

Cauchy principal value existence at the endpoint `1/2 + H*I` and corner `-1/2 + H*I`
of the fundamental domain boundary `fdBoundaryH H`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `∫ t in a..1, t⁻¹ = log 1 - log a` for `0 < a ≤ 1`. -/
private lemma integral_inv_eq_log_sub (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∫ t in a..1, (↑t : ℂ)⁻¹ = Complex.log ↑(1 : ℝ) - Complex.log ↑a := by
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal]
  have hderiv : ∀ t ∈ Set.uIcc a 1,
      HasDerivAt (fun t => Real.log t) (t⁻¹) t := by
    intro t ht; rw [Set.uIcc_of_le ha1] at ht
    exact Real.hasDerivAt_log (by linarith [ht.1] : t ≠ 0)
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹) MeasureTheory.volume a 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht; rw [Set.uIcc_of_le ha1, Set.mem_Icc] at ht
    simp only [id]; linarith [ht.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Real.log_one,
    Complex.ofReal_one, Complex.log_one, ← Complex.ofReal_log ha.le]
  push_cast; ring

/-- `∫ t in 4..(5 - η), (t - 5)⁻¹ = log η` for `0 < η < 1`. -/
private lemma integral_shifted_inv_eq_log (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∫ t in (4 : ℝ)..(5 - η), (↑(t - 5) : ℂ)⁻¹ = ↑(Real.log η) := by
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal]
  congr 1
  have h5η : (4 : ℝ) ≤ 5 - η := by linarith
  have hderiv : ∀ t ∈ Set.uIcc 4 (5 - η),
      HasDerivAt (fun t => Real.log (t - 5)) ((t - 5)⁻¹) t := by
    intro t ht; rw [Set.uIcc_of_le h5η] at ht
    have : t - 5 ≠ 0 := ne_of_lt (by linarith [ht.2])
    have h1 := (Real.hasDerivAt_log this).comp t ((hasDerivAt_id t).sub_const 5)
    simp only [Function.comp_def, mul_one] at h1; exact h1
  have hint : IntervalIntegrable (fun t => (t - 5)⁻¹) MeasureTheory.volume 4 (5 - η) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
    intro t ht; rw [Set.uIcc_of_le h5η, Set.mem_Icc] at ht
    simp only [id]; exact ne_of_lt (by linarith [ht.2])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [show 5 - η - 5 = -η from by ring, show (4 : ℝ) - 5 = -(1 : ℝ) from by ring]
  rw [Real.log_neg_eq_log, Real.log_neg_eq_log, Real.log_one, sub_zero]

/-- The endpoint `s = 1/2 + H*I` is not hit by segments 1--4 of `fdBoundaryH H`. -/
private lemma endpoint_avoid_14 (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    let s := (1/2 : ℂ) + ↑H * I
    ∀ t ∈ Set.Icc (1 : ℝ) 4, fdBoundaryH H t ≠ s := by
  intro s t ht habs
  rw [Set.mem_Icc] at ht
  by_cases ht3 : t ≤ 3
  · by_cases ht1 : t = 1
    · subst ht1
      rw [fdBoundary_H_at_one] at habs
      have h_im := congr_arg Complex.im habs
      simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
        UpperHalfPlane.coe_mk, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.div_ofNat, mul_zero, mul_one, s] at h_im
      linarith
    · have ht1' : 1 < t := lt_of_le_of_ne ht.1 (Ne.symm ht1)
      have h_norm : ‖fdBoundaryH H t‖ = 1 :=
        fdBoundary_H_eq_arc ht1' (lt_of_le_of_ne ht3 (by
          intro h; subst h
          have hγ3_eq : fdBoundaryH H 3 = fdBoundary 3 := by
            rw [fdBoundary_H_at_three]
            exact fdBoundary_at_three.symm
          rw [hγ3_eq, fdBoundary_at_three] at habs
          have him := congr_arg Complex.im habs
          simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
            Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat, s] at him
          linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 from by norm_num)])) |>.symm ▸
        Complex.norm_exp_ofReal_mul_I _
      rw [habs] at h_norm
      have : 1 < ‖s‖ := by
        have h_nsq : 1 < Complex.normSq s := by
          simp only [s, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
            Complex.add_im, Complex.mul_im, Complex.one_re, Complex.one_im,
            Complex.div_ofNat]
          have hH0 : 0 < H := by
            linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 from by norm_num)]
          nlinarith [mul_lt_mul hH hH.le (by positivity : (0 : ℝ) < Real.sqrt 3 / 2) hH0.le,
                     Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 from by norm_num)]
        calc (1 : ℝ) = Real.sqrt 1 := by simp only [Real.sqrt_one]
          _ < Real.sqrt (Complex.normSq s) := Real.sqrt_lt_sqrt (by norm_num) h_nsq
          _ = ‖s‖ := rfl
      linarith
  · push Not at ht3
    have h_re_t := fdBoundary_H_seg4_re' H ht3 ht.2
    rw [habs] at h_re_t
    simp [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im] at h_re_t
    norm_num at h_re_t

/-- The endpoint `s = 1/2 + H*I` has positive distance to the boundary on `[1, 4]`. -/
private lemma endpoint_min_dist (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    let s := (1/2 : ℂ) + ↑H * I
    ∃ δ > 0, ∀ t ∈ Set.Icc (1 : ℝ) 4, δ ≤ ‖fdBoundaryH H t - s‖ := by
  intro s
  have h_cont_norm : ContinuousOn (fun t => ‖fdBoundaryH H t - s‖)
      (Set.Icc (1 : ℝ) 4) :=
    ((fdBoundary_H_continuous H).continuousOn.sub continuousOn_const).norm.mono
      (Set.Icc_subset_Icc (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (4 : ℝ) ≤ 5))
  have h_pos_norm : ∀ t ∈ Set.Icc (1 : ℝ) 4, 0 < ‖fdBoundaryH H t - s‖ :=
    fun t ht => norm_pos_iff.mpr (sub_ne_zero.mpr (endpoint_avoid_14 H hH t ht))
  exact isCompact_Icc.exists_forall_le' h_cont_norm h_pos_norm

/-- Segment 1 difference: `fdBoundaryH H t - s = (-t) * c * I` for the endpoint. -/
private lemma endpoint_diff_seg1 (H : ℝ) (s : ℂ) (hs_def : s = (1 / 2 : ℂ) + ↑H * I)
    (c : ℝ) (hc_def : c = H - Real.sqrt 3 / 2) (t : ℝ) (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    fdBoundaryH H t - s = ↑((-t) * c) * I := by
  rw [fdBoundary_H_eq_seg1_H ht1, hs_def]
  simp only [fdBoundarySeg1H, hc_def]
  push_cast; ring

/-- Segment 5 difference: `fdBoundaryH H t - s = t - 5` for the endpoint. -/
private lemma endpoint_diff_seg5 (H : ℝ) (s : ℂ) (hs_def : s = (1 / 2 : ℂ) + ↑H * I)
    (t : ℝ) (ht4 : 4 < t) :
    fdBoundaryH H t - s = ↑(t - 5) := by
  rw [fdBoundary_H_eq_seg5_H ht4, hs_def]
  simp only [fdBoundarySeg5H]
  push_cast; ring

/-- Norm on seg1: `‖fdBoundaryH H t - s‖ = t * c` for the endpoint. -/
private lemma endpoint_norm_seg1 (H : ℝ) (s : ℂ) (hs_def : s = (1 / 2 : ℂ) + ↑H * I)
    (c : ℝ) (hc_def : c = H - Real.sqrt 3 / 2) (hc : 0 < c)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖fdBoundaryH H t - s‖ = t * c := by
  rw [endpoint_diff_seg1 H s hs_def c hc_def t ht0 ht1, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_nonpos (by nlinarith : (-t) * c ≤ 0)]
  ring

/-- Norm on seg5: `‖fdBoundaryH H t - s‖ = 5 - t` for the endpoint. -/
private lemma endpoint_norm_seg5 (H : ℝ) (s : ℂ) (hs_def : s = (1 / 2 : ℂ) + ↑H * I)
    (t : ℝ) (ht4 : 4 < t) (ht5 : t ≤ 5) :
    ‖fdBoundaryH H t - s‖ = 5 - t := by
  rw [endpoint_diff_seg5 H s hs_def t ht4, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  ring

/-- Integrand on seg1: `(γ t - s)⁻¹ * γ'(t) = t⁻¹` for the endpoint. -/
private lemma endpoint_integrand_seg1 (H : ℝ) (s : ℂ) (hs_def : s = (1 / 2 : ℂ) + ↑H * I)
    (c : ℝ) (hc_def : c = H - Real.sqrt 3 / 2) (hc : 0 < c)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t = (↑t : ℂ)⁻¹ := by
  rw [endpoint_diff_seg1 H s hs_def c hc_def t ht0.le ht1.le]
  erw [(fdBoundary_H_hasDerivAt_seg1 H ht1).deriv]
  have key : ∀ (a b : ℂ), a ≠ 0 → b ≠ 0 → (a * b)⁻¹ * b = a⁻¹ := fun a b _ hb => by
    rw [mul_inv_rev, mul_assoc, mul_comm a⁻¹ b,
      ← mul_assoc, inv_mul_cancel₀ hb, one_mul]
  have hc_eq : (↑H - ↑(Real.sqrt 3) / 2 : ℂ) = ↑c := by push_cast [hc_def]; ring
  have hrw1 : (-(↑H - ↑(Real.sqrt 3) / 2 : ℂ)) * I = -(↑c : ℂ) * I := by rw [hc_eq]
  have hrw2 : (↑(-t * c) : ℂ) * I = ↑t * (-(↑c : ℂ) * I) := by push_cast; ring
  rw [hrw1, hrw2]
  exact key ↑t _ (Complex.ofReal_ne_zero.mpr ht0.ne') (mul_ne_zero (neg_ne_zero.mpr
      (Complex.ofReal_ne_zero.mpr hc.ne')) I_ne_zero)

/-- Integrand on seg5: `(γ t - s)⁻¹ * γ'(t) = (t - 5)⁻¹` for the endpoint. -/
private lemma endpoint_integrand_seg5 (H : ℝ) (s : ℂ) (hs_def : s = (1 / 2 : ℂ) + ↑H * I)
    (t : ℝ) (ht4 : 4 < t) :
    (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t = (↑(t - 5) : ℂ)⁻¹ := by
  rw [endpoint_diff_seg5 H s hs_def t ht4]
  erw [(fdBoundary_H_hasDerivAt_seg5 H ht4).deriv]; rw [mul_one]

lemma cpv_at_endpoint (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z => (z - ((1/2 : ℂ) + ↑H * I))⁻¹)
      (fdBoundaryH H) 0 5 ((1/2 : ℂ) + ↑H * I) := by
  set s := (1/2 : ℂ) + ↑H * I with hs_def
  set c := H - Real.sqrt 3 / 2 with hc_def
  have hc : 0 < c := sub_pos.mpr hH
  have hc_ne : c ≠ 0 := hc.ne'
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := endpoint_min_dist H hH
  set ε₀ := min c (min 1 δ) with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min hc (lt_min one_pos hδ_pos)
  set F := fun ε => ∫ t in (0 : ℝ)..5,
    if ε < ‖fdBoundaryH H t - s‖ then (fdBoundaryH H t - s)⁻¹ *
      deriv (fdBoundaryH H) t else 0
  set C := ∫ t in (1 : ℝ)..4, (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t
  suffices h_ev : ∀ ε, 0 < ε → ε < ε₀ → F ε = F (ε₀ / 2) from
    ⟨F (ε₀ / 2), tendsto_const_nhds.congr'
      (Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioo 0 ε₀, Ioo_mem_nhdsGT hε₀,
        fun ε ⟨hε_pos, hε_lt⟩ => (h_ev ε hε_pos hε_lt).symm⟩)⟩
  intro ε hε hε_lt
  have hε_c : ε < c := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_1 : ε < 1 := by have := min_le_right c (min 1 δ); have := min_le_left 1 δ; linarith
  have hε_δ : ε < δ := by have := min_le_right c (min 1 δ); have := min_le_right 1 δ; linarith
  have hε₀2_pos : 0 < ε₀ / 2 := by positivity
  have hε₀2_c : ε₀ / 2 < c := by have := min_le_left c (min 1 δ); linarith
  have hε₀2_1 : ε₀ / 2 < 1 := by
    have := min_le_right c (min 1 δ); have := min_le_left 1 δ; linarith
  have hε₀2_δ : ε₀ / 2 < δ := by
    have := min_le_right c (min 1 δ); have := min_le_right 1 δ; linarith
  suffices h_formula : ∀ η, 0 < η → η < c → η < 1 → η < δ →
      F η = ↑(Real.log c) + C by
    rw [h_formula ε hε hε_c hε_1 hε_δ,
      h_formula (ε₀/2) hε₀2_pos hε₀2_c hε₀2_1 hε₀2_δ]
  intro η hη hη_c hη_1 hη_δ
  have hη_div_c_pos : 0 < η / c := div_pos hη hc
  have hη_div_c_lt_1 : η / c < 1 := (div_lt_one hc).mpr hη_c
  have h_norm_seg1 : ∀ t, 0 ≤ t → t ≤ 1 → ‖fdBoundaryH H t - s‖ = t * c :=
    fun t ht0 ht1 => endpoint_norm_seg1 H s hs_def c hc_def hc t ht0 ht1
  have h_norm_seg5 : ∀ t, 4 < t → t ≤ 5 → ‖fdBoundaryH H t - s‖ = 5 - t :=
    fun t ht4 ht5 => endpoint_norm_seg5 H s hs_def t ht4 ht5
  have h_integrand_seg1 : ∀ t, 0 < t → t < 1 →
      (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t = (↑t : ℂ)⁻¹ :=
    fun t ht0 ht1 => endpoint_integrand_seg1 H s hs_def c hc_def hc t ht0 ht1
  have h_integrand_seg5 : ∀ t, 4 < t →
      (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t = (↑(t - 5) : ℂ)⁻¹ :=
    fun t ht4 => endpoint_integrand_seg5 H s hs_def t ht4
  have hii := fdBoundary_H_cutout_ii H hH s η hη
  have h_01_15 : (∫ t in (0 : ℝ)..5, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) =
    (∫ t in (0 : ℝ)..1, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) +
    (∫ t in (1 : ℝ)..5, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) :=
    (intervalIntegral.integral_add_adjacent_intervals (hii.mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc_right (by norm_num)))
      (hii.mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 5),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc_left (by norm_num)))).symm
  have h_14_45 : (∫ t in (1 : ℝ)..5, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) =
    (∫ t in (1 : ℝ)..4, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) +
    (∫ t in (4 : ℝ)..5, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) :=
    (intervalIntegral.integral_add_adjacent_intervals (hii.mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 4),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc (by norm_num) (by norm_num)))
      (hii.mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (4 : ℝ) ≤ 5),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc_left (by norm_num)))).symm
  have h_split : F η = (∫ t in (0 : ℝ)..1, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) +
    (∫ t in (1 : ℝ)..4, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) +
    (∫ t in (4 : ℝ)..5, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) := by
    change (∫ t in (0 : ℝ)..5, _) = _
    rw [h_01_15, h_14_45, add_assoc]
  have h_I14 : (∫ t in (1 : ℝ)..4, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) = C := by
    apply intervalIntegral.integral_congr
    intro t ht; rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 4)] at ht
    dsimp only; rw [if_pos (lt_of_lt_of_le hη_δ (hδ_bound t ht))]
  have h_I01 : (∫ t in (0 : ℝ)..1, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) =
    ∫ t in (η / c)..1, (↑t : ℂ)⁻¹ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii.mono_set (by
        rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ η / c),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc_right (by linarith)))
      (hii.mono_set (by
        rw [Set.uIcc_of_le (by linarith : η / c ≤ 1),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc (by linarith) (by norm_num)))]
    have h_zero : (∫ t in (0 : ℝ)..(η / c),
        if η < ‖fdBoundaryH H t - s‖
        then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) = 0 := by
      have : (∫ t in (0 : ℝ)..(η / c), if η < ‖fdBoundaryH H t - s‖
          then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) =
          ∫ _ in (0 : ℝ)..(η / c), (0 : ℂ) :=
        intervalIntegral.integral_congr (fun t ht => by
          rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ η / c)] at ht
          rw [if_neg]; push Not
          rw [h_norm_seg1 t ht.1 (by linarith [ht.2])]
          calc t * c ≤ (η / c) * c := mul_le_mul_of_nonneg_right ht.2 hc.le
            _ = η := by field_simp)
      rw [this, intervalIntegral.integral_zero]
    rw [h_zero, zero_add]
    refine intervalIntegral.integral_congr_ae' ?_ (by
      filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
    filter_upwards [compl_mem_ae_iff.mpr (show volume {η / c} = 0 by
                      simp only [Real.volume_singleton]),
                    compl_mem_ae_iff.mpr (show volume {(1 : ℝ)} = 0 by
                      simp only [Real.volume_singleton])]
      with t ht_ne_low ht_ne_high
    intro ht
    have ht_low : η / c < t := ht.1
    have ht_high : t < 1 := lt_of_le_of_ne ht.2 (fun h => ht_ne_high (Set.mem_singleton_iff.mpr h))
    have ht_pos : 0 < t := lt_of_lt_of_le hη_div_c_pos ht_low.le
    rw [if_pos, h_integrand_seg1 t ht_pos ht_high]
    rw [h_norm_seg1 t ht_pos.le ht_high.le]
    calc η = (η / c) * c := by field_simp
      _ < t * c := mul_lt_mul_of_pos_right ht_low hc
  have h_I45 : (∫ t in (4 : ℝ)..5, if η < ‖fdBoundaryH H t - s‖
      then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) =
    ∫ t in (4 : ℝ)..(5 - η), (↑(t - 5) : ℂ)⁻¹ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii.mono_set (by
        rw [Set.uIcc_of_le (by linarith : (4 : ℝ) ≤ 5 - η),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc (by norm_num) (by linarith)))
      (hii.mono_set (by
        rw [Set.uIcc_of_le (by linarith : 5 - η ≤ 5),
          Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
        exact Set.Icc_subset_Icc_left (by linarith)))]
    have h_zero : (∫ t in (5 - η)..5,
        if η < ‖fdBoundaryH H t - s‖
        then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) = 0 := by
      have : (∫ t in (5 - η)..5, if η < ‖fdBoundaryH H t - s‖
          then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) =
          ∫ _ in (5 - η)..5, (0 : ℂ) :=
        intervalIntegral.integral_congr (fun t ht => by
          rw [Set.uIcc_of_le (by linarith : 5 - η ≤ 5)] at ht
          rw [if_neg]; push Not
          by_cases ht5 : t = 5
          · rw [ht5, fdBoundary_H_at_five, hs_def, sub_self, norm_zero]; exact hη.le
          · have ht5' : t < 5 := lt_of_le_of_ne ht.2 ht5
            by_cases ht4 : t ≤ 4
            · linarith [ht.1]
            · push Not at ht4
              rw [h_norm_seg5 t ht4 ht.2]; linarith [ht.1])
      rw [this, intervalIntegral.integral_zero]
    rw [h_zero, add_zero]
    refine intervalIntegral.integral_congr_ae' ?_ (by
      filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
    filter_upwards [compl_mem_ae_iff.mpr (show volume {5 - η} = 0 by
                      simp only [Real.volume_singleton])]
      with t ht_ne_high
    intro ht
    have ht4 : 4 < t := ht.1
    have ht_strict : t < 5 - η := lt_of_le_of_ne ht.2
      (fun h => ht_ne_high (Set.mem_singleton_iff.mpr h))
    rw [if_pos, h_integrand_seg5 t ht4]
    rw [h_norm_seg5 t ht4 (by linarith)]; linarith
  have h_int1 : ∫ t in (η / c)..1, (↑t : ℂ)⁻¹ =
      Complex.log ↑(1 : ℝ) - Complex.log ↑(η / c) :=
    integral_inv_eq_log_sub (η / c) hη_div_c_pos hη_div_c_lt_1.le
  have h_int2 : ∫ t in (4 : ℝ)..(5 - η), (↑(t - 5) : ℂ)⁻¹ = ↑(Real.log η) :=
    integral_shifted_inv_eq_log η hη hη_1
  rw [h_split, h_I14, h_I01, h_I45, h_int1, h_int2]
  rw [Complex.ofReal_one, Complex.log_one, ← Complex.ofReal_log hη_div_c_pos.le,
    Real.log_div hη.ne' hc_ne, Complex.ofReal_sub]
  ring

/-- The corner `s = -1/2 + H*I` avoids the boundary on `[0, 3]`. -/
private lemma corner_cpv_03 (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z => (z - (-(1/2 : ℂ) + ↑H * I))⁻¹)
      (fdBoundaryH H) 0 3 (-(1/2 : ℂ) + ↑H * I) := by
  set s := -(1/2 : ℂ) + ↑H * I with hs_def
  apply cpv_avoidance _ _ _ _ _ ((fdBoundary_H_continuous H).continuousOn.mono
    (Set.Icc_subset_Icc_right (by norm_num : (3 : ℝ) ≤ 5))) (by norm_num)
  intro t ht habs
  rw [Set.mem_Icc] at ht
  by_cases ht1 : t ≤ 1
  · have hre := fdBoundary_H_seg1_re' H ht.1 ht1
    rw [habs, hs_def] at hre
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.one_re, Complex.div_ofNat] at hre
    linarith
  · push Not at ht1
    by_cases ht3 : t < 3
    · have h_norm : ‖fdBoundaryH H t‖ = 1 := by
        rw [fdBoundary_H_eq_arc (H := H) ht1 ht3, Complex.norm_exp_ofReal_mul_I]
      rw [habs] at h_norm
      have : 1 < ‖s‖ := by
        have h_nsq : 1 < Complex.normSq s := by
          simp only [hs_def, Complex.normSq_apply, Complex.add_re, Complex.neg_re,
            Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
            Complex.add_im, Complex.neg_im, Complex.mul_im, Complex.one_re, Complex.one_im,
            Complex.div_ofNat]
          have hH0 : 0 < H := by
            linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 from by norm_num)]
          nlinarith [mul_lt_mul hH hH.le (by positivity : (0 : ℝ) < Real.sqrt 3 / 2) hH0.le,
                     Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 from by norm_num)]
        calc (1 : ℝ) = Real.sqrt 1 := by simp only [Real.sqrt_one]
          _ < Real.sqrt (Complex.normSq s) := Real.sqrt_lt_sqrt (by norm_num) h_nsq
          _ = ‖s‖ := rfl
      linarith
    · have ht3_eq : t = 3 := le_antisymm ht.2 (by linarith)
      subst ht3_eq
      have hγ3_eq : fdBoundaryH H 3 = fdBoundary 3 := by
        rw [fdBoundary_H_at_three]
        exact fdBoundary_at_three.symm
      rw [hγ3_eq, fdBoundary_at_three] at habs
      have him_s : s.im = H := by
        simp [hs_def, Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re]
      rw [← habs] at him_s
      have him_rho : (ellipticPointRho : ℂ).im = Real.sqrt 3 / 2 := by
        simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
          Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat]
      linarith [him_rho]

private lemma integral_inv_shift_four (a b : ℝ) :
    (∫ t in a..b, (↑(t - 4) : ℂ)⁻¹) = ∫ u in (a - 4)..(b - 4), (↑u : ℂ)⁻¹ := by
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  congr 1
  exact intervalIntegral.integral_comp_sub_right (fun u : ℝ => u⁻¹) (4 : ℝ)

private lemma integral_inv_neg_axis (r : ℝ) :
    (∫ u in (-1 : ℝ)..(-r), (↑u : ℂ)⁻¹) = -(∫ u in r..1, (↑u : ℂ)⁻¹) := by
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    ← Complex.ofReal_neg, Complex.ofReal_inj]
  have key : (∫ x in r..(1 : ℝ), (-x)⁻¹) = ∫ x in (-1 : ℝ)..-r, x⁻¹ :=
    intervalIntegral.integral_comp_neg (fun u : ℝ => u⁻¹) (a := r) (b := 1)
  rw [show (∫ x in r..(1 : ℝ), (-x)⁻¹) = ∫ x in r..(1 : ℝ), -(x⁻¹) from by
      apply intervalIntegral.integral_congr; intro x _; exact neg_inv.symm] at key
  rw [intervalIntegral.integral_neg] at key
  linarith

lemma cpv_at_corner (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z => (z - (-(1/2 : ℂ) + ↑H * I))⁻¹)
      (fdBoundaryH H) 0 5 (-(1/2 : ℂ) + ↑H * I) := by
  set s := -(1/2 : ℂ) + ↑H * I with hs_def
  set c := H - Real.sqrt 3 / 2 with hc_def
  have hc : 0 < c := sub_pos.mpr hH
  have h_cpv_03 : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) 0 3 s := corner_cpv_03 H hH
  have h_cpv_35 : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) 3 5 s := by
    set ε₀ := min c 1 with hε₀_def
    have hε₀ : 0 < ε₀ := lt_min hc one_pos
    set F := fun ε => ∫ t in (3 : ℝ)..5,
      if ε < ‖fdBoundaryH H t - s‖ then (fdBoundaryH H t - s)⁻¹ *
        deriv (fdBoundaryH H) t else 0
    suffices h_ev : ∀ ε, 0 < ε → ε < ε₀ → F ε = F (ε₀ / 2) from
      ⟨F (ε₀ / 2), tendsto_const_nhds.congr'
        (Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioo 0 ε₀, Ioo_mem_nhdsGT hε₀,
          fun ε ⟨hε_pos, hε_lt⟩ => (h_ev ε hε_pos hε_lt).symm⟩)⟩
    intro ε hε hε_lt
    have hε_c : ε < c := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_1 : ε < 1 := lt_of_lt_of_le hε_lt (min_le_right _ _)
    have hε₀2_pos : 0 < ε₀ / 2 := by positivity
    have hε₀2_c : ε₀ / 2 < c := by
      calc ε₀ / 2 < ε₀ := by linarith
        _ ≤ c := min_le_left _ _
    have hε₀2_1 : ε₀ / 2 < 1 := by
      calc ε₀ / 2 < ε₀ := by linarith
        _ ≤ 1 := min_le_right _ _
    suffices h_formula : ∀ η, 0 < η → η < c → η < 1 →
        F η = -↑(Real.log c) by
      rw [h_formula ε hε hε_c hε_1, h_formula (ε₀/2) hε₀2_pos hε₀2_c hε₀2_1]
    intro η hη hη_c hη_1
    have hη_div_c_pos : 0 < η / c := div_pos hη hc
    have hη_div_c_lt_1 : η / c < 1 := (div_lt_one hc).mpr hη_c
    have hc_ne : c ≠ 0 := hc.ne'
    have h_diff_seg4 : ∀ t, 3 < t → t ≤ 4 →
        fdBoundaryH H t - s = ↑((t - 4) * c) * I := by
      intro t ht3 ht4
      rw [fdBoundary_H_eq_seg4_H ht3 ht4, hs_def]
      simp only [fdBoundarySeg4H, hc_def]
      push_cast; ring
    have h_diff_seg5 : ∀ t, 4 < t →
        fdBoundaryH H t - s = ↑(t - 4) := by
      intro t ht4
      rw [fdBoundary_H_eq_seg5_H ht4, hs_def]
      simp only [fdBoundarySeg5H]
      push_cast; ring
    have h_norm_seg4 : ∀ t, 3 < t → t ≤ 4 →
        ‖fdBoundaryH H t - s‖ = (4 - t) * c := by
      intro t ht3 ht4
      rw [h_diff_seg4 t ht3 ht4, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_nonpos (by nlinarith : (t - 4) * c ≤ 0)]
      ring
    have h_norm_seg5 : ∀ t, 4 < t →
        ‖fdBoundaryH H t - s‖ = t - 4 := by
      intro t ht4
      rw [h_diff_seg5 t ht4, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    have h_integrand_seg4 : ∀ t, 3 < t → t < 4 →
        (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t = (↑(t - 4) : ℂ)⁻¹ := by
      intro t ht3 ht4
      rw [h_diff_seg4 t ht3 ht4.le]; erw [(fdBoundary_H_hasDerivAt_seg4 H ht3 ht4).deriv]
      have key : ∀ (a b : ℂ), a ≠ 0 → b ≠ 0 → (a * b)⁻¹ * b = a⁻¹ := fun a b _ hb => by
        rw [mul_inv_rev, mul_assoc, mul_comm a⁻¹ b,
          ← mul_assoc, inv_mul_cancel₀ hb, one_mul]
      have hc_eq : (↑H - ↑(Real.sqrt 3) / 2 : ℂ) = ↑c := by
        push_cast [hc_def]; ring
      have hrw1 : (↑H - ↑(Real.sqrt 3) / 2 : ℂ) * I = (↑c : ℂ) * I := by rw [hc_eq]
      have hrw2 : (↑((t - 4) * c) : ℂ) * I = ↑(t - 4) * (↑c * I) := by push_cast; ring
      rw [hrw1, hrw2]
      exact key ↑(t - 4) _ (Complex.ofReal_ne_zero.mpr (by linarith : (t - 4 : ℝ) ≠ 0))
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') I_ne_zero)
    have h_integrand_seg5 : ∀ t, 4 < t →
        (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t = (↑(t - 4) : ℂ)⁻¹ := by
      intro t ht4
      rw [h_diff_seg5 t ht4]; erw [(fdBoundary_H_hasDerivAt_seg5 H ht4).deriv]; rw [mul_one]
    have h_split : F η = (∫ t in (3 : ℝ)..4, if η < ‖fdBoundaryH H t - s‖
        then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) +
      (∫ t in (4 : ℝ)..5, if η < ‖fdBoundaryH H t - s‖
        then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) := by
      change (∫ t in (3 : ℝ)..5, _) = _
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4),
                   Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by norm_num) (by norm_num)))
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le (by norm_num : (4 : ℝ) ≤ 5),
                   Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by norm_num) (by norm_num)))]
    have h_I34 : (∫ t in (3 : ℝ)..4, if η < ‖fdBoundaryH H t - s‖
        then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) =
      ∫ t in (3 : ℝ)..(4 - η / c), (↑(t - 4) : ℂ)⁻¹ := by
      have h_4mc : 3 < 4 - η / c := by linarith [hη_div_c_lt_1]
      have h_4mc_le : 4 - η / c ≤ 4 := by linarith [hη_div_c_pos]
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le (by linarith : (3 : ℝ) ≤ 4 - η / c),
                   Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by norm_num) (by linarith)))
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le (by linarith : 4 - η / c ≤ 4),
                   Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by linarith) (by norm_num)))]
      have h_zero : (∫ t in (4 - η / c)..4,
          if η < ‖fdBoundaryH H t - s‖
          then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) = 0 := by
        have : (∫ t in (4 - η / c)..4,
            if η < ‖fdBoundaryH H t - s‖
            then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) =
            ∫ _ in (4 - η / c)..4, (0 : ℂ) :=
          intervalIntegral.integral_congr (fun t ht => by
            rw [Set.uIcc_of_le h_4mc_le] at ht
            rw [if_neg]; push Not
            rw [h_norm_seg4 t (by linarith [ht.1]) ht.2]
            have h1 : 4 - t ≤ η / c := by linarith [ht.1]
            calc (4 - t) * c ≤ (η / c) * c := by
                  apply mul_le_mul_of_nonneg_right h1 hc.le
              _ = η := by field_simp)
        rw [this, intervalIntegral.integral_zero]
      rw [h_zero, add_zero]
      have h_le : (3 : ℝ) ≤ 4 - η / c := by linarith [hη_div_c_lt_1]
      refine intervalIntegral.integral_congr_ae' ?_ (by
        filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
      filter_upwards [compl_mem_ae_iff.mpr (show volume {4 - η / c} = 0 by
                        simp only [Real.volume_singleton])]
        with t ht_ne
      intro ht
      have ht3 : 3 < t := ht.1
      have ht4_le : t ≤ 4 - η / c := ht.2
      have ht_ne' : t ≠ 4 - η / c := fun h => ht_ne (Set.mem_singleton_iff.mpr h)
      have ht4_strict : t < 4 - η / c := lt_of_le_of_ne ht4_le ht_ne'
      have ht4 : t < 4 := by linarith [hη_div_c_pos]
      rw [if_pos, h_integrand_seg4 t ht3 ht4]
      rw [h_norm_seg4 t ht3 ht4.le]
      have : η / c < 4 - t := by linarith
      calc η = (η / c) * c := by field_simp
        _ < (4 - t) * c := mul_lt_mul_of_pos_right this hc
    have h_I45 : (∫ t in (4 : ℝ)..5, if η < ‖fdBoundaryH H t - s‖
        then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) =
      ∫ t in (4 + η)..5, (↑(t - 4) : ℂ)⁻¹ := by
      have h_4ph : 4 + η ≤ 5 := by linarith
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le (by linarith : (4 : ℝ) ≤ 4 + η),
                   Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by norm_num) (by linarith)))
        (IntervalIntegrable.mono_set (fdBoundary_H_cutout_ii H hH s η hη)
          (by rw [Set.uIcc_of_le h_4ph,
                   Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
              exact Set.Icc_subset_Icc (by linarith) (by norm_num)))]
      have h_zero : (∫ t in (4 : ℝ)..(4 + η),
          if η < ‖fdBoundaryH H t - s‖
          then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) = 0 := by
        have : (∫ t in (4 : ℝ)..(4 + η),
            if η < ‖fdBoundaryH H t - s‖
            then (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0) =
            ∫ _ in (4 : ℝ)..(4 + η), (0 : ℂ) :=
          intervalIntegral.integral_congr (fun t ht => by
            rw [Set.uIcc_of_le (by linarith : (4 : ℝ) ≤ 4 + η)] at ht
            rw [if_neg]; push Not
            by_cases ht4 : t = 4
            · subst ht4
              rw [fdBoundary_H_at_four H, hs_def]
              norm_num
              linarith
            · have ht4' : 4 < t := lt_of_le_of_ne ht.1 (Ne.symm ht4)
              rw [h_norm_seg5 t ht4']; linarith [ht.2])
        rw [this, intervalIntegral.integral_zero]
      rw [h_zero, zero_add]
      refine intervalIntegral.integral_congr_ae' ?_ (by
        filter_upwards with t ht; exfalso; linarith [ht.1, ht.2])
      filter_upwards with t ht
      have ht4 : 4 < t := by linarith [ht.1]
      rw [if_pos, h_integrand_seg5 t ht4]
      rw [h_norm_seg5 t ht4]; linarith [ht.1]
    have h_sub34 : (∫ t in (3 : ℝ)..(4 - η / c), (↑(t - 4) : ℂ)⁻¹) =
        ∫ u in (-1 : ℝ)..(-η / c), (↑u : ℂ)⁻¹ := by
      rw [integral_inv_shift_four, show (3 : ℝ) - 4 = -1 from by ring,
        show (4 - η / c) - 4 = -η / c from by ring]
    have h_sub45 : (∫ t in (4 + η)..5, (↑(t - 4) : ℂ)⁻¹) =
        ∫ u in η..1, (↑u : ℂ)⁻¹ := by
      rw [integral_inv_shift_four, show (4 + η) - 4 = η from by ring,
        show (5 : ℝ) - 4 = 1 from by ring]
    have h_neg_axis : (∫ u in (-1 : ℝ)..(-η / c), (↑u : ℂ)⁻¹) =
        -(∫ u in (η / c)..1, (↑u : ℂ)⁻¹) := by
      rw [show (-η / c : ℝ) = -(η / c) from by ring]; exact integral_inv_neg_axis (η / c)
    have h_pos_int1 : ∫ u in (η / c)..1, (↑u : ℂ)⁻¹ =
        Complex.log ↑(1 : ℝ) - Complex.log ↑(η / c) :=
      integral_inv_eq_log_sub (η / c) hη_div_c_pos hη_div_c_lt_1.le
    have h_pos_int2 : ∫ u in η..1, (↑u : ℂ)⁻¹ =
        Complex.log ↑(1 : ℝ) - Complex.log ↑η :=
      integral_inv_eq_log_sub η hη hη_1.le
    rw [h_split, h_I34, h_I45, h_sub34, h_sub45, h_neg_axis, h_pos_int1, h_pos_int2,
      Complex.ofReal_one, Complex.log_one,
      ← Complex.ofReal_log hη.le, ← Complex.ofReal_log hη_div_c_pos.le,
      Real.log_div hη.ne' hc_ne, Complex.ofReal_sub]
    ring
  exact cpv_concat _ _ 0 3 5 s h_cpv_03 h_cpv_35 (by norm_num) (by norm_num)
    (fun ε hε => fdBoundary_H_cutout_ii H hH s ε hε)

end
