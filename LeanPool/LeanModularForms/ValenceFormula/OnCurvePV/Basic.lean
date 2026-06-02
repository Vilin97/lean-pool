/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Boundary.Smooth
import LeanPool.LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.UniformStepBound
import LeanPool.LeanModularForms.GeneralizedResidueTheory.OnCurvePV.Basic
import LeanPool.LeanModularForms.ValenceFormula.WindingWeights.I
import LeanPool.LeanModularForms.ValenceFormula.WindingWeights.Rho
import LeanPool.LeanModularForms.ValenceFormula.WindingWeights.RhoPlusOne

/-!
# On-Curve PV: Infrastructure

Bridge lemmas, elliptic point CPV, segment geometry helpers, arc injectivity,
and CPV helper lemmas (avoidance, concatenation, sub-interval extension, integrability).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- CPV of `(z - rho)^{-1}` exists along `fdBoundaryH H` for `H > sqrt(3)/2`. -/
theorem cpv_exists_at_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z => (z - ellipticPointRho)⁻¹)
      (fdBoundaryH H) 0 5 ellipticPointRho :=
  cpv_exists_from_shifted_tendsto (fdBoundaryH H) 0 5 _ _ (pv_integral_at_rho_tendsto H hH)

/-- CPV of `(z - rho')^{-1}` exists along `fdBoundaryH H` for `H > sqrt(3)/2`. -/
theorem cpv_exists_at_rho_plus_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    CauchyPrincipalValueExists' (fun z => (z - ellipticPointRhoPlusOne)⁻¹)
      (fdBoundaryH H) 0 5 ellipticPointRhoPlusOne :=
  cpv_exists_from_shifted_tendsto (fdBoundaryH H) 0 5 _ _
    (pv_integral_at_rho_plus_one_tendsto H hH)

/-- CPV of `(z - I)^{-1}` exists along `fdBoundaryH H` for `H > 1`. -/
theorem cpv_exists_at_i (H : ℝ) (hH : 1 < H) :
    CauchyPrincipalValueExists' (fun z => (z - I)⁻¹) (fdBoundaryH H) 0 5 I :=
  cpv_exists_from_shifted_tendsto (fdBoundaryH H) 0 5 _ _ (pv_integral_at_i_tendsto H hH)

lemma fdBoundary_H_seg1_re' (H : ℝ) {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fdBoundaryH H t).re = 1/2 := by
  rw [fdBoundary_H_eq_seg1_H ht1]
  simp [fdBoundarySeg1H, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im]

lemma fdBoundary_H_seg4_re' (H : ℝ) {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    (fdBoundaryH H t).re = -1/2 := by
  rw [fdBoundary_H_eq_seg4_H ht3 ht4]
  simp [fdBoundarySeg4H, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.div_ofNat]

lemma fdBoundary_H_seg5_re' (H : ℝ) {t : ℝ} (ht4 : 4 < t) (_ht5 : t ≤ 5) :
    (fdBoundaryH H t).re = t - 9/2 := by
  rw [fdBoundary_H_eq_seg5_H ht4]
  simp [fdBoundarySeg5H, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]

lemma fdBoundary_H_seg5_im' (H : ℝ) {t : ℝ} (ht4 : 4 < t) (_ht5 : t ≤ 5) :
    (fdBoundaryH H t).im = H := by
  rw [fdBoundary_H_eq_seg5_H ht4]
  simp [fdBoundarySeg5H, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]

lemma fdBoundary_H_arc_re' (H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    (fdBoundaryH H t).re = Real.cos (Real.pi * (1 + t) / 6) := by
  rw [fdBoundary_H_eq_arc ht1 ht3, Complex.exp_ofReal_mul_I_re]

lemma fdBoundary_H_arc_im' (H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    (fdBoundaryH H t).im = Real.sin (Real.pi * (1 + t) / 6) := by
  rw [fdBoundary_H_eq_arc ht1 ht3, Complex.exp_ofReal_mul_I_im]

lemma cpv_exists_on_smooth_subinterval (H : ℝ) (_hH : Real.sqrt 3 / 2 < H)
    {t₀ : ℝ} {a' b' : ℝ} (s : ℂ) (hat₀ : t₀ ∈ Set.Ioo a' b')
    (hs : fdBoundaryH H t₀ = s) (hγ_C2 : ContDiffAt ℝ 2 (fdBoundaryH H) t₀)
    (hL_ne : deriv (fdBoundaryH H) t₀ ≠ 0)
    (hγ_cont_deriv : ContinuousOn (deriv (fdBoundaryH H)) (Set.Icc a' b'))
    (h_inj : ∀ t ∈ Set.Icc a' b', fdBoundaryH H t = fdBoundaryH H t₀ → t = t₀) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) a' b' s := by
  have hγ_meas : Measurable (fdBoundaryH H) := (fdBoundary_H_continuous H).measurable
  have hγ_cont : ContinuousOn (fdBoundaryH H) (Set.Icc a' b') :=
    (fdBoundary_H_continuous H).continuousOn
  obtain ⟨limit, h_limit⟩ := pv_limit_via_dyadic hat₀ hL_ne hγ_C2
    (show deriv (fdBoundaryH H) t₀ = deriv (fdBoundaryH H) t₀ from rfl)
    hγ_cont_deriv hγ_meas hγ_cont h_inj
  exact ⟨limit, h_limit.congr (fun ε => intervalIntegral.integral_congr
    (fun t _ => by rw [hs]))⟩

private lemma fdBoundary_H_cutout_cont_inv (s : ℂ) (H : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ContinuousOn (fun z => (z - s)⁻¹) ((fdBoundaryH H) '' Set.Icc 0 5 \ Metric.ball s ε) := by
  apply ContinuousOn.inv₀
  · exact continuousOn_id.sub continuousOn_const
  · intro z ⟨_, hz_ball⟩
    simp only [Metric.mem_ball, not_lt] at hz_ball
    exact sub_ne_zero.mpr (fun heq => by subst heq; simp [dist_self] at hz_ball; linarith)

private lemma fdBoundary_H_cutout_bound (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    (s : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 5,
      ‖(fun t => if ε < ‖fdBoundaryH H t - s‖ then (fdBoundaryH H t - s)⁻¹ *
        deriv (fdBoundaryH H) t else 0) t‖ ≤ C := by
  obtain ⟨M, hM_pos, hM_bound⟩ := fdBoundary_H_deriv_bound_ex hH
  refine ⟨ε⁻¹ * M, fun t _ht => ?_⟩
  simp only
  split_ifs with h
  · calc ‖(fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t‖
        = ‖(fdBoundaryH H t - s)⁻¹‖ * ‖deriv (fdBoundaryH H) t‖ := norm_mul _ _
      _ ≤ ε⁻¹ * M := by
        apply mul_le_mul
        · rw [norm_inv]
          exact inv_anti₀ hε (le_of_lt h)
        · by_cases htp : t ∈ fdBoundaryHPartition
          · simp only [fdBoundaryHPartition, Finset.mem_insert, Finset.mem_singleton] at htp
            have : ¬DifferentiableAt ℝ (fdBoundaryH H) t := by
              rcases htp with rfl | rfl | rfl
              · exact fdBoundary_H_not_differentiableAt_1 hH
              · exact fdBoundary_H_not_differentiableAt_3 hH
              · exact fdBoundary_H_not_differentiableAt_4 hH
            erw [deriv_zero_of_not_differentiableAt this]; simp [le_of_lt hM_pos]
          · exact hM_bound t htp
        · exact norm_nonneg _
        · exact le_of_lt (inv_pos_of_pos hε)
  · simp only [norm_zero]; exact mul_nonneg (le_of_lt (inv_pos_of_pos hε)) (le_of_lt hM_pos)

private lemma fdBoundary_H_cutout_meas (H : ℝ) (s : ℂ) (ε : ℝ) (hε : 0 < ε) :
    AEStronglyMeasurable (fun t => if ε < ‖fdBoundaryH H t - s‖ then
        (fdBoundaryH H t - s)⁻¹ * deriv (fdBoundaryH H) t else 0)
      (volume.restrict (Set.Icc 0 5)) :=
  aEStronglyMeasurable_pv_integrand_piecewiseC1
    (f := fun z => (z - s)⁻¹) (γ := fdBoundaryH H) (a := 0) (b := 5)
    (z₀ := s) (ε := ε) (P := fdBoundaryHPartition) (fdBoundary_H_cutout_cont_inv s H ε hε)
    (fdBoundary_H_continuous H).continuousOn (fdBoundary_H_deriv_continuousOn_off_partition H)

/-- The cutout integrand for `(z - s)⁻¹` along `fdBoundaryH H` is interval-integrable
on `[0, 5]`. Uses ae-measurability from piecewise C1 structure + uniform bound. -/
lemma fdBoundary_H_cutout_ii (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    (s : ℂ) (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable (fun t => if ε < ‖fdBoundaryH H t - s‖ then (fdBoundaryH H t - s)⁻¹ *
        deriv (fdBoundaryH H) t else 0)
      volume 0 5 := by
  obtain ⟨C, hC⟩ := fdBoundary_H_cutout_bound H hH s ε hε
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
  have hmeas := fdBoundary_H_cutout_meas H s ε hε
  exact IntegrableOn.mono_set
    ⟨hmeas, HasFiniteIntegral.of_bounded
      (by filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
          exact hC t ht)⟩
    Ioc_subset_Icc_self

/-- If CPV exists on a sub-interval `[a', b'] ⊆ [0, 5]` containing the sole crossing point,
and the curve avoids `s` on `[0, a']` and `[b', 5]`, then CPV exists on `[0, 5]`.
This combines `cpv_avoidance` on the complement and `cpv_concat` to glue. -/
lemma cpv_extend_to_full_interval (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    (s : ℂ) (a' b' : ℝ) (ha' : 0 ≤ a') (hb' : b' ≤ 5) (hab' : a' < b')
    (h_sub : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) a' b' s)
    (h_avoid_left : ∀ t ∈ Set.Icc 0 a', fdBoundaryH H t ≠ s)
    (h_avoid_right : ∀ t ∈ Set.Icc b' 5, fdBoundaryH H t ≠ s) :
    CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) (fdBoundaryH H) 0 5 s := by
  have hγ_cont : ContinuousOn (fdBoundaryH H) (Set.Icc 0 5) :=
    (fdBoundary_H_continuous H).continuousOn
  have h_cpv_left : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) 0 a' s :=
    cpv_avoidance _ _ _ _ _ (hγ_cont.mono (Set.Icc_subset_Icc_right
        (le_trans (le_of_lt hab') hb')))
      ha' h_avoid_left
  have h_cpv_right : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) b' 5 s :=
    cpv_avoidance _ _ _ _ _ (hγ_cont.mono (Set.Icc_subset_Icc_left (le_trans ha' (le_of_lt hab'))))
      hb' h_avoid_right
  have h_cpv_0b' : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹)
      (fdBoundaryH H) 0 b' s := by
    apply cpv_concat _ _ 0 a' b' s h_cpv_left h_sub ha' (le_of_lt hab')
    intro ε hε
    exact (fdBoundary_H_cutout_ii H hH s ε hε).mono_set (by
      rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ b'),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc_right hb')
  apply cpv_concat _ _ 0 b' 5 s h_cpv_0b' h_cpv_right (le_trans ha' (le_of_lt hab')) hb'
  intro ε hε
  exact fdBoundary_H_cutout_ii H hH s ε hε

end
