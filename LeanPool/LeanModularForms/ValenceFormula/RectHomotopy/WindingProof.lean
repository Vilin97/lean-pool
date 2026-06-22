/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.CircleParam
import LeanPool.LeanModularForms.ValenceFormula.RectHomotopy.WindingBase

/-!
# Winding number computation

Proves that the winding number of `fdPolygon` around interior points equals -1,
using FTC with lifted angle functions and S1 curve comparisons.

* `angle_lifted_ref_p₀_continuousOn` — lifted angle is continuous on [0, 5]
* `rc_integral_eq_neg_two_pi_I_ref_p₀` — S1 integral equals -2piI
* `winding_fdPolygon_at_ref_eq_neg_one` — base case at reference point
* `winding_fdPolygon_eq_neg_one` — general case for all interior points
* `winding_fdPolygon_eq_circleParamCW` — matches circleParamCW winding
-/

open Complex Set Metric Filter Topology MeasureTheory

namespace RectHomotopyProof

/-- The lifted angle function is continuous on [0, 5] for the reference point ref_p0. -/
lemma angle_lifted_ref_p₀_continuousOn :
    ContinuousOn (fun t => (fdPolygonRadialCircleAngleLifted refP₀ t : ℂ)) (Icc 0 5) := by
  set T := tL refP₀
  have htL := tL_mem_Ioo refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im
  have hfun_eq : (fun t => (fdPolygonRadialCircleAngleLifted refP₀ t : ℂ)) =
      fun t => if t < T then ↑(Complex.arg (fdPolygon t - refP₀))
        else ↑(Complex.arg (fdPolygon t - refP₀) - 2 * Real.pi) := by
    ext t; simp only [fdPolygonRadialCircleAngleLifted]; split_ifs <;> rfl
  rw [hfun_eq]
  have hval_at_T :
      ↑(Complex.arg (fdPolygon T - refP₀) - 2 * Real.pi) = (↑(-Real.pi) : ℂ) := by
    congr 1
    rw [arg_at_tL_eq_pi refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im]; ring
  apply ContinuousOn.if'
  · intro a ha
    have ha_eq : a = T := by
      have h := ha.2; change a ∈ frontier (Iio T) at h
      rw [frontier_Iio, Set.mem_singleton_iff] at h; exact h
    subst ha_eq
    rw [if_neg (lt_irrefl T), hval_at_T]
    apply Filter.Tendsto.mono_left _ (nhdsWithin_mono _ Set.inter_subset_right)
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_arg_w_left
  · intro a ha
    have ha_eq : a = T := by
      have h := ha.2; change a ∈ frontier (Iio T) at h
      rw [frontier_Iio, Set.mem_singleton_iff] at h; exact h
    subst ha_eq
    rw [if_neg (lt_irrefl T), hval_at_T]
    apply Filter.Tendsto.mono_left _ (nhdsWithin_mono _ Set.inter_subset_right)
    have hset_eq : {t : ℝ | ¬t < T} = Ici T := by ext; simp [not_lt]
    rw [hset_eq]
    have hIci_eq : Ici T = {T} ∪ Ioi T := by ext; simp [le_iff_lt_or_eq, or_comm]
    have h_arg_right : Tendsto (fun t => Complex.arg (fdPolygon t - refP₀))
        (𝓝[Ici T] T) (𝓝 Real.pi) := by
      rw [hIci_eq, nhdsWithin_union]
      exact Filter.tendsto_sup.mpr ⟨by
        rw [nhdsWithin_singleton, Filter.tendsto_pure_left]
        intro s hs
        rw [arg_at_tL_eq_pi refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im]
        exact mem_of_mem_nhds hs, tendsto_arg_w_right⟩
    have hcomp_fun : (fun t => (↑(Complex.arg (fdPolygon t - refP₀) - 2 * Real.pi) : ℂ)) =
        (fun x : ℝ => (↑(x - 2 * Real.pi) : ℂ)) ∘
        (fun t => Complex.arg (fdPolygon t - refP₀)) := by ext; rfl
    rw [hcomp_fun]
    have h_outer : Tendsto (fun x : ℝ => (↑(x - 2 * Real.pi) : ℂ))
        (𝓝 Real.pi) (𝓝 ↑(-Real.pi : ℝ)) := by
      have : ↑(-Real.pi : ℝ) = (↑(Real.pi - 2 * Real.pi) : ℂ) := by push_cast; ring
      rw [this]
      exact (Complex.continuous_ofReal.comp
        (continuous_sub_right (2 * Real.pi))).continuousAt.tendsto
    exact h_outer.comp h_arg_right
  · apply ContinuousOn.comp Complex.continuous_ofReal.continuousOn
    · exact continuousOn_arg_w.mono (fun t ⟨ht, htT⟩ =>
        ⟨ht, fun h => (ne_of_lt htT) (Set.mem_singleton_iff.mp h)⟩)
    · exact Set.mapsTo_image _ _
  · show ContinuousOn (fun t => (↑(Complex.arg (fdPolygon t - refP₀) - 2 * Real.pi) : ℂ))
        (Icc 0 5 ∩ {t | ¬t < T})
    intro t ⟨ht, ht_ge⟩
    simp only [not_lt] at ht_ge
    by_cases htT : t = T
    · subst htT
      rw [ContinuousWithinAt, hval_at_T]
      apply Filter.Tendsto.mono_left _ (nhdsWithin_mono _ (fun x hx => hx.2))
      have hset_eq : {t : ℝ | ¬t < T} = Ici T := by ext; simp [not_lt]
      rw [hset_eq]
      have hIci_eq : Ici T = {T} ∪ Ioi T := by ext; simp [le_iff_lt_or_eq, or_comm]
      have h_arg_right : Tendsto (fun t => Complex.arg (fdPolygon t - refP₀))
          (𝓝[Ici T] T) (𝓝 Real.pi) := by
        rw [hIci_eq, nhdsWithin_union]
        exact Filter.tendsto_sup.mpr ⟨by
          rw [nhdsWithin_singleton, Filter.tendsto_pure_left]
          intro s hs
          rw [arg_at_tL_eq_pi refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im]
          exact mem_of_mem_nhds hs, tendsto_arg_w_right⟩
      have hcomp_fun : (fun t => (↑(Complex.arg (fdPolygon t - refP₀) - 2 * Real.pi) : ℂ)) =
          (fun x : ℝ => (↑(x - 2 * Real.pi) : ℂ)) ∘
          (fun t => Complex.arg (fdPolygon t - refP₀)) := by ext; rfl
      rw [hcomp_fun]
      have h_outer : Tendsto (fun x : ℝ => (↑(x - 2 * Real.pi) : ℂ))
          (𝓝 Real.pi) (𝓝 ↑(-Real.pi : ℝ)) := by
        have : ↑(-Real.pi : ℝ) = (↑(Real.pi - 2 * Real.pi) : ℂ) := by push_cast; ring
        rw [this]
        exact (Complex.continuous_ofReal.comp
        (continuous_sub_right (2 * Real.pi))).continuousAt.tendsto
      exact h_outer.comp h_arg_right
    · have h_slit : fdPolygon t - refP₀ ∈ Complex.slitPlane :=
        fdPolygon_sub_ref_p₀_mem_slitPlane t ht htT
      apply ContinuousWithinAt.mono _ Set.inter_subset_left
      have h_w_cont : ContinuousAt (fun t => fdPolygon t - refP₀) t :=
        continuous_w.continuousAt
      have h_arg_cont : ContinuousAt (fun t => Complex.arg (fdPolygon t - refP₀)) t :=
        (Complex.continuousAt_arg h_slit).comp h_w_cont (f := fun t => fdPolygon t - refP₀)
      exact Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (h_arg_cont.continuousWithinAt.sub continuousWithinAt_const)

/-- The S1 integral for the radial circle around ref_p0 equals -2piI. -/
lemma rc_integral_eq_neg_two_pi_I_ref_p₀ :
    ∫ t in (0 : ℝ)..5, (fdPolygonRadialCircle refP₀ t - refP₀)⁻¹ *
    deriv (fdPolygonRadialCircle refP₀) t = -2 * ↑Real.pi * I := by
  set rc := fdPolygonRadialCircle refP₀ with hrc
  set θ_L := fdPolygonRadialCircleAngleLifted refP₀ with hθ_L
  set F : ℝ → ℂ := fun t => I * (θ_L t : ℂ) with hF
  have hF_change : F 5 - F 0 = -2 * ↑Real.pi * I := by
    change I * (θ_L 5 : ℂ) - I * (θ_L 0 : ℂ) = -2 * ↑Real.pi * I
    have h := fdPolygonRadialCircle_angle_lifted_change refP₀
      ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im
    rw [← mul_sub]
    have hsub : (θ_L 5 : ℂ) - (θ_L 0 : ℂ) = ((θ_L 5 - θ_L 0 : ℝ) : ℂ) := by push_cast; ring
    rw [hsub]
    have hval : θ_L 5 - θ_L 0 = -(2 * Real.pi) := by linarith
    rw [hval]; push_cast; ring
  have hF_cont : ContinuousOn F (Icc 0 5) := by
    change ContinuousOn (fun t => I * (θ_L t : ℂ)) (Icc 0 5)
    exact continuousOn_const.mul angle_lifted_ref_p₀_continuousOn
  have hF_deriv : ∀ x ∈ (Ioo (0 : ℝ) 5) \ ({1, 2, 3, tL refP₀, 4} : Set ℝ),
      HasDerivAt F ((rc x - refP₀)⁻¹ * deriv rc x) x := by
    intro t ⟨ht, ht_exc⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_exc
    obtain ⟨ht1, ht2, ht3, htL, ht4⟩ := ht_exc
    have ht_not_P : t ∉ ({1, 2, 3, 4} : Finset ℝ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ht1, ht2, ht3, ht4⟩
    have hrc_diff : DifferentiableAt ℝ rc t := by
      change DifferentiableAt ℝ (fun t' => polygonToCircleRadial refP₀ (t', 1)) t
      exact polygonToCircleRadial_differentiable_off_partition refP₀ ref_p₀_norm ref_p₀_re
        ref_p₀_im t ht ht_not_P 1 ⟨by norm_num, le_refl 1⟩
    have hrc_hasderiv : HasDerivAt (fun t' => rc t' - refP₀) (deriv rc t) t := by
      exact hrc_diff.hasDerivAt.sub_const refP₀
    have ht_Icc : t ∈ Icc (0 : ℝ) 5 := Ioo_subset_Icc_self ht
    have h_slit : rc t - refP₀ ∈ Complex.slitPlane :=
      rc_sub_ref_p₀_mem_slitPlane t ht_Icc htL
    have h_log_deriv : HasDerivAt (fun t' => Complex.log (rc t' - refP₀))
        ((rc t - refP₀)⁻¹ * deriv rc t) t := by
      have h_comp := @HasDerivAt.scomp ℝ _ ℂ _ _ t ℂ _ _ _ IsScalarTower.right _ _ _ _
        (Complex.hasDerivAt_log h_slit) hrc_hasderiv
      rw [Function.comp_def] at h_comp
      exact h_comp.congr_deriv (by rw [smul_eq_mul, mul_comm])
    have log_eq_I_arg : ∀ t' ∈ Icc (0 : ℝ) 5, fdPolygon t' ≠ refP₀ →
        Complex.log (rc t' - refP₀) =
        I * ↑(Complex.arg (fdPolygon t' - refP₀)) := by
      intro t' ht' hne
      have hw_ne : fdPolygon t' - refP₀ ≠ 0 := sub_ne_zero.mpr hne
      have hnorm_pos : (0 : ℝ) < ‖fdPolygon t' - refP₀‖ := norm_pos_iff.mpr hw_ne
      have hrc_sub : rc t' - refP₀ = (fdPolygon t' - refP₀) / ↑‖fdPolygon t' - refP₀‖ := by
        simp only [hrc, fdPolygonRadialCircle, polygonToCircleRadial]
        simp only [sub_self, zero_mul, zero_add, add_sub_cancel_left, div_eq_mul_inv]
        exact one_smul ℝ _
      have hnorm_one : ‖rc t' - refP₀‖ = 1 :=
        fdPolygonRadialCircle_dist refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im t' ht'
      rw [Complex.log]
      rw [hnorm_one, Real.log_one, Complex.ofReal_zero, zero_add]
      rw [hrc_sub, arg_normalize_eq _ hw_ne]
      ring
    have htL_Ioo := tL_mem_Ioo refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im_pos ref_p₀_im
    by_cases h_lt_tL : t < tL refP₀
    · have hF_eq_log : F =ᶠ[𝓝 t] (fun t' => Complex.log (rc t' - refP₀)) := by
        have h_ev_lt : ∀ᶠ t' in 𝓝 t, t' < tL refP₀ := eventually_lt_nhds h_lt_tL
        have h_ev_pos : ∀ᶠ t' in 𝓝 t, 0 < t' := eventually_gt_nhds ht.1
        have h_ev_lt5 : ∀ᶠ t' in 𝓝 t, t' < 5 := eventually_lt_nhds ht.2
        filter_upwards [h_ev_lt, h_ev_pos, h_ev_lt5] with t' ht'_lt ht'_pos ht'_lt5
        have ht'_Icc : t' ∈ Icc (0 : ℝ) 5 := ⟨le_of_lt ht'_pos, le_of_lt ht'_lt5⟩
        have hne : fdPolygon t' ≠ refP₀ :=
          fdPolygon_avoids_interior refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im t' ht'_Icc
        change I * ↑(θ_L t') = Complex.log (rc t' - refP₀)
        simp only [hθ_L, fdPolygonRadialCircleAngleLifted, ht'_lt, ↓reduceIte]
        exact (log_eq_I_arg t' ht'_Icc hne).symm
      exact h_log_deriv.congr_of_eventuallyEq hF_eq_log
    · push Not at h_lt_tL
      have h_gt_tL : tL refP₀ < t := lt_of_le_of_ne h_lt_tL (Ne.symm htL)
      have h_log_const : HasDerivAt (fun t' => Complex.log (rc t' - refP₀) +
          (-2 * ↑Real.pi * I)) ((rc t - refP₀)⁻¹ * deriv rc t) t :=
        h_log_deriv.add_const _
      have hF_eq_log_shift : F =ᶠ[𝓝 t] (fun t' => Complex.log (rc t' - refP₀) +
          (-2 * ↑Real.pi * I)) := by
        have h_ev_gt : ∀ᶠ t' in 𝓝 t, tL refP₀ < t' := eventually_gt_nhds h_gt_tL
        have h_ev_pos : ∀ᶠ t' in 𝓝 t, 0 < t' := eventually_gt_nhds ht.1
        have h_ev_lt5 : ∀ᶠ t' in 𝓝 t, t' < 5 := eventually_lt_nhds ht.2
        filter_upwards [h_ev_gt, h_ev_pos, h_ev_lt5] with t' ht'_gt ht'_pos ht'_lt5
        have ht'_Icc : t' ∈ Icc (0 : ℝ) 5 := ⟨le_of_lt ht'_pos, le_of_lt ht'_lt5⟩
        have hne : fdPolygon t' ≠ refP₀ :=
          fdPolygon_avoids_interior refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im t' ht'_Icc
        change I * ↑(θ_L t') = Complex.log (rc t' - refP₀) + (-2 * ↑Real.pi * I)
        simp only [hθ_L, fdPolygonRadialCircleAngleLifted,
          show ¬t' < tL refP₀ from
            not_lt.mpr (le_of_lt ht'_gt), ↓reduceIte]
        rw [log_eq_I_arg t' ht'_Icc hne]
        push_cast; ring
      exact h_log_const.congr_of_eventuallyEq hF_eq_log_shift
  have h_int : IntervalIntegrable (fun t => (rc t - refP₀)⁻¹ * deriv rc t) volume 0 5 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 5)]
    obtain ⟨M, hM⟩ :=
      polygonToCircleRadial_deriv_bounded refP₀
        ref_p₀_norm ref_p₀_re ref_p₀_im
    have h_bound : ∀ t ∈ Icc (0 : ℝ) 5,
        ‖(rc t - refP₀)⁻¹ * deriv rc t‖ ≤ M := by
      intro t ht
      have h1 : ‖rc t - refP₀‖ = 1 :=
        fdPolygonRadialCircle_dist refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im t ht
      rw [norm_mul, norm_inv, h1, inv_one, one_mul]
      exact hM t ht 1 (right_mem_Icc.mpr zero_le_one)
    have h_meas : AEStronglyMeasurable (fun t => (rc t - refP₀)⁻¹ * deriv rc t)
        (volume.restrict (Ioc 0 5)) := by
      have hrc_cont : Continuous rc := by
        change Continuous (fun t => polygonToCircleRadial refP₀ (t, 1))
        exact (polygonToCircleRadial_continuous refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im).comp
          (continuous_id.prodMk continuous_const)
      have h_inv_factor : AEStronglyMeasurable (fun t => (rc t - refP₀)⁻¹)
          (volume.restrict (Ioc 0 5)) :=
        (((measurable_inv.comp (hrc_cont.sub continuous_const).measurable
          ).stronglyMeasurable).aestronglyMeasurable
          ).restrict
      have h_deriv_factor : AEStronglyMeasurable (fun t => deriv rc t)
          (volume.restrict (Ioc 0 5)) :=
        (aestronglyMeasurable_deriv rc volume).restrict
      exact h_inv_factor.mul h_deriv_factor
    exact IntegrableOn.of_bound measure_Ioc_lt_top h_meas M
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact h_bound t (Ioc_subset_Icc_self ht))
  have h_countable : ({1, 2, 3, tL refP₀, 4} : Set ℝ).Countable :=
    Set.Finite.countable (Set.Finite.insert _ (Set.Finite.insert _ (Set.Finite.insert _
      (Set.Finite.insert _ (Set.finite_singleton _)))))
  rw [MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le F
    (fun t => (rc t - refP₀)⁻¹ * deriv rc t) (by norm_num : (0 : ℝ) ≤ 5)
    h_countable hF_cont hF_deriv h_int, hF_change]

/-- Winding number of fdPolygon at the reference point ref_p0 is -1. -/
lemma winding_fdPolygon_at_ref_eq_neg_one :
    generalizedWindingNumber' fdPolygon 0 5 refP₀ = -1 := by
  rw [winding_fdPolygon_eq_radialCircle refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im]
  set θ₀ := fdPolygonRadialCircleAngleLifted refP₀ 0 with hθ₀_def
  let θ_target : ℝ → ℝ := fun t => θ₀ - 2 * Real.pi * t / 5
  let γ_target : ℝ → ℂ := fun t => refP₀ + exp (I * (θ_target t : ℂ))
  have h_target_winding : generalizedWindingNumber' γ_target 0 5 refP₀ = (-1 : ℤ) := by
    have hab : (0 : ℝ) < 5 := by norm_num
    have hθ_diff : Differentiable ℝ θ_target := by
      intro t
      change DifferentiableAt ℝ (fun t => θ₀ - 2 * Real.pi * t / 5) t
      exact ((differentiableAt_const θ₀).sub
        ((differentiableAt_const (2 * Real.pi)).mul differentiableAt_id |>.div_const 5))
    have hθ_deriv_cont : Continuous (deriv θ_target) := by
      have hd : deriv θ_target = fun _ => -(2 * Real.pi / 5) := by
        ext t
        have hd : HasDerivAt θ_target (-(2 * Real.pi / 5)) t := by
          change HasDerivAt (fun t => θ₀ - 2 * Real.pi * t / 5) _ t
          have := ((hasDerivAt_const t θ₀).sub
            ((hasDerivAt_id t).const_mul (2 * Real.pi) |>.div_const 5))
          exact this.congr_deriv (by ring)
        exact hd.deriv
      rw [hd]; exact continuous_const
    have hθ_change : θ_target 5 - θ_target 0 = 2 * Real.pi * (-1 : ℤ) := by
      change (θ₀ - 2 * Real.pi * 5 / 5) - (θ₀ - 2 * Real.pi * 0 / 5) = _
      push_cast; ring
    exact winding_of_S1_curve_eq_degree refP₀ 0 5 hab (-1) θ_target hθ_diff hθ_deriv_cont hθ_change
  set rc := fdPolygonRadialCircle refP₀ with hrc_def
  have h_dist_one : ∀ t ∈ Icc (0 : ℝ) 5, ‖rc t - refP₀‖ = 1 := by
    intro t ht; exact fdPolygonRadialCircle_dist refP₀ ref_p₀_norm ref_p₀_re ref_p₀_im t ht
  have h_cutoff : ∀ ε > 0, ε < 1 →
      ∀ t ∈ Icc (0 : ℝ) 5, ‖rc t - refP₀‖ > ε := by
    intro ε _hε_pos hε_lt t ht; rw [h_dist_one t ht]; exact hε_lt
  have h_neg_one : (-1 : ℤ) = (-1 : ℂ) := by norm_cast
  rw [h_neg_one] at h_target_winding
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  simp only [sub_zero, deriv_sub_const]
  unfold generalizedWindingNumber' cauchyPrincipalValue' at h_target_winding
  simp only [sub_zero, deriv_sub_const] at h_target_winding
  have h_dist_target : ∀ t, ‖γ_target t - refP₀‖ = 1 := by
    intro t
    change ‖(refP₀ + exp (I * (θ_target t : ℂ))) - refP₀‖ = 1
    simp only [add_sub_cancel_left, mul_comm I]
    exact norm_exp_ofReal_mul_I _
  have h_target_integral : ∀ ε > 0, ε < 1 → (∫ t in (0 : ℝ)..5,
        if ‖γ_target t - refP₀‖ > ε then (γ_target t - refP₀)⁻¹ * deriv γ_target t else 0) =
      -2 * Real.pi * I := by
    intro ε _hε hε1
    have h_triv : ∀ t, ‖γ_target t - refP₀‖ > ε :=
      fun t => by rw [h_dist_target]; exact hε1
    have h_simp : (fun t => if ‖γ_target t - refP₀‖ > ε then
          (γ_target t - refP₀)⁻¹ * deriv γ_target t else 0) =
        (fun t => (γ_target t - refP₀)⁻¹ * deriv γ_target t) := by
      ext t; simp [h_triv t]
    rw [h_simp]
    have h_integrand : ∀ t, (γ_target t - refP₀)⁻¹ * deriv γ_target t =
        -(2 * ↑Real.pi * I / 5) := by
      intro t
      change (refP₀ + exp (I * ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ)) - refP₀)⁻¹ *
        deriv (fun t => refP₀ + exp (I * ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ))) t = _
      simp only [add_sub_cancel_left]
      have h_deriv : deriv (fun t =>
          refP₀ + exp (I * ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ))) t =
          exp (I * ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ)) * (I * (-(2 * Real.pi / 5) : ℝ)) := by
        have h1 : HasDerivAt (fun t : ℝ => (θ₀ - 2 * Real.pi * t / 5 : ℝ))
            (-(2 * Real.pi / 5)) t := by
          have := ((hasDerivAt_const t θ₀).sub
            ((hasDerivAt_id t).const_mul (2 * Real.pi) |>.div_const 5))
          exact this.congr_deriv (by ring)
        have h2 : HasDerivAt (fun t : ℝ => ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ))
            ((-(2 * Real.pi / 5) : ℝ) : ℂ) t := by
          have :=
            Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t h1
          simp only [Complex.ofRealCLM_apply,
            map_neg] at this
          convert this using 1
          all_goals first | rfl | simp [Complex.ofReal_div, Complex.ofReal_mul]
        have h3 : HasDerivAt (fun t : ℝ => I * ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ))
            (I * ((-(2 * Real.pi / 5) : ℝ) : ℂ)) t :=
          h2.const_mul I
        have h4 : HasDerivAt (fun t : ℝ =>
              exp (I * ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ)))
            (exp (I * ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ)) *
              (I * ((-(2 * Real.pi / 5) : ℝ) : ℂ))) t := by
          have := (hasDerivAt_exp _).comp t h3
          exact this
        have h5 : HasDerivAt (fun t : ℝ =>
              refP₀ +
                exp (I * ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ)))
            (exp (I * ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ)) *
              (I * ((-(2 * Real.pi / 5) : ℝ) : ℂ))) t := by
          have := (hasDerivAt_const t refP₀).add h4
          simp only [zero_add] at this; exact this
        exact h5.deriv
      rw [h_deriv]
      have hexp_ne : exp (I * ((θ₀ - 2 * Real.pi * t / 5 : ℝ) : ℂ)) ≠ 0 := exp_ne_zero _
      field_simp [hexp_ne]
      push_cast; ring
    rw [show (fun t => (γ_target t - refP₀)⁻¹ * deriv γ_target t) =
        fun _ => -(2 * ↑Real.pi * I / 5) from funext h_integrand]
    rw [intervalIntegral.integral_const]
    erw [Complex.real_smul]; push_cast; ring
  have h_target_limit : limUnder (𝓝[>] (0 : ℝ)) (fun ε =>
      ∫ t in (0 : ℝ)..5,
        if ‖γ_target t - refP₀‖ > ε then (γ_target t - refP₀)⁻¹ * deriv γ_target t else 0) =
      -2 * Real.pi * I := by
    apply limUnder_eventually_eq_const
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
    exact h_target_integral ε (mem_Ioo.mp hε).1 (mem_Ioo.mp hε).2
  suffices h_rc_limit_eq : limUnder (𝓝[>] (0 : ℝ)) (fun ε =>
      ∫ t in (0 : ℝ)..5,
        if ‖rc t - refP₀‖ > ε then (rc t - refP₀)⁻¹ * deriv rc t else 0) =
      -2 * ↑Real.pi * I by
    erw [h_rc_limit_eq]
    erw [h_target_limit] at h_target_winding
    exact h_target_winding
  apply limUnder_eventually_eq_const
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
  have hε_pos : ε > 0 := (mem_Ioo.mp hε).1
  have hε_lt1 : ε < 1 := (mem_Ioo.mp hε).2
  have h_if_eq : Set.EqOn
      (fun t => if ‖rc t - refP₀‖ > ε then (rc t - refP₀)⁻¹ * deriv rc t else 0)
      (fun t => (rc t - refP₀)⁻¹ * deriv rc t) (Set.uIcc 0 5) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 5 := by
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht
    exact if_pos (h_cutoff ε hε_pos hε_lt1 t ht')
  rw [intervalIntegral.integral_congr h_if_eq]
  exact rc_integral_eq_neg_two_pi_I_ref_p₀

/-- The winding number of fdPolygon around any valid interior point is -1. -/
lemma winding_fdPolygon_eq_neg_one (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im) (hp_im : p.im < HHeight) :
    generalizedWindingNumber' fdPolygon 0 5 p = -1 := by
  rw [winding_fdPolygon_center_invariant p refP₀
    hp_norm hp_re hp_im ref_p₀_norm ref_p₀_re ref_p₀_im
    (fdPolygon_avoids_line_to_ref p hp_norm hp_re hp_im_pos hp_im)]
  exact winding_fdPolygon_at_ref_eq_neg_one

/-- Winding number of fdPolygonRadialCircle around p equals -1. -/
lemma winding_radialCircle_eq_neg_one (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im) (hp_im : p.im < HHeight) :
    generalizedWindingNumber' (fdPolygonRadialCircle p) 0 5 p = -1 := by
  rw [← winding_fdPolygon_eq_radialCircle p hp_norm hp_re hp_im]
  exact winding_fdPolygon_eq_neg_one p hp_norm hp_re hp_im_pos hp_im

/-- Winding numbers of fdPolygonRadialCircle and circleParamCW are equal. -/
lemma winding_radialCircle_eq_circleParamCW (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im) (hp_im : p.im < HHeight) :
    generalizedWindingNumber' (fdPolygonRadialCircle p) 0 5 p =
    generalizedWindingNumber' (circleParamCW p 1 0 5) 0 5 p := by
  rw [winding_radialCircle_eq_neg_one p hp_norm hp_re hp_im_pos hp_im,
      circleParamCW_winding_eq_neg_one p 1 (by norm_num : (0 : ℝ) < 1) 0 5
        (by norm_num : (0 : ℝ) < 5)]

/-- Winding number of fdPolygon equals winding number of circleParamCW. -/
lemma winding_fdPolygon_eq_circleParamCW (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im) (hp_im : p.im < HHeight) :
    generalizedWindingNumber' fdPolygon 0 5 p =
    generalizedWindingNumber' (circleParamCW p 1 0 5) 0 5 p := by
  rw [winding_fdPolygon_eq_radialCircle p hp_norm hp_re hp_im,
      winding_radialCircle_eq_circleParamCW p hp_norm hp_re hp_im_pos hp_im]

end RectHomotopyProof
