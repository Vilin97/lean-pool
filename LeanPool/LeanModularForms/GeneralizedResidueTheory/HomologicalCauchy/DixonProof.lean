/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Dixon's Proof of the Homological Cauchy Theorem

The Dixon kernel `g(z, w) = (f(z) - f(w))/(z - w)` (extended to `f'(w)` at `z = w`)
is exactly mathlib's `dslope f z w`. We use this identification throughout.

## Main definitions

* `dixonKernel` -- the Dixon kernel (= dslope)
* `dixonH1` -- the Dixon integral h₁(w)
* `dixonH2` -- the Cauchy-type integral h₂(w)
* `dixonFunction` -- the piecewise Dixon function

## Main results

* `dixonH1_eq` -- key identity: h₁(w) = h₂(w) - 2πi · n(γ,w) · f(w)
* `dixonH1_differentiableOn` -- h₁ is differentiable on U
* `dixonH2_differentiableAt` -- h₂ is differentiable off the curve
* `dixonFunction_differentiable` -- the Dixon function is entire
* `dixonFunction_eq_zero` -- h ≡ 0 by Liouville's theorem
* `cauchyIntegralFormula_nullHomologous` -- Cauchy integral formula
* `contourIntegral_eq_zero_of_nullHomologous` -- vanishing for holomorphic functions
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral

noncomputable section

section DixonProof

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- A parameter in `Icc γ.a γ.b` off the partition lies in the open interval
`Ioo γ.a γ.b`, since the endpoints belong to the partition. -/
private lemma mem_Ioo_of_notMem_partition (γ : PiecewiseC1Immersion) {t : ℝ}
    (ht_Icc : t ∈ Icc γ.a γ.b) (ht_npart : t ∉ (↑γ.partition : Set ℝ)) :
    t ∈ Ioo γ.a γ.b :=
  ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm fun h => ht_npart (h ▸ γ.endpoints_in_partition.1)),
   lt_of_le_of_ne ht_Icc.2 fun h => ht_npart (h ▸ γ.endpoints_in_partition.2)⟩

/-- The Dixon kernel is exactly `dslope`: `dixonKernel f z w = dslope f z w`.
We use `dslope` directly rather than a custom definition. -/
abbrev dixonKernel (f : ℂ → ℂ) (z w : ℂ) : ℂ := dslope f z w

/-- h₁(w) = ∮_γ dslope(f, γ(t), w) · γ'(t) dt — the Dixon integral.
Holomorphic on all of U including image(γ). -/
noncomputable def dixonH1 (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  ∫ t in γ.a..γ.b, dslope f (γ.toFun t) w * deriv γ.toFun t

/-- h₂(w) = ∮_γ f(z)/(z-w) · γ'(t) dt — the Cauchy-type integral.
Holomorphic on ℂ \ image(γ). -/
noncomputable def dixonH2 (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t

private lemma dixonH1_dslope_expansion (γ : PiecewiseC1Immersion) (w : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    ∀ t ∈ Set.uIcc γ.a γ.b,
      dslope f (γ.toFun t) w * deriv γ.toFun t =
        f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t -
          f w / (γ.toFun t - w) * deriv γ.toFun t := by
  intro t ht_ui
  have ht : t ∈ Icc γ.a γ.b := Set.uIcc_of_le (le_of_lt γ.hab) ▸ ht_ui
  have hne : γ.toFun t ≠ w := hoff t ht
  rw [dslope_of_ne _ (Ne.symm hne), slope_def_field,
    show w - γ.toFun t = -(γ.toFun t - w) from by ring]
  field_simp [sub_ne_zero.mpr hne]
  ring

private lemma dixonH1_cauchyIntegrand_integrable (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (w : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    IntervalIntegrable
      (fun t => f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t) volume γ.a γ.b := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have h_inv_cont : ContinuousOn (fun t => (γ.toFun t - w)⁻¹) (Icc γ.a γ.b) :=
    ContinuousOn.inv₀ (γ.continuous_toFun.sub continuousOn_const)
      (fun t ht => sub_ne_zero.mpr (hoff t ht))
  obtain ⟨M_inv, hM_inv⟩ := isCompact_Icc.exists_bound_of_continuousOn h_inv_cont.norm
  simp only [norm_norm] at hM_inv
  have hf_contOn_U : ContinuousOn f U := fun z hz =>
    ((hf z hz).differentiableAt (hU.mem_nhds hz)).continuousAt.continuousWithinAt
  have hf_cont_on : ContinuousOn (f ∘ γ.toFun) (Icc γ.a γ.b) :=
    hf_contOn_U.comp γ.continuous_toFun fun t ht => hγ_in_U t ht
  obtain ⟨M_f, hM_f⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont_on.norm
  simp only [Function.comp_def, norm_norm] at hM_f
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  apply intervalIntegrable_of_piecewise_continuousOn_bounded
    (P := γ.partition) (M_f * M_inv * M_d) hab
  · intro t ⟨ht_Icc, ht_npart⟩
    have ht_Ioo : t ∈ Ioo γ.a γ.b := mem_Ioo_of_notMem_partition γ ht_Icc ht_npart
    apply ContinuousWithinAt.mul
    · apply ContinuousWithinAt.div
      · exact (hf_cont_on t ht_Icc).mono sdiff_subset
      · exact ((γ.continuous_toFun t ht_Icc).sub continuousWithinAt_const).mono sdiff_subset
      · exact sub_ne_zero.mpr (hoff t ht_Icc)
    · exact (γ.deriv_continuous_off_partition t ht_Ioo ht_npart).continuousWithinAt
  · intro t ht
    calc ‖f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t‖
        ≤ ‖f (γ.toFun t) / (γ.toFun t - w)‖ * ‖deriv γ.toFun t‖ := norm_mul_le _ _
      _ = ‖f (γ.toFun t)‖ * ‖(γ.toFun t - w)⁻¹‖ * ‖deriv γ.toFun t‖ := by
            rw [norm_div, norm_inv, div_eq_mul_inv]
      _ ≤ M_f * M_inv * M_d :=
            mul_le_mul (mul_le_mul (hM_f t ht) (hM_inv t ht) (norm_nonneg _)
              (le_trans (norm_nonneg _) (hM_f t ht)))
              (hM_d t ht) (norm_nonneg _)
              (mul_nonneg (le_trans (norm_nonneg _) (hM_f t ht))
                (le_trans (norm_nonneg _) (hM_inv t ht)))

/-- Key identity: h₁(w) = h₂(w) - 2πi · n(γ,w) · f(w) for w off the curve.
This follows from expanding dslope and splitting the integral. -/
theorem dixonH1_eq (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (w : ℂ) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    dixonH1 f γ w = dixonH2 f γ w -
      2 * ↑Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b w * f w := by
  simp only [dixonH1, dixonH2]
  rw [intervalIntegral.integral_congr (dixonH1_dslope_expansion γ w hoff)]
  have h_base_int : IntervalIntegrable
      (fun t => (γ.toFun t - w)⁻¹ * deriv γ.toFun t) volume γ.a γ.b :=
    integrand_intervalIntegrable_of_avoids γ w hoff
  have h_fw_int : IntervalIntegrable
      (fun t => f w / (γ.toFun t - w) * deriv γ.toFun t) volume γ.a γ.b := by
    rw [show (fun t => f w / (γ.toFun t - w) * deriv γ.toFun t) =
        (fun t => f w * ((γ.toFun t - w)⁻¹ * deriv γ.toFun t)) from by
      ext t; rw [div_eq_mul_inv]; ring]
    exact h_base_int.const_mul _
  rw [intervalIntegral.integral_sub
    (dixonH1_cauchyIntegrand_integrable hU hf γ hγ_in_U w hoff) h_fw_int]
  congr 1
  exact integral_singular_term_eq_winding_times_coeff γ.toPiecewiseC1Curve w (f w) hoff

private lemma dixonH2_integrand_integrable (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b))
    (M_f M_d ε : ℝ) (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hM_f_nn : 0 ≤ M_f) (hε_pos : 0 < ε) (x : ℂ)
    (hdist_lb : ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - x‖)
    (hball_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x) :
    IntervalIntegrable
      (fun t => f (γ.toFun t) / (γ.toFun t - x) * deriv γ.toFun t) volume γ.a γ.b := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  apply intervalIntegrable_of_piecewise_continuousOn_bounded
    (P := γ.partition) (M_f * ε⁻¹ * M_d) hab
  · intro t ⟨ht_Icc, ht_npart⟩
    have ht_Ioo : t ∈ Ioo γ.a γ.b := mem_Ioo_of_notMem_partition γ ht_Icc ht_npart
    exact ((hfγ_cont t ht_Icc).div
        ((γ.continuous_toFun t ht_Icc).sub continuousWithinAt_const)
        (sub_ne_zero.mpr (hball_avoids t ht_Icc)) |>.mono sdiff_subset).mul
      (γ.deriv_continuous_off_partition t ht_Ioo ht_npart).continuousWithinAt
  · intro t ht
    rw [norm_mul, norm_div]
    have hbound1 : ‖f (γ.toFun t)‖ / ‖γ.toFun t - x‖ ≤ M_f / ε :=
      calc ‖f (γ.toFun t)‖ / ‖γ.toFun t - x‖
          ≤ ‖f (γ.toFun t)‖ / ε :=
            div_le_div_of_nonneg_left (norm_nonneg _) hε_pos (hdist_lb t ht)
        _ ≤ M_f / ε := by gcongr; exact hM_f t ht
    calc ‖f (γ.toFun t)‖ / ‖γ.toFun t - x‖ * ‖deriv γ.toFun t‖
        ≤ (M_f / ε) * M_d :=
          mul_le_mul hbound1 (hM_d t ht) (norm_nonneg _) (div_nonneg hM_f_nn hε_pos.le)
      _ = M_f * ε⁻¹ * M_d := by rw [div_eq_mul_inv]

private noncomputable def dixonH2_F (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) : ℂ → ℝ → ℂ :=
  fun x t => f (γ.toFun t) * (γ.toFun t - x)⁻¹ * deriv γ.toFun t

private noncomputable def dixonH2_F' (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) : ℂ → ℝ → ℂ :=
  fun x t => f (γ.toFun t) * (γ.toFun t - x)⁻¹ ^ 2 * deriv γ.toFun t

private lemma dixonH2_pointwise_hasDerivAt (fz c z x : ℂ) (hne : z - x ≠ 0) :
    HasDerivAt (fun x => fz * (z - x)⁻¹ * c) (fz * (z - x)⁻¹ ^ 2 * c) x := by
  have h1 : HasDerivAt (fun x => z - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub z
  have h2 : HasDerivAt (fun x => (z - x)⁻¹) (-(-1) / (z - x) ^ 2) x :=
    h1.fun_inv hne
  simp only [neg_neg, one_div] at h2
  have h3 : HasDerivAt (fun x => fz * (z - x)⁻¹) (fz * ((z - x) ^ 2)⁻¹) x :=
    h2.const_mul fz
  exact (h3.mul_const c).congr_deriv (by rw [inv_pow])

private lemma dixonH2_deriv_bound (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (M_f M_d ε : ℝ) (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hM_f_nn : 0 ≤ M_f) (hε_pos : 0 < ε) (w : ℂ)
    (hdist_lb : ∀ x ∈ Metric.ball w ε, ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - x‖) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w ε,
        ‖f (γ.toFun t) * (γ.toFun t - x)⁻¹ ^ 2 * deriv γ.toFun t‖ ≤
          M_f * ε⁻¹ ^ 2 * M_d := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  filter_upwards with t _ht x hx_ball
  have ht : t ∈ Icc γ.a γ.b := by rw [Set.uIoc_of_le hab] at _ht; exact Set.Ioc_subset_Icc_self _ht
  rw [norm_mul, norm_mul, norm_pow, norm_inv]
  calc ‖f (γ.toFun t)‖ * ‖γ.toFun t - x‖⁻¹ ^ 2 * ‖deriv γ.toFun t‖
      ≤ M_f * ε⁻¹ ^ 2 * M_d := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact hM_f t ht
          · exact pow_le_pow_left₀ (by positivity)
              (inv_anti₀ hε_pos (hdist_lb x hx_ball t ht)) 2
          · positivity
          · exact hM_f_nn
        · exact hM_d t ht
        · positivity
        · apply mul_nonneg
          · exact hM_f_nn
          · positivity

private lemma dixonH2_hasDerivAt (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b))
    (M_f M_d ε : ℝ) (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (_hM_f_nn : 0 ≤ M_f) (hε_pos : 0 < ε) (w : ℂ)
    (_hdist_lb_w : ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - w‖)
    (_hball_avoids : ∀ x ∈ Metric.ball w ε, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x)
    (_hdist_lb : ∀ x ∈ Metric.ball w ε, ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - x‖) :
    HasDerivAt (fun w => ∫ t in γ.a..γ.b, f (γ.toFun t) * (γ.toFun t - w)⁻¹ * deriv γ.toFun t)
      (∫ t in γ.a..γ.b, f (γ.toFun t) * (γ.toFun t - w)⁻¹ ^ 2 * deriv γ.toFun t) w := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hav_w : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w := fun t ht =>
    _hball_avoids w (Metric.mem_ball_self hε_pos) t ht
  have hF_int : IntervalIntegrable (dixonH2_F f γ w) volume γ.a γ.b := by
    have heq : dixonH2_F f γ w =
        fun t => f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t := by
      ext t; simp only [dixonH2_F, div_eq_mul_inv]
    rw [heq]
    exact dixonH2_integrand_integrable f γ hfγ_cont M_f M_d ε
      hM_f hM_d _hM_f_nn hε_pos w _hdist_lb_w hav_w
  have hF_meas : ∀ᶠ x in 𝓝 w,
      AEStronglyMeasurable (dixonH2_F f γ x) (volume.restrict (Set.uIoc γ.a γ.b)) := by
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds w hε_pos)
    intro x hx
    have hint_x : IntervalIntegrable (dixonH2_F f γ x) volume γ.a γ.b := by
      have heq : dixonH2_F f γ x =
          fun t => f (γ.toFun t) / (γ.toFun t - x) * deriv γ.toFun t := by
        ext t; simp only [dixonH2_F, div_eq_mul_inv]
      rw [heq]
      exact dixonH2_integrand_integrable f γ hfγ_cont M_f M_d ε
        hM_f hM_d _hM_f_nn hε_pos x (fun t ht => _hdist_lb x hx t ht)
        (fun t ht => _hball_avoids x hx t ht)
    exact hint_x.def'.aestronglyMeasurable
  have hF'_int : IntervalIntegrable (dixonH2_F' f γ w) volume γ.a γ.b := by
    apply intervalIntegrable_of_piecewise_continuousOn_bounded
      (P := γ.partition) (M_f * ε⁻¹ ^ 2 * M_d) hab
    · intro t ⟨ht_Icc, ht_npart⟩
      change ContinuousWithinAt
          (fun t => f (γ.toFun t) * (γ.toFun t - w)⁻¹ ^ 2 * deriv γ.toFun t)
          (Icc γ.a γ.b \ γ.partition) t
      have ht_Ioo : t ∈ Ioo γ.a γ.b := mem_Ioo_of_notMem_partition γ ht_Icc ht_npart
      exact ((hfγ_cont t ht_Icc).mul
          (((γ.continuous_toFun t ht_Icc).sub continuousWithinAt_const |>.inv₀
            (sub_ne_zero.mpr (hav_w t ht_Icc))).pow 2)
          |>.mono sdiff_subset).mul
        (γ.deriv_continuous_off_partition t ht_Ioo ht_npart).continuousWithinAt
    · intro t ht
      change ‖f (γ.toFun t) * (γ.toFun t - w)⁻¹ ^ 2 * deriv γ.toFun t‖ ≤ M_f * ε⁻¹ ^ 2 * M_d
      rw [norm_mul, norm_mul, norm_pow, norm_inv]
      exact mul_le_mul
        (mul_le_mul (hM_f t ht)
          (pow_le_pow_left₀ (by positivity) (inv_anti₀ hε_pos (_hdist_lb_w t ht)) 2)
          (by positivity) _hM_f_nn)
        (hM_d t ht) (by positivity) (mul_nonneg _hM_f_nn (by positivity))
  have hF'_meas : AEStronglyMeasurable (dixonH2_F' f γ w)
      (volume.restrict (Set.uIoc γ.a γ.b)) := hF'_int.def'.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w ε, ‖dixonH2_F' f γ x t‖ ≤ M_f * ε⁻¹ ^ 2 * M_d :=
    dixonH2_deriv_bound f γ M_f M_d ε hM_f hM_d _hM_f_nn hε_pos w _hdist_lb
  have hbound_int : IntervalIntegrable (fun _ => M_f * ε⁻¹ ^ 2 * M_d)
      volume γ.a γ.b := intervalIntegral.intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w ε,
        HasDerivAt (fun x => dixonH2_F f γ x t) (dixonH2_F' f γ x t) x := by
    filter_upwards with t _ht x hx_ball
    have ht' : t ∈ Icc γ.a γ.b := by rw [Set.uIoc_of_le hab] at _ht; exact Ioc_subset_Icc_self _ht
    simp only [dixonH2_F, dixonH2_F']
    exact dixonH2_pointwise_hasDerivAt (f (γ.toFun t)) (deriv γ.toFun t) (γ.toFun t) x
      (sub_ne_zero.mpr (_hball_avoids x hx_ball t ht'))
  refine ((intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds w hε_pos) hF_meas hF_int hF'_meas h_bound hbound_int
    h_diff).2).congr_deriv ?_
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [dixonH2_F', sq]

private lemma ball_avoids_curve_of_infDist_pos (γ : PiecewiseC1Immersion)
    (w : ℂ) (hinfDist_pos : 0 < Metric.infDist w (γ.toFun '' Icc γ.a γ.b)) :
    ∀ x ∈ Metric.ball w (Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2),
      ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x := by
  intro x hx t ht heq
  linarith [Metric.infDist_le_dist_of_mem (x := w) (show x ∈ γ.toFun '' Icc γ.a γ.b from ⟨t, ht,
    heq⟩),
    show dist w x < _ / 2 from by rw [dist_comm]; exact Metric.mem_ball.mp hx]

private lemma dist_lower_bound_at_center (γ : PiecewiseC1Immersion) (w : ℂ) :
    ∀ t ∈ Icc γ.a γ.b,
      Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 ≤ ‖γ.toFun t - w‖ := by
  intro t ht
  have hid := Metric.infDist_le_dist_of_mem (x := w)
    (show γ.toFun t ∈ γ.toFun '' Icc γ.a γ.b from ⟨t, ht, rfl⟩)
  rw [Complex.dist_eq, ← norm_neg (w - γ.toFun t), neg_sub] at hid
  linarith [Metric.infDist_nonneg (x := w) (s := γ.toFun '' Icc γ.a γ.b)]

private lemma dist_lower_bound_on_ball (γ : PiecewiseC1Immersion) (w : ℂ) :
    ∀ x ∈ Metric.ball w (Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2),
      ∀ t ∈ Icc γ.a γ.b,
        Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 ≤ ‖γ.toFun t - x‖ := by
  intro x hx t ht
  have htri := dist_triangle w x (γ.toFun t)
  rw [dist_comm w x] at htri
  have h1 : Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 ≤ dist x (γ.toFun t) := by
    linarith [Metric.infDist_le_dist_of_mem (x := w)
      (show γ.toFun t ∈ γ.toFun '' Icc γ.a γ.b from ⟨t, ht, rfl⟩),
      Metric.mem_ball.mp hx]
  rwa [Complex.dist_eq, ← norm_neg (x - γ.toFun t), neg_sub] at h1

private lemma dixonH2_differentiableAt_infDist_pos (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hf_cont : ContinuousOn f (γ.toFun '' Icc γ.a γ.b))
    (w : ℂ) (hinfDist_pos : 0 < Metric.infDist w (γ.toFun '' Icc γ.a γ.b)) :
    DifferentiableAt ℂ
      (fun w => ∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t) w := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b) :=
    hf_cont.comp γ.continuous_toFun fun t ht => ⟨t, ht, rfl⟩
  obtain ⟨M_f, hM_f_spec⟩ := isCompact_Icc.exists_bound_of_continuousOn hfγ_cont.norm
  simp only [norm_norm] at hM_f_spec
  obtain ⟨M_d, hM_d_spec⟩ := piecewiseC1Immersion_deriv_bounded γ
  exact (dixonH2_hasDerivAt f γ hfγ_cont M_f M_d
    (Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2) hM_f_spec hM_d_spec
    (le_trans (norm_nonneg _) (hM_f_spec γ.a (left_mem_Icc.mpr hab))) (by linarith) w
    (dist_lower_bound_at_center γ w) (ball_avoids_curve_of_infDist_pos γ w hinfDist_pos)
    (dist_lower_bound_on_ball γ w)).differentiableAt

/-- h₂ is differentiable at every point off the curve, when f is continuous on the image. -/
theorem dixonH2_differentiableAt (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hf_cont : ContinuousOn f (γ.toFun '' Icc γ.a γ.b)) (w : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    DifferentiableAt ℂ (dixonH2 f γ) w := by
  change DifferentiableAt ℂ
      (fun w => ∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t) w
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have himage_closed := (isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isClosed
  exact dixonH2_differentiableAt_infDist_pos f γ hf_cont w
    ((himage_closed.notMem_iff_infDist_pos
      ⟨γ.toFun γ.a, γ.a, left_mem_Icc.mpr hab, rfl⟩).mp
      fun ⟨t, ht, heq⟩ => hoff t ht heq)

/-- Uniform bound on dslope: for c in a compact set K ⊂ U and w in a ball B ⊂ U,
‖dslope f c w‖ is bounded. Uses MVT on convex balls for nearby points and
triangle inequality for distant points. -/
private lemma dslope_uniform_bound (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (K : Set ℂ) (hK_compact : IsCompact K) (hK_sub : K ⊆ U) (w₀ : ℂ) (hw₀ : w₀ ∈ U) :
    ∃ C > 0, ∃ δ > 0, ∀ c ∈ K, ∀ w ∈ Metric.ball w₀ δ,
      ‖dslope f c w‖ ≤ C := by
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  have hcb_sub : Metric.closedBall w₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hr_sub
  obtain ⟨M_f, hM_f⟩ :=
    (hK_compact.union (isCompact_closedBall w₀ (r / 2))).exists_bound_of_continuousOn
      (hf.continuousOn.mono (Set.union_subset hK_sub hcb_sub) |>.norm)
  obtain ⟨C_d, hC_d⟩ :=
    (isCompact_closedBall w₀ (r / 2)).exists_bound_of_continuousOn
      (((hf.mono hr_sub).deriv Metric.isOpen_ball).continuousOn.mono
        (Metric.closedBall_subset_ball (by linarith)))
  refine ⟨max (C_d + 1) (8 * (|M_f| + 1) / r + 1), by positivity,
    r / 4, by linarith, fun c hc w hw => ?_⟩
  by_cases hcw : c = w
  · subst hcw; rw [dslope_same]
    calc ‖deriv f c‖ ≤ C_d :=
          hC_d c (Metric.closedBall_subset_closedBall (by linarith : r / 4 ≤ r / 2)
            (Metric.ball_subset_closedBall hw))
      _ ≤ C_d + 1 := by linarith
      _ ≤ _ := le_max_left _ _
  · have hne : w ≠ c := fun h => hcw h.symm
    rw [dslope_of_ne _ hne, slope_def_field, norm_div]
    by_cases hc_near : c ∈ Metric.closedBall w₀ (r / 2)
    · have hw_cb : w ∈ Metric.closedBall w₀ (r / 2) :=
        Metric.closedBall_subset_closedBall (by linarith : r / 4 ≤ r / 2)
          (Metric.ball_subset_closedBall hw)
      have h_mvt := (convex_closedBall w₀ (r / 2)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hf z (hcb_sub hz)).differentiableAt (hU.mem_nhds (hcb_sub hz)))
        hC_d hc_near hw_cb
      calc ‖f w - f c‖ / ‖w - c‖
          ≤ C_d * ‖w - c‖ / ‖w - c‖ :=
            div_le_div_of_nonneg_right h_mvt (norm_nonneg _)
        _ = C_d := mul_div_cancel_right₀ C_d (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
        _ ≤ C_d + 1 := by linarith
        _ ≤ _ := le_max_left _ _
    · have h_sep : r / 4 ≤ ‖w - c‖ := by
        have : r / 2 < dist w₀ c := by
          rw [dist_comm]; rwa [Metric.mem_closedBall, not_le] at hc_near
        calc r / 4 = r / 2 - r / 4 := by ring
          _ ≤ dist w₀ c - dist w w₀ := by linarith [Metric.mem_ball.mp hw]
          _ ≤ dist w c := by
              have := dist_triangle_left c w₀ w
              rw [dist_comm w₀ c]; linarith
          _ = ‖w - c‖ := by rw [dist_eq_norm]
      simp only [norm_norm] at hM_f
      have h1 : ‖f w‖ ≤ M_f := hM_f w (Or.inr
        (Metric.closedBall_subset_closedBall (by linarith : r / 4 ≤ r / 2)
          (Metric.ball_subset_closedBall hw)))
      have hM_f_nn : 0 ≤ M_f := le_trans (norm_nonneg _) h1
      have h_num : ‖f w - f c‖ ≤ 2 * M_f := by
        linarith [norm_sub_le (f w) (f c), hM_f c (Or.inl hc)]
      have h_denom_pos : (0 : ℝ) < ‖w - c‖ := lt_of_lt_of_le (by linarith) h_sep
      have h_eq : 2 * M_f / (r / 4) = 8 * M_f / r := by ring
      have h_le : 8 * M_f / r ≤ 8 * (|M_f| + 1) / r + 1 := by
        rw [abs_of_nonneg hM_f_nn]
        linarith [div_nonneg (show (0 : ℝ) ≤ 8 by norm_num) hr_pos.le,
          (show 8 * M_f / r + 8 / r + 1 = 8 * (M_f + 1) / r + 1 from by ring)]
      exact le_trans
        (le_trans (div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos))
          (div_le_div_of_nonneg_left (by linarith) (by linarith) h_sep))
        (le_trans (h_eq ▸ le_refl _) (le_trans h_le (le_max_right _ _)))

private theorem dixonH1_dslope_t_cont (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (x : ℂ) :
    ContinuousOn (fun t => dslope f (γ.toFun t) x) (Icc γ.a γ.b) := by
  by_cases hx : x ∈ U
  · have h_eq : ∀ t ∈ Icc γ.a γ.b, dslope f (γ.toFun t) x = dslope f x (γ.toFun t) := by
      intro t ht
      by_cases h : γ.toFun t = x
      · subst h; simp only [dslope_same]
      · simp only [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ h]
        exact slope_comm f (γ.toFun t) x
    apply ContinuousOn.congr _ h_eq
    exact ((continuousOn_dslope (hU.mem_nhds hx)).mpr
        ⟨hf.continuousOn, (hf x hx).differentiableAt (hU.mem_nhds hx)⟩).comp
      γ.continuous_toFun (fun t ht => hγ_in_U t ht)
  · have hne : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x := fun t ht heq =>
      hx (heq ▸ hγ_in_U t ht)
    have h_eq : ∀ t ∈ Icc γ.a γ.b,
        dslope f (γ.toFun t) x = (f x - f (γ.toFun t)) / (x - γ.toFun t) := by
      intro t ht
      rw [dslope_of_ne _ (Ne.symm (hne t ht)), slope_def_field]
    apply ContinuousOn.congr _ h_eq
    apply ContinuousOn.div
    · exact continuousOn_const.sub
        (hf.continuousOn.comp γ.continuous_toFun (fun t ht => hγ_in_U t ht))
    · exact continuousOn_const.sub γ.continuous_toFun
    · intro t ht; exact sub_ne_zero.mpr (Ne.symm (hne t ht))

private theorem dixonH1_F'_aestronglyMeasurable {M_d C_b δ₀ : ℝ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (w₀ : ℂ) (hw₀ : w₀ ∈ U)
    (hdslope_diff : ∀ t ∈ Icc γ.a γ.b, DifferentiableOn ℂ (dslope f (γ.toFun t)) U)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hδ₀_pos : 0 < δ₀)
    (hBd : ∀ c ∈ γ.toFun '' Icc γ.a γ.b, ∀ w ∈ Metric.ball w₀ δ₀,
      ‖dslope f c w‖ ≤ C_b)
    (_hC_pos : 0 < C_b) :
    AEStronglyMeasurable
      (fun t => deriv (dslope f (γ.toFun t)) w₀ * deriv γ.toFun t)
      (volume.restrict (Set.uIoc γ.a γ.b)) := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hdslope_t_cont := dixonH1_dslope_t_cont hU hf γ hγ_in_U
  refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop (α := ℕ))
      (f := fun n t => ((↑n + 1 : ℂ)) * (dslope f (γ.toFun t) (w₀ + 1 / (↑n + 1)) -
        dslope f (γ.toFun t) w₀) * deriv γ.toFun t) ?_ ?_
  · intro n
    obtain ⟨M_n, hM_n⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hdslope_t_cont (w₀ + 1 / ((n : ℂ) + 1))).norm)
    simp only [norm_norm] at hM_n
    exact (intervalIntegrable_of_piecewise_continuousOn_bounded (P := γ.partition)
      (‖(n : ℂ) + 1‖ * (M_n + C_b) * M_d) hab
      (fun t ⟨ht_Icc, ht_np⟩ => by
        have ht_Ioo : t ∈ Ioo γ.a γ.b := mem_Ioo_of_notMem_partition γ ht_Icc ht_np
        exact (continuousWithinAt_const.mul
          ((hdslope_t_cont _ t ht_Icc |>.mono sdiff_subset).sub
            (hdslope_t_cont _ t ht_Icc |>.mono sdiff_subset))).mul
          (γ.deriv_continuous_off_partition t ht_Ioo ht_np).continuousWithinAt)
      (fun t ht => by
        simp only [norm_mul]
        have h1 : ‖dslope f (γ.toFun t) (w₀ + 1 / ((n : ℂ) + 1)) -
            dslope f (γ.toFun t) w₀‖ ≤ M_n + C_b :=
          le_trans (norm_sub_le _ _)
            (add_le_add (hM_n t ht) (hBd _ ⟨t, ht, rfl⟩ w₀ (Metric.mem_ball_self hδ₀_pos)))
        have h2 : ‖deriv γ.toFun t‖ ≤ M_d := hM_d t ht
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
          h2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (le_trans (norm_nonneg _) h1))
        )).def'.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le hab] at ht
    have ht_Icc : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self ht
    have hderiv : HasDerivAt (dslope f (γ.toFun t)) (deriv (dslope f (γ.toFun t)) w₀) w₀ :=
      ((hdslope_diff t ht_Icc).differentiableAt (hU.mem_nhds hw₀)).hasDerivAt
    have h_tendsto_zero : Filter.Tendsto
        (fun n : ℕ => (1 : ℂ) / (↑n + 1)) Filter.atTop (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hR : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) Filter.atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hC : Filter.Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) Filter.atTop (𝓝 0) := by
          have := Complex.continuous_ofReal.continuousAt.tendsto.comp hR
          simp only [Function.comp_def] at this
          exact this.congr (fun n => by push_cast; ring)
        exact hC
      · exact Filter.Eventually.of_forall (fun n => by
          apply div_ne_zero one_ne_zero
          norm_cast)
    have hGn_eq : ∀ n : ℕ, ((↑n + 1 : ℂ)) *
            (dslope f (γ.toFun t) (w₀ + 1 / (↑n + 1)) - dslope f (γ.toFun t) w₀) *
            deriv γ.toFun t =
        ((1 : ℂ) / (↑n + 1))⁻¹ •
          (dslope f (γ.toFun t) (w₀ + 1 / (↑n + 1)) - dslope f (γ.toFun t) w₀) *
        deriv γ.toFun t := by
      intro n; simp only [smul_eq_mul]
      have hn1 : (↑n + 1 : ℂ) ≠ 0 := by norm_cast
      field_simp [hn1]
    simp_rw [hGn_eq]
    exact (hderiv.tendsto_slope_zero.comp h_tendsto_zero).mul_const _

private theorem dixonH1_dslope_intervalIntegrable (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (x : ℂ) (C_b M_d : ℝ) (hC_pos : 0 < C_b)
    (hBd : ∀ c ∈ γ.toFun '' Icc γ.a γ.b, ‖dslope f c x‖ ≤ C_b)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d) :
    IntervalIntegrable
      (fun t => dslope f (γ.toFun t) x * deriv γ.toFun t) volume γ.a γ.b := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hdslope_t_cont := dixonH1_dslope_t_cont hU hf γ hγ_in_U
  apply intervalIntegrable_of_piecewise_continuousOn_bounded (P := γ.partition) (C_b * M_d) hab
  · intro t ⟨ht_Icc, ht_np⟩
    have ht_Ioo : t ∈ Ioo γ.a γ.b := mem_Ioo_of_notMem_partition γ ht_Icc ht_np
    exact (hdslope_t_cont x t ht_Icc |>.mono sdiff_subset).mul
      (γ.deriv_continuous_off_partition t ht_Ioo ht_np).continuousWithinAt
  · intro t ht
    rw [norm_mul]
    exact mul_le_mul (hBd _ ⟨t, ht, rfl⟩) (hM_d t ht) (norm_nonneg _) hC_pos.le

/-- h₁ is differentiable on all of U, including across the curve.
Uses the Leibniz rule (parametric differentiation of the dslope integral). -/
theorem dixonH1_differentiableOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    DifferentiableOn ℂ (dixonH1 f γ) U := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hdslope_diff : ∀ t ∈ Icc γ.a γ.b, DifferentiableOn ℂ (dslope f (γ.toFun t)) U :=
    fun t ht => (differentiableOn_dslope (hU.mem_nhds (hγ_in_U t ht))).mpr hf
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  intro w₀ hw₀
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  obtain ⟨C, hC_pos, δ₀, hδ₀_pos, hBd⟩ :=
    dslope_uniform_bound hU hf _
      (isCompact_Icc.image_of_continuousOn γ.continuous_toFun)
      (fun _ ⟨t, ht, he⟩ => he ▸ hγ_in_U t ht) w₀ hw₀
  set ε := min δ₀ r / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have h2ε_le_δ₀ : 2 * ε ≤ δ₀ := by simp only [hε_def]; linarith [min_le_left δ₀ r]
  have h2ε_le_r : 2 * ε ≤ r := by simp only [hε_def]; linarith [min_le_right δ₀ r]
  have hcb_U : ∀ x ∈ Metric.ball w₀ ε, Metric.closedBall x ε ⊆ U := fun x hx y hy => by
    apply hr_sub; rw [Metric.mem_ball] at hx ⊢
    have hy' := Metric.mem_closedBall.mp hy
    linarith [dist_triangle y x w₀]
  have hCauchy : ∀ t ∈ Icc γ.a γ.b, ∀ x ∈ Metric.ball w₀ ε,
      ‖deriv (dslope f (γ.toFun t)) x‖ ≤ C / ε := by
    intro t ht x hx
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hε_pos
    · exact (hdslope_diff t ht).diffContOnCl_ball (hcb_U x hx)
    · intro z hz
      apply hBd _ ⟨t, ht, rfl⟩
      rw [Metric.mem_ball] at hx ⊢; rw [Metric.mem_sphere] at hz
      linarith [dist_triangle z x w₀]
  have hF_int := dixonH1_dslope_intervalIntegrable hU hf γ hγ_in_U w₀ C M_d hC_pos
    (fun c hc => hBd c hc w₀ (Metric.mem_ball_self hδ₀_pos)) hM_d
  have hF_meas : ∀ᶠ x in 𝓝 w₀,
      AEStronglyMeasurable (fun t => dslope f (γ.toFun t) x * deriv γ.toFun t)
        (volume.restrict (Set.uIoc γ.a γ.b)) := by
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds w₀ hε_pos)
    intro x hx
    exact (dixonH1_dslope_intervalIntegrable hU hf γ hγ_in_U x C M_d hC_pos
      (fun c hc => hBd c hc x (Metric.ball_subset_ball (by linarith) hx))
      hM_d).def'.aestronglyMeasurable
  have hF'_meas := dixonH1_F'_aestronglyMeasurable hU hf γ hγ_in_U w₀ hw₀
    hdslope_diff hM_d hδ₀_pos hBd hC_pos
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w₀ ε,
        ‖deriv (dslope f (γ.toFun t)) x * deriv γ.toFun t‖ ≤ C / ε * M_d := by
    filter_upwards with t _ht x hx
    have ht_Icc : t ∈ Icc γ.a γ.b := by
      rw [Set.uIoc_of_le hab] at _ht; exact Ioc_subset_Icc_self _ht
    rw [norm_mul]
    exact mul_le_mul (hCauchy t ht_Icc x hx) (hM_d t ht_Icc) (norm_nonneg _)
      (div_nonneg hC_pos.le hε_pos.le)
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w₀ ε,
        HasDerivAt (fun x => dslope f (γ.toFun t) x * deriv γ.toFun t)
          (deriv (dslope f (γ.toFun t)) x * deriv γ.toFun t) x := by
    filter_upwards with t _ht x hx
    have ht_Icc : t ∈ Icc γ.a γ.b := by
      rw [Set.uIoc_of_le hab] at _ht; exact Ioc_subset_Icc_self _ht
    have hx_U : x ∈ U := hr_sub (Metric.ball_subset_ball (by linarith : ε ≤ r) hx)
    exact ((hdslope_diff t ht_Icc).differentiableAt (hU.mem_nhds hx_U) |>.hasDerivAt).mul_const _
  exact ((intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds w₀ hε_pos) hF_meas hF_int hF'_meas h_bound
    intervalIntegral.intervalIntegrable_const h_diff).2).differentiableAt

open Classical in
/-- The Dixon function: h1 on U, h2 on C \ U. -/
noncomputable def dixonFunction (f : ℂ → ℂ) (U : Set ℂ)
    (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  if _h : w ∈ U then dixonH1 f γ w else dixonH2 f γ w

/-- The Dixon function is entire (differentiable on all of ℂ).
On U: it's h₁, holomorphic by dixonH1_differentiableOn.
On ℂ \ U: it's h₂, holomorphic by dixonH2_differentiableAt.
Patching at ∂U: null-homologous gives n(γ,w) = 0 near ∂U, so h₁ = h₂ there. -/
theorem dixonFunction_differentiable (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    Differentiable ℂ (dixonFunction f U γ) := by
  classical
  intro w
  by_cases hw : w ∈ U
  · have h_eq : ∀ᶠ w' in 𝓝 w, dixonFunction f U γ w' = dixonH1 f γ w' :=
      Filter.Eventually.mono (hU.mem_nhds hw)
        (fun w' hw' => by simp only [dixonFunction]; exact if_pos hw')
    exact ((dixonH1_differentiableOn hU hf γ h_null.image_subset).differentiableAt
      (hU.mem_nhds hw)).congr_of_eventuallyEq h_eq
  · have hab : γ.a ≤ γ.b := le_of_lt γ.hab
    have hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w := fun t ht heq =>
      hw (heq ▸ h_null.image_subset t ht)
    have himage_closed :=
      (isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isClosed
    have hw_notmem : w ∉ γ.toFun '' Icc γ.a γ.b := fun ⟨t, ht, heq⟩ => hoff t ht heq
    have hinfDist_pos : 0 < Metric.infDist w (γ.toFun '' Icc γ.a γ.b) :=
      (himage_closed.notMem_iff_infDist_pos
        ⟨γ.toFun γ.a, γ.a, left_mem_Icc.mpr hab, rfl⟩).mp hw_notmem
    set ε := Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 with hε_def
    have hε_pos : 0 < ε := by positivity
    have hball_avoids : ∀ t ∈ Icc γ.a γ.b, ∀ w' ∈ Metric.ball w ε, γ.toFun t ≠ w' := by
      intro t ht w' hw' heq
      linarith [Metric.infDist_le_dist_of_mem (x := w)
        (show w' ∈ γ.toFun '' Icc γ.a γ.b from ⟨t, ht, heq⟩),
        show dist w w' < ε from dist_comm w' w ▸ Metric.mem_ball.mp hw']
    have hwn_cts : ContinuousOn (fun w' => generalizedWindingNumber' γ.toFun γ.a γ.b w')
        (Metric.ball w ε) := by
      apply ContinuousOn.congr
        (f := fun w' => (2 * ↑Real.pi * I)⁻¹ *
          ∫ t in γ.a..γ.b, (γ.toFun t - w')⁻¹ * deriv γ.toFun t)
      · apply continuousOn_const.mul
        intro w' hw'
        have hoff' : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w' :=
          fun t ht heq => hball_avoids t ht w' hw' heq
        have hdiff2 : DifferentiableAt ℂ
            (fun w'' => ∫ t in γ.a..γ.b, (γ.toFun t - w'')⁻¹ * deriv γ.toFun t) w' := by
          have h := dixonH2_differentiableAt (fun _ => 1) γ continuousOn_const w' hoff'
          convert h using 2; simp only [dixonH2, div_eq_mul_inv, one_mul]
        exact hdiff2.continuousAt.continuousWithinAt
      · intro w' hw'
        have hoff' : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w' :=
          fun t ht heq => hball_avoids t ht w' hw' heq
        exact generalizedWindingNumber_eq_classical_away γ.toPiecewiseC1Curve w' hoff'
    have hwn_w := h_null.winding_zero w hw
    have hwn_int : ∀ w' ∈ Metric.ball w ε, ∃ n : ℤ,
        generalizedWindingNumber' γ.toFun γ.a γ.b w' = n := by
      intro w' hw'
      exact windingNumber_integer_of_piecewise_closed_avoiding γ.toFun γ.a γ.b w' γ.partition
        γ.hab h_null.closed γ.continuous_toFun
        (fun t ht hP => γ.smooth_off_partition t (Ioo_subset_Icc_self ht) hP)
        (fun _p1 _p2 _h12 hnoP hsub t ht =>
          (γ.deriv_continuous_off_partition t (hsub ht) (hnoP t ht)).continuousWithinAt)
        (fun t ht => hball_avoids t ht w' hw')
        ⟨_, fun t ht => (piecewiseC1Immersion_deriv_bounded γ).choose_spec t ht⟩
    have hwn_zero_ball : ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber' γ.toFun γ.a γ.b w' = 0 := by
      haveI hpreconn : PreconnectedSpace (Metric.ball w ε) :=
        isPreconnected_iff_preconnectedSpace.mp
          (Metric.isConnected_ball hε_pos).isPreconnected
      have hwn_cts_sub : Continuous
          (fun w'' : Metric.ball w ε =>
            generalizedWindingNumber' γ.toFun γ.a γ.b w''.val) :=
        hwn_cts.comp_continuous continuous_subtype_val (fun w'' => w''.2)
      let wn_Z : Metric.ball w ε → ℤ := fun w'' => (hwn_int w'' w''.2).choose
      have wn_Z_cast : ∀ w'' : Metric.ball w ε,
          (wn_Z w'' : ℂ) = generalizedWindingNumber' γ.toFun γ.a γ.b w''.val :=
        fun w'' => (hwn_int w'' w''.2).choose_spec.symm
      have wn_Z_cont : Continuous wn_Z := by
        rw [← IsLocallyConstant.iff_continuous, IsLocallyConstant.iff_eventually_eq]
        intro ⟨w'', hw''⟩
        have hwn_cts_at : ContinuousAt
            (fun w''' : Metric.ball w ε =>
              generalizedWindingNumber' γ.toFun γ.a γ.b w'''.val) ⟨w'', hw''⟩ :=
          hwn_cts_sub.continuousAt
        have hev : ∀ᶠ w''' : Metric.ball w ε in 𝓝 ⟨w'', hw''⟩,
            ‖generalizedWindingNumber' γ.toFun γ.a γ.b w'''.val -
              generalizedWindingNumber' γ.toFun γ.a γ.b w''‖ < 1 / 2 := by
          have h_nbhd : ∀ᶠ w''' : Metric.ball w ε in 𝓝 ⟨w'', hw''⟩,
              generalizedWindingNumber' γ.toFun γ.a γ.b w'''.val ∈
                Metric.ball (generalizedWindingNumber' γ.toFun γ.a γ.b w'') (1/2) :=
            hwn_cts_at (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))
          exact h_nbhd.mono fun w''' h_mem =>
            (Complex.dist_eq _ _).symm ▸ Metric.mem_ball.mp h_mem
        apply hev.mono; intro ⟨w''', hw'''⟩ h_lt
        apply Int.cast_injective (α := ℂ); rw [wn_Z_cast, wn_Z_cast]
        obtain ⟨n1, hn1⟩ := hwn_int w''' hw'''
        obtain ⟨n2, hn2⟩ := hwn_int w'' hw''
        have hm : generalizedWindingNumber' γ.toFun γ.a γ.b w''' -
            generalizedWindingNumber' γ.toFun γ.a γ.b w'' = (n1 - n2 : ℤ) := by
          push_cast [hn1, hn2]; ring
        have h_norm_m : ‖((n1 - n2 : ℤ) : ℂ)‖ < 1 / 2 := hm ▸ h_lt
        rw [Complex.norm_intCast] at h_norm_m
        have h_zero : n1 - n2 = 0 := by
          have key : (|(n1 - n2 : ℤ)| : ℝ) < 1 := by
            have := h_norm_m
            simp only [Int.cast_sub] at this
            linarith [abs_nonneg ((n1 : ℝ) - n2)]
          exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast key)
        exact sub_eq_zero.mp (hm ▸ (by exact_mod_cast h_zero))
      have hwn_Z_w : wn_Z ⟨w, Metric.mem_ball_self hε_pos⟩ = 0 := by
        apply Int.cast_injective (α := ℂ); push_cast; rwa [wn_Z_cast]
      intro w' hw'
      obtain ⟨n, hn⟩ := hwn_int w' hw'
      have h_n_zero : n = (0 : ℤ) := by
        have h1 : (wn_Z ⟨w', hw'⟩ : ℂ) = n := by rwa [wn_Z_cast]
        have hlc : IsLocallyConstant wn_Z := (IsLocallyConstant.iff_continuous wn_Z).mpr wn_Z_cont
        have h2 : (wn_Z ⟨w', hw'⟩ : ℂ) = 0 := mod_cast
          (hlc.apply_eq_of_isPreconnected hpreconn.isPreconnected_univ
            (Set.mem_univ _) (Set.mem_univ _)).trans hwn_Z_w
        exact_mod_cast h1.symm.trans h2
      simp only [hn, h_n_zero, Int.cast_zero]
    have heq_on_ball : ∀ᶠ w' in 𝓝 w, dixonFunction f U γ w' = dixonH2 f γ w' := by
      apply Filter.Eventually.mono (Metric.ball_mem_nhds w hε_pos)
      intro w' hw'
      simp only [dixonFunction]
      split_ifs with hw'U
      · have hoff' : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w' := fun t ht heq =>
          hball_avoids t ht w' hw' heq
        rw [dixonH1_eq hU hf γ h_null.image_subset w' hoff', hwn_zero_ball w' hw']; ring
      · rfl
    have h2_diff : DifferentiableAt ℂ (dixonH2 f γ) w := dixonH2_differentiableAt f γ
      (hf.continuousOn.mono fun _ ⟨t, ht, heq⟩ => heq ▸ h_null.image_subset t ht) w hoff
    exact h2_diff.congr_of_eventuallyEq heq_on_ball

private lemma curveImage_dist_lower_bound (γ : PiecewiseC1Immersion) {R : ℝ}
    (hR : ∀ x ∈ γ.toFun '' Icc γ.a γ.b, ‖x‖ ≤ R) (w : ℂ) {t : ℝ}
    (ht : t ∈ Icc γ.a γ.b) : ‖w‖ - R ≤ ‖γ.toFun t - w‖ := by
  have h1 : ‖w‖ - ‖γ.toFun t‖ ≤ ‖w - γ.toFun t‖ := norm_sub_norm_le w (γ.toFun t)
  rw [norm_sub_rev] at h1
  linarith [hR (γ.toFun t) ⟨t, ht, rfl⟩]

private lemma dixonH2_norm_bound (γ : PiecewiseC1Immersion) {R M_f M_d : ℝ}
    (hM_f_nn : 0 ≤ M_f) (hR : ∀ x ∈ γ.toFun '' Icc γ.a γ.b, ‖x‖ ≤ R)
    (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    {w : ℂ} (hw : R < ‖w‖) :
    ‖dixonH2 f γ w‖ ≤ M_f * M_d * (γ.b - γ.a) / (‖w‖ - R) := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  simp only [dixonH2]
  have hpos : 0 < ‖w‖ - R := by linarith
  have h_ptwise : ∀ t ∈ Set.uIoc γ.a γ.b,
      ‖f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t‖ ≤ M_f * M_d / (‖w‖ - R) := by
    intro t ht_ui
    have ht : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self (Set.uIoc_of_le hab ▸ ht_ui)
    rw [norm_mul, norm_div]
    calc ‖f (γ.toFun t)‖ / ‖γ.toFun t - w‖ * ‖deriv γ.toFun t‖
        ≤ (M_f / (‖w‖ - R)) * M_d :=
          mul_le_mul (div_le_div₀ hM_f_nn (hM_f t ht) hpos
            (curveImage_dist_lower_bound γ hR w ht))
            (hM_d t ht) (norm_nonneg _) (div_nonneg hM_f_nn hpos.le)
      _ = M_f * M_d / (‖w‖ - R) := by ring
  calc ‖∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t‖
      ≤ (M_f * M_d / (‖w‖ - R)) * |γ.b - γ.a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise
    _ = M_f * M_d * (γ.b - γ.a) / (‖w‖ - R) := by
        rw [abs_of_nonneg (by linarith : 0 ≤ γ.b - γ.a)]; ring

private lemma windingNumber_norm_lt_one (γ : PiecewiseC1Immersion) {R M_d : ℝ} {w : ℂ}
    (hR : ∀ x ∈ γ.toFun '' Icc γ.a γ.b, ‖x‖ ≤ R)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w)
    (hR_lt : R < ‖w‖)
    (hw : M_d * (γ.b - γ.a) / (2 * Real.pi) < ‖w‖ - R) :
    ‖generalizedWindingNumber' γ.toFun γ.a γ.b w‖ < 1 := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hba_nn : 0 ≤ γ.b - γ.a := by linarith
  have h2pi_pos : 0 < 2 * Real.pi := Real.two_pi_pos
  have hpos : 0 < ‖w‖ - R := by linarith
  rw [generalizedWindingNumber_eq_classical_away γ.toPiecewiseC1Curve w hoff, norm_mul,
    norm_inv, norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  have h_ptwise : ∀ t ∈ Set.uIoc γ.a γ.b,
      ‖(γ.toFun t - w)⁻¹ * deriv γ.toFun t‖ ≤ M_d / (‖w‖ - R) := by
    intro t ht_ui
    have ht := Ioc_subset_Icc_self (Set.uIoc_of_le hab ▸ ht_ui)
    rw [norm_mul, norm_inv]
    calc ‖γ.toFun t - w‖⁻¹ * ‖deriv γ.toFun t‖
        ≤ (‖w‖ - R)⁻¹ * M_d := by
          apply mul_le_mul _ (hM_d t ht) (norm_nonneg _) (inv_nonneg.mpr hpos.le)
          exact inv_anti₀ hpos (curveImage_dist_lower_bound γ hR w ht)
      _ = M_d / (‖w‖ - R) := by rw [mul_comm, div_eq_mul_inv]
  have h_int_b : ‖∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
      ≤ M_d / (‖w‖ - R) * (γ.b - γ.a) := by
    calc ‖∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
        ≤ M_d / (‖w‖ - R) * |γ.b - γ.a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise
      _ = M_d / (‖w‖ - R) * (γ.b - γ.a) := by rw [abs_of_nonneg hba_nn]
  calc (2 * Real.pi)⁻¹ * ‖∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
      ≤ (2 * Real.pi)⁻¹ * (M_d / (‖w‖ - R) * (γ.b - γ.a)) :=
        mul_le_mul_of_nonneg_left h_int_b (inv_nonneg.mpr h2pi_pos.le)
    _ < 1 := by
        rw [show (2 * Real.pi)⁻¹ * (M_d / (‖w‖ - R) * (γ.b - γ.a)) =
            M_d * (γ.b - γ.a) / ((‖w‖ - R) * (2 * Real.pi)) from by field_simp]
        rw [div_lt_one (mul_pos hpos h2pi_pos)]
        linarith [(div_lt_iff₀ h2pi_pos).mp hw]

private lemma windingNumber_zero_of_large_norm (γ : PiecewiseC1Immersion) {R M_d : ℝ}
    (hM_d_nn : 0 ≤ M_d) (hR : ∀ x ∈ γ.toFun '' Icc γ.a γ.b, ‖x‖ ≤ R)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hclosed : γ.toFun γ.a = γ.toFun γ.b)
    {w : ℂ} (hw : R + M_d * (γ.b - γ.a) / (2 * Real.pi) < ‖w‖) :
    generalizedWindingNumber' γ.toFun γ.a γ.b w = 0 := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have h2pi_pos : 0 < 2 * Real.pi := Real.two_pi_pos
  have hR_lt : R < ‖w‖ := by linarith [div_nonneg (mul_nonneg hM_d_nn
    (by linarith : 0 ≤ γ.b - γ.a)) h2pi_pos.le]
  have hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w := fun t ht heq => by
    linarith [hR (γ.toFun t) ⟨t, ht, rfl⟩, heq ▸ hR_lt]
  obtain ⟨n, hn_eq⟩ := windingNumber_integer_of_piecewise_closed_avoiding γ.toFun γ.a γ.b w
    γ.partition γ.hab hclosed γ.continuous_toFun
    (fun t ht hP => γ.smooth_off_partition t (Ioo_subset_Icc_self ht) hP)
    (fun _p1 _p2 _h12 hnoP hsub t ht =>
      (γ.deriv_continuous_off_partition t (hsub ht) (hnoP t ht)).continuousWithinAt)
    hoff ⟨M_d, hM_d⟩
  rw [hn_eq]
  have h_norm_wn : ‖generalizedWindingNumber' γ.toFun γ.a γ.b w‖ < 1 :=
    windingNumber_norm_lt_one γ hR hM_d hoff hR_lt (by linarith)
  rw [hn_eq, Complex.norm_intCast] at h_norm_wn
  have h_abs := abs_lt.mp h_norm_wn
  norm_cast at h_abs ⊢
  omega

private lemma dixonFunction_norm_lt_of_large (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    {R M_f M_d : ℝ} (hM_f_nn : 0 ≤ M_f) (hM_d_nn : 0 ≤ M_d)
    (hR : ∀ x ∈ γ.toFun '' Icc γ.a γ.b, ‖x‖ ≤ R)
    (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    {ε : ℝ} (hε : 0 < ε) {w : ℂ}
    (hw : max (R + M_d * (γ.b - γ.a) / (2 * Real.pi))
              (R + M_f * M_d * (γ.b - γ.a) / ε) < ‖w‖) :
    ‖dixonFunction f U γ w‖ < ε := by
  have hR_lt : R < ‖w‖ := by
    have hnn : 0 ≤ M_d * (γ.b - γ.a) / (2 * Real.pi) :=
      div_nonneg (mul_nonneg hM_d_nn (by linarith [γ.hab])) Real.two_pi_pos.le
    linarith [le_max_left (R + M_d * (γ.b - γ.a) / (2 * Real.pi))
                           (R + M_f * M_d * (γ.b - γ.a) / ε)]
  have hwn_eq_zero : generalizedWindingNumber' γ.toFun γ.a γ.b w = 0 :=
    windingNumber_zero_of_large_norm γ hM_d_nn hR hM_d h_null.closed
      (lt_of_le_of_lt (le_max_left _ _) hw)
  have h_bound_lt_ε : M_f * M_d * (γ.b - γ.a) / (‖w‖ - R) < ε := by
    have hpos : 0 < ‖w‖ - R := by linarith
    rw [div_lt_iff₀ hpos]
    have h_div_lt : M_f * M_d * (γ.b - γ.a) / ε < ‖w‖ - R := by
      linarith [lt_of_le_of_lt (le_max_right _ _) hw]
    linarith [(div_lt_iff₀ hε).mp h_div_lt]
  have hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w := by
    intro t ht heq; linarith [hR (γ.toFun t) ⟨t, ht, rfl⟩, heq ▸ hR_lt]
  by_cases hwin : w ∈ U
  · simp only [dixonFunction, dif_pos hwin]
    rw [dixonH1_eq hU hf γ h_null.image_subset w hoff, hwn_eq_zero]
    simp only [mul_zero, zero_mul, sub_zero]
    exact lt_of_le_of_lt
      (dixonH2_norm_bound γ hM_f_nn hR hM_f hM_d hR_lt) h_bound_lt_ε
  · simp only [dixonFunction, dif_neg hwin]
    exact lt_of_le_of_lt
      (dixonH2_norm_bound γ hM_f_nn hR hM_f hM_d hR_lt) h_bound_lt_ε

theorem dixonFunction_tendsto_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    Tendsto (dixonFunction f U γ) (Filter.cocompact ℂ) (𝓝 0) := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  obtain ⟨R, hR⟩ :=
    (isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isBounded.exists_norm_le
  have hR_nn : 0 ≤ R := le_trans (norm_nonneg _)
    (hR (γ.toFun γ.a) ⟨γ.a, left_mem_Icc.mpr hab, rfl⟩)
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  have hM_d_nn : 0 ≤ M_d := le_trans (norm_nonneg _) (hM_d γ.a (left_mem_Icc.mpr hab))
  have hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b) :=
    hf.continuousOn.comp γ.continuous_toFun fun t ht => h_null.image_subset t ht
  obtain ⟨M_f, hM_f⟩ := isCompact_Icc.exists_bound_of_continuousOn hfγ_cont.norm
  simp only [norm_norm] at hM_f
  have hM_f_nn : 0 ≤ M_f := le_trans (norm_nonneg _) (hM_f γ.a (left_mem_Icc.mpr hab))
  exact zero_at_infty_of_norm_le _ fun ε hε => ⟨_, fun w hw =>
    dixonFunction_norm_lt_of_large hU hf γ h_null hM_f_nn hM_d_nn hR hM_f hM_d hε hw⟩

/-- h ≡ 0 by Liouville's theorem. -/
theorem dixonFunction_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    ∀ w, dixonFunction f U γ w = 0 := fun w =>
  Differentiable.apply_eq_of_tendsto_cocompact
    (dixonFunction_differentiable hU hf γ h_null) w
    (dixonFunction_tendsto_zero hU hf γ h_null)

/-- Cauchy integral formula for null-homologous curves:
∮_γ f(z)/(z-w) dz = 2πi · n(γ,w) · f(w) for w ∈ U off the curve. -/
theorem cauchyIntegralFormula_nullHomologous (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (w : ℂ) (hw : w ∈ U) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    dixonH2 f γ w =
      2 * ↑Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b w * f w := by
  have h_zero := dixonFunction_eq_zero hU hf γ h_null w
  simp only [dixonFunction, dif_pos hw] at h_zero
  have h_eq := dixonH1_eq hU hf γ h_null.image_subset w hoff
  rw [h_zero] at h_eq; linear_combination -h_eq

/-- The image of a piecewise C¹ immersion has empty interior in ℂ.
This follows from the fact that a Lipschitz map from ℝ to ℂ has image with
Hausdorff dimension at most 1, hence Lebesgue measure 0 in ℂ. -/
lemma piecewiseC1_image_interior_empty (γ : PiecewiseC1Immersion) :
    interior (γ.toFun '' Icc γ.a γ.b) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  apply dense_compl_of_dimH_lt_finrank
  have hsplit : γ.toFun '' Icc γ.a γ.b =
      γ.toFun '' (Icc γ.a γ.b \ ↑γ.partition) ∪ γ.toFun '' ↑γ.partition := by
    rw [← Set.image_union]
    congr 1
    exact (Set.sdiff_union_of_subset γ.partition_subset).symm
  rw [hsplit, dimH_union]
  apply max_lt
  · apply lt_of_le_of_lt
    · apply dimH_image_le_of_locally_lipschitzOn
      intro t ⟨ht_Icc, ht_npart⟩
      have ht_Ioo : t ∈ Ioo γ.a γ.b := mem_Ioo_of_notMem_partition γ ht_Icc ht_npart
      have hevt : ∀ᶠ y in 𝓝 t, HasDerivAt γ.toFun (deriv γ.toFun y) y := by
        filter_upwards [(γ.partition.finite_toSet.isClosed.isOpen_compl.inter
          (isOpen_Ioo (a := γ.a) (b := γ.b))).mem_nhds ⟨ht_npart, ht_Ioo⟩]
          with y ⟨hy_compl, hy_Ioo⟩
        exact (γ.smooth_off_partition y (Ioo_subset_Icc_self hy_Ioo) hy_compl).hasDerivAt
      have hstrict : HasStrictDerivAt γ.toFun (deriv γ.toFun t) t :=
        hasStrictDerivAt_of_hasDerivAt_of_continuousAt hevt
          (γ.deriv_continuous_off_partition t ht_Ioo ht_npart)
      obtain ⟨K, v, hv, hLip⟩ := hstrict.hasStrictFDerivAt.exists_lipschitzOnWith
      refine ⟨K, (Icc γ.a γ.b \ ↑γ.partition) ∩ v,
        inter_mem_nhdsWithin _ hv,
        hLip.mono Set.inter_subset_right⟩
    · apply lt_of_le_of_lt (dimH_mono (Set.subset_univ _))
      simp only [Real.dimH_univ]
      rw [Complex.finrank_real_complex]
      norm_cast
  · rw [(γ.partition.finite_toSet.image γ.toFun).dimH_zero]
    rw [Complex.finrank_real_complex]
    norm_cast

theorem contourIntegral_eq_zero_of_nullHomologous (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hU_ne : U.Nonempty := ⟨γ.toFun γ.a, h_null.image_subset γ.a (left_mem_Icc.mpr hab)⟩
  have h_im_int_empty := piecewiseC1_image_interior_empty γ
  obtain ⟨w₀, hw₀U, hw₀_off⟩ : ∃ w₀ ∈ U, w₀ ∉ γ.toFun '' Icc γ.a γ.b := by
    by_contra h; push Not at h
    have : U ⊆ interior (γ.toFun '' Icc γ.a γ.b) := hU.subset_interior_iff.mpr h
    rw [h_im_int_empty] at this
    exact Set.not_nonempty_empty (hU_ne.mono this)
  have hw₀_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w₀ := fun t ht heq =>
    hw₀_off ⟨t, ht, heq⟩
  set F := fun z => f z * (z - w₀) with hF_def
  have hF_diff : DifferentiableOn ℂ F U :=
    hf.mul (differentiableOn_id.sub (differentiableOn_const w₀))
  have h_eq : ∀ t ∈ Set.uIcc γ.a γ.b,
      f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun t) / (γ.toFun t - w₀) * deriv γ.toFun t := by
    intro t ht
    have ht_Icc : t ∈ Icc γ.a γ.b := Set.uIcc_of_le hab ▸ ht
    have hne : γ.toFun t - w₀ ≠ 0 := sub_ne_zero.mpr (hw₀_avoids t ht_Icc)
    simp only [hF_def, mul_div_assoc, div_self hne, mul_one]
  rw [intervalIntegral.integral_congr h_eq]
  have hCIF := cauchyIntegralFormula_nullHomologous hU hF_diff γ h_null w₀ hw₀U hw₀_avoids
  rwa [show F w₀ = 0 from by simp only [hF_def, sub_self, mul_zero], mul_zero] at hCIF

end DixonProof

end
