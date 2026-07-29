/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedGaussFubini
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedPoitouSqrtWeightedIntegrable

/-!
# Regularized Gauss Full Fubini

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

private theorem integrableOn_four_div_sqrt_Ioc :
    IntegrableOn (fun x : ℝ ↦ 4 / Real.sqrt x) (Ioc 0 1) := by
  have hp :
      IntegrableOn (fun x : ℝ ↦ 4 * x ^ (-(1 : ℝ) / 2)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
      (by norm_num)).const_mul 4
  have hp' :
      IntegrableOn (fun x : ℝ ↦ 4 * x ^ (-(1 : ℝ) / 2)) (Ioc 0 1) :=
    hp.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  apply hp'.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have he : (-(1 : ℝ) / 2) = -(1 / 2) := by ring
  rw [Real.sqrt_eq_rpow, he, Real.rpow_neg hx.1.le]
  ring

private theorem norm_regularizedPoitou_mul_gauss_le_sqrt_product
    {δ : ℝ} (y σ t : ℝ) {x : ℝ}
    (hσ : 0 ≤ σ) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        gaussDigammaIntegrand (σ + t * I) x‖ ≤
      (Real.sqrt (|σ - 1| + |t|) *
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖) *
      (4 / Real.sqrt x) := by
  have hnorm :
      ‖(σ : ℂ) + t * I - 1‖ ≤ |σ - 1| + |t| := by
    rw [show (σ : ℂ) + t * I - 1 =
        ((σ - 1 : ℝ) : ℂ) + (t : ℂ) * I by
      push_cast
      ring]
    calc
      ‖((σ - 1 : ℝ) : ℂ) + (t : ℂ) * I‖ ≤
          ‖((σ - 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ :=
        norm_add_le _ _
      _ = |σ - 1| + |t| := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hsqrt :
      Real.sqrt (‖(σ : ℂ) + t * I - 1‖ / x) ≤
        Real.sqrt (|σ - 1| + |t|) / Real.sqrt x := by
    rw [Real.sqrt_div (norm_nonneg _)]
    exact div_le_div_of_nonneg_right
      (Real.sqrt_le_sqrt hnorm) (Real.sqrt_nonneg _)
  rw [norm_mul]
  calc
    ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ *
        ‖gaussDigammaIntegrand (σ + t * I) x‖ ≤
      ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ *
        (4 * Real.sqrt (‖(σ : ℂ) + t * I - 1‖ / x)) := by
      gcongr
      exact norm_gaussDigammaIntegrand_vertical_le_sqrt hσ hx hx1
    _ ≤
      ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ *
        (4 * (Real.sqrt (|σ - 1| + |t|) / Real.sqrt x)) := by
      gcongr
    _ = _ := by ring

private theorem integrableOn_gaussDigammaVerticalTailMajorant
    {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (gaussDigammaVerticalMajorant σ) (Ioi 1) := by
  let C : ℝ := (1 - Real.exp (-1))⁻¹
  have hfirst :
      IntegrableOn (fun x : ℝ ↦ Real.exp (-x)) (Ioi 1) := by
    simpa only [neg_mul, one_mul] using
      (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 1)
  have hsecond :
      IntegrableOn (fun x : ℝ ↦ Real.exp (-σ * x)) (Ioi 1) :=
    integrableOn_exp_mul_Ioi (by linarith) 1
  have hmajor :
      IntegrableOn
        (fun x : ℝ ↦ C * (Real.exp (-x) + Real.exp (-σ * x)))
        (Ioi 1) :=
    (hfirst.add hsecond).const_mul C
  apply hmajor.mono'
  · change AEStronglyMeasurable
      (fun x : ℝ ↦
        (Real.exp (-x) + Real.exp (-σ * x)) /
          (1 - Real.exp (-x)))
      (volume.restrict (Ioi 1))
    exact (by measurability : Measurable (fun x : ℝ ↦
      (Real.exp (-x) + Real.exp (-σ * x)) /
        (1 - Real.exp (-x)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    change
      ‖(Real.exp (-x) + Real.exp (-σ * x)) /
          (1 - Real.exp (-x))‖ ≤
        C * (Real.exp (-x) + Real.exp (-σ * x))
    rw [Real.norm_eq_abs]
    have hxpos : 0 < x := zero_lt_one.trans hx
    have hdenPos : 0 < 1 - Real.exp (-x) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hxpos))
    have hnumNonneg :
        0 ≤ Real.exp (-x) + Real.exp (-σ * x) := by positivity
    rw [abs_of_nonneg (div_nonneg hnumNonneg hdenPos.le)]
    change
      (Real.exp (-x) + Real.exp (-σ * x)) /
          (1 - Real.exp (-x)) ≤
      C * (Real.exp (-x) + Real.exp (-σ * x))
    dsimp only [C]
    rw [← div_eq_inv_mul]
    exact div_le_div_of_nonneg_left hnumNonneg
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
      (by
        gcongr)

theorem integrableOn_uncurry_poitouTransform_regularized_mul_gaussDigammaIntegrand_Ioi
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable
      (Function.uncurry fun t x : ℝ ↦
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          gaussDigammaIntegrand (σ + t * I) x)
      (volume.prod (volume.restrict (Ioi 0))) := by
  let F : ℝ × ℝ → ℂ := Function.uncurry fun t x : ℝ ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
      gaussDigammaIntegrand (σ + t * I) x
  have hΦcont : Continuous (fun t : ℝ ↦
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hin : ContinuousAt
        (fun u : ℝ ↦ (σ : ℂ) + u * I) t := by fun_prop
    have hout :
        ContinuousAt
          (poitouTransform (regularizedScaledTartar y δ))
          (σ + t * I) :=
      (analyticOnNhd_poitouTransform_regularizedScaledTartar
        hδ (σ + t * I) (mem_univ _)).continuousAt
    simpa only [ContinuousAt, Function.comp_def] using
      Filter.Tendsto.comp hout hin
  have hmeas : Measurable F := by
    unfold F Function.uncurry gaussDigammaIntegrand
    apply Measurable.mul
    · exact hΦcont.measurable.comp measurable_fst
    · measurability
  have hnear :
      Integrable F
        (volume.prod (volume.restrict (Ioc 0 1))) := by
    have ht :=
      integrable_sqrt_add_abs_mul_norm_poitouTransform_regularized
        hδ y σ
    have hx := integrableOn_four_div_sqrt_Ioc
    have hmajor :=
      ht.mul_prod hx
    apply hmajor.mono' hmeas.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hmeas.norm (by
        apply Measurable.mul
        · apply Measurable.mul
          · measurability
          · exact (hΦcont.measurable.comp measurable_fst).norm
        · measurability))).2
    filter_upwards [] with t
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact norm_regularizedPoitou_mul_gauss_le_sqrt_product
      y σ t hσ.le hx.1 hx.2
  have htail :
      Integrable F
        (volume.prod (volume.restrict (Ioi 1))) := by
    have ht :=
      (poitouTransform_regularizedScaledTartar_vertical_integrable
        hδ y σ).norm
    have hx := integrableOn_gaussDigammaVerticalTailMajorant hσ
    have hmajor := ht.mul_prod hx
    apply hmajor.mono' hmeas.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hmeas.norm (by
        apply Measurable.mul
        · exact (hΦcont.measurable.comp measurable_fst).norm
        · unfold gaussDigammaVerticalMajorant
          measurability))).2
    filter_upwards [] with t
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change
      ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          gaussDigammaIntegrand (σ + t * I) x‖ ≤
        ‖poitouTransform (regularizedScaledTartar y δ) (σ + t * I)‖ *
          gaussDigammaVerticalMajorant σ x
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact norm_gaussDigammaIntegrand_vertical_le
      σ t (zero_lt_one.trans hx)
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by simp
  have hdisjoint : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
    Set.disjoint_left.2 fun _ hx hy ↦ (not_lt_of_ge hx.2) hy
  have hmeasure :
      volume.restrict (Ioi (0 : ℝ)) =
        volume.restrict (Ioc 0 1) + volume.restrict (Ioi 1) := by
    rw [← hunion, Measure.restrict_union hdisjoint measurableSet_Ioi]
  rw [hmeasure, Measure.prod_add]
  exact hnear.add_measure htail

theorem integral_poitouTransform_regularized_mul_integral_gaussDigammaIntegrand_Ioi
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ t : ℝ,
      poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
        ∫ x : ℝ in Ioi 0,
          gaussDigammaIntegrand (σ + t * I) x) =
      ∫ x : ℝ in Ioi 0,
        ((2 * Real.pi *
          inverseGaussKernel (regularizedScaledTartar y δ) x : ℝ) : ℂ) := by
  let F : ℝ → ℝ → ℂ := fun t x ↦
    poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
      gaussDigammaIntegrand (σ + t * I) x
  have hdouble :=
    integrableOn_uncurry_poitouTransform_regularized_mul_gaussDigammaIntegrand_Ioi
      hδ y hσ
  calc
    _ = ∫ t : ℝ, ∫ x : ℝ in Ioi 0, F t x := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [integral_const_mul]
    _ = ∫ x : ℝ in Ioi 0, ∫ t : ℝ, F t x := by
      exact integral_integral_swap hdouble
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact
        integral_poitouTransform_regularized_mul_gaussDigammaIntegrand
          hδ y σ hx

end NumberField.Odlyzko
