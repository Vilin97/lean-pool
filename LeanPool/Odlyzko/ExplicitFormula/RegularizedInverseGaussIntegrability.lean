/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedGaussFubini

/-!
# Regularized Inverse Gauss Integrability

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set

namespace NumberField.Odlyzko

/-- A regularized archimedean integrand used in the Odlyzko-bound argument. -/
noncomputable def regularizedArchimedeanIntegrand
    (y δ x : ℝ) : ℝ :=
  (1 - regularizedScaledTartar y δ x) / Real.sinh x

theorem one_sub_regularizedScaledTartar_le_sq
    {δ : ℝ} (hδ : 0 ≤ δ) (y x : ℝ) :
    1 - regularizedScaledTartar y δ x ≤
      (y ^ 2 / 5 + δ) * x ^ 2 := by
  let f := scaledTartarTestFunction y x
  let q := δ * x ^ 2
  have hf1 : f ≤ 1 := tartarTestFunction_le_one _
  have hq0 : 0 ≤ q := mul_nonneg hδ (sq_nonneg x)
  have hexp0 : 0 ≤ 1 - Real.exp (-q) := by simp_all
  have hexp : 1 - Real.exp (-q) ≤ q := by
    have h := Real.add_one_le_exp (-q)
    nlinarith
  have hfexp : f * (1 - Real.exp (-q)) ≤ q := by
    calc
      f * (1 - Real.exp (-q)) ≤ 1 * (1 - Real.exp (-q)) := by
        exact mul_le_mul_of_nonneg_right hf1 hexp0
      _ ≤ q := by grind
  have htartar :
      1 - f ≤ y ^ 2 / 5 * x ^ 2 := by
    dsimp only [f, scaledTartarTestFunction]
    have h := one_sub_tartarTestFunction_le_sq_div_five (y * x)
    nlinarith
  unfold regularizedScaledTartar
  grind

theorem regularizedArchimedeanIntegrand_nonneg
    {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x) (y : ℝ) :
    0 ≤ regularizedArchimedeanIntegrand y δ x := by
  unfold regularizedArchimedeanIntegrand
  exact div_nonneg
    (sub_nonneg.mpr (regularizedScaledTartar_le_one hδ))
    (Real.sinh_pos_iff.mpr hx).le

theorem regularizedArchimedeanIntegrand_le_linear
    {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 < x) (y : ℝ) :
    regularizedArchimedeanIntegrand y δ x ≤
      (y ^ 2 / 5 + δ) * x := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hxs : x ≤ Real.sinh x := Real.self_le_sinh_iff.mpr hx.le
  rw [regularizedArchimedeanIntegrand, div_le_iff₀ hs]
  calc
    1 - regularizedScaledTartar y δ x ≤
        (y ^ 2 / 5 + δ) * x ^ 2 :=
      one_sub_regularizedScaledTartar_le_sq hδ y x
    _ = ((y ^ 2 / 5 + δ) * x) * x := by ring
    _ ≤ ((y ^ 2 / 5 + δ) * x) * Real.sinh x := by
      gcongr

theorem integrableOn_regularizedArchimedeanIntegrand_Ioc_zero_one
    {δ : ℝ} (hδ : 0 ≤ δ) (y : ℝ) :
    IntegrableOn (regularizedArchimedeanIntegrand y δ) (Ioc 0 1) := by
  have hmajor :
      IntegrableOn (fun x : ℝ ↦ (y ^ 2 / 5 + δ) * x) (Ioc 0 1) :=
    (by fun_prop : Continuous (fun x : ℝ ↦
      (y ^ 2 / 5 + δ) * x)).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
  apply Integrable.mono' hmajor
  · unfold regularizedArchimedeanIntegrand
    exact (((measurable_const.sub
      (continuous_regularizedScaledTartar y δ).measurable).div
        Real.continuous_sinh.measurable).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (regularizedArchimedeanIntegrand_nonneg hδ hx.1 y)]
    exact regularizedArchimedeanIntegrand_le_linear hδ hx.1 y

theorem integrableOn_regularizedArchimedeanIntegrand_Ioi_one
    {δ : ℝ} (hδ : 0 ≤ δ) (y : ℝ) :
    IntegrableOn (regularizedArchimedeanIntegrand y δ) (Ioi 1) := by
  have hmajor :
      IntegrableOn (fun x : ℝ ↦ (8 / 3 : ℝ) * Real.exp (-x)) (Ioi 1) :=
    (integrableOn_exp_neg_Ioi 1).const_mul _
  apply Integrable.mono' hmajor
  · unfold regularizedArchimedeanIntegrand
    exact (((measurable_const.sub
      (continuous_regularizedScaledTartar y δ).measurable).div
        Real.continuous_sinh.measurable).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (regularizedArchimedeanIntegrand_nonneg hδ hx0 y)]
    calc
      regularizedArchimedeanIntegrand y δ x ≤
          1 / Real.sinh x := by
        unfold regularizedArchimedeanIntegrand
        exact div_le_div_of_nonneg_right
          (sub_le_self _ (regularizedScaledTartar_nonneg y δ x))
          (Real.sinh_pos_iff.mpr hx0).le
      _ ≤ (8 / 3 : ℝ) * Real.exp (-x) :=
        one_div_sinh_le_exp_tail hx.le

theorem integrableOn_regularizedArchimedeanIntegrand_Ioi
    {δ : ℝ} (hδ : 0 ≤ δ) (y : ℝ) :
    IntegrableOn (regularizedArchimedeanIntegrand y δ) (Ioi 0) := by
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by simp
  rw [← hunion]
  exact
    (integrableOn_regularizedArchimedeanIntegrand_Ioc_zero_one hδ y).union
      (integrableOn_regularizedArchimedeanIntegrand_Ioi_one hδ y)

end NumberField.Odlyzko
