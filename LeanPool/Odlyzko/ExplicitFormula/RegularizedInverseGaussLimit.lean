/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedInverseGaussIntegrability

/-!
# Regularized Inverse Gauss Limit

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A regularized archimedean majorant used in the Odlyzko-bound argument. -/
noncomputable def regularizedArchimedeanMajorant
    (y x : ℝ) : ℝ :=
  if x ≤ 1 then (y ^ 2 / 5 + 1) * x
  else (8 / 3 : ℝ) * Real.exp (-x)

theorem integrableOn_regularizedArchimedeanMajorant_Ioi
    (y : ℝ) :
    IntegrableOn (regularizedArchimedeanMajorant y) (Ioi 0) := by
  have hnear :
      IntegrableOn (regularizedArchimedeanMajorant y) (Ioc 0 1) := by
    have hlin :
        IntegrableOn (fun x : ℝ ↦ (y ^ 2 / 5 + 1) * x) (Ioc 0 1) :=
      (by fun_prop : Continuous (fun x : ℝ ↦
        (y ^ 2 / 5 + 1) * x)).integrableOn_Icc.mono_set
          Ioc_subset_Icc_self
    apply hlin.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    simp [regularizedArchimedeanMajorant, hx.2]
  have htail :
      IntegrableOn (regularizedArchimedeanMajorant y) (Ioi 1) := by
    have hexp :
        IntegrableOn
          (fun x : ℝ ↦ (8 / 3 : ℝ) * Real.exp (-x)) (Ioi 1) :=
      (integrableOn_exp_neg_Ioi 1).const_mul _
    apply hexp.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    simp [regularizedArchimedeanMajorant, not_le_of_gt hx]
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by simp
  rw [← hunion]
  exact hnear.union htail

theorem norm_regularizedArchimedeanIntegrand_le_majorant
    {δ x : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : 0 < x) (y : ℝ) :
    ‖regularizedArchimedeanIntegrand y δ x‖ ≤
      regularizedArchimedeanMajorant y x := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg (regularizedArchimedeanIntegrand_nonneg hδ hx y)]
  by_cases hx1 : x ≤ 1
  · rw [regularizedArchimedeanMajorant, if_pos hx1]
    exact
      (regularizedArchimedeanIntegrand_le_linear hδ hx y).trans
        (mul_le_mul_of_nonneg_right
          (by linarith : y ^ 2 / 5 + δ ≤ y ^ 2 / 5 + 1) hx.le)
  · rw [regularizedArchimedeanMajorant, if_neg hx1]
    have hxone : 1 ≤ x := le_of_not_ge hx1
    calc
      regularizedArchimedeanIntegrand y δ x ≤
          1 / Real.sinh x := by
        unfold regularizedArchimedeanIntegrand
        exact div_le_div_of_nonneg_right
          (sub_le_self _ (regularizedScaledTartar_nonneg y δ x))
          (Real.sinh_pos_iff.mpr hx).le
      _ ≤ (8 / 3 : ℝ) * Real.exp (-x) :=
        one_div_sinh_le_exp_tail hxone

theorem tendsto_integral_regularizedArchimedeanIntegrand_nhdsGT_zero
    (y : ℝ) :
    Tendsto
      (fun δ : ℝ ↦
        ∫ x : ℝ in Ioi 0,
          regularizedArchimedeanIntegrand y δ x)
      (𝓝[>] 0)
      (𝓝 (archimedeanIntegral y)) := by
  unfold archimedeanIntegral
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := regularizedArchimedeanMajorant y)
  · filter_upwards [] with δ
    unfold regularizedArchimedeanIntegrand
    exact (((measurable_const.sub
      (continuous_regularizedScaledTartar y δ).measurable).div
        Real.continuous_sinh.measurable).aestronglyMeasurable)
  · have hlt :
        ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 :=
      Filter.Eventually.filter_mono inf_le_left
        (Iio_mem_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin, hlt] with δ hδ hδ1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_regularizedArchimedeanIntegrand_le_majorant
      hδ.le hδ1.le hx y
  · exact integrableOn_regularizedArchimedeanMajorant_Ioi y
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    unfold regularizedArchimedeanIntegrand archimedeanIntegrand
    simpa [scaledTartarTestFunction] using
      tendsto_nhdsWithin_of_tendsto_nhds
        ((tendsto_const_nhds.sub
          (tendsto_regularizedScaledTartar_nhds_zero y x))
        |>.div_const (Real.sinh x))

theorem tendsto_integral_inverseGaussKernel_regularizedScaledTartar_nhdsGT_zero
    (y : ℝ) :
    Tendsto
      (fun δ : ℝ ↦
        ∫ x : ℝ in Ioi 0,
          inverseGaussKernel (regularizedScaledTartar y δ) x)
      (𝓝[>] 0)
      (𝓝 (archimedeanIntegral y - Real.log 2)) := by
  have harch :=
    tendsto_integral_regularizedArchimedeanIntegrand_nhdsGT_zero y
  apply harch.sub_const (Real.log 2) |>.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [← integral_fermiDiracKernel,
    ← integral_sub
      (integrableOn_regularizedArchimedeanIntegrand_Ioi hδ.le y)
      integrableOn_fermiDiracKernel_Ioi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (inverseGaussKernel_eq hx).symm

end NumberField.Odlyzko
