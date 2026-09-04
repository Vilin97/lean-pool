/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.Lemma43
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Density identification for the local transfer step

This file connects the pushforward laws `zPlusLaw` and `zMinusLaw` to the
convolution densities `LikelihoodRatio.fPlus` and `fMinus`.
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace Feige

namespace Lemma43Density

open TransferStein ProbabilityTheory

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- Rate-one exponential integration in the `ENNReal` form used by the
likelihood-ratio convolution densities. -/
theorem lintegral_expMeasure_one_eq
    {g : ℝ → ENNReal} (hg : Measurable g) :
    (∫⁻ s, g s ∂expMeasure 1) =
      ∫⁻ s in Ici 0, g s * LikelihoodRatio.expWeight s := by
  have hpdf : Measurable (gammaPDF 1 1) := by
    unfold gammaPDF
    exact (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul volume hpdf hg]
  rw [← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro s
  by_cases hs : 0 ≤ s
  · simp [gammaPDF, gammaPDFReal, hs, LikelihoodRatio.expWeight,
      mul_comm]
  · simp [gammaPDF, gammaPDFReal, hs, LikelihoodRatio.expWeight]

/-- Nonnegative test functions under `Z₊ = Y + aE` can be integrated
against the explicit convolution density `fPlus`. -/
theorem lintegral_zPlusLaw_eq_fPlus
    {f h : ℝ → ENNReal} (hf : Measurable f) (hh : Measurable h)
    (a : ℝ) :
    (∫⁻ z, h z ∂zPlusLaw (volume.withDensity f) a) =
      ∫⁻ x, LikelihoodRatio.fPlus f a x * h x ∂volume := by
  rw [zPlusLaw, lintegral_map' hh.aemeasurable
    (measurable_zPlusMap a).aemeasurable]
  rw [lintegral_prod _ (by fun_prop)]
  · rw [lintegral_withDensity_eq_lintegral_mul volume hf
      (by
        have hjoint : Measurable (fun p : ℝ × ℝ ↦
            h (p.1 + a * p.2)) := by fun_prop
        exact hjoint.lintegral_prod_right')]
    calc
      (∫⁻ y, f y * ∫⁻ s, h (y + a * s) ∂expMeasure 1 ∂volume) =
          ∫⁻ y, ∫⁻ s, f y * h (y + a * s)
            ∂expMeasure 1 ∂volume := by
        apply lintegral_congr
        intro y
        rw [lintegral_const_mul]
        fun_prop
      _ = ∫⁻ s, ∫⁻ y, f y * h (y + a * s)
            ∂volume ∂expMeasure 1 := by
        rw [lintegral_lintegral_swap]
        fun_prop
      _ = ∫⁻ s, ∫⁻ x, f (x - a * s) * h x
            ∂volume ∂expMeasure 1 := by
        apply lintegral_congr
        intro s
        let k : ℝ → ENNReal := fun x ↦ f (x - a * s) * h x
        calc
          (∫⁻ y, f y * h (y + a * s)) =
              ∫⁻ y, k (y + a * s) := by
            apply lintegral_congr
            intro y
            simp only [k]
            congr 2; ring
          _ = ∫⁻ x, k x :=
            lintegral_add_right_eq_self (μ := volume) k (a * s)
          _ = ∫⁻ x, f (x - a * s) * h x := rfl
      _ = ∫⁻ x, (∫⁻ s, f (x - a * s) ∂expMeasure 1) * h x
            ∂volume := by
        rw [lintegral_lintegral_swap]
        · apply lintegral_congr
          intro x
          rw [lintegral_mul_const]
          fun_prop
        · fun_prop
      _ = ∫⁻ x, LikelihoodRatio.fPlus f a x * h x ∂volume := by
        apply lintegral_congr
        intro x
        rw [lintegral_expMeasure_one_eq]
        · rfl
        · fun_prop
/-- The pushforward law of a positive exponential shift has density
`LikelihoodRatio.fPlus`. -/
theorem zPlusLaw_eq_withDensity_fPlus
    {f : ℝ → ENNReal} (hf : Measurable f) (a : ℝ) :
    zPlusLaw (volume.withDensity f) a =
      volume.withDensity (LikelihoodRatio.fPlus f a) := by
  ext B hB
  rw [withDensity_apply _ hB]
  rw [show zPlusLaw (volume.withDensity f) a B =
      ∫⁻ z, B.indicator (fun _ ↦ (1 : ENNReal)) z
        ∂zPlusLaw (volume.withDensity f) a by
          symm
          exact lintegral_indicator_one hB]
  rw [lintegral_zPlusLaw_eq_fPlus hf (measurable_const.indicator hB) a]
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ B <;> simp [hx]

/-- Nonnegative test functions under `Z₋ = Y - bE` can be integrated
against the explicit convolution density `fMinus`. -/
theorem lintegral_zMinusLaw_eq_fMinus
    {f h : ℝ → ENNReal} (hf : Measurable f) (hh : Measurable h)
    (b : ℝ) :
    (∫⁻ z, h z ∂zMinusLaw (volume.withDensity f) b) =
      ∫⁻ x, LikelihoodRatio.fMinus f b x * h x ∂volume := by
  rw [zMinusLaw, lintegral_map' hh.aemeasurable
    (measurable_zMinusMap b).aemeasurable]
  rw [lintegral_prod _ (by fun_prop)]
  · rw [lintegral_withDensity_eq_lintegral_mul volume hf
      (by
        have hjoint : Measurable (fun p : ℝ × ℝ ↦
            h (p.1 - b * p.2)) := by fun_prop
        exact hjoint.lintegral_prod_right')]
    calc
      (∫⁻ y, f y * ∫⁻ s, h (y - b * s) ∂expMeasure 1 ∂volume) =
          ∫⁻ y, ∫⁻ s, f y * h (y - b * s)
            ∂expMeasure 1 ∂volume := by
        apply lintegral_congr
        intro y
        rw [lintegral_const_mul]
        fun_prop
      _ = ∫⁻ s, ∫⁻ y, f y * h (y - b * s)
            ∂volume ∂expMeasure 1 := by
        rw [lintegral_lintegral_swap]
        fun_prop
      _ = ∫⁻ s, ∫⁻ x, f (x + b * s) * h x
            ∂volume ∂expMeasure 1 := by
        apply lintegral_congr
        intro s
        let k : ℝ → ENNReal := fun x ↦ f (x + b * s) * h x
        calc
          (∫⁻ y, f y * h (y - b * s)) =
              ∫⁻ y, k (y + (-b * s)) := by
            apply lintegral_congr
            intro y
            simp only [k]
            congr 2 <;> ring
          _ = ∫⁻ x, k x :=
            lintegral_add_right_eq_self (μ := volume) k (-b * s)
          _ = ∫⁻ x, f (x + b * s) * h x := rfl
      _ = ∫⁻ x, (∫⁻ s, f (x + b * s) ∂expMeasure 1) * h x
            ∂volume := by
        rw [lintegral_lintegral_swap]
        · apply lintegral_congr
          intro x
          rw [lintegral_mul_const]
          fun_prop
        · fun_prop
      _ = ∫⁻ x, LikelihoodRatio.fMinus f b x * h x ∂volume := by
        apply lintegral_congr
        intro x
        rw [lintegral_expMeasure_one_eq]
        · rfl
        · fun_prop

/-- The pushforward law of a negative exponential shift has density
`LikelihoodRatio.fMinus`. -/
theorem zMinusLaw_eq_withDensity_fMinus
    {f : ℝ → ENNReal} (hf : Measurable f) (b : ℝ) :
    zMinusLaw (volume.withDensity f) b =
      volume.withDensity (LikelihoodRatio.fMinus f b) := by
  ext B hB
  rw [withDensity_apply _ hB]
  rw [show zMinusLaw (volume.withDensity f) b B =
      ∫⁻ z, B.indicator (fun _ ↦ (1 : ENNReal)) z
        ∂zMinusLaw (volume.withDensity f) b by
          symm
          exact lintegral_indicator_one hB]
  rw [lintegral_zMinusLaw_eq_fMinus hf (measurable_const.indicator hB) b]
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ B <;> simp [hx]

/-- For a finite measure presented by a density, the actual upper-tail
probability used by `Lemma43` is its `uIntegral`. -/
theorem ofReal_u_withDensity_eq_uIntegral
    {g : ℝ → ENNReal} (hg : Measurable g)
    [IsFiniteMeasure (volume.withDensity g)]
    {d : ℝ} (hd : 0 < d) :
    ENNReal.ofReal (Lemma43.u (volume.withDensity g) d) =
      LikelihoodRatio.uIntegral g d := by
  rw [Lemma43.u, uProbability_eq_integral _ hd]
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_uTailIntegrand (volume.withDensity g) hd)
    (Filter.Eventually.of_forall (uTailIntegrand_nonneg d))]
  rw [lintegral_withDensity_eq_lintegral_mul volume hg
    ((measurable_uTailIntegrand d).ennreal_ofReal)]
  unfold LikelihoodRatio.uIntegral
  rw [← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro x
  by_cases hx : 0 ≤ x
  · simp [uTailIntegrand, hx]
  · simp [uTailIntegrand, hx]

/-- The analogous density identification for the lower-tail probability. -/
theorem ofReal_v_withDensity_eq_vIntegral
    {g : ℝ → ENNReal} (hg : Measurable g)
    [IsFiniteMeasure (volume.withDensity g)]
    {c : ℝ} (hc : 0 < c) :
    ENNReal.ofReal (Lemma43.v (volume.withDensity g) c) =
      LikelihoodRatio.vIntegral g c := by
  rw [Lemma43.v, vProbability_eq_integral _ hc]
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_vTailIntegrand (volume.withDensity g) hc)
    (Filter.Eventually.of_forall (vTailIntegrand_nonneg c))]
  rw [lintegral_withDensity_eq_lintegral_mul volume hg
    ((measurable_vTailIntegrand c).ennreal_ofReal)]
  unfold LikelihoodRatio.vIntegral
  rw [← lintegral_indicator measurableSet_Iio]
  apply lintegral_congr
  intro x
  by_cases hx : x < 0
  · simp [vTailIntegrand, hx]
  · simp [vTailIntegrand, hx]

/-- The four density identifications required by `Lemma43` are automatic for
the actual positive and negative exponential-shift laws of a density. -/
theorem densityIdentification_zPlus_zMinus
    {f : ℝ → ENNReal} (hf : Measurable f)
    [IsFiniteMeasure (volume.withDensity f)]
    {a b c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Lemma43.DensityIdentification f
      (zPlusLaw (volume.withDensity f) a)
      (zMinusLaw (volume.withDensity f) b) a b c d := by
  have hP := zPlusLaw_eq_withDensity_fPlus hf a
  have hM := zMinusLaw_eq_withDensity_fMinus hf b
  let : IsFiniteMeasure
      (volume.withDensity (LikelihoodRatio.fPlus f a)) :=
    ⟨by rw [← hP]; exact measure_lt_top _ _⟩
  let : IsFiniteMeasure
      (volume.withDensity (LikelihoodRatio.fMinus f b)) :=
    ⟨by rw [← hM]; exact measure_lt_top _ _⟩
  constructor
  · rw [hP]
    exact ofReal_u_withDensity_eq_uIntegral
      (LikelihoodRatio.measurable_fPlus hf a) hd
  constructor
  · rw [hM]
    exact ofReal_u_withDensity_eq_uIntegral
      (LikelihoodRatio.measurable_fMinus hf b) hd
  constructor
  · rw [hP]
    exact ofReal_v_withDensity_eq_vIntegral
      (LikelihoodRatio.measurable_fPlus hf a) hc
  · rw [hM]
    exact ofReal_v_withDensity_eq_vIntegral
      (LikelihoodRatio.measurable_fMinus hf b) hc

/-- Consequently, the likelihood-ratio order of the two actual shifted laws
needs no separate density-identification hypothesis. -/
theorem theta_order_zPlus_zMinus
    {f : ℝ → ENNReal} (hf : Measurable f)
    (hflc : LikelihoodRatio.FourPointLogConcave f)
    [IsProbabilityMeasure (volume.withDensity f)]
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d) :
    Lemma43.theta (zMinusLaw (volume.withDensity f) b) c d ≤
      Lemma43.theta (zPlusLaw (volume.withDensity f) a) c d := by
  let : IsProbabilityMeasure
      (zPlusLaw (volume.withDensity f) a) := by
    constructor
    rw [zPlusLaw, Measure.map_apply (measurable_zPlusMap a)
      MeasurableSet.univ]
    simp
  let : IsProbabilityMeasure
      (zMinusLaw (volume.withDensity f) b) := by
    constructor
    rw [zMinusLaw, Measure.map_apply (measurable_zMinusMap b)
      MeasurableSet.univ]
    simp
  exact Lemma43.theta_order hf hflc _ _ ha hb hc hd
    (densityIdentification_zPlus_zMinus hf hc hd)

end Lemma43Density

end Feige
