/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarFourier
public import LeanPool.Odlyzko.ExplicitFormula.TartarPoitouPositivity

/-!
# Regularized Poitou Positivity

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Asymptotics Complex Filter MeasureTheory Real Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A regularized poitou critical strip majorant used in the Odlyzko-bound argument. -/
noncomputable def regularizedPoitouCriticalStripMajorant
    (δ x : ℝ) : ℝ :=
  Real.exp ((1 / 2 : ℝ) ^ 2 / (2 * δ)) *
    Real.exp (-(δ / 2) * x ^ 2)

private theorem regularizedPoitouCriticalStripMajorant_integrable
    {δ : ℝ} (hδ : 0 < δ) :
    Integrable (regularizedPoitouCriticalStripMajorant δ) := by
  exact (integrable_exp_neg_mul_sq (half_pos hδ)).const_mul _

theorem norm_poitouTransformIntegrand_regularized_le_criticalStripMajorant
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {s : ℂ}
    (hs : s ∈ poitouClosedCriticalStrip) (x : ℝ) :
    ‖poitouTransformIntegrand (regularizedScaledTartar y δ) s x‖ ≤
      regularizedPoitouCriticalStripMajorant δ x := by
  refine (norm_poitouTransformIntegrand_regularizedScaledTartar_le
    hδ s x).trans ?_
  unfold regularizedPoitouCriticalStripMajorant
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right
    · have habs : |s.re - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]
        constructor <;> linarith [hs.1, hs.2]
      exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 habs
    · positivity
  · exact (Real.exp_pos _).le

theorem norm_poitouTransform_regularized_le_criticalStripIntegral
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {s : ℂ}
    (hs : s ∈ poitouClosedCriticalStrip) :
    ‖poitouTransform (regularizedScaledTartar y δ) s‖ ≤
      ∫ x : ℝ, regularizedPoitouCriticalStripMajorant δ x := by
  rw [poitouTransform]
  apply norm_integral_le_of_norm_le
    (regularizedPoitouCriticalStripMajorant_integrable hδ)
  filter_upwards [] with x
  exact norm_poitouTransformIntegrand_regularized_le_criticalStripMajorant
    hδ y hs x

theorem diffContOnCl_poitouTransform_regularized
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    DiffContOnCl ℂ (poitouTransform (regularizedScaledTartar y δ))
      poitouCriticalStrip := by
  have han :=
    analyticOnNhd_poitouTransform_regularizedScaledTartar
      (y := y) hδ
  constructor
  · intro s hs
    exact (han s (mem_univ s)).differentiableAt.differentiableWithinAt
  · exact han.continuousOn.mono (subset_univ _)

/-- A negative exp regularized poitou transform used in the Odlyzko-bound argument. -/
noncomputable def negativeExpRegularizedPoitouTransform
    (y δ : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-poitouTransform (regularizedScaledTartar y δ) s)

theorem diffContOnCl_negativeExpRegularizedPoitouTransform
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    DiffContOnCl ℂ (negativeExpRegularizedPoitouTransform y δ)
      poitouCriticalStrip := by
  let h := (diffContOnCl_poitouTransform_regularized hδ y).neg
  constructor
  · intro s hs
    exact (h.differentiableOn s hs).cexp
  · exact Complex.continuous_exp.continuousOn.comp h.continuousOn
      (fun _ _ ↦ mem_univ _)

theorem norm_negativeExpRegularizedPoitouTransform_le
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) {s : ℂ}
    (hs : s ∈ poitouClosedCriticalStrip) :
    ‖negativeExpRegularizedPoitouTransform y δ s‖ ≤
      Real.exp
        (∫ x : ℝ, regularizedPoitouCriticalStripMajorant δ x) := by
  rw [negativeExpRegularizedPoitouTransform, Complex.norm_exp, neg_re]
  apply Real.exp_le_exp.mpr
  calc
    -(poitouTransform (regularizedScaledTartar y δ) s).re ≤
        |(poitouTransform (regularizedScaledTartar y δ) s).re| :=
      neg_le_abs _
    _ ≤ ‖poitouTransform (regularizedScaledTartar y δ) s‖ :=
      Complex.abs_re_le_norm _
    _ ≤ _ :=
      norm_poitouTransform_regularized_le_criticalStripIntegral hδ y hs

theorem negativeExpRegularizedPoitouTransform_growth
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    ∃ c < Real.pi / (1 - 0), ∃ B,
      negativeExpRegularizedPoitouTransform y δ
        =O[comap (_root_.abs ∘ im) atTop ⊓
          𝓟 (re ⁻¹' Ioo (0 : ℝ) 1)]
        fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
  refine ⟨0, by positivity, 0, ?_⟩
  apply IsBigO.of_bound
    (Real.exp
      (∫ x : ℝ, regularizedPoitouCriticalStripMajorant δ x))
  apply eventually_inf_principal.2
  filter_upwards [] with s hs
  have hs' : s ∈ poitouClosedCriticalStrip := ⟨hs.1.le, hs.2.le⟩
  simpa using
    norm_negativeExpRegularizedPoitouTransform_le hδ y hs'

theorem norm_negativeExpRegularizedPoitouTransform_le_one_of_re_zero
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) {s : ℂ}
    (hs : s.re = 0) :
    ‖negativeExpRegularizedPoitouTransform y δ s‖ ≤ 1 := by
  have heq : s = (s.im : ℂ) * I := by
    apply Complex.ext
    · simp [hs]
    · simp
  rw [negativeExpRegularizedPoitouTransform, Complex.norm_exp,
    neg_re, Real.exp_le_one_iff, heq]
  exact neg_nonpos.mpr (re_poitouTransform_mul_I_nonneg
    (regularizedScaledTartar_poitouAdmissible hy hδ) s.im
    (poitouTransformIntegrand_regularizedScaledTartar_integrable
      hδ (s.im * I)))

theorem norm_negativeExpRegularizedPoitouTransform_le_one_of_re_one
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) {s : ℂ}
    (hs : s.re = 1) :
    ‖negativeExpRegularizedPoitouTransform y δ s‖ ≤ 1 := by
  have heq : s = 1 + (s.im : ℂ) * I := by
    apply Complex.ext
    · simp [hs]
    · simp
  rw [negativeExpRegularizedPoitouTransform, Complex.norm_exp,
    neg_re, Real.exp_le_one_iff, heq]
  exact neg_nonpos.mpr (re_poitouTransform_one_add_mul_I_nonneg
    (regularizedScaledTartar_poitouAdmissible hy hδ) s.im
    (poitouTransformIntegrand_regularizedScaledTartar_integrable
      hδ (((-s.im : ℝ) : ℂ) * I)))

theorem re_poitouTransform_regularizedScaledTartar_nonneg
    {y δ : ℝ} (hy : y ≠ 0) (hδ : 0 < δ) {s : ℂ}
    (hs : s ∈ poitouClosedCriticalStrip) :
    0 ≤ (poitouTransform (regularizedScaledTartar y δ) s).re := by
  have hnorm :
      ‖negativeExpRegularizedPoitouTransform y δ s‖ ≤ 1 :=
    PhragmenLindelof.vertical_strip
      (a := 0) (b := 1) (C := 1)
      (diffContOnCl_negativeExpRegularizedPoitouTransform hδ y)
      (negativeExpRegularizedPoitouTransform_growth hδ y)
      (fun z hz ↦
        norm_negativeExpRegularizedPoitouTransform_le_one_of_re_zero
          hy hδ hz)
      (fun z hz ↦
        norm_negativeExpRegularizedPoitouTransform_le_one_of_re_one
          hy hδ hz)
      hs.1 hs.2
  rw [negativeExpRegularizedPoitouTransform, Complex.norm_exp,
    Real.exp_le_one_iff] at hnorm
  simp_all

end NumberField.Odlyzko
