/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GaussDigammaIntegral

/-!
# Gauss Digamma Bounds

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Real Set

namespace NumberField.Odlyzko

theorem half_mul_le_one_sub_exp_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hexp : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have hpos : 0 < x + 1 := by linarith
  have hinv : (Real.exp x)⁻¹ ≤ (x + 1)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) hpos).mpr hexp
  have hrec : (x + 1)⁻¹ ≤ 1 - x / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  rw [Real.exp_neg]
  linarith

theorem norm_gaussDigammaIntegrand_le_local
    (s : ℂ) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hsx : ‖s - 1‖ * x ≤ 1) :
    ‖gaussDigammaIntegrand s x‖ ≤ 4 * ‖s - 1‖ := by
  have hdenPos : 0 < 1 - Real.exp (-x) := by simp_all
  have hden :
      ‖(1 : ℂ) - Complex.exp (-x)‖ =
        1 - Real.exp (-x) := by
    rw [show Complex.exp (-x) = (Real.exp (-x) : ℝ) by
      simp]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdenPos]
  have hfactor :
      Complex.exp (-x) - Complex.exp (-s * x) =
        Complex.exp (-x) *
          (1 - Complex.exp (-(s - 1) * x)) := by
    have hexp :
        Complex.exp (-s * x) =
          Complex.exp (-x) * Complex.exp (-(s - 1) * x) := by
      rw [← Complex.exp_add]
      ring_nf
    grind
  have hz : ‖-(s - 1) * (x : ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx0]
    grind
  have hnum :
      ‖Complex.exp (-x) - Complex.exp (-s * x)‖ ≤
        2 * ‖s - 1‖ * x := by
    rw [hfactor, norm_mul]
    have hexpnorm : ‖Complex.exp (-x)‖ = Real.exp (-x) := by
      rw [Complex.norm_exp]
      simp
    rw [hexpnorm]
    have hsub :
        ‖1 - Complex.exp (-(s - 1) * x)‖ ≤
          2 * ‖s - 1‖ * x := by
      rw [← norm_neg, neg_sub]
      calc
        ‖Complex.exp (-(s - 1) * x) - 1‖ ≤
            2 * ‖-(s - 1) * (x : ℂ)‖ :=
          Complex.norm_exp_sub_one_le hz
        _ = 2 * ‖s - 1‖ * x := by
          rw [norm_mul, norm_neg, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hx0]
          ring
    calc
      Real.exp (-x) * ‖1 - Complex.exp (-(s - 1) * x)‖ ≤
          1 * (2 * ‖s - 1‖ * x) := by
        gcongr
        grind
      _ = _ := by ring
  rw [gaussDigammaIntegrand, norm_div, hden]
  have hlower : x / 2 ≤ 1 - Real.exp (-x) :=
    half_mul_le_one_sub_exp_neg hx0.le hx1
  apply (div_le_iff₀ hdenPos).mpr
  calc
    ‖Complex.exp (-x) - Complex.exp (-s * x)‖ ≤
        2 * ‖s - 1‖ * x := hnum
    _ ≤ (4 * ‖s - 1‖) * (1 - Real.exp (-x)) := by
      nlinarith [norm_nonneg (s - 1)]

theorem norm_gaussDigammaIntegrand_le_tail
    {s : ℂ} (_hs : 0 < s.re) {x : ℝ} (hx : 1 ≤ x) :
    ‖gaussDigammaIntegrand s x‖ ≤
      (1 - Real.exp (-1))⁻¹ *
        (Real.exp (-x) + Real.exp (-s.re * x)) := by
  have hdenPos : 0 < 1 - Real.exp (-x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hdenOnePos : 0 < 1 - Real.exp (-1) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hden :
      ‖(1 : ℂ) - Complex.exp (-x)‖ =
        1 - Real.exp (-x) := by
    rw [show Complex.exp (-x) = (Real.exp (-x) : ℝ) by
      simp]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdenPos]
  have hdenLower : 1 - Real.exp (-1) ≤ 1 - Real.exp (-x) := by
    gcongr
  have hnum :
      ‖Complex.exp (-x) - Complex.exp (-s * x)‖ ≤
        Real.exp (-x) + Real.exp (-s.re * x) := by
    calc
      ‖Complex.exp (-x) - Complex.exp (-s * x)‖ ≤
          ‖Complex.exp (-x)‖ + ‖Complex.exp (-s * x)‖ :=
        norm_sub_le _ _
      _ = Real.exp (-x) + Real.exp (-s.re * x) := by
        rw [Complex.norm_exp, Complex.norm_exp]
        simp
  rw [gaussDigammaIntegrand, norm_div, hden]
  calc
    ‖Complex.exp (-x) - Complex.exp (-s * x)‖ /
          (1 - Real.exp (-x)) ≤
        (Real.exp (-x) + Real.exp (-s.re * x)) /
          (1 - Real.exp (-x)) := by
      exact div_le_div_of_nonneg_right hnum hdenPos.le
    _ ≤ (Real.exp (-x) + Real.exp (-s.re * x)) /
          (1 - Real.exp (-1)) := by
      exact div_le_div_of_nonneg_left
        (by positivity) hdenOnePos hdenLower
    _ = _ := by grind

theorem gaussDigammaIntegrand_integrableOn_Ioi_one
    {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn (gaussDigammaIntegrand s)
      (Set.Ioi (1 : ℝ)) := by
  let C : ℝ := (1 - Real.exp (-1))⁻¹
  let majorant : ℝ → ℝ := fun x ↦
    C * (Real.exp (-x) + Real.exp (-s.re * x))
  have hfirst :
      MeasureTheory.IntegrableOn (fun x : ℝ ↦ Real.exp (-x))
        (Set.Ioi (1 : ℝ)) := by
    simpa only [neg_mul, one_mul] using
      (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 1)
  have hsecond :
      MeasureTheory.IntegrableOn
        (fun x : ℝ ↦ Real.exp (-s.re * x))
        (Set.Ioi (1 : ℝ)) :=
    integrableOn_exp_mul_Ioi (by linarith) 1
  have hmajorant :
      MeasureTheory.IntegrableOn majorant (Set.Ioi (1 : ℝ)) :=
    (hfirst.add hsecond).const_mul C
  have hmeas :
      AEStronglyMeasurable (gaussDigammaIntegrand s)
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
    have hcont : ContinuousOn (gaussDigammaIntegrand s) (Set.Ioi (1 : ℝ)) := by
      intro x hx
      unfold gaussDigammaIntegrand
      apply ContinuousWithinAt.div
      · fun_prop
      · fun_prop
      · have hx0 : 0 < x := zero_lt_one.trans hx
        intro h
        have hexp : Complex.exp (-(x : ℂ)) = 1 :=
          sub_eq_zero.mp h |>.symm
        have hnorm := congrArg norm hexp
        have hre : Real.exp (-x) = Real.exp 0 := by
          simpa [Complex.norm_exp] using hnorm
        simp_all
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  apply Integrable.mono' hmajorant hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_gaussDigammaIntegrand_le_tail hs hx.le

/-- A gauss digamma local radius used in the Odlyzko-bound argument. -/
noncomputable def gaussDigammaLocalRadius (s : ℂ) : ℝ :=
  min 1 (1 / (1 + ‖s - 1‖))

theorem norm_mul_gaussDigammaLocalRadius_le_one (s : ℂ) :
    ‖s - 1‖ * gaussDigammaLocalRadius s ≤ 1 := by
  have hr :
      gaussDigammaLocalRadius s ≤ 1 / (1 + ‖s - 1‖) :=
    min_le_right _ _
  calc
    ‖s - 1‖ * gaussDigammaLocalRadius s ≤
        ‖s - 1‖ * (1 / (1 + ‖s - 1‖)) := by gcongr
    _ ≤ 1 := by
      have hp : 0 < 1 + ‖s - 1‖ := by positivity
      rw [one_div, ← div_eq_mul_inv]
      exact (div_le_one hp).mpr (by linarith)

theorem gaussDigammaIntegrand_integrableOn_Ioc_zero_localRadius
    (s : ℂ) :
    IntegrableOn (gaussDigammaIntegrand s)
      (Ioc 0 (gaussDigammaLocalRadius s)) := by
  let r := gaussDigammaLocalRadius s
  have hr1 : r ≤ 1 := min_le_left _ _
  have hmajor :
      IntegrableOn (fun _ : ℝ ↦ 4 * ‖s - 1‖)
        (Ioc 0 r) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmeas :
      AEStronglyMeasurable (gaussDigammaIntegrand s)
        (volume.restrict (Ioc 0 r)) := by
    have hcont : ContinuousOn (gaussDigammaIntegrand s) (Ioc 0 r) := by
      intro x hx
      unfold gaussDigammaIntegrand
      apply ContinuousWithinAt.div
      · fun_prop
      · fun_prop
      · intro h
        have hexp : Complex.exp (-(x : ℂ)) = 1 :=
          sub_eq_zero.mp h |>.symm
        have hnorm := congrArg norm hexp
        have hre : Real.exp (-x) = Real.exp 0 := by
          simpa [Complex.norm_exp] using hnorm
        simp_all
    exact hcont.aestronglyMeasurable measurableSet_Ioc
  apply Integrable.mono' hmajor hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  apply norm_gaussDigammaIntegrand_le_local s hx.1
    (hx.2.trans hr1)
  calc
    ‖s - 1‖ * x ≤ ‖s - 1‖ * r := by gcongr; simp_all
    _ ≤ 1 := norm_mul_gaussDigammaLocalRadius_le_one s

theorem gaussDigammaIntegrand_integrableOn_Ioi
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (gaussDigammaIntegrand s) (Ioi 0) := by
  let r := gaussDigammaLocalRadius s
  have hr0 : 0 < r := by
    dsimp only [r, gaussDigammaLocalRadius]
    positivity
  have hlocal :=
    gaussDigammaIntegrand_integrableOn_Ioc_zero_localRadius s
  have hmiddle : IntegrableOn (gaussDigammaIntegrand s) (Ioc r 1) := by
    have hcont : ContinuousOn (gaussDigammaIntegrand s) (Icc r 1) := by
      intro x hx
      unfold gaussDigammaIntegrand
      apply ContinuousWithinAt.div
      · fun_prop
      · fun_prop
      · intro h
        have hexp : Complex.exp (-(x : ℂ)) = 1 :=
          sub_eq_zero.mp h |>.symm
        have hnorm := congrArg norm hexp
        have hre : Real.exp (-x) = Real.exp 0 := by
          simpa [Complex.norm_exp] using hnorm
        have : -x = 0 := Real.exp_injective hre
        grind
    exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have htail := gaussDigammaIntegrand_integrableOn_Ioi_one hs
  rw [show Ioi (0 : ℝ) = Ioc 0 r ∪ Ioc r 1 ∪ Ioi 1 by
    grind]
  exact (hlocal.union hmiddle).union htail

end NumberField.Odlyzko
