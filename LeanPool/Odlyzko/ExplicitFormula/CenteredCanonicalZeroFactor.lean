/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CanonicalZeroFactor

/-!
# Centered Canonical Zero Factor

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex ComplexConjugate Metric Set

namespace NumberField.Odlyzko

/-- A centered canonical zero factor used in the Odlyzko-bound argument. -/
noncomputable def centeredCanonicalZeroFactor
    (c : ℂ) (R : ℝ) (u : ℂ) : ℂ → ℂ :=
  fun z ↦ canonicalZeroFactor R (u - c) (z - c)

theorem norm_centeredCanonicalZeroFactor_eq_one
    {c u z : ℂ} {R : ℝ} (hu : u ∈ ball c R) (hz : z ∈ sphere c R) :
    ‖centeredCanonicalZeroFactor c R u z‖ = 1 := by
  apply norm_canonicalZeroFactor_eq_one
  · simpa [Metric.mem_ball, dist_eq] using hu
  · simp_all

theorem centeredCanonicalZeroFactor_eq_zero_iff
    {c u z : ℂ} {R : ℝ} (hu : u ∈ ball c R) (hz : z ∈ ball c R) :
    centeredCanonicalZeroFactor c R u z = 0 ↔ z = u := by
  rw [centeredCanonicalZeroFactor,
    canonicalZeroFactor_eq_zero_iff
      (by simpa [Metric.mem_ball, dist_eq] using hu)
      (by simpa [Metric.mem_ball, dist_eq] using hz)]
  simp

theorem canonicalReflectedDenominator_ne_zero_on_closedBall
    {c u z : ℂ} {R : ℝ} (hu : u ∈ ball c R)
    (hz : z ∈ closedBall c R) :
    (R : ℂ) ^ 2 - conj (u - c) * (z - c) ≠ 0 := by
  have hR : 0 < R := pos_of_mem_ball hu
  have huNorm : ‖u - c‖ < R := by
    simpa [Metric.mem_ball, dist_eq] using hu
  have hzNorm : ‖z - c‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq] using hz
  have hprod :
      ‖conj (u - c) * (z - c)‖ < ‖((R : ℂ) ^ 2)‖ := by
    rw [norm_mul, norm_conj, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
    calc
      ‖u - c‖ * ‖z - c‖ ≤ ‖u - c‖ * R :=
        mul_le_mul_of_nonneg_left hzNorm (norm_nonneg _)
      _ < R * R := mul_lt_mul_of_pos_right huNorm hR
      _ = R ^ 2 := by ring
  grind

theorem analyticOnNhd_centeredCanonicalZeroFactor
    {c u : ℂ} {R : ℝ} (hu : u ∈ ball c R) :
    AnalyticOnNhd ℂ (centeredCanonicalZeroFactor c R u)
      (closedBall c R) := by
  intro z hz
  have hden :=
    canonicalReflectedDenominator_ne_zero_on_closedBall hu hz
  have hden' :
      (-conj (u - c)) * (z - c) + (R : ℂ) ^ 2 ≠ 0 := by grind
  rw [show centeredCanonicalZeroFactor c R u =
      fun w ↦ (w - u) * (R : ℂ) /
        ((-conj (u - c)) * (w - c) + (R : ℂ) ^ 2) by
      funext w
      rw [centeredCanonicalZeroFactor,
        canonicalZeroFactor_apply R (u - c) (w - c)]
      simp]
  fun_prop

theorem differentiableAt_centeredCanonicalZeroFactor
    {c u z : ℂ} {R : ℝ} (hu : u ∈ ball c R) (hz : z ∈ ball c R)
    (hzu : z ≠ u) :
    DifferentiableAt ℂ (centeredCanonicalZeroFactor c R u) z := by
  have hu' : u - c ∈ ball 0 R := by
    simpa [Metric.mem_ball, dist_eq] using hu
  have hz' : z - c ∈ ball 0 R := by
    simpa [Metric.mem_ball, dist_eq] using hz
  have hzu' : z - c ≠ u - c := by simp_all
  change DifferentiableAt ℂ
    (fun w ↦ (canonicalFactor R (u - c) (w - c))⁻¹) z
  have hshift : AnalyticAt ℂ (fun w : ℂ ↦ w - c) z := by
    fun_prop
  have houter :=
    (analyticOnNhd_canonicalFactor R (u - c) (z - c) hzu').inv
      (canonicalFactor_ne_zero hu'
        (Metric.ball_subset_closedBall hz') hzu')
  have hcomp :
      AnalyticAt ℂ
        ((fun w ↦ (canonicalFactor R (u - c) w)⁻¹) ∘
          fun w : ℂ ↦ w - c) z :=
    AnalyticAt.comp
      (g := fun w ↦ (canonicalFactor R (u - c) w)⁻¹)
      (f := fun w : ℂ ↦ w - c) (x := z) houter hshift
  simpa [Function.comp_def] using hcomp.differentiableAt

theorem canonicalReflectedDenominator_ne_zero
    {c u z : ℂ} {R : ℝ} (hu : u ∈ ball c R) (hz : z ∈ ball c R)
    (hzu : z ≠ u) :
    (R : ℂ) ^ 2 - conj (u - c) * (z - c) ≠ 0 := by
  have hu' : u - c ∈ ball 0 R := by
    simpa [Metric.mem_ball, dist_eq] using hu
  have hz' : z - c ∈ ball 0 R := by
    simpa [Metric.mem_ball, dist_eq] using hz
  have hzu' : z - c ≠ u - c := by simp_all
  have hfactor :=
    canonicalFactor_ne_zero hu' (Metric.ball_subset_closedBall hz') hzu'
  intro h
  apply hfactor
  rw [canonicalFactor_apply, h, zero_div]

theorem logDeriv_centeredCanonicalZeroFactor
    {c u z : ℂ} {R : ℝ} (hR : R ≠ 0)
    (hu : u ∈ ball c R) (hz : z ∈ ball c R) (hzu : z ≠ u)
    (hreflect :
      (R : ℂ) ^ 2 - conj (u - c) * (z - c) ≠ 0) :
    logDeriv (centeredCanonicalZeroFactor c R u) z =
      1 / (z - u) +
        conj (u - c) /
          ((R : ℂ) ^ 2 - conj (u - c) * (z - c)) := by
  have hu' : u - c ∈ ball 0 R := by
    simpa [Metric.mem_ball, dist_eq] using hu
  have hz' : z - c ∈ ball 0 R := by
    simpa [Metric.mem_ball, dist_eq] using hz
  have hzu' : z - c ≠ u - c := by simp_all
  have hcanDiff :
      DifferentiableAt ℂ (canonicalZeroFactor R (u - c)) (z - c) := by
    change DifferentiableAt ℂ
      (fun w ↦ (canonicalFactor R (u - c) w)⁻¹) (z - c)
    exact
      (analyticOnNhd_canonicalFactor R (u - c) (z - c) hzu').inv
        (canonicalFactor_ne_zero hu'
          (Metric.ball_subset_closedBall hz') hzu') |>.differentiableAt
  have hshift : DifferentiableAt ℂ (fun w : ℂ ↦ w - c) z := by simp
  change logDeriv
      (canonicalZeroFactor R (u - c) ∘ fun w : ℂ ↦ w - c) z = _
  rw [logDeriv_comp
      (f := canonicalZeroFactor R (u - c))
      (g := fun w : ℂ ↦ w - c) (x := z) hcanDiff hshift,
    deriv_sub_const, deriv_id'', mul_one,
    logDeriv_canonicalZeroFactor hR hzu' hreflect]
  simp

theorem norm_conj_div_reflected_centered_le
    {c u z : ℂ} {r R : ℝ} (hR : 0 < R) (_hr : 0 ≤ r) (hrR : r < R)
    (hu : u ∈ ball c R) (hz : z ∈ closedBall c r) :
    ‖conj (u - c) /
        ((R : ℂ) ^ 2 - conj (u - c) * (z - c))‖ ≤
      1 / (R - r) := by
  have huNorm : ‖u - c‖ ≤ R := by
    exact (by simpa [Metric.mem_ball, dist_eq] using hu : ‖u - c‖ < R).le
  have hzNorm : ‖z - c‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq] using hz
  have hgap : 0 < R * (R - r) := mul_pos hR (sub_pos.mpr hrR)
  have hprod : ‖u - c‖ * ‖z - c‖ ≤ R * r := by
    exact mul_le_mul huNorm hzNorm (norm_nonneg _) hR.le
  have hden :
      R * (R - r) ≤
        ‖(R : ℂ) ^ 2 - conj (u - c) * (z - c)‖ := by
    calc
      R * (R - r) ≤
          ‖((R : ℂ) ^ 2)‖ -
            ‖conj (u - c) * (z - c)‖ := by
        rw [norm_mul, norm_conj, norm_pow, norm_real, Real.norm_eq_abs,
          abs_of_pos hR]
        nlinarith
      _ ≤ ‖(R : ℂ) ^ 2 - conj (u - c) * (z - c)‖ :=
        norm_sub_norm_le _ _
  rw [norm_div, norm_conj]
  calc
    ‖u - c‖ /
        ‖(R : ℂ) ^ 2 - conj (u - c) * (z - c)‖ ≤
        R / (R * (R - r)) :=
      div_le_div₀ hR.le huNorm hgap hden
    _ = 1 / (R - r) := by grind

theorem norm_finprod_centeredCanonicalZeroFactor_zpow_eq_one
    {c : ℂ} {R : ℝ} (D : ℂ → ℤ) (hfin : D.support.Finite)
    (hinside : ∀ u ∈ D.support, u ∈ ball c R)
    {z : ℂ} (hz : z ∈ sphere c R) :
    ‖(∏ᶠ u, (centeredCanonicalZeroFactor c R u) ^ D u) z‖ = 1 := by
  classical
  let S := hfin.toFinset
  have hmul :
      (fun u ↦ (centeredCanonicalZeroFactor c R u) ^ D u).mulSupport ⊆ S := by
    intro u hu
    apply hfin.mem_toFinset.mpr
    by_contra hDu
    simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ hmul]
  simp only [Finset.prod_apply, norm_prod]
  apply Finset.prod_eq_one
  intro u hu
  change ‖(centeredCanonicalZeroFactor c R u z) ^ D u‖ = 1
  rw [norm_zpow, norm_centeredCanonicalZeroFactor_eq_one
    (hinside u (hfin.mem_toFinset.mp hu)) hz, one_zpow]

end NumberField.Odlyzko
