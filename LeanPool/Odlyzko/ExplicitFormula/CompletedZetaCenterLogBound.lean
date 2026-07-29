/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.VerticalGrowth
public import LeanPool.Odlyzko.CompletedZeta.VerticalLowerBound
public import LeanPool.Odlyzko.ECanonicalDecomposition
public import LeanPool.Odlyzko.ExplicitFormula.CompletedZetaRectangle
public import LeanPool.Odlyzko.ExplicitFormula.FiniteSetAvoidance
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Completed Zeta Center Log Bound

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Complex

namespace NumberField.Odlyzko

open Classical in
theorem norm_finsum_div_sub_le_finsum_div
    {D : ℂ → ℤ} (hfin : D.support.Finite)
    (hD : ∀ u, 0 ≤ D u) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ u ∈ D.support, δ ≤ ‖z - u‖) :
    ‖∑ᶠ u, (D u : ℂ) / (z - u)‖ ≤
      ((∑ᶠ u, D u : ℤ) : ℝ) / δ := by
  let S := hfin.toFinset
  have hsupp : D.support ⊆ S := fun u hu ↦ hfin.mem_toFinset.mpr hu
  have hterm :
      (fun u ↦ (D u : ℂ) / (z - u)).support ⊆ S := by
    intro u hu
    simp_all
  have hsumC :
      ∑ᶠ u, (D u : ℂ) / (z - u) =
        ∑ u ∈ S, (D u : ℂ) / (z - u) :=
    finsum_eq_sum_of_support_subset _ hterm
  have hsumZ : ∑ᶠ u, D u = ∑ u ∈ S, D u :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsumC, hsumZ]
  calc
    ‖∑ u ∈ S, (D u : ℂ) / (z - u)‖ ≤
        ∑ u ∈ S, ‖(D u : ℂ) / (z - u)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ u ∈ S, (D u : ℝ) / δ := by
      apply Finset.sum_le_sum
      intro u hu
      have huD : 0 ≤ (D u : ℝ) := by simp_all
      by_cases hDu : D u = 0
      · simp [hDu]
      · rw [norm_div, norm_intCast, abs_of_nonneg huD]
        exact div_le_div₀ huD le_rfl hδ
          (hsep u (Function.mem_support.mpr hDu))
    _ = ((∑ u ∈ S, D u : ℤ) : ℝ) / δ := by
      rw [Int.cast_sum]
      rw [Finset.sum_div]

end NumberField.Odlyzko

end

section

open Complex ComplexConjugate Filter Metric Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A canonical zero factor used in the Odlyzko-bound argument. -/
noncomputable def canonicalZeroFactor (R : ℝ) (u : ℂ) : ℂ → ℂ :=
  fun z ↦ (canonicalFactor R u z)⁻¹

theorem norm_canonicalZeroFactor_eq_one
    {R : ℝ} {u z : ℂ} (hu : u ∈ ball 0 R) (hz : z ∈ sphere 0 R) :
    ‖canonicalZeroFactor R u z‖ = 1 := by
  rw [canonicalZeroFactor, norm_inv,
    norm_canonicalFactor_eval_circle_eq_one hu hz, inv_one]

theorem canonicalZeroFactor_eq_zero_iff
    {R : ℝ} {u z : ℂ} (hu : u ∈ ball 0 R) (hz : z ∈ ball 0 R) :
    canonicalZeroFactor R u z = 0 ↔ z = u := by
  rw [canonicalZeroFactor, inv_eq_zero,
    canonicalFactor_eq_zero_iff hu hz]

theorem canonicalZeroFactor_apply
    (R : ℝ) (u z : ℂ) :
    canonicalZeroFactor R u z =
      (z - u) * (R : ℂ) / ((-conj u) * z + (R : ℂ) ^ 2) := by
  rw [canonicalZeroFactor, canonicalFactor_apply, inv_div]
  ring

theorem logDeriv_canonicalZeroFactor
    {R : ℝ} {u z : ℂ} (hR : R ≠ 0) (hzu : z ≠ u)
    (hreflect : (R : ℂ) ^ 2 - conj u * z ≠ 0) :
    logDeriv (canonicalZeroFactor R u) z =
      1 / (z - u) + conj u / ((R : ℂ) ^ 2 - conj u * z) := by
  have hreflect' : (-conj u) * z + (R : ℂ) ^ 2 ≠ 0 := by grind
  have hlocal :
      canonicalZeroFactor R u =ᶠ[𝓝 z]
        fun w ↦ (w - u) * (R : ℂ) /
          ((-conj u) * w + (R : ℂ) ^ 2) := by
    filter_upwards with w
    exact canonicalZeroFactor_apply R u w
  rw [logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds,
    deriv_fun_div
      (c := fun w : ℂ ↦ (w - u) * (R : ℂ))
      (d := fun w : ℂ ↦ (-conj u) * w + (R : ℂ) ^ 2)
      (x := z) (by simp) (by fun_prop) hreflect']
  rw [deriv_mul_const_field, deriv_sub_const, deriv_id'', one_mul,
    deriv_add_const, deriv_const_mul_id]
  have hsub : z - u ≠ 0 := sub_ne_zero.mpr hzu
  have hR' : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR
  let q : ℂ := (-conj u) * z + (R : ℂ) ^ 2
  have hq : (R : ℂ) ^ 2 - conj u * z = q := by grind
  have hqne : q ≠ 0 := hq ▸ hreflect
  rw [hq]
  change
    (((R : ℂ) * q - (z - u) * (R : ℂ) * (-conj u)) / q ^ 2) /
        ((z - u) * (R : ℂ) / q) =
      1 / (z - u) + conj u / q
  have hfactor :
      (z - u) * (R : ℂ) / q ≠ 0 :=
    div_ne_zero (mul_ne_zero hsub hR') hqne
  grind

end NumberField.Odlyzko

end

section

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

end

section

open Complex ComplexConjugate Metric Set

namespace NumberField.Odlyzko

open Classical in
theorem norm_finsum_reflected_centered_le
    {D : ℂ → ℤ} (hfin : D.support.Finite) (hD : ∀ u, 0 ≤ D u)
    {c z : ℂ} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hinside : ∀ u ∈ D.support, u ∈ ball c R)
    (hz : z ∈ closedBall c r) :
    ‖∑ᶠ u,
        (D u : ℂ) *
          (conj (u - c) /
            ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))‖ ≤
      ((∑ᶠ u, D u : ℤ) : ℝ) / (R - r) := by
  let S := hfin.toFinset
  have hsupp : D.support ⊆ S := fun u hu ↦ hfin.mem_toFinset.mpr hu
  have hterm :
      (fun u ↦
        (D u : ℂ) *
          (conj (u - c) /
            ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))).support ⊆ S := by
    intro u hu
    simp_all
  have hsumC :
      ∑ᶠ u,
          (D u : ℂ) *
            (conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c))) =
        ∑ u ∈ S,
          (D u : ℂ) *
            (conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c))) :=
    finsum_eq_sum_of_support_subset _ hterm
  have hsumZ : ∑ᶠ u, D u = ∑ u ∈ S, D u :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsumC, hsumZ]
  calc
    ‖∑ u ∈ S,
        (D u : ℂ) *
          (conj (u - c) /
            ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))‖ ≤
        ∑ u ∈ S,
          ‖(D u : ℂ) *
            (conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ u ∈ S, (D u : ℝ) * (1 / (R - r)) := by
      apply Finset.sum_le_sum
      intro u hu
      have huD : 0 ≤ (D u : ℝ) := by simp_all
      rw [norm_mul, norm_intCast, abs_of_nonneg huD]
      exact mul_le_mul_of_nonneg_left
        (norm_conj_div_reflected_centered_le hR hr hrR
          (hinside u (hfin.mem_toFinset.mp hu)) hz) huD
    _ = ((∑ u ∈ S, D u : ℤ) : ℝ) / (R - r) := by
      rw [Int.cast_sum]
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      simp only [one_mul]

open Classical in
theorem norm_finsum_canonicalLogDeriv_le
    {D : ℂ → ℤ} (hfin : D.support.Finite) (hD : ∀ u, 0 ≤ D u)
    {c z : ℂ} {δ r R : ℝ} (hδ : 0 < δ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hinside : ∀ u ∈ D.support, u ∈ ball c R)
    (hz : z ∈ closedBall c r)
    (hsep : ∀ u ∈ D.support, δ ≤ ‖z - u‖) :
    ‖∑ᶠ u,
        (D u : ℂ) *
          (1 / (z - u) +
            conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))‖ ≤
      ((∑ᶠ u, D u : ℤ) : ℝ) / δ +
        ((∑ᶠ u, D u : ℤ) : ℝ) / (R - r) := by
  have hfinA : Function.HasFiniteSupport
      (fun u ↦ (D u : ℂ) * (1 / (z - u))) := by
    apply hfin.subset
    intro u hu
    simp_all
  have hfinB : Function.HasFiniteSupport
      (fun u ↦
        (D u : ℂ) *
          (conj (u - c) /
            ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))) := by
    apply hfin.subset
    intro u hu
    simp_all
  simp_rw [mul_add]
  rw [finsum_add_distrib hfinA hfinB]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have heq :
        (∑ᶠ u, (D u : ℂ) * (1 / (z - u))) =
          ∑ᶠ u, (D u : ℂ) / (z - u) := by grind
    rw [heq]
    exact norm_finsum_div_sub_le_finsum_div hfin hD hδ hsep
  · exact norm_finsum_reflected_centered_le
      hfin hD hR hr hrR hinside hz

open Classical in
theorem norm_finsum_canonicalLogDeriv_le_of_finsum_le
    {D : ℂ → ℤ} (hfin : D.support.Finite) (hD : ∀ u, 0 ≤ D u)
    {c z : ℂ} {δ r R B : ℝ} (hδ : 0 < δ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hinside : ∀ u ∈ D.support, u ∈ ball c R)
    (hz : z ∈ closedBall c r)
    (hsep : ∀ u ∈ D.support, δ ≤ ‖z - u‖)
    (hmass : ((∑ᶠ u, D u : ℤ) : ℝ) ≤ B) :
    ‖∑ᶠ u,
        (D u : ℂ) *
          (1 / (z - u) +
            conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))‖ ≤
      B / δ + B / (R - r) := by
  refine (norm_finsum_canonicalLogDeriv_le
    hfin hD hδ hR hr hrR hinside hz hsep).trans ?_
  exact add_le_add
    (div_le_div_of_nonneg_right hmass hδ.le)
    (div_le_div_of_nonneg_right hmass (sub_nonneg.mpr hrR.le))

end NumberField.Odlyzko

end

section

open Complex ComplexConjugate Metric Set

namespace NumberField.Odlyzko

open Classical in
/-- A centered canonical zero product used in the Odlyzko-bound argument. -/
noncomputable def centeredCanonicalZeroProduct
    (c : ℂ) (R : ℝ) (D : ℂ → ℤ) : ℂ → ℂ :=
  ∏ᶠ u, (centeredCanonicalZeroFactor c R u) ^ D u

open Classical in
theorem analyticOnNhd_centeredCanonicalZeroProduct
    {D : ℂ → ℤ} (hD : ∀ u, 0 ≤ D u)
    {c : ℂ} {R : ℝ}
    (hinside : ∀ u ∈ D.support, u ∈ ball c R) :
    AnalyticOnNhd ℂ (centeredCanonicalZeroProduct c R D)
      (closedBall c R) := by
  intro z hz
  rw [centeredCanonicalZeroProduct]
  apply analyticAt_finprod
  intro u
  by_cases hu : u ∈ D.support
  · exact
      ((analyticOnNhd_centeredCanonicalZeroFactor (hinside u hu)) z hz)
        |>.zpow_nonneg (hD u)
  · have hDu : D u = 0 := not_ne_iff.mp hu
    rw [hDu, zpow_zero]
    exact analyticAt_const

open Classical in
theorem norm_centeredCanonicalZeroProduct_eq_one
    {D : ℂ → ℤ} (hfin : D.support.Finite)
    {c z : ℂ} {R : ℝ}
    (hinside : ∀ u ∈ D.support, u ∈ ball c R)
    (hz : z ∈ sphere c R) :
    ‖centeredCanonicalZeroProduct c R D z‖ = 1 := by
  exact norm_finprod_centeredCanonicalZeroFactor_zpow_eq_one
    D hfin hinside hz

open Classical in
theorem norm_centeredCanonicalZeroProduct_le_one
    {D : ℂ → ℤ} (hfin : D.support.Finite) (hD : ∀ u, 0 ≤ D u)
    {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hinside : ∀ u ∈ D.support, u ∈ ball c R)
    (hz : z ∈ closedBall c R) :
    ‖centeredCanonicalZeroProduct c R D z‖ ≤ 1 := by
  apply norm_le_of_forall_mem_frontier_norm_le
    (U := ball c R) isBounded_ball
    (DifferentiableOn.diffContOnCl fun w hw ↦
      ((analyticOnNhd_centeredCanonicalZeroProduct hD hinside) w
        (closure_ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt)
  · intro w hw
    exact (norm_centeredCanonicalZeroProduct_eq_one
      hfin hinside (frontier_ball_subset_sphere hw)).le
  · rwa [closure_ball c hR.ne']

open Classical in
theorem logDeriv_centeredCanonicalZeroProduct
    {D : ℂ → ℤ} (hfin : D.support.Finite)
    {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hinside : ∀ u ∈ D.support, u ∈ ball c R)
    (hz : z ∈ ball c R) (hzD : z ∉ D.support) :
    logDeriv (centeredCanonicalZeroProduct c R D) z =
      ∑ᶠ u,
        (D u : ℂ) *
          (1 / (z - u) +
            conj (u - c) /
              ((R : ℂ) ^ 2 - conj (u - c) * (z - c))) := by
  let S := hfin.toFinset
  have hmul :
      (fun u ↦ (centeredCanonicalZeroFactor c R u) ^ D u).mulSupport ⊆ S := by
    intro u hu
    apply hfin.mem_toFinset.mpr
    by_contra hDu
    simp_all
  have hprod :
      centeredCanonicalZeroProduct c R D =
        ∏ u ∈ S, (centeredCanonicalZeroFactor c R u) ^ D u := by
    exact finprod_eq_prod_of_mulSupport_subset _ hmul
  rw [hprod]
  have hpoint :
      (∏ u ∈ S, (centeredCanonicalZeroFactor c R u) ^ D u) =
        fun w ↦ ∏ u ∈ S,
          (centeredCanonicalZeroFactor c R u w) ^ D u := by
    funext w
    simp
  rw [hpoint, logDeriv_prod]
  · rw [finsum_eq_sum_of_support_subset]
    · apply Finset.sum_congr rfl
      intro u hu
      have huSupport : u ∈ D.support := hfin.mem_toFinset.mp hu
      have hzu : z ≠ u := by grind
      have huBall := hinside u huSupport
      have hreflect :
          (R : ℂ) ^ 2 - conj (u - c) * (z - c) ≠ 0 :=
        canonicalReflectedDenominator_ne_zero huBall hz hzu
      have hdiff :
          DifferentiableAt ℂ (centeredCanonicalZeroFactor c R u) z :=
        differentiableAt_centeredCanonicalZeroFactor huBall hz hzu
      rw [logDeriv_fun_zpow hdiff,
        logDeriv_centeredCanonicalZeroFactor hR.ne' huBall hz hzu hreflect]
    · intro u hu
      apply hfin.mem_toFinset.mpr
      simp_all
  · intro u hu
    have huSupport : u ∈ D.support := hfin.mem_toFinset.mp hu
    have hzu : z ≠ u := by grind
    exact zpow_ne_zero _ <|
      (centeredCanonicalZeroFactor_eq_zero_iff
        (hinside u huSupport) hz).not.mpr hzu
  · intro u hu
    have huSupport : u ∈ D.support := hfin.mem_toFinset.mp hu
    have hzu : z ≠ u := by grind
    have hdiff :
        DifferentiableAt ℂ (centeredCanonicalZeroFactor c R u) z :=
      differentiableAt_centeredCanonicalZeroFactor
        (hinside u huSupport) hz hzu
    exact hdiff.zpow <| Or.inl <|
      (centeredCanonicalZeroFactor_eq_zero_iff
        (hinside u huSupport) hz).not.mpr hzu

end NumberField.Odlyzko

end

section

open Complex Filter Function MeromorphicOn Metric Set
open scoped Topology

namespace NumberField.Odlyzko

open Classical in
theorem divisor_eq_zero_of_analyticOnNhd_of_ne_zero
    {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∀ z ∈ U, f z ≠ 0) :
    MeromorphicOn.divisor f U = 0 := by
  ext z
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz,
      (hf z hz).meromorphicOrderAt_eq,
      (hf z hz).analyticOrderAt_eq_zero.mpr (hne z hz)]
    simp
  · simp [hz]

open Classical in
theorem divisor_ball_support_subset
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} :
    (MeromorphicOn.divisor f (ball c R)).support ⊆ ball c R := by
  intro z hz
  by_contra hzball
  simp_all

open Classical in
theorem divisor_ball_eq_divisor_closedBall_of_boundary_ne
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∀ z,
      MeromorphicOn.divisor f (ball c R) z =
        MeromorphicOn.divisor f (closedBall c R) z := by
  intro z
  by_cases hzball : z ∈ ball c R
  · rw [MeromorphicOn.divisor_apply
        (hf.mono ball_subset_closedBall).meromorphicOn hzball,
      MeromorphicOn.divisor_apply hf.meromorphicOn
        (ball_subset_closedBall hzball)]
  · by_cases hzclosed : z ∈ closedBall c R
    · have hzsphere : z ∈ sphere c R := by
        rw [mem_sphere, mem_closedBall, mem_ball] at *
        grind
      have hzorder :
          meromorphicOrderAt f z = 0 := by
        rw [(hf z hzclosed).meromorphicOrderAt_eq,
          (hf z hzclosed).analyticOrderAt_eq_zero.mpr
            (hboundary z hzsphere)]
        simp
      rw [MeromorphicOn.divisor_apply hf.meromorphicOn hzclosed,
        hzorder]
      simp [MeromorphicOn.divisor, hzball]
    · simp [MeromorphicOn.divisor, hzball, hzclosed]

open Classical in
theorem AnalyticOnNhd.exists_canonicalZeroFactor_on_ball_zero
    {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hc : f 0 ≠ 0)
    (hboundary : ∀ z ∈ sphere 0 R, f z ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ closedBall 0 R, g z ≠ 0) ∧
      EqOn f
        ((centeredCanonicalZeroProduct 0 R
          (MeromorphicOn.divisor f (ball 0 R))) * g)
        (closedBall 0 R) ∧
      (∀ z ∈ sphere 0 R, ‖g z‖ = ‖f z‖) ∧
      ‖f 0‖ ≤ ‖g 0‖ := by
  let U := closedBall (0 : ℂ) R
  let D := MeromorphicOn.divisor f (ball 0 R)
  let B := centeredCanonicalZeroProduct 0 R D
  have hfmer : MeromorphicOn f U := hf.meromorphicOn
  have h0U : (0 : ℂ) ∈ U := mem_closedBall_self hR.le
  have h0ord : meromorphicOrderAt f 0 ≠ ⊤ := by
    intro htop
    have hne : f =ᶠ[𝓝[≠] 0] 0 := meromorphicOrderAt_eq_top_iff.mp htop
    have hnhds : f =ᶠ[𝓝 0] 0 :=
      ((hf 0 h0U).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        continuousAt_const).1 hne
    exact hc hnhds.eq_of_nhds
  have hord : ∀ z : U, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    exact hfmer.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall 0 R).isPreconnected h0U z.property h0ord
  obtain ⟨g, hg⟩ := hfmer.exists_ecanonicalDecomp hord
  have hsphere :
      MeromorphicOn.divisor f (sphere 0 R) = 0 :=
    divisor_eq_zero_of_analyticOnNhd_of_ne_zero
      (hf.mono sphere_subset_closedBall) hboundary
  have hDfin : D.support.Finite := by
    exact hfmer.divisor_ball_support_finite
  have hDnonneg : ∀ z, 0 ≤ D z := by
    intro z
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hf.mono ball_subset_closedBall) z
  have hDinside : ∀ z ∈ D.support, z ∈ ball 0 R := by
    exact divisor_ball_support_subset
  have hBanalytic : AnalyticOnNhd ℂ B U := by
    exact analyticOnNhd_centeredCanonicalZeroProduct hDnonneg hDinside
  have hcanonical :
      (∏ᶠ u, canonicalFactor R u ^
        (-MeromorphicOn.divisor f (ball 0 R) u)) = B := by
    apply finprod_congr
    intro u
    funext z
    simp [D, centeredCanonicalZeroFactor, canonicalZeroFactor]
  have hevent : f =ᶠ[codiscreteWithin U] B * g := by
    filter_upwards [hg.eventuallyEq] with z hz
    simp_all
  have heq : EqOn f (B * g) U := by
    intro z hz
    have hprod : MeromorphicAt (B * g) z :=
      (hBanalytic z hz).meromorphicAt.mul
        (hg.analyticOnNhd z hz).meromorphicAt
    have hne : f =ᶠ[𝓝[≠] z] B * g :=
      (hfmer z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (U := U) hprod hz (by
          dsimp [U]
          rw [← closure_ball (0 : ℂ) hR.ne']
          exact isOpen_ball.perfect_closure.2) hevent
    have hnhds : f =ᶠ[𝓝 z] B * g :=
      ((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        ((hBanalytic.mul hg.analyticOnNhd) z hz).continuousAt).1 hne
    exact hnhds.eq_of_nhds
  refine ⟨g, hg.analyticOnNhd, hg.ne_zero, ?_, ?_, ?_⟩
  · grind
  · intro z hz
    have hzU : z ∈ U := sphere_subset_closedBall hz
    have heqz := heq hzU
    have hBnorm : ‖B z‖ = 1 :=
      norm_centeredCanonicalZeroProduct_eq_one hDfin hDinside hz
    simp_all
  · have heq0 := heq h0U
    have hB0 :
        ‖B 0‖ ≤ 1 :=
      norm_centeredCanonicalZeroProduct_le_one
        hDfin hDnonneg hR hDinside h0U
    simp_all

end NumberField.Odlyzko

end

section

open Complex Filter Metric Set
open scoped Topology

namespace NumberField.Odlyzko

open Classical in
theorem AnalyticOnNhd.exists_zeroFree_sphere
    {f : ℂ → ℂ} {c : ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b)
    (hf : AnalyticOnNhd ℂ f (closedBall c b))
    (hc : f c ≠ 0) :
    ∃ R ∈ Ioo a b, ∀ z ∈ sphere c R, f z ≠ 0 := by
  let D := MeromorphicOn.divisor f (closedBall c b)
  have hDfin : D.support.Finite :=
    D.finiteSupport (isCompact_closedBall c b)
  have hb : 0 < b := ha.trans_lt hab
  have hcball : c ∈ closedBall c b := mem_closedBall_self hb.le
  have hmer : MeromorphicOn f (closedBall c b) := hf.meromorphicOn
  have hcord : meromorphicOrderAt f c ≠ ⊤ := by
    intro htop
    have hne : f =ᶠ[nhdsWithin c {c}ᶜ] 0 :=
      meromorphicOrderAt_eq_top_iff.mp htop
    have hnhds : f =ᶠ[𝓝 c] 0 :=
      ((hf c hcball).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
        continuousAt_const).1 hne
    exact hc hnhds.eq_of_nhds
  have hord : ∀ z : closedBall c b, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    exact hmer.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c b).isPreconnected hcball z.property hcord
  let S : Finset ℝ := hDfin.toFinset.image fun z ↦ dist z c
  obtain ⟨R, hR, hsep⟩ :=
    exists_mem_Ioo_abs_sub_ge_finiteSetAvoidanceRadiusOnLength
      S a (sub_pos.mpr hab)
  refine ⟨R, by grind, ?_⟩
  intro z hz hzero
  have hzball : z ∈ closedBall c b := by
    rw [mem_sphere] at hz
    rw [mem_closedBall, hz]
    grind
  have hzSupport : z ∈ D.support := by
    apply Function.mem_support.mpr
    rw [MeromorphicOn.divisor_apply hmer hzball]
    intro horder
    have horder0 : meromorphicOrderAt f z = 0 :=
      (WithTop.untop₀_eq_zero.mp horder).resolve_right (hord ⟨z, hzball⟩)
    rw [(hf z hzball).meromorphicOrderAt_eq] at horder0
    have : analyticOrderAt f z = 0 := by simpa using horder0
    exact (hf z hzball).analyticOrderAt_ne_zero.mpr hzero this
  have hzS : dist z c ∈ S := by
    apply Finset.mem_image.mpr
    exact ⟨z, hDfin.mem_toFinset.mpr hzSupport, rfl⟩
  have hpositive :=
    finiteSetAvoidanceRadiusOnLength_pos (sub_pos.mpr hab) S
  rw [mem_sphere] at hz
  grind

end NumberField.Odlyzko

end

section

open Complex

namespace NumberField.Odlyzko

open Classical in
theorem card_le_finsum_of_subset_support_of_nonneg
    {α : Type*} (D : α → ℤ)
    (hfin : Function.support D |>.Finite)
    (S : Finset α) (hS : (S : Set α) ⊆ Function.support D)
    (hD : ∀ x, 0 ≤ D x) :
    (S.card : ℝ) ≤ ((∑ᶠ x, D x : ℤ) : ℝ) := by
  let F := hfin.toFinset
  have hSF : S ⊆ F := by
    intro x hx
    exact hfin.mem_toFinset.mpr (hS hx)
  calc
    (S.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_le_card hSF
    _ = ∑ x ∈ F, (1 : ℝ) := by simp
    _ ≤ ∑ x ∈ F, (D x : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxD : D x ≠ 0 := Function.mem_support.mp
        (hfin.mem_toFinset.mp hx)
      have hxnonneg := hD x
      exact_mod_cast (show (1 : ℤ) ≤ D x by lia)
    _ = ((∑ᶠ x, D x : ℤ) : ℝ) := by
      rw [finsum_eq_sum_of_support_subset D (by
        intro x hx
        exact hfin.mem_toFinset.mpr hx)]
      norm_cast

open Classical in
theorem AnalyticOnNhd.card_zeros_le
    {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ} (hr : 0 < |r|)
    (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c |R|))
    (hc : f c ≠ 0)
    (f_bound : ∀ z ∈ Metric.sphere c |R|, ‖f z‖ ≤ M)
    (S : Finset ℂ)
    (hSsupport : ∀ z ∈ S,
      z ∈ Function.support
        (MeromorphicOn.divisor f (Metric.closedBall c |r|))) :
    (S.card : ℝ) ≤
      Real.log (M / ‖f c‖) / Real.log (R / r) := by
  let D : ℂ → ℤ := fun z ↦
    MeromorphicOn.divisor f (Metric.closedBall c |r|) z
  have hDnonneg (z : ℂ) : 0 ≤ D z := by
    dsimp [D]
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hf.mono (Metric.closedBall_subset_closedBall hrR.le)) z
  have hDfin : (Function.support D).Finite := by
    exact (MeromorphicOn.divisor f (Metric.closedBall c |r|)).finiteSupport
      (isCompact_closedBall c |r|)
  have hSsupport' : (S : Set ℂ) ⊆ Function.support D := by grind
  refine
    (card_le_finsum_of_subset_support_of_nonneg D hDfin S hSsupport' hDnonneg).trans ?_
  simpa [D] using hf.sum_divisor_le hr hrR hM hc f_bound

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
theorem mem_divisor_closedBall_of_mem_completedZetaZeroDivisor_support
    {c z : ℂ} {r : ℝ} (hzball : z ∈ Metric.closedBall c |r|)
    (hz : z ∈ (completedDedekindZetaZeroDivisor K).support) :
    z ∈ Function.support
      (MeromorphicOn.divisor
        (poleClearedCompletedDedekindZetaContinuation K)
        (Metric.closedBall c |r|)) := by
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  have hΞ :
      MeromorphicOn Ξ (Metric.closedBall c |r|) :=
    fun z _ ↦
      (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K)
        z (mem_univ z) |>.meromorphicAt
  have hglobal :
      MeromorphicOn Ξ Set.univ :=
    (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K).meromorphicOn
  intro hzero
  apply Function.mem_support.mp hz
  rw [completedDedekindZetaZeroDivisor,
    MeromorphicOn.divisor_apply hglobal (mem_univ z)]
  have hsmall :
      (MeromorphicOn.divisor Ξ (Metric.closedBall c |r|)) z =
        (meromorphicOrderAt Ξ z).untop₀ :=
    MeromorphicOn.divisor_apply hΞ hzball
  grind

open Classical in
theorem card_completedDedekindZetaZerosInClosedRectangle_le_jensen
    {a b u v : ℝ} {c : ℂ} {r R M : ℝ}
    (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hc :
      poleClearedCompletedDedekindZetaContinuation K c ≠ 0)
    (f_bound : ∀ z ∈ Metric.sphere c |R|,
      ‖poleClearedCompletedDedekindZetaContinuation K z‖ ≤ M)
    (hrect : Icc a b ×ℂ Icc u v ⊆ Metric.closedBall c |r|) :
    ((completedDedekindZetaZerosInClosedRectangle K a b u v).card : ℝ) ≤
      Real.log
          (M / ‖poleClearedCompletedDedekindZetaContinuation K c‖) /
        Real.log (R / r) := by
  apply AnalyticOnNhd.card_zeros_le hr hrR hM
    ((analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K).mono
      (subset_univ _))
    hc f_bound
  intro z hz
  have hz' :=
    (mem_completedDedekindZetaZerosInClosedRectangle_iff K).mp hz
  exact mem_divisor_closedBall_of_mem_completedZetaZeroDivisor_support K
    (hrect hz'.1) hz'.2

end NumberField.Odlyzko

end

section

open Complex NumberField Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A completed zeta moving circle bound used in the Odlyzko-bound argument. -/
noncomputable def completedZetaMovingCircleBound (R t : ℝ) : ℝ :=
  max 1 <|
    poleClearedCompletedDedekindZetaVerticalBound K (2 - |R|) (2 + |R|) *
      (1 + |t| + |R|) ^ 2

omit [IsTotallyComplex K] in
theorem one_le_completedZetaMovingCircleBound (R t : ℝ) :
    1 ≤ completedZetaMovingCircleBound K R t :=
  le_max_left _ _

theorem norm_poleClearedCompletedZeta_le_movingCircleBound
    (R t : ℝ) {z : ℂ} (hz : z ∈ Metric.sphere (2 + t * I) |R|) :
    ‖poleClearedCompletedDedekindZetaContinuation K z‖ ≤
      completedZetaMovingCircleBound K R t := by
  have hdist : ‖z - (2 + t * I)‖ = |R| := by simp_all
  have hre : |z.re - 2| ≤ |R| := by
    calc
      |z.re - 2| = |(z - (2 + t * I)).re| := by simp
      _ ≤ ‖z - (2 + t * I)‖ := Complex.abs_re_le_norm _
      _ = |R| := hdist
  have him : |z.im - t| ≤ |R| := by
    calc
      |z.im - t| = |(z - (2 + t * I)).im| := by simp
      _ ≤ ‖z - (2 + t * I)‖ := Complex.abs_im_le_norm _
      _ = |R| := hdist
  have hzre : z.re ∈ Icc (2 - |R|) (2 + |R|) := by grind
  have : |z.im| ≤ |t| + |R| := by grind
  have hrepr : (z.re : ℂ) + z.im * I = z := by simp
  rw [← hrepr]
  calc
    ‖poleClearedCompletedDedekindZetaContinuation K
        ((z.re : ℂ) + z.im * I)‖ ≤
        poleClearedCompletedDedekindZetaVerticalBound K
            (2 - |R|) (2 + |R|) * (1 + |z.im|) ^ 2 :=
      norm_poleClearedCompletedDedekindZetaContinuation_vertical_le K hzre
    _ ≤ poleClearedCompletedDedekindZetaVerticalBound K
            (2 - |R|) (2 + |R|) * (1 + |t| + |R|) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply pow_le_pow_left₀
        · positivity
        · linarith
      · exact poleClearedCompletedDedekindZetaVerticalBound_nonneg K _ _
    _ ≤ completedZetaMovingCircleBound K R t := le_max_right _ _

theorem card_completedDedekindZetaZerosInClosedRectangle_le_movingJensen
    {a b u v r R t : ℝ}
    (hr : 0 < |r|) (hrR : |r| < |R|)
    (hc : poleClearedCompletedDedekindZetaContinuation K (2 + t * I) ≠ 0)
    (hrect :
      Icc a b ×ℂ Icc u v ⊆ Metric.closedBall (2 + t * I) |r|) :
    ((completedDedekindZetaZerosInClosedRectangle K a b u v).card : ℝ) ≤
      Real.log
          (completedZetaMovingCircleBound K R t /
            ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖) /
        Real.log (R / r) := by
  exact card_completedDedekindZetaZerosInClosedRectangle_le_jensen K
    hr hrR (one_le_completedZetaMovingCircleBound K R t) hc
    (fun z hz ↦ norm_poleClearedCompletedZeta_le_movingCircleBound K R t hz)
    hrect

end NumberField.Odlyzko

end

section

open Complex Metric Set

namespace NumberField.Odlyzko

theorem norm_le_on_closedBall_of_norm_le_on_sphere
    {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall c R) :
    ‖f z‖ ≤ M := by
  apply norm_le_of_forall_mem_frontier_norm_le
    (U := ball c R) isBounded_ball
    (DifferentiableOn.diffContOnCl fun w hw ↦
      (hf w (closure_ball_subset_closedBall hw))
        |>.differentiableAt.differentiableWithinAt)
  · intro w hw
    exact hbound w (frontier_ball_subset_sphere hw)
  · rwa [closure_ball c hR.ne']

end NumberField.Odlyzko

end

section

open Complex Set

namespace NumberField.Odlyzko

theorem norm_deriv_le_of_re_le_on_ball
    {F : ℂ → ℂ} {R r A : ℝ}
    (hR : 0 < R) (_hr : 0 ≤ r) (hrR : r < R) (hA : 0 < A)
    (hF : DifferentiableOn ℂ F (Metric.ball 0 R))
    (hFre : ∀ z ∈ Metric.ball 0 R, (F z).re ≤ A)
    (hF0 : F 0 = 0)
    {w : ℂ} (hw : w ∈ Metric.closedBall 0 r) :
    ‖deriv F w‖ ≤ 4 * A * (R + r) / (R - r) ^ 2 := by
  let d := (R - r) / 2
  let q := (R + r) / 2
  have hd : 0 < d := by grind
  have hqR : q < R := by grind
  have hwNorm : ‖w‖ ≤ r := by simp_all
  have hsphere :
      ∀ z ∈ Metric.sphere w d,
        ‖F z‖ ≤ 2 * A * (R + r) / (R - r) := by
    intro z hz
    have hzw : ‖z - w‖ = d := by simp_all
    have hzNorm : ‖z‖ ≤ q := by
      calc
        ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
          simpa [add_comm] using norm_le_norm_add_norm_sub' z w
        _ ≤ r + d := add_le_add hwNorm hzw.le
        _ = q := by grind
    have hzball : z ∈ Metric.ball 0 R := by
      simpa [Metric.mem_ball, dist_zero_right] using hzNorm.trans_lt hqR
    have hborel :=
      Complex.borelCaratheodory_zero hA hF
        (fun x hx ↦ hFre x hx) hR hzball hF0
    calc
      ‖F z‖ ≤ 2 * A * ‖z‖ / (R - ‖z‖) := hborel
      _ ≤ 2 * A * q / (R - q) := by
        have hzR : ‖z‖ < R := hzNorm.trans_lt hqR
        have hmono : ‖z‖ / (R - ‖z‖) ≤ q / (R - q) := by
          rw [div_le_div_iff₀ (sub_pos.mpr hzR) (sub_pos.mpr hqR)]
          nlinarith
        calc
          2 * A * ‖z‖ / (R - ‖z‖) =
              (2 * A) * (‖z‖ / (R - ‖z‖)) := by ring
          _ ≤ (2 * A) * (q / (R - q)) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
          _ = 2 * A * q / (R - q) := by ring
      _ = 2 * A * (R + r) / (R - r) := by grind
  have hclosed :
      Metric.closedBall w d ⊆ Metric.ball 0 R := by
    intro z hz
    have hzw : ‖z - w‖ ≤ d := by
      simpa [Metric.mem_closedBall, dist_eq] using hz
    have hzNorm : ‖z‖ ≤ q := by
      calc
        ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
          simpa [add_comm] using norm_le_norm_add_norm_sub' z w
        _ ≤ r + d := add_le_add hwNorm hzw
        _ = q := by grind
    simpa [Metric.mem_ball, dist_zero_right] using hzNorm.trans_lt hqR
  have hcauchy :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (c := w) (R := d) (C := 2 * A * (R + r) / (R - r))
      hd (by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball w hd.ne']
        exact hF.mono hclosed) hsphere
  calc
    ‖deriv F w‖ ≤ (2 * A * (R + r) / (R - r)) / d := hcauchy
    _ = 4 * A * (R + r) / (R - r) ^ 2 := by grind

end NumberField.Odlyzko

end

section

open Complex Set

namespace NumberField.Odlyzko

theorem AnalyticOnNhd.exists_analyticLog_on_ball
    {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R))
    (hgn : ∀ z ∈ Metric.ball c R, g z ≠ 0) :
    ∃ L : ℂ → ℂ,
      L c = Complex.log (g c) ∧
      (∀ z ∈ Metric.ball c R,
        HasDerivAt L (logDeriv g z) z) ∧
      ∀ z ∈ Metric.ball c R, Complex.exp (L z) = g z := by
  have hc : c ∈ Metric.ball c R := Metric.mem_ball_self hR
  have hlogDiff :
      DifferentiableOn ℂ (logDeriv g) (Metric.ball c R) := by
    intro z hz
    change DifferentiableWithinAt ℂ (fun w ↦ deriv g w / g w)
      (Metric.ball c R) z
    exact (hg.deriv z hz).differentiableAt.div
      (hg z hz).differentiableAt (hgn z hz) |>.differentiableWithinAt
  obtain ⟨L, hLc, hL⟩ :=
    hlogDiff.isExactOn_ball.with_val_at c (Complex.log (g c))
  refine ⟨L, hLc, hL, ?_⟩
  let q : ℂ → ℂ := (Complex.exp ∘ L) * g⁻¹
  have hqdiff : DifferentiableOn ℂ q (Metric.ball c R) := by
    intro z hz
    exact ((Complex.hasDerivAt_exp (L z)).comp z (hL z hz)).differentiableAt.mul
      ((hg z hz).differentiableAt.inv (hgn z hz)) |>.differentiableWithinAt
  have hqderiv : Set.EqOn (deriv q) 0 (Metric.ball c R) := by
    intro z hz
    have hgz := (hg z hz).differentiableAt.hasDerivAt
    have hq :
        HasDerivAt q 0 z := by
      have hprod :=
        ((Complex.hasDerivAt_exp (L z)).comp z (hL z hz)).mul
          (hgz.inv (hgn z hz))
      change HasDerivAt (Complex.exp ∘ L * g⁻¹) 0 z
      apply hprod.congr_deriv
      rw [logDeriv_apply]
      simp only [Function.comp_apply, Pi.inv_apply]
      grind
    exact hq.deriv
  have hqconst (z : ℂ) (hz : z ∈ Metric.ball c R) : q z = q c :=
    IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball
      (convex_ball c R).isPreconnected hqdiff hqderiv hz hc
  have hqc : q c = 1 := by
    simp only [q, Pi.mul_apply, Function.comp_apply, Pi.inv_apply]
    rw [hLc, Complex.exp_log (hgn c hc)]
    simp_all
  intro z hz
  have hqz : q z = 1 := (hqconst z hz).trans hqc
  simp only [q, Pi.mul_apply, Function.comp_apply, Pi.inv_apply] at hqz
  grind

end NumberField.Odlyzko

end

section

open Complex Set

namespace NumberField.Odlyzko

theorem norm_logDeriv_le_of_zeroFree_on_ball
    {g : ℂ → ℂ} {c z : ℂ} {R r M A : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hM : 0 < M) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R))
    (hgn : ∀ w ∈ Metric.ball c R, g w ≠ 0)
    (hbound : ∀ w ∈ Metric.ball c R, ‖g w‖ ≤ M)
    (hcenter : Real.log M - Real.log ‖g c‖ ≤ A)
    (hz : z ∈ Metric.closedBall c r) :
    ‖logDeriv g z‖ ≤ 4 * A * (R + r) / (R - r) ^ 2 := by
  obtain ⟨L, hLc, hLderiv, hLexp⟩ :=
    AnalyticOnNhd.exists_analyticLog_on_ball hR hg hgn
  let F : ℂ → ℂ := fun w ↦ L (c + w) - L c
  have hFdiff : DifferentiableOn ℂ F (Metric.ball 0 R) := by
    intro w hw
    have hcw : c + w ∈ Metric.ball c R := by simp_all
    exact ((hLderiv (c + w) hcw).comp w
      ((hasDerivAt_const w c).add (hasDerivAt_id w))).sub_const _
      |>.differentiableAt.differentiableWithinAt
  have hreal (w : ℂ) (hw : w ∈ Metric.ball c R) :
      (L w).re = Real.log ‖g w‖ := by
    rw [← hLexp w hw, Complex.norm_exp, Real.log_exp]
  have hFre : ∀ w ∈ Metric.ball 0 R, (F w).re ≤ A := by
    intro w hw
    have hcw : c + w ∈ Metric.ball c R := by simp_all
    have hcball : c ∈ Metric.ball c R := Metric.mem_ball_self hR
    have hgwpos : 0 < ‖g (c + w)‖ := norm_pos_iff.mpr (hgn (c + w) hcw)
    have hlog :
        Real.log ‖g (c + w)‖ ≤ Real.log M :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hgwpos) (Set.mem_Ioi.mpr hM) (hbound (c + w) hcw)
    dsimp [F]
    grind
  have hF0 : F 0 = 0 := by simp [F]
  let w := z - c
  have hw : w ∈ Metric.closedBall 0 r := by
    simpa [w, Metric.mem_closedBall, dist_eq, norm_sub_rev] using hz
  have hmain :=
    norm_deriv_le_of_re_le_on_ball hR hr hrR hA hFdiff hFre hF0 hw
  have hzball : z ∈ Metric.ball c R :=
    Metric.closedBall_subset_ball hrR hz
  have hFderiv :
      deriv F w = logDeriv g z := by
    have hcz : c + w = z := by grind
    have hLz := hLderiv z hzball
    rw [← hcz] at hLz
    have h :=
      (hLz.comp w
        ((hasDerivAt_const w c).add (hasDerivAt_id w))).sub_const (L c)
    have h' : deriv F w = logDeriv g (c + w) := by
      simpa [F] using h.deriv
    simp_all
  simp_all

end NumberField.Odlyzko

end

section

open Complex Metric Set

namespace NumberField.Odlyzko

open Classical in
theorem norm_logDeriv_le_of_canonical_factorization
    {f : ℂ → ℂ} {z : ℂ} {r R δ M A B : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hδ : 0 < δ) (hM : 0 < M) (hA : 0 < A)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hc : f 0 ≠ 0)
    (hboundary : ∀ w ∈ sphere 0 R, f w ≠ 0)
    (hbound : ∀ w ∈ sphere 0 R, ‖f w‖ ≤ M)
    (hcenter : Real.log M - Real.log ‖f 0‖ ≤ A)
    (hz : z ∈ closedBall 0 r) (hfz : f z ≠ 0)
    (hsep : ∀ u ∈
      (MeromorphicOn.divisor f (ball 0 R)).support,
        δ ≤ ‖z - u‖)
    (hmass :
      ((∑ᶠ u, MeromorphicOn.divisor f (ball 0 R) u : ℤ) : ℝ) ≤ B) :
    ‖logDeriv f z‖ ≤
      (B / δ + B / (R - r)) +
        4 * A * (R + r) / (R - r) ^ 2 := by
  let D := MeromorphicOn.divisor f (ball 0 R)
  let P := centeredCanonicalZeroProduct 0 R D
  obtain ⟨g, hg, hgn, heq, hgboundary, hcenterNorm⟩ :=
    AnalyticOnNhd.exists_canonicalZeroFactor_on_ball_zero
      hR hf hc hboundary
  have hDfin : D.support.Finite :=
    hf.meromorphicOn.divisor_ball_support_finite
  have hDnonneg : ∀ u, 0 ≤ D u := by
    intro u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hf.mono ball_subset_closedBall) u
  have hDinside : ∀ u ∈ D.support, u ∈ ball 0 R :=
    divisor_ball_support_subset
  have hzBall : z ∈ ball 0 R := by
    rw [mem_ball, mem_closedBall] at *
    grind
  have hzD : z ∉ D.support := by
    intro hzSupport
    have := hsep z hzSupport
    simp at this
    linarith
  have hgz : g z ≠ 0 :=
    hgn z (ball_subset_closedBall hzBall)
  have heqz : f z = P z * g z := by
    simpa [P, D] using heq (ball_subset_closedBall hzBall)
  have hPz : P z ≠ 0 := by simp_all
  have hPanalytic : AnalyticOnNhd ℂ P (closedBall 0 R) := by
    exact analyticOnNhd_centeredCanonicalZeroProduct hDnonneg hDinside
  have hlogEq :
      logDeriv f z = logDeriv P z + logDeriv g z := by
    have heqBall : EqOn f (P * g) (ball 0 R) := by
      intro w hw
      simpa [P, D] using heq (ball_subset_closedBall hw)
    rw [logDeriv_apply, heqBall.deriv isOpen_ball hzBall,
      heqBall hzBall, logDeriv_apply]
    exact logDeriv_mul z hPz hgz
      ((hPanalytic z (ball_subset_closedBall hzBall)).differentiableAt)
      ((hg z (ball_subset_closedBall hzBall)).differentiableAt)
  have hPbound :
      ‖logDeriv P z‖ ≤ B / δ + B / (R - r) := by
    rw [logDeriv_centeredCanonicalZeroProduct
      hDfin hR hDinside hzBall hzD]
    exact norm_finsum_canonicalLogDeriv_le_of_finsum_le
      hDfin hDnonneg hδ hR hr hrR hDinside hz
      (by grind) (by grind)
  have hgBound : ∀ w ∈ ball 0 R, ‖g w‖ ≤ M := by
    intro w hw
    apply norm_le_on_closedBall_of_norm_le_on_sphere hR hg
      (fun v hv ↦ (hgboundary v hv).le.trans (hbound v hv))
    exact ball_subset_closedBall hw
  have hcenterG : Real.log M - Real.log ‖g 0‖ ≤ A := by
    have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hc
    have hg0pos : 0 < ‖g 0‖ :=
      norm_pos_iff.mpr (hgn 0 (mem_closedBall_self hR.le))
    have hlogle : Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hf0pos) (Set.mem_Ioi.mpr hg0pos) hcenterNorm
    linarith
  have hgLog :
      ‖logDeriv g z‖ ≤
        4 * A * (R + r) / (R - r) ^ 2 :=
    norm_logDeriv_le_of_zeroFree_on_ball
      hR hr hrR hM hA
      (hg.mono ball_subset_closedBall)
      (fun w hw ↦ hgn w (ball_subset_closedBall hw))
      hgBound hcenterG hz
  rw [hlogEq]
  exact (norm_add_le _ _).trans (add_le_add hPbound hgLog)

open Classical in
theorem norm_logDeriv_le_of_canonical_factorization_centered
    {f : ℂ → ℂ} {c z : ℂ} {r R δ M A B : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hδ : 0 < δ) (hM : 0 < M) (hA : 0 < A)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hc : f c ≠ 0)
    (hboundary : ∀ w ∈ sphere c R, f w ≠ 0)
    (hbound : ∀ w ∈ sphere c R, ‖f w‖ ≤ M)
    (hcenter : Real.log M - Real.log ‖f c‖ ≤ A)
    (hz : z ∈ closedBall c r) (hfz : f z ≠ 0)
    (hsep : ∀ u ∈
      (MeromorphicOn.divisor (fun w ↦ f (c + w)) (ball 0 R)).support,
        δ ≤ ‖(z - c) - u‖)
    (hmass :
      ((∑ᶠ u,
        MeromorphicOn.divisor (fun w ↦ f (c + w)) (ball 0 R) u : ℤ) : ℝ) ≤ B) :
    ‖logDeriv f z‖ ≤
      (B / δ + B / (R - r)) +
        4 * A * (R + r) / (R - r) ^ 2 := by
  let F : ℂ → ℂ := fun w ↦ f (c + w)
  let w : ℂ := z - c
  have hF : AnalyticOnNhd ℂ F (closedBall 0 R) := by
    intro v hv
    have hcv : c + v ∈ closedBall c R := by simp_all
    have hshift : AnalyticAt ℂ (fun x : ℂ ↦ c + x) v := by
      fun_prop
    exact AnalyticAt.comp
      (g := f) (f := fun x : ℂ ↦ c + x) (x := v)
      (hf (c + v) hcv) hshift
  have hw : w ∈ closedBall 0 r := by
    simpa [w, mem_closedBall, dist_eq] using hz
  have hFbound : ∀ v ∈ sphere 0 R, ‖F v‖ ≤ M := by
    intro v hv
    apply hbound
    simp_all
  have hFboundary : ∀ v ∈ sphere 0 R, F v ≠ 0 := by
    intro v hv
    apply hboundary
    simp_all
  have hlocal :=
    norm_logDeriv_le_of_canonical_factorization
      hR hr hrR hδ hM hA hF (by simpa [F] using hc)
      hFboundary hFbound (by simpa [F] using hcenter)
      hw (by simpa [F, w] using hfz)
      (by grind)
      (by simpa [F] using hmass)
  have hzBall : z ∈ ball c R := by
    rw [mem_ball, mem_closedBall] at *
    grind
  have hfDiff : DifferentiableAt ℂ f z :=
    (hf z (ball_subset_closedBall hzBall)).differentiableAt
  have hshiftDiff :
      DifferentiableAt ℂ (fun x : ℂ ↦ c + x) w := by
    fun_prop
  have hcomp :=
    logDeriv_comp (f := f) (g := fun x : ℂ ↦ c + x) (x := w)
      (by simpa [w] using hfDiff) hshiftDiff
  have hcw : c + w = z := by
    grind
  rw [deriv_const_add_id, mul_one, hcw] at hcomp
  change ‖logDeriv F w‖ ≤ _ at hlocal
  rw [show F = f ∘ (fun x : ℂ ↦ c + x) by grind, hcomp] at hlocal
  grind

end NumberField.Odlyzko

end

section

open Complex Metric Set

namespace NumberField.Odlyzko

open Classical in
theorem AnalyticOnNhd.eq_zero_of_mem_divisor_support
    {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hz : z ∈ (MeromorphicOn.divisor f U).support) :
    f z = 0 := by
  have hzU : z ∈ U := by
    by_contra hzU
    simp_all
  by_contra hfz
  apply Function.mem_support.mp hz
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hzU,
    (hf z hzU).meromorphicOrderAt_eq,
    (hf z hzU).analyticOrderAt_eq_zero.mpr hfz]
  simp

open Classical in
theorem AnalyticOnNhd.sum_divisor_ball_le
    {f : ℂ → ℂ} {c : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hc : f c ≠ 0)
    (hboundary : ∀ z ∈ sphere c r, f z ≠ 0)
    (f_bound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) :
    ((∑ᶠ z, MeromorphicOn.divisor f (ball c r) z : ℤ) : ℝ) ≤
      Real.log (M / ‖f c‖) / Real.log (R / r) := by
  have heq :=
    divisor_ball_eq_divisor_closedBall_of_boundary_ne
      (hf.mono (closedBall_subset_closedBall hrR.le)) hboundary
  have hfinsum :
      (∑ᶠ z, MeromorphicOn.divisor f (ball c r) z : ℤ) =
        ∑ᶠ z, MeromorphicOn.divisor f (closedBall c r) z := by simp_all
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by grind
  have f_bound' : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M := by grind
  rw [hfinsum]
  have hJ :=
    hf'.sum_divisor_le
      (show 0 < |r| by grind)
      (show |r| < |R| by
        grind)
      hM hc f_bound'
  grind

end NumberField.Odlyzko

end

section

open Complex NumberField Metric Set

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed zeta canonical jensen coefficient used in the Odlyzko-bound argument. -/
noncomputable def completedZetaCanonicalJensenCoefficient : ℝ :=
  1 / Real.log (6 / 5)

open Classical in
theorem completedZetaCanonicalJensenCoefficient_pos :
    0 < completedZetaCanonicalJensenCoefficient := by
  unfold completedZetaCanonicalJensenCoefficient
  positivity

open Classical in
theorem norm_logDeriv_poleClearedCompletedZeta_le_of_local_separation
    {t δ A : ℝ} (hδ : 0 < δ) (hA : 0 < A)
    (hcenter :
      Real.log (completedZetaMovingCircleBound K 6 t) -
          Real.log
            ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall (2 + t * I) 3)
    (hfz : poleClearedCompletedDedekindZetaContinuation K z ≠ 0)
    (hsep : ∀ p ∈ ball (2 + t * I) 5,
      poleClearedCompletedDedekindZetaContinuation K p = 0 →
      δ ≤ ‖z - p‖) :
    ‖logDeriv (poleClearedCompletedDedekindZetaContinuation K) z‖ ≤
      (A * completedZetaCanonicalJensenCoefficient / δ +
        A * completedZetaCanonicalJensenCoefficient) +
      32 * A := by
  let Ξ := poleClearedCompletedDedekindZetaContinuation K
  let c : ℂ := 2 + t * I
  let M : ℝ := completedZetaMovingCircleBound K 6 t
  have hMone : 1 ≤ M := one_le_completedZetaMovingCircleBound K 6 t
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hMone
  have hΞ : AnalyticOnNhd ℂ Ξ (closedBall c 6) :=
    (analyticOnNhd_poleClearedCompletedDedekindZetaContinuation K).mono
      (subset_univ _)
  have hc : Ξ c ≠ 0 := by
    have hs : 1 < c.re := by simp [c]
    exact poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
      (by simp_all)
  obtain ⟨R, ⟨hR4, hR5⟩, hboundary⟩ :=
    AnalyticOnNhd.exists_zeroFree_sphere
      (show (0 : ℝ) ≤ 4 by norm_num) (show (4 : ℝ) < 5 by norm_num)
      (hΞ.mono (closedBall_subset_closedBall (by norm_num))) hc
  have hRpos : 0 < R := by linarith
  have hR6 : R < 6 := by linarith
  have houter :
      ∀ w ∈ sphere c 6, ‖Ξ w‖ ≤ M := by
    intro w hw
    exact norm_poleClearedCompletedZeta_le_movingCircleBound K 6 t
      (by grind)
  have hboundR : ∀ w ∈ sphere c R, ‖Ξ w‖ ≤ M := by
    intro w hw
    apply norm_le_on_closedBall_of_norm_le_on_sphere
      (show (0 : ℝ) < 6 by norm_num) hΞ houter
    rw [mem_closedBall, mem_sphere] at *
    linarith
  let F : ℂ → ℂ := fun w ↦ Ξ (c + w)
  have hF : AnalyticOnNhd ℂ F (closedBall 0 6) := by
    intro w hw
    have hcw : c + w ∈ closedBall c 6 := by simp_all
    have hshift : AnalyticAt ℂ (fun x : ℂ ↦ c + x) w := by
      fun_prop
    exact AnalyticAt.comp
      (g := Ξ) (f := fun x : ℂ ↦ c + x) (x := w)
      (hΞ (c + w) hcw) hshift
  have hFboundary : ∀ w ∈ sphere 0 R, F w ≠ 0 := by
    intro w hw
    apply hboundary (c + w)
    simp_all
  have hFouter : ∀ w ∈ sphere 0 6, ‖F w‖ ≤ M := by
    intro w hw
    apply houter (c + w)
    simp_all
  let B : ℝ := A * completedZetaCanonicalJensenCoefficient
  have hmass :
      ((∑ᶠ u, MeromorphicOn.divisor F (ball 0 R) u : ℤ) : ℝ) ≤ B := by
    have hJ :=
      AnalyticOnNhd.sum_divisor_ball_le hRpos hR6 hMone hF
        (by simpa [F] using hc) hFboundary hFouter
    have hnum :
        Real.log (M / ‖F 0‖) ≤ A := by
      rw [Real.log_div (ne_of_gt hMpos)
        (norm_ne_zero_iff.mpr (by simpa [F] using hc))]
      simpa [F, M, c] using hcenter
    have hlogpos : 0 < Real.log (6 / 5) := by positivity
    have hden :
        Real.log (6 / 5) ≤ Real.log (6 / R) := by
      apply Real.strictMonoOn_log.monotoneOn
      · norm_num
      · simp_all
      · apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6)
          (by linarith) (by linarith)
    have hdenpos : 0 < Real.log (6 / R) := hlogpos.trans_le hden
    calc
      ((∑ᶠ u, MeromorphicOn.divisor F (ball 0 R) u : ℤ) : ℝ) ≤
          Real.log (M / ‖F 0‖) / Real.log (6 / R) := hJ
      _ ≤ A / Real.log (6 / R) :=
        div_le_div_of_nonneg_right hnum hdenpos.le
      _ ≤ A / Real.log (6 / 5) := by
        exact div_le_div₀ hA.le le_rfl hlogpos hden
      _ = B := by
        simp [B, completedZetaCanonicalJensenCoefficient]
        ring
  have hsepF :
      ∀ u ∈ (MeromorphicOn.divisor F (ball 0 R)).support,
        δ ≤ ‖(z - c) - u‖ := by
    intro u hu
    have huBall : u ∈ ball 0 R := divisor_ball_support_subset hu
    have hzero : F u = 0 :=
      AnalyticOnNhd.eq_zero_of_mem_divisor_support
        (hF.mono ((ball_subset_ball hR6.le).trans ball_subset_closedBall)) hu
    have hcu : c + u ∈ ball c 5 := by
      rw [mem_ball, dist_eq]
      have : ‖u‖ < R := by simp_all
      simpa using this.trans hR5
    have := hsep (c + u) hcu (by grind)
    (convert this using 1; ring_nf)
  have hlocal :=
    norm_logDeriv_le_of_canonical_factorization_centered
      (f := Ξ) (c := c) (z := z)
      hRpos (show (0 : ℝ) ≤ 3 by norm_num) (by linarith)
      hδ hMpos hA
      (hΞ.mono (closedBall_subset_closedBall hR6.le))
      hc hboundary hboundR (by grind)
      (by grind) hfz hsepF hmass
  have hBnonneg : 0 ≤ B := by
    exact mul_nonneg hA.le completedZetaCanonicalJensenCoefficient_pos.le
  calc
    ‖logDeriv Ξ z‖ ≤
        (B / δ + B / (R - 3)) +
          4 * A * (R + 3) / (R - 3) ^ 2 := hlocal
    _ ≤ (B / δ + B) + 32 * A := by
      have hgapPos : 0 < R - 3 := by linarith
      have hfrac : B / (R - 3) ≤ B := by
        exact (div_le_iff₀ hgapPos).2
          (by nlinarith)
      have hbor :
          4 * A * (R + 3) / (R - 3) ^ 2 ≤ 32 * A := by
        rw [div_le_iff₀ (sq_pos_of_pos hgapPos)]
        nlinarith [sq_nonneg (R - 4)]
      grind
    _ = (A * completedZetaCanonicalJensenCoefficient / δ +
          A * completedZetaCanonicalJensenCoefficient) + 32 * A := by grind

end NumberField.Odlyzko

end

section

open Complex NumberField NumberField.InfinitePlace

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A completed zeta radius six vertical coefficient used in the Odlyzko-bound argument. -/
noncomputable def completedZetaRadiusSixVerticalCoefficient : ℝ :=
  max 1 (poleClearedCompletedDedekindZetaVerticalBound K (-4) 8)

/-- A completed zeta center log linear expression used in the Odlyzko-bound argument. -/
noncomputable def completedZetaCenterLogLinearExpression (t : ℝ) : ℝ :=
  completedZetaRadiusSixVerticalCoefficient K + 2 * (7 + |t|) +
    Real.log (dedekindZetaInverseVerticalMajorant K) -
    (nrComplexPlaces K : ℝ) / 2 *
      Real.log complexPlaceGammaVerticalLowerConstant +
    (nrComplexPlaces K : ℝ) / 2 * Real.pi * |t|

/-- A completed zeta center log linear bound used in the Odlyzko-bound argument. -/
noncomputable def completedZetaCenterLogLinearBound (t : ℝ) : ℝ :=
  max 1 (completedZetaCenterLogLinearExpression K t)

omit [IsTotallyComplex K] in
theorem one_le_completedZetaCenterLogLinearBound (t : ℝ) :
    1 ≤ completedZetaCenterLogLinearBound K t :=
  le_max_left _ _

private theorem neg_log_le_of_pow_mul_exp_le_sq
    {g C X u : ℝ} {n : ℕ}
    (hg : 0 < g) (hC : 0 < C) (hX : 0 < X)
    (h : (g * Real.exp (-u)) ^ n ≤ C ^ 2 * X ^ 2) :
    -Real.log X ≤
      Real.log C - (n : ℝ) / 2 * Real.log g + (n : ℝ) / 2 * u := by
  have hleft : 0 < (g * Real.exp (-u)) ^ n := by positivity
  have hlog := Real.log_le_log hleft h
  rw [Real.log_pow, Real.log_mul (ne_of_gt hg) (ne_of_gt (Real.exp_pos _)),
    Real.log_exp, Real.log_mul (pow_ne_zero _ (ne_of_gt hC))
      (pow_ne_zero _ (ne_of_gt hX)), Real.log_pow, Real.log_pow] at hlog
  grind

theorem neg_log_norm_poleClearedCompletedZeta_two_add_mul_I_le
    {t : ℝ} (ht : 1 ≤ |t|) :
    -Real.log
        ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ ≤
      Real.log (dedekindZetaInverseVerticalMajorant K) -
        (nrComplexPlaces K : ℝ) / 2 *
          Real.log complexPlaceGammaVerticalLowerConstant +
        (nrComplexPlaces K : ℝ) / 2 * Real.pi * |t| := by
  have hX : 0 <
      ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ :=
    norm_pos_iff.mpr
      (poleClearedCompletedDedekindZetaContinuation_ne_zero_of_one_lt_re K
        (by simp))
  have hlower :
      (complexPlaceGammaVerticalLowerConstant *
          Real.exp (-(Real.pi * |t|))) ^ nrComplexPlaces K ≤
        dedekindZetaInverseVerticalMajorant K ^ 2 *
          ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ ^ 2 := by
    simpa [mul_assoc] using
      complexGammaExponential_pow_le_majorant_sq_mul_completedZeta_sq K ht
  have h := neg_log_le_of_pow_mul_exp_le_sq
    (g := complexPlaceGammaVerticalLowerConstant)
    (C := dedekindZetaInverseVerticalMajorant K)
    (X := ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖)
    (u := Real.pi * |t|) (n := nrComplexPlaces K)
    complexPlaceGammaVerticalLowerConstant_pos
    (lt_of_lt_of_le zero_lt_one
      (one_le_dedekindZetaInverseVerticalMajorant K))
    hX hlower
  grind

omit [IsTotallyComplex K] in
theorem log_completedZetaMovingCircleBound_six_le (t : ℝ) :
    Real.log (completedZetaMovingCircleBound K 6 t) ≤
      completedZetaRadiusSixVerticalCoefficient K + 2 * (7 + |t|) := by
  let V : ℝ := poleClearedCompletedDedekindZetaVerticalBound K (-4) 8
  let D : ℝ := completedZetaRadiusSixVerticalCoefficient K
  let Q : ℝ := 7 + |t|
  have hD : 1 ≤ D := le_max_left _ _
  have hVD : V ≤ D := le_max_right _ _
  have hQ : 1 ≤ Q := by grind
  have hmajor :
      completedZetaMovingCircleBound K 6 t ≤ D * Q ^ 2 := by
    have hraw : max 1 (V * Q ^ 2) ≤ D * Q ^ 2 := by
      apply max_le
      · nlinarith [sq_nonneg Q]
      · apply mul_le_mul_of_nonneg_right hVD
        positivity
    simpa [completedZetaMovingCircleBound, V, Q,
      show (2 : ℝ) - 6 = -4 by norm_num,
      show (2 : ℝ) + 6 = 8 by norm_num,
      show 1 + |t| + 6 = 7 + |t| by ring] using hraw
  calc
    Real.log (completedZetaMovingCircleBound K 6 t) ≤
        Real.log (D * Q ^ 2) :=
      Real.log_le_log
        (lt_of_lt_of_le zero_lt_one
          (one_le_completedZetaMovingCircleBound K 6 t)) hmajor
    _ = Real.log D + 2 * Real.log Q := by
      rw [Real.log_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one hD))
        (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hQ))),
        Real.log_pow]
      norm_num
    _ ≤ D + 2 * Q := by
      gcongr
      · exact Real.log_le_self (zero_le_one.trans hD)
      · exact Real.log_le_self (zero_le_one.trans hQ)
    _ = completedZetaRadiusSixVerticalCoefficient K + 2 * (7 + |t|) := rfl

theorem completedZeta_center_log_gap_le
    {t : ℝ} (ht : 1 ≤ |t|) :
    Real.log (completedZetaMovingCircleBound K 6 t) -
        Real.log
          ‖poleClearedCompletedDedekindZetaContinuation K (2 + t * I)‖ ≤
      completedZetaCenterLogLinearBound K t := by
  apply le_trans ?_ (le_max_right _ _)
  dsimp [completedZetaCenterLogLinearExpression]
  linarith [log_completedZetaMovingCircleBound_six_le K t,
    neg_log_norm_poleClearedCompletedZeta_two_add_mul_I_le K ht]

end NumberField.Odlyzko

end
