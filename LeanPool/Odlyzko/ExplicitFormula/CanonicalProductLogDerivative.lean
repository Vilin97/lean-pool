/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.CanonicalZeroSumBound
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Canonical Product Log Derivative

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

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
