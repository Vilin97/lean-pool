/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMetric
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Ball
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Cube
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.DerivativeBounds
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Profile
import LeanPool.CoarseGraining.Homogenization.Sobolev.WeakDerivatives
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! # Quantitative Cutoff -/

noncomputable section

open Set
open scoped Topology

namespace Homogenization

/-!
# Quantitative smooth cutoffs

This file provides the quantitative cutoff interfaces used by local Sobolev and
Caccioppoli arguments.  The ball version is the standard radial cutoff between
two concentric balls.  The cube version is the analogous cutoff between two
concentric subcubes of a triadic cube.

The derivative bounds are expressed using dimensional constants.  The default
norm on `Vec d` is the product/sup norm, so Euclidean-ball cutoffs acquire
dimension factors when their derivatives are measured with Lean's operator norm.
-/

/-- Dimensional first-derivative constant for the ball cutoff interface.

The factor `d` accounts for measuring derivatives on `Vec d` using the default
sup/product norm. -/
def quantitativeBallCutoffGradientConst (d : ℕ) : ℝ :=
  8 * (d : ℝ) * smoothTransitionProfile.derivBound

/-- Dimensional Hessian constant for the ball cutoff interface. -/
def quantitativeBallCutoffHessianConst (d : ℕ) : ℝ :=
  32 * (d : ℝ) ^ 2 *
    max 1 (max smoothTransitionProfile.derivBound smoothTransitionProfile.secondDerivBound)

/-- Dimensional first-derivative constant for the cube cutoff interface. -/
def quantitativeCubeCutoffGradientConst (d : ℕ) : ℝ :=
  8 * (d : ℝ) * smoothTransitionProfile.derivBound

/-- Dimensional Hessian constant for the cube cutoff interface. -/
def quantitativeCubeCutoffHessianConst (d : ℕ) : ℝ :=
  8 * (d : ℝ) ^ 2 *
    (max 1
      (max smoothTransitionProfile.derivBound smoothTransitionProfile.secondDerivBound)) ^ 2

/-- A quantitative smooth cutoff between two concentric balls. -/
structure QuantitativeBallCutoff {d : ℕ} (x₀ : Vec d) (r R : ℝ) where
  toFun : Vec d → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun
  support_subset : tsupport toFun ⊆ euclideanBall x₀ R
  nonneg : ∀ x, 0 ≤ toFun x
  le_one : ∀ x, toFun x ≤ 1
  eq_one_on_inner : ∀ x ∈ euclideanBall x₀ r, toFun x = 1
  gradient_bound : ∀ x, ‖fderiv ℝ toFun x‖ ≤
    quantitativeBallCutoffGradientConst d / (R - r)
  hessian_bound :
    ∀ x, ‖iteratedFDeriv ℝ 2 toFun x‖ ≤
      quantitativeBallCutoffHessianConst d / (R - r) ^ 2

namespace QuantitativeBallCutoff

instance {d : ℕ} {x₀ : Vec d} {r R : ℝ} :
    CoeFun (QuantitativeBallCutoff x₀ r R) (fun _ => Vec d → ℝ) where
  coe η := η.toFun

/-- Canonical smooth ball cutoff formula using `Real.smoothTransition`.

The extra support radius `s` leaves a collar between the support and `B_R`,
which is necessary for `tsupport` to be contained in the open ball. -/
def canonicalFun {d : ℕ} (x₀ : Vec d) (r s : ℝ) : Vec d → ℝ :=
  QuantitativeTransitionProfile.ballCutoff smoothTransitionProfile.quantitativeProfile x₀ r s

theorem canonicalFun_smooth {d : ℕ} (x₀ : Vec d) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) :
    ContDiff ℝ (⊤ : ℕ∞) (canonicalFun x₀ r s) :=
  QuantitativeTransitionProfile.ballCutoff_smooth
    smoothTransitionProfile.quantitativeProfile x₀ hr hrs

theorem canonicalFun_hasCompactSupport {d : ℕ} (x₀ : Vec d) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) :
    HasCompactSupport (canonicalFun x₀ r s) :=
  QuantitativeTransitionProfile.ballCutoff_hasCompactSupport
    smoothTransitionProfile.quantitativeProfile hr hrs

theorem canonicalFun_tsupport_subset_euclideanBall {d : ℕ} (x₀ : Vec d) {r s R : ℝ}
    (hr : 0 < r) (hrs : r < s) (hsR : s < R) :
    tsupport (canonicalFun x₀ r s) ⊆ euclideanBall x₀ R :=
  QuantitativeTransitionProfile.ballCutoff_tsupport_subset_euclideanBall
    smoothTransitionProfile.quantitativeProfile hr hrs hsR

theorem canonicalFun_nonneg {d : ℕ} (x₀ : Vec d) (r s : ℝ) (x : Vec d) :
    0 ≤ canonicalFun x₀ r s x :=
  QuantitativeTransitionProfile.ballCutoff_nonneg
    smoothTransitionProfile.quantitativeProfile x₀ r s x

theorem canonicalFun_le_one {d : ℕ} (x₀ : Vec d) (r s : ℝ) (x : Vec d) :
    canonicalFun x₀ r s x ≤ 1 :=
  QuantitativeTransitionProfile.ballCutoff_le_one
    smoothTransitionProfile.quantitativeProfile x₀ r s x

theorem canonicalFun_eq_one_on_inner {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) {x : Vec d}
    (hx : x ∈ euclideanBall x₀ r) :
    canonicalFun x₀ r s x = 1 :=
  QuantitativeTransitionProfile.ballCutoff_eq_one_of_mem_euclideanBall
    smoothTransitionProfile.quantitativeProfile hr hrs hx

theorem canonicalFun_gradient_bound {d : ℕ} (x₀ : Vec d) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (x : Vec d) :
    ‖fderiv ℝ (canonicalFun x₀ r s) x‖ ≤
      smoothTransitionProfile.derivBound * (2 * (d : ℝ) / (s - r)) :=
  QuantitativeTransitionProfile.norm_fderiv_ballCutoff_le
    smoothTransitionProfile.quantitativeProfile hr hrs x

theorem canonicalFun_hessian_bound {d : ℕ} (x₀ : Vec d) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (x : Vec d) :
    ‖iteratedFDeriv ℝ 2 (canonicalFun x₀ r s) x‖ ≤
      2 * (max 1
        (max smoothTransitionProfile.derivBound smoothTransitionProfile.secondDerivBound)) *
        (2 * (d : ℝ) / (s - r)) ^ 2 :=
  QuantitativeTransitionProfile.norm_iteratedFDeriv_two_ballCutoff_le
    smoothTransitionProfile.quantitativeProfile hr hrs x

theorem exists_bound_fderiv_canonicalFun {d : ℕ} (x₀ : Vec d) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (canonicalFun x₀ r s) x‖ ≤ C :=
  exists_bound_fderiv_of_contDiff_hasCompactSupport
    (canonicalFun_smooth x₀ hr hrs)
    (canonicalFun_hasCompactSupport x₀ hr hrs)

theorem exists_bound_hessian_canonicalFun {d : ℕ} (x₀ : Vec d) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, ‖iteratedFDeriv ℝ 2 (canonicalFun x₀ r s) x‖ ≤ C :=
  exists_bound_iteratedFDeriv_two_of_contDiff_hasCompactSupport
    (canonicalFun_smooth x₀ hr hrs)
    (canonicalFun_hasCompactSupport x₀ hr hrs)

/-- Canonical quantitative ball cutoff between `B_r(x₀)` and `B_R(x₀)`,
using the midpoint radius `(r + R) / 2` as transition scale. -/
noncomputable def canonical {d : ℕ} (x₀ : Vec d) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) : QuantitativeBallCutoff x₀ r R := by
  let s : ℝ := (r + R) / 2
  have hrs : r < s := by
    dsimp [s]
    nlinarith
  have hsR : s < R := by
    dsimp [s]
    nlinarith
  refine
    { toFun := canonicalFun x₀ r s
      smooth := canonicalFun_smooth x₀ hr hrs
      hasCompactSupport := canonicalFun_hasCompactSupport x₀ hr hrs
      support_subset := canonicalFun_tsupport_subset_euclideanBall x₀ hr hrs hsR
      nonneg := canonicalFun_nonneg x₀ r s
      le_one := canonicalFun_le_one x₀ r s
      eq_one_on_inner := by
        intro x hx
        exact canonicalFun_eq_one_on_inner hr hrs hx
      gradient_bound := by
        intro x
        have hbase := canonicalFun_gradient_bound x₀ hr hrs x
        have hs_eq : s - r = (R - r) / 2 := by
          dsimp [s]
          ring
        have hconst :
            smoothTransitionProfile.derivBound * (2 * (d : ℝ) / (s - r))
              = 4 * (d : ℝ) * smoothTransitionProfile.derivBound / (R - r) := by
          rw [hs_eq]
          field_simp [sub_ne_zero.mpr (ne_of_gt hrR)]
          ring
        rw [hconst] at hbase
        calc
          ‖fderiv ℝ (canonicalFun x₀ r s) x‖
              ≤ 4 * (d : ℝ) * smoothTransitionProfile.derivBound / (R - r) := hbase
          _ ≤ quantitativeBallCutoffGradientConst d / (R - r) := by
            have hRR : 0 < R - r := sub_pos.mpr hrR
            have hcoeff :
                4 * (d : ℝ) * smoothTransitionProfile.derivBound
                  ≤ quantitativeBallCutoffGradientConst d := by
              dsimp [quantitativeBallCutoffGradientConst]
              have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
              nlinarith [smoothTransitionProfile.derivBound_nonneg, hd_nonneg]
            exact div_le_div_of_nonneg_right hcoeff (le_of_lt hRR)
      hessian_bound := by
        intro x
        have hbase := canonicalFun_hessian_bound x₀ hr hrs x
        have hs_eq : s - r = (R - r) / 2 := by
          dsimp [s]
          ring
        have hconst :
            2 * (max 1
              (max smoothTransitionProfile.derivBound smoothTransitionProfile.secondDerivBound)) *
              (2 * (d : ℝ) / (s - r)) ^ 2
              =
            quantitativeBallCutoffHessianConst d / (R - r) ^ 2 := by
          rw [hs_eq]
          dsimp [quantitativeBallCutoffHessianConst]
          field_simp [pow_two, sub_ne_zero.mpr (ne_of_gt hrR)]
          ring
        simpa [hconst] using hbase }

end QuantitativeBallCutoff

/-- A quantitative smooth cutoff between two concentric subcubes of a triadic cube. -/
structure QuantitativeCubeCutoff {d : ℕ} (Q : TriadicCube d) (ρ₁ ρ₂ : ℝ) where
  toFun : Vec d → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun
  support_subset : Function.support toFun ⊆ scaledOpenCubeSet Q ρ₂
  nonneg : ∀ x, 0 ≤ toFun x
  le_one : ∀ x, toFun x ≤ 1
  eq_one_on_inner : ∀ x ∈ scaledClosedCubeSet Q ρ₁, toFun x = 1
  gradient_bound : ∀ x,
    ‖fderiv ℝ toFun x‖ ≤
      quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q)
  hessian_bound : ∀ x,
    ‖iteratedFDeriv ℝ 2 toFun x‖ ≤
      quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2)

namespace QuantitativeCubeCutoff

instance {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ} :
    CoeFun (QuantitativeCubeCutoff Q ρ₁ ρ₂) (fun _ => Vec d → ℝ) where
  coe η := η.toFun

/-- Canonical smooth cube cutoff formula using `Real.smoothTransition`. -/
def canonicalFun {d : ℕ} (Q : TriadicCube d) (ρ₁ ρ₂ : ℝ) : Vec d → ℝ :=
  QuantitativeTransitionProfile.cubeCutoff smoothTransitionProfile.quantitativeProfile Q ρ₁ ρ₂

theorem canonicalFun_smooth {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) :
    ContDiff ℝ (⊤ : ℕ∞) (canonicalFun Q ρ₁ ρ₂) :=
  QuantitativeTransitionProfile.cubeCutoff_smooth
    smoothTransitionProfile.quantitativeProfile Q hρ₁ hρ₁₂

theorem canonicalFun_nonneg {d : ℕ} (Q : TriadicCube d)
    (ρ₁ ρ₂ : ℝ) (x : Vec d) :
    0 ≤ canonicalFun Q ρ₁ ρ₂ x :=
  QuantitativeTransitionProfile.cubeCutoff_nonneg
    smoothTransitionProfile.quantitativeProfile Q ρ₁ ρ₂ x

theorem canonicalFun_le_one {d : ℕ} (Q : TriadicCube d)
    (ρ₁ ρ₂ : ℝ) (x : Vec d) :
    canonicalFun Q ρ₁ ρ₂ x ≤ 1 :=
  QuantitativeTransitionProfile.cubeCutoff_le_one
    smoothTransitionProfile.quantitativeProfile Q ρ₁ ρ₂ x

theorem canonicalFun_eq_one_on_inner {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) {x : Vec d}
    (hx : x ∈ scaledClosedCubeSet Q ρ₁) :
    canonicalFun Q ρ₁ ρ₂ x = 1 :=
  QuantitativeTransitionProfile.cubeCutoff_eq_one_of_mem_scaledClosedCubeSet
    smoothTransitionProfile.quantitativeProfile hρ₁ hρ₁₂ hx

theorem canonicalFun_support_subset {d : ℕ} {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) :
    Function.support (canonicalFun Q ρ₁ ρ₂) ⊆ scaledOpenCubeSet Q ρ₂ :=
  QuantitativeTransitionProfile.cubeCutoff_support_subset_scaledOpenCubeSet
    smoothTransitionProfile.quantitativeProfile hρ₁ hρ₁₂

theorem canonicalFun_tsupport_subset_scaledClosedCubeSet {d : ℕ}
    {Q : TriadicCube d} {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) :
    tsupport (canonicalFun Q ρ₁ ρ₂) ⊆ scaledClosedCubeSet Q ρ₂ :=
  QuantitativeTransitionProfile.cubeCutoff_tsupport_subset_scaledClosedCubeSet
    smoothTransitionProfile.quantitativeProfile hρ₁ hρ₁₂

/-- The canonical product cutoff has zero coordinate derivative away from the
corresponding coordinate collar. -/
theorem canonicalFun_fderiv_apply_basisVec_eq_zero_of_abs_sub_center_lt_inner {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂)
    {i : Fin d} {x : Vec d}
    (hx : |x i - cubeCenter Q i| < ρ₁ * cubeRadius Q) :
    (fderiv ℝ (canonicalFun Q ρ₁ ρ₂) x) (basisVec i) = 0 := by
  simpa [canonicalFun] using
    QuantitativeTransitionProfile.fderiv_cubeCutoff_apply_basisVec_eq_zero_of_abs_sub_center_lt_inner
        smoothTransitionProfile.quantitativeProfile Q hρ₁ hρ₁₂ hx

/-- Support form of `canonicalFun_fderiv_apply_basisVec_eq_zero_of_abs_sub_center_lt_inner`. -/
theorem support_fderiv_canonicalFun_apply_basisVec_subset_coord_abs_ge_inner {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂)
    (i : Fin d) :
    Function.support (fun x : Vec d => (fderiv ℝ (canonicalFun Q ρ₁ ρ₂) x) (basisVec i)) ⊆
      {x | ρ₁ * cubeRadius Q ≤ |x i - cubeCenter Q i|} := by
  intro x hx
  by_contra hnot
  exact hx (canonicalFun_fderiv_apply_basisVec_eq_zero_of_abs_sub_center_lt_inner
    Q hρ₁ hρ₁₂ (not_le.mp hnot))

theorem support_fderiv_canonicalFun_apply_basisVec_subset_scaledClosedCubeSet {d : ℕ}
    (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂)
    (i : Fin d) :
    Function.support (fun x : Vec d => (fderiv ℝ (canonicalFun Q ρ₁ ρ₂) x) (basisVec i)) ⊆
      scaledClosedCubeSet Q ρ₂ := by
  intro x hx
  have hx_deriv : x ∈ Function.support (fderiv ℝ (canonicalFun Q ρ₁ ρ₂)) := by
    intro hzero
    exact hx (by simp [hzero])
  exact canonicalFun_tsupport_subset_scaledClosedCubeSet hρ₁ hρ₁₂
    ((support_fderiv_subset (𝕜 := ℝ) (f := canonicalFun Q ρ₁ ρ₂)) hx_deriv)

theorem canonicalFun_gradient_bound {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (x : Vec d) :
    ‖fderiv ℝ (canonicalFun Q ρ₁ ρ₂) x‖ ≤
      (d : ℝ) * smoothTransitionProfile.derivBound *
        (2 / ((ρ₂ - ρ₁) * cubeRadius Q)) :=
  QuantitativeTransitionProfile.norm_fderiv_cubeCutoff_le
    smoothTransitionProfile.quantitativeProfile Q hρ₁ hρ₁₂ x

theorem canonicalFun_hessian_bound {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) (x : Vec d) :
    ‖iteratedFDeriv ℝ 2 (canonicalFun Q ρ₁ ρ₂) x‖ ≤
      2 * (d : ℝ) ^ 2 *
        ((max 1
          (max smoothTransitionProfile.derivBound smoothTransitionProfile.secondDerivBound)) *
          (2 / ((ρ₂ - ρ₁) * cubeRadius Q))) ^ 2 :=
  QuantitativeTransitionProfile.norm_iteratedFDeriv_two_cubeCutoff_le
    smoothTransitionProfile.quantitativeProfile Q hρ₁ hρ₁₂ x

theorem canonicalFun_hasCompactSupport {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) :
    HasCompactSupport (canonicalFun Q ρ₁ ρ₂) := by
  have hρ₂_nonneg : 0 ≤ ρ₂ := le_of_lt (lt_trans hρ₁ hρ₁₂)
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_scaledClosedCubeSet Q hρ₂_nonneg) ?_
  intro x hx
  exact fun i => le_of_lt ((canonicalFun_support_subset hρ₁ hρ₁₂ hx) i)

theorem exists_bound_fderiv_canonicalFun {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (canonicalFun Q ρ₁ ρ₂) x‖ ≤ C :=
  exists_bound_fderiv_of_contDiff_hasCompactSupport
    (canonicalFun_smooth Q hρ₁ hρ₁₂)
    (canonicalFun_hasCompactSupport Q hρ₁ hρ₁₂)

theorem exists_bound_hessian_canonicalFun {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, ‖iteratedFDeriv ℝ 2 (canonicalFun Q ρ₁ ρ₂) x‖ ≤ C :=
  exists_bound_iteratedFDeriv_two_of_contDiff_hasCompactSupport
    (canonicalFun_smooth Q hρ₁ hρ₁₂)
    (canonicalFun_hasCompactSupport Q hρ₁ hρ₁₂)

/-- Canonical quantitative cube cutoff between the concentric subcubes
`scaledClosedCubeSet Q ρ₁` and `scaledOpenCubeSet Q ρ₂`. -/
noncomputable def canonical {d : ℕ} (Q : TriadicCube d) (ρ₁ ρ₂ : ℝ)
    (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ < ρ₂) : QuantitativeCubeCutoff Q ρ₁ ρ₂ := by
  refine
    { toFun := canonicalFun Q ρ₁ ρ₂
      smooth := canonicalFun_smooth Q hρ₁ hρ₁₂
      hasCompactSupport := canonicalFun_hasCompactSupport Q hρ₁ hρ₁₂
      support_subset := by
        intro x hx
        exact canonicalFun_support_subset hρ₁ hρ₁₂ hx
      nonneg := canonicalFun_nonneg Q ρ₁ ρ₂
      le_one := canonicalFun_le_one Q ρ₁ ρ₂
      eq_one_on_inner := by
        intro x hx
        exact canonicalFun_eq_one_on_inner hρ₁ hρ₁₂ hx
      gradient_bound := by
        intro x
        have hbase := canonicalFun_gradient_bound Q hρ₁ hρ₁₂ x
        have hgap_pos : 0 < (ρ₂ - ρ₁) * cubeRadius Q := by
          exact mul_pos (sub_pos.mpr hρ₁₂) (cubeRadius_pos Q)
        have hcoeff :
            (d : ℝ) * smoothTransitionProfile.derivBound * 2
              ≤ quantitativeCubeCutoffGradientConst d := by
          dsimp [quantitativeCubeCutoffGradientConst]
          have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
          nlinarith [hd_nonneg, smoothTransitionProfile.derivBound_nonneg]
        calc
          ‖fderiv ℝ (canonicalFun Q ρ₁ ρ₂) x‖
              ≤ (d : ℝ) * smoothTransitionProfile.derivBound *
                  (2 / ((ρ₂ - ρ₁) * cubeRadius Q)) := hbase
          _ ≤ quantitativeCubeCutoffGradientConst d / ((ρ₂ - ρ₁) * cubeRadius Q) := by
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_right hcoeff (inv_nonneg.mpr (le_of_lt hgap_pos))
      hessian_bound := by
        intro x
        have hbase := canonicalFun_hessian_bound Q hρ₁ hρ₁₂ x
        have hgap_pos : 0 < (ρ₂ - ρ₁) * cubeRadius Q := by
          exact mul_pos (sub_pos.mpr hρ₁₂) (cubeRadius_pos Q)
        have hgap_ne : ((ρ₂ - ρ₁) * cubeRadius Q) ≠ 0 := ne_of_gt hgap_pos
        calc
          ‖iteratedFDeriv ℝ 2 (canonicalFun Q ρ₁ ρ₂) x‖
              ≤ 2 * (d : ℝ) ^ 2 *
                ((max 1
                  (max smoothTransitionProfile.derivBound smoothTransitionProfile.secondDerivBound)) *
                  (2 / ((ρ₂ - ρ₁) * cubeRadius Q))) ^ 2 := hbase
          _ = quantitativeCubeCutoffHessianConst d / (((ρ₂ - ρ₁) * cubeRadius Q) ^ 2) := by
            dsimp [quantitativeCubeCutoffHessianConst]
            field_simp [pow_two, hgap_ne]
            ring }

end QuantitativeCubeCutoff

end Homogenization
