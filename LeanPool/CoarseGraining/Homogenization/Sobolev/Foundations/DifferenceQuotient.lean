/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.Translation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.EuclideanL2CZ
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareLpSmooth
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.Prod

/-! # Difference Quotient -/

namespace Homogenization

open scoped ENNReal Interval Topology

noncomputable section

/-!
# Coordinate difference quotients

This file starts the difference-quotient API needed for the interior `H2`
regularity proof in the cube Neumann Calderon-Zygmund discharge.  The first
slice is intentionally small: coordinate shifts, forward/backward quotients,
and the smooth/support facts that make the eventual difference-quotient tests
admissible.
-/

/-- Shift a point by `h` in coordinate direction `i`. -/
def euclideanCoordShift {d : ℕ} (h : ℝ) (i : Fin d) (x : Vec d) : Vec d :=
  x + h • basisVec i

@[simp] theorem euclideanCoordShift_apply {d : ℕ}
    (h : ℝ) (i : Fin d) (x : Vec d) :
    euclideanCoordShift h i x = x + h • basisVec i :=
  rfl

@[simp] theorem euclideanCoordShift_zero {d : ℕ} (i : Fin d) (x : Vec d) :
    euclideanCoordShift 0 i x = x := by
  simp [euclideanCoordShift]

@[simp] theorem euclideanCoordShift_zero_step {d : ℕ} (h : ℝ) (i : Fin d) :
    euclideanCoordShift h i 0 = h • basisVec i := by
  simp [euclideanCoordShift]

@[simp] theorem euclideanCoordShift_neg_cancel {d : ℕ}
    (h : ℝ) (i : Fin d) (x : Vec d) :
    euclideanCoordShift (-h) i (euclideanCoordShift h i x) = x := by
  ext k
  by_cases hk : k = i
  · subst hk
    simp [euclideanCoordShift, basisVec]
  · simp [euclideanCoordShift, basisVec, hk]

@[simp] theorem euclideanCoordShift_cancel_neg {d : ℕ}
    (h : ℝ) (i : Fin d) (x : Vec d) :
    euclideanCoordShift h i (euclideanCoordShift (-h) i x) = x := by
  simp

/-- Forward coordinate difference quotient. -/
def euclideanForwardDifferenceQuotient {d : ℕ}
    (h : ℝ) (i : Fin d) (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => (u (euclideanCoordShift h i x) - u x) / h

/-- Backward coordinate difference quotient. -/
def euclideanBackwardDifferenceQuotient {d : ℕ}
    (h : ℝ) (i : Fin d) (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => (u x - u (euclideanCoordShift (-h) i x)) / h

@[simp] theorem euclideanForwardDifferenceQuotient_apply {d : ℕ}
    (h : ℝ) (i : Fin d) (u : Vec d → ℝ) (x : Vec d) :
    euclideanForwardDifferenceQuotient h i u x =
      (u (euclideanCoordShift h i x) - u x) / h :=
  rfl

@[simp] theorem euclideanBackwardDifferenceQuotient_apply {d : ℕ}
    (h : ℝ) (i : Fin d) (u : Vec d → ℝ) (x : Vec d) :
    euclideanBackwardDifferenceQuotient h i u x =
      (u x - u (euclideanCoordShift (-h) i x)) / h :=
  rfl

/-- Product rule for forward coordinate difference quotients. -/
theorem euclideanForwardDifferenceQuotient_mul {d : ℕ}
    (h : ℝ) (i : Fin d) (u v : Vec d → ℝ) (x : Vec d) :
    euclideanForwardDifferenceQuotient h i (fun y => u y * v y) x =
      euclideanForwardDifferenceQuotient h i u x *
          v (euclideanCoordShift h i x) +
        u x * euclideanForwardDifferenceQuotient h i v x := by
  simp [euclideanForwardDifferenceQuotient, div_eq_mul_inv]
  ring

/-- Product rule for backward coordinate difference quotients. -/
theorem euclideanBackwardDifferenceQuotient_mul {d : ℕ}
    (h : ℝ) (i : Fin d) (u v : Vec d → ℝ) (x : Vec d) :
    euclideanBackwardDifferenceQuotient h i (fun y => u y * v y) x =
      euclideanBackwardDifferenceQuotient h i u x * v x +
        u (euclideanCoordShift (-h) i x) *
          euclideanBackwardDifferenceQuotient h i v x := by
  simp [euclideanBackwardDifferenceQuotient, div_eq_mul_inv]
  ring

/-- Square rule for forward coordinate difference quotients. -/
theorem euclideanForwardDifferenceQuotient_sq {d : ℕ}
    (h : ℝ) (i : Fin d) (u : Vec d → ℝ) (x : Vec d) :
    euclideanForwardDifferenceQuotient h i (fun y => u y ^ 2) x =
      euclideanForwardDifferenceQuotient h i u x *
        (u (euclideanCoordShift h i x) + u x) := by
  simp [euclideanForwardDifferenceQuotient, div_eq_mul_inv, pow_two]
  ring

/-- Square rule for backward coordinate difference quotients. -/
theorem euclideanBackwardDifferenceQuotient_sq {d : ℕ}
    (h : ℝ) (i : Fin d) (u : Vec d → ℝ) (x : Vec d) :
    euclideanBackwardDifferenceQuotient h i (fun y => u y ^ 2) x =
      euclideanBackwardDifferenceQuotient h i u x *
        (u x + u (euclideanCoordShift (-h) i x)) := by
  simp [euclideanBackwardDifferenceQuotient, div_eq_mul_inv, pow_two]
  ring

/-- A backward quotient at the forward-shifted point is the corresponding
forward quotient. This is the pointwise algebra behind the future integral
summation-by-parts identity. -/
theorem euclideanBackwardDifferenceQuotient_coordShift_eq_forward {d : ℕ}
    (h : ℝ) (i : Fin d) (u : Vec d → ℝ) (x : Vec d) :
    euclideanBackwardDifferenceQuotient h i u (euclideanCoordShift h i x) =
      euclideanForwardDifferenceQuotient h i u x := by
  simp [euclideanBackwardDifferenceQuotient, euclideanForwardDifferenceQuotient]

/-- A forward quotient at the backward-shifted point is the corresponding
backward quotient. -/
theorem euclideanForwardDifferenceQuotient_coordShift_neg_eq_backward {d : ℕ}
    (h : ℝ) (i : Fin d) (u : Vec d → ℝ) (x : Vec d) :
    euclideanForwardDifferenceQuotient h i u (euclideanCoordShift (-h) i x) =
      euclideanBackwardDifferenceQuotient h i u x := by
  simp [euclideanBackwardDifferenceQuotient, euclideanForwardDifferenceQuotient]

/-- A forward quotient with step `h` is the backward quotient with step `-h`. -/
theorem euclideanForwardDifferenceQuotient_eq_backwardDifferenceQuotient_neg {d : ℕ}
    (h : ℝ) (i : Fin d) (u : Vec d → ℝ) :
    euclideanForwardDifferenceQuotient h i u =
      euclideanBackwardDifferenceQuotient (-h) i u := by
  funext x
  simp [euclideanForwardDifferenceQuotient, euclideanBackwardDifferenceQuotient,
    div_eq_mul_inv]
  ring

/-- Backward quotient of the direct difference-quotient test
`η² D_i^+ u`, expanded into its unshifted and shifted pieces. -/
theorem euclideanBackwardDifferenceQuotient_sq_mul_forwardDifferenceQuotient {d : ℕ}
    (h : ℝ) (i : Fin d) (η u : Vec d → ℝ) (x : Vec d) :
    euclideanBackwardDifferenceQuotient h i
        (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient h i u y) x =
      h⁻¹ *
        (η x ^ 2 * euclideanForwardDifferenceQuotient h i u x -
          η (euclideanCoordShift (-h) i x) ^ 2 *
            euclideanBackwardDifferenceQuotient h i u x) := by
  rw [euclideanBackwardDifferenceQuotient_apply,
    euclideanForwardDifferenceQuotient_coordShift_neg_eq_backward]
  simp [div_eq_mul_inv]
  ring

/-- Smooth functions remain smooth after a coordinate shift. -/
theorem contDiff_comp_euclideanCoordShift {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (h : ℝ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => u (euclideanCoordShift h i x)) := by
  simpa [euclideanCoordShift] using!
    hu.comp (contDiff_id.add contDiff_const)

/-- Compact support is preserved by precomposition with a coordinate shift. -/
theorem hasCompactSupport_comp_euclideanCoordShift {d : ℕ}
    {u : Vec d → ℝ} (hu : HasCompactSupport u) (h : ℝ) (i : Fin d) :
    HasCompactSupport (fun x => u (euclideanCoordShift h i x)) := by
  show HasCompactSupport (u ∘ Homeomorph.addRight (h • basisVec i))
  simpa [euclideanCoordShift, Function.comp] using
    hu.comp_homeomorph (Homeomorph.addRight (h • basisVec i))

/-- Forward difference quotients of smooth functions are smooth. -/
theorem contDiff_euclideanForwardDifferenceQuotient {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (h : ℝ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (euclideanForwardDifferenceQuotient h i u) := by
  have hshift := contDiff_comp_euclideanCoordShift hu h i
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => (u (euclideanCoordShift h i x) - u x) * h⁻¹)
  simpa [div_eq_mul_inv] using
    (hshift.sub hu).mul contDiff_const

/-- Backward difference quotients of smooth functions are smooth. -/
theorem contDiff_euclideanBackwardDifferenceQuotient {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (h : ℝ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (euclideanBackwardDifferenceQuotient h i u) := by
  have hshift := contDiff_comp_euclideanCoordShift hu (-h) i
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => (u x - u (euclideanCoordShift (-h) i x)) * h⁻¹)
  simpa [div_eq_mul_inv] using
    (hu.sub hshift).mul contDiff_const

/-- Forward difference quotients of compactly supported functions are compactly
supported. -/
theorem hasCompactSupport_euclideanForwardDifferenceQuotient {d : ℕ}
    {u : Vec d → ℝ} (hu : HasCompactSupport u) (h : ℝ) (i : Fin d) :
    HasCompactSupport (euclideanForwardDifferenceQuotient h i u) := by
  have hshift := hasCompactSupport_comp_euclideanCoordShift hu h i
  change HasCompactSupport
    (fun x => (u (euclideanCoordShift h i x) - u x) * h⁻¹)
  exact (hshift.sub hu).mul_right

/-- Backward difference quotients of compactly supported functions are compactly
supported. -/
theorem hasCompactSupport_euclideanBackwardDifferenceQuotient {d : ℕ}
    {u : Vec d → ℝ} (hu : HasCompactSupport u) (h : ℝ) (i : Fin d) :
    HasCompactSupport (euclideanBackwardDifferenceQuotient h i u) := by
  have hshift := hasCompactSupport_comp_euclideanCoordShift hu (-h) i
  change HasCompactSupport
    (fun x => (u x - u (euclideanCoordShift (-h) i x)) * h⁻¹)
  exact (hu.sub hshift).mul_right

/-- Coordinate derivatives commute with precomposition by a coordinate shift. -/
theorem euclideanCoordDeriv_comp_euclideanCoordShift {d : ℕ}
    (h : ℝ) (i j : Fin d) (u : Vec d → ℝ) (x : Vec d) :
    euclideanCoordDeriv j (fun y => u (euclideanCoordShift h i y)) x =
      euclideanCoordDeriv j u (euclideanCoordShift h i x) := by
  unfold euclideanCoordDeriv euclideanCoordShift
  simpa using
    congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec j))
      (fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := x)
        (h • basisVec i))

/-- Coordinate derivatives distribute over subtraction for smooth functions. -/
theorem euclideanCoordDeriv_sub {d : ℕ} {u v : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => u y - v y) x =
      euclideanCoordDeriv i u x - euclideanCoordDeriv i v x := by
  unfold euclideanCoordDeriv
  change (fderiv ℝ (u - v) x) (basisVec i) =
    (fderiv ℝ u x) (basisVec i) - (fderiv ℝ v x) (basisVec i)
  rw [fderiv_sub]
  · simp
  · exact (hu.differentiable (by simp)) x
  · exact (hv.differentiable (by simp)) x

/-- Coordinate derivatives commute with multiplication by a scalar on the
right. -/
theorem euclideanCoordDeriv_mul_const {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (c : ℝ) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => u y * c) x =
      euclideanCoordDeriv i u x * c := by
  unfold euclideanCoordDeriv
  rw [fderiv_mul_const]
  · simp [smul_eq_mul, mul_comm]
  · exact (hu.differentiable (by simp)) x

/-- Coordinate derivatives commute with forward coordinate difference
quotients for smooth functions. -/
theorem euclideanCoordDeriv_euclideanForwardDifferenceQuotient {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (h : ℝ) (i j : Fin d) (x : Vec d) :
    euclideanCoordDeriv j (euclideanForwardDifferenceQuotient h i u) x =
      euclideanForwardDifferenceQuotient h i (euclideanCoordDeriv j u) x := by
  have hshift := contDiff_comp_euclideanCoordShift hu h i
  calc
    euclideanCoordDeriv j (euclideanForwardDifferenceQuotient h i u) x
        = euclideanCoordDeriv j
            (fun y : Vec d => (u (euclideanCoordShift h i y) - u y) * h⁻¹) x := by
          rfl
    _ = (euclideanCoordDeriv j (fun y : Vec d => u (euclideanCoordShift h i y)) x -
            euclideanCoordDeriv j u x) * h⁻¹ := by
          rw [euclideanCoordDeriv_mul_const (hshift.sub hu)]
          rw [euclideanCoordDeriv_sub hshift hu]
    _ = euclideanForwardDifferenceQuotient h i (euclideanCoordDeriv j u) x := by
          rw [euclideanCoordDeriv_comp_euclideanCoordShift]
          simp [euclideanForwardDifferenceQuotient, div_eq_mul_inv]

/-- Coordinate derivatives commute with backward coordinate difference
quotients for smooth functions. -/
theorem euclideanCoordDeriv_euclideanBackwardDifferenceQuotient {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (h : ℝ) (i j : Fin d) (x : Vec d) :
    euclideanCoordDeriv j (euclideanBackwardDifferenceQuotient h i u) x =
      euclideanBackwardDifferenceQuotient h i (euclideanCoordDeriv j u) x := by
  have hshift := contDiff_comp_euclideanCoordShift hu (-h) i
  calc
    euclideanCoordDeriv j (euclideanBackwardDifferenceQuotient h i u) x
        = euclideanCoordDeriv j
            (fun y : Vec d => (u y - u (euclideanCoordShift (-h) i y)) * h⁻¹) x := by
          rfl
    _ = (euclideanCoordDeriv j u x -
            euclideanCoordDeriv j (fun y : Vec d => u (euclideanCoordShift (-h) i y)) x) *
          h⁻¹ := by
          rw [euclideanCoordDeriv_mul_const (hu.sub hshift)]
          rw [euclideanCoordDeriv_sub hu hshift]
    _ = euclideanBackwardDifferenceQuotient h i (euclideanCoordDeriv j u) x := by
          rw [euclideanCoordDeriv_comp_euclideanCoordShift]
          simp [euclideanBackwardDifferenceQuotient, div_eq_mul_inv]

/-- Euclidean gradients commute with forward coordinate difference quotients
for smooth functions. -/
theorem euclideanGradient_euclideanForwardDifferenceQuotient {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (h : ℝ) (i : Fin d) (x : Vec d) :
    euclideanGradient (euclideanForwardDifferenceQuotient h i u) x =
      fun j => euclideanForwardDifferenceQuotient h i (euclideanCoordDeriv j u) x := by
  ext j
  exact euclideanCoordDeriv_euclideanForwardDifferenceQuotient hu h i j x

/-- Euclidean gradients commute with backward coordinate difference quotients
for smooth functions. -/
theorem euclideanGradient_euclideanBackwardDifferenceQuotient {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (h : ℝ) (i : Fin d) (x : Vec d) :
    euclideanGradient (euclideanBackwardDifferenceQuotient h i u) x =
      fun j => euclideanBackwardDifferenceQuotient h i (euclideanCoordDeriv j u) x := by
  ext j
  exact euclideanCoordDeriv_euclideanBackwardDifferenceQuotient hu h i j x

/-- Euclidean gradients commute with precomposition by a coordinate shift. -/
theorem euclideanGradient_comp_euclideanCoordShift {d : ℕ}
    (h : ℝ) (i : Fin d) (u : Vec d → ℝ) (x : Vec d) :
    euclideanGradient (fun y => u (euclideanCoordShift h i y)) x =
      euclideanGradient u (euclideanCoordShift h i x) := by
  ext j
  exact euclideanCoordDeriv_comp_euclideanCoordShift h i j u x

/-- Pointwise FTC formula for a backward coordinate difference quotient of a
smooth function. -/
theorem euclideanBackwardDifferenceQuotient_eq_integral_coordDeriv_along_segment {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {h : ℝ} (hh : h ≠ 0) (i : Fin d) (x : Vec d) :
    euclideanBackwardDifferenceQuotient h i u x =
      ∫ t in (0 : ℝ)..1,
        euclideanCoordDeriv i u
          (segmentBlend x t (euclideanCoordShift (-h) i x)) := by
  let y : Vec d := euclideanCoordShift (-h) i x
  have hxy : x - y = h • basisVec i := by
    ext j
    by_cases hji : j = i
    · subst hji
      simp [y, basisVec]
    · simp [y, basisVec, hji]
  have hftc := sub_eq_integral_fderiv_along_segment hu x y
  have hintegrand :
      (fun t : ℝ => (fderiv ℝ u (segmentBlend x t y)) (x - y)) =
        fun t : ℝ =>
          h * euclideanCoordDeriv i u (segmentBlend x t y) := by
    funext t
    rw [hxy]
    simp [euclideanCoordDeriv]
  have hscale :
      ∫ t in (0 : ℝ)..1,
          (fderiv ℝ u (segmentBlend x t y)) (x - y) =
        h * ∫ t in (0 : ℝ)..1, euclideanCoordDeriv i u (segmentBlend x t y) := by
    rw [hintegrand]
    rw [intervalIntegral.integral_const_mul]
  calc
    euclideanBackwardDifferenceQuotient h i u x =
        (u x - u y) / h := by
          rfl
    _ = (∫ t in (0 : ℝ)..1,
          (fderiv ℝ u (segmentBlend x t y)) (x - y)) / h := by
          rw [hftc]
    _ = (h * ∫ t in (0 : ℝ)..1,
          euclideanCoordDeriv i u (segmentBlend x t y)) / h := by
          rw [hscale]
    _ = ∫ t in (0 : ℝ)..1,
          euclideanCoordDeriv i u (segmentBlend x t y) := by
          field_simp [hh]

/-- Pointwise norm bound following from the FTC representation of a backward
coordinate difference quotient. -/
theorem abs_euclideanBackwardDifferenceQuotient_le_integral_abs_coordDeriv_along_segment
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {h : ℝ} (hh : h ≠ 0) (i : Fin d) (x : Vec d) :
    |euclideanBackwardDifferenceQuotient h i u x| ≤
      ∫ t in (0 : ℝ)..1,
        |euclideanCoordDeriv i u
          (segmentBlend x t (euclideanCoordShift (-h) i x))| := by
  rw [euclideanBackwardDifferenceQuotient_eq_integral_coordDeriv_along_segment hu hh i x]
  simpa [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_integral_norm
      (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ =>
        euclideanCoordDeriv i u
          (segmentBlend x t (euclideanCoordShift (-h) i x)))
      zero_le_one)

/-- Jensen/Cauchy on the unit interval for a continuous real function. -/
theorem sq_intervalIntegral_abs_le_intervalIntegral_sq_abs_of_continuous
    {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, |g t|) ^ 2 ≤
      ∫ t in (0 : ℝ)..1, |g t| ^ 2 := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) fun y : ℝ => y ^ 2 := by
    simpa using (convexOn_pow (𝕜 := ℝ) 2)
  have hJ :
      (⨍ t in Set.Ioc (0 : ℝ) 1, |g t|) ^ 2 ≤
        ⨍ t in Set.Ioc (0 : ℝ) 1, |g t| ^ 2 := by
    refine hconv.map_set_average_le
      (μ := MeasureTheory.volume) (t := Set.Ioc (0 : ℝ) 1)
      (f := fun t : ℝ => |g t|)
      (g := fun y : ℝ => y ^ 2)
      (by exact (continuous_pow 2).continuousOn)
      isClosed_Ici ?h0 ?ht ?hfs ?hfi ?hgi
    · simp [Real.volume_Ioc]
    · simp [Real.volume_Ioc]
    · exact Filter.Eventually.of_forall fun t => abs_nonneg (g t)
    · exact hg.abs.integrableOn_Ioc
    · simpa [Function.comp_def, Pi.pow_def] using!
        ((hg.abs.pow 2).integrableOn_Ioc :
          MeasureTheory.IntegrableOn (fun t : ℝ => |g t| ^ 2)
            (Set.Ioc (0 : ℝ) 1) MeasureTheory.volume)
  have hleft :
      (⨍ t in Set.Ioc (0 : ℝ) 1, |g t|) =
        ∫ t in (0 : ℝ)..1, |g t| := by
    rw [MeasureTheory.setAverage_eq]
    simp [intervalIntegral.integral_of_le zero_le_one]
  have hright :
      (⨍ t in Set.Ioc (0 : ℝ) 1, g t ^ 2) =
        ∫ t in (0 : ℝ)..1, g t ^ 2 := by
    rw [MeasureTheory.setAverage_eq]
    simp [intervalIntegral.integral_of_le zero_le_one]
  have htarget :
      (∫ t in (0 : ℝ)..1, |g t|) ^ 2 ≤
        ∫ t in (0 : ℝ)..1, g t ^ 2 := by
    simpa [hleft, hright] using hJ
  simpa [sq_abs] using htarget

/-- Pointwise squared version of the smooth FTC/Jensen estimate for backward
coordinate difference quotients. -/
theorem sq_euclideanBackwardDifferenceQuotient_le_integral_sq_coordDeriv_along_segment
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {h : ℝ} (hh : h ≠ 0) (i : Fin d) (x : Vec d) :
    (euclideanBackwardDifferenceQuotient h i u x) ^ 2 ≤
      ∫ t in (0 : ℝ)..1,
        (euclideanCoordDeriv i u
          (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2 := by
  let y : Vec d := euclideanCoordShift (-h) i x
  let g : ℝ → ℝ := fun t =>
    euclideanCoordDeriv i u (segmentBlend x t y)
  have hderiv_cont : Continuous (euclideanCoordDeriv i u) := by
    have h1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
    simpa [euclideanCoordDeriv] using!
      (h1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsegment_cont :
      Continuous (fun t : ℝ => segmentBlend x t y) := by
    have hraw : Continuous (fun t : ℝ => y + t • (x - y)) :=
      continuous_const.add
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ => x - y))
    have hEq :
        (fun t : ℝ => segmentBlend x t y) =
          fun t : ℝ => y + t • (x - y) := by
      funext t
      exact segmentBlend_eq_add_smul_sub x y t
    rw [hEq]
    exact hraw
  have hg_cont : Continuous g := hderiv_cont.comp hsegment_cont
  have hnorm :
      |euclideanBackwardDifferenceQuotient h i u x| ≤
        ∫ t in (0 : ℝ)..1, |g t| := by
    simpa [g, y] using
      abs_euclideanBackwardDifferenceQuotient_le_integral_abs_coordDeriv_along_segment
        hu hh i x
  have hnonneg :
      0 ≤ ∫ t in (0 : ℝ)..1, |g t| :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _ => abs_nonneg (g t))
  have hsq_abs :
      |euclideanBackwardDifferenceQuotient h i u x| ^ 2 ≤
        (∫ t in (0 : ℝ)..1, |g t|) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hnonneg).2 hnorm
  have hJ :=
    sq_intervalIntegral_abs_le_intervalIntegral_sq_abs_of_continuous (g := g) hg_cont
  calc
    (euclideanBackwardDifferenceQuotient h i u x) ^ 2 =
        |euclideanBackwardDifferenceQuotient h i u x| ^ 2 := by
          rw [sq_abs]
    _ ≤ (∫ t in (0 : ℝ)..1, |g t|) ^ 2 := hsq_abs
    _ ≤ ∫ t in (0 : ℝ)..1, |g t| ^ 2 := hJ
    _ = ∫ t in (0 : ℝ)..1,
        (euclideanCoordDeriv i u
          (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2 := by
          simp [g, y, sq_abs]

/-- The segment from `x - h eᵢ` to `x` is just a coordinate shift of `x`.
This is the algebraic step behind collapsing the FTC/Jensen segment average by
translation invariance. -/
theorem segmentBlend_euclideanCoordShift_neg_eq_euclideanCoordShift
    {d : ℕ} (h : ℝ) (i : Fin d) (x : Vec d) (t : ℝ) :
    segmentBlend x t (euclideanCoordShift (-h) i x) =
      euclideanCoordShift ((t - 1) * h) i x := by
  rw [segmentBlend_eq_add_smul_sub]
  ext j
  by_cases hji : j = i
  · subst hji
    simp [euclideanCoordShift, basisVec]
    ring_nf
  · simp [euclideanCoordShift, basisVec, hji]

/-- Whole-space translation invariance for a coordinate shift. -/
theorem integral_comp_euclideanCoordShift_eq_integral
    {d : ℕ} (h : ℝ) (i : Fin d) (u : Vec d → ℝ) :
    ∫ x, u (euclideanCoordShift h i x) ∂MeasureTheory.volume =
      ∫ x, u x ∂MeasureTheory.volume := by
  let z : Vec d := h • basisVec i
  have hmp :
      MeasureTheory.MeasurePreserving (fun x : Vec d => x + z)
        MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_add_right MeasureTheory.volume z
  have hchange :=
    hmp.integral_comp (Homeomorph.addRight z).measurableEmbedding u
  simpa [euclideanCoordShift, z] using hchange

/-- Combining the segment algebra with whole-space translation invariance:
integrating along the segment from `x - h eᵢ` to `x`, for fixed `t`, has the
same integral as the unshifted function. -/
theorem integral_comp_segmentBlend_euclideanCoordShift_neg_eq_integral
    {d : ℕ} (h : ℝ) (i : Fin d) (t : ℝ) (u : Vec d → ℝ) :
    ∫ x, u (segmentBlend x t (euclideanCoordShift (-h) i x)) ∂MeasureTheory.volume =
      ∫ x, u x ∂MeasureTheory.volume := by
  calc
    ∫ x, u (segmentBlend x t (euclideanCoordShift (-h) i x)) ∂MeasureTheory.volume =
        ∫ x, u (euclideanCoordShift ((t - 1) * h) i x) ∂MeasureTheory.volume := by
          simp_rw [segmentBlend_euclideanCoordShift_neg_eq_euclideanCoordShift]
    _ = ∫ x, u x ∂MeasureTheory.volume := by
          exact integral_comp_euclideanCoordShift_eq_integral ((t - 1) * h) i u

/-- Fixed-time translation collapse for the squared coordinate derivative
appearing in the smooth FTC/Jensen estimate. -/
theorem integral_sq_coordDeriv_comp_segmentBlend_euclideanCoordShift_neg_eq_integral
    {d : ℕ} (h : ℝ) (i : Fin d) (t : ℝ) (u : Vec d → ℝ) :
    ∫ x,
        (euclideanCoordDeriv i u
          (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2
        ∂MeasureTheory.volume =
      ∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume := by
  simpa using
    integral_comp_segmentBlend_euclideanCoordShift_neg_eq_integral
      h i t (fun y : Vec d => (euclideanCoordDeriv i u y) ^ 2)

/-- Product integrability of the smooth segment-square integrand used to swap
the `t` and `x` integrals in the quotient bound. -/
theorem integrable_sq_coordDeriv_comp_segmentBlend_euclideanCoordShift_neg_prod
    {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hus : HasCompactSupport u)
    (h : ℝ) (i : Fin d) :
    MeasureTheory.Integrable
      (Function.uncurry fun t x =>
        (euclideanCoordDeriv i u
          (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        MeasureTheory.volume) := by
  let F : ℝ × Vec d → ℝ := fun p =>
    (euclideanCoordDeriv i u
      (segmentBlend p.2 p.1 (euclideanCoordShift (-h) i p.2))) ^ 2
  have hderiv_cont : Continuous (euclideanCoordDeriv i u) :=
    (contDiff_euclideanCoordDeriv hu i).continuous
  have hseg_cont :
      Continuous
        (fun p : ℝ × Vec d =>
          segmentBlend p.2 p.1 (euclideanCoordShift (-h) i p.2)) := by
    have hraw :
        Continuous
          (fun p : ℝ × Vec d =>
            euclideanCoordShift ((p.1 - 1) * h) i p.2) := by
      simpa [euclideanCoordShift] using!
        continuous_snd.add
          (((continuous_fst.sub continuous_const).mul continuous_const).smul
            (continuous_const : Continuous fun _ : ℝ × Vec d => basisVec i))
    have hEq :
        (fun p : ℝ × Vec d =>
          segmentBlend p.2 p.1 (euclideanCoordShift (-h) i p.2)) =
            fun p : ℝ × Vec d =>
              euclideanCoordShift ((p.1 - 1) * h) i p.2 := by
      funext p
      exact segmentBlend_euclideanCoordShift_neg_eq_euclideanCoordShift h i p.2 p.1
    rw [hEq]
    exact hraw
  have hF_cont : Continuous F := by
    simpa [F] using! (hderiv_cont.comp hseg_cont).pow 2
  have hF_aesm :
      MeasureTheory.AEStronglyMeasurable F
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
          MeasureTheory.volume) :=
    hF_cont.aestronglyMeasurable
  have hbase_cont : Continuous (fun x : Vec d => (euclideanCoordDeriv i u x) ^ 2) :=
    ((contDiff_euclideanCoordDeriv hu i).continuous).pow 2
  have hbase_comp : HasCompactSupport
      (fun x : Vec d => (euclideanCoordDeriv i u x) ^ 2) := by
    simpa [pow_two] using!
      (hasCompactSupport_euclideanCoordDeriv hus i).mul_right
  have hsection_int :
      ∀ t : ℝ, MeasureTheory.Integrable (fun x : Vec d => F (t, x))
        MeasureTheory.volume := by
    intro t
    have hshift_cont :
        Continuous (fun x : Vec d => euclideanCoordShift ((t - 1) * h) i x) := by
      simpa [euclideanCoordShift] using!
        continuous_id.add (continuous_const : Continuous fun _ : Vec d =>
          ((t - 1) * h) • basisVec i)
    have hshift_comp :
        HasCompactSupport
          (fun x : Vec d =>
            (fun y : Vec d => (euclideanCoordDeriv i u y) ^ 2)
              (euclideanCoordShift ((t - 1) * h) i x)) :=
      hasCompactSupport_comp_euclideanCoordShift hbase_comp ((t - 1) * h) i
    have hEq :
        (fun x : Vec d => F (t, x)) =
          fun x : Vec d =>
            (euclideanCoordDeriv i u
              (euclideanCoordShift ((t - 1) * h) i x)) ^ 2 := by
      funext x
      dsimp [F]
      change
        (euclideanCoordDeriv i u
          (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2 =
            (euclideanCoordDeriv i u
              (euclideanCoordShift ((t - 1) * h) i x)) ^ 2
      rw [segmentBlend_euclideanCoordShift_neg_eq_euclideanCoordShift]
    rw [hEq]
    exact (hbase_cont.comp hshift_cont).integrable_of_hasCompactSupport hshift_comp
  have habs_integral_eq :
      (fun t : ℝ => ∫ x, |F (t, x)| ∂MeasureTheory.volume) =
        fun _ : ℝ => ∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume := by
    funext t
    have habs_fun :
        (fun x : Vec d => |F (t, x)|) =
          fun x : Vec d =>
            (euclideanCoordDeriv i u
              (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2 := by
      funext x
      dsimp [F]
      rw [abs_of_nonneg (sq_nonneg _)]
    calc
      ∫ x, |F (t, x)| ∂MeasureTheory.volume =
          ∫ x,
            (euclideanCoordDeriv i u
              (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2
            ∂MeasureTheory.volume := by
            rw [habs_fun]
      _ = ∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume :=
            integral_sq_coordDeriv_comp_segmentBlend_euclideanCoordShift_neg_eq_integral
              h i t u
  let : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  refine
    (MeasureTheory.integrable_prod_iff
      (μ := MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1))
      (ν := MeasureTheory.volume)
      hF_aesm).2 ?_
  constructor
  · exact Filter.Eventually.of_forall hsection_int
  · have hnorm_to_abs :
        (fun t : ℝ => ∫ x, ‖F (t, x)‖ ∂MeasureTheory.volume) =
          fun t : ℝ => ∫ x, |F (t, x)| ∂MeasureTheory.volume := by
        funext t
        simp [Real.norm_eq_abs]
    rw [hnorm_to_abs, habs_integral_eq]
    exact
      (MeasureTheory.integrable_const
        (∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume) :
          MeasureTheory.Integrable
            (fun _ : ℝ => ∫ x, (euclideanCoordDeriv i u x) ^ 2
              ∂MeasureTheory.volume)
            (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)))

/-- The integrated smooth FTC/Jensen segment term collapses to the unshifted
coordinate-derivative square norm. -/
theorem integral_intervalIntegral_sq_coordDeriv_comp_segmentBlend_euclideanCoordShift_neg_eq_integral
    {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hus : HasCompactSupport u)
    (h : ℝ) (i : Fin d) :
    ∫ x, (∫ t in (0 : ℝ)..1,
        (euclideanCoordDeriv i u
          (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2)
        ∂MeasureTheory.volume =
      ∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume := by
  let G : ℝ → Vec d → ℝ := fun t x =>
    (euclideanCoordDeriv i u
      (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2
  have hprod :
      MeasureTheory.Integrable (Function.uncurry G)
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
          MeasureTheory.volume) := by
    simpa [G] using
      integrable_sq_coordDeriv_comp_segmentBlend_euclideanCoordShift_neg_prod
        hu hus h i
  have hswap :
      ∫ x, (∫ t in (0 : ℝ)..1, G t x) ∂MeasureTheory.volume =
        ∫ t in (0 : ℝ)..1, ∫ x, G t x ∂MeasureTheory.volume := by
    simpa [G, Set.uIoc_of_le zero_le_one] using
      (MeasureTheory.intervalIntegral_integral_swap
        (μ := MeasureTheory.volume)
        (a := (0 : ℝ)) (b := 1)
        (f := G) hprod).symm
  have hinner :
      ∀ t : ℝ,
        ∫ x, G t x ∂MeasureTheory.volume =
          ∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume := by
    intro t
    simpa [G] using
      integral_sq_coordDeriv_comp_segmentBlend_euclideanCoordShift_neg_eq_integral
        h i t u
  calc
    ∫ x, (∫ t in (0 : ℝ)..1,
        (euclideanCoordDeriv i u
          (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2)
        ∂MeasureTheory.volume =
        ∫ x, (∫ t in (0 : ℝ)..1, G t x) ∂MeasureTheory.volume := by
          rfl
    _ = ∫ t in (0 : ℝ)..1, ∫ x, G t x ∂MeasureTheory.volume := hswap
    _ = ∫ t in (0 : ℝ)..1,
          ∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume := by
          simp_rw [hinner]
    _ = ∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume := by
          simp

/-- Smooth compact-support `L²` control of a backward coordinate difference
quotient by the corresponding coordinate derivative. -/
theorem integral_sq_euclideanBackwardDifferenceQuotient_le_integral_sq_coordDeriv
    {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hus : HasCompactSupport u)
    {h : ℝ} (hh : h ≠ 0) (i : Fin d) :
    ∫ x, (euclideanBackwardDifferenceQuotient h i u x) ^ 2
        ∂MeasureTheory.volume ≤
      ∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume := by
  let G : ℝ → Vec d → ℝ := fun t x =>
    (euclideanCoordDeriv i u
      (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2
  have hleft_int :
      MeasureTheory.Integrable
        (fun x : Vec d => (euclideanBackwardDifferenceQuotient h i u x) ^ 2)
        MeasureTheory.volume := by
    let q : Vec d → ℝ := euclideanBackwardDifferenceQuotient h i u
    have hq_cont : Continuous q :=
      (contDiff_euclideanBackwardDifferenceQuotient hu h i).continuous
    have hq_comp : HasCompactSupport q :=
      hasCompactSupport_euclideanBackwardDifferenceQuotient hus h i
    have hmul_int :
        MeasureTheory.Integrable (fun x : Vec d => q x * q x)
          MeasureTheory.volume :=
      (hq_cont.mul hq_cont).integrable_of_hasCompactSupport hq_comp.mul_right
    simpa [q, pow_two] using hmul_int
  have hprod :
      MeasureTheory.Integrable (Function.uncurry G)
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
          MeasureTheory.volume) := by
    simpa [G] using
      integrable_sq_coordDeriv_comp_segmentBlend_euclideanCoordShift_neg_prod
        hu hus h i
  have hright_int :
      MeasureTheory.Integrable
        (fun x : Vec d => ∫ t in (0 : ℝ)..1, G t x)
        MeasureTheory.volume := by
    have hset_int :
        MeasureTheory.Integrable
          (fun x : Vec d => ∫ t, G t x
            ∂MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1))
          MeasureTheory.volume :=
      hprod.integral_prod_right
    simpa [G, intervalIntegral.integral_of_le zero_le_one,
      Set.uIoc_of_le zero_le_one] using hset_int
  have hpoint :
      (fun x : Vec d => (euclideanBackwardDifferenceQuotient h i u x) ^ 2) ≤
        fun x : Vec d => ∫ t in (0 : ℝ)..1, G t x := by
    intro x
    simpa [G] using
      sq_euclideanBackwardDifferenceQuotient_le_integral_sq_coordDeriv_along_segment
        hu hh i x
  calc
    ∫ x, (euclideanBackwardDifferenceQuotient h i u x) ^ 2
        ∂MeasureTheory.volume ≤
        ∫ x, (∫ t in (0 : ℝ)..1, G t x) ∂MeasureTheory.volume :=
          MeasureTheory.integral_mono hleft_int hright_int hpoint
    _ = ∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume := by
          change
            ∫ x, (∫ t in (0 : ℝ)..1,
              (euclideanCoordDeriv i u
                (segmentBlend x t (euclideanCoordShift (-h) i x))) ^ 2)
              ∂MeasureTheory.volume =
                ∫ x, (euclideanCoordDeriv i u x) ^ 2 ∂MeasureTheory.volume
          exact
            integral_intervalIntegral_sq_coordDeriv_comp_segmentBlend_euclideanCoordShift_neg_eq_integral
              hu hus h i

/-- For real-valued `L²` functions, the square of the `toReal` `eLpNorm` is
the integral of the pointwise square. -/
theorem toReal_eLpNorm_two_sq_eq_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f : α → ℝ} (hf : MeasureTheory.MemLp f 2 μ) :
    (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ 2 =
      ∫ x, f x ^ 2 ∂μ := by
  have hpow : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by
    norm_num
  have hnorm :=
    hf.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by simp : (2 : ℝ≥0∞) ≠ ⊤)
  have hsq_norm :
      (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ 2 =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
    rw [hnorm, hpow]
    have hint_nonneg :
        0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
      exact MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (norm_nonneg _) _)
    rw [ENNReal.toReal_ofReal]
    · rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
      rw [← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt hint_nonneg
    · exact Real.rpow_nonneg hint_nonneg _
  calc
    (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ 2 =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := hsq_norm
    _ = ∫ x, f x ^ 2 ∂μ := by
        congr 1 with x
        rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- Smooth compact-support quotient control in `eLpNorm` form. This is the
form used by the `H¹₀` approximation bridge. -/
theorem eLpNorm_euclideanBackwardDifferenceQuotient_le_eLpNorm_coordDeriv
    {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hus : HasCompactSupport u)
    {h : ℝ} (hh : h ≠ 0) (i : Fin d) :
    MeasureTheory.eLpNorm (euclideanBackwardDifferenceQuotient h i u)
        2 MeasureTheory.volume ≤
      MeasureTheory.eLpNorm (euclideanCoordDeriv i u) 2 MeasureTheory.volume := by
  have hquot_mem :
      MeasureTheory.MemLp (euclideanBackwardDifferenceQuotient h i u)
        2 MeasureTheory.volume :=
    (contDiff_euclideanBackwardDifferenceQuotient hu h i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanBackwardDifferenceQuotient hus h i)
  have hderiv_mem :
      MeasureTheory.MemLp (euclideanCoordDeriv i u) 2 MeasureTheory.volume :=
    (contDiff_euclideanCoordDeriv hu i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordDeriv hus i)
  have hsq_le :
      (ENNReal.toReal
        (MeasureTheory.eLpNorm (euclideanBackwardDifferenceQuotient h i u)
          2 MeasureTheory.volume)) ^ 2 ≤
        (ENNReal.toReal
          (MeasureTheory.eLpNorm (euclideanCoordDeriv i u)
            2 MeasureTheory.volume)) ^ 2 := by
    rw [toReal_eLpNorm_two_sq_eq_integral_sq hquot_mem]
    rw [toReal_eLpNorm_two_sq_eq_integral_sq hderiv_mem]
    exact integral_sq_euclideanBackwardDifferenceQuotient_le_integral_sq_coordDeriv
      hu hus hh i
  have htoReal_le :
      ENNReal.toReal
        (MeasureTheory.eLpNorm (euclideanBackwardDifferenceQuotient h i u)
          2 MeasureTheory.volume) ≤
        ENNReal.toReal
          (MeasureTheory.eLpNorm (euclideanCoordDeriv i u)
            2 MeasureTheory.volume) :=
    (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).1 hsq_le
  exact
    (ENNReal.toReal_le_toReal hquot_mem.eLpNorm_ne_top hderiv_mem.eLpNorm_ne_top).1
      htoReal_le

/-- Whole-space translation change of variables for a coordinate shift. This is
the measure-theoretic core of finite-difference summation by parts. -/
theorem integral_comp_euclideanCoordShift_mul_eq_integral_mul_comp_euclideanCoordShift_neg
    {d : ℕ} (h : ℝ) (i : Fin d) (u v : Vec d → ℝ) :
    ∫ x, u (euclideanCoordShift h i x) * v x ∂MeasureTheory.volume =
      ∫ x, u x * v (euclideanCoordShift (-h) i x) ∂MeasureTheory.volume := by
  let z : Vec d := h • basisVec i
  have hmp :
      MeasureTheory.MeasurePreserving (fun x : Vec d => x + z)
        MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_add_right MeasureTheory.volume z
  have hchange :=
    hmp.integral_comp (Homeomorph.addRight z).measurableEmbedding
      (fun y : Vec d => u y * v (y - z))
  simpa [euclideanCoordShift, z, sub_eq_add_neg, neg_smul] using hchange

/-- Vector-valued whole-space translation change of variables for coordinate
shifts, paired by `vecDot`. -/
theorem integral_vecDot_comp_euclideanCoordShift_eq_integral_vecDot_comp_euclideanCoordShift_neg
    {d : ℕ} (h : ℝ) (i : Fin d) (F G : Vec d → Vec d) :
    ∫ x, vecDot (F (euclideanCoordShift h i x)) (G x) ∂MeasureTheory.volume =
      ∫ x, vecDot (F x) (G (euclideanCoordShift (-h) i x)) ∂MeasureTheory.volume := by
  let z : Vec d := h • basisVec i
  have hmp :
      MeasureTheory.MeasurePreserving (fun x : Vec d => x + z)
        MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_add_right MeasureTheory.volume z
  have hchange :=
    hmp.integral_comp (Homeomorph.addRight z).measurableEmbedding
      (fun y : Vec d => vecDot (F y) (G (y - z)))
  simpa [euclideanCoordShift, z, sub_eq_add_neg, neg_smul] using hchange

/-- Whole-space finite-difference summation by parts. The compact-support
assumption on `u` supplies the integrability needed to expand the two
difference quotients into ordinary Lebesgue integrals. -/
theorem integral_euclideanForwardDifferenceQuotient_mul_eq_neg_integral_mul_euclideanBackwardDifferenceQuotient
    {d : ℕ} {u v : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hus : HasCompactSupport u) (h : ℝ) (i : Fin d) :
    ∫ x, euclideanForwardDifferenceQuotient h i u x * v x ∂MeasureTheory.volume =
      -∫ x, u x * euclideanBackwardDifferenceQuotient h i v x ∂MeasureTheory.volume := by
  have hshiftInt :
      MeasureTheory.Integrable
        (fun x : Vec d => u (euclideanCoordShift h i x) * v x)
        MeasureTheory.volume :=
    integrable_mul_of_contDiff_hasCompactSupport_left
      (contDiff_comp_euclideanCoordShift hu h i) hv
      (hasCompactSupport_comp_euclideanCoordShift hus h i)
  have huvInt :
      MeasureTheory.Integrable (fun x : Vec d => u x * v x)
        MeasureTheory.volume :=
    integrable_mul_of_contDiff_hasCompactSupport_left hu hv hus
  have hbackShiftInt :
      MeasureTheory.Integrable
        (fun x : Vec d => u x * v (euclideanCoordShift (-h) i x))
        MeasureTheory.volume :=
    integrable_mul_of_contDiff_hasCompactSupport_left hu
      (contDiff_comp_euclideanCoordShift hv (-h) i) hus
  have hchange :=
    integral_comp_euclideanCoordShift_mul_eq_integral_mul_comp_euclideanCoordShift_neg
      h i u v
  have hpointLeft :
      (fun x : Vec d => euclideanForwardDifferenceQuotient h i u x * v x) =
        fun x : Vec d =>
          (u (euclideanCoordShift h i x) * v x - u x * v x) * h⁻¹ := by
    funext x
    simp [euclideanForwardDifferenceQuotient, div_eq_mul_inv]
    ring
  have hpointRight :
      (fun x : Vec d => u x * euclideanBackwardDifferenceQuotient h i v x) =
        fun x : Vec d =>
          (u x * v x - u x * v (euclideanCoordShift (-h) i x)) * h⁻¹ := by
    funext x
    simp [euclideanBackwardDifferenceQuotient, div_eq_mul_inv]
    ring
  calc
    ∫ x, euclideanForwardDifferenceQuotient h i u x * v x ∂MeasureTheory.volume
        = ∫ x, (u (euclideanCoordShift h i x) * v x - u x * v x) * h⁻¹
            ∂MeasureTheory.volume := by
          rw [hpointLeft]
    _ = (∫ x, u (euclideanCoordShift h i x) * v x - u x * v x
            ∂MeasureTheory.volume) * h⁻¹ := by
          rw [MeasureTheory.integral_mul_const]
    _ = ((∫ x, u (euclideanCoordShift h i x) * v x ∂MeasureTheory.volume) -
            (∫ x, u x * v x ∂MeasureTheory.volume)) * h⁻¹ := by
          rw [MeasureTheory.integral_sub hshiftInt huvInt]
    _ = ((∫ x, u x * v (euclideanCoordShift (-h) i x) ∂MeasureTheory.volume) -
            (∫ x, u x * v x ∂MeasureTheory.volume)) * h⁻¹ := by
          rw [hchange]
    _ = -(((∫ x, u x * v x ∂MeasureTheory.volume) -
            (∫ x, u x * v (euclideanCoordShift (-h) i x) ∂MeasureTheory.volume)) * h⁻¹) := by
          ring
    _ = -((∫ x, u x * v x - u x * v (euclideanCoordShift (-h) i x)
            ∂MeasureTheory.volume) * h⁻¹) := by
          rw [MeasureTheory.integral_sub huvInt hbackShiftInt]
    _ = -∫ x, (u x * v x - u x * v (euclideanCoordShift (-h) i x)) * h⁻¹
            ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_mul_const]
    _ = -∫ x, u x * euclideanBackwardDifferenceQuotient h i v x
            ∂MeasureTheory.volume := by
          rw [hpointRight]

end

end Homogenization
