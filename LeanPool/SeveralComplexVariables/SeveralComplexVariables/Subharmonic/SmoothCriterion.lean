/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analysis.TaylorBounds
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Subharmonic.Majorant

/-!
# The Laplacian criterion for subharmonicity

A `C²` function of one complex variable is subharmonic exactly when its Laplacian is
nonnegative. The proof expands the circle average of a `C²` function to second order: the
difference between the circle average of radius `r` and the center value is `r ^ 2 / 4` times
the Laplacian, up to `o(r ^ 2)`. A positive Laplacian therefore gives the strict submean
inequality on small circles and a negative one the reverse inequality. The nonstrict direction
adds a small multiple of `‖z - t₀‖ ^ 2`, whose Laplacian is `4`, and uses the submean inequality
on closed discs for continuous subharmonic functions.

The Laplacian is Mathlib's `InnerProductSpace` Laplacian on `ℂ`, written in terms of the second
Fréchet derivative in the directions `1` and `I`.

References: [Fritzsche–Grauert][FritzscheGrauert2002] (2002), Chapter II, Theorem 2.8;
[Hörmander][Hormander1973] (1973), Section 1.6 and Theorem 2.6.2.

## Main results

* `exists_taylor_bound`: **Uniform second-order Taylor bound.** For a `C²` function on a real normed
  space, the second-order Taylor remainder at a point is bounded by `ε ‖h‖ ^ 2` for all small
  increments `h`.
* `exists_circleAverage_sub_le`: **Second-order expansion of circle averages.** For a `C²` function,
  the circle average of radius `r` differs from the center value by `r ^ 2 / 4` times the Laplacian,
  up to `ε r ^ 2` for all small `r`.
* `HasSubmeanAt.laplacian_nonneg`: **Necessity.** A `C²` subharmonic function has nonnegative
  Laplacian.
* `subharmonicOn_of_laplacian_nonneg`: **Sufficiency.** A `C²` function with nonnegative Laplacian
  on an open set is subharmonic.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
-/

public section

open Complex Filter MeasureTheory Metric Set Real
open scoped Topology InnerProductSpace Laplacian

namespace SeveralComplexVariables

variable {g : ℂ → ℝ} {t₀ : ℂ}

/-- The Laplacian on `ℂ` in terms of the iterated Fréchet derivative. -/
theorem laplacian_eq_fderiv_fderiv (g : ℂ → ℝ) (t : ℂ) :
    Δ g t = fderiv ℝ (fderiv ℝ g) t 1 1 + fderiv ℝ (fderiv ℝ g) t I I := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp [iteratedFDeriv_two_apply]

/-- A point on the circle of radius `r` about `0`, as a real combination of `1` and `I`. -/
theorem circleMap_zero_eq_smul (r θ : ℝ) :
    circleMap 0 r θ = (r * Real.cos θ) • (1 : ℂ) + (r * Real.sin θ) • I := by
  simp only [circleMap, zero_add, Complex.exp_mul_I, Complex.real_smul]
  push_cast
  ring

/-- **Uniform second-order Taylor bound.** For a `C²` function on a real normed space, the
second-order Taylor remainder at a point is bounded by `ε ‖h‖ ^ 2` for all small increments
`h`. The bound is uniform in the direction of `h`. -/
theorem exists_taylor_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : G → ℝ}
    {t₀ : G} (hg : ContDiffAt ℝ 2 g t₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : G, ‖h‖ < δ →
      |g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h - (1 / 2) * fderiv ℝ (fderiv ℝ g) t₀ h h|
        ≤ ε * ‖h‖ ^ 2 := by
  set D := fderiv ℝ g with hDdef
  set B := fderiv ℝ (fderiv ℝ g) t₀ with hBdef
  have hD : HasFDerivAt D B t₀ :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hev : ∀ᶠ y in 𝓝 t₀, HasFDerivAt g (D y) y := by
    filter_upwards [hg.eventually (by simp)] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt
  have hsymm : ∀ v w, B v w = B w v := second_derivative_symmetric_of_eventually hev hD
  have hlo : ∀ᶠ h in 𝓝 (0 : G), ‖D (t₀ + h) - D t₀ - B h‖ ≤ ε * ‖h‖ :=
    (hasFDerivAt_iff_isLittleO_nhds_zero.mp hD).def hε
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.mem_nhds_iff.mp hlo
  obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun h hh => ?_⟩
  set φ : G → ℝ := fun k => g (t₀ + k) - g t₀ - D t₀ k - (1 / 2) * B k k with hφdef
  have hφ' : ∀ k : G, ‖k‖ < min δ₁ δ₂ → HasFDerivAt φ (D (t₀ + k) - D t₀ - B k) k := by
    intro k hk
    have hk₂ : t₀ + k ∈ ball t₀ δ₂ := by
      simpa [dist_eq_norm] using hk.trans_le (min_le_right _ _)
    have h1 : HasFDerivAt (fun k => g (t₀ + k)) (D (t₀ + k)) k :=
      ((hball₂ hk₂).comp k ((hasFDerivAt_id k).const_add t₀)).congr_fderiv
        (ContinuousLinearMap.comp_id _)
    have h2 : HasFDerivAt (fun k => D t₀ k) (D t₀) k := (D t₀).hasFDerivAt
    have h3 : HasFDerivAt (fun k => (1 / 2 : ℝ) * B k k) (B k) k := by
      have hb := (B.hasFDerivAt (x := k)).clm_apply (hasFDerivAt_id k)
      have := hb.const_mul (1 / 2 : ℝ)
      refine this.congr_fderiv ?_
      ext s
      simp
      linarith [hsymm s k]
    have := (h1.sub_const (g t₀)).sub h2 |>.sub h3
    convert this using 1
  have hbound : ∀ k ∈ closedBall (0 : G) ‖h‖, ‖D (t₀ + k) - D t₀ - B k‖ ≤ ε * ‖h‖ := by
    intro k hk
    have hk' : ‖k‖ ≤ ‖h‖ := by simpa using hk
    have hk₁ : k ∈ ball (0 : G) δ₁ := by
      simpa using hk'.trans_lt (hh.trans_le (min_le_left _ _))
    exact (hball₁ hk₁).trans (mul_le_mul_of_nonneg_left hk' hε.le)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := φ) (f' := fun k => D (t₀ + k) - D t₀ - B k) (s := closedBall (0 : G) ‖h‖)
    (fun k hk => (hφ' k (by
      have hk' : ‖k‖ ≤ ‖h‖ := by simpa using hk
      exact hk'.trans_lt hh)).hasFDerivWithinAt)
    hbound (convex_closedBall _ _) (mem_closedBall_self (norm_nonneg h))
    (mem_closedBall_zero_iff.mpr le_rfl)
  have hφ0 : φ 0 = 0 := by simp [hφdef]
  rw [hφ0, sub_zero, sub_zero, Real.norm_eq_abs] at hmvt
  calc |g (t₀ + h) - g t₀ - fderiv ℝ g t₀ h - (1 / 2) * fderiv ℝ (fderiv ℝ g) t₀ h h|
      = |φ h| := rfl
    _ ≤ ε * ‖h‖ * ‖h‖ := hmvt
    _ = ε * ‖h‖ ^ 2 := by ring

/-- The integral of the cosine over a period vanishes. -/
private theorem integral_cos_two_pi : ∫ θ in (0 : ℝ)..2 * π, Real.cos θ = 0 := by
  simp [integral_cos]

/-- The integral of the sine over a period vanishes. -/
private theorem integral_sin_two_pi : ∫ θ in (0 : ℝ)..2 * π, Real.sin θ = 0 := by
  simp [integral_sin]

/-- The integral of the squared cosine over a period is `π`. -/
private theorem integral_cos_sq_two_pi : ∫ θ in (0 : ℝ)..2 * π, Real.cos θ ^ 2 = π := by
  rw [integral_cos_sq]
  simp

/-- The integral of the squared sine over a period is `π`. -/
private theorem integral_sin_sq_two_pi : ∫ θ in (0 : ℝ)..2 * π, Real.sin θ ^ 2 = π := by
  rw [integral_sin_sq]
  simp

/-- The integral of `sin θ cos θ` over a period vanishes. -/
private theorem integral_sin_mul_cos_two_pi :
    ∫ θ in (0 : ℝ)..2 * π, Real.sin θ * Real.cos θ = 0 := by
  rw [integral_sin_mul_cos₁]
  simp

/-- The circle integral of a real-linear form vanishes. -/
theorem integral_clm_circleMap_zero (L : ℂ →L[ℝ] ℝ) (r : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, L (circleMap 0 r θ) = 0 := by
  have : (fun θ => L (circleMap 0 r θ)) =
      fun θ => (r * L 1) * Real.cos θ + (r * L I) * Real.sin θ := by
    funext θ
    rw [circleMap_zero_eq_smul, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [this, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_two_pi, integral_sin_two_pi]
  · ring
  · exact (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
  · exact (continuous_const.mul Real.continuous_sin).intervalIntegrable _ _

/-- The circle integral of a real bilinear form on the diagonal is `π r ^ 2` times its trace in the
directions `1` and `I`. -/
theorem integral_bilinear_circleMap (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (r : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, B (circleMap 0 r θ) (circleMap 0 r θ) =
      π * r ^ 2 * (B 1 1 + B I I) := by
  have : (fun θ => B (circleMap 0 r θ) (circleMap 0 r θ)) =
      fun θ => (r ^ 2 * B 1 1) * Real.cos θ ^ 2 + (r ^ 2 * (B 1 I + B I 1)) *
        (Real.sin θ * Real.cos θ) + (r ^ 2 * B I I) * Real.sin θ ^ 2 := by
    funext θ
    rw [circleMap_zero_eq_smul]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  rw [this, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_sq_two_pi, integral_sin_mul_cos_two_pi,
    integral_sin_sq_two_pi]
  · ring
  · exact (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  · exact (continuous_const.mul (Real.continuous_sin.mul Real.continuous_cos)).intervalIntegrable
      _ _
  · exact ((continuous_const.mul (Real.continuous_cos.pow 2)).add
      (continuous_const.mul (Real.continuous_sin.mul Real.continuous_cos))).intervalIntegrable _ _
  · exact (continuous_const.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _

/-- **Second-order expansion of circle averages.** For a `C²` function, the circle average
of radius `r` differs from the center value by `r ^ 2 / 4` times the Laplacian, up to
`ε r ^ 2` for all small `r`. -/
theorem exists_circleAverage_sub_le (hg : ContDiffAt ℝ 2 g t₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r, 0 < r → r < δ → CircleIntegrable g t₀ r ∧
      |circleAverage g t₀ r - g t₀ - r ^ 2 / 4 * Δ g t₀| ≤ ε * r ^ 2 := by
  obtain ⟨δ₁, hδ₁, htaylor⟩ := exists_taylor_bound hg hε
  obtain ⟨δ₂, hδ₂, hcont⟩ := Metric.mem_nhds_iff.mp (hg.eventually (by simp))
  have hgc : ContinuousOn g (ball t₀ δ₂) := fun y hy =>
    (show ContDiffAt ℝ 2 g y from hcont hy).continuousAt.continuousWithinAt
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun r hr hrδ => ?_⟩
  set D := fderiv ℝ g with hDdef
  set B := fderiv ℝ (fderiv ℝ g) t₀ with hBdef
  have hmap : ∀ θ : ℝ, circleMap t₀ r θ = t₀ + circleMap 0 r θ := fun θ => by
    simp [circleMap]
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 r θ‖ = r := fun θ => by
    simp [circleMap, abs_of_pos hr]
  have hint : CircleIntegrable g t₀ r := by
    refine ContinuousOn.circleIntegrable hr.le (hgc.mono fun z hz => ?_)
    exact sphere_subset_closedBall.trans (closedBall_subset_ball (hrδ.trans_le (min_le_right _
      _))) hz
  refine ⟨hint, ?_⟩
  -- the remainder as a function of the angle
  set R : ℝ → ℝ := fun θ => g (t₀ + circleMap 0 r θ) - g t₀ - D t₀ (circleMap 0 r θ) -
    (1 / 2) * B (circleMap 0 r θ) (circleMap 0 r θ) with hRdef
  have hRle : ∀ θ, |R θ| ≤ ε * r ^ 2 := fun θ => by
    have := htaylor (circleMap 0 r θ) (by rw [hnorm]; exact hrδ.trans_le (min_le_left _ _))
    rwa [hnorm] at this
  have hRint : ‖∫ θ in (0 : ℝ)..2 * π, R θ‖ ≤ ε * r ^ 2 * |2 * π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => by
      rw [Real.norm_eq_abs]; exact hRle θ
  rw [sub_zero, abs_of_pos Real.two_pi_pos, Real.norm_eq_abs] at hRint
  -- integrability of the pieces
  have hcm : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hi₁ : IntervalIntegrable (fun θ => g (t₀ + circleMap 0 r θ)) volume 0 (2 * π) := by
    have := (circleIntegrable_def g t₀ r).mp hint
    simpa only [hmap] using this
  have hi₂ : IntervalIntegrable (fun θ => D t₀ (circleMap 0 r θ)) volume 0 (2 * π) :=
    ((D t₀).continuous.comp hcm).intervalIntegrable _ _
  have hi₃ : IntervalIntegrable (fun θ => (1 / 2 : ℝ) * B (circleMap 0 r θ) (circleMap 0 r θ))
      volume 0 (2 * π) :=
    (continuous_const.mul (B.continuous₂.comp (hcm.prodMk hcm))).intervalIntegrable _ _
  -- the integral identity
  have hsplit : ∫ θ in (0 : ℝ)..2 * π, R θ =
      (∫ θ in (0 : ℝ)..2 * π, g (t₀ + circleMap 0 r θ)) - 2 * π * g t₀ -
        (∫ θ in (0 : ℝ)..2 * π, D t₀ (circleMap 0 r θ)) -
        ∫ θ in (0 : ℝ)..2 * π, (1 / 2 : ℝ) * B (circleMap 0 r θ) (circleMap 0 r θ) := by
    simp only [hRdef]
    rw [intervalIntegral.integral_sub ((hi₁.sub intervalIntegrable_const).sub hi₂) hi₃,
      intervalIntegral.integral_sub (hi₁.sub intervalIntegrable_const) hi₂,
      intervalIntegral.integral_sub hi₁ intervalIntegrable_const, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [integral_clm_circleMap_zero, intervalIntegral.integral_const_mul, integral_bilinear_circleMap,
    sub_zero] at hsplit
  have havg : circleAverage g t₀ r = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, g (t₀ + circleMap 0 r θ)
    := by
    rw [circleAverage_def, smul_eq_mul]
    simp only [hmap]
  have hlap : Δ g t₀ = B 1 1 + B I I := laplacian_eq_fderiv_fderiv g t₀
  have hkey : circleAverage g t₀ r - g t₀ - r ^ 2 / 4 * Δ g t₀ =
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, R θ := by
    rw [havg, hlap, hsplit]
    field_simp
    ring
  rw [hkey, abs_mul, abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, R θ| ≤ (2 * π)⁻¹ * (ε * r ^ 2 * (2 * π)) :=
        mul_le_mul_of_nonneg_left hRint (inv_pos.mpr Real.two_pi_pos).le
    _ = ε * r ^ 2 := by field_simp

/-- A positive Laplacian gives the strict submean inequality on all small circles. -/
theorem eventually_lt_circleAverage_of_laplacian_pos (hg : ContDiffAt ℝ 2 g t₀)
    (hΔ : 0 < Δ g t₀) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), CircleIntegrable g t₀ r ∧ g t₀ < circleAverage g t₀ r := by
  obtain ⟨δ, hδ, h⟩ := exists_circleAverage_sub_le hg (ε := Δ g t₀ / 8) (by positivity)
  refine mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨δ, hδ, fun r hr => ?_⟩
  obtain ⟨hint, hle⟩ := h r hr.1 hr.2
  refine ⟨hint, ?_⟩
  have := (abs_le.mp hle).1
  nlinarith [sq_pos_of_pos hr.1]

/-- A negative Laplacian gives the strict reverse inequality on all small circles. -/
theorem eventually_circleAverage_lt_of_laplacian_neg (hg : ContDiffAt ℝ 2 g t₀)
    (hΔ : Δ g t₀ < 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), CircleIntegrable g t₀ r ∧ circleAverage g t₀ r < g t₀ := by
  obtain ⟨δ, hδ, h⟩ := exists_circleAverage_sub_le hg (ε := -Δ g t₀ / 8) (by linarith)
  refine mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨δ, hδ, fun r hr => ?_⟩
  obtain ⟨hint, hle⟩ := h r hr.1 hr.2
  refine ⟨hint, ?_⟩
  have := (abs_le.mp hle).2
  nlinarith [sq_pos_of_pos hr.1]

/-- A `C²` function with positive Laplacian has the local submean property. -/
theorem hasSubmeanAt_of_laplacian_pos (hg : ContDiffAt ℝ 2 g t₀) (hΔ : 0 < Δ g t₀) :
    HasSubmeanAt g t₀ :=
  (eventually_lt_circleAverage_of_laplacian_pos hg hΔ).mono fun _ h => ⟨h.1, h.2.le⟩

/-- **Necessity.** A `C²` subharmonic function has nonnegative Laplacian. -/
theorem HasSubmeanAt.laplacian_nonneg (hg : ContDiffAt ℝ 2 g t₀) (hs : HasSubmeanAt g t₀) :
    0 ≤ Δ g t₀ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, ⟨_, h₁⟩, ⟨_, h₂⟩⟩ :=
    ((eventually_circleAverage_lt_of_laplacian_neg hg hlt).and hs).exists
  linarith

/-- The Laplacian of the squared distance to a point is `4`. -/
theorem laplacian_normSq_sub (t₀ t : ℂ) : Δ (fun z : ℂ => ‖z - t₀‖ ^ 2) t = 4 := by
  have hq : (fun z : ℂ => ‖z - t₀‖ ^ 2) = fun z => (Complex.reCLM (z - t₀)) ^ 2 +
      (Complex.imCLM (z - t₀)) ^ 2 := by
    funext z
    simp only [Complex.reCLM_apply, Complex.imCLM_apply, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hD : ∀ z, HasFDerivAt (fun z : ℂ => ‖z - t₀‖ ^ 2)
      ((2 * (z - t₀).re) • Complex.reCLM + (2 * (z - t₀).im) • Complex.imCLM) z := by
    intro z
    rw [hq]
    have h1 : HasFDerivAt (fun z : ℂ => Complex.reCLM (z - t₀)) Complex.reCLM z :=
      Complex.reCLM.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const t₀) |>.congr_fderiv (by simp)
    have h2 : HasFDerivAt (fun z : ℂ => Complex.imCLM (z - t₀)) Complex.imCLM z :=
      Complex.imCLM.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const t₀) |>.congr_fderiv (by simp)
    have := (h1.pow 2).add (h2.pow 2)
    convert this using 1
    ext s
    simp [Complex.reCLM_apply, Complex.imCLM_apply]
  have hfd : fderiv ℝ (fun z : ℂ => ‖z - t₀‖ ^ 2) =
      fun z => (2 * (z - t₀).re) • Complex.reCLM + (2 * (z - t₀).im) • Complex.imCLM :=
    funext fun z => (hD z).fderiv
  -- second derivative: differentiate the coefficient functions
  have h1 : HasFDerivAt (fun z : ℂ => 2 * (z - t₀).re) ((2 : ℝ) • Complex.reCLM) t := by
    have h := Complex.reCLM.hasFDerivAt.comp t ((hasFDerivAt_id t).sub_const t₀)
    have := h.const_mul (2 : ℝ)
    refine this.congr_fderiv ?_
    ext s
    simp
  have h2 : HasFDerivAt (fun z : ℂ => 2 * (z - t₀).im) ((2 : ℝ) • Complex.imCLM) t := by
    have h := Complex.imCLM.hasFDerivAt.comp t ((hasFDerivAt_id t).sub_const t₀)
    have := h.const_mul (2 : ℝ)
    refine this.congr_fderiv ?_
    ext s
    simp
  have hD2 : HasFDerivAt (fun z : ℂ => (2 * (z - t₀).re) • Complex.reCLM +
      (2 * (z - t₀).im) • Complex.imCLM) _ t :=
    (h1.smul_const Complex.reCLM).add (h2.smul_const Complex.imCLM)
  rw [laplacian_eq_fderiv_fderiv, hfd, hD2.fderiv]
  simp
  norm_num

/-- **Sufficiency.** A `C²` function with nonnegative Laplacian on an open set is subharmonic. -/
theorem subharmonicOn_of_laplacian_nonneg {U : Set ℂ} (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hΔ : ∀ t ∈ U, 0 ≤ Δ g t) : SubharmonicOn g U := by
  refine ⟨hg.continuousOn.upperSemicontinuousOn, fun a ha => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  refine hasSubmeanAt_of_forall_lt hρ fun r hr hrρ => ?_
  have hsub : closedBall a r ⊆ U := (closedBall_subset_ball hrρ).trans hball
  have hint : CircleIntegrable g a r :=
    (hg.continuousOn.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hr.le
  refine ⟨hint, le_of_forall_pos_le_add fun ε hε => ?_⟩
  set η : ℝ := ε / r ^ 2 with hη
  have hη0 : 0 < η := div_pos hε (by positivity)
  -- the perturbed function
  set q : ℂ → ℝ := fun z => ‖z - a‖ ^ 2 with hqdef
  have hqc : ContDiff ℝ 2 q := by
    have : q = fun z : ℂ => (Complex.reCLM (z - a)) ^ 2 + (Complex.imCLM (z - a)) ^ 2 := by
      funext z
      simp only [hqdef, Complex.reCLM_apply, Complex.imCLM_apply, Complex.sq_norm,
        Complex.normSq_apply]
      ring
    rw [this]
    fun_prop
  set gε : ℂ → ℝ := fun z => g z + η * q z with hgεdef
  have hgε : ContDiffOn ℝ 2 gε U := hg.add (hqc.contDiffOn.const_smul η |>.congr fun z _ => rfl)
  have hΔε : ∀ t ∈ U, 0 < Δ gε t := by
    intro t ht
    have h1 : ContDiffAt ℝ 2 g t := hg.contDiffAt (hU.mem_nhds ht)
    have h2 : ContDiffAt ℝ 2 (fun z => η * q z) t := by
      have := hqc.contDiffAt (x := t)
      exact this.const_smul η |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => rfl)
    have hadd := ContDiffAt.laplacian_add h1 h2
    have hsm : Δ (fun z => η * q z) t = η * Δ q t := by
      have := InnerProductSpace.laplacian_smul (𝕜 := ℝ) η (hqc.contDiffAt (x := t))
      simpa [Pi.smul_def, smul_eq_mul] using this
    have hq4 : Δ q t = 4 := laplacian_normSq_sub a t
    have : Δ gε t = Δ g t + η * 4 := by
      rw [hgεdef]
      change Δ (g + fun z => η * q z) t = _
      rw [hadd, hsm, hq4]
    rw [this]
    linarith [hΔ t ht]
  have hsub_ε : SubharmonicOn gε U :=
    ⟨hgε.continuousOn.upperSemicontinuousOn, fun t ht =>
      hasSubmeanAt_of_laplacian_pos (hgε.contDiffAt (hU.mem_nhds ht)) (hΔε t ht)⟩
  have hmean := hsub_ε.le_circleAverage_of_continuousOn hgε.continuousOn hr hsub
  have hqint : CircleIntegrable (fun z => η * q z) a r :=
    (continuous_const.mul (hqc.continuous)).continuousOn.circleIntegrable hr.le
  have hqavg : circleAverage (fun z => η * q z) a r = η * r ^ 2 := by
    rw [circleAverage_congr_sphere (f₂ := fun _ => η * r ^ 2), circleAverage_const]
    intro z hz
    simp only [hqdef]
    rw [abs_of_pos hr] at hz
    rw [mem_sphere, dist_eq_norm] at hz
    rw [hz]
  have havg : circleAverage gε a r = circleAverage g a r + η * r ^ 2 := by
    rw [hgεdef, circleAverage_fun_add hint hqint, hqavg]
  have hga : gε a = g a := by simp [hgεdef, hqdef]
  rw [havg, hga] at hmean
  have hηr : η * r ^ 2 = ε := by
    rw [hη]
    field_simp
  rw [hηr] at hmean
  exact hmean

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
