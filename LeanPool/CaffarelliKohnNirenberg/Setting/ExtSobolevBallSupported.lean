/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.InterpolationBall
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallFaithful
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.ProdSwap

/-!
# Ext Sobolev Ball Supported

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

namespace CKN

private theorem euclideanBall_eq_vec3Ball_extSobolev
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

/-- The absolute-constant unit-ball instance of external Sobolev embedding
clause (ii), with the repository's representative-level `H¹` norm. -/
theorem extSobolevBall_unitBall
    (x₀ : Vec3) (v : H1Function (euclideanBall x₀ 1)) :
    lpNormOn 6 (euclideanBall x₀ 1) v.toFun ≤
      ENNReal.ofReal sobolevPoincareFaithfulC5 *
        (weakGradientLpNormOn 2 (euclideanBall x₀ 1) v.grad +
          lpNormOn 2 (euclideanBall x₀ 1) v.toFun) := by
  have hball := euclideanBall_eq_vec3Ball_extSobolev
    (x₀ := x₀) (r := 1) (by norm_num)
  have h := (sobolevPoincare_ball_L6_faithful x₀ (by norm_num)).2 v
  simpa [hball] using h

/-- The scale-explicit `H¹ → L⁶` estimate on every Euclidean ball, with the
same absolute constant as the faithful ball Sobolev–Poincaré result. -/
theorem extSobolevBall_everyBall
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    (v : H1Function (euclideanBall x₀ r)) :
    lpNormOn 6 (euclideanBall x₀ r) v.toFun ≤
      ENNReal.ofReal sobolevPoincareFaithfulC5 *
        (weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad +
          (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) v.toFun) := by
  have hball := euclideanBall_eq_vec3Ball_extSobolev (x₀ := x₀) hr
  have h := (sobolevPoincare_ball_L6_faithful x₀ hr).2 v
  simpa [hball] using h

/-- The spatial `q = 10/3` interpolation inequality on every Euclidean ball;
this is the integrand estimate used for the ball case of clause (iv). -/
theorem extSobolevBall_spatialTenThirds :
    ∃ C₆ : ℝ≥0∞, C₆ ≠ ∞ ∧ ∀ {x₀ : Vec3} {r : ℝ}, 0 < r →
      ∀ v : H1Function (euclideanBall x₀ r),
        lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r) v.toFun ^ (10 / 3 : ℝ) ≤
          C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^ (2 : ℕ) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (4 / 3 : ℝ) +
            C₆ * (ENNReal.ofReal r) ^ (-(2 : ℝ)) *
              lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (10 / 3 : ℝ) := by
  obtain ⟨C₆, hC₆, hC⟩ := interpolationBall_finite
  refine ⟨C₆, hC₆, ?_⟩
  intro x₀ r hr v
  have h := hC (10 / 3) (by norm_num) (by norm_num) hr v
  change lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r) v.toFun ^ (10 / 3 : ℝ) ≤
      C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^
          (2 * (3 * ((10 / 3 : ℝ) - 2) / 4)) *
        lpNormOn 2 (euclideanBall x₀ r) v.toFun ^
          ((10 / 3 : ℝ) - 2 * (3 * ((10 / 3 : ℝ) - 2) / 4)) +
      C₆ * (ENNReal.ofReal r) ^ (-(2 * (3 * ((10 / 3 : ℝ) - 2) / 4))) *
        lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (10 / 3 : ℝ) at h
  norm_num at h
  exact h

/-- Time integration of the same-ball `q = 10/3` inequality.  `hA` is the
essential `L∞_t L²_x` bound and `hG` is the integrated squared spatial-gradient
bound. -/
theorem extSobolevBall_timeTenThirds
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) {J : Set ℝ}
    {u : ℝ → H1Function (euclideanBall x₀ r)} {A G : ℝ≥0∞}
    (hA : ∀ᵐ t ∂(volume.restrict J),
      lpNormOn 2 (euclideanBall x₀ r) (u t).toFun ≤ A)
    (hgrad : AEMeasurable
      (fun t => weakGradientLpNormOn 2 (euclideanBall x₀ r) (u t).grad ^ (2 : ℕ))
      (volume.restrict J))
    (hG : ∫⁻ t,
      weakGradientLpNormOn 2 (euclideanBall x₀ r) (u t).grad ^ (2 : ℕ)
        ∂(volume.restrict J) ≤ G) :
    ∃ C₆ : ℝ≥0∞, C₆ ≠ ∞ ∧
      (∫⁻ t,
        lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r) (u t).toFun ^ (10 / 3 : ℝ)
          ∂(volume.restrict J)) ≤
        C₆ * A ^ (4 / 3 : ℝ) * G +
          C₆ * (ENNReal.ofReal r) ^ (-(2 : ℝ)) * A ^ (10 / 3 : ℝ) * volume J := by
  obtain ⟨C₆, hC₆, hC⟩ := interpolationBall_finite
  refine ⟨C₆, hC₆, ?_⟩
  let D : ℝ → ℝ≥0∞ :=
    fun t => weakGradientLpNormOn 2 (euclideanBall x₀ r) (u t).grad ^ (2 : ℕ)
  let M : ℝ → ℝ≥0∞ := fun t => lpNormOn 2 (euclideanBall x₀ r) (u t).toFun
  let Q : ℝ≥0∞ := (ENNReal.ofReal r) ^ (-(2 : ℝ))
  have hpoint : ∀ᵐ t ∂(volume.restrict J),
      lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r) (u t).toFun ^ (10 / 3 : ℝ) ≤
        C₆ * D t * A ^ (4 / 3 : ℝ) + C₆ * Q * A ^ (10 / 3 : ℝ) := by
    filter_upwards [hA] with t ht
    have hslice := hC (10 / 3) (by norm_num) (by norm_num) hr (u t)
    have hslice' :
        lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r) (u t).toFun ^ (10 / 3 : ℝ) ≤
          C₆ * D t * M t ^ (4 / 3 : ℝ) +
            C₆ * Q * M t ^ (10 / 3 : ℝ) := by
      change lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r) (u t).toFun ^ (10 / 3 :
        ℝ) ≤
          C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) (u t).grad ^
              (2 * (3 * ((10 / 3 : ℝ) - 2) / 4)) *
            lpNormOn 2 (euclideanBall x₀ r) (u t).toFun ^
              ((10 / 3 : ℝ) - 2 * (3 * ((10 / 3 : ℝ) - 2) / 4)) +
          C₆ * (ENNReal.ofReal r) ^ (-(2 * (3 * ((10 / 3 : ℝ) - 2) / 4))) *
            lpNormOn 2 (euclideanBall x₀ r) (u t).toFun ^ (10 / 3 : ℝ) at hslice
      norm_num at hslice
      simpa [D, M, Q] using hslice
    have hpow₁ : M t ^ (4 / 3 : ℝ) ≤ A ^ (4 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow ht (by norm_num)
    have hpow₂ : M t ^ (10 / 3 : ℝ) ≤ A ^ (10 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow ht (by norm_num)
    exact hslice'.trans (add_le_add (by gcongr) (by gcongr))
  have hq1 : AEMeasurable (fun t => (C₆ * A ^ (4 / 3 : ℝ)) * D t)
      (volume.restrict J) := by
    exact hgrad.const_mul (C₆ * A ^ (4 / 3 : ℝ))
  have hsum :
      (∫⁻ t,
        C₆ * D t * A ^ (4 / 3 : ℝ) + C₆ * Q * A ^ (10 / 3 : ℝ)
          ∂(volume.restrict J)) =
        C₆ * A ^ (4 / 3 : ℝ) * (∫⁻ t, D t ∂(volume.restrict J)) +
          C₆ * Q * A ^ (10 / 3 : ℝ) * volume J := by
    calc
      _ = ∫⁻ t, (C₆ * A ^ (4 / 3 : ℝ)) * D t + C₆ * Q * A ^ (10 / 3 : ℝ)
            ∂(volume.restrict J) := by
          congr 1
          funext t
          ring
    _ = _ := by
        rw [lintegral_add_left' hq1]
        rw [lintegral_const_mul'' _ hgrad]
        simp only [lintegral_const]
        simp [D, volume.restrict_apply_univ]
  calc
    _ ≤ ∫⁻ t,
          C₆ * D t * A ^ (4 / 3 : ℝ) + C₆ * Q * A ^ (10 / 3 : ℝ)
            ∂(volume.restrict J) :=
        lintegral_mono_ae hpoint
    _ = C₆ * A ^ (4 / 3 : ℝ) * (∫⁻ t, D t ∂(volume.restrict J)) +
          C₆ * Q * A ^ (10 / 3 : ℝ) * volume J := hsum
    _ ≤ C₆ * A ^ (4 / 3 : ℝ) * G +
          C₆ * Q * A ^ (10 / 3 : ℝ) * volume J := by
        gcongr

private theorem lpNormOn_tenThirds_pow_eq_lintegral
    {S : Set Vec3} {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict S)) :
    lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) S f ^ (10 / 3 : ℝ) =
      ∫⁻ x in S, ‖f x‖ₑ ^ (10 / 3 : ℝ) := by
  dsimp [lpNormOn]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3),
    ← ENNReal.rpow_mul]
  norm_num

/-- Identify the product-space `L^(10/3)` integral with the time integral of
the `H¹` slice norms when the measurable space-time representative agrees
with those slices almost everywhere. -/
theorem extSobolevBall_productIntegral_eq_timeSlices
    {x₀ : Vec3} {r : ℝ} {J : Set ℝ}
    {g : Vec3 × ℝ → ℝ} {u : ℝ → H1Function (euclideanBall x₀ r)}
    (hF : AEMeasurable
      (fun z => ‖g z‖ₑ ^ (10 / 3 : ℝ))
      ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)))
    (hrep : ∀ᵐ s ∂(volume.restrict J),
      ∀ᵐ x ∂(volume.restrict (euclideanBall x₀ r)),
        g (x, s) = (u s).toFun x) :
    (∫⁻ z in euclideanBall x₀ r ×ˢ J, ‖g z‖ₑ ^ (10 / 3 : ℝ)) =
      ∫⁻ s in J,
        lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r)
          (u s).toFun ^ (10 / 3 : ℝ) := by
  rw [CKN.Foundation.Parabolic.Integration.prod_lintegral_swap_cyl
    (S := euclideanBall x₀ r) (T := J) hF]
  apply lintegral_congr_ae
  filter_upwards [hrep] with s hs
  calc
    ∫⁻ x in euclideanBall x₀ r, ‖g (x, s)‖ₑ ^ (10 / 3 : ℝ) =
        ∫⁻ x in euclideanBall x₀ r,
          ‖(u s).toFun x‖ₑ ^ (10 / 3 : ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [hs] with x hx
      rw [hx]
    _ = lpNormOn (ENNReal.ofReal (10 / 3 : ℝ)) (euclideanBall x₀ r)
          (u s).toFun ^ (10 / 3 : ℝ) := by
      symm
      exact lpNormOn_tenThirds_pow_eq_lintegral (u s).memL2.aestronglyMeasurable

/-- Product-space ball form of the parabolic `L^(10/3)` estimate. -/
theorem extSobolevBall_productTenThirds
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) {J : Set ℝ}
    {g : Vec3 × ℝ → ℝ} {u : ℝ → H1Function (euclideanBall x₀ r)}
    {A : ℝ≥0∞}
    (hA : ∀ᵐ t ∂(volume.restrict J),
      lpNormOn 2 (euclideanBall x₀ r) (u t).toFun ≤ A)
    (hgrad : AEMeasurable
      (fun t => weakGradientLpNormOn 2 (euclideanBall x₀ r) (u t).grad ^ (2 : ℕ))
      (volume.restrict J))
    (hF : AEMeasurable
      (fun z => ‖g z‖ₑ ^ (10 / 3 : ℝ))
      ((volume.restrict (euclideanBall x₀ r)).prod (volume.restrict J)))
    (hrep : ∀ᵐ s ∂(volume.restrict J),
      ∀ᵐ x ∂(volume.restrict (euclideanBall x₀ r)),
        g (x, s) = (u s).toFun x) :
    ∃ C₆ : ℝ≥0∞, C₆ ≠ ∞ ∧
      (∫⁻ z in euclideanBall x₀ r ×ˢ J, ‖g z‖ₑ ^ (10 / 3 : ℝ)) ≤
        C₆ * A ^ (4 / 3 : ℝ) *
            (∫⁻ t, weakGradientLpNormOn 2 (euclideanBall x₀ r) (u t).grad ^ (2 : ℕ)
              ∂(volume.restrict J)) +
          C₆ * (ENNReal.ofReal r) ^ (-(2 : ℝ)) * A ^ (10 / 3 : ℝ) * volume J := by
  obtain ⟨C₆, hC₆, htime⟩ :=
    extSobolevBall_timeTenThirds hr hA hgrad (G :=
      ∫⁻ t, weakGradientLpNormOn 2 (euclideanBall x₀ r) (u t).grad ^ (2 : ℕ)
        ∂(volume.restrict J)) le_rfl
  refine ⟨C₆, hC₆, ?_⟩
  rw [extSobolevBall_productIntegral_eq_timeSlices hF hrep]
  exact htime

end CKN
