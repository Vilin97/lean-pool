/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorWeak
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Interior Representative

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology Convolution
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

/-! The fixed-annulus representative used for weakly harmonic functions. -/

/-- Interior representative constructed from a weakly harmonic function by Newtonian integration.
-/
noncomputable def weakHarmonicInteriorRepresentative
    (h : Vec3 → ℝ) (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (x : Vec3) : ℝ :=
  (-∫ y : Vec3, newtonianKernel (x - y) *
      (h y * CKN.spatialLaplacian (eta x₀ hρ) y)) +
    2 * ∑ i : Fin 3, ∫ y : Vec3,
      h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y

/-- Source coefficient in the weakly harmonic interior representation estimate. -/
noncomputable def weakHarmonicInteriorSourceConstant : ℝ :=
  (4 * Real.pi)⁻¹ * 60 * cutoffSecondDerivativeConstant

/-- Cutoff-derivative coefficient in the weakly harmonic representation estimate. -/
noncomputable def weakHarmonicInteriorCutoffConstant : ℝ :=
  (4 * Real.pi)⁻¹ * (400 * cutoffGradientConstant +
    20 * cutoffSecondDerivativeConstant)

/-- Spatial-gradient coefficient for the cutoff part of the weak harmonic representation. -/
noncomputable def weakHarmonicInteriorXGradientConstant : ℝ :=
  (4 * Real.pi)⁻¹ * (32000 * cutoffGradientConstant +
    400 * cutoffSecondDerivativeConstant)

/-- Spatial-gradient coefficient for the source part of the weak harmonic representation. -/
noncomputable def weakHarmonicInteriorSourceXGradientConstant : ℝ :=
  (4 * Real.pi)⁻¹ * (1200 * cutoffSecondDerivativeConstant)

/-- Supremum coefficient for the weakly harmonic interior representative. -/
noncomputable def weakHarmonicInteriorSupConstant : ℝ :=
  (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
    (weakHarmonicInteriorSourceConstant +
      6 * weakHarmonicInteriorCutoffConstant)

/-- Gradient coefficient for the weakly harmonic interior representative. -/
noncomputable def weakHarmonicInteriorGradientConstant : ℝ :=
  (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
    (weakHarmonicInteriorSourceConstant +
      6 * weakHarmonicInteriorXGradientConstant)

lemma weakHarmonicInteriorSourceConstant_nonneg :
    0 ≤ weakHarmonicInteriorSourceConstant := by
  dsimp [weakHarmonicInteriorSourceConstant]
  have hS := cutoffSecondDerivativeConstant_nonneg_global
  positivity

lemma weakHarmonicInteriorCutoffConstant_nonneg :
    0 ≤ weakHarmonicInteriorCutoffConstant := by
  dsimp [weakHarmonicInteriorCutoffConstant]
  have hG := cutoffGradientConstant_nonneg_global
  have hS := cutoffSecondDerivativeConstant_nonneg_global
  positivity

lemma weakHarmonicInteriorXGradientConstant_nonneg :
    0 ≤ weakHarmonicInteriorXGradientConstant := by
  dsimp [weakHarmonicInteriorXGradientConstant]
  have hG := cutoffGradientConstant_nonneg_global
  have hS := cutoffSecondDerivativeConstant_nonneg_global
  positivity

lemma weakHarmonicInteriorSupConstant_nonneg :
    0 ≤ weakHarmonicInteriorSupConstant := by
  dsimp [weakHarmonicInteriorSupConstant]
  have hS := weakHarmonicInteriorSourceConstant_nonneg
  have hC := weakHarmonicInteriorCutoffConstant_nonneg
  positivity

lemma weakHarmonicInteriorSourceXGradientConstant_nonneg :
    0 ≤ weakHarmonicInteriorSourceXGradientConstant := by
  dsimp [weakHarmonicInteriorSourceXGradientConstant]
  have hS := cutoffSecondDerivativeConstant_nonneg_global
  positivity

lemma weak_annulus_distance
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ ρ) :
    ρ / 20 < ‖x - y‖ := by
  have hx' : vec3EuclideanNorm (x - x₀) < ρ / 2 :=
    by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
        (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  have hy' : 13 * ρ / 20 < vec3EuclideanNorm (y - x₀) := by
    have hnot : y ∉ euclideanClosedBall x₀ (13 * ρ / 20) := hy.2
    by_contra hle
    apply hnot
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    exact le_of_not_gt (by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hle)
  have htri : vec3EuclideanNorm (y - x₀) ≤
      vec3EuclideanNorm (x - y) + vec3EuclideanNorm (x - x₀) := by
    rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
      vec3EuclideanNorm_eq_l2]
    calc
      ‖WithLp.toLp 2 (y - x₀)‖ =
          ‖WithLp.toLp 2 ((y - x) + (x - x₀))‖ := by
            congr 1
            ext i
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
      _ ≤ ‖WithLp.toLp 2 (y - x)‖ +
          ‖WithLp.toLp 2 (x - x₀)‖ := norm_add_le _ _
      _ = ‖WithLp.toLp 2 (x - y)‖ +
          ‖WithLp.toLp 2 (x - x₀)‖ := by
            have hneg : y - x = -(x - y) := by
              ext i
              simp only [Pi.neg_apply, Pi.sub_apply]
              ring
            rw [hneg, WithLp.toLp_neg, norm_neg]
  have hvec : 3 * (ρ / 20) < vec3EuclideanNorm (x - y) := by
    nlinarith only [hy', htri, hx', hρ]
  have hthree := CKN.euclideanNorm_le_three_mul_space_norm (x - y)
  have hthree' : vec3EuclideanNorm (x - y) ≤ 3 * ‖x - y‖ := by
    simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hthree
  nlinarith only [hvec, hthree', hρ]

lemma weak_annulus_subset_outer
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    cutoffAnnulus x₀ ρ ⊆ euclideanBall x₀ ρ := by
  intro y hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
  have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy.1
  have hy'' : vecEuclideanNorm (y - x₀) < ρ := by
    exact hy'.trans (by
      calc
        3 * ρ / 4 = (3 / 4 : ℝ) * ρ := by ring
        _ < 1 * ρ := by gcongr; norm_num
        _ = ρ := by ring)
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hy''

lemma weak_source_kernel_bound
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ ρ) :
    |newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y| ≤
      weakHarmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
  have hd := weak_annulus_distance hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 20)) (by simpa using hd)
  have hk := newtonianKernel_size_bound hxy
  have hki : ‖x - y‖⁻¹ ≤ (ρ / 20)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hd.le
  have hs := eta_laplacian_bound_global x₀ hρ y
  rw [abs_mul]
  calc
    |newtonianKernel (x - y)| *
        |CKN.spatialLaplacian (eta x₀ hρ) y| ≤
      ((4 * Real.pi)⁻¹ * (ρ / 20)⁻¹) *
        (3 * cutoffSecondDerivativeConstant / ρ ^ 2) := by
          gcongr
          exact hk.trans (mul_le_mul_of_nonneg_left hki (by positivity))
    _ = weakHarmonicInteriorSourceConstant * (ρ ^ 3)⁻¹ := by
      dsimp [weakHarmonicInteriorSourceConstant]
      field_simp [hρ.ne']
      ring

lemma weak_cutoff_kernel_bound
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    {y : Vec3} (hy : y ∈ cutoffAnnulus x₀ ρ) (i : Fin 3) :
    |CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y| ≤
      weakHarmonicInteriorCutoffConstant * (ρ ^ 3)⁻¹ := by
  have hd := weak_annulus_distance hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 20)) (by simpa using hd)
  have hk := newtonianKernel_size_bound hxy
  have hki : ‖x - y‖⁻¹ ≤ (ρ / 20)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hd.le
  have hdi := newtonianKernel_spatialDeriv_size_bound hxy i
  have hd2 : (‖x - y‖ ^ 2)⁻¹ ≤ ((ρ / 20) ^ 2)⁻¹ := by gcongr
  have hdi' : |CKN.spatialDeriv newtonianKernel i (x - y)| ≤
      (4 * Real.pi)⁻¹ * ((ρ / 20) ^ 2)⁻¹ := by
    exact hdi.trans (mul_le_mul_of_nonneg_left hd2 (by positivity))
  have he := eta_spatialDeriv_bound_global x₀ hρ y i
  have hs := eta_spatialSecond_bound_global x₀ hρ y i i
  rw [spatialDeriv_kernelCutoffDerivative_of_ne hρ hxy]
  calc
    |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) i y *
          CKN.spatialDeriv (eta x₀ hρ) i y +
        newtonianKernel (x - y) *
          CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) i y| ≤
      |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) i y| *
          |CKN.spatialDeriv (eta x₀ hρ) i y| +
        |newtonianKernel (x - y)| *
          |CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) i y| := by
            calc
              _ ≤ |CKN.spatialDeriv (fun z => newtonianKernel (x - z)) i y *
                  CKN.spatialDeriv (eta x₀ hρ) i y| +
                |newtonianKernel (x - y) *
                  CKN.spatialDeriv (CKN.spatialDeriv
                    (eta x₀ hρ) i) i y| := abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul]
    _ ≤ ((4 * Real.pi)⁻¹ * ((ρ / 20) ^ 2)⁻¹) *
          (cutoffGradientConstant / ρ) +
        ((4 * Real.pi)⁻¹ * (ρ / 20)⁻¹) *
          (cutoffSecondDerivativeConstant / ρ ^ 2) := by
            have hshift : |CKN.spatialDeriv
                (fun z => newtonianKernel (x - z)) i y| =
                |CKN.spatialDeriv newtonianKernel i (x - y)| := by
              rw [spatialDeriv_newtonianKernel_shift_eq_neg hxy, abs_neg]
            rw [hshift]
            exact add_le_add (mul_le_mul hdi' he (by positivity) (by positivity))
              (mul_le_mul (hk.trans
                (mul_le_mul_of_nonneg_left hki (by positivity))) hs
                (by positivity) (by positivity))
    _ = weakHarmonicInteriorCutoffConstant * (ρ ^ 3)⁻¹ := by
      dsimp [weakHarmonicInteriorCutoffConstant]
      field_simp [hρ.ne']
      ring

lemma weak_cutoff_x_derivative_bound
    {x x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    (hy : y ∈ cutoffAnnulus x₀ ρ) (i j : Fin 3) :
    |CKN.spatialDeriv (fun z : Vec3 =>
      CKN.spatialDeriv (kernelCutoffDerivative z x₀ hρ i) i y) j x| ≤
      weakHarmonicInteriorXGradientConstant * (ρ ^ 4)⁻¹ := by
  have hd := weak_annulus_distance hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 20)) (by simpa using hd)
  have hne_event : ∀ᶠ z : Vec3 in 𝓝 x, z - y ≠ 0 := by
    have hopen : IsOpen ({(0 : Vec3)}ᶜ) := isClosed_singleton.isOpen_compl
    have hpre : IsOpen ((fun z : Vec3 => z - y) ⁻¹' {(0 : Vec3)}ᶜ) :=
      hopen.preimage (by fun_prop)
    apply hpre.mem_nhds
    exact hxy
  let A : Vec3 → ℝ := fun z =>
    CKN.spatialDeriv (fun w : Vec3 => newtonianKernel (z - w)) i y
  let B : Vec3 → ℝ := fun z => newtonianKernel (z - y)
  let E : ℝ := CKN.spatialDeriv (eta x₀ hρ) i y
  let F : ℝ := CKN.spatialDeriv (CKN.spatialDeriv (eta x₀ hρ) i) i y
  have hA : HasFDerivAt A
      (-(fderiv ℝ (CKN.spatialDeriv newtonianKernel i) (x - y))) x := by
    have hinner : HasFDerivAt (fun z : Vec3 => z - y)
        (1 : Vec3 →L[ℝ] Vec3) x := by
      exact hasFDerivAt_sub_const y
    have houter := (hasFDerivAt_newtonianKernel_spatialDeriv_formula hxy i).comp
      x hinner
    have houter' : HasFDerivAt (fun z : Vec3 =>
        CKN.spatialDeriv newtonianKernel i (z - y))
        (fderiv ℝ (CKN.spatialDeriv newtonianKernel i) (x - y)) x := by
      convert houter using 1
      · rfl
      · rw [(hasFDerivAt_newtonianKernel_spatialDeriv_formula hxy i).fderiv]
        ext v
        simp [ContinuousLinearMap.comp_apply]
    have hAevent : (fun z : Vec3 => A z) =ᶠ[𝓝 x]
        (fun z : Vec3 => -CKN.spatialDeriv newtonianKernel i (z - y)) := by
      filter_upwards [hne_event] with z hz
      dsimp [A]
      rw [spatialDeriv_newtonianKernel_shift_eq_neg hz]
    have hneg := houter'.neg
    exact hneg.congr_of_eventuallyEq hAevent
  have hB : HasFDerivAt B
      (fderiv ℝ newtonianKernel (x - y)) x := by
    have hinner : HasFDerivAt (fun z : Vec3 => z - y)
        (1 : Vec3 →L[ℝ] Vec3) x := by
      exact hasFDerivAt_sub_const y
    have houter := (newtonianKernel_hasFDerivAt hxy).comp x hinner
    convert houter using 1
    · rfl
    · ext v
      simp [ContinuousLinearMap.comp_apply]
  have hEq : (fun z : Vec3 =>
        CKN.spatialDeriv (kernelCutoffDerivative z x₀ hρ i) i y) =ᶠ[𝓝 x]
        (fun z : Vec3 => A z * E) + (fun z : Vec3 => B z * F) := by
    filter_upwards [hne_event] with z hz
    rw [spatialDeriv_kernelCutoffDerivative_of_ne hρ hz]
    simp [A, B, E, F]
  have hprod := (hA.mul_const E).add (hB.mul_const F)
  have hK := hprod.congr_of_eventuallyEq hEq
  have hfd := hK.fderiv
  have hcoord := congrArg
    (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j)) hfd
  change |(fderiv ℝ (fun z : Vec3 =>
      CKN.spatialDeriv (kernelCutoffDerivative z x₀ hρ i) i y) x)
      (basisVec j)| ≤ _
  rw [hcoord]
  have hdist3 : (‖x - y‖ ^ 3)⁻¹ ≤ ((ρ / 20) ^ 3)⁻¹ := by gcongr
  have hdist2 : (‖x - y‖ ^ 2)⁻¹ ≤ ((ρ / 20) ^ 2)⁻¹ := by gcongr
  have hess := newtonianKernel_spatialDeriv_second_size_bound hxy i j
  have hderiv := newtonianKernel_spatialDeriv_size_bound hxy j
  have heta := eta_spatialDeriv_bound_global x₀ hρ y i
  have hsecond := eta_spatialSecond_bound_global x₀ hρ y i i
  have hess' : ‖(fderiv ℝ (CKN.spatialDeriv newtonianKernel i)
      (x - y)) (basisVec j)‖ ≤
      4 * (4 * Real.pi)⁻¹ * ((ρ / 20) ^ 3)⁻¹ := by
    exact hess.trans (mul_le_mul_of_nonneg_left hdist3 (by positivity))
  have hderiv' : ‖(fderiv ℝ newtonianKernel (x - y))
      (basisVec j)‖ ≤
      (4 * Real.pi)⁻¹ * ((ρ / 20) ^ 2)⁻¹ := by
    exact hderiv.trans (mul_le_mul_of_nonneg_left hdist2 (by positivity))
  have hess'' : |(fderiv ℝ (CKN.spatialDeriv newtonianKernel i)
      (x - y)) (basisVec j)| ≤
      4 * (4 * Real.pi)⁻¹ * ((ρ / 20) ^ 3)⁻¹ := by
    simpa only [Real.norm_eq_abs] using hess'
  have hderiv'' : |(fderiv ℝ newtonianKernel (x - y))
      (basisVec j)| ≤
      (4 * Real.pi)⁻¹ * ((ρ / 20) ^ 2)⁻¹ := by
    simpa only [Real.norm_eq_abs] using hderiv'
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  calc
    _ ≤ |(fderiv ℝ (CKN.spatialDeriv newtonianKernel i)
          (x - y)) (basisVec j)| * |E| +
        |(fderiv ℝ newtonianKernel (x - y)) (basisVec j)| * |F| := by
          calc
            _ ≤ |E * (-(fderiv ℝ (CKN.spatialDeriv newtonianKernel i)
                (x - y)) (basisVec j))| +
              |F * (fderiv ℝ newtonianKernel (x - y)) (basisVec j)| :=
                abs_add_le _ _
            _ = _ := by
              rw [abs_mul, abs_mul, abs_neg]
              ring
    _ ≤ weakHarmonicInteriorXGradientConstant * (ρ ^ 4)⁻¹ := by
          rw [show |E| = |CKN.spatialDeriv (eta x₀ hρ) i y| by rfl,
            show |F| = |CKN.spatialDeriv (CKN.spatialDeriv
              (eta x₀ hρ) i) i y| by rfl]
          calc
            _ ≤ (4 * (4 * Real.pi)⁻¹ * ((ρ / 20) ^ 3)⁻¹) *
                  (cutoffGradientConstant / ρ) +
                ((4 * Real.pi)⁻¹ * ((ρ / 20) ^ 2)⁻¹) *
                  (cutoffSecondDerivativeConstant / ρ ^ 2) := by
                    exact add_le_add (mul_le_mul hess'' heta
                      (by positivity) (by positivity))
                      (mul_le_mul hderiv'' hsecond (by positivity) (by positivity))
            _ = _ := by
              dsimp [weakHarmonicInteriorXGradientConstant]
              field_simp [hρ.ne']
              ring

lemma weak_source_x_derivative_bound
    {x x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    (hy : y ∈ cutoffAnnulus x₀ ρ) (j : Fin 3) :
    |CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (z - y)) j x *
        CKN.spatialLaplacian (eta x₀ hρ) y| ≤
      weakHarmonicInteriorSourceXGradientConstant * (ρ ^ 4)⁻¹ := by
  have hd := weak_annulus_distance hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 20)) (by simpa using hd)
  have hdist2 : (‖x - y‖ ^ 2)⁻¹ ≤ ((ρ / 20) ^ 2)⁻¹ := by gcongr
  have hderiv := newtonianKernel_spatialDeriv_size_bound hxy j
  have hderiv' : |CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (z - y)) j x| ≤
      (4 * Real.pi)⁻¹ * ((ρ / 20) ^ 2)⁻¹ := by
    have hshift : |CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (z - y)) j x| =
        |CKN.spatialDeriv newtonianKernel j (x - y)| := by
      have hfd := (newtonianKernel_hasFDerivAt hxy).comp x
        (hasFDerivAt_sub_const y)
      have hcoord := congrArg
        (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j)) hfd.fderiv
      change (fderiv ℝ (fun z : Vec3 => newtonianKernel (z - y)) x)
          (basisVec j) =
        (fderiv ℝ newtonianKernel (x - y)) (basisVec j) at hcoord
      have hcoord' :
          (fderiv ℝ (fun z : Vec3 => newtonianKernel (z - y)) x)
              (basisVec j) =
            (fderiv ℝ newtonianKernel (x - y)) (basisVec j) := by
        exact hcoord
      exact congrArg abs hcoord'
    rw [hshift]
    exact hderiv.trans (mul_le_mul_of_nonneg_left hdist2 (by positivity))
  have hs := eta_laplacian_bound_global x₀ hρ y
  rw [abs_mul]
  calc
    |CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (z - y)) j x| *
        |CKN.spatialLaplacian (eta x₀ hρ) y| ≤
      ((4 * Real.pi)⁻¹ * ((ρ / 20) ^ 2)⁻¹) *
        (3 * cutoffSecondDerivativeConstant / ρ ^ 2) := by
          exact mul_le_mul hderiv' hs (by positivity) (by positivity)
    _ = weakHarmonicInteriorSourceXGradientConstant * (ρ ^ 4)⁻¹ := by
      dsimp [weakHarmonicInteriorSourceXGradientConstant]
      field_simp [hρ.ne']
      ring

lemma weak_source_kernel_zero_off_annulus
    {x x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hy : y ∉ cutoffAnnulus x₀ ρ) :
    newtonianKernel (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y = 0 := by
  rw [eta_laplacian_zero_off_annulus hρ hy, mul_zero]

lemma weak_cutoff_kernel_zero_off_annulus
    {x x₀ y : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2))
    (hy : y ∉ cutoffAnnulus x₀ ρ) (i : Fin 3) :
    CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y = 0 := by
  by_cases hxy : x - y = 0
  · have hxinner : x ∈ euclideanBall x₀ (13 * ρ / 20) := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
      have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
      have hxnorm : vecEuclideanNorm (x - x₀) < ρ / 2 := by
        simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
          using hx'
      exact hxnorm.trans (by
        calc
          ρ / 2 = 10 * ρ / 20 := by ring
          _ < 13 * ρ / 20 := by gcongr; norm_num)
    have hz := spatialDeriv_kernelCutoffDerivative_at_x hρ hxinner i i
    simpa [sub_eq_zero.mp hxy] using hz
  · rw [spatialDeriv_kernelCutoffDerivative_of_ne hρ hxy]
    rw [eta_spatialDeriv_zero_off_annulus hρ hy i,
      eta_spatialSecond_zero_off_annulus hρ hy i i]
    simp

lemma weak_annulus_isFinite
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    volume (cutoffAnnulus x₀ ρ) ≠ ∞ := by
  apply ne_of_lt
  have hclosed : cutoffAnnulus x₀ ρ ⊆ euclideanClosedBall x₀ ρ := by
    intro y hy
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hρ.le).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).1
      (weak_annulus_subset_outer hρ hy)).le
  exact lt_of_le_of_lt (measure_mono hclosed)
    ((isCompact_euclideanClosedBall x₀ hρ.le).measure_lt_top)

lemma weak_lp_kernel_bound
    {x₀ : Vec3} {ρ C : ℝ} (hρ : 0 < ρ) {k : Vec3 → ℝ}
    (hAmeas : MeasurableSet (cutoffAnnulus x₀ ρ))
    (hkcont : ContinuousOn k (cutoffAnnulus x₀ ρ))
    (hC : 0 ≤ C) (hkbound : ∀ y ∈ cutoffAnnulus x₀ ρ, |k y| ≤ C * (ρ ^ 3)⁻¹) :
    lpNorm k (ENNReal.ofReal (3 : ℝ))
        (volume.restrict (cutoffAnnulus x₀ ρ)) ≤
      C * (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ := by
  let _ : IsFiniteMeasure (volume.restrict (cutoffAnnulus x₀ ρ)) :=
    isFiniteMeasure_restrict.mpr (weak_annulus_isFinite hρ)
  have hk := memLp_of_continuousOn_bound hAmeas hkcont
    (C * (ρ ^ 3)⁻¹) hkbound (ENNReal.ofReal (3 : ℝ))
  have hlp := lpNorm_bound_on hAmeas
    (by norm_num : ENNReal.ofReal (3 : ℝ) ≠ 0)
    (by norm_num : ENNReal.ofReal (3 : ℝ) ≠ ∞)
    (C * (ρ ^ 3)⁻¹) (mul_nonneg hC (by positivity)) (fun y hy => by
      simpa only [Real.norm_eq_abs] using hkbound y hy)
  have hv := volume_root_bound (s := cutoffAnnulus x₀ ρ) (x₀ := x₀)
    hρ (weak_annulus_subset_outer hρ)
  have hp : (ENNReal.ofReal (3 : ℝ)).toReal⁻¹ = 1 / (3 : ℝ) := by
    norm_num
  rw [hp] at hlp
  have hlp' : lpNorm k (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (cutoffAnnulus x₀ ρ)) ≤
      C * (ρ ^ 3)⁻¹ * (volume (cutoffAnnulus x₀ ρ)).toReal ^
        (1 / (3 : ℝ)) := by
    convert hlp using 1
  calc
    lpNorm k (ENNReal.ofReal (3 : ℝ))
        (volume.restrict (cutoffAnnulus x₀ ρ)) ≤
        C * (ρ ^ 3)⁻¹ * (volume (cutoffAnnulus x₀ ρ)).toReal ^
          (1 / (3 : ℝ)) := hlp'
    _ ≤ C * (ρ ^ 3)⁻¹ *
        (ρ * (Real.pi * 4 / 3) ^ (1 / (3 : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hv
            (mul_nonneg hC (by positivity))
    _ = C * (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 2)⁻¹ := by
      field_simp [hρ.ne']

lemma weak_source_kernel_continuousOn
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2)) :
    ContinuousOn (fun y : Vec3 => newtonianKernel (x - y) *
      CKN.spatialLaplacian (eta x₀ hρ) y) (cutoffAnnulus x₀ ρ) := by
  intro y hy
  have hd := weak_annulus_distance hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 20)) (by simpa using hd)
  have hN : ContinuousAt (fun z : Vec3 => newtonianKernel (x - z)) y :=
    (newtonianKernel_continuousAt hxy).comp
      (continuousAt_const.sub continuousAt_id)
  have hD : Continuous (CKN.spatialLaplacian (eta x₀ hρ)) := by
    simpa only [eta] using
      (CKN.contDiff_spatialLaplacian_smooth
        (mollifiedBallCutoff_smooth x₀ hρ)).continuous
  exact hN.continuousWithinAt.mul hD.continuousAt.continuousWithinAt

lemma weak_cutoff_kernel_continuousOn
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2)) (i : Fin 3) :
    ContinuousOn (fun y : Vec3 =>
      CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y)
      (cutoffAnnulus x₀ ρ) := by
  have hxinner : x ∈ euclideanBall x₀ (13 * ρ / 20) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
    exact hx'.trans (by nlinarith only [hρ])
  have hcont : Continuous (fun y : Vec3 =>
      CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y) := by
    exact ((kernelCutoffDerivative_contDiff_one x x₀ hρ hxinner i).continuous_fderiv
      (by norm_num)).clm_apply continuous_const
  exact hcont.continuousOn

private lemma weak_source_x_kernel_continuousOn
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2)) (j : Fin 3) :
    ContinuousOn (fun y : Vec3 =>
      CKN.spatialDeriv newtonianKernel j (x - y) *
        CKN.spatialLaplacian (eta x₀ hρ) y) (cutoffAnnulus x₀ ρ) := by
  intro y hy
  have hd := weak_annulus_distance hρ hx hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 20)) (by simpa using hd)
  have hN : ContinuousAt (fun z : Vec3 =>
      CKN.spatialDeriv newtonianKernel j (x - z)) y :=
    (newtonianKernel_spatialDeriv_continuousAt hxy j).comp
      (continuousAt_const.sub continuousAt_id)
  have hD : Continuous (CKN.spatialLaplacian (eta x₀ hρ)) := by
    simpa only [eta] using
      (CKN.contDiff_spatialLaplacian_smooth
        (mollifiedBallCutoff_smooth x₀ hρ)).continuous
  exact hN.continuousWithinAt.mul hD.continuousAt.continuousWithinAt

end CKN.Foundation.Heat
