/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorRegularity
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Interior Smooth

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology Convolution
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

private lemma euclidean_ball_isOpen_smooth {x₀ : Vec3} {ρ : ℝ} (_ : 0 < ρ) :
    IsOpen (euclideanBall x₀ ρ) := by
  change IsOpen {y : Vec3 | euclideanSqDist y x₀ < ρ ^ 2}
  exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const

private lemma fderiv_norm_le_three_classicalGradient_smooth
    {f : Vec3 → ℝ} (x : Vec3) :
    ‖fderiv ℝ f x‖ ≤ 3 * vec3EuclideanNorm (classicalGradient f x) := by
  have hbase : ‖fderiv ℝ f x‖ ≤ 3 * ‖classicalGradient f x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    calc
      ‖(fderiv ℝ f x) z‖ =
          ‖∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i)‖ := by
        calc
          ‖(fderiv ℝ f x) z‖ =
              ‖(fderiv ℝ f x) (∑ i : Fin 3, z i • basisVec i)‖ := by
                rw [sum_smul_basisVec]
          _ = ‖∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i)‖ := by
            rw [_root_.map_sum]
            simp only [map_smul]
      _ ≤ ∑ i : Fin 3, ‖z i • (fderiv ℝ f x) (basisVec i)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ‖z‖ * ‖classicalGradient f x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Real.norm_eq_abs]
        have hz : |z i| ≤ ‖z‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
        have hg : |(fderiv ℝ f x) (basisVec i)| ≤
            ‖classicalGradient f x‖ := by
          simpa only [classicalGradient_apply, Real.norm_eq_abs] using
            norm_le_pi_norm (classicalGradient f x) i
        exact mul_le_mul hz hg (abs_nonneg _) (norm_nonneg _)
      _ = 3 * ‖classicalGradient f x‖ * ‖z‖ := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (CKN.space_norm_le_euclideanNorm (classicalGradient f x)) (by positivity))

private lemma euclidean_quarter_ball_subset_smooth
    {x x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (ρ / 2)) :
    euclideanBall x (ρ / 4) ⊆ euclideanBall x₀ (3 * ρ / 4) := by
  intro y hy
  have hy' : vec3EuclideanNorm (y - x) < ρ / 4 := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy
  have hx' : vec3EuclideanNorm (x - x₀) < ρ / 2 := by
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
  have htri : vec3EuclideanNorm (y - x₀) ≤
      vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - x₀) := by
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
  have hthree := CKN.euclideanNorm_le_three_mul_space_norm (y - x)
  have hthree' : vec3EuclideanNorm (y - x) ≤ 3 * ‖y - x‖ := by
    simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hthree
  have hfinal : vec3EuclideanNorm (y - x₀) < 3 * ρ / 4 := by
    nlinarith only [htri, hthree', hy', hx', hρ]
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hfinal

private lemma weakly_harmonic_interior_smooth_hdiffHarm_1 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ},
      let U : Set Vec3 := euclideanBall x₀ ρ;
      let g : Vec3 → ℝ := U.indicator h;
      let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
        (∀ (n : ℕ), ContDiff ℝ (⊤ : ℕ∞) (fn n)) →
          (∀ (n : ℕ),
              ∀ y ∈ euclideanBall x₀ ((3 : ℝ) * ρ / (4 : ℝ)), spatialLaplacian (fn n) y = (0 : ℝ)) →
            ∀ (m n : ℕ),
              ∀ y ∈ euclideanBall x₀ ((3 : ℝ) * ρ / (4 : ℝ)),
                spatialLaplacian (fn m - fn n) y = (0 : ℝ)
    := by
  intro h x₀ ρ U g ε hεpos fn hfnSmooth hfnHarm m n y hy
  rw [CKN.spatialLaplacian]
  have hfirst : ∀ i : Fin 3, CKN.spatialDeriv (fn m - fn n) i =
      CKN.spatialDeriv (fn m) i - CKN.spatialDeriv (fn n) i := by
    intro i
    funext z
    change (fderiv ℝ (fn m - fn n) z) (basisVec i) = _
    rw [fderiv_sub ((hfnSmooth m).differentiable (by simp) z)
      ((hfnSmooth n).differentiable (by simp) z)]
    simp [spatialDeriv]
  have hsecond : ∀ i : Fin 3,
      CKN.spatialDeriv (CKN.spatialDeriv (fn m - fn n) i) i y =
        CKN.spatialDeriv (CKN.spatialDeriv (fn m) i) i y -
          CKN.spatialDeriv (CKN.spatialDeriv (fn n) i) i y := by
    intro i
    rw [hfirst i]
    change (fderiv ℝ (CKN.spatialDeriv (fn m) i -
      CKN.spatialDeriv (fn n) i) y) (basisVec i) = _
    rw [fderiv_sub
      ((contDiff_spatialDeriv_smooth (hfnSmooth m) i).differentiable (by simp) y)
      ((contDiff_spatialDeriv_smooth (hfnSmooth n) i).differentiable (by simp) y)]
    simp [spatialDeriv]
  simp_rw [hsecond]
  rw [Finset.sum_sub_distrib]
  change CKN.spatialLaplacian (fn m) y - CKN.spatialLaplacian (fn n) y = 0
  rw [hfnHarm m y hy, hfnHarm n y hy]
  simp

private lemma weakly_harmonic_interior_smooth_hdiff_toReal_2 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ},
      let U : Set Vec3 := euclideanBall x₀ ρ;
      let g : Vec3 → ℝ := U.indicator h;
      MemLp (m0 := MeasureSpace.toMeasurableSpace) g (ENNReal.ofReal (3 / 2 : ℝ)) volume →
        let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
        ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
          let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
          (∀ (n : ℕ),
              MemLp (m0 := MeasureSpace.toMeasurableSpace) (fn n) (ENNReal.ofReal (3 / 2 : ℝ))
                volume) →
            ∀ (m n : ℕ),
              (@eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace (fn m - fn n)
                    (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal ≤
                (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace (fun (y : Vec3) => fn m y - g y)
                      (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal +
                  (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace (fun (y : Vec3) => fn n y - g y)
                      (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal
    := by
  intro h x₀ ρ U g hgmem ε hεpos fn hfnmem m n
  have he := eLpNorm_sub_le (p := ENNReal.ofReal (3 / 2 : ℝ))
    (μ := volume) (f := fun y => fn m y - g y)
    (g := fun y => fn n y - g y) (by norm_num)
  have hfun : fn m - fn n =
      (fun y => fn m y - g y) - (fun y => fn n y - g y) := by
    funext y
    dsimp
    ring
  have he' : eLpNorm (fn m - fn n) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      eLpNorm (fun y => fn m y - g y)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume +
      eLpNorm (fun y => fn n y - g y)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    rw [hfun]
    exact he
  have hm_top : eLpNorm (fun y => fn m y - g y)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume ≠ ∞ := by
    change eLpNorm (fn m - g) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≠ ∞
    exact (hfnmem m).sub hgmem |>.eLpNorm_ne_top
  have hn_top : eLpNorm (fun y => fn n y - g y)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume ≠ ∞ := by
    change eLpNorm (fn n - g) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≠ ∞
    exact (hfnmem n).sub hgmem |>.eLpNorm_ne_top
  calc
    _ ≤ (eLpNorm (fun y => fn m y - g y)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume +
        eLpNorm (fun y => fn n y - g y)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hm_top, hn_top⟩) he'
    _ = _ := ENNReal.toReal_add hm_top hn_top

private lemma weakly_harmonic_interior_smooth_hgrad_bound_3 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ},
      (0 : ℝ) < ρ →
        let U : Set Vec3 := euclideanBall x₀ ρ;
        let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
        let g : Vec3 → ℝ := U.indicator h;
        let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
        ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
          let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
          (∀ (n : ℕ), ContDiff ℝ (⊤ : ℕ∞) (fn n)) →
            (∀ (m n : ℕ), ContDiff ℝ (⊤ : ℕ∞) (fn m - fn n)) →
              (∀ (m n : ℕ),
                  ∀ y ∈ euclideanBall x₀ ((3 : ℝ) * ρ / (4 : ℝ)),
                    spatialLaplacian (fn m - fn n) y = (0 : ℝ)) →
                (∀ (m n : ℕ),
                    MemLp (m0 := MeasureSpace.toMeasurableSpace) (fn m - fn n)
                      (ENNReal.ofReal (3 / 2 : ℝ)) volume) →
                  (∀ (m n : ℕ),
                      MemLp (m0 := MeasureSpace.toMeasurableSpace) (fn m - fn n)
                        (ENNReal.ofReal (3 / 2 : ℝ)) (Measure.restrict volume U)) →
                    (∀ (m n : ℕ),
                        (@eLpNorm _ _ _ _ MeasureSpace.toMeasurableSpace (fn m - fn n)
                              (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal ≤
                          (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                                (fun (y : Vec3) => fn m y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                                volume).toReal +
                            (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                                (fun (y : Vec3) => fn n y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                                volume).toReal) →
                      let grad : ℕ → Vec3 → Vec3 := fun (n : ℕ) => classicalGradient (fn n);
                      ∀ (m n : ℕ),
                        ∀ x ∈ I,
                          dist (grad m x) (grad n x) ≤
                            (192 : ℝ) * harmonicInteriorGradientSupConstant * (ρ ^ (3 : ℕ))⁻¹ *
                              ((@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                                    (fun (y : Vec3) => fn m y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                                    volume).toReal +
                                (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                                    (fun (y : Vec3) => fn n y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                                    volume).toReal)
    := by
  intro h x₀ ρ hρ U I g ε hεpos fn hfnSmooth hdiffSmooth hdiffHarm hdiffGlobal hdiffU hdiff_toReal
    grad m n x hx
  have hlocal_sub : euclideanBall x (ρ / 4) ⊆ U := by
    intro y hy
    have hy3 := euclidean_quarter_ball_subset_smooth hρ hx hy
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
    have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy3
    exact hy'.trans (by nlinarith only [hρ])
  have hlocal_mem := (hdiffU m n).mono_measure
    (Measure.restrict_mono_set volume hlocal_sub)
  have hlocal_harm : ∀ y ∈ euclideanBall x (ρ / 4),
      CKN.spatialLaplacian (fn m - fn n) y = 0 := by
    intro y hy
    exact hdiffHarm m n y (euclidean_quarter_ball_subset_smooth hρ hx hy)
  have hxlocal : x ∈ euclideanBall x ((ρ / 4) / 2) := by
    have hlocalρ : 0 < (ρ / 4) / 2 := by positivity
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hlocalρ).2
    simp [vecEuclideanNorm, vecNormSq, vecDot]
    nlinarith only [hρ]
  have hLp_local := smooth_harmonic_interior_gradient_norm_bound
    (x₀ := x) (ρ := ρ / 4) (hdiffSmooth m n) (by positivity)
    hlocal_harm hlocal_mem x hxlocal
  have hLpU' : lpNorm (fn m - fn n)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) ≤
      lpNorm (fn m - fn n)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
    exact ENNReal.toReal_mono (hdiffGlobal m n).eLpNorm_lt_top.ne
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hgrad_eq : classicalGradient (fn m - fn n) x = grad m x - grad n x := by
    ext i
    change (fderiv ℝ (fn m - fn n) x) (basisVec i) = _
    rw [fderiv_sub ((hfnSmooth m).differentiable (by simp) x)
      ((hfnSmooth n).differentiable (by simp) x)]
    rfl
  have hrinv : 0 ≤ (ρ ^ 3)⁻¹ := inv_nonneg.mpr (by positivity)
  have hcoef : 0 ≤ 192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ := by
    exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (192 : ℝ))
      harmonicInteriorGradientSupConstant_nonneg) hrinv
  have hspace := CKN.space_norm_le_euclideanNorm (classicalGradient (fn m - fn n) x)
  calc
    dist (grad m x) (grad n x) = ‖grad m x - grad n x‖ := by rw [dist_eq_norm]
    _ = ‖classicalGradient (fn m - fn n) x‖ := by rw [hgrad_eq]
    _ ≤ vec3EuclideanNorm (classicalGradient (fn m - fn n) x) := hspace
    _ ≤ 3 * harmonicInteriorGradientSupConstant * ((ρ / 4) ^ 3)⁻¹ *
        lpNorm (fn m - fn n)
          (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x (ρ / 4))) := hLp_local
    _ = 192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
        lpNorm (fn m - fn n)
          (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x (ρ / 4))) := by
      have hscale : ((ρ / 4) ^ 3)⁻¹ = 64 * (ρ ^ 3)⁻¹ := by
        rw [show (ρ / 4) ^ 3 = ρ ^ 3 / 4 ^ 3 by ring, inv_div]
        norm_num [div_eq_mul_inv]
      rw [hscale]
      ring
    _ ≤ 192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
        lpNorm (fn m - fn n)
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by
      exact mul_le_mul_of_nonneg_left
        (lpNorm_restrict_mono hlocal_sub (hdiffU m n)) hcoef
    _ ≤ 192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
        (eLpNorm (fn m - fn n)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal := by
      exact mul_le_mul_of_nonneg_left hLpU' hcoef
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (hdiff_toReal m n) hcoef

private lemma weakly_harmonic_interior_smooth_hgrad_uc_4 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ},
      (0 : ℝ) < ρ →
        let U : Set Vec3 := euclideanBall x₀ ρ;
        let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
        let g : Vec3 → ℝ := U.indicator h;
        let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
        ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
          let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
          let grad : ℕ → Vec3 → Vec3 := fun (n : ℕ) => classicalGradient (fn n);
          (∀ (m n : ℕ),
              ∀ x ∈ I,
                dist (grad m x) (grad n x) ≤
                  (192 : ℝ) * harmonicInteriorGradientSupConstant * (ρ ^ (3 : ℕ))⁻¹ *
                    ((@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                          (fun (y : Vec3) => fn m y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                          volume).toReal +
                      (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                          (fun (y : Vec3) => fn n y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                          volume).toReal)) →
            Tendsto
                (fun (n : ℕ) =>
                  (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace (fun (y : Vec3) => fn n y - g y)
                      (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal)
                atTop (𝓝 (0 : ℝ)) →
              UniformCauchySeqOn grad atTop I
    := by
  intro h x₀ ρ hρ U I g ε hεpos fn grad hgrad_bound hconv_real
  rw [Metric.uniformCauchySeqOn_iff]
  intro δ hδ
  have hK : 0 ≤ 192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ := by
    exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (192 : ℝ))
      harmonicInteriorGradientSupConstant_nonneg)
      (inv_nonneg.mpr (by positivity))
  by_cases hK0 : 192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ = 0
  · refine ⟨0, fun m hm n hn x hx => ?_⟩
    have hb := hgrad_bound m n x hx
    rw [hK0, zero_mul] at hb
    exact hb.trans_lt hδ
  · have hKpos : 0 < 192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ :=
      lt_of_le_of_ne hK (Ne.symm hK0)
    have hN' := (tendsto_order.1 hconv_real).2
      (δ / (2 * (192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹)))
      (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hN'
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    have hm' := hN m hm
    have hn' := hN n hn
    have hb := hgrad_bound m n x hx
    have hsmall := mul_lt_mul_of_pos_left (add_lt_add hm' hn') hKpos
    have hcancel :
        192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
            (δ / (2 * (192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹)) +
              δ / (2 * (192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹))) = δ := by
      have hGpos : 0 < harmonicInteriorGradientSupConstant := by
        by_contra hG
        have hG' : harmonicInteriorGradientSupConstant ≤ 0 := le_of_not_gt hG
        have hG'' : harmonicInteriorGradientSupConstant = 0 :=
          le_antisymm hG' harmonicInteriorGradientSupConstant_nonneg
        rw [hG''] at hKpos
        norm_num at hKpos
      have hGne : harmonicInteriorGradientSupConstant ≠ 0 := ne_of_gt hGpos
      field_simp [hGne, ne_of_gt hρ]
      ring
    exact hb.trans_lt (hsmall.trans_eq hcancel)

private lemma weakly_harmonic_interior_smooth_hderiv_diff_bound_5 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ},
      let U : Set Vec3 := euclideanBall x₀ ρ;
      let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
      let g : Vec3 → ℝ := U.indicator h;
      let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
        (∀ (n : ℕ), ContDiff ℝ (⊤ : ℕ∞) (fn n)) →
          let grad : ℕ → Vec3 → Vec3 := fun (n : ℕ) => classicalGradient (fn n);
          (∀ (m n : ℕ),
              ∀ x ∈ I,
                dist (grad m x) (grad n x) ≤
                  (192 : ℝ) * harmonicInteriorGradientSupConstant * (ρ ^ (3 : ℕ))⁻¹ *
                    ((@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                          (fun (y : Vec3) => fn m y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                          volume).toReal +
                      (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                          (fun (y : Vec3) => fn n y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                          volume).toReal)) →
            let d : ℕ → Vec3 → Vec3 →L[ℝ] ℝ := fun (n : ℕ) (x : Vec3) => fderiv ℝ (fn n) x;
            ∀ (m n : ℕ),
              ∀ x ∈ I,
                ‖d m x - d n x‖ ≤
                  (9 : ℝ) * ((192 : ℝ) * harmonicInteriorGradientSupConstant * (ρ ^ (3 : ℕ))⁻¹) *
                    ((@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                          (fun (y : Vec3) => fn m y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                          volume).toReal +
                      (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                          (fun (y : Vec3) => fn n y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                          volume).toReal)
    := by
  intro h x₀ ρ U I g ε hεpos fn hfnSmooth grad hgrad_bound d m n x hx
  have hgrad_eq : classicalGradient (fn m - fn n) x = grad m x - grad n x := by
    ext i
    change (fderiv ℝ (fn m - fn n) x) (basisVec i) = _
    rw [fderiv_sub ((hfnSmooth m).differentiable (by simp) x)
      ((hfnSmooth n).differentiable (by simp) x)]
    rfl
  have hd_eq : d m x - d n x = fderiv ℝ (fn m - fn n) x := by
    dsimp [d]
    rw [fderiv_sub ((hfnSmooth m).differentiable (by simp) x)
      ((hfnSmooth n).differentiable (by simp) x)]
  have heuc := CKN.euclideanNorm_le_three_mul_space_norm
    (classicalGradient (fn m - fn n) x)
  have heuc' : vec3EuclideanNorm (classicalGradient (fn m - fn n) x) ≤
      3 * ‖classicalGradient (fn m - fn n) x‖ := by
    simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using heuc
  calc
    ‖d m x - d n x‖ = ‖fderiv ℝ (fn m - fn n) x‖ := by rw [hd_eq]
    _ ≤ 3 * vec3EuclideanNorm (classicalGradient (fn m - fn n) x) :=
      fderiv_norm_le_three_classicalGradient_smooth x
    _ ≤ 3 * (3 * ‖classicalGradient (fn m - fn n) x‖) :=
      mul_le_mul_of_nonneg_left heuc' (by norm_num)
    _ = 9 * dist (grad m x) (grad n x) := by
      rw [hgrad_eq, dist_eq_norm]
      ring
    _ ≤ 9 * (192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹) *
        ((eLpNorm (fun y => fn m y - g y)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal +
        (eLpNorm (fun y => fn n y - g y)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal) := by
      calc
        9 * dist (grad m x) (grad n x) ≤
            9 * (192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹) *
              ((eLpNorm (fun y => fn m y - g y)
                (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal +
              (eLpNorm (fun y => fn n y - g y)
                (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal) := by
          exact (mul_le_mul_of_nonneg_left (hgrad_bound m n x hx)
            (by norm_num : (0 : ℝ) ≤ 9)).trans_eq (by ring)
    _ = _ := by ring

private lemma weakly_harmonic_interior_smooth_hd_uc_6 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ},
      (0 : ℝ) < ρ →
        let U : Set Vec3 := euclideanBall x₀ ρ;
        let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
        let g : Vec3 → ℝ := U.indicator h;
        let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
        ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
          let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
          Tendsto
              (fun (n : ℕ) =>
                (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace (fun (y : Vec3) => fn n y - g y)
                    (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal)
              atTop (𝓝 (0 : ℝ)) →
            let d : ℕ → Vec3 → Vec3 →L[ℝ] ℝ := fun (n : ℕ) (x : Vec3) => fderiv ℝ (fn n) x;
            (∀ (m n : ℕ),
                ∀ x ∈ I,
                  ‖d m x - d n x‖ ≤
                    (9 : ℝ) * ((192 : ℝ) * harmonicInteriorGradientSupConstant * (ρ ^ (3 : ℕ))⁻¹) *
                      ((@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                            (fun (y : Vec3) => fn m y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                            volume).toReal +
                        (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                            (fun (y : Vec3) => fn n y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                            volume).toReal)) →
              UniformCauchySeqOn d atTop I
    := by
  intro h x₀ ρ hρ U I g ε hεpos fn hconv_real d hderiv_diff_bound
  rw [Metric.uniformCauchySeqOn_iff]
  intro δ hδ
  let L : ℝ := 9 * (192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹)
  have hK : 0 ≤ 192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ := by
    exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (192 : ℝ))
      harmonicInteriorGradientSupConstant_nonneg)
      (inv_nonneg.mpr (by positivity))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  by_cases hL0 : L = 0
  · refine ⟨0, fun m hm n hn x hx => ?_⟩
    have hb := hderiv_diff_bound m n x hx
    rw [show 9 * (192 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹) = L
      by rfl, hL0, zero_mul] at hb
    rw [dist_eq_norm]
    exact hb.trans_lt hδ
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    have hN' := (tendsto_order.1 hconv_real).2
      (δ / (2 * L)) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hN'
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    have hm' := hN m hm
    have hn' := hN n hn
    have hb := hderiv_diff_bound m n x hx
    have hb' : dist (d m x) (d n x) ≤ L *
        ((eLpNorm (fun y => fn m y - g y)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal +
        (eLpNorm (fun y => fn n y - g y)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal) := by
      rw [dist_eq_norm]
      simpa [L] using hb
    have hsmall := mul_lt_mul_of_pos_left (add_lt_add hm' hn') hLpos
    have hcancel : L * (δ / (2 * L) + δ / (2 * L)) = δ := by
      field_simp [ne_of_gt hLpos]
      ring
    exact hb'.trans_lt (hsmall.trans_eq hcancel)

private lemma weakly_harmonic_interior_smooth_hrepn_7 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
      let U : Set Vec3 := euclideanBall x₀ ρ;
      let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
      let g : Vec3 → ℝ := U.indicator h;
      MemLp (m0 := MeasureSpace.toMeasurableSpace) g (ENNReal.ofReal (3 / 2 : ℝ)) volume →
        let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
        ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
          let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
          (∀ (n : ℕ),
              ∀ y ∈ euclideanBall x₀ ((3 : ℝ) * ρ / (4 : ℝ)), spatialLaplacian (fn n) y = (0 : ℝ)) →
            ∀ (n : ℕ), ∀ x ∈ I, fn n x = weakHarmonicInteriorRepresentative (fn n) x₀ hρ x
    := by
  intro h x₀ ρ hρ U I g hgmem ε hεpos fn hfnHarm n x hx
  have hxinner : x ∈ euclideanBall x₀ (13 * ρ / 20) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
    have hx'' : vec3EuclideanNorm (x - x₀) < ρ / 2 := by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hx'
    have hx''' : vec3EuclideanNorm (x - x₀) < 13 * ρ / 20 := by
      exact hx''.trans (by nlinarith only [hρ])
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hx'''
  have hrep := smooth_harmonic_annular_representation_on_outer
    (CKN.mollify_contDiff (hεpos n) (hgmem.locallyIntegrable (by norm_num)))
    hρ (hfnHarm n) hxinner
  simpa only [fn, weakHarmonicInteriorRepresentative] using hrep

private lemma weakly_harmonic_interior_smooth_hbound_8 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
      let U : Set Vec3 := euclideanBall x₀ ρ;
      let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
      let g : Vec3 → ℝ := U.indicator h;
      let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
        (∀ (n : ℕ),
            MemLp (m0 := MeasureSpace.toMeasurableSpace) (fn n) (ENNReal.ofReal (3 / 2 : ℝ))
              (Measure.restrict volume U)) →
          MemLp (m0 := MeasureSpace.toMeasurableSpace) g (ENNReal.ofReal (3 / 2 : ℝ))
              (Measure.restrict volume U) →
            (∀ (m n : ℕ),
                MemLp (m0 := MeasureSpace.toMeasurableSpace) (fn m - fn n)
                  (ENNReal.ofReal (3 / 2 : ℝ)) (Measure.restrict volume U)) →
              (∀ (n : ℕ),
                  MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace)
                    (fun (y : Vec3) => fn n y - g y) (ENNReal.ofReal (3 / 2 : ℝ)) volume) →
                (∀ (n : ℕ), ∀ x ∈ I, fn n x = weakHarmonicInteriorRepresentative (fn n) x₀ hρ x) →
                  ∀ (n : ℕ),
                    ∀ x ∈ I,
                      dist (fn n x) (weakHarmonicInteriorRepresentative g x₀ hρ x) ≤
                        weakHarmonicInteriorSupConstant * (ρ ^ (2 : ℕ))⁻¹ *
                          (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                              (fun (y : Vec3) => fn n y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                              volume).toReal
    := by
  intro h x₀ ρ hρ U I g ε hεpos fn hfnU hgun hdiffU hdiffmem hrepn n x hx
  have hdiffU := (hfnU n).sub hgun
  have hrepdiff := weak_rep_sub_eq hρ hx (hfnU n) hgun
  have hdiffU_lp : lpNorm (fun y => fn n y - g y)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) ≤
      (eLpNorm (fun y => fn n y - g y)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal := by
    exact ENNReal.toReal_mono (hdiffmem n).eLpNorm_lt_top.ne
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hrepbound := weak_harmonic_interior_representative_bound hρ hdiffU x hx
  have hC : 0 ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ := by
    exact mul_nonneg weakHarmonicInteriorSupConstant_nonneg (by positivity)
  rw [dist_eq_norm, Real.norm_eq_abs]
  have hval : |weakHarmonicInteriorRepresentative (fun y => fn n y - g y)
      x₀ hρ x| ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
        lpNorm (fun y => fn n y - g y)
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := hrepbound
  rw [← hrepdiff] at hval
  rw [← hrepn n x hx] at hval
  exact hval.trans (mul_le_mul_of_nonneg_left hdiffU_lp hC)

private lemma weakly_harmonic_interior_smooth_hvalue_uc_9 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
      let U : Set Vec3 := euclideanBall x₀ ρ;
      let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
      let g : Vec3 → ℝ := U.indicator h;
      let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
        Tendsto
            (fun (n : ℕ) =>
              (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace (fun (y : Vec3) => fn n y - g y)
                  (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal)
            atTop (𝓝 (0 : ℝ)) →
          (∀ (n : ℕ),
              ∀ x ∈ I,
                dist (fn n x) (weakHarmonicInteriorRepresentative g x₀ hρ x) ≤
                  weakHarmonicInteriorSupConstant * (ρ ^ (2 : ℕ))⁻¹ *
                    (@eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                        (fun (y : Vec3) => fn n y - g y) (ENNReal.ofReal (3 / 2 : ℝ))
                        volume).toReal) →
            let H : Vec3 → ℝ := fun (x : Vec3) => weakHarmonicInteriorRepresentative g x₀ hρ x;
            TendstoUniformlyOn fn H atTop I
    := by
  intro h x₀ ρ hρ U I g ε hεpos fn hconv_real hbound H
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hC : 0 ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ := by
    exact mul_nonneg weakHarmonicInteriorSupConstant_nonneg (by positivity)
  have hprod : Tendsto
      (fun n => weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
        (eLpNorm (fun y => fn n y - g y)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal)
      atTop (nhds 0) := by
    have hD : Tendsto (fun _ : ℕ => weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹)
        atTop (nhds (weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹)) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hD.mul hconv_real
  filter_upwards [hprod.eventually (gt_mem_nhds hδ)] with n hn x hx
  rw [dist_comm]
  exact (hbound n x hx).trans_lt hn

open scoped Classical in
private lemma weakly_harmonic_interior_smooth_hCont_10 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
      let U : Set Vec3 := euclideanBall x₀ ρ;
      let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
      IsOpen I →
        let g : Vec3 → ℝ := U.indicator h;
        let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
        ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
          let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
          let d : ℕ → Vec3 → Vec3 →L[ℝ] ℝ := fun (n : ℕ) (x : Vec3) => fderiv ℝ (fn n) x;
          ∀ (hd_cauchy : ∀ x ∈ I, CauchySeq (α := Vec3 →L[ℝ] ℝ) fun (n : ℕ) => d n x),
            let D : Vec3 → Vec3 →L[ℝ] ℝ := fun (x : Vec3) =>
              if hx : x ∈ I then
                Classical.choose (p := fun (x_1 : Vec3 →L[ℝ] ℝ) =>
                  Tendsto (fun (n : ℕ) => d n x) atTop (𝓝 x_1))
                  (cauchySeq_tendsto_of_complete (hd_cauchy x hx))
              else (0 : Vec3 →L[ℝ] ℝ);
            let H : Vec3 → ℝ := fun (x : Vec3) => weakHarmonicInteriorRepresentative g x₀ hρ x;
            (∀ x ∈ I, HasFDerivAt H (D x) x) →
              ContinuousOn D I → ContDiffOn ℝ (↑(1 : ℕ∞) : WithTop ℕ∞) H I
    := by
  intro h x₀ ρ hρ U I hIopen g ε hεpos fn d hd_cauchy D H hderiv hDcont
  have hdiffH : DifferentiableOn ℝ H I := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hfdwithin_cont : ContinuousOn
      (fun y => fderivWithin ℝ H I y) I := by
    apply hDcont.congr
    intro x hx
    change fderivWithin ℝ H I x = D x
    rw [fderivWithin_eq_fderiv
      (hIopen.uniqueDiffOn.uniqueDiffWithinAt hx) (hderiv x hx).differentiableAt]
    exact (hderiv x hx).fderiv
  have hfdwithin : ContDiffOn ℝ (0 : ℕ∞)
      (fun y => fderivWithin ℝ H I y) I :=
    contDiffOn_zero.mpr hfdwithin_cont
  exact contDiffOn_succ_of_fderivWithin hdiffH (by simp) hfdwithin

private lemma weakly_harmonic_interior_smooth_hfn_lp_global_11 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ},
      let U : Set Vec3 := euclideanBall x₀ ρ;
      let g : Vec3 → ℝ := U.indicator h;
      MemLp (m0 := MeasureSpace.toMeasurableSpace) g (ENNReal.ofReal (3 / 2 : ℝ)) volume →
        let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
        ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
          let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
          ∀ (n : ℕ),
            lpNorm (m0 := MeasureSpace.toMeasurableSpace) (fn n) (ENNReal.ofReal (3 / 2 : ℝ))
                volume ≤
              lpNorm (m0 := MeasureSpace.toMeasurableSpace) g (ENNReal.ofReal (3 / 2 : ℝ)) volume
    := by
  intro h x₀ ρ U g hgmem ε hεpos fn n
  have hyoung := young_convolution_nonneg_integral_one_of_aemeasurable
    (p := ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num) (by norm_num)
    (mollifier_nonneg (hεpos n))
    (integrable_of_integral_eq_one (mollifier_integral_one (hεpos n)))
    (mollifier_integral_one (hεpos n))
    (mollifier_contDiff (hεpos n) (n := 0)).continuous.measurable
    hgmem.aestronglyMeasurable.aemeasurable
  have hE : eLpNorm (fn n) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      eLpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    simpa only [fn, mollify] using hyoung
  rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
  exact ENNReal.toReal_mono hgmem.eLpNorm_lt_top.ne hE

open scoped Classical in
private lemma weakly_harmonic_interior_smooth_hD_bound_12 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ},
      (0 : ℝ) < ρ →
        let U : Set Vec3 := euclideanBall x₀ ρ;
        let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
        let g : Vec3 → ℝ := U.indicator h;
        let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
        ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
          let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
          (∀ (n : ℕ),
              MemLp (m0 := MeasureSpace.toMeasurableSpace) (fn n) (ENNReal.ofReal (3 / 2 : ℝ))
                volume) →
            (∀ (n : ℕ),
                MemLp (m0 := MeasureSpace.toMeasurableSpace) (fn n) (ENNReal.ofReal (3 / 2 : ℝ))
                  (Measure.restrict volume U)) →
              (∀ (n : ℕ), ContDiff ℝ (⊤ : ℕ∞) (fn n)) →
                (∀ (n : ℕ),
                    ∀ y ∈ euclideanBall x₀ ((3 : ℝ) * ρ / (4 : ℝ)),
                      spatialLaplacian (fn n) y = (0 : ℝ)) →
                  let d : ℕ → Vec3 → Vec3 →L[ℝ] ℝ := fun (n : ℕ) (x : Vec3) => fderiv ℝ (fn n) x;
                  ∀ (hd_cauchy : ∀ x ∈ I, CauchySeq (α := Vec3 →L[ℝ] ℝ) fun (n : ℕ) => d n x),
                    let D : Vec3 → Vec3 →L[ℝ] ℝ := fun (x : Vec3) =>
                      if hx : x ∈ I then
                        Classical.choose (p := fun (x_1 : Vec3 →L[ℝ] ℝ) =>
                          Tendsto (fun (n : ℕ) => d n x) atTop (𝓝 x_1))
                          (cauchySeq_tendsto_of_complete (hd_cauchy x hx))
                      else (0 : Vec3 →L[ℝ] ℝ);
                    (∀ x ∈ I, Tendsto (fun (n : ℕ) => d n x) atTop (𝓝 (D x))) →
                      (∀ x ∈ I,
                          euclideanBall x (ρ / (4 : ℝ)) ⊆
                            euclideanBall x₀ ((3 : ℝ) * ρ / (4 : ℝ))) →
                        lpNorm (m0 := MeasureSpace.toMeasurableSpace) g (ENNReal.ofReal (3 / 2 : ℝ))
                              volume =
                            lpNorm (m0 := MeasureSpace.toMeasurableSpace) h
                              (ENNReal.ofReal (3 / 2 : ℝ)) (Measure.restrict volume U) →
                          (∀ (n : ℕ),
                              lpNorm (m0 := MeasureSpace.toMeasurableSpace) (fn n)
                                  (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
                                lpNorm (m0 := MeasureSpace.toMeasurableSpace) g
                                  (ENNReal.ofReal (3 / 2 : ℝ)) volume) →
                            ∀ x ∈ I,
                              ‖D x‖ ≤
                                (576 : ℝ) * harmonicInteriorGradientSupConstant * (ρ ^ (3 : ℕ))⁻¹ *
                                  lpNorm (m0 := MeasureSpace.toMeasurableSpace) h
                                    (ENNReal.ofReal (3 / 2 : ℝ)) (Measure.restrict volume U)
    := by
  intro h x₀ ρ hρ U I g ε hεpos fn hfnmem hfnU hfnSmooth hfnHarm d hd_cauchy D hDlim hball_sub3
    hg_lp_eq
    hfn_lp_global x hx
  have hballU : euclideanBall x (ρ / 4) ⊆ U := by
    exact (hball_sub3 x hx).trans (by
      intro y hy
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
      have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy
      exact hy'.trans (by nlinarith only [hρ]))
  have hnorm_n : ∀ n, ‖d n x‖ ≤
      576 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by
    intro n
    have hlocalmem := (hfnU n).mono_measure
      (Measure.restrict_mono_set volume hballU)
    have hlocalharm : ∀ y ∈ euclideanBall x (ρ / 4),
        CKN.spatialLaplacian (fn n) y = 0 := by
      intro y hy
      exact hfnHarm n y (hball_sub3 x hx hy)
    have hxlocal : x ∈ euclideanBall x ((ρ / 4) / 2) := by
      have hlocalρ : 0 < (ρ / 4) / 2 := by positivity
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hlocalρ).2
      simp [vecEuclideanNorm, vecNormSq, vecDot]
      nlinarith only [hρ]
    have hgradn := smooth_harmonic_interior_gradient_norm_bound
      (x₀ := x) (ρ := ρ / 4) (hfnSmooth n) (by positivity)
      hlocalharm hlocalmem x hxlocal
    have hlocal_lp := lpNorm_restrict_mono hballU (hfnU n)
    have hUglobal : lpNorm (fn n) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict U) ≤ lpNorm (fn n)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
      rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
      exact ENNReal.toReal_mono (hfnmem n).eLpNorm_lt_top.ne
        (eLpNorm_mono_measure _ Measure.restrict_le_self)
    have hfnlp : lpNorm (fn n) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x (ρ / 4))) ≤
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) :=
      hlocal_lp.trans (hUglobal.trans ((hfn_lp_global n).trans_eq hg_lp_eq))
    calc
      ‖d n x‖ = ‖fderiv ℝ (fn n) x‖ := rfl
      _ ≤ 3 * vec3EuclideanNorm (classicalGradient (fn n) x) :=
        fderiv_norm_le_three_classicalGradient_smooth x
      _ ≤ 9 * harmonicInteriorGradientSupConstant * ((ρ / 4) ^ 3)⁻¹ *
          lpNorm (fn n) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x (ρ / 4))) := by
        exact (mul_le_mul_of_nonneg_left hgradn (by norm_num)).trans_eq (by ring)
      _ ≤ 9 * harmonicInteriorGradientSupConstant * ((ρ / 4) ^ 3)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by
        exact mul_le_mul_of_nonneg_left hfnlp (by
          exact mul_nonneg (mul_nonneg (by norm_num)
            harmonicInteriorGradientSupConstant_nonneg)
            (inv_nonneg.mpr (by positivity)))
      _ = _ := by
        have hscale : ((ρ / 4) ^ 3)⁻¹ = 64 * (ρ ^ 3)⁻¹ := by
          rw [show (ρ / 4) ^ 3 = ρ ^ 3 / 4 ^ 3 by ring, inv_div]
          norm_num [div_eq_mul_inv]
        rw [hscale]
        ring
  have hnormlim : Tendsto (fun n => ‖d n x‖) atTop (𝓝 ‖D x‖) :=
    (continuous_norm.tendsto (D x)).comp (hDlim x hx)
  exact le_of_tendsto hnormlim (Eventually.of_forall (fun n => hnorm_n n))

open scoped Classical in
private lemma weakly_harmonic_interior_smooth_hgrad_space_13 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
      let U : Set Vec3 := euclideanBall x₀ ρ;
      let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
      let g : Vec3 → ℝ := U.indicator h;
      let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
        let d : ℕ → Vec3 → Vec3 →L[ℝ] ℝ := fun (n : ℕ) (x : Vec3) => fderiv ℝ (fn n) x;
        ∀ (hd_cauchy : ∀ x ∈ I, CauchySeq (α := Vec3 →L[ℝ] ℝ) fun (n : ℕ) => d n x),
          let D : Vec3 → Vec3 →L[ℝ] ℝ := fun (x : Vec3) =>
            if hx : x ∈ I then
              Classical.choose (p := fun (x_1 : Vec3 →L[ℝ] ℝ) =>
                Tendsto (fun (n : ℕ) => d n x) atTop (𝓝 x_1))
                (cauchySeq_tendsto_of_complete (hd_cauchy x hx))
            else (0 : Vec3 →L[ℝ] ℝ);
          let H : Vec3 → ℝ := fun (x : Vec3) => weakHarmonicInteriorRepresentative g x₀ hρ x;
          (∀ x ∈ I, ∀ (i : Fin (3 : ℕ)), classicalGradient H x i = (D x : Vec3 → ℝ) (basisVec i)) →
            ∀ x ∈ I, ‖classicalGradient H x‖ ≤ ‖D x‖
    := by
  intro h x₀ ρ hρ U I g ε hεpos fn d hd_cauchy D H hgrad_D x hx
  rw [Pi.norm_def]
  change (↑(Finset.univ.sup (fun i : Fin 3 =>
    ‖classicalGradient H x i‖₊) : NNReal) : ℝ) ≤ ‖D x‖
  have hs : Finset.univ.sup (fun i : Fin 3 =>
      ‖classicalGradient H x i‖₊) ≤ ⟨‖D x‖, norm_nonneg _⟩ := by
    apply Finset.sup_le
    intro i hi
    have hi' : ‖classicalGradient H x i‖ ≤ ‖D x‖ := by
      rw [hgrad_D x hx i]
      have hiop := ContinuousLinearMap.le_opNorm (D x) (basisVec i)
      have hbi : ‖basisVec i‖ = 1 := by
        simp [basisVec, Pi.norm_single]
      exact hiop.trans_eq (by rw [hbi, mul_one])
    exact_mod_cast hi'
  exact_mod_cast hs

open scoped Classical in
private lemma weakly_harmonic_interior_smooth_hgrad_bound_H_14 :
    ∀ {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
      let U : Set Vec3 := euclideanBall x₀ ρ;
      let I : Set Vec3 := euclideanBall x₀ (ρ / (2 : ℝ));
      let g : Vec3 → ℝ := U.indicator h;
      let ε : ℕ → ℝ := fun (n : ℕ) => ρ / ((12 : ℝ) * ((↑n : ℝ) + (1 : ℝ)));
      ∀ (hεpos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let fn : ℕ → Vec3 → ℝ := fun (n : ℕ) => mollify g (ε n) (hεpos n);
        let d : ℕ → Vec3 → Vec3 →L[ℝ] ℝ := fun (n : ℕ) (x : Vec3) => fderiv ℝ (fn n) x;
        ∀ (hd_cauchy : ∀ x ∈ I, CauchySeq (α := Vec3 →L[ℝ] ℝ) fun (n : ℕ) => d n x),
          let D : Vec3 → Vec3 →L[ℝ] ℝ := fun (x : Vec3) =>
            if hx : x ∈ I then
              Classical.choose (p := fun (x_1 : Vec3 →L[ℝ] ℝ) =>
                Tendsto (fun (n : ℕ) => d n x) atTop (𝓝 x_1))
                (cauchySeq_tendsto_of_complete (hd_cauchy x hx))
            else (0 : Vec3 →L[ℝ] ℝ);
          let H : Vec3 → ℝ := fun (x : Vec3) => weakHarmonicInteriorRepresentative g x₀ hρ x;
          (∀ x ∈ I,
              ‖D x‖ ≤
                (576 : ℝ) * harmonicInteriorGradientSupConstant * (ρ ^ (3 : ℕ))⁻¹ *
                  lpNorm (m0 := MeasureSpace.toMeasurableSpace) h (ENNReal.ofReal (3 / 2 : ℝ))
                    (Measure.restrict volume U)) →
            (∀ x ∈ I, ‖classicalGradient H x‖ ≤ ‖D x‖) →
              ∀ x ∈ I,
                vec3EuclideanNorm (classicalGradient H x) ≤
                  (1728 : ℝ) * harmonicInteriorGradientSupConstant * (ρ ^ (3 : ℕ))⁻¹ *
                    lpNorm (m0 := MeasureSpace.toMeasurableSpace) h (ENNReal.ofReal (3 / 2 : ℝ))
                      (Measure.restrict volume U)
    := by
  intro h x₀ ρ hρ U I g ε hεpos fn d hd_cauchy D H hD_bound hgrad_space x hx
  have heuc := CKN.euclideanNorm_le_three_mul_space_norm
    (classicalGradient H x)
  calc
    vec3EuclideanNorm (classicalGradient H x) ≤
        3 * ‖classicalGradient H x‖ := by
      simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using heuc
    _ ≤ 3 * ‖D x‖ := mul_le_mul_of_nonneg_left (hgrad_space x hx) (by norm_num)
    _ ≤ 3 * (576 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U)) := by
      exact mul_le_mul_of_nonneg_left (hD_bound x hx) (by norm_num)
    _ = 1728 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
        lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by ring

theorem weakly_harmonic_interior_smooth
    {h : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hmem : MemLp h (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ ρ) h) :
    ∃ H : Vec3 → ℝ,
      ContDiffOn ℝ (1 : ℕ∞) H (euclideanBall x₀ (ρ / 2)) ∧
      h =ᵐ[volume.restrict (euclideanBall x₀ (ρ / 2))] H ∧
      (∀ x ∈ euclideanBall x₀ (ρ / 2),
        |H x| ≤ weakHarmonicInteriorSupConstant * (ρ ^ 2)⁻¹ *
          lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ))) ∧
      (∀ x ∈ euclideanBall x₀ (ρ / 2),
        vec3EuclideanNorm (classicalGradient H x) ≤
      1728 * harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
            lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall x₀ ρ))) := by
  classical
  let U : Set Vec3 := euclideanBall x₀ ρ
  let I : Set Vec3 := euclideanBall x₀ (ρ / 2)
  have hUopen : IsOpen U := euclidean_ball_isOpen_smooth hρ
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hIopen : IsOpen I := euclidean_ball_isOpen_smooth (by positivity)
  have hImeas : MeasurableSet I := hIopen.measurableSet
  let g : Vec3 → ℝ := U.indicator h
  have hgmem : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    dsimp [g]
    exact (memLp_indicator_iff_restrict hUmeas).2 hmem
  let ε : ℕ → ℝ := fun n => ρ / (12 * ((n : ℝ) + 1))
  have hεpos : ∀ n, 0 < ε n := fun n => approximation_scale_pos hρ n
  have hεle : ∀ n, ε n ≤ ρ / 12 := fun n => approximation_scale_le hρ n
  have hεtendsto : Tendsto ε atTop (nhds 0) := approximation_scale_tendsto hρ
  let fn : ℕ → Vec3 → ℝ := fun n => mollify g (ε n) (hεpos n)
  have hfnmem : ∀ n, MemLp (fn n) (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    intro n
    dsimp [fn]
    exact mollify_memLp_of_memLp (by norm_num) (by norm_num) hgmem (hεpos n)
  have hfnU : ∀ n, MemLp (fn n) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict U) := fun n => (hfnmem n).mono_measure Measure.restrict_le_self
  have hgun : MemLp g (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict U) := hgmem.mono_measure Measure.restrict_le_self
  have hfnSmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fn n) := by
    intro n
    exact CKN.mollify_contDiff (hεpos n)
      (hgmem.locallyIntegrable (by norm_num))
  have hfnHarm : ∀ n y, y ∈ euclideanBall x₀ (3 * ρ / 4) →
      CKN.spatialLaplacian (fn n) y = 0 := by
    intro n y hy
    apply weaklyHarmonicOn_mollify_spatialLaplacian_eq_zero hUmeas hmem hweak
    exact closedBall_subset_euclideanBall hρ (hεpos n) hy (hεle n)
  have hdiffSmooth : ∀ m n, ContDiff ℝ (⊤ : ℕ∞) (fn m - fn n) := by
    intro m n
    exact (hfnSmooth m).sub (hfnSmooth n)
  have hdiffHarm := @weakly_harmonic_interior_smooth_hdiffHarm_1 h x₀ ρ hεpos hfnSmooth hfnHarm
  have hdiffGlobal : ∀ m n, MemLp (fn m - fn n)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    intro m n
    exact (hfnmem m).sub (hfnmem n)
  have hdiffU : ∀ m n, MemLp (fn m - fn n)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by
    intro m n
    exact (hfnU m).sub (hfnU n)
  have hdiff_toReal := @weakly_harmonic_interior_smooth_hdiff_toReal_2 h x₀ ρ hgmem hεpos hfnmem
  let grad : ℕ → Vec3 → Vec3 := fun n => classicalGradient (fn n)
  have hgrad_bound := @weakly_harmonic_interior_smooth_hgrad_bound_3 h x₀ ρ hρ hεpos hfnSmooth
    hdiffSmooth hdiffHarm hdiffGlobal hdiffU hdiff_toReal
  have hdiffmem : ∀ n, MemLp (fun y => fn n y - g y)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume := by
    intro n
    exact (hfnmem n).sub hgmem
  have hconv : Tendsto
      (fun n => eLpNorm (fun y => fn n y - g y)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume) atTop (nhds 0) := by
    dsimp [fn]
    exact tendsto_eLpNorm_sub_zero_mollify
      (p := ENNReal.ofReal (3 / 2 : ℝ)) (by norm_num) (by norm_num)
      hgmem hεtendsto hεpos
  have hconv_real : Tendsto
      (fun n => (eLpNorm (fun y => fn n y - g y)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal) atTop (nhds 0) := by
    exact (ENNReal.tendsto_toReal_zero_iff
      (fun n => (hdiffmem n).eLpNorm_ne_top)).mpr hconv
  have hgrad_uc := @weakly_harmonic_interior_smooth_hgrad_uc_4 h x₀ ρ hρ hεpos hgrad_bound
    hconv_real
  have hgrad_cauchy : ∀ x, x ∈ I → CauchySeq (fun n => grad n x) := by
    intro x hx
    apply Metric.cauchySeq_iff.2
    intro δ hδ
    obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp hgrad_uc) δ hδ
    exact ⟨N, fun m hm n hn => hN m hm n hn x hx⟩
  let G : Vec3 → Vec3 := fun x =>
    if hx : x ∈ I then
      Classical.choose (cauchySeq_tendsto_of_complete
        (hgrad_cauchy x hx))
    else 0
  have hGlim : ∀ x, x ∈ I → Tendsto (fun n => grad n x) atTop (𝓝 (G x)) := by
    intro x hx
    simpa [G, hx] using Classical.choose_spec (cauchySeq_tendsto_of_complete
      (hgrad_cauchy x hx))
  let d : ℕ → Vec3 → Vec3 →L[ℝ] ℝ := fun n x => fderiv ℝ (fn n) x
  have hderiv_diff_bound := @weakly_harmonic_interior_smooth_hderiv_diff_bound_5 h x₀ ρ hεpos
    hfnSmooth hgrad_bound
  have hd_uc := @weakly_harmonic_interior_smooth_hd_uc_6 h x₀ ρ hρ hεpos hconv_real
    hderiv_diff_bound
  have hd_cauchy : ∀ x, x ∈ I → CauchySeq (fun n => d n x) := by
    intro x hx
    apply Metric.cauchySeq_iff.2
    intro δ hδ
    obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp hd_uc) δ hδ
    exact ⟨N, fun m hm n hn => hN m hm n hn x hx⟩
  let D : Vec3 → Vec3 →L[ℝ] ℝ := fun x =>
    if hx : x ∈ I then
      Classical.choose (cauchySeq_tendsto_of_complete (hd_cauchy x hx))
    else 0
  have hDlim : ∀ x, x ∈ I → Tendsto (fun n => d n x) atTop (𝓝 (D x)) := by
    intro x hx
    simpa [D, hx] using Classical.choose_spec (cauchySeq_tendsto_of_complete
      (hd_cauchy x hx))
  have hD_uc : TendstoUniformlyOn d D atTop I :=
    hd_uc.tendstoUniformlyOn_of_tendsto (fun x hx => hDlim x hx)
  have hrepn := @weakly_harmonic_interior_smooth_hrepn_7 h x₀ ρ hρ hgmem hεpos hfnHarm
  have hbound := @weakly_harmonic_interior_smooth_hbound_8 h x₀ ρ hρ hεpos hfnU hgun hdiffU
    hdiffmem hrepn
  let H : Vec3 → ℝ := fun x => weakHarmonicInteriorRepresentative g x₀ hρ x
  have hvalue_uc := @weakly_harmonic_interior_smooth_hvalue_uc_9 h x₀ ρ hρ hεpos hconv_real hbound
  have hderiv : ∀ x, x ∈ I → HasFDerivAt H (D x) x := by
    intro x hx
    exact hasFDerivAt_of_tendstoUniformlyOn hIopen hD_uc
      (fun n z hz => by
        dsimp [d]
        exact ((hfnSmooth n).differentiable (by simp) z).hasFDerivAt)
      (fun z hz => hvalue_uc.tendsto_at hz) hx
  have hDcont : ContinuousOn D I := by
    apply hD_uc.continuousOn
    exact Filter.Frequently.of_forall (fun n => by
      simpa [d] using (hfnSmooth n).continuous_fderiv (by simp) |>.continuousOn)
  have hCont := @weakly_harmonic_interior_smooth_hCont_10 h x₀ ρ hρ hIopen hεpos hd_cauchy hderiv
    hDcont
  have hball_sub3 : ∀ x, x ∈ I →
      euclideanBall x (ρ / 4) ⊆ euclideanBall x₀ (3 * ρ / 4) :=
    fun _ hx => euclidean_quarter_ball_subset_smooth hρ hx
  have hg_lp_eq : lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) volume =
      lpNorm h (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict U) := by
    dsimp [g]
    rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm,
      eLpNorm_indicator_eq_eLpNorm_restrict hUmeas]
  have hg_h_ae : g =ᵐ[volume.restrict U] h := by
    filter_upwards [ae_restrict_mem hUmeas] with y hy
    simp [g, hy]
  have hg_lp_local : lpNorm g (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict U) = lpNorm h (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict U) := by
    rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm,
      eLpNorm_congr_ae hg_h_ae]
  have hfn_lp_global := @weakly_harmonic_interior_smooth_hfn_lp_global_11 h x₀ ρ hgmem hεpos
  have hD_bound := @weakly_harmonic_interior_smooth_hD_bound_12 h x₀ ρ hρ hεpos hfnmem hfnU
    hfnSmooth hfnHarm hd_cauchy hDlim hball_sub3 hg_lp_eq hfn_lp_global
  have hgrad_D : ∀ x, x ∈ I → ∀ i : Fin 3,
      classicalGradient H x i = (D x) (basisVec i) := by
    intro x hx i
    change (fderiv ℝ H x) (basisVec i) = (D x) (basisVec i)
    rw [(hderiv x hx).fderiv]
  have hgrad_space := @weakly_harmonic_interior_smooth_hgrad_space_13 h x₀ ρ hρ hεpos hd_cauchy
    hgrad_D
  have hgrad_bound_H := @weakly_harmonic_interior_smooth_hgrad_bound_H_14 h x₀ ρ hρ hεpos
    hd_cauchy hD_bound hgrad_space
  refine ⟨H, hCont, ?_, ?_, ?_⟩
  · have hae := weakly_harmonic_interior_representative_ae hρ hmem hweak
    simpa [H, U, g, I]
      using hae
  · intro x hx
    have hb := weak_harmonic_interior_representative_bound hρ hgun x hx
    rw [hg_lp_local] at hb
    simpa [H, U, I] using hb
  · intro x hx
    simpa [I] using hgrad_bound_H x hx

end CKN.Foundation.Heat
