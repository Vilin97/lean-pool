/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorEstimatesBasic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Smooth
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Interior Estimates

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Heat

/-- Coefficient in the interior supremum estimate for a harmonic function. -/
noncomputable def harmonicInteriorSupConstant : ℝ :=
  (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
    (harmonicInteriorSourceConstant + 6 * harmonicInteriorGradientConstant)

/-- Coefficient in the interior supremum estimate for the harmonic gradient. -/
noncomputable def harmonicInteriorGradientSupConstant : ℝ :=
  (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
    (harmonicInteriorSourceGradientConstant +
      6 * harmonicInteriorKernelXGradientConstant)

lemma harmonicInteriorGradientSupConstant_nonneg :
    0 ≤ harmonicInteriorGradientSupConstant := by
  dsimp [harmonicInteriorGradientSupConstant]
  have hS := harmonicInteriorSourceGradientConstant_nonneg
  have hK := harmonicInteriorKernelXGradientConstant_nonneg
  positivity

private lemma line_hasDerivAt_sub (x y : Vec3) (j : Fin 3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • CKN.basisVec j - y)
      (CKN.basisVec j) t := by
  convert ((hasDerivAt_const (x := t) x).add
    ((hasDerivAt_id t).smul_const (CKN.basisVec j))).sub
      (hasDerivAt_const (x := t) y) using 1
  · funext s
    simp
  · simp

private lemma line_kernel_hasDerivAt {x y : Vec3} {j : Fin 3} {t : ℝ}
    (hxy : x + t • CKN.basisVec j - y ≠ 0) :
    HasDerivAt (fun s : ℝ => newtonianKernel
      (x + s • CKN.basisVec j - y))
      (CKN.spatialDeriv newtonianKernel j
        (x + t • CKN.basisVec j - y)) t := by
  have hfd := (newtonianKernel_hasFDerivAt hxy).comp t
    (line_hasDerivAt_sub x y j t).hasFDerivAt
  have hd := hfd.hasDerivAt
  convert hd using 1
  · rfl
  · change (fderiv ℝ newtonianKernel
      (x + t • CKN.basisVec j - y)) (CKN.basisVec j) = _
    simp [ContinuousLinearMap.comp_apply]

private lemma line_spatialDeriv_kernel_hasDerivAt
    {x y : Vec3} {i j : Fin 3} {t : ℝ}
    (hxy : x + t • CKN.basisVec j - y ≠ 0) :
    HasDerivAt (fun s : ℝ => CKN.spatialDeriv newtonianKernel i
      (x + s • CKN.basisVec j - y))
      (CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j
        (x + t • CKN.basisVec j - y)) t := by
  have hfd := (hasFDerivAt_newtonianKernel_spatialDeriv_formula hxy i).comp
    t (line_hasDerivAt_sub x y j t).hasFDerivAt
  have hd := hfd.hasDerivAt
  convert hd using 1
  · rfl
  · change (fderiv ℝ (CKN.spatialDeriv newtonianKernel i)
      (x + t • CKN.basisVec j - y)) (CKN.basisVec j) = _
    rw [(hasFDerivAt_newtonianKernel_spatialDeriv_formula hxy i).fderiv]
    simp [ContinuousLinearMap.comp_apply]

private lemma smooth_harmonic_interior_gradient_bound_hF₀'cont_1 :
    ∀ {H : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) H →
        ∀ {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
          ∀ x ∈ euclideanBall x₀ (ρ / (2 : ℝ)),
            ∀ (j : Fin (3 : ℕ)),
              let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
              let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
              let D : Vec3 → ℝ :=
                spatialLaplacian
                  (eta x₀
                    (by positivity : (0 : ℝ) < 4 * ρ / 3));
              Continuous D →
                let F₀' : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) =>
                  H y * spatialDeriv newtonianKernel j (z t - y) * D y;
                ContinuousOn (F₀' (0 : ℝ)) A
    := by
  intro H hH x₀ ρ hρ x hx j A z D hDcont F₀' y hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    have hd := cutoff_annulus_norm_distance_for_inner_half hρ (by rfl) hx hy
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hd)
  have hN := newtonianKernel_spatialDeriv_continuousAt hxy j
  have hsub : @ContinuousAt Vec3 Vec3 Pi.topologicalSpace Pi.topologicalSpace
      (fun w : Vec3 => x - w) y := by
    convert (continuousAt_const.sub
      (continuousAt_id : ContinuousAt (id : Vec3 → Vec3) y)) using 1
    on_goal 1 => ext w k
    rfl
  have hN' : @ContinuousAt Vec3 ℝ Pi.topologicalSpace
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fun w : Vec3 => spatialDeriv newtonianKernel j (x - w)) y :=
    by
      convert hN.comp hsub using 1
      ext w
      rfl
  have hHc : @Continuous Vec3 ℝ Pi.topologicalSpace
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace H := by
    exact hH.continuous
  have hDc : @Continuous Vec3 ℝ Pi.topologicalSpace
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace D := by
    exact hDcont
  have hprod :=
    ((hHc.continuousAt.mul hN').mul hDc.continuousAt).continuousWithinAt
      (s := A)
  have hprod' : ContinuousWithinAt (fun w : Vec3 =>
      H w * spatialDeriv newtonianKernel j (x - w) * D w) A y := by
    convert hprod using 1
  simpa [F₀', z] using hprod'

private lemma smooth_harmonic_interior_gradient_bound_hF₀'bound_2 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      MeasurableSet A →
        let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
        let S : Set ℝ := z ⁻¹' euclideanBall x₀ (ρ / (2 : ℝ));
        (∀ t ∈ S, z t ∈ euclideanBall x₀ (ρ / (2 : ℝ))) →
          let D : Vec3 → ℝ :=
            spatialLaplacian
              (eta x₀
                (by positivity : (0 : ℝ) < 4 * ρ / 3));
          let F₀' : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) =>
            H y * spatialDeriv newtonianKernel j (z t - y) * D y;
          ∀ᵐ (y : Vec3) ∂Measure.restrict volume A,
            ∀ t ∈ S, ‖F₀' t y‖ ≤ harmonicInteriorSourceGradientConstant * (ρ ^ (4 : ℕ))⁻¹ * |H y|
    := by
  intro H x₀ ρ hρ x j A hAmeas z S hzt_inner D F₀'
  filter_upwards [ae_restrict_mem hAmeas] with y hy
  intro t ht
  have hzmem := hzt_inner t ht
  have hb := source_kernel_spatialDeriv_bound_scaled hρ hzmem
    (by exact hy) j
  dsimp [F₀', z, D]
  rw [abs_mul]
  calc
    |H y * CKN.spatialDeriv newtonianKernel j
        (x + t • CKN.basisVec j - y)| *
        |CKN.spatialLaplacian (eta (ρ := 4 * ρ / 3)
          x₀ (by positivity)) y| =
        |H y| * |CKN.spatialDeriv newtonianKernel j
          (x + t • CKN.basisVec j - y) *
          CKN.spatialLaplacian (eta (ρ := 4 * ρ / 3)
            x₀ (by positivity)) y| := by
          rw [abs_mul, abs_mul]
          ring
    _ ≤ |H y| * (harmonicInteriorSourceGradientConstant *
        (ρ ^ 4)⁻¹) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [z] using hb)
        (abs_nonneg _)
    _ = _ := by ring

private lemma smooth_harmonic_interior_gradient_bound_hF₀'diff_3 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      MeasurableSet A →
        let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
        let S : Set ℝ := z ⁻¹' euclideanBall x₀ (ρ / (2 : ℝ));
        (∀ t ∈ S, z t ∈ euclideanBall x₀ (ρ / (2 : ℝ))) →
          let D : Vec3 → ℝ :=
            spatialLaplacian
              (eta x₀
                (by positivity : (0 : ℝ) < 4 * ρ / 3));
          let F₀ : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) => H y * newtonianKernel (z t - y) * D y;
          let F₀' : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) =>
            H y * spatialDeriv newtonianKernel j (z t - y) * D y;
          ∀ᵐ (y : Vec3) ∂Measure.restrict volume A,
            ∀ t ∈ S, HasDerivAt (fun (x : ℝ) => F₀ x y) (F₀' t y) t
    := by
  intro H x₀ ρ hρ x j A hAmeas z S hzt_inner D F₀ F₀'
  filter_upwards [ae_restrict_mem hAmeas] with y hy
  intro t ht
  have hzmem := hzt_inner t ht
  have hxy : z t - y ≠ 0 := by
    intro hzero
    have hd := cutoff_annulus_norm_distance_for_inner_half hρ (by rfl) hzmem hy
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hd)
  have hN := line_kernel_hasDerivAt (x := x) (y := y) (j := j) hxy
  have hp := (hN.const_mul (H y)).mul_const (D y)
  simpa only [F₀, F₀', z] using hp

private lemma smooth_harmonic_interior_gradient_bound_hGdiff_4 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      MeasurableSet A →
        let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
        let S : Set ℝ := z ⁻¹' euclideanBall x₀ (ρ / (2 : ℝ));
        (∀ t ∈ S, z t ∈ euclideanBall x₀ (ρ / (2 : ℝ))) →
          let G : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
            H y *
              spatialDeriv
                (kernelCutoffDerivative (z t) x₀
                  (by positivity : (0 : ℝ) < 4 * ρ / 3)
                  i)
                i y;
          let G' : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
            H y *
              (-spatialDeriv (spatialDeriv newtonianKernel i) j (z t - y) *
                  spatialDeriv
                    (eta x₀
                      (by positivity : (0 : ℝ) < 4 * ρ / 3))
                    i y +
                spatialDeriv newtonianKernel j (z t - y) *
                  spatialDeriv
                    (spatialDeriv
                      (eta x₀
                        (by positivity : (0 : ℝ) < 4 * ρ / 3))
                      i)
                    i y);
          ∀ (i : Fin (3 : ℕ)),
            ∀ᵐ (y : Vec3) ∂Measure.restrict volume A,
              ∀ t ∈ S, HasDerivAt (fun (x : ℝ) => G i x y) (G' i t y) t
    := by
  intro H x₀ ρ hρ x j A hAmeas z S hzt_inner G G' i
  filter_upwards [ae_restrict_mem hAmeas] with y hy
  intro t ht
  have hzmem := hzt_inner t ht
  have hxy : z t - y ≠ 0 := by
    intro hzero
    have hd := cutoff_annulus_norm_distance_for_inner_half hρ (by rfl)
      hzmem hy
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hd)
  have hne : ∀ᶠ s in 𝓝 t, z s - y ≠ 0 := by
    apply (isOpen_compl_singleton.preimage (by fun_prop)).mem_nhds
    exact hxy
  have hshift : (fun s : ℝ => CKN.spatialDeriv
      (fun w : Vec3 => newtonianKernel (z s - w)) i y) =ᶠ[𝓝 t]
      (fun s : ℝ => -CKN.spatialDeriv newtonianKernel i (z s - y)) := by
    filter_upwards [hne] with s hs
    exact spatialDeriv_newtonianKernel_shift_eq_neg hs i
  have ha := (line_spatialDeriv_kernel_hasDerivAt
    (x := x) (y := y) (i := i) (j := j) hxy).neg
  have ha' := ha.congr_of_eventuallyEq hshift
  have hb := (line_kernel_hasDerivAt
    (x := x) (y := y) (j := j) hxy).mul_const
    (CKN.spatialDeriv (CKN.spatialDeriv
      (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i y)
  have hc := ha'.mul_const
    (CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y)
  have hd := hc.add hb
  have heq : ∀ᶠ s in 𝓝 t, G i s y =
      H y * (CKN.spatialDeriv
        (fun w : Vec3 => newtonianKernel (z s - w)) i y *
        CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y +
        newtonianKernel (z s - y) * CKN.spatialDeriv
          (CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i y) := by
    filter_upwards [hne] with s hs
    dsimp [G]
    have hformula := spatialDeriv_kernelCutoffDerivative_of_ne (x₀ := x₀)
      (ρ := 4 * ρ / 3) (by positivity) hs i i
    rw [hformula]
  have hd' := hd.const_mul (H y)
  simpa only [G, G', z] using
    hd'.congr_of_eventuallyEq heq

private lemma smooth_harmonic_interior_gradient_bound_hGmeas_5 :
    ∀ {H : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) H →
        ∀ {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
          let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
          let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
          let S : Set ℝ := z ⁻¹' euclideanBall x₀ (ρ / (2 : ℝ));
          S ∈ 𝓝 (0 : ℝ) →
            (∀ t ∈ S, z t ∈ euclideanBall x₀ (ρ / (2 : ℝ))) →
              let G : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
                H y *
                  spatialDeriv
                    (kernelCutoffDerivative (z t) x₀
                      (by positivity : (0 : ℝ) < 4 * ρ / 3)
                      i)
                    i y;
              ∀ (i : Fin (3 : ℕ)),
                ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ),
                  AEStronglyMeasurable (m₀ := MeasureSpace.toMeasurableSpace) (G i t)
                    (Measure.restrict volume A)
    := by
  intro H hH x₀ ρ hρ x j A z S hS hzt_inner G i
  filter_upwards [hS] with t ht
  have hzt := hzt_inner t ht
  have hzt13 : z t ∈ euclideanBall x₀ (13 * (4 * ρ / 3) / 20) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hz := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hzt
    exact hz.trans (by nlinarith only [hρ])
  have hGint := kernelCutoffDerivative_integrable_mul_right_global hH
    (ρ := 4 * ρ / 3) (z t) x₀ (by positivity) hzt13 i
  have hGint' := hGint.mono_measure
    (Measure.restrict_le_self : volume.restrict A ≤ volume)
  simpa [G] using hGint'.aestronglyMeasurable

private lemma smooth_harmonic_interior_gradient_bound_hG'cont_6 :
    ∀ {H : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) H →
        ∀ {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
          ∀ x ∈ euclideanBall x₀ (ρ / (2 : ℝ)),
            ∀ (j : Fin (3 : ℕ)),
              let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
              let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
              let G' : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
                H y *
                  (-spatialDeriv (spatialDeriv newtonianKernel i) j (z t - y) *
                      spatialDeriv
                        (eta x₀
                          (by positivity : (0 : ℝ) < 4 * ρ / 3))
                        i y +
                    spatialDeriv newtonianKernel j (z t - y) *
                      spatialDeriv
                        (spatialDeriv
                          (eta x₀
                            (by positivity : (0 : ℝ) < 4 * ρ / 3))
                          i)
                        i y);
              ∀ (i : Fin (3 : ℕ)), ContinuousOn (G' i (0 : ℝ)) A
    := by
  intro H hH x₀ ρ hρ x hx j A z G' i y hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    have hd := cutoff_annulus_norm_distance_for_inner_half hρ (by rfl) hx hy
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hd)
  have hsub : @ContinuousAt Vec3 Vec3 Pi.topologicalSpace Pi.topologicalSpace
      (fun w : Vec3 => x - w) y := by
    convert (continuousAt_const.sub
      (continuousAt_id : ContinuousAt (id : Vec3 → Vec3) y)) using 1
    on_goal 1 => ext w k
    rfl
  have hHc : @Continuous Vec3 ℝ Pi.topologicalSpace
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace H := hH.continuous
  have hηc : @Continuous Vec3 ℝ Pi.topologicalSpace
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) := by
    exact (CKN.contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth x₀ (by positivity)) i).continuous
  have hηηc : @Continuous Vec3 ℝ Pi.topologicalSpace
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (CKN.spatialDeriv (CKN.spatialDeriv
        (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i) := by
    exact eta_spatialSecond_continuous_global x₀ (by positivity) i
  have hN := newtonianKernel_spatialDeriv_second_continuousAt hxy i j
  have hN' : @ContinuousAt Vec3 ℝ Pi.topologicalSpace
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fun w : Vec3 => CKN.spatialDeriv (CKN.spatialDeriv
        newtonianKernel i) j (x - w)) y := by
    convert hN.comp hsub using 1
    ext w
    rfl
  have hM := newtonianKernel_spatialDeriv_continuousAt hxy j
  have hM' : @ContinuousAt Vec3 ℝ Pi.topologicalSpace
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fun w : Vec3 => CKN.spatialDeriv newtonianKernel j (x - w)) y := by
    convert hM.comp hsub using 1
    ext w
    rfl
  have hp := hN'.mul hηc.continuousAt
  have hq := hM'.mul hηηc.continuousAt
  have hr := (hp.neg.add hq).mul hHc.continuousAt
  have hrs := hr.continuousWithinAt (s := A)
  have hrs' : ContinuousWithinAt (fun w : Vec3 =>
      H w * (-CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j
        (x - w) * CKN.spatialDeriv
          (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i w +
        CKN.spatialDeriv newtonianKernel j (x - w) *
          CKN.spatialDeriv (CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i w)) A y := by
    convert hrs using 1
    ext w
    simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply]
    ring
  simpa only [G', z, zero_smul, add_zero] using hrs'

private lemma smooth_harmonic_interior_gradient_bound_hGbound_7 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      MeasurableSet A →
        let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
        let S : Set ℝ := z ⁻¹' euclideanBall x₀ (ρ / (2 : ℝ));
        (∀ t ∈ S, z t ∈ euclideanBall x₀ (ρ / (2 : ℝ))) →
          let G' : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
            H y *
              (-spatialDeriv (spatialDeriv newtonianKernel i) j (z t - y) *
                  spatialDeriv
                    (eta x₀
                      (by positivity : (0 : ℝ) < 4 * ρ / 3))
                    i y +
                spatialDeriv newtonianKernel j (z t - y) *
                  spatialDeriv
                    (spatialDeriv
                      (eta x₀
                        (by positivity : (0 : ℝ) < 4 * ρ / 3))
                      i)
                    i y);
          ∀ (i : Fin (3 : ℕ)),
            ∀ᵐ (y : Vec3) ∂Measure.restrict volume A,
              ∀ t ∈ S,
                ‖G' i t y‖ ≤ harmonicInteriorKernelXGradientConstant * (ρ ^ (4 : ℕ))⁻¹ * |H y|
    := by
  intro H x₀ ρ hρ x j A hAmeas z S hzt_inner G' i
  filter_upwards [ae_restrict_mem hAmeas] with y hy
  intro t ht
  have hb := kernel_cutoff_x_derivative_bound_scaled hρ (hzt_inner t ht)
    hy i j
  dsimp [G', z]
  rw [abs_mul]
  calc
    |H y| * |-CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j
          (x + t • CKN.basisVec j - y) * CKN.spatialDeriv
            (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y +
        CKN.spatialDeriv newtonianKernel j
          (x + t • CKN.basisVec j - y) * CKN.spatialDeriv
            (CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀
              (by positivity)) i) i y| ≤
        |H y| * (harmonicInteriorKernelXGradientConstant * (ρ ^ 4)⁻¹) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [z] using hb)
        (abs_nonneg _)
    _ = _ := by ring

private lemma smooth_harmonic_interior_gradient_bound_hrep_t_8 :
    ∀ {H : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) H →
        ∀ {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
          (∀ y ∈ euclideanBall x₀ ρ, spatialLaplacian H y = (0 : ℝ)) →
            ∀ (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
              let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
              let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
              let S : Set ℝ := z ⁻¹' euclideanBall x₀ (ρ / (2 : ℝ));
              (∀ t ∈ S, z t ∈ euclideanBall x₀ (ρ / (2 : ℝ))) →
                let D : Vec3 → ℝ :=
                  spatialLaplacian
                    (eta x₀
                      (by positivity : (0 : ℝ) < 4 * ρ / 3));
                let F₀ : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) =>
                  H y * newtonianKernel (z t - y) * D y;
                let G : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
                  H y *
                    spatialDeriv
                      (kernelCutoffDerivative (z t) x₀
                        (by positivity : (0 : ℝ) < 4 * ρ / 3)
                        i)
                      i y;
                (∀ (t : ℝ),
                    Eq (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                        F₀ t y)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                        fun (y : Vec3) => F₀ t y)) →
                  (∀ (i : Fin (3 : ℕ)),
                      ∀ t ∈ S,
                        Eq (α := ℝ)
                          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
                            G i t y)
                          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                            (Measure.restrict volume A) fun (y : Vec3) => G i t y)) →
                    ∀ t ∈ S,
                      H (z t) =
                        (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                              (Measure.restrict volume A) fun (y : Vec3) => F₀ t y) +
                          (2 : ℝ) *
                            ∑ i : Fin (3 : ℕ),
                              @integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                (Measure.restrict volume A) fun (y : Vec3) => G i t y
    := by
  intro H hH x₀ ρ hρ hHarm x j A z S hzt_inner D F₀ G hF₀restrict hGrestrict t ht
  have hzt := hzt_inner t ht
  have hztinner : z t ∈ euclideanBall x₀ (13 * (4 * ρ / 3) / 20) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hz := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hzt
    exact hz.trans (by nlinarith only [hρ])
  have hrep := smooth_harmonic_annular_representation_on_outer hH
    (by positivity) (by
      intro y hy
      apply hHarm y
      have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hy
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).2
      rw [show 3 * (4 * ρ / 3) / 4 = ρ by ring] at hy'
      exact hy') hztinner
  have hint : (∫ y : Vec3, newtonianKernel (z t - y) * (H y * D y))
      = ∫ y : Vec3, F₀ t y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only [F₀]
    ring
  calc
    H (z t) = (-∫ y, F₀ t y) + 2 * ∑ i : Fin 3, ∫ y, G i t y := by
      rw [← hint]
      simpa only [G, D] using hrep
    _ = (-∫ y in A, F₀ t y) + 2 * ∑ i : Fin 3, ∫ y in A, G i t y := by
      rw [hF₀restrict t]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      exact hGrestrict i t ht

private lemma smooth_harmonic_interior_gradient_bound_kernel_lp_bound_9 :
    ∀ {x₀ : Vec3} {ρ : ℝ},
      (0 : ℝ) < ρ →
        let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
        MeasurableSet A →
          A ⊆ euclideanBall x₀ ρ →
            ∀ (hAvol : Ne (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) A : ℝ≥0∞) (∞ : ℝ≥0∞)),
              let _ : IsFiniteMeasure (volume.restrict A) :=
                Iff.mpr (isFiniteMeasure_restrict (s := A)) hAvol;
              ∀ {k : Vec3 → ℝ} {C : ℝ},
                ContinuousOn k A →
                  (0 : ℝ) ≤ C →
                    (∀ y ∈ A, |k y| ≤ C) →
                      MemLp (m0 := MeasureSpace.toMeasurableSpace) k (ENNReal.ofReal (3 : ℝ))
                          (Measure.restrict volume A) ∧
                        lpNorm (m0 := MeasureSpace.toMeasurableSpace) k (ENNReal.ofReal (3 : ℝ))
                            (Measure.restrict volume A) ≤
                          C * (ρ * (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ))
    := by
  intro x₀ ρ hρ A hAmeas hAsub hAvol localHypothesis7 k C hkcont hC hkbound
  have hk := memLp_of_continuousOn_bound hAmeas hkcont C hkbound
    (ENNReal.ofReal (3 : ℝ))
  have hp := lpNorm_bound_on hAmeas
    (by norm_num : ENNReal.ofReal (3 : ℝ) ≠ 0)
    (by norm_num : ENNReal.ofReal (3 : ℝ) ≠ ∞) C hC
    (fun y hy => by simpa only [Real.norm_eq_abs] using hkbound y hy)
  have hp' : lpNorm k (ENNReal.ofReal (3 : ℝ))
      (volume.restrict A) ≤ C * (volume A).toReal ^ (1 / (3 : ℝ)) := by
    convert hp using 1
    norm_num
  have hv := volume_root_bound hρ hAsub
  refine ⟨hk, ?_⟩
  exact (hp'.trans (mul_le_mul_of_nonneg_left hv hC))

private lemma smooth_harmonic_interior_gradient_bound_hk₀'cont_10 :
    ∀ {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
      ∀ x ∈ euclideanBall x₀ (ρ / (2 : ℝ)),
        ∀ (j : Fin (3 : ℕ)),
          let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
          let D : Vec3 → ℝ :=
            spatialLaplacian
              (eta x₀
                (by positivity : (0 : ℝ) < 4 * ρ / 3));
          Continuous D →
            let k₀' : Vec3 → ℝ := fun (y : Vec3) => spatialDeriv newtonianKernel j (x - y) * D y;
            ContinuousOn k₀' A
    := by
  intro x₀ ρ hρ x hx j A D hDcont k₀' y hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    have hd := cutoff_annulus_norm_distance_for_inner_half hρ (by rfl) hx hy
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hd)
  have hsub : ContinuousAt (fun w : Vec3 => x - w) y := by
    fun_prop
  have hN := (newtonianKernel_spatialDeriv_continuousAt hxy j).comp hsub
  exact hN.continuousWithinAt.mul hDcont.continuousAt.continuousWithinAt

private lemma smooth_harmonic_interior_gradient_bound_hsource_deriv_bound_11 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      MeasurableSet A →
        ∀ (hAvol : Ne (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) A : ℝ≥0∞) (∞ : ℝ≥0∞)),
          let _ : IsFiniteMeasure (volume.restrict A) :=
            Iff.mpr (isFiniteMeasure_restrict (s := A)) hAvol;
          MemLp (m0 := MeasureSpace.toMeasurableSpace) H (ENNReal.ofReal (3 / 2 : ℝ))
              (Measure.restrict volume A) →
            lpNorm (m0 := MeasureSpace.toMeasurableSpace) H (ENNReal.ofReal (3 / 2 : ℝ))
                  (Measure.restrict volume A) ≤
                lpNorm (m0 := MeasureSpace.toMeasurableSpace) H (ENNReal.ofReal (3 / 2 : ℝ))
                  (Measure.restrict volume (euclideanBall x₀ ρ)) →
              let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
              let D : Vec3 → ℝ :=
                spatialLaplacian
                  (eta x₀
                    (by positivity : (0 : ℝ) < 4 * ρ / 3));
              let F₀' : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) =>
                H y * spatialDeriv newtonianKernel j (z t - y) * D y;
              let k₀' : Vec3 → ℝ := fun (y : Vec3) => spatialDeriv newtonianKernel j (x - y) * D y;
              MemLp (m0 := MeasureSpace.toMeasurableSpace) k₀' (ENNReal.ofReal (3 : ℝ))
                    (Measure.restrict volume A) ∧
                  lpNorm (m0 := MeasureSpace.toMeasurableSpace) k₀' (ENNReal.ofReal (3 : ℝ))
                      (Measure.restrict volume A) ≤
                    harmonicInteriorSourceGradientConstant * (ρ ^ (4 : ℕ))⁻¹ *
                      (ρ * (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ)) →
                |@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                      fun (y : Vec3) => F₀' (0 : ℝ) y| ≤
                  harmonicInteriorSourceGradientConstant *
                        (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ) *
                      (ρ ^ (3 : ℕ))⁻¹ *
                    lpNorm (m0 := MeasureSpace.toMeasurableSpace) H (ENNReal.ofReal (3 / 2 : ℝ))
                      (Measure.restrict volume (euclideanBall x₀ ρ))
    := by
  intro H x₀ ρ hρ x j A hAmeas hAvol localHypothesis9 hH_A hHlp_mono z D F₀' k₀' hk₀'data
  have hk₀'zero : ∀ y, y ∉ A → k₀' y = 0 := by
    intro y hy
    dsimp [k₀', D]
    have hz := eta_laplacian_zero_off_annulus (R := 4 * ρ / 3)
      (by positivity) (by simpa [A] using hy)
    simp [hz]
  have hb := integral_mul_memLp_bound_on hAmeas hH_A hk₀'data.1
    hk₀'zero
  have hrestrict : (∫ y, H y * k₀' y) = ∫ y in A, H y * k₀' y := by
    rw [← integral_indicator hAmeas]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ A
    · simp [hy]
    · simp [hy, hk₀'zero y hy]
  calc
    |∫ y in A, F₀' 0 y| = |∫ y in A, H y * k₀' y| := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hAmeas] with y hy
      simp only [F₀', k₀', z, zero_smul, add_zero, mul_assoc]
    _ = |∫ y, H y * k₀' y| := by rw [hrestrict]
    _ ≤
        lpNorm H (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) *
          lpNorm k₀' (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := by
      exact hb
    _ ≤ lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) *
        (harmonicInteriorSourceGradientConstant *
          (ρ ^ 4)⁻¹ * (ρ * (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)))) := by
      calc
        _ ≤ lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) *
            lpNorm k₀' (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) :=
          mul_le_mul_of_nonneg_right hHlp_mono lpNorm_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_left hk₀'data.2 lpNorm_nonneg
    _ = _ := by
      field_simp [hρ.ne']

private lemma smooth_harmonic_interior_gradient_bound_hkGcont_12 :
    ∀ {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ),
      ∀ x ∈ euclideanBall x₀ (ρ / (2 : ℝ)),
        ∀ (j : Fin (3 : ℕ)),
          let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
          let kG : Fin (3 : ℕ) → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (y : Vec3) =>
            -spatialDeriv (spatialDeriv newtonianKernel i) j (x - y) *
                spatialDeriv
                  (eta x₀
                    (by positivity : (0 : ℝ) < 4 * ρ / 3))
                  i y +
              spatialDeriv newtonianKernel j (x - y) *
                spatialDeriv
                  (spatialDeriv
                    (eta x₀
                      (by positivity : (0 : ℝ) < 4 * ρ / 3))
                    i)
                  i y;
          ∀ (i : Fin (3 : ℕ)), ContinuousOn (kG i) A
    := by
  intro x₀ ρ hρ x hx j A kG i y hy
  have hxy : x - y ≠ 0 := by
    intro hzero
    have hd := cutoff_annulus_norm_distance_for_inner_half hρ (by rfl) hx hy
    rw [hzero] at hd
    exact (not_lt_of_ge (by positivity : 0 ≤ ρ / 30)) (by simpa using hd)
  have hsub : ContinuousAt (fun w : Vec3 => x - w) y := by fun_prop
  have hηc : Continuous (CKN.spatialDeriv
      (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) :=
    (CKN.contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth x₀ (by positivity)) i).continuous
  have hηηc : Continuous (CKN.spatialDeriv (CKN.spatialDeriv
      (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i) :=
    eta_spatialSecond_continuous_global x₀ (by positivity) i
  have hN := (newtonianKernel_spatialDeriv_second_continuousAt hxy i j).comp hsub
  have hM := (newtonianKernel_spatialDeriv_continuousAt hxy j).comp hsub
  have hp := (hN.continuousWithinAt (s := A)).mul
    (hηc.continuousAt.continuousWithinAt (s := A))
  have hq := (hM.continuousWithinAt (s := A)).mul
    (hηηc.continuousAt.continuousWithinAt (s := A))
  have hrs := hp.neg.add hq
  convert hrs using 1
  ext w
  simp only [kG, Function.comp_apply, Pi.mul_apply, Pi.add_apply, Pi.neg_apply]
  ring

private lemma smooth_harmonic_interior_gradient_bound_hG_deriv_bound_13 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      MeasurableSet A →
        ∀ (hAvol : Ne (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) A : ℝ≥0∞) (∞ : ℝ≥0∞)),
          let _ : IsFiniteMeasure (volume.restrict A) :=
            Iff.mpr (isFiniteMeasure_restrict (s := A)) hAvol;
          MemLp (m0 := MeasureSpace.toMeasurableSpace) H (ENNReal.ofReal (3 / 2 : ℝ))
              (Measure.restrict volume A) →
            lpNorm (m0 := MeasureSpace.toMeasurableSpace) H (ENNReal.ofReal (3 / 2 : ℝ))
                  (Measure.restrict volume A) ≤
                lpNorm (m0 := MeasureSpace.toMeasurableSpace) H (ENNReal.ofReal (3 / 2 : ℝ))
                  (Measure.restrict volume (euclideanBall x₀ ρ)) →
              let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
              let G' : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
                H y *
                  (-spatialDeriv (spatialDeriv newtonianKernel i) j (z t - y) *
                      spatialDeriv
                        (eta x₀
                          (by positivity : (0 : ℝ) < 4 * ρ / 3))
                        i y +
                    spatialDeriv newtonianKernel j (z t - y) *
                      spatialDeriv
                        (spatialDeriv
                          (eta x₀
                            (by positivity : (0 : ℝ) < 4 * ρ / 3))
                          i)
                        i y);
              let kG : Fin (3 : ℕ) → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (y : Vec3) =>
                -spatialDeriv (spatialDeriv newtonianKernel i) j (x - y) *
                    spatialDeriv
                      (eta x₀
                        (by positivity : (0 : ℝ) < 4 * ρ / 3))
                      i y +
                  spatialDeriv newtonianKernel j (x - y) *
                    spatialDeriv
                      (spatialDeriv
                        (eta x₀
                          (by positivity : (0 : ℝ) < 4 * ρ / 3))
                        i)
                      i y;
              (∀ (i : Fin (3 : ℕ)),
                  MemLp (m0 := MeasureSpace.toMeasurableSpace) (kG i) (ENNReal.ofReal (3 : ℝ))
                      (Measure.restrict volume A) ∧
                    lpNorm (m0 := MeasureSpace.toMeasurableSpace) (kG i) (ENNReal.ofReal (3 : ℝ))
                        (Measure.restrict volume A) ≤
                      harmonicInteriorKernelXGradientConstant * (ρ ^ (4 : ℕ))⁻¹ *
                        (ρ * (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ))) →
                (∀ (i : Fin (3 : ℕ)), ∀ y ∉ A, kG i y = (0 : ℝ)) →
                  ∀ (i : Fin (3 : ℕ)),
                    |@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                          fun (y : Vec3) => G' i (0 : ℝ) y| ≤
                      harmonicInteriorKernelXGradientConstant *
                            (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ) *
                          (ρ ^ (3 : ℕ))⁻¹ *
                        lpNorm (m0 := MeasureSpace.toMeasurableSpace) H (ENNReal.ofReal (3 / 2 : ℝ))
                          (Measure.restrict volume (euclideanBall x₀ ρ))
    := by
  intro H x₀ ρ hρ x j A hAmeas hAvol localHypothesis9 hH_A hHlp_mono z G' kG hkGdata hkGzero i
  have hb := integral_mul_memLp_bound_on hAmeas hH_A (hkGdata i).1
    (hkGzero i)
  have hpoint : ∀ᵐ y ∂(volume.restrict A), G' i 0 y = H y * kG i y := by
    filter_upwards [ae_restrict_mem hAmeas] with y hy
    simp only [G', kG, z, zero_smul, add_zero]
  have hrestrict : (∫ y, H y * kG i y) = ∫ y in A, H y * kG i y := by
    rw [← integral_indicator hAmeas]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ A
    · simp [hy]
    · simp [hy, hkGzero i y hy]
  calc
    |∫ y in A, G' i 0 y| = |∫ y in A, H y * kG i y| := by
      congr 1
      exact integral_congr_ae hpoint
    _ = |∫ y, H y * kG i y| := by rw [hrestrict]
    _ ≤ lpNorm H (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict A) *
        lpNorm (kG i) (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) := hb
    _ ≤ lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) *
        (harmonicInteriorKernelXGradientConstant * (ρ ^ 4)⁻¹ *
          (ρ * (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)))) := by
      calc
        _ ≤ lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) *
            lpNorm (kG i) (ENNReal.ofReal (3 : ℝ)) (volume.restrict A) :=
          mul_le_mul_of_nonneg_right hHlp_mono lpNorm_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_left (hkGdata i).2 lpNorm_nonneg
    _ = _ := by field_simp [hρ.ne']

private lemma smooth_harmonic_interior_gradient_bound_hsumG_14 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
      let G' : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
        H y *
          (-spatialDeriv (spatialDeriv newtonianKernel i) j (z t - y) *
              spatialDeriv
                (eta x₀
                  (by positivity : (0 : ℝ) < 4 * ρ / 3))
                i y +
            spatialDeriv newtonianKernel j (z t - y) *
              spatialDeriv
                (spatialDeriv
                  (eta x₀
                    (by positivity : (0 : ℝ) < 4 * ρ / 3))
                  i)
                i y);
      (∀ (i : Fin (3 : ℕ)),
          |@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                fun (y : Vec3) => G' i (0 : ℝ) y| ≤
            harmonicInteriorKernelXGradientConstant * (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ) *
                (ρ ^ (3 : ℕ))⁻¹ *
              lpNorm (m0 := MeasureSpace.toMeasurableSpace) H (ENNReal.ofReal (3 / 2 : ℝ))
                (Measure.restrict volume (euclideanBall x₀ ρ))) →
        |(2 : ℝ) *
              ∑ i : Fin (3 : ℕ),
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                  fun (y : Vec3) => G' i (0 : ℝ) y| ≤
          (6 : ℝ) * harmonicInteriorKernelXGradientConstant *
                (Real.pi * (4 : ℝ) / (3 : ℝ)) ^ (1 / 3 : ℝ) *
              (ρ ^ (3 : ℕ))⁻¹ *
            lpNorm (m0 := MeasureSpace.toMeasurableSpace) H (ENNReal.ofReal (3 / 2 : ℝ))
              (Measure.restrict volume (euclideanBall x₀ ρ))
    := by
  intro H x₀ ρ hρ x j A z G' hG_deriv_bound
  rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  let I : Fin 3 → ℝ := fun i => ∫ y in A, G' i 0 y
  change 2 * |∑ i : Fin 3, I i| ≤ _
  have habs : |∑ i : Fin 3, I i| ≤ ∑ i : Fin 3, |I i| := by
    simpa only [Fin.sum_univ_three] using
      (Finset.abs_sum_le_sum_abs I (Finset.univ : Finset (Fin 3)))
  calc
    2 * |∑ i : Fin 3, I i| ≤ 2 * ∑ i : Fin 3, |I i| :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ 2 * ∑ i : Fin 3,
        (harmonicInteriorKernelXGradientConstant *
          (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) * (ρ ^ 3)⁻¹ *
          lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : 0 ≤ (2 : ℝ))
      apply Finset.sum_le_sum
      intro i hi
      exact hG_deriv_bound i
    _ = _ := by simp; ring

private lemma smooth_harmonic_interior_gradient_bound_hAvol_1 :
    ∀ {x₀ : Vec3} {ρ : ℝ},
      (0 : ℝ) < ρ →
        let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
        A ⊆ euclideanBall x₀ ρ → Ne (α := ℝ≥0∞) ((volume : Set Vec3 → ℝ≥0∞) A : ℝ≥0∞) (∞ : ℝ≥0∞)
    := by
  intro x₀ ρ hρ A hAsub
  apply ne_of_lt
  have hAclosed : A ⊆ euclideanClosedBall x₀ ρ := by
    intro y hy
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hρ.le).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).1 (hAsub hy)).le
  exact lt_of_le_of_lt (measure_mono hAclosed)
    ((isCompact_euclideanClosedBall x₀ hρ.le).measure_lt_top)

private lemma smooth_harmonic_interior_gradient_bound_hF₀full_2 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
      let D : Vec3 → ℝ :=
        spatialLaplacian
          (eta x₀
            (by positivity : (0 : ℝ) < 4 * ρ / 3));
      (Continuous (Y := ℝ) fun (y : Vec3) => H y * D y) →
        (HasCompactSupport (β := ℝ) fun (y : Vec3) => H y * D y) →
          let F₀ : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) => H y * newtonianKernel (z t - y) * D y;
          ∀ (t : ℝ), @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (F₀ t) volume
    := by
  intro H x₀ ρ hρ x j z D hHDcont hHDsupport F₀ t
  have h := newtonianKernel_mul_compact_integrable_global hHDcont hHDsupport (z t)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  dsimp only [F₀]
  ring

private lemma smooth_harmonic_interior_gradient_bound_hGint_3 :
    ∀ {H : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) H →
        ∀ {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
          let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
          x ∈ euclideanBall x₀ ((13 : ℝ) * ((4 : ℝ) * ρ / (3 : ℝ)) / (20 : ℝ)) →
            let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
            let G : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
              H y *
                spatialDeriv
                  (kernelCutoffDerivative (z t) x₀
                    (by positivity : (0 : ℝ) < 4 * ρ / 3)
                    i)
                  i y;
            ∀ (i : Fin (3 : ℕ)),
              @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (G i (0 : ℝ))
                (Measure.restrict volume A)
    := by
  intro H hH x₀ ρ hρ x j A hxinner z G i
  have h := kernelCutoffDerivative_integrable_mul_right_global hH x x₀
    (ρ := 4 * ρ / 3) (by positivity) hxinner i
  have h' := h.mono_measure
    (Measure.restrict_le_self : volume.restrict A ≤ volume)
  simpa [G, z] using h'

private lemma smooth_harmonic_interior_gradient_bound_hF₀zero_4 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
      let D : Vec3 → ℝ :=
        spatialLaplacian
          (eta x₀
            (by positivity : (0 : ℝ) < 4 * ρ / 3));
      let F₀ : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) => H y * newtonianKernel (z t - y) * D y;
      ∀ (t : ℝ), ∀ y ∉ A, F₀ t y = (0 : ℝ)
    := by
  intro H x₀ ρ hρ x j A z D F₀ t y hy
  dsimp [F₀, D]
  have hz := eta_laplacian_zero_off_annulus (R := 4 * ρ / 3)
    (by positivity) (by simpa [A] using hy)
  simp [hz]

private lemma smooth_harmonic_interior_gradient_bound_hGzero_5 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
      let S : Set ℝ := z ⁻¹' euclideanBall x₀ (ρ / (2 : ℝ));
      (∀ t ∈ S, z t ∈ euclideanBall x₀ (ρ / (2 : ℝ))) →
        let G : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
          H y *
            spatialDeriv
              (kernelCutoffDerivative (z t) x₀
                (by positivity : (0 : ℝ) < 4 * ρ / 3)
                i)
              i y;
        ∀ (i : Fin (3 : ℕ)), ∀ t ∈ S, ∀ y ∉ A, G i t y = (0 : ℝ)
    := by
  intro H x₀ ρ hρ x j A z S hzt_inner G i t ht y hy
  dsimp [G]
  have hz := kernel_cutoff_derivative_zero_off_annulus (R := 4 * ρ / 3)
    hρ (by rfl) (by positivity) (hzt_inner t ht) hy i i
  simp [hz]

private lemma smooth_harmonic_interior_gradient_bound_hF₀restrict_6 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      MeasurableSet A →
        let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
        let D : Vec3 → ℝ :=
          spatialLaplacian
            (eta x₀
              (by positivity : (0 : ℝ) < 4 * ρ / 3));
        let F₀ : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) => H y * newtonianKernel (z t - y) * D y;
        (∀ (t : ℝ), ∀ y ∉ A, F₀ t y = (0 : ℝ)) →
          ∀ (t : ℝ),
            Eq (α := ℝ)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) => F₀ t y)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                fun (y : Vec3) => F₀ t y)
    := by
  intro H x₀ ρ hρ x j A hAmeas z D F₀ hF₀zero t
  rw [← integral_indicator hAmeas]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ A
  · simp [hy]
  · simp [hy, hF₀zero t y hy]

private lemma smooth_harmonic_interior_gradient_bound_hGrestrict_7 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      MeasurableSet A →
        let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
        let S : Set ℝ := z ⁻¹' euclideanBall x₀ (ρ / (2 : ℝ));
        let G : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
          H y *
            spatialDeriv
              (kernelCutoffDerivative (z t) x₀
                (by positivity : (0 : ℝ) < 4 * ρ / 3)
                i)
              i y;
        (∀ (i : Fin (3 : ℕ)), ∀ t ∈ S, ∀ y ∉ A, G i t y = (0 : ℝ)) →
          ∀ (i : Fin (3 : ℕ)),
            ∀ t ∈ S,
              Eq (α := ℝ)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) => G i t y)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                  fun (y : Vec3) => G i t y)
    := by
  intro H x₀ ρ hρ x j A hAmeas z S G hGzero i t ht
  rw [← integral_indicator hAmeas]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ A
  · simp [hy]
  · simp [hy, hGzero i t ht y hy]

private lemma smooth_harmonic_interior_gradient_bound_hline_8 :
    ∀ (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
      HasDerivAt z (basisVec j) (0 : ℝ)
    := by
  intro x j z
  dsimp [z]
  have h := (hasDerivAt_const (x := (0 : ℝ)) x).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (CKN.basisVec j))
  convert h using 1
  · ext t
    simp
  · simp

private lemma smooth_harmonic_interior_gradient_bound_hleft_9 :
    ∀ {H : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) H →
        ∀ (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
          let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
          HasDerivAt z (basisVec j) (0 : ℝ) →
            HasDerivAt (fun (t : ℝ) => H (z t)) (spatialDeriv H j x) (0 : ℝ)
    := by
  intro H hH x j z hline
  have hfd := (hH.differentiable (by norm_num) (z 0)).hasFDerivAt.comp 0
    hline.hasFDerivAt
  have h := hfd.hasDerivAt
  convert h using 1
  · rfl
  · simp [CKN.spatialDeriv, z, ContinuousLinearMap.comp_apply]

private lemma smooth_harmonic_interior_gradient_bound_hright_10 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
      let D : Vec3 → ℝ :=
        spatialLaplacian
          (eta x₀
            (by positivity : (0 : ℝ) < 4 * ρ / 3));
      let F₀ : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) => H y * newtonianKernel (z t - y) * D y;
      let F₀' : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) =>
        H y * spatialDeriv newtonianKernel j (z t - y) * D y;
      @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (F₀' (0 : ℝ)) (Measure.restrict volume A) ∧
          HasDerivAt (F := ℝ)
            (fun (n : ℝ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                fun (a : Vec3) => F₀ n a)
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
              fun (a : Vec3) => F₀' (0 : ℝ) a)
            (0 : ℝ) →
        let G : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
          H y *
            spatialDeriv
              (kernelCutoffDerivative (z t) x₀
                (by positivity : (0 : ℝ) < 4 * ρ / 3)
                i)
              i y;
        let G' : Fin (3 : ℕ) → ℝ → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (t : ℝ) (y : Vec3) =>
          H y *
            (-spatialDeriv (spatialDeriv newtonianKernel i) j (z t - y) *
                spatialDeriv
                  (eta x₀
                    (by positivity : (0 : ℝ) < 4 * ρ / 3))
                  i y +
              spatialDeriv newtonianKernel j (z t - y) *
                spatialDeriv
                  (spatialDeriv
                    (eta x₀
                      (by positivity : (0 : ℝ) < 4 * ρ / 3))
                    i)
                  i y);
        (∀ (i : Fin (3 : ℕ)),
            @Integrable _ _ _ _ MeasureSpace.toMeasurableSpace (G' i (0 : ℝ))
                (Measure.restrict volume A) ∧
              HasDerivAt (F := ℝ)
                (fun (t : ℝ) =>
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                    fun (y : Vec3) => G i t y)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                  fun (y : Vec3) => G' i (0 : ℝ) y)
                (0 : ℝ)) →
          HasDerivAt
            (fun (t : ℝ) =>
              (-@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                    fun (y : Vec3) => F₀ t y) +
                (2 : ℝ) *
                  ∑ i : Fin (3 : ℕ),
                    @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                      fun (y : Vec3) => G i t y)
            ((-@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                  fun (y : Vec3) => F₀' (0 : ℝ) y) +
              (2 : ℝ) *
                ∑ i : Fin (3 : ℕ),
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
                    fun (y : Vec3) => G' i (0 : ℝ) y)
            (0 : ℝ)
    := by
  intro H x₀ ρ hρ x j A z D F₀ F₀' hF₀deriv G G' hGderiv
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin 3)))
    (fun i hi => (hGderiv i).2)
  have hsum' := hsum.const_mul 2
  have hf := (hF₀deriv.2).neg
  convert hf.add hsum' using 1
  · funext t
    simp [Pi.add_apply]

private lemma smooth_harmonic_interior_gradient_bound_hF₀'zero_11 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
      let D : Vec3 → ℝ :=
        spatialLaplacian
          (eta x₀
            (by positivity : (0 : ℝ) < 4 * ρ / 3));
      let F₀' : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) =>
        H y * spatialDeriv newtonianKernel j (z t - y) * D y;
      ∀ y ∉ A, F₀' (0 : ℝ) y = (0 : ℝ)
    := by
  intro H x₀ ρ hρ x j A z D F₀' y hy
  dsimp [F₀', D]
  have hz := eta_laplacian_zero_off_annulus (R := 4 * ρ / 3)
    (by positivity) (by simpa [A] using hy)
  simp [hz]

private lemma smooth_harmonic_interior_gradient_bound_hF₀'full_12 :
    ∀ {H : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      MeasurableSet A →
        let z : ℝ → Vec3 := fun (t : ℝ) => x + t • basisVec j;
        let D : Vec3 → ℝ :=
          spatialLaplacian
            (eta x₀
              (by positivity : (0 : ℝ) < 4 * ρ / 3));
        let F₀' : ℝ → Vec3 → ℝ := fun (t : ℝ) (y : Vec3) =>
          H y * spatialDeriv newtonianKernel j (z t - y) * D y;
        (∀ y ∉ A, F₀' (0 : ℝ) y = (0 : ℝ)) →
          Eq (α := ℝ)
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace volume fun (y : Vec3) =>
              F₀' (0 : ℝ) y)
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume A)
              fun (y : Vec3) => F₀' (0 : ℝ) y)
    := by
  intro H x₀ ρ hρ x j A hAmeas z D F₀' hF₀'zero
  rw [← integral_indicator hAmeas]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ A
  · simp [hy]
  · simp [hy, hF₀'zero y hy]

private lemma smooth_harmonic_interior_gradient_bound_hkGzero_13 :
    ∀ {x₀ : Vec3} {ρ : ℝ} (hρ : (0 : ℝ) < ρ) (x : Vec (3 : ℕ)) (j : Fin (3 : ℕ)),
      let A : Set Vec3 := cutoffAnnulus x₀ ((4 : ℝ) * ρ / (3 : ℝ));
      let kG : Fin (3 : ℕ) → Vec3 → ℝ := fun (i : Fin (3 : ℕ)) (y : Vec3) =>
        -spatialDeriv (spatialDeriv newtonianKernel i) j (x - y) *
            spatialDeriv
              (eta x₀
                (by positivity : (0 : ℝ) < 4 * ρ / 3))
              i y +
          spatialDeriv newtonianKernel j (x - y) *
            spatialDeriv
              (spatialDeriv
                (eta x₀
                  (by positivity : (0 : ℝ) < 4 * ρ / 3))
                i)
              i y;
      ∀ (i : Fin (3 : ℕ)), ∀ y ∉ A, kG i y = (0 : ℝ)
    := by
  intro x₀ ρ hρ x j A kG i y hy
  have hz := eta_derivatives_zero_off_cutoff_annulus
    (hρ := (by positivity : 0 < (4 * ρ / 3 : ℝ)))
    (hy := by simpa [A] using hy) i i
  simp [kG, hz.1, hz.2]

theorem smooth_harmonic_interior_gradient_bound
    {H : Vec3 → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ)
    (hHarm : ∀ y ∈ euclideanBall x₀ ρ,
      CKN.spatialLaplacian H y = 0)
    (hHmem : MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ))) :
    ∀ x ∈ euclideanBall x₀ (ρ / 2), ∀ j : Fin 3,
      |CKN.spatialDeriv H j x| ≤ harmonicInteriorGradientSupConstant *
        (ρ ^ 3)⁻¹ * lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
  intro x hx j
  let A : Set Vec3 := cutoffAnnulus x₀ (4 * ρ / 3)
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact cutoffAnnulus_measurable (by positivity)
  have hAsub : A ⊆ euclideanBall x₀ ρ := by
    dsimp [A]
    exact cutoffAnnulus_subset_outer_ball hρ
  have hAvol := @smooth_harmonic_interior_gradient_bound_hAvol_1 x₀ ρ hρ hAsub
  let _ : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAvol
  have hxinner : x ∈ euclideanBall x₀ (13 * (4 * ρ / 3) / 20) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx
    exact hx'.trans (by nlinarith only [hρ])
  have hH_A : MemLp H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict A) :=
    hHmem.mono_measure (Measure.restrict_mono_set volume hAsub)
  have hHlp_mono : lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict A) ≤ lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall x₀ ρ)) := by
    rw [← MeasureTheory.toReal_eLpNorm, ← MeasureTheory.toReal_eLpNorm]
    apply ENNReal.toReal_mono hHmem.eLpNorm_lt_top.ne
    exact eLpNorm_mono_measure H (Measure.restrict_mono_set volume hAsub)
  let z : ℝ → Vec3 := fun t => x + t • CKN.basisVec j
  let S : Set ℝ := z ⁻¹' euclideanBall x₀ (ρ / 2)
  have hinner_open : IsOpen (euclideanBall x₀ (ρ / 2)) := by
    change IsOpen {y : Vec3 | euclideanSqDist y x₀ < (ρ / 2) ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hS : S ∈ 𝓝 (0 : ℝ) := by
    apply (hinner_open.preimage (by fun_prop)).mem_nhds
    simpa [S, z] using hx
  have hzt_inner : ∀ t ∈ S, z t ∈ euclideanBall x₀ (ρ / 2) := by
    intro t ht
    exact ht
  let D : Vec3 → ℝ := CKN.spatialLaplacian
    (eta (ρ := 4 * ρ / 3) x₀ (by positivity))
  have hDcont : Continuous D := by
    simpa [D, eta] using
      (CKN.contDiff_spatialLaplacian_smooth
        (mollifiedBallCutoff_smooth x₀ (by positivity))).continuous
  have hDsupport : HasCompactSupport D := by
    apply laplacian_compact_support_global
    simpa only [eta] using mollifiedBallCutoff_hasCompactSupport x₀ (by positivity)
  have hHDcont : Continuous (fun y : Vec3 => H y * D y) := hH.continuous.mul hDcont
  have hHDsupport : HasCompactSupport (fun y : Vec3 => H y * D y) := by
    change HasCompactSupport (H * D)
    exact hDsupport.mul_left
  let F₀ : ℝ → Vec3 → ℝ := fun t y =>
    H y * newtonianKernel (z t - y) * D y
  let F₀' : ℝ → Vec3 → ℝ := fun t y =>
    H y * CKN.spatialDeriv newtonianKernel j (z t - y) * D y
  have hF₀full := @smooth_harmonic_interior_gradient_bound_hF₀full_2 H x₀ ρ hρ x j hHDcont
    hHDsupport
  have hF₀int : Integrable (F₀ 0) (volume.restrict A) :=
    (hF₀full 0).mono_measure Measure.restrict_le_self
  have hF₀meas : ∀ᶠ t in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (F₀ t) (volume.restrict A) :=
    Filter.Eventually.of_forall fun t =>
      (hF₀full t).mono_measure Measure.restrict_le_self |>.aestronglyMeasurable
  have hF₀'cont := @smooth_harmonic_interior_gradient_bound_hF₀'cont_1 H hH x₀ ρ hρ x hx j hDcont
  have hF₀'meas : AEStronglyMeasurable (F₀' 0)
      (volume.restrict A) := hF₀'cont.aestronglyMeasurable hAmeas
  have hHabsInt : Integrable (fun y : Vec3 => |H y|)
      (volume.restrict A) := by
    have h := (hH_A.norm.mono_exponent (by norm_num : ENNReal.ofReal (1 : ℝ) ≤
      ENNReal.ofReal (3 / 2 : ℝ))).integrable (by norm_num)
    simpa only [Real.norm_eq_abs] using h
  have hsource_bound_int : Integrable (fun y : Vec3 =>
      harmonicInteriorSourceGradientConstant * (ρ ^ 4)⁻¹ * |H y|)
      (volume.restrict A) := by
    exact (hHabsInt.const_mul
      (harmonicInteriorSourceGradientConstant * (ρ ^ 4)⁻¹))
  have hF₀'bound := @smooth_harmonic_interior_gradient_bound_hF₀'bound_2 H x₀ ρ hρ x j hAmeas
    hzt_inner
  have hF₀'diff := @smooth_harmonic_interior_gradient_bound_hF₀'diff_3 H x₀ ρ hρ x j hAmeas
    hzt_inner
  have hF₀deriv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict A) hS hF₀meas hF₀int hF₀'meas
      hF₀'bound hsource_bound_int hF₀'diff
  let G : Fin 3 → ℝ → Vec3 → ℝ := fun i t y =>
    H y * CKN.spatialDeriv (kernelCutoffDerivative (ρ := 4 * ρ / 3)
      (z t) x₀ (by positivity) i) i y
  let G' : Fin 3 → ℝ → Vec3 → ℝ := fun i t y =>
    H y * (-CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j
        (z t - y) * CKN.spatialDeriv
          (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y +
      CKN.spatialDeriv newtonianKernel j (z t - y) *
        CKN.spatialDeriv (CKN.spatialDeriv
          (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i y)
  have hGdiff := @smooth_harmonic_interior_gradient_bound_hGdiff_4 H x₀ ρ hρ x j hAmeas hzt_inner
  have hGmeas := @smooth_harmonic_interior_gradient_bound_hGmeas_5 H hH x₀ ρ hρ x j hS hzt_inner
  have hGint := @smooth_harmonic_interior_gradient_bound_hGint_3 H hH x₀ ρ hρ x j hxinner
  have hG'cont := @smooth_harmonic_interior_gradient_bound_hG'cont_6 H hH x₀ ρ hρ x hx j
  have hG'meas : ∀ i : Fin 3, AEStronglyMeasurable (G' i 0)
      (volume.restrict A) := by
    intro i
    exact (hG'cont i).aestronglyMeasurable hAmeas
  have hGbound := @smooth_harmonic_interior_gradient_bound_hGbound_7 H x₀ ρ hρ x j hAmeas hzt_inner
  have hG'bound_int : Integrable (fun y : Vec3 =>
      harmonicInteriorKernelXGradientConstant * (ρ ^ 4)⁻¹ * |H y|)
      (volume.restrict A) := hHabsInt.const_mul
        (harmonicInteriorKernelXGradientConstant * (ρ ^ 4)⁻¹)
  have hGderiv : ∀ i : Fin 3, Integrable (G' i 0) (volume.restrict A) ∧
      HasDerivAt (fun t => ∫ y in A, G i t y) (∫ y in A, G' i 0 y) 0 := by
    intro i
    exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict A) hS (hGmeas i) (hGint i) (hG'meas i)
        (hGbound i) hG'bound_int (hGdiff i)
  have hF₀zero := @smooth_harmonic_interior_gradient_bound_hF₀zero_4 H x₀ ρ hρ x j
  have hGzero := @smooth_harmonic_interior_gradient_bound_hGzero_5 H x₀ ρ hρ x j hzt_inner
  have hF₀restrict := @smooth_harmonic_interior_gradient_bound_hF₀restrict_6 H x₀ ρ hρ x j hAmeas
    hF₀zero
  have hGrestrict := @smooth_harmonic_interior_gradient_bound_hGrestrict_7 H x₀ ρ hρ x j hAmeas
    hGzero
  have hrep_t := @smooth_harmonic_interior_gradient_bound_hrep_t_8 H hH x₀ ρ hρ hHarm x j
    hzt_inner hF₀restrict hGrestrict
  have hline := @smooth_harmonic_interior_gradient_bound_hline_8 x j
  have hleft := @smooth_harmonic_interior_gradient_bound_hleft_9 H hH x j hline
  have hright := @smooth_harmonic_interior_gradient_bound_hright_10 H x₀ ρ hρ x j hF₀deriv hGderiv
  have hevent : (fun t => H (z t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => (-∫ y in A, F₀ t y) + 2 * ∑ i : Fin 3, ∫ y in A, G i t y) := by
    filter_upwards [hS] with t ht
    exact hrep_t t ht
  have hcoord : CKN.spatialDeriv H j x =
      (-∫ y in A, F₀' 0 y) + 2 * ∑ i : Fin 3, ∫ y in A, G' i 0 y := by
    exact (hleft.congr_of_eventuallyEq hevent.symm).unique hright
  have kernel_lp_bound := @smooth_harmonic_interior_gradient_bound_kernel_lp_bound_9 x₀ ρ hρ
    hAmeas hAsub hAvol
  let k₀' : Vec3 → ℝ := fun y =>
    CKN.spatialDeriv newtonianKernel j (x - y) * D y
  have hk₀'cont := @smooth_harmonic_interior_gradient_bound_hk₀'cont_10 x₀ ρ hρ x hx j hDcont
  have hk₀'bound : ∀ y ∈ A, |k₀' y| ≤
      harmonicInteriorSourceGradientConstant * (ρ ^ 4)⁻¹ := by
    intro y hy
    exact source_kernel_spatialDeriv_bound_scaled hρ hx hy j
  have hk₀'data := kernel_lp_bound hk₀'cont
    (mul_nonneg harmonicInteriorSourceGradientConstant_nonneg (by positivity))
    hk₀'bound
  have hF₀'zero := @smooth_harmonic_interior_gradient_bound_hF₀'zero_11 H x₀ ρ hρ x j
  have hF₀'full := @smooth_harmonic_interior_gradient_bound_hF₀'full_12 H x₀ ρ hρ x j hAmeas
    hF₀'zero
  have hsource_deriv_bound := @smooth_harmonic_interior_gradient_bound_hsource_deriv_bound_11 H x₀
    ρ hρ x j hAmeas hAvol hH_A hHlp_mono hk₀'data
  let kG : Fin 3 → Vec3 → ℝ := fun i y =>
    -CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j (x - y) *
        CKN.spatialDeriv (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i y +
      CKN.spatialDeriv newtonianKernel j (x - y) *
        CKN.spatialDeriv (CKN.spatialDeriv
          (eta (ρ := 4 * ρ / 3) x₀ (by positivity)) i) i y
  have hkGcont := @smooth_harmonic_interior_gradient_bound_hkGcont_12 x₀ ρ hρ x hx j
  have hkGbound : ∀ i y, y ∈ A → |kG i y| ≤
      harmonicInteriorKernelXGradientConstant * (ρ ^ 4)⁻¹ := by
    intro i y hy
    exact kernel_cutoff_x_derivative_bound_scaled hρ hx hy i j
  have hkGdata : ∀ i : Fin 3, MemLp (kG i) (ENNReal.ofReal (3 : ℝ))
      (volume.restrict A) ∧ lpNorm (kG i) (ENNReal.ofReal (3 : ℝ))
        (volume.restrict A) ≤ harmonicInteriorKernelXGradientConstant *
          (ρ ^ 4)⁻¹ * (ρ * (Real.pi * 4 / 3) ^ (1 / (3 : ℝ))) := by
    intro i
    exact kernel_lp_bound (hkGcont i)
      (mul_nonneg harmonicInteriorKernelXGradientConstant_nonneg (by positivity))
      (fun y hy => hkGbound i y hy)
  have hkGzero := @smooth_harmonic_interior_gradient_bound_hkGzero_13 x₀ ρ hρ x j
  have hG_deriv_bound := @smooth_harmonic_interior_gradient_bound_hG_deriv_bound_13 H x₀ ρ hρ x j
    hAmeas hAvol hH_A hHlp_mono hkGdata hkGzero
  have hsumG := @smooth_harmonic_interior_gradient_bound_hsumG_14 H x₀ ρ hρ x j hG_deriv_bound
  rw [hcoord]
  calc
    |(-∫ y in A, F₀' 0 y) + 2 * ∑ i : Fin 3, ∫ y in A, G' i 0 y| ≤
        |∫ y in A, F₀' 0 y| + |2 * ∑ i : Fin 3, ∫ y in A, G' i 0 y| := by
      calc
        _ ≤ |-(∫ y in A, F₀' 0 y)| +
            |2 * ∑ i : Fin 3, ∫ y in A, G' i 0 y| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    _ ≤ harmonicInteriorGradientSupConstant * (ρ ^ 3)⁻¹ *
        lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall x₀ ρ)) := by
      rw [show harmonicInteriorGradientSupConstant =
        (Real.pi * 4 / 3) ^ (1 / (3 : ℝ)) *
          (harmonicInteriorSourceGradientConstant +
            6 * harmonicInteriorKernelXGradientConstant) by rfl]
      exact (add_le_add hsource_deriv_bound hsumG).trans_eq (by ring)

end CKN.Foundation.Heat
