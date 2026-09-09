/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanMollifierLimit
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCalculus
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicLaplacian
import LeanPool.NavierStokesAndEuler.Euler.MeanHarmonicScaling

/-! Differentiating an actual compact mollifier transfers the distributional Laplacian to the
kernel. -/

@[expose] public section


noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
open scoped ContDiff Convolution

theorem partialDerivative_convolution_right (f g : Space → ℝ)
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (i : Fin 3) :
    partialDerivative (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) i =
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] partialDerivative g i := by
  funext x
  unfold partialDerivative
  rw [(hgc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf
    (hg.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hf (hgc.fderiv ℝ)
    (hg.fderiv_right (m := ∞) (by simp)).continuous x (EuclideanSpace.single i 1)

/-- Two genuine differentiations under the compact-kernel convolution integral. -/
theorem laplacian_convolution_right (f g : Space → ℝ)
    (hf : LocallyIntegrable f volume) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    Δ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Δ g := by
  have hc : ContDiff ℝ ∞ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) :=
    hgc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hg
  have hd (i : Fin 3) : ContDiff ℝ ∞ (partialDerivative g i) :=
    contDiff_partialDerivative g hg i
  have hdc (i : Fin 3) : HasCompactSupport (partialDerivative g i) :=
    hgc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  funext x
  rw [laplacian_eq_coordinate_sum _ hc]
  simp_rw [partialDerivative_convolution_right f g hf hg hgc,
    partialDerivative_convolution_right f _ hf (hd _) (hdc _)]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  simp_rw [laplacian_eq_coordinate_sum g hg, Finset.mul_sum]
  have hi (i : Fin 3) : Integrable
      (fun y => f y * partialDerivative (partialDerivative g i) i (x-y)) volume :=
    ((hdc i).fderiv_apply ℝ (EuclideanSpace.single i 1)).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hf (contDiff_partialDerivative _ (hd i) i).continuous x
  exact (integral_finsetSum Finset.univ (fun i _ => hi i)).symm

theorem laplacian_comp_add_left (g : Space → ℝ) (a x : Space) :
    Δ (fun y => g (a+y)) x = Δ g (a+x) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 3) ℝ),
    laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_comp_add_left]

/-- Reflection contributes two minus signs to the scalar Laplacian. -/
theorem laplacian_comp_const_sub (g : Space → ℝ) (hg : ContDiff ℝ ∞ g) (a x : Space) :
    Δ (fun y => g (a-y)) x = Δ g (a-x) := by
  have h := laplacian_comp_const_smul (fun y => g (a+y))
    (hg.comp (contDiff_const.add contDiff_id)) (-1) x
  rw [laplacian_comp_add_left] at h
  simpa only [neg_one_smul, neg_one_sq, one_mul, sub_eq_add_neg] using h

/-- A compact kernel contained in the weak-harmonic region produces a classical harmonic value. -/
theorem convolution_harmonic_at (U : Set Space) (f g : Space → ℝ)
    (hf : LocallyIntegrable f volume) (hh : ScalarWeakHarmonicOn U f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (x : Space)
    (hsupport : tsupport (fun y => g (x - y)) ⊆ U) :
    Δ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = 0 := by
  rw [laplacian_convolution_right f g hf hg hgc, convolution_def]
  change (∫ y, f y * Δ g (x-y)) = 0
  have hc : HasCompactSupport (fun y => g (x-y)) :=
    hgc.comp_homeomorph (Homeomorph.subLeft x)
  have hs : ContDiff ℝ ∞ (fun y => g (x-y)) :=
    hg.comp (contDiff_const.sub contDiff_id)
  have H := hh (fun y => g (x-y)) hc hs hsupport
  simpa only [laplacian_comp_const_sub g hg] using H

theorem normed_reflected_support (φ : ContDiffBump (0 : Space)) (x : Space) :
    tsupport (fun y => φ.normed volume (x-y)) ⊆ Metric.closedBall x φ.rOut := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro y hy
  have hnorm : ‖x-y‖ < φ.rOut := by
    have hy' : x-y ∈ Function.support (φ.normed (volume : Measure Space)) := hy
    simpa only [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] using hy'
  change ‖y-x‖ ≤ φ.rOut
  rw [norm_sub_rev]
  exact hnorm.le

/-- Actual compact mollification turns weak harmonicity into classical harmonicity in the interior.
-/
theorem scalarMollification_harmonic (φ : ContDiffBump (0 : Space))
    (f : Space → ℝ) (hf : MemLp f 2 volume)
    (hh : ScalarWeakHarmonicOn (Metric.ball (0 : Space) 1) f)
    (hr : φ.rOut ≤ 1 / 4) :
    ∀ x ∈ Metric.ball (0 : Space) (1/2 : ℝ), Δ (scalarMollification φ f) x = 0 := by
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm b a
  have heq := convolution_flip (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure Space)) (f := f) (g := φ.normed volume)
  rw [hflip] at heq
  change ∀ x ∈ Metric.ball (0 : Space) (1/2 : ℝ),
    Δ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x = 0
  rw [heq]
  intro x hx
  apply convolution_harmonic_at (Metric.ball (0 : Space) 1) f (φ.normed volume)
    (hf.locallyIntegrable (by norm_num)) hh φ.contDiff_normed φ.hasCompactSupport_normed x
  intro y hy
  have hd := normed_reflected_support φ x hy
  have htriangle := dist_triangle y x (0 : Space)
  simp only [Metric.mem_ball, Metric.mem_closedBall, dist_zero_right] at hx hd htriangle ⊢
  linarith

theorem interiorMollifier_harmonic (f : Space → ℝ) (hf : MemLp f 2 volume)
    (hh : ScalarWeakHarmonicOn (Metric.ball (0 : Space) 1) f) (n : ℕ) :
    ∀ x ∈ Metric.ball (0 : Space) (1/2 : ℝ),
      Δ (scalarMollification (interiorMollifier n) f) x = 0 :=
  scalarMollification_harmonic (interiorMollifier n) f hf hh (interiorMollifier_rOut_le n)

end EulerMeanHarmonic
