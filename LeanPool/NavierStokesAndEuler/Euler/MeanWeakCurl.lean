/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSolenoidalSpace
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public section

/-! The ordinary closed L² gradient space has zero distributional curl.
For smooth representatives this gives actual pointwise symmetry of the derivative. -/

noncomputable section

namespace EulerMeanPressure

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus EulerMeanSolenoidal
open scoped ContDiff

theorem scalar_test_ibp (f ψ : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (i : Fin 3) :
    (∫ x, partialDerivative f i x * ψ x) = -∫ x, f x * partialDerivative ψ i x := by
  have hi₁ : Integrable (fun x => partialDerivative f i x * ψ x) :=
    ((contDiff_partialDerivative f hf i).continuous.mul
      hψ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have hi₂ : Integrable (fun x => f x * partialDerivative ψ i x) :=
    (hf.continuous.mul (contDiff_partialDerivative ψ hψ
      i).continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_left
  have hi₀ : Integrable (fun x => f x * ψ x) :=
    (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Space)) (v := EuclideanSpace.single i 1) hi₁ hi₂ hi₀
    (fun x _ => (hf.differentiable (by simp)).differentiableAt)
    (fun x _ => (hψ.differentiable (by simp)).differentiableAt)
  change (∫ x, f x * partialDerivative ψ i x) =
    -∫ x, partialDerivative f i x * ψ x at h
  linarith

def skewTest (i j : Fin 3) (ψ : Space → ℝ) (x : Space) : Space :=
  partialDerivative ψ j x • EuclideanSpace.single i 1 -
    partialDerivative ψ i x • EuclideanSpace.single j 1

theorem skewTest_smooth (i j : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (skewTest i j ψ) :=
  ((contDiff_partialDerivative ψ hψ j).smul contDiff_const).sub
    ((contDiff_partialDerivative ψ hψ i).smul contDiff_const)

theorem skewTest_compact (i j : Fin 3) (ψ : Space → ℝ) (hc : HasCompactSupport ψ) :
    HasCompactSupport (skewTest i j ψ) := by
  apply HasCompactSupport.intro hc
  intro x hx
  simp only [skewTest, partialDerivative, fderiv_of_notMem_tsupport ℝ hx,
    zero_apply, zero_smul, sub_self]

theorem skewTest_inner (i j : Fin 3) (ψ : Space → ℝ) (x v : Space) :
    ⟪v, skewTest i j ψ x⟫_ℝ = v i * partialDerivative ψ j x - v j * partialDerivative ψ i x := by
  simp only [skewTest, inner_sub_right, inner_smul_right,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul]
  ring

theorem gradient_coordinate (φ : Space → ℝ) (x : Space) (i : Fin 3) :
    gradient φ x i = partialDerivative φ i x := by
  simpa only [EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real, partialDerivative]
    using (inner_gradient_left (f := φ) (x := x) (y := EuclideanSpace.single i 1))

theorem gradient_skewTest_integral (i j : Fin 3) (φ ψ : Space → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ x, ⟪gradient φ x, skewTest i j ψ x⟫_ℝ) = 0 := by
  have hi (a b : Fin 3) : Integrable (fun x => partialDerivative φ a x * partialDerivative ψ b x) :=
    ((contDiff_partialDerivative φ hφ a).continuous.mul
      (contDiff_partialDerivative ψ hψ b).continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (EuclideanSpace.single b 1)).mul_left
  simp_rw [skewTest_inner, gradient_coordinate]
  rw [integral_sub (hi i j) (hi j i),
    scalar_test_ibp φ (partialDerivative ψ j) hφ (contDiff_partialDerivative ψ hψ j)
      (hc.fderiv_apply ℝ (EuclideanSpace.single j 1)) i,
    scalar_test_ibp φ (partialDerivative ψ i) hφ (contDiff_partialDerivative ψ hψ i)
      (hc.fderiv_apply ℝ (EuclideanSpace.single i 1)) j]
  simp_rw [partialDerivative_comm ψ (hψ.of_le (by simp)) j i]
  exact sub_self _

def skewTestLp (i j : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) : L2 :=
  ((skewTest_smooth i j ψ hψ).continuous.memLp_of_hasCompactSupport
    (skewTest_compact i j ψ hc)).toLp (skewTest i j ψ)

theorem skewTestLp_ae (i j : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) : skewTestLp i j ψ hψ hc =ᵐ[volume] skewTest i j ψ :=
  MemLp.coeFn_toLp _

theorem skewTestLp_solenoidal (i j : Fin 3) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    skewTestLp i j ψ hψ hc ∈ solenoidalSpace := by
  apply (mem_solenoidal_iff _).2
  intro φ _ hφ
  calc
    (∫ x, ⟪gradient φ x, skewTestLp i j ψ hψ hc x⟫_ℝ) =
        ∫ x, ⟪gradient φ x, skewTest i j ψ x⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [skewTestLp_ae i j ψ hψ hc] with x hx
      rw [hx]
    _ = 0 := gradient_skewTest_integral i j φ ψ hφ hψ hc

theorem gradientSpace_weak_curl_zero (p : L2) (hp : p ∈ gradientSpace)
    (i j : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ x, p x i * partialDerivative ψ j x - p x j * partialDerivative ψ i x) = 0 := by
  have h := pressure_pairing_zero hp (skewTestLp_solenoidal i j ψ hψ hc)
  rw [MeasureTheory.L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [skewTestLp_ae i j ψ hψ hc] with x hx
  rw [hx, skewTest_inner]

/-- The distributional statement becomes the actual classical closedness identity. -/
theorem gradientSpace_classical_curl_zero (p : L2) (hp : p ∈ gradientSpace)
    (g : Space → Space) (hrep : p =ᵐ[volume] g) (hg : ContDiff ℝ ∞ g) :
    ∀ x i j, (fderiv ℝ g x (EuclideanSpace.single i 1)) j =
      (fderiv ℝ g x (EuclideanSpace.single j 1)) i := by
  intro x i j
  let gi : Space → ℝ := fun y => g y i
  let gj : Space → ℝ := fun y => g y j
  have hgi : ContDiff ℝ ∞ gi := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hg
  have hgj : ContDiff ℝ ∞ gj := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hg
  let q : Space → ℝ := fun y => partialDerivative gi j y - partialDerivative gj i y
  have hqa := contDiff_partialDerivative gi hgi j
  have hqb := contDiff_partialDerivative gj hgj i
  have hq : ContDiff ℝ ∞ q := hqa.sub hqb
  have hz : q =ᵐ[volume] 0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hq.continuous.locallyIntegrable (fun ψ hψ hc => by
      have hw := gradientSpace_weak_curl_zero p hp i j ψ hψ hc
      have hw' : (∫ y, gi y * partialDerivative ψ j y - gj y * partialDerivative ψ i y) = 0 := by
        rw [← hw]
        apply integral_congr_ae
        filter_upwards [hrep] with y hy
        rw [hy]
      have hIa : Integrable (fun y => gi y * partialDerivative ψ j y) :=
        (hgi.continuous.mul (contDiff_partialDerivative ψ hψ
          j).continuous).integrable_of_hasCompactSupport
          (hc.fderiv_apply ℝ (EuclideanSpace.single j 1)).mul_left
      have hIb : Integrable (fun y => gj y * partialDerivative ψ i y) :=
        (hgj.continuous.mul (contDiff_partialDerivative ψ hψ
          i).continuous).integrable_of_hasCompactSupport
          (hc.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_left
      have hJa : Integrable (fun y => partialDerivative gi j y * ψ y) :=
        (hqa.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
      have hJb : Integrable (fun y => partialDerivative gj i y * ψ y) :=
        (hqb.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
      rw [integral_sub hIa hIb] at hw'
      have ha := scalar_test_ibp gi ψ hgi hψ hc j
      have hb := scalar_test_ibp gj ψ hgj hψ hc i
      change (∫ y, ψ y * (partialDerivative gi j y - partialDerivative gj i y)) = 0
      simp_rw [mul_comm (ψ _), sub_mul]
      rw [integral_sub hJa hJb]
      linarith)
  have hzero := congrFun (MeasureTheory.Measure.eq_of_ae_eq hz hq.continuous continuous_const) x
  change partialDerivative gi j x - partialDerivative gj i x = 0 at hzero
  dsimp [partialDerivative, gi, gj] at hzero
  rw [fderiv_coordinate g x (hg.differentiable (by simp)).differentiableAt,
    fderiv_coordinate g x (hg.differentiable (by simp)).differentiableAt] at hzero
  exact (sub_eq_zero.mp hzero).symm

end EulerMeanPressure
