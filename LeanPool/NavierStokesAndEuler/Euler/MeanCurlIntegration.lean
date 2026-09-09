/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities

@[expose] public section

/-! Classical integration by parts and its extension to the actual homogeneous gradient space. -/

noncomputable section

namespace EulerMeanCurlIntegration

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanCutoffCurl EulerMeanGradientTest EulerMeanVectorIdentities
  EulerMeanCurlTensor
open scoped ContDiff

def partialTest (f : Test) (i : Fin 3) : Test :=
  ⟨vectorPartial (f : Space → Space) i, vectorPartial_smooth f f.smooth i,
    vectorPartial_compact f f.compact i⟩

theorem test_memLp (f : Test) : MemLp (f : Space → Space) 2 volume :=
  f.smooth.continuous.memLp_of_hasCompactSupport f.compact

def testValue (f : Test) : L2 := (test_memLp f).toLp (f : Space → Space)

theorem testValue_ae (f : Test) : testValue f =ᵐ[volume] (f : Space → Space) :=
  (test_memLp f).coeFn_toLp

theorem test_inner_integrable (f g : Test) :
    Integrable (fun x => ⟪(f : Space → Space) x, (g : Space → Space) x⟫_ℝ) :=
  (f.smooth.continuous.inner g.smooth.continuous).integrable_of_hasCompactSupport
    (f.compact.comp₂_left g.compact (inner_zero_left (0 : Space)))

theorem test_inner_eq_integral (f g : Test) :
    ⟪testValue f, testValue g⟫_ℝ = ∫ x, ⟪(f : Space → Space) x, (g : Space → Space) x⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testValue_ae f, testValue_ae g] with x hf hg
  rw [hf, hg]

theorem directional_integration_by_parts (f g : Test) (i : Fin 3) :
    (∫ x, ⟪vectorPartial (f : Space → Space) i x, (g : Space → Space) x⟫_ℝ) =
      -∫ x, ⟪(f : Space → Space) x, vectorPartial (g : Space → Space) i x⟫_ℝ := by
  have h := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := (volume : Measure Space)) (B := innerSL ℝ) (v := EuclideanSpace.single i 1)
    (test_inner_integrable (partialTest f i) g)
    (test_inner_integrable f (partialTest g i)) (test_inner_integrable f g)
    (fun x _ => (f.smooth.differentiable (by simp)).differentiableAt)
    (fun x _ => (g.smooth.differentiable (by simp)).differentiableAt)
  change (∫ x, ⟪(f : Space → Space) x, vectorPartial (g : Space → Space) i x⟫_ℝ) =
    -∫ x, ⟪vectorPartial (f : Space → Space) i x, (g : Space → Space) x⟫_ℝ at h
  linarith

/-- The actual tensor inner product has the usual distributional Laplacian formula. -/
theorem testGradient_pairing (f g : Test) :
    ⟪EulerMeanGradientTest.testGradient f, EulerMeanGradientTest.testGradient g⟫_ℝ =
      -∫ x, ⟪(f : Space → Space) x, Δ (g : Space → Space) x⟫_ℝ := by
  rw [PiLp.inner_apply]
  calc
    _ = ∑ i : Fin 3, ∫ x,
        ⟪vectorPartial (f : Space → Space) i x, vectorPartial (g : Space → Space) i x⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [testGradient_apply, testGradient_apply, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [derivativeColumn_ae f i, derivativeColumn_ae g i] with x hf hg
      rw [hf, hg]
      rfl
    _ = ∑ i : Fin 3, -∫ x,
        ⟪(f : Space → Space) x, vectorPartial (vectorPartial (g : Space → Space) i) i x⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i _
      exact directional_integration_by_parts f (partialTest g i) i
    _ = _ := by
      rw [vector_laplacian_eq_sum (g : Space → Space) g.smooth]
      simp_rw [inner_sum]
      have hsum := integral_finsetSum Finset.univ
        (fun (i : Fin 3) _ => test_inner_integrable f (partialTest (partialTest g i) i))
      change (∫ x, ∑ i : Fin 3, ⟪(f : Space → Space) x,
        vectorPartial (vectorPartial (g : Space → Space) i) i x⟫_ℝ) = _ at hsum
      rw [hsum]
      simp only [Finset.sum_neg_distrib]
      rfl

theorem scalar_partial_ibp (f g : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (i : Fin 3) :
    (∫ x, partialDerivative f i x * g x) = -∫ x, f x * partialDerivative g i x := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Space)) (v := EuclideanSpace.single i 1)
    (((contDiff_partialDerivative f hf i).continuous.mul
      hg.continuous).integrable_of_hasCompactSupport
      ((hfc.fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_right))
    ((hf.continuous.mul (contDiff_partialDerivative g hg
      i).continuous).integrable_of_hasCompactSupport
      hfc.mul_right)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left)
    (fun x _ => (hf.differentiable (by simp)).differentiableAt)
    (fun x _ => (hg.differentiable (by simp)).differentiableAt)
  change (∫ x, f x * partialDerivative g i x) = -∫ x, partialDerivative f i x * g x at h
  linarith

theorem integral_three_sub (a b c d e f : Space → ℝ)
    (ha : Integrable a) (hb : Integrable b) (hc : Integrable c)
    (hd : Integrable d) (he : Integrable e) (hf : Integrable f) :
    (∫ x, (a x - b x) + (c x - d x) + (e x - f x)) =
      ((∫ x, a x) - ∫ x, b x) + ((∫ x, c x) - ∫ x, d x) +
        ((∫ x, e x) - ∫ x, f x) := by
  have h₁ := integral_add ((ha.sub hb).add (hc.sub hd)) (he.sub hf)
  have h₂ := integral_add (ha.sub hb) (hc.sub hd)
  simp only [Pi.add_apply, Pi.sub_apply] at h₁ h₂
  rw [h₁, h₂, integral_sub ha hb, integral_sub hc hd, integral_sub he hf]

/-- The ordinary real curl is formally self-adjoint on compact smooth vector tests. -/
theorem integral_curl_selfadjoint (f g : Test) :
    (∫ x, ⟪vectorCurl (f : Space → Space) x, (g : Space → Space) x⟫_ℝ) =
      ∫ x, ⟪(f : Space → Space) x, vectorCurl (g : Space → Space) x⟫_ℝ := by
  let fc (a : Fin 3) (x : Space) := (f : Space → Space) x a
  let gc (a : Fin 3) (x : Space) := (g : Space → Space) x a
  have hfs (a : Fin 3) : ContDiff ℝ ∞ (fc a) := (contDiff_piLp 2).mp f.smooth a
  have hgs (a : Fin 3) : ContDiff ℝ ∞ (gc a) := (contDiff_piLp 2).mp g.smooth a
  have hfc (a : Fin 3) : HasCompactSupport (fc a) :=
    f.compact.comp_left (g := fun v : Space => v a) rfl
  have hgc (a : Fin 3) : HasCompactSupport (gc a) :=
    g.compact.comp_left (g := fun v : Space => v a) rfl
  have hl (a b i : Fin 3) : Integrable (fun x => partialDerivative (fc a) i x * gc b x) :=
    ((contDiff_partialDerivative _ (hfs a) i).continuous.mul (hgs
      b).continuous).integrable_of_hasCompactSupport
      ((hfc a).fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_right
  have hr (a b i : Fin 3) : Integrable (fun x => fc a x * partialDerivative (gc b) i x) :=
    ((hfs a).continuous.mul (contDiff_partialDerivative _ (hgs b)
      i).continuous).integrable_of_hasCompactSupport
      (hfc a).mul_right
  have hleft (x : Space) : ⟪vectorCurl (f : Space → Space) x, (g : Space → Space) x⟫_ℝ =
      (partialDerivative (fc 2) 1 x * gc 0 x - partialDerivative (fc 1) 2 x * gc 0 x) +
      (partialDerivative (fc 0) 2 x * gc 1 x - partialDerivative (fc 2) 0 x * gc 1 x) +
      (partialDerivative (fc 1) 0 x * gc 2 x - partialDerivative (fc 0) 1 x * gc 2 x) := by
    simp only [PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three, vectorCurl, curl_apply]
    change (partialDerivative (fc 2) 1 x - partialDerivative (fc 1) 2 x) * gc 0 x +
      (partialDerivative (fc 0) 2 x - partialDerivative (fc 2) 0 x) * gc 1 x +
      (partialDerivative (fc 1) 0 x - partialDerivative (fc 0) 1 x) * gc 2 x = _
    ring
  have hright (x : Space) : ⟪(f : Space → Space) x, vectorCurl (g : Space → Space) x⟫_ℝ =
      (fc 0 x * partialDerivative (gc 2) 1 x - fc 0 x * partialDerivative (gc 1) 2 x) +
      (fc 1 x * partialDerivative (gc 0) 2 x - fc 1 x * partialDerivative (gc 2) 0 x) +
      (fc 2 x * partialDerivative (gc 1) 0 x - fc 2 x * partialDerivative (gc 0) 1 x) := by
    simp only [PiLp.inner_apply, Real.inner_apply, Fin.sum_univ_three, vectorCurl, curl_apply]
    change fc 0 x * (partialDerivative (gc 2) 1 x - partialDerivative (gc 1) 2 x) +
      fc 1 x * (partialDerivative (gc 0) 2 x - partialDerivative (gc 2) 0 x) +
      fc 2 x * (partialDerivative (gc 1) 0 x - partialDerivative (gc 0) 1 x) = _
    ring
  simp_rw [hleft, hright]
  rw [integral_three_sub _ _ _ _ _ _ (hl 2 0 1) (hl 1 0 2) (hl 0 1 2)
      (hl 2 1 0) (hl 1 2 0) (hl 0 2 1),
    integral_three_sub _ _ _ _ _ _ (hr 0 2 1) (hr 0 1 2) (hr 1 0 2)
      (hr 1 2 0) (hr 2 1 0) (hr 2 0 1)]
  simp_rw [scalar_partial_ibp _ _ (hfs _) (hgs _) (hfc _) (hgc _)]
  ring

theorem curlTensor_test_eq (f : Test) :
    curlTensor (EulerMeanGradientTest.testGradient f) = testValue (curlTest f) := by
  apply Lp.ext
  exact (curlTensor_test_ae f).trans (testValue_ae (curlTest f)).symm

theorem test_gradient_curl_pairing (f g : Test) :
    ⟪EulerMeanGradientTest.testGradient f, EulerMeanGradientTest.testGradient (curlTest g)⟫_ℝ =
      -⟪curlTensor (EulerMeanGradientTest.testGradient f), testValue (laplacianTest g)⟫_ℝ := by
  rw [testGradient_pairing, curlTensor_test_eq, test_inner_eq_integral]
  change -(∫ x, ⟪(f : Space → Space) x, Δ (vectorCurl (g : Space → Space)) x⟫_ℝ) =
    -∫ x, ⟪vectorCurl (f : Space → Space) x, Δ (g : Space → Space) x⟫_ℝ
  rw [laplacian_vectorCurl (g : Space → Space) g.smooth]
  exact congrArg Neg.neg (integral_curl_selfadjoint f (laplacianTest g)).symm

/-- Distributional integration by parts survives passage to the closed homogeneous gradient space. -/
theorem homogeneous_curl_pairing (u : homogeneousSpace) (g : Test) :
    ⟪u, homogeneousGradient (curlTest g)⟫_ℝ =
      -⟪curlTensor (u : GradientTensor), testValue (laplacianTest g)⟫_ℝ := by
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const)
      (((curlTensor.continuous.comp continuous_subtype_val).inner continuous_const).neg)
  · intro f
    exact test_gradient_curl_pairing f g

end EulerMeanCurlIntegration
