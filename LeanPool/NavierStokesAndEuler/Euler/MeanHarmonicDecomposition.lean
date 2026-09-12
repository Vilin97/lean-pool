/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.MeanVectorIdentities
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator

/-!
The localized weak Newtonian potential produces the source's actual curl field `w`.
Its complement is distributionally harmonic wherever the cutoff is one.
-/

section

/-! Classical integration by parts and its extension to the actual homogeneous gradient space. -/

section

/-! The ordinary curl as a bounded antisymmetrization of actual L² gradient tensors. -/

@[expose] public section

noncomputable section

namespace EulerMeanCurlTensor

open MeasureTheory EulerSmoothLimit EulerVectorCalculus EulerMeanSolenoidal
  EulerMeanCutoffCurl EulerMeanGradientTest EulerMeanBoundary
open scoped ContDiff ENNReal NNReal

/-- Coordinate insertion, given by `(EuclideanSpace.proj j).smulRight (EuclideanSpace.single i
1)`. -/
def coordinateInsertion (i j : Fin 3) : Space →L[ℝ] Space :=
  (EuclideanSpace.proj j).smulRight (EuclideanSpace.single i 1)

theorem coordinateInsertion_norm_le (i j : Fin 3) : ‖coordinateInsertion i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  simpa [coordinateInsertion, ContinuousLinearMap.smulRight_apply, norm_smul] using
      PiLp.norm_apply_le v j

/-- Coordinate L², given by `(coordinateInsertion i j).compLpL 2 volume`. -/
def coordinateL2 (i j : Fin 3) : L2 →L[ℝ] L2 :=
  (coordinateInsertion i j).compLpL 2 volume

theorem coordinateL2_ae (i j : Fin 3) (u : L2) :
    coordinateL2 i j u =ᵐ[volume] fun x => (u x j) • EuclideanSpace.single i 1 :=
  (coordinateInsertion i j).coeFn_compLpL (p := 2) (μ := volume) u

theorem coordinateL2_apply_norm_le (i j : Fin 3) (u : L2) : ‖coordinateL2 i j u‖ ≤ ‖u‖ := by
  refine ((coordinateInsertion i j).norm_compLp_le u).trans ?_
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (coordinateInsertion_norm_le i j)
      (norm_nonneg u)

/-- Each output component is the difference of the two off-diagonal derivative entries. -/
def curlTensor : GradientTensor →L[ℝ] L2 :=
  ∑ i : Fin 3,
    ((coordinateL2 i (i+2)).comp (PiLp.proj 2 (fun _ : Fin 3 => L2) (i+1)) -
      (coordinateL2 i (i+1)).comp (PiLp.proj 2 (fun _ : Fin 3 => L2) (i+2)))

theorem curlTensor_apply (G : GradientTensor) :
    curlTensor G = ∑ i : Fin 3,
      (coordinateL2 i (i+2) (G (i+1)) - coordinateL2 i (i+1) (G (i+2))) := by
  simp [curlTensor]

/-- A fixed universal contraction bound; sharpness is not needed for localization. -/
theorem curlTensor_norm_le (G : GradientTensor) : ‖curlTensor G‖ ≤ 6 * ‖G‖ := by
  rw [curlTensor_apply]
  calc
    _ ≤ ∑ i : Fin 3, ‖coordinateL2 i (i+2) (G (i+1)) - coordinateL2 i (i+1) (G (i+2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, 2 * ‖G‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h1 := (coordinateL2_apply_norm_le i (i+2) (G (i+1))).trans (PiLp.norm_apply_le G (i+1))
      have h2 := (coordinateL2_apply_norm_le i (i+1) (G (i+2))).trans (PiLp.norm_apply_le G (i+2))
      exact (norm_sub_le _ _).trans (by linarith)
    _ = 6 * ‖G‖ := by simp; ring

theorem curlTensor_ae (G : GradientTensor) :
    curlTensor G =ᵐ[volume] fun x => WithLp.toLp 2 (fun i : Fin 3 =>
      (G (i+1) x) (i+2) - (G (i+2) x) (i+1)) := by
  rw [curlTensor_apply]
  have hpart (i : Fin 3) :
      (coordinateL2 i (i+2) (G (i+1)) - coordinateL2 i (i+1) (G (i+2))) =ᵐ[volume]
        fun x => ((G (i+1) x) (i+2) - (G (i+2) x) (i+1)) • EuclideanSpace.single i 1 := by
    filter_upwards [Lp.coeFn_sub (coordinateL2 i (i+2) (G (i+1)))
      (coordinateL2 i (i+1) (G (i+2))), coordinateL2_ae i (i+2) (G (i+1)),
      coordinateL2_ae i (i+1) (G (i+2))] with x hs h1 h2
    simp only [Pi.sub_apply] at hs
    rw [hs, h1, h2, sub_smul]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin 3 => coordinateL2 i (i+2) (G (i+1)) - coordinateL2 i (i+1) (G (i+2))),
    ae_all_iff.mpr hpart] with x hs hp
  simp only [Finset.sum_apply] at hs
  rw [hs]
  simp_rw [hp]
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three]

/-- On genuine test gradients the tensor operator is exactly the ordinary classical curl. -/
theorem curlTensor_test_ae (f : Test) :
    curlTensor (testGradient f) =ᵐ[volume] vectorCurl (f : Space → Space) := by
  filter_upwards [curlTensor_ae (testGradient f),
    ae_all_iff.mpr (fun i => derivativeColumn_ae f i)] with x hc hd
  rw [hc, vectorCurl_eq_matrix _ x ((f.smooth.differentiable (by simp)).differentiableAt)]
  ext i
  change (derivativeColumn f (i+1) x) (i+2) - (derivativeColumn f (i+2) x) (i+1) = _
  rw [hd, hd]
  rfl

/-- The source's field `w`, formed directly from the weak potential's gradient tensor. -/
def harmonicPart (χ : Cutoff) (z : L2) : L2 :=
  curlTensor (weakPotential χ z : GradientTensor)

theorem harmonicPart_norm_le (χ : Cutoff) (z : L2) :
    ‖harmonicPart χ z‖ ≤ 6 * ‖weakPotential χ z‖ :=
  curlTensor_norm_le (weakPotential χ z : GradientTensor)

end EulerMeanCurlTensor

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanCurlIntegration

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanCutoffCurl EulerMeanGradientTest EulerMeanVectorIdentities
  EulerMeanCurlTensor
open scoped ContDiff

/-- Partial test, given by `⟨vectorPartial (f : Space → Space) i, vectorPartial_smooth f
f.smooth i, vectorPartial_compact f f.compact i⟩`. -/
def partialTest (f : Test) (i : Fin 3) : Test :=
  ⟨vectorPartial (f : Space → Space) i, vectorPartial_smooth f f.smooth i,
    vectorPartial_compact f f.compact i⟩

theorem test_memLp (f : Test) : MemLp (f : Space → Space) 2 volume :=
  f.smooth.continuous.memLp_of_hasCompactSupport f.compact

/-- Test value, given by `(test_memLp f).toLp (f : Space → Space)`. -/
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

/-- Distributional integration by parts survives passage to the closed homogeneous gradient space.
-/
theorem homogeneous_curl_pairing (u : homogeneousSpace) (g : Test) :
    ⟪u, homogeneousGradient (curlTest g)⟫_ℝ =
      -⟪curlTensor (u : GradientTensor), testValue (laplacianTest g)⟫_ℝ := by
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact isClosed_eq (continuous_id.inner continuous_const)
      (((curlTensor.continuous.comp continuous_subtype_val).inner continuous_const).neg)
  · intro f
    exact test_gradient_curl_pairing f g

end EulerMeanCurlIntegration

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanHarmonic

open MeasureTheory InnerProductSpace Laplacian EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanCutoffCurl EulerMeanGradientTest EulerMeanBoundary
  EulerMeanCurlTensor EulerMeanVectorIdentities EulerMeanCurlIntegration
open scoped ContDiff

/-- Distributional harmonicity of an actual ordinary L² vector field on a set. -/
def WeakHarmonicOn (U : Set Space) (u : EulerMeanSolenoidal.L2) : Prop :=
  ∀ φ : Space → Space, HasCompactSupport φ → ContDiff ℝ ∞ φ →
    tsupport φ ⊆ U → (∫ x, ⟪u x, Δ φ x⟫_ℝ) = 0

theorem l2_test_pairing (u : L2) (f : Test) :
    ⟪u, testValue f⟫_ℝ = ∫ x, ⟪u x, (f : Space → Space) x⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testValue_ae f] with x hx
  rw [hx]

/-- Divergence gradient, constructed using `EulerMeanSolenoidal.testGradient`. -/
def divergenceGradient (f : Test) : L2 :=
  EulerMeanSolenoidal.testGradient (divergence (f : Space → Space))
    (divergence_compact f f.smooth f.compact) (divergence_smooth f f.smooth)

theorem divergenceGradient_ae (f : Test) :
    divergenceGradient f =ᵐ[volume] gradient (divergence (f : Space → Space)) :=
  EulerMeanSolenoidal.testGradient_ae _ _ _

theorem divergenceGradient_mem (f : Test) : divergenceGradient f ∈ gradientSpace :=
  testGradient_mem _ _ _

theorem testValue_curlcurl (f : Test) :
    testValue (curlTest (curlTest f)) = divergenceGradient f - testValue (laplacianTest f) := by
  apply Lp.ext
  filter_upwards [testValue_ae (curlTest (curlTest f)), divergenceGradient_ae f,
    testValue_ae (laplacianTest f), Lp.coeFn_sub (divergenceGradient f) (testValue (laplacianTest
        f))]
    with x hcc hg hl hs
  rw [hcc, hs]
  change vectorCurl (vectorCurl (f : Space → Space)) x =
    divergenceGradient f x - testValue (laplacianTest f) x
  rw [hg, hl, vectorCurl_vectorCurl f f.smooth]
  rfl

theorem solenoidal_curlcurl_pairing (z : L2) (hz : z ∈ solenoidalSpace) (f : Test) :
    ⟪z, testValue (curlTest (curlTest f))⟫_ℝ = -⟪z, testValue (laplacianTest f)⟫_ℝ := by
  rw [testValue_curlcurl, inner_sub_right]
  have hg : ⟪z, divergenceGradient f⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hz (divergenceGradient f) (divergenceGradient_mem f)
  rw [hg, zero_sub]

theorem cutoff_curlTest_eq (χ : Cutoff) (U : Set Space)
    (hχ : ∀ x ∈ U, χ.field x = 1) (f : Test) (hf : tsupport (f : Space → Space) ⊆ U) :
    (fun x => χ.field x • (curlTest f : Space → Space) x) = vectorCurl (f : Space → Space) := by
  funext x
  by_cases hx : x ∈ U
  · change χ.field x • vectorCurl (f : Space → Space) x = _
    rw [hχ x hx, one_smul]
  · have hs : x ∉ tsupport (vectorCurl (f : Space → Space)) :=
      fun h => hx (hf (vectorCurl_support f h))
    change χ.field x • vectorCurl (f : Space → Space) x = _
    rw [image_eq_zero_of_notMem_tsupport hs, smul_zero]

/-- The actual curl tensor of any homogeneous potential remains solenoidal. -/
theorem homogeneous_curl_solenoidal (u : homogeneousSpace) :
    curlTensor (u : GradientTensor) ∈ solenoidalSpace := by
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact gradientSpace.isClosed_orthogonal.preimage
      (curlTensor.continuous.comp continuous_subtype_val)
  · intro f
    change curlTensor (EulerMeanGradientTest.testGradient f) ∈ solenoidalSpace
    rw [curlTensor_test_eq]
    exact curl_mem_solenoidal _ ((contDiff_piLp 2).mp f.smooth) (test_memLp (curlTest f))

theorem harmonicPart_solenoidal (χ : Cutoff) (z : L2) :
    harmonicPart χ z ∈ solenoidalSpace := homogeneous_curl_solenoidal (weakPotential χ z)

/-- The source's `z - w` is genuinely weakly harmonic where the actual cutoff equals one. -/
theorem weakHarmonicOn_sub_harmonicPart (χ : Cutoff) (U : Set Space) (z : L2)
    (hz : z ∈ solenoidalSpace) (hχ : ∀ x ∈ U, χ.field x = 1) :
    WeakHarmonicOn U (z - harmonicPart χ z) := by
  intro φ hc hs hsupport
  let f : Test := ⟨φ, hs, hc⟩
  have h₁ : ⟪weakPotential χ z, homogeneousGradient (curlTest f)⟫_ℝ =
      ⟪z, testValue (curlTest (curlTest f))⟫_ℝ := by
    rw [weakPotential_pairing, cutoff_curlTest_eq χ U hχ f hsupport, l2_test_pairing]
    rfl
  have h₂ := homogeneous_curl_pairing (weakPotential χ z) f
  have h₃ := solenoidal_curlcurl_pairing z hz f
  have hi : ⟪z - harmonicPart χ z, testValue (laplacianTest f)⟫_ℝ = 0 := by
    rw [inner_sub_left]
    change ⟪z, testValue (laplacianTest f)⟫_ℝ -
      ⟪curlTensor (weakPotential χ z : GradientTensor), testValue (laplacianTest f)⟫_ℝ = 0
    linarith
  exact (l2_test_pairing (z - harmonicPart χ z) (laplacianTest f)).symm.trans hi

/-- A quantitative decomposition constructed from the cutoff and the given solenoidal field. -/
theorem exists_weak_harmonic_decomposition (χ : Cutoff) (U : Set Space) (z : L2)
    (hz : z ∈ solenoidalSpace) (hχ : ∀ x ∈ U, χ.field x = 1) :
    ∃ w : L2, w = harmonicPart χ z ∧ w ∈ solenoidalSpace ∧
      ‖w‖ ≤ 6 * ‖weakPotential χ z‖ ∧ WeakHarmonicOn U (z - w) :=
  ⟨harmonicPart χ z, rfl, harmonicPart_solenoidal χ z, harmonicPart_norm_le χ z,
    weakHarmonicOn_sub_harmonicPart χ U z hz hχ⟩

end EulerMeanHarmonic
