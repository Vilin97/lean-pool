/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanGradientTestSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Construction of the actual mean boundary operator by homogeneous-gradient
completion and the Hilbert adjoint. No bounded inverse Laplacian on L² is assumed. -/

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanCutoffCurl EulerMeanGradientTest
open scoped ContDiff ENNReal NNReal

/-- The only cutoff data: an actual compactly supported smooth scalar function. -/
structure Cutoff where
  field : Space → ℝ
  smooth : ContDiff ℝ ∞ field
  compact : HasCompactSupport field

/-- Coordinate antisymmetrization of a genuine derivative. -/
def curlMatrix (A : Space →L[ℝ] Space) : Space :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    (A (EuclideanSpace.single (i+1) 1)) (i+2) -
      (A (EuclideanSpace.single (i+2) 1)) (i+1))

theorem vectorCurl_eq_matrix (f : Space → Space) (x : Space)
    (hf : DifferentiableAt ℝ f x) : vectorCurl f x = curlMatrix (fderiv ℝ f x) := by
  ext i
  simp only [vectorCurl, curl_apply, partialDerivative, fderiv_coordinate f x hf, curlMatrix]

theorem curlMatrix_add (A B : Space →L[ℝ] Space) :
    curlMatrix (A+B) = curlMatrix A + curlMatrix B := by
  ext i
  simp only [curlMatrix, add_apply, PiLp.add_apply]
  ring

theorem curlMatrix_smul (c : ℝ) (A : Space →L[ℝ] Space) :
    curlMatrix (c • A) = c • curlMatrix A := by
  ext i
  simp only [curlMatrix, smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem vectorCurl_add (f g : Space → Space)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    vectorCurl (f+g) = vectorCurl f + vectorCurl g := by
  funext x
  rw [vectorCurl_eq_matrix _ x ((hf x).add (hg x)), fderiv_add (hf x) (hg x), curlMatrix_add,
    ← vectorCurl_eq_matrix f x (hf x), ← vectorCurl_eq_matrix g x (hg x)]
  rfl

theorem vectorCurl_smul (c : ℝ) (f : Space → Space) (hf : Differentiable ℝ f) :
    vectorCurl (c • f) = c • vectorCurl f := by
  funext x
  rw [vectorCurl_eq_matrix _ x ((hf x).const_smul c), fderiv_const_smul (hf x) c,
    curlMatrix_smul, ← vectorCurl_eq_matrix f x (hf x)]
  rfl

theorem testCurl_memLp (χ : Cutoff) (f : Test) :
    MemLp (vectorCurl (fun x => χ.field x • (f : Space → Space) x)) 2 volume :=
  vectorCurl_memLp _ (χ.smooth.smul f.smooth) (f.compact.smul_left (f := χ.field))

/-- The literal curl of the cutoff times a compact vector test, in ordinary L². -/
def testCurl (χ : Cutoff) (f : Test) : L2 := (testCurl_memLp χ f).toLp _

theorem testCurl_ae (χ : Cutoff) (f : Test) :
    testCurl χ f =ᵐ[volume] vectorCurl (fun x => χ.field x • (f : Space → Space) x) :=
  (testCurl_memLp χ f).coeFn_toLp

theorem testCurl_add (χ : Cutoff) (f g : Test) :
    testCurl χ (f+g) = testCurl χ f + testCurl χ g := by
  apply Lp.ext
  filter_upwards [testCurl_ae χ (f+g), testCurl_ae χ f, testCurl_ae χ g,
    Lp.coeFn_add (testCurl χ f) (testCurl χ g)] with x hfg hf hg ha
  simp only [Pi.add_apply] at ha
  rw [hfg, ha, hf, hg]
  have hadd : (fun y => χ.field y • (↑(f+g) : Space → Space) y) =
      (fun y => χ.field y • (f : Space → Space) y) +
        (fun y => χ.field y • (g : Space → Space) y) := by
    funext y
    exact smul_add _ _ _
  have hdf : Differentiable ℝ (fun y => χ.field y • (f : Space → Space) y) :=
    (χ.smooth.smul f.smooth).differentiable (by simp)
  have hdg : Differentiable ℝ (fun y => χ.field y • (g : Space → Space) y) :=
    (χ.smooth.smul g.smooth).differentiable (by simp)
  rw [hadd]
  exact congrFun (vectorCurl_add _ _ hdf hdg) x

theorem testCurl_smul (χ : Cutoff) (c : ℝ) (f : Test) :
    testCurl χ (c • f) = c • testCurl χ f := by
  apply Lp.ext
  filter_upwards [testCurl_ae χ (c • f), testCurl_ae χ f,
    Lp.coeFn_smul c (testCurl χ f)] with x hcf hf hs
  simp only [Pi.smul_apply] at hs
  rw [hcf, hs, hf]
  have hsmul : (fun y => χ.field y • (↑(c • f) : Space → Space) y) =
      c • (fun y => χ.field y • (f : Space → Space) y) := by
    funext y
    exact smul_comm (χ.field y) c ((f : Space → Space) y)
  have hdf : Differentiable ℝ (fun y => χ.field y • (f : Space → Space) y) :=
    (χ.smooth.smul f.smooth).differentiable (by simp)
  rw [hsmul]
  exact congrFun (vectorCurl_smul c _ hdf) x

/-- The actual linear cutoff-curl operation on vector tests. -/
def testCurlLinear (χ : Cutoff) : Test →ₗ[ℝ] L2 where
  toFun := testCurl χ
  map_add' := testCurl_add χ
  map_smul' := testCurl_smul χ

/-- The proved cutoff-dependent bound on the homogeneous space. -/
def cutoffBound (χ : Cutoff) : ℝ :=
  3 * cutoffCurlConstant *
    (lpNorm χ.field ∞ volume + lpNorm (gradient χ.field) 3 volume)

theorem cutoffBound_nonneg (χ : Cutoff) : 0 ≤ cutoffBound χ := by
  unfold cutoffBound
  exact mul_nonneg (mul_nonneg (by norm_num) cutoffCurlConstant_pos.le)
    (add_nonneg lpNorm_nonneg lpNorm_nonneg)

theorem testCurl_bound (χ : Cutoff) (f : Test) :
    ‖testCurlLinear χ f‖ ≤ cutoffBound χ * ‖homogeneousGradient f‖ := by
  change ‖testCurl χ f‖ ≤ _
  rw [testCurl, Lp.norm_toLp, toReal_eLpNorm (testCurl_memLp χ f).aestronglyMeasurable]
  calc
    _ ≤ cutoffCurlConstant *
        (lpNorm χ.field ∞ volume + lpNorm (gradient χ.field) 3 volume) *
          lpNorm (fderiv ℝ (f : Space → Space)) 2 volume :=
      cutoff_curl_bound χ.field f χ.smooth χ.compact f.smooth f.compact
    _ ≤ cutoffCurlConstant *
        (lpNorm χ.field ∞ volume + lpNorm (gradient χ.field) 3 volume) *
          (3 * ‖testGradient f‖) :=
      mul_le_mul_of_nonneg_left (lpNorm_fderiv_le_gradient f)
        (mul_nonneg cutoffCurlConstant_pos.le (add_nonneg lpNorm_nonneg lpNorm_nonneg))
    _ = cutoffBound χ * ‖homogeneousGradient f‖ := by
      change _ = cutoffBound χ * ‖testGradient f‖
      unfold cutoffBound
      ring

/-- The bounded extension of actual cutoff-curl to the homogeneous Hilbert space. -/
def cutoffCurl (χ : Cutoff) : homogeneousSpace →L[ℝ] L2 :=
  (testCurlLinear χ).extendOfNorm homogeneousGradient

theorem cutoffCurl_on_test (χ : Cutoff) (f : Test) :
    cutoffCurl χ (homogeneousGradient f) = testCurl χ f :=
  LinearMap.extendOfNorm_eq homogeneousGradient_dense ⟨cutoffBound χ, testCurl_bound χ⟩ f

theorem cutoffCurl_norm_le (χ : Cutoff) : ‖cutoffCurl χ‖ ≤ cutoffBound χ :=
  LinearMap.opNorm_extendOfNorm_le homogeneousGradient_dense (cutoffBound_nonneg χ) (testCurl_bound
    χ)

/-- The Riesz/weak-Newtonian representation of the cutoff curl functional. -/
def weakPotential (χ : Cutoff) : L2 →L[ℝ] homogeneousSpace := (cutoffCurl χ).adjoint

/-- The represented functional agrees exactly with the source's distributional pairing. -/
theorem weakPotential_pairing (χ : Cutoff) (z : L2) (f : Test) :
    ⟪weakPotential χ z, homogeneousGradient f⟫_ℝ =
      ∫ x, ⟪z x, vectorCurl (fun y => χ.field y • (f : Space → Space) y) x⟫_ℝ := by
  rw [weakPotential, ContinuousLinearMap.adjoint_inner_left, cutoffCurl_on_test,
    MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testCurl_ae χ f] with x hx
  rw [hx]

theorem weakPotential_norm_le (χ : Cutoff) (z : L2) :
    ‖weakPotential χ z‖ ≤ cutoffBound χ * ‖z‖ := by
  refine ((weakPotential χ).le_opNorm z).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  change ‖(cutoffCurl χ).adjoint‖ ≤ cutoffBound χ
  rw [LinearIsometryEquiv.norm_map]
  exact cutoffCurl_norm_le χ

/-- Compact vector tests determine the weak potential uniquely in the actual homogeneous space. -/
theorem weakPotential_unique (χ : Cutoff) (z : L2) (u : homogeneousSpace)
    (hu : ∀ f : Test, ⟪u, homogeneousGradient f⟫_ℝ =
      ∫ x, ⟪z x, vectorCurl (fun y => χ.field y • (f : Space → Space) y) x⟫_ℝ) :
    u = weakPotential χ z := by
  apply ext_inner_right ℝ
  intro v
  refine homogeneousGradient_dense.induction_on v ?_ ?_
  · exact isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  · intro f
    exact (hu f).trans (weakPotential_pairing χ z f).symm

/-- A genuine uniquely solvable weak Poisson/Riesz problem for the cutoff-curl functional. -/
theorem existsUnique_weakPotential (χ : Cutoff) (z : L2) :
    ∃! u : homogeneousSpace, ∀ f : Test, ⟪u, homogeneousGradient f⟫_ℝ =
      ∫ x, ⟪z x, vectorCurl (fun y => χ.field y • (f : Space → Space) y) x⟫_ℝ :=
  ⟨weakPotential χ z, weakPotential_pairing χ z, fun u hu => weakPotential_unique χ z u hu⟩

/-- The actual bounded positive mean boundary operator `Tχ Tχ*`. -/
def boundaryOperator (χ : Cutoff) : L2 →L[ℝ] L2 := (cutoffCurl χ).comp (weakPotential χ)

theorem boundaryOperator_pairing (χ : Cutoff) (z w : L2) :
    ⟪boundaryOperator χ z, w⟫_ℝ = ⟪weakPotential χ z, weakPotential χ w⟫_ℝ := by
  change ⟪cutoffCurl χ (weakPotential χ z), w⟫_ℝ = _
  exact (ContinuousLinearMap.adjoint_inner_right (cutoffCurl χ) (weakPotential χ z) w).symm

theorem boundaryOperator_positive (χ : Cutoff) (z : L2) :
    0 ≤ ⟪boundaryOperator χ z, z⟫_ℝ := by
  rw [boundaryOperator_pairing]
  exact real_inner_self_nonneg

theorem boundaryOperator_energy (χ : Cutoff) (z : L2) :
    ⟪boundaryOperator χ z, z⟫_ℝ = ‖weakPotential χ z‖ ^ 2 := by
  rw [boundaryOperator_pairing, real_inner_self_eq_norm_sq]

theorem boundaryOperator_norm_le (χ : Cutoff) :
    ‖boundaryOperator χ‖ ≤ cutoffBound χ ^ 2 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  change ‖cutoffCurl χ‖ * ‖(cutoffCurl χ).adjoint‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (mul_le_mul (cutoffCurl_norm_le χ) (cutoffCurl_norm_le χ)
    (norm_nonneg (cutoffCurl χ)) (cutoffBound_nonneg χ)).trans_eq (sq (cutoffBound χ)).symm

/-- The actual test-level cutoff curl is solenoidal. -/
theorem testCurl_solenoidal (χ : Cutoff) (f : Test) :
    testCurl χ f ∈ solenoidalSpace := by
  have hs : ContDiff ℝ ∞ (fun x => χ.field x • (f : Space → Space) x) := χ.smooth.smul f.smooth
  exact curl_mem_solenoidal _ ((contDiff_piLp 2).mp hs) (testCurl_memLp χ f)

/-- Closedness of the ordinary solenoidal space preserves the curl constraint under completion. -/
theorem cutoffCurl_solenoidal (χ : Cutoff) (u : homogeneousSpace) :
    cutoffCurl χ u ∈ solenoidalSpace := by
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact EulerMeanSolenoidal.gradientSpace.isClosed_orthogonal.preimage (cutoffCurl χ).continuous
  · intro f
    rw [cutoffCurl_on_test]
    exact testCurl_solenoidal χ f

theorem boundaryOperator_solenoidal (χ : Cutoff) (z : L2) :
    boundaryOperator χ z ∈ solenoidalSpace :=
  cutoffCurl_solenoidal χ (weakPotential χ z)

/-- Fields supported in the cutoff's closed support, defined by actual L² restriction. -/
def supportedSpace (χ : Cutoff) : Submodule ℝ L2 :=
  (LpToLpRestrictCLM Space Space ℝ volume 2 (tsupport χ.field)ᶜ).ker

theorem supportedSpace_closed (χ : Cutoff) : IsClosed (supportedSpace χ : Set L2) :=
  (LpToLpRestrictCLM Space Space ℝ volume 2 (tsupport χ.field)ᶜ).isClosed_ker

theorem mem_supportedSpace_iff (χ : Cutoff) (z : L2) :
    z ∈ supportedSpace χ ↔
      (z : Space → Space) =ᵐ[volume.restrict (tsupport χ.field)ᶜ] 0 := by
  change LpToLpRestrictCLM Space Space ℝ volume 2 (tsupport χ.field)ᶜ z = 0 ↔ _
  constructor
  · intro h
    have ha := LpToLpRestrictCLM_coeFn (μ := (volume : Measure Space)) (p := 2)
      ℝ (tsupport χ.field)ᶜ z
    rw [h] at ha
    exact ha.symm.trans (Lp.coeFn_zero Space 2 _)
  · intro h
    apply Lp.ext
    exact (LpToLpRestrictCLM_coeFn ℝ (tsupport χ.field)ᶜ z).trans
      (h.trans (Lp.coeFn_zero Space 2 _).symm)

/-- Multiplication by the cutoff and then curl has no support outside the cutoff support. -/
theorem testCurl_supported (χ : Cutoff) (f : Test) : testCurl χ f ∈ supportedSpace χ := by
  rw [mem_supportedSpace_iff]
  have hs : tsupport (vectorCurl (fun x => χ.field x • (f : Space → Space) x)) ⊆
      tsupport χ.field := by
    apply tsupport_curl_subset _ _ (isClosed_tsupport χ.field)
    intro i
    exact tsupport_mul_subset_left
  filter_upwards [ae_restrict_of_ae (testCurl_ae χ f),
    ae_restrict_mem (isClosed_tsupport χ.field).measurableSet.compl] with x hx hm
  rw [hx]
  exact image_eq_zero_of_notMem_tsupport (fun h => hm (hs h))

/-- Actual support is retained under homogeneous completion because L² restriction is continuous. -/
theorem cutoffCurl_supported (χ : Cutoff) (u : homogeneousSpace) :
    cutoffCurl χ u ∈ supportedSpace χ := by
  refine homogeneousGradient_dense.induction_on u ?_ ?_
  · exact (supportedSpace_closed χ).preimage (cutoffCurl χ).continuous
  · intro f
    rw [cutoffCurl_on_test]
    exact testCurl_supported χ f

theorem boundaryOperator_supported (χ : Cutoff) (z : L2) :
    boundaryOperator χ z ∈ supportedSpace χ :=
  cutoffCurl_supported χ (weakPotential χ z)

/-- The constructed mean boundary output vanishes almost everywhere outside the cutoff support. -/
theorem boundaryOperator_zero_off_support (χ : Cutoff) (z : L2) :
    (boundaryOperator χ z : Space → Space) =ᵐ[volume.restrict (tsupport χ.field)ᶜ] 0 :=
  (mem_supportedSpace_iff χ _).mp (boundaryOperator_supported χ z)

/-- Symmetry follows from the actual Hilbert-adjoint construction. -/
theorem boundaryOperator_symmetric (χ : Cutoff) (z w : L2) :
    ⟪boundaryOperator χ z, w⟫_ℝ = ⟪z, boundaryOperator χ w⟫_ℝ := by
  calc
    ⟪boundaryOperator χ z, w⟫_ℝ = ⟪weakPotential χ z, weakPotential χ w⟫_ℝ :=
      boundaryOperator_pairing χ z w
    _ = ⟪weakPotential χ w, weakPotential χ z⟫_ℝ := real_inner_comm _ _
    _ = ⟪boundaryOperator χ w, z⟫_ℝ := (boundaryOperator_pairing χ w z).symm
    _ = ⟪z, boundaryOperator χ w⟫_ℝ := real_inner_comm _ _

end EulerMeanBoundary
