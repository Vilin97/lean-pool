/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.InnerCubeAndHessian

/-! # Smooth Test Bound Estimate -/

namespace Homogenization

open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ}

/-- Multiplication by a quantitative cube cutoff does not increase a single
gradient-coordinate square integral. -/
theorem setIntegral_openCubeSet_cutoff_grad_sq_le
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q)) (i : Fin d)
    {σ₁ σ₂ : ℝ} (θ : QuantitativeCubeCutoff Q σ₁ σ₂) :
    ∫ x in openCubeSet Q, ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2
        ∂MeasureTheory.volume ≤
      ∫ x in openCubeSet Q, (uQ.grad x i) ^ 2 ∂MeasureTheory.volume := by
  have hθ_top : MeasureTheory.MemLp (θ : Vec d → ℝ) ⊤
      (volumeMeasureOn (openCubeSet Q)) :=
    θ.smooth.continuous.memLp_top_of_hasCompactSupport θ.hasCompactSupport
      (volumeMeasureOn (openCubeSet Q))
  have hleft_mem : MemScalarL2 (openCubeSet Q)
      (fun x => (θ : Vec d → ℝ) x * uQ.grad x i) := by
    simpa [MemScalarL2, volumeMeasureOn, mul_comm] using
      (uQ.gradMemL2 i).mul' hθ_top
  have hleft_int : MeasureTheory.IntegrableOn
      (fun x => ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2) (openCubeSet Q) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using hleft_mem.integrable_sq
  have hright_int : MeasureTheory.IntegrableOn
      (fun x => (uQ.grad x i) ^ 2) (openCubeSet Q) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (uQ.gradMemL2 i).integrable_sq
  have hpoint :
      (fun x => ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict (openCubeSet Q)]
      fun x => (uQ.grad x i) ^ 2 := by
    filter_upwards with x
    have hθ_abs : |(θ : Vec d → ℝ) x| ≤ 1 :=
      quantitativeCubeCutoff_abs_le_one θ x
    have hθ_sq_le_one : ((θ : Vec d → ℝ) x) ^ 2 ≤ 1 := by
      have hsq :=
        (sq_le_sq₀ (abs_nonneg ((θ : Vec d → ℝ) x))
          (by norm_num : 0 ≤ (1 : ℝ))).2 hθ_abs
      simpa [sq_abs] using hsq
    have hgrad_nonneg : 0 ≤ (uQ.grad x i) ^ 2 := sq_nonneg _
    calc
      ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2
          = ((θ : Vec d → ℝ) x) ^ 2 * (uQ.grad x i) ^ 2 := by ring
      _ ≤ 1 * (uQ.grad x i) ^ 2 :=
          mul_le_mul_of_nonneg_right hθ_sq_le_one hgrad_nonneg
      _ = (uQ.grad x i) ^ 2 := by ring
  exact MeasureTheory.integral_mono_ae hleft_int hright_int hpoint

/-- A coordinate derivative of a quantitative cube cutoff is bounded by the
finite-dimensional cutoff-gradient constant. -/
theorem sq_fderiv_quantitativeCubeCutoff_apply_basisVec_le
    {Q : TriadicCube d} {σ₁ σ₂ : ℝ}
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂) (i : Fin d) (x : Vec d) :
    ((fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2 ≤
      (d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          ((σ₂ - σ₁) * cubeRadius Q)) ^ 2 := by
  have hcoord :
      ((fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2 ≤
        vecNormSq (euclideanGradient (θ : Vec d → ℝ) x) := by
    simpa [euclideanGradient, euclideanCoordDeriv] using
      coord_sq_le_vecNormSq (euclideanGradient (θ : Vec d → ℝ) x) i
  exact hcoord.trans (vecNormSq_euclideanGradient_quantitativeCubeCutoff_le θ x)

/-- The cutoff-derivative lower-order term is controlled by the `L²` size of
the function and the explicit finite-dimensional cutoff-gradient constant. -/
theorem setIntegral_openCubeSet_value_fderiv_cutoff_sq_le
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q)) (i : Fin d)
    {σ₁ σ₂ : ℝ} (θ : QuantitativeCubeCutoff Q σ₁ σ₂) :
    ∫ x in openCubeSet Q,
        (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
        ∂MeasureTheory.volume ≤
      ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            ((σ₂ - σ₁) * cubeRadius Q)) ^ 2) *
        ∫ x in openCubeSet Q, uQ.toFun x ^ 2 ∂MeasureTheory.volume := by
  let K : ℝ :=
    (d : ℝ) *
      (quantitativeCubeCutoffGradientConst d /
        ((σ₂ - σ₁) * cubeRadius Q)) ^ 2
  have hdθ_top : MeasureTheory.MemLp
      (fun x => (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ⊤
      (volumeMeasureOn (openCubeSet Q)) := by
    simpa [euclideanCoordDeriv, volumeMeasureOn] using!
      (contDiff_euclideanCoordDeriv θ.smooth i).continuous.memLp_top_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordDeriv θ.hasCompactSupport i)
        (volumeMeasureOn (openCubeSet Q))
  have hleft_mem : MemScalarL2 (openCubeSet Q)
      (fun x => uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) := by
    simpa [MemScalarL2, volumeMeasureOn, mul_comm] using
      (uQ.memL2.mul' (p := ⊤) (q := 2) (r := 2) hdθ_top)
  have hleft_int : MeasureTheory.IntegrableOn
      (fun x =>
        (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2)
      (openCubeSet Q) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using hleft_mem.integrable_sq
  have hu_sq_int : MeasureTheory.IntegrableOn
      (fun x => uQ.toFun x ^ 2) (openCubeSet Q) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using uQ.memL2.integrable_sq
  have hright_int : MeasureTheory.IntegrableOn
      (fun x => K * uQ.toFun x ^ 2) (openCubeSet Q) :=
    hu_sq_int.const_mul K
  have hpoint :
      (fun x =>
        (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict (openCubeSet Q)]
      fun x => K * uQ.toFun x ^ 2 := by
    filter_upwards with x
    have hderiv :
        ((fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2 ≤ K := by
      simpa [K] using
        sq_fderiv_quantitativeCubeCutoff_apply_basisVec_le θ i x
    have hu_nonneg : 0 ≤ uQ.toFun x ^ 2 := sq_nonneg _
    calc
      (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
          = uQ.toFun x ^ 2 *
              ((fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2 := by ring
      _ ≤ uQ.toFun x ^ 2 * K :=
          mul_le_mul_of_nonneg_left hderiv hu_nonneg
      _ = K * uQ.toFun x ^ 2 := by ring
  have hmono := MeasureTheory.integral_mono_ae hleft_int hright_int hpoint
  have hright_eq :
      ∫ x in openCubeSet Q, K * uQ.toFun x ^ 2 ∂MeasureTheory.volume =
        K * ∫ x in openCubeSet Q, uQ.toFun x ^ 2 ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_const_mul]
  rw [hright_eq] at hmono
  simpa [K] using hmono

/-- A reduced version of the smooth-test quotient-Hessian bound where the two
cutoff lower-order terms have been replaced by unweighted `H¹` integrals. -/
noncomputable def openCubeInnerQuotientHessianSmoothTestReducedBound
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q)) (f : Vec d → ℝ)
    (i : Fin d) {ρ₁ ρ₂ σ₁ σ₂ : ℝ}
    (_θ : QuantitativeCubeCutoff Q σ₁ σ₂) : ℝ :=
  ((4 : ℝ) *
    ((2 : ℝ) * ∫ x in openCubeSet Q, f x ^ 2 ∂MeasureTheory.volume +
      ((3 : ℝ) *
        ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
        ((2 : ℝ) * ∫ x in openCubeSet Q, (uQ.grad x i) ^ 2
            ∂MeasureTheory.volume +
          (2 : ℝ) *
            (((d : ℝ) *
              (quantitativeCubeCutoffGradientConst d /
                ((σ₂ - σ₁) * cubeRadius Q)) ^ 2) *
              ∫ x in openCubeSet Q, uQ.toFun x ^ 2
                ∂MeasureTheory.volume)))) ^ (1 / (2 : ℝ))

/-- The smooth-test quotient-Hessian bound is controlled by its reduced
unweighted `H¹` version. -/
theorem openCubeInnerQuotientHessianSmoothTestBound_le_reducedBound
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q)) (f : Vec d → ℝ)
    (i : Fin d) {ρ₁ ρ₂ σ₁ σ₂ : ℝ}
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂) :
    openCubeInnerQuotientHessianSmoothTestBound
        (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ ≤
      openCubeInnerQuotientHessianSmoothTestReducedBound
        (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ := by
  let A : ℝ :=
    (2 : ℝ) * ∫ x in openCubeSet Q, f x ^ 2 ∂MeasureTheory.volume +
      ((3 : ℝ) *
        ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
        ((2 : ℝ) * ∫ x in openCubeSet Q, ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2
            ∂MeasureTheory.volume +
          (2 : ℝ) *
            ∫ x in openCubeSet Q,
              (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
              ∂MeasureTheory.volume)
  let B : ℝ :=
    (2 : ℝ) * ∫ x in openCubeSet Q, f x ^ 2 ∂MeasureTheory.volume +
      ((3 : ℝ) *
        ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
        ((2 : ℝ) * ∫ x in openCubeSet Q, (uQ.grad x i) ^ 2
            ∂MeasureTheory.volume +
          (2 : ℝ) *
            (((d : ℝ) *
              (quantitativeCubeCutoffGradientConst d /
                ((σ₂ - σ₁) * cubeRadius Q)) ^ 2) *
              ∫ x in openCubeSet Q, uQ.toFun x ^ 2
                ∂MeasureTheory.volume))
  have hcut :=
    setIntegral_openCubeSet_cutoff_grad_sq_le (Q := Q) uQ i θ
  have hderiv :=
    setIntegral_openCubeSet_value_fderiv_cutoff_sq_le (Q := Q) uQ i θ
  have hlower :
      (2 : ℝ) * ∫ x in openCubeSet Q, ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2
          ∂MeasureTheory.volume +
        (2 : ℝ) *
          ∫ x in openCubeSet Q,
            (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
            ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in openCubeSet Q, (uQ.grad x i) ^ 2
          ∂MeasureTheory.volume +
        (2 : ℝ) *
          (((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((σ₂ - σ₁) * cubeRadius Q)) ^ 2) *
            ∫ x in openCubeSet Q, uQ.toFun x ^ 2
              ∂MeasureTheory.volume) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hcut (by norm_num))
      (mul_le_mul_of_nonneg_left hderiv (by norm_num))
  have hcoef_nonneg :
      0 ≤
        (3 : ℝ) *
          ((d : ℝ) *
            (quantitativeCubeCutoffGradientConst d /
              ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2) := by
    positivity
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hlower hcoef_nonneg) _
  have h4AB : (4 : ℝ) * A ≤ (4 : ℝ) * B :=
    mul_le_mul_of_nonneg_left hAB (by norm_num)
  have h4A_nonneg : 0 ≤ (4 : ℝ) * A := by
    dsimp [A]
    positivity
  simpa [openCubeInnerQuotientHessianSmoothTestBound,
    openCubeInnerQuotientHessianSmoothTestReducedBound, A, B] using
    Real.rpow_le_rpow h4A_nonneg h4AB (by norm_num : 0 ≤ (1 / (2 : ℝ)))

end WeakPoissonEquationOn

end

end Homogenization
