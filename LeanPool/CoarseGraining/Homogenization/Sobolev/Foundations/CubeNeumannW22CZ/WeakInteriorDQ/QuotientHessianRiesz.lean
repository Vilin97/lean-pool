/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.OpenInnerFunctional

/-! # Quotient Hessian Riesz -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {V : Set (Vec d)}

/-- A coordinate derivative of a smooth test is supported where the test is
topologically supported. -/
private theorem support_fderiv_apply_basisVec_subset_of_tsupport_subset
    {U : Set (Vec d)} {φ : Vec d → ℝ} (j : Fin d) (hφ_sub : tsupport φ ⊆ U) :
    Function.support (fun x => (fderiv ℝ φ x) (basisVec j)) ⊆ U := by
  intro x hx
  exact hφ_sub <|
    (support_fderiv_subset (𝕜 := ℝ) (f := φ)) <| by
      change fderiv ℝ φ x ≠ 0
      intro hzero
      apply hx
      simp [hzero]

/-- Multiplying by an arbitrary scalar field does not enlarge the support of a
test derivative. -/
private theorem support_mul_fderiv_apply_basisVec_subset_of_tsupport_subset
    {U : Set (Vec d)} {w φ : Vec d → ℝ} (j : Fin d) (hφ_sub : tsupport φ ⊆ U) :
    Function.support (fun x => w x * (fderiv ℝ φ x) (basisVec j)) ⊆ U := by
  intro x hx
  have hderiv_ne : (fderiv ℝ φ x) (basisVec j) ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  exact support_fderiv_apply_basisVec_subset_of_tsupport_subset j hφ_sub hderiv_ne

/-- Riesz representative of the open-inner quotient-Hessian functional. -/
noncomputable def openCubeInnerOpenCubeQuotientHessianRieszRep
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    {step : ℝ} (hstep : step ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : |step| ≤ (σ₁ - ν) * cubeRadius Q) :
    ScalarL2 (scaledOpenCubeSet Q ρ₁) :=
  (InnerProductSpace.toDual ℝ (ScalarL2 (scaledOpenCubeSet Q ρ₁))).symm
    (openCubeInnerOpenCubeQuotientHessianFunctional
      h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one hstep_abs)

/-- The Riesz representative evaluates against any open-inner `L²` test as the
continuous quotient-Hessian functional. -/
theorem inner_openCubeInnerOpenCubeQuotientHessianRieszRep_eq_functional
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    {step : ℝ} (hstep : step ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : |step| ≤ (σ₁ - ν) * cubeRadius Q)
    (x : ScalarL2 (scaledOpenCubeSet Q ρ₁)) :
    inner ℝ
        (openCubeInnerOpenCubeQuotientHessianRieszRep
          h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
          hσ₂_nonneg hσ₂_lt_one hstep_abs)
        x =
      openCubeInnerOpenCubeQuotientHessianFunctional
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs x := by
  change inner ℝ
      (((InnerProductSpace.toDual ℝ (ScalarL2 (scaledOpenCubeSet Q ρ₁))).symm)
        (openCubeInnerOpenCubeQuotientHessianFunctional
          h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
          hσ₂_nonneg hσ₂_lt_one hstep_abs))
      x =
    openCubeInnerOpenCubeQuotientHessianFunctional
      h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one hstep_abs x
  exact
    InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ)
      (E := ScalarL2 (scaledOpenCubeSet Q ρ₁))
      (x := x)
      (y :=
        (openCubeInnerOpenCubeQuotientHessianFunctional
          h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
          hσ₂_nonneg hσ₂_lt_one hstep_abs :
          StrongDual ℝ (ScalarL2 (scaledOpenCubeSet Q ρ₁))))

/-- On the dense smooth-test submodule, the continuous open-inner functional
agrees with the concrete quotient-Hessian pairing. -/
theorem openCubeInnerOpenCubeQuotientHessianFunctional_apply_subtype
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    {step : ℝ} (hstep : step ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : |step| ≤ (σ₁ - ν) * cubeRadius Q)
    (hρ₁_nonneg : 0 ≤ ρ₁)
    (x : h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)) :
    openCubeInnerOpenCubeQuotientHessianFunctional
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs
        ((h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)).subtype x) =
      openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs x := by
  exact
    extendH1WeakTestScalarL2Functional_apply_subtype
      (d := d) (U := scaledOpenCubeSet Q ρ₁)
      (isOpen_scaledOpenCubeSet Q ρ₁)
      (volume_scaledOpenCubeSet_ne_top_of_nonneg Q hρ₁_nonneg)
      (openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ)
      (openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs)
      (norm_openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional_apply_le
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs)
      x

/-- The explicit square-root bound used for the quotient-Hessian functional is
nonnegative. -/
theorem openCubeInnerQuotientHessianSmoothTestBound_nonneg
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q)) (f : Vec d → ℝ)
    (i : Fin d) {ρ₁ ρ₂ σ₁ σ₂ : ℝ}
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂) :
    0 ≤ openCubeInnerQuotientHessianSmoothTestBound
      (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ := by
  dsimp [openCubeInnerQuotientHessianSmoothTestBound]
  positivity

/-- The Riesz representative has the same explicit norm bound as the
continuous open-inner quotient-Hessian functional. -/
theorem norm_openCubeInnerOpenCubeQuotientHessianRieszRep_le
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    {step : ℝ} (hstep : step ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : |step| ≤ (σ₁ - ν) * cubeRadius Q)
    (hρ₁_nonneg : 0 ≤ ρ₁) :
    ‖openCubeInnerOpenCubeQuotientHessianRieszRep
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs‖ ≤
      openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ := by
  let L : ScalarL2 (scaledOpenCubeSet Q ρ₁) →L[ℝ] ℝ :=
    openCubeInnerOpenCubeQuotientHessianFunctional
      h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one hstep_abs
  let C : ℝ :=
    openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ
  have hL_bound : ∀ x, ‖L x‖ ≤ C * ‖x‖ := by
    intro x
    simpa [L, C] using
      norm_openCubeInnerOpenCubeQuotientHessianFunctional_apply_le
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs hρ₁_nonneg x
  have hL_op : ‖L‖ ≤ C :=
    L.opNorm_le_bound
      (by
        simpa [C] using
          openCubeInnerQuotientHessianSmoothTestBound_nonneg
            (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ)
      hL_bound
  have hnorm_eq :
      ‖openCubeInnerOpenCubeQuotientHessianRieszRep
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs‖ = ‖L‖ := by
    change
      ‖((InnerProductSpace.toDual ℝ (ScalarL2 (scaledOpenCubeSet Q ρ₁))).symm) L‖ = ‖L‖
    exact ((InnerProductSpace.toDual ℝ (ScalarL2 (scaledOpenCubeSet Q ρ₁))).symm.norm_map L)
  exact hnorm_eq.trans_le hL_op

/-- For each nonzero step, the Riesz representative is the weak derivative of
the forward difference quotient on the open inner cube. -/
theorem openCubeInnerOpenCubeQuotientHessianRieszRep_hasWeakPartialDerivOn_forwardDifferenceQuotient
    {Q : TriadicCube d} {uQ : H1Function (openCubeSet Q)} {f : Vec d → ℝ}
    (h : WeakPoissonEquationOn (openCubeSet Q) uQ f)
    (hf : MemScalarL2 (openCubeSet Q) f)
    (hV : IsOpenBoundedConvexDomain V)
    {step : ℝ} (hstep : step ≠ 0) (i j : Fin d)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν ≤ σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hstep_abs : |step| ≤ (σ₁ - ν) * cubeRadius Q)
    (hρ₁_nonneg : 0 ≤ ρ₁) :
    HasWeakPartialDerivOn (scaledOpenCubeSet Q ρ₁) j
      (euclideanForwardDifferenceQuotient step i uQ.toFun)
      (fun x =>
        openCubeInnerOpenCubeQuotientHessianRieszRep
          h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
          hσ₂_nonneg hσ₂_lt_one hstep_abs x) := by
  intro φ hφ hφs hφ_sub
  let S : Set (Vec d) := scaledOpenCubeSet Q ρ₁
  let φTest : H1WeakTestFunction S :=
    { toFun := φ
      smooth := hφ
      compactSupport := hφs
      support_subset := by simpa [S] using hφ_sub }
  let xsub : h1WeakTestScalarL2Submodule (d := d) S :=
    ⟨φTest.toScalarL2, by exact ⟨φTest, rfl⟩⟩
  let rep : ScalarL2 S :=
    openCubeInnerOpenCubeQuotientHessianRieszRep
      h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one hstep_abs
  have hinner_functional :
      inner ℝ rep φTest.toScalarL2 =
        openCubeInnerOpenCubeQuotientHessianFunctional
          h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
          hσ₂_nonneg hσ₂_lt_one hstep_abs φTest.toScalarL2 := by
    simpa [rep, S] using
      inner_openCubeInnerOpenCubeQuotientHessianRieszRep_eq_functional
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs φTest.toScalarL2
  have hfunctional_smooth :
      openCubeInnerOpenCubeQuotientHessianFunctional
          h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
          hσ₂_nonneg hσ₂_lt_one hstep_abs φTest.toScalarL2 =
        openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional
          h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
          hσ₂_nonneg hσ₂_lt_one hstep_abs xsub := by
    simpa [xsub, S, Submodule.subtype] using
      openCubeInnerOpenCubeQuotientHessianFunctional_apply_subtype
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs hρ₁_nonneg xsub
  have hsmooth_pairing :
      openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional
          h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
          hσ₂_nonneg hσ₂_lt_one hstep_abs xsub =
        -∫ y in V,
          euclideanForwardDifferenceQuotient step i uQ.toFun y *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume := by
    let ψ : H1WeakTestFunction S := h1WeakTestScalarL2Representative xsub
    have hψ_eq : ψ.toScalarL2 = φTest.toScalarL2 := by
      simpa [ψ, xsub, S, Submodule.subtype] using
        h1WeakTestScalarL2Representative_toScalarL2 xsub
    have hpair :=
      h.neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerOpenCube_eq_of_h1WeakTest_toScalarL2_eq_of_step_abs_le
        hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs ψ φTest hψ_eq
    change
      -∫ y in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun y *
          (fderiv ℝ (ψ : Vec d → ℝ) y) (basisVec j) ∂MeasureTheory.volume =
      -∫ y in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun y *
          (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume
    simpa [φTest] using hpair
  have hinner_integral :
      inner ℝ rep φTest.toScalarL2 =
        ∫ x in S, rep x * φ x ∂MeasureTheory.volume := by
    rw [scalarInner_eq_integral]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [φTest.coeFn_toScalarL2] with x hφ_l2
    rw [hφ_l2]
  have hrep_integral :
      ∫ x in S, rep x * φ x ∂MeasureTheory.volume =
        -∫ y in V,
          euclideanForwardDifferenceQuotient step i uQ.toFun y *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume :=
    hinner_integral.symm.trans
      (hinner_functional.trans (hfunctional_smooth.trans hsmooth_pairing))
  have hSV : S ⊆ V := by
    simpa [S] using
      (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁).trans hinnerV
  have hderiv_support :
      Function.support
        (fun x =>
          euclideanForwardDifferenceQuotient step i uQ.toFun x *
            (fderiv ℝ φ x) (basisVec j)) ⊆ S :=
    support_mul_fderiv_apply_basisVec_subset_of_tsupport_subset j (by simpa [S] using hφ_sub)
  have hV_eq_S :
      ∫ y in V,
          euclideanForwardDifferenceQuotient step i uQ.toFun y *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume =
        ∫ y in S,
          euclideanForwardDifferenceQuotient step i uQ.toFun y *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume :=
    integral_subset_of_support_subset (U := V) (V := S) hSV hderiv_support
  have hV_pair :
      ∫ y in V,
          euclideanForwardDifferenceQuotient step i uQ.toFun y *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume =
        -∫ x in S, rep x * φ x ∂MeasureTheory.volume := by
    rw [hrep_integral, neg_neg]
  calc
    ∫ y in scaledOpenCubeSet Q ρ₁,
        euclideanForwardDifferenceQuotient step i uQ.toFun y *
          (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume =
        ∫ y in S,
          euclideanForwardDifferenceQuotient step i uQ.toFun y *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume := by
          rfl
    _ = ∫ y in V,
          euclideanForwardDifferenceQuotient step i uQ.toFun y *
            (fderiv ℝ φ y) (basisVec j) ∂MeasureTheory.volume := hV_eq_S.symm
    _ = -∫ x in S, rep x * φ x ∂MeasureTheory.volume := hV_pair
    _ = -∫ x in scaledOpenCubeSet Q ρ₁,
        (fun y =>
          openCubeInnerOpenCubeQuotientHessianRieszRep
            h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
            hσ₂_nonneg hσ₂_lt_one hstep_abs y) x *
          φ x ∂MeasureTheory.volume := by
          rfl

end WeakPoissonEquationOn

end

end Homogenization
