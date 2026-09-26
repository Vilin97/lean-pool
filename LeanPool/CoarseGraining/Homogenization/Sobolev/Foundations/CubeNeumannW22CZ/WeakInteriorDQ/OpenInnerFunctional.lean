/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.InnerCubeAndHessian

/-! # Open Inner Functional -/

@[expose] public section

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {V : Set (Vec d)}

/-- The square of a smooth weak test on an open inner cube is supported in that
open inner cube. -/
private theorem support_norm_sq_h1WeakTest_subset_scaledOpenCubeSet
    (Q : TriadicCube d) (ρ₁ : ℝ)
    (φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁)) :
    Function.support (fun x => ‖φ x‖ ^ (2 : ℝ)) ⊆ scaledOpenCubeSet Q ρ₁ := by
  intro x hx
  have hφ_ne : φ x ≠ 0 := by
    intro hφ_zero
    apply hx
    change ‖φ x‖ ^ (2 : ℝ) = 0
    rw [hφ_zero, norm_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
  exact φ.support_subset (subset_tsupport (φ : Vec d → ℝ) hφ_ne)

/-- The squared distance between two smooth weak tests on an open inner cube is
supported in that open inner cube. -/
private theorem support_norm_sq_sub_h1WeakTest_subset_scaledOpenCubeSet
    (Q : TriadicCube d) (ρ₁ : ℝ)
    (φ ψ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁)) :
    Function.support (fun x => ‖φ x - ψ x‖ ^ (2 : ℝ)) ⊆ scaledOpenCubeSet Q ρ₁ := by
  intro x hx
  by_cases hφ_zero : φ x = 0
  · have hψ_ne : ψ x ≠ 0 := by
      intro hψ_zero
      apply hx
      change ‖φ x - ψ x‖ ^ (2 : ℝ) = 0
      rw [hφ_zero, hψ_zero, sub_self, norm_zero,
        Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
    exact ψ.support_subset (subset_tsupport (ψ : Vec d → ℝ) hψ_ne)
  · exact φ.support_subset (subset_tsupport (φ : Vec d → ℝ) hφ_zero)

/-- A smooth weak test supported in the open inner cube has the same squared
`L²` integral over the corresponding closed inner cube. -/
theorem integral_norm_sq_h1WeakTest_scaledClosedCubeSet_eq_scaledOpenCubeSet
    (Q : TriadicCube d) (ρ₁ : ℝ)
    (φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁)) :
    ∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume =
      ∫ x in scaledOpenCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume :=
  integral_subset_of_support_subset
    (U := scaledClosedCubeSet Q ρ₁) (V := scaledOpenCubeSet Q ρ₁)
    (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁)
    (support_norm_sq_h1WeakTest_subset_scaledOpenCubeSet Q ρ₁ φ)

/-- The squared distance between two open-inner smooth weak tests has the same
integral over the corresponding closed inner cube. -/
theorem integral_norm_sq_sub_h1WeakTest_scaledClosedCubeSet_eq_scaledOpenCubeSet
    (Q : TriadicCube d) (ρ₁ : ℝ)
    (φ ψ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁)) :
    ∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x - ψ x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume =
      ∫ x in scaledOpenCubeSet Q ρ₁, ‖φ x - ψ x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume :=
  integral_subset_of_support_subset
    (U := scaledClosedCubeSet Q ρ₁) (V := scaledOpenCubeSet Q ρ₁)
    (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁)
    (support_norm_sq_sub_h1WeakTest_subset_scaledOpenCubeSet Q ρ₁ φ ψ)

/-- The quotient-Hessian pairing depends only on the open-inner scalar `L²`
class of a smooth weak test. -/
theorem neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerOpenCube_eq_of_h1WeakTest_toScalarL2_eq_of_step_abs_le
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
    (φ ψ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁))
    (hφψ : φ.toScalarL2 = ψ.toScalarL2) :
    -∫ x in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun x *
          (fderiv ℝ (φ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume =
      -∫ x in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun x *
          (fderiv ℝ (ψ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume := by
  have hφψ_zero_open :
      ∫ x in scaledOpenCubeSet Q ρ₁, ‖φ x - ψ x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume = 0 :=
    integral_norm_sq_sub_eq_zero_of_h1WeakTestFunction_toScalarL2_eq φ ψ hφψ
  have hφψ_zero_closed :
      ∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x - ψ x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume = 0 := by
    rw [integral_norm_sq_sub_h1WeakTest_scaledClosedCubeSet_eq_scaledOpenCubeSet
      Q ρ₁ φ ψ]
    exact hφψ_zero_open
  exact
    h.neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_eq_of_l2_dist_zero_of_step_abs_le
      hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one hstep_abs
      φ.smooth ψ.smooth φ.compactSupport ψ.compactSupport
      (φ.support_subset.trans (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁))
      (ψ.support_subset.trans (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁))
      hφψ_zero_closed

/-- The concrete quotient-Hessian pairing on the dense smooth-test submodule
over the open inner cube.  The estimates are still supplied by the closed
inner cube, using `scaledOpenCubeSet_subset_scaledClosedCubeSet`. -/
noncomputable def openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional
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
    h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁) →ₗ[ℝ] ℝ := by
  let S : Set (Vec d) := scaledOpenCubeSet Q ρ₁
  let rep :
      h1WeakTestScalarL2Submodule (d := d) S → H1WeakTestFunction S :=
    h1WeakTestScalarL2Representative
  let pairing : H1WeakTestFunction S → ℝ := fun φ =>
    -∫ x in V,
      euclideanForwardDifferenceQuotient step i uQ.toFun x *
        (fderiv ℝ (φ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume
  have hVU : V ⊆ openCubeSet Q := by
    intro x hx
    exact
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q hν_nonneg
        (lt_of_le_of_lt hνσ hσ₁_lt_one) (hVν hx)
  have hVshift : V ⊆ translateSet ((-step) • basisVec i) (openCubeSet Q) := by
    intro x hx
    rw [mem_translateSet_iff_sub_mem]
    have hσ₁_nonneg : 0 ≤ σ₁ := hν_nonneg.trans hνσ
    have hxshift :
        euclideanCoordShift step i x ∈ scaledClosedCubeSet Q σ₁ :=
      euclideanCoordShift_mem_scaledClosedCubeSet_of_mem_scaledClosedCubeSet
        Q hνσ hstep_abs i (hVν hx)
    have hxopen : euclideanCoordShift step i x ∈ openCubeSet Q :=
      scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one
        Q hσ₁_nonneg hσ₁_lt_one hxshift
    simpa [euclideanCoordShift, sub_eq_add_neg, neg_smul] using hxopen
  have hSV : S ⊆ V := by
    simpa [S] using
      (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁).trans hinnerV
  refine
    { toFun := fun x => pairing (rep x)
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    have hrep_add_eq :
        pairing (rep (x + y)) = pairing ((rep x).add (rep y)) := by
      unfold pairing
      exact
        h.neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerOpenCube_eq_of_h1WeakTest_toScalarL2_eq_of_step_abs_le
          hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
          hσ₂_nonneg hσ₂_lt_one hstep_abs
          (rep (x + y)) ((rep x).add (rep y)) (by
            rw [h1WeakTestScalarL2Representative_toScalarL2,
              H1WeakTestFunction.toScalarL2_add,
              h1WeakTestScalarL2Representative_toScalarL2,
              h1WeakTestScalarL2Representative_toScalarL2]
            rfl)
    have hpair_add :
        pairing ((rep x).add (rep y)) = pairing (rep x) + pairing (rep y) := by
      simpa [pairing, S] using
        neg_integral_forwardDifferenceQuotient_mul_fderiv_h1WeakTest_add
          (U := openCubeSet Q) (V := V) uQ hV hVU
          (step := step) i j hVshift (S := S) hSV (rep x) (rep y)
    exact hrep_add_eq.trans hpair_add
  · intro c x
    have hrep_smul_eq :
        pairing (rep (c • x)) = pairing ((rep x).smul c) := by
      unfold pairing
      exact
        h.neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerOpenCube_eq_of_h1WeakTest_toScalarL2_eq_of_step_abs_le
          hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
          hσ₂_nonneg hσ₂_lt_one hstep_abs
          (rep (c • x)) ((rep x).smul c) (by
            rw [h1WeakTestScalarL2Representative_toScalarL2,
              H1WeakTestFunction.toScalarL2_smul,
              h1WeakTestScalarL2Representative_toScalarL2]
            rfl)
    have hpair_smul :
        pairing ((rep x).smul c) = c * pairing (rep x) := by
      simpa [pairing, S] using
        neg_integral_forwardDifferenceQuotient_mul_fderiv_h1WeakTest_smul
          (U := openCubeSet Q) (V := V) uQ hV hVU
          (step := step) i j hVshift (S := S) hSV c (rep x)
    calc
      pairing (rep (c • x)) = pairing ((rep x).smul c) := hrep_smul_eq
      _ = c * pairing (rep x) := hpair_smul
      _ = c • pairing (rep x) := by rfl

/-- The open-inner smooth-test functional satisfies the closed-inner
square-root operator bound. -/
theorem norm_openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional_apply_le
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
    (x : h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)) :
    ‖openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs x‖ ≤
      openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ *
        ‖((h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)).subtype x)‖ := by
  let φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁) :=
    h1WeakTestScalarL2Representative x
  have hφ_sub_closed : tsupport (φ : Vec d → ℝ) ⊆ scaledClosedCubeSet Q ρ₁ :=
    φ.support_subset.trans (scaledOpenCubeSet_subset_scaledClosedCubeSet Q ρ₁)
  have hbound :=
    h.abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_le_sqrt_energy_bound_mul_l2_of_step_abs_le
      hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one hstep_abs
      φ.smooth φ.compactSupport hφ_sub_closed
  have hroot :
      (∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) =
        ‖((h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)).subtype x)‖ := by
    rw [integral_norm_sq_h1WeakTest_scaledClosedCubeSet_eq_scaledOpenCubeSet Q ρ₁ φ]
    calc
      (∫ x in scaledOpenCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ)
          ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) =
          ‖φ.toScalarL2‖ :=
        integral_norm_sq_rpow_half_eq_norm_h1WeakTestFunction_toScalarL2 φ
      _ = ‖((h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)).subtype x)‖ := by
        rw [show φ.toScalarL2 =
            ((h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)).subtype x) by
          simpa [φ, Submodule.subtype] using h1WeakTestScalarL2Representative_toScalarL2 x]
  calc
    ‖openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs x‖ =
        |(-∫ y in V,
          euclideanForwardDifferenceQuotient step i uQ.toFun y *
            (fderiv ℝ (φ : Vec d → ℝ) y) (basisVec j) ∂MeasureTheory.volume)| := by
          change ‖(-∫ y in V,
            euclideanForwardDifferenceQuotient step i uQ.toFun y *
              (fderiv ℝ (φ : Vec d → ℝ) y) (basisVec j) ∂MeasureTheory.volume)‖ =
            |(-∫ y in V,
              euclideanForwardDifferenceQuotient step i uQ.toFun y *
                (fderiv ℝ (φ : Vec d → ℝ) y) (basisVec j) ∂MeasureTheory.volume)|
          rw [Real.norm_eq_abs]
    _ ≤ openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ *
        (∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ)
          ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
          simpa [openCubeInnerQuotientHessianSmoothTestBound, φ] using hbound
    _ = openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ *
        ‖((h1WeakTestScalarL2Submodule (d := d) (scaledOpenCubeSet Q ρ₁)).subtype x)‖ := by
          rw [hroot]

/-- Continuous extension of the open-inner quotient-Hessian functional from
smooth tests to all scalar `L²` fields on the open inner cube. -/
noncomputable def openCubeInnerOpenCubeQuotientHessianFunctional
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
    ScalarL2 (scaledOpenCubeSet Q ρ₁) →L[ℝ] ℝ :=
  extendH1WeakTestScalarL2Functional
    (d := d) (U := scaledOpenCubeSet Q ρ₁)
    (openCubeInnerOpenCubeQuotientHessianSmoothTestFunctional
      h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one hstep_abs)

/-- The continuous open-inner quotient-Hessian functional inherits the same
explicit bound as the dense smooth-test functional. -/
theorem norm_openCubeInnerOpenCubeQuotientHessianFunctional_apply_le
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
    (x : ScalarL2 (scaledOpenCubeSet Q ρ₁)) :
    ‖openCubeInnerOpenCubeQuotientHessianFunctional
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs x‖ ≤
      openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ *
        ‖x‖ := by
  exact
    norm_extendH1WeakTestScalarL2Functional_apply_le
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

end WeakPoissonEquationOn

end

end Homogenization
