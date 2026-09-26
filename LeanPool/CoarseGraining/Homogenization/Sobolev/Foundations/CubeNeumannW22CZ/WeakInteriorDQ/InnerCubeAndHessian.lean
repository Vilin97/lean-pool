/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotientH1
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph.Preliminaries
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.QuantitativeCutoff
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Order.Filter.Finite

public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1

/-! # Inner Cube And Hessian -/

@[expose] public section

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {U V : Set (Vec d)}
variable {u : H1Function U} {f : Vec d → ℝ}


/-- Open-cube quantitative test-functional bound obtained by combining the
inner-cube Caccioppoli estimate with the weak-gradient handoff.  This is the
uniform small-step form aimed at the weak Hessian limit argument. -/
theorem abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_le_of_step_abs_le
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
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub_inner : tsupport φ ⊆ scaledClosedCubeSet Q ρ₁) :
    |(-∫ x in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume)| ≤
      (2 : ℝ) *
        ((2 : ℝ) * ∫ x in openCubeSet Q, f x ^ 2 ∂MeasureTheory.volume +
          ((3 : ℝ) *
            ((d : ℝ) *
              (quantitativeCubeCutoffGradientConst d /
                ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
            ((2 : ℝ) * ∫ x in openCubeSet Q, ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2
                ∂MeasureTheory.volume +
              (2 : ℝ) *
                ∫ x in openCubeSet Q,
                  (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
                  ∂MeasureTheory.volume)) +
        (1 / 2 : ℝ) * ∫ x in scaledClosedCubeSet Q ρ₁, φ x ^ 2
          ∂MeasureTheory.volume := by
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
  let R : ℝ :=
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
  have henergy :
      (1 / 4 : ℝ) *
          ∫ x in scaledClosedCubeSet Q ρ₁,
            vecNormSq
              ((uQ.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume ≤ R := by
    simpa only [R, one_div] using!
      h.directDifferenceQuotient_quantitativeCubeCutoff_openCube_innerCube_energy_quarter_le_forcing_sq_add_quantitative_lower_h1_terms_of_step_abs_le
        hf hV hstep i η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs
  have hbound :=
    abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_le_of_inner_energy_quarter_le
      (U := openCubeSet Q) (V := V) uQ hV hVU
      (step := step) (R := R) i j hVshift
      (S := scaledClosedCubeSet Q ρ₁) hinnerV
      hφ hφ_compact hφ_sub_inner henergy
  simpa [R] using hbound

/-- Open-cube homogeneous test-functional bound obtained by combining the
inner-cube Caccioppoli estimate with the full-gradient Cauchy handoff. -/
theorem abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_le_sqrt_energy_bound_mul_l2_of_step_abs_le
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
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub_inner : tsupport φ ⊆ scaledClosedCubeSet Q ρ₁) :
    |(-∫ x in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume)| ≤
      ((4 : ℝ) *
        ((2 : ℝ) * ∫ x in openCubeSet Q, f x ^ 2 ∂MeasureTheory.volume +
          ((3 : ℝ) *
            ((d : ℝ) *
              (quantitativeCubeCutoffGradientConst d /
                ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
            ((2 : ℝ) * ∫ x in openCubeSet Q, ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2
                ∂MeasureTheory.volume +
              (2 : ℝ) *
                ∫ x in openCubeSet Q,
                  (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
                  ∂MeasureTheory.volume))) ^ (1 / (2 : ℝ)) *
        (∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ)
          ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
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
  let R : ℝ :=
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
  have henergy :
      (1 / 4 : ℝ) *
          ∫ x in scaledClosedCubeSet Q ρ₁,
            vecNormSq
              ((uQ.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume ≤ R := by
    simpa only [R, one_div] using!
      h.directDifferenceQuotient_quantitativeCubeCutoff_openCube_innerCube_energy_quarter_le_forcing_sq_add_quantitative_lower_h1_terms_of_step_abs_le
        hf hV hstep i η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs
  have hbound :=
    abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_le_sqrt_energy_bound_mul_l2
      (U := openCubeSet Q) (V := V) uQ hV hVU
      (step := step) (R := R) i j hVshift
      (S := scaledClosedCubeSet Q ρ₁) hinnerV
      hφ hφ_compact hφ_sub_inner henergy
  simpa [R] using hbound

/-- Open-cube version of the zero-seminorm well-definedness consequence for
the quotient Hessian test functional. -/
theorem neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_eq_zero_of_l2_norm_zero_of_step_abs_le
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
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub_inner : tsupport φ ⊆ scaledClosedCubeSet Q ρ₁)
    (hφ_zero :
      ∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume = 0) :
    -∫ x in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume = 0 := by
  let T : ℝ :=
    -∫ x in V,
      euclideanForwardDifferenceQuotient step i uQ.toFun x *
        (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume
  change T = 0
  have hbound :
      |T| ≤
        ((4 : ℝ) *
          ((2 : ℝ) * ∫ x in openCubeSet Q, f x ^ 2 ∂MeasureTheory.volume +
            ((3 : ℝ) *
              ((d : ℝ) *
                (quantitativeCubeCutoffGradientConst d /
                  ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
              ((2 : ℝ) * ∫ x in openCubeSet Q, ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2
                  ∂MeasureTheory.volume +
                (2 : ℝ) *
                  ∫ x in openCubeSet Q,
                    (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
                    ∂MeasureTheory.volume))) ^ (1 / (2 : ℝ)) *
          (∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ)
            ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
    simpa [T] using
      h.abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_le_sqrt_energy_bound_mul_l2_of_step_abs_le
        hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs hφ hφ_compact hφ_sub_inner
  have hroot_zero :
      (∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) = 0 := by
    rw [hφ_zero, Real.zero_rpow]
    norm_num
  have hle_zero : |T| ≤ 0 := by
    calc
      |T| ≤
          ((4 : ℝ) *
            ((2 : ℝ) * ∫ x in openCubeSet Q, f x ^ 2 ∂MeasureTheory.volume +
              ((3 : ℝ) *
                ((d : ℝ) *
                  (quantitativeCubeCutoffGradientConst d /
                    ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
                ((2 : ℝ) * ∫ x in openCubeSet Q, ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2
                    ∂MeasureTheory.volume +
                  (2 : ℝ) *
                    ∫ x in openCubeSet Q,
                      (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
                      ∂MeasureTheory.volume))) ^ (1 / (2 : ℝ)) *
            (∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ)
              ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) :=
        hbound
      _ = 0 := by
        rw [hroot_zero, mul_zero]
  exact abs_eq_zero.mp (le_antisymm hle_zero (abs_nonneg T))

/-- Open-cube version of the distance-zero well-definedness consequence for
the quotient Hessian test functional. -/
theorem neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_eq_of_l2_dist_zero_of_step_abs_le
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
    {φ ψ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hφ_compact : HasCompactSupport φ) (hψ_compact : HasCompactSupport ψ)
    (hφ_sub_inner : tsupport φ ⊆ scaledClosedCubeSet Q ρ₁)
    (hψ_sub_inner : tsupport ψ ⊆ scaledClosedCubeSet Q ρ₁)
    (hφψ_zero :
      ∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x - ψ x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume = 0) :
    -∫ x in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume =
      -∫ x in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun x *
          (fderiv ℝ ψ x) (basisVec j) ∂MeasureTheory.volume := by
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
  let R : ℝ :=
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
  have henergy :
      (1 / 4 : ℝ) *
          ∫ x in scaledClosedCubeSet Q ρ₁,
            vecNormSq
              ((uQ.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume ≤ R := by
    simpa only [R, one_div] using!
      h.directDifferenceQuotient_quantitativeCubeCutoff_openCube_innerCube_energy_quarter_le_forcing_sq_add_quantitative_lower_h1_terms_of_step_abs_le
        hf hV hstep i η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs
  exact
    neg_integral_forwardDifferenceQuotient_mul_fderiv_eq_of_l2_dist_zero_on_inner
      (U := openCubeSet Q) (V := V) uQ hV hVU
      (step := step) (R := R) i j hVshift
      (S := scaledClosedCubeSet Q ρ₁) hinnerV
      hφ hψ hφ_compact hψ_compact hφ_sub_inner hψ_sub_inner henergy hφψ_zero

/-- The open-cube quotient-Hessian pairing depends only on the scalar `L²`
class of a smooth weak test on the inner cube. -/
theorem neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_eq_of_h1WeakTest_toScalarL2_eq_of_step_abs_le
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
    (φ ψ : H1WeakTestFunction (scaledClosedCubeSet Q ρ₁))
    (hφψ : φ.toScalarL2 = ψ.toScalarL2) :
    -∫ x in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun x *
          (fderiv ℝ (φ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume =
      -∫ x in V,
        euclideanForwardDifferenceQuotient step i uQ.toFun x *
          (fderiv ℝ (ψ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume := by
  have hφψ_zero :
      ∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x - ψ x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume = 0 :=
    integral_norm_sq_sub_eq_zero_of_h1WeakTestFunction_toScalarL2_eq φ ψ hφψ
  exact
    h.neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_eq_of_l2_dist_zero_of_step_abs_le
      hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one hstep_abs
      φ.smooth ψ.smooth φ.compactSupport ψ.compactSupport
      φ.support_subset ψ.support_subset hφψ_zero

/-- The explicit square-root bound controlling the smooth-test
quotient-Hessian functional on an inner cube. -/
noncomputable def openCubeInnerQuotientHessianSmoothTestBound
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q)) (f : Vec d → ℝ)
    (i : Fin d) {ρ₁ ρ₂ σ₁ σ₂ : ℝ}
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂) : ℝ :=
  ((4 : ℝ) *
    ((2 : ℝ) * ∫ x in openCubeSet Q, f x ^ 2 ∂MeasureTheory.volume +
      ((3 : ℝ) *
        ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            ((ρ₂ - ρ₁) * cubeRadius Q)) ^ 2)) *
        ((2 : ℝ) * ∫ x in openCubeSet Q, ((θ : Vec d → ℝ) x * uQ.grad x i) ^ 2
            ∂MeasureTheory.volume +
          (2 : ℝ) *
            ∫ x in openCubeSet Q,
              (uQ.toFun x * (fderiv ℝ (θ : Vec d → ℝ) x) (basisVec i)) ^ 2
              ∂MeasureTheory.volume))) ^ (1 / (2 : ℝ))

/-- The concrete linear functional on the dense smooth-test `ScalarL2`
submodule induced by one quotient-Hessian pairing. -/
noncomputable def openCubeInnerQuotientHessianSmoothTestFunctional
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
    h1WeakTestScalarL2Submodule (d := d) (scaledClosedCubeSet Q ρ₁) →ₗ[ℝ] ℝ := by
  let S : Set (Vec d) := scaledClosedCubeSet Q ρ₁
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
  refine
    { toFun := fun x => pairing (rep x)
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    have hrep_add_eq :
        pairing (rep (x + y)) = pairing ((rep x).add (rep y)) := by
      unfold pairing
      exact
        h.neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_eq_of_h1WeakTest_toScalarL2_eq_of_step_abs_le
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
          (step := step) i j hVshift (S := S) (by simpa [S] using hinnerV)
          (rep x) (rep y)
    exact hrep_add_eq.trans hpair_add
  · intro c x
    have hrep_smul_eq :
        pairing (rep (c • x)) = pairing ((rep x).smul c) := by
      unfold pairing
      exact
        h.neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_eq_of_h1WeakTest_toScalarL2_eq_of_step_abs_le
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
          (step := step) i j hVshift (S := S) (by simpa [S] using hinnerV)
          c (rep x)
    calc
      pairing (rep (c • x)) = pairing ((rep x).smul c) := hrep_smul_eq
      _ = c * pairing (rep x) := hpair_smul
      _ = c • pairing (rep x) := by rfl

/-- The concrete smooth-test functional satisfies the square-root operator
bound needed by the dense-domain extension API. -/
theorem norm_openCubeInnerQuotientHessianSmoothTestFunctional_apply_le
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
    (x : h1WeakTestScalarL2Submodule (d := d) (scaledClosedCubeSet Q ρ₁)) :
    ‖openCubeInnerQuotientHessianSmoothTestFunctional
        h hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
        hσ₂_nonneg hσ₂_lt_one hstep_abs x‖ ≤
      openCubeInnerQuotientHessianSmoothTestBound (ρ₁ := ρ₁) (ρ₂ := ρ₂) uQ f i θ *
        ‖((h1WeakTestScalarL2Submodule (d := d) (scaledClosedCubeSet Q ρ₁)).subtype x)‖ := by
  let φ : H1WeakTestFunction (scaledClosedCubeSet Q ρ₁) :=
    h1WeakTestScalarL2Representative x
  have hbound :=
    h.abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_openCube_innerCube_le_sqrt_energy_bound_mul_l2_of_step_abs_le
      hf hV hstep i j η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one hstep_abs
      φ.smooth φ.compactSupport φ.support_subset
  have hroot :
      (∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ)
        ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) =
        ‖((h1WeakTestScalarL2Submodule (d := d) (scaledClosedCubeSet Q ρ₁)).subtype x)‖ := by
    calc
      (∫ x in scaledClosedCubeSet Q ρ₁, ‖φ x‖ ^ (2 : ℝ)
          ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) =
          ‖φ.toScalarL2‖ :=
        integral_norm_sq_rpow_half_eq_norm_h1WeakTestFunction_toScalarL2 φ
      _ = ‖((h1WeakTestScalarL2Submodule (d := d) (scaledClosedCubeSet Q ρ₁)).subtype x)‖ := by
        rw [show φ.toScalarL2 =
            ((h1WeakTestScalarL2Submodule (d := d) (scaledClosedCubeSet Q ρ₁)).subtype x) by
          simpa [φ, Submodule.subtype] using h1WeakTestScalarL2Representative_toScalarL2 x]
  calc
    ‖openCubeInnerQuotientHessianSmoothTestFunctional
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
        ‖((h1WeakTestScalarL2Submodule (d := d) (scaledClosedCubeSet Q ρ₁)).subtype x)‖ := by
          rw [hroot]

/-- Product-rule form of the cutoff energy test. -/
theorem test_mulContDiffHasCompactSupport_expanded
    (h : WeakPoissonEquationOn U u f)
    (hU : IsOpenBoundedConvexDomain U) (hf : MemScalarL2 U f)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    ∫ x in U,
        vecDot (u.grad x)
          (fun j => φ x * u.grad x j + u x * (fderiv ℝ φ x) (basisVec j))
          ∂MeasureTheory.volume =
      ∫ x in U, f x * (φ x * u.toFun x) ∂MeasureTheory.volume := by
  have htest :=
    h.test_mulContDiffHasCompactSupportToH10 hU hf hφ hφ_compact hφ_sub
  have hgrad_ae :=
    mulContDiffHasCompactSupportToH10_grad_ae u hU hφ hφ_compact hφ_sub
  have hleft :
      ∫ x in U,
          vecDot (u.grad x)
            ((u.mulContDiffHasCompactSupportToH10 hU
              hφ hφ_compact hφ_sub).toH1Function.grad x)
            ∂MeasureTheory.volume =
        ∫ x in U,
          vecDot (u.grad x)
            (fun j => φ x * u.grad x j + u x * (fderiv ℝ φ x) (basisVec j))
            ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hgrad_ae] with x hx
    simp [hx]
  simpa [hleft] using htest

/-- Coordinatewise gradient identification for the forward localized
difference-quotient test.  The `H¹₀` constructor is chosen through membership
data, so the product-rule gradient is recovered by weak-derivative uniqueness
on the open interior domain. -/
theorem cutoffForwardDifferenceQuotientToH10_grad_coord_ae
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    (fun x =>
        (u.cutoffForwardDifferenceQuotientToH10 step i hV hVU hVshift
          hφ hφ_compact hφ_sub).toH1Function.grad x j) =ᵐ[
          MeasureTheory.volume.restrict V]
      fun x =>
        φ x * (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
          euclideanForwardDifferenceQuotient step i u.toFun x *
            (fderiv ℝ φ x) (basisVec j) := by
  let ψ : H10Function V :=
    u.cutoffForwardDifferenceQuotientToH10 step i hV hVU hVshift
      hφ hφ_compact hφ_sub
  let w : H1Function V :=
    u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift
  let wφ : H1Function V := w.mulContDiffHasCompactSupport hφ hφ_compact
  have hψ_fun : ψ.toH1Function.toFun = wφ.toFun := by
    funext x
    simp [ψ, wφ, w]
  have hψ_loc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => ψ.toH1Function.grad x j) V MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((ψ.toH1Function.gradMemL2 j).locallyIntegrable (by norm_num))
  have hwφ_loc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => wφ.grad x j) V MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((wφ.gradMemL2 j).locallyIntegrable (by norm_num))
  have hψ_weak :
      HasWeakPartialDerivOn V j ψ.toH1Function.toFun
        (fun x => ψ.toH1Function.grad x j) :=
    ψ.toH1Function.hasWeakPartialDerivOn j
  have hwφ_weak :
      HasWeakPartialDerivOn V j ψ.toH1Function.toFun
        (fun x => wφ.grad x j) := by
    rw [hψ_fun]
    exact wφ.hasWeakPartialDerivOn j
  have hae :=
    HasWeakPartialDerivOn.ae_eq hV.isOpen hψ_loc hwφ_loc hψ_weak hwφ_weak
  simpa [ψ, wφ, w, H1Function.mulContDiffHasCompactSupport_grad] using hae

/-- Coordinatewise gradient identification for the backward localized
difference-quotient test. -/
theorem cutoffBackwardDifferenceQuotientToH10_grad_coord_ae
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i j : Fin d)
    (hVshift : V ⊆ translateSet (step • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    (fun x =>
        (u.cutoffBackwardDifferenceQuotientToH10 step i hV hVU hVshift
          hφ hφ_compact hφ_sub).toH1Function.grad x j) =ᵐ[
          MeasureTheory.volume.restrict V]
      fun x =>
        φ x * (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
          euclideanBackwardDifferenceQuotient step i u.toFun x *
            (fderiv ℝ φ x) (basisVec j) := by
  let ψ : H10Function V :=
    u.cutoffBackwardDifferenceQuotientToH10 step i hV hVU hVshift
      hφ hφ_compact hφ_sub
  let w : H1Function V :=
    u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift
  let wφ : H1Function V := w.mulContDiffHasCompactSupport hφ hφ_compact
  have hψ_fun : ψ.toH1Function.toFun = wφ.toFun := by
    funext x
    simp [ψ, wφ, w]
  have hψ_loc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => ψ.toH1Function.grad x j) V MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((ψ.toH1Function.gradMemL2 j).locallyIntegrable (by norm_num))
  have hwφ_loc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => wφ.grad x j) V MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((wφ.gradMemL2 j).locallyIntegrable (by norm_num))
  have hψ_weak :
      HasWeakPartialDerivOn V j ψ.toH1Function.toFun
        (fun x => ψ.toH1Function.grad x j) :=
    ψ.toH1Function.hasWeakPartialDerivOn j
  have hwφ_weak :
      HasWeakPartialDerivOn V j ψ.toH1Function.toFun
        (fun x => wφ.grad x j) := by
    rw [hψ_fun]
    exact wφ.hasWeakPartialDerivOn j
  have hae :=
    HasWeakPartialDerivOn.ae_eq hV.isOpen hψ_loc hwφ_loc hψ_weak hwφ_weak
  simpa [ψ, wφ, w, H1Function.mulContDiffHasCompactSupport_grad] using hae

/-- Vector-valued a.e. gradient identification for the forward localized
difference-quotient test. -/
theorem cutoffForwardDifferenceQuotientToH10_grad_ae
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    (fun x =>
        (u.cutoffForwardDifferenceQuotientToH10 step i hV hVU hVshift
          hφ hφ_compact hφ_sub).toH1Function.grad x) =ᵐ[
          MeasureTheory.volume.restrict V]
      fun x j =>
        φ x * (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
          euclideanForwardDifferenceQuotient step i u.toFun x *
            (fderiv ℝ φ x) (basisVec j) := by
  have hcoord :
      ∀ j : Fin d,
        (fun x =>
            (u.cutoffForwardDifferenceQuotientToH10 step i hV hVU hVshift
              hφ hφ_compact hφ_sub).toH1Function.grad x j) =ᵐ[
              MeasureTheory.volume.restrict V]
          fun x =>
            φ x * (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
              euclideanForwardDifferenceQuotient step i u.toFun x *
                (fderiv ℝ φ x) (basisVec j) := by
    intro j
    exact cutoffForwardDifferenceQuotientToH10_grad_coord_ae
      u hV hVU step i j hVshift hφ hφ_compact hφ_sub
  filter_upwards [(Filter.eventually_all (l := MeasureTheory.ae (MeasureTheory.volume.restrict V))).2 hcoord] with x hx
  ext j
  exact hx j

/-- Vector-valued a.e. gradient identification for the backward localized
difference-quotient test. -/
theorem cutoffBackwardDifferenceQuotientToH10_grad_ae
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet (step • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    (fun x =>
        (u.cutoffBackwardDifferenceQuotientToH10 step i hV hVU hVshift
          hφ hφ_compact hφ_sub).toH1Function.grad x) =ᵐ[
          MeasureTheory.volume.restrict V]
      fun x j =>
        φ x * (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
          euclideanBackwardDifferenceQuotient step i u.toFun x *
            (fderiv ℝ φ x) (basisVec j) := by
  have hcoord :
      ∀ j : Fin d,
        (fun x =>
            (u.cutoffBackwardDifferenceQuotientToH10 step i hV hVU hVshift
              hφ hφ_compact hφ_sub).toH1Function.grad x j) =ᵐ[
              MeasureTheory.volume.restrict V]
          fun x =>
            φ x * (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
              euclideanBackwardDifferenceQuotient step i u.toFun x *
                (fderiv ℝ φ x) (basisVec j) := by
    intro j
    exact cutoffBackwardDifferenceQuotientToH10_grad_coord_ae
      u hV hVU step i j hVshift hφ hφ_compact hφ_sub
  filter_upwards [(Filter.eventually_all (l := MeasureTheory.ae (MeasureTheory.volume.restrict V))).2 hcoord] with x hx
  ext j
  exact hx j

/-- Expanded weak-test identity for a forward localized difference quotient.
This is the product-rule form of
`restrict_test_cutoffForwardDifferenceQuotientToH10`. -/
theorem restrict_test_cutoffForwardDifferenceQuotient_expanded
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    ∫ x in V,
        vecDot ((u.restrict hV.isOpen hVU).grad x)
          (fun j =>
            φ x * (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
              euclideanForwardDifferenceQuotient step i u.toFun x *
                (fderiv ℝ φ x) (basisVec j)) ∂MeasureTheory.volume =
      ∫ x in V,
        f x * (φ x * euclideanForwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume := by
  have htest :=
    h.restrict_test_cutoffForwardDifferenceQuotientToH10
      hV hVU hfV step i hVshift hφ hφ_compact hφ_sub
  have hgrad_ae :=
    cutoffForwardDifferenceQuotientToH10_grad_ae
      u hV hVU step i hVshift hφ hφ_compact hφ_sub
  have hleft :
      ∫ x in V,
          vecDot ((u.restrict hV.isOpen hVU).grad x)
            ((u.cutoffForwardDifferenceQuotientToH10 step i hV hVU hVshift
              hφ hφ_compact hφ_sub).toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in V,
          vecDot ((u.restrict hV.isOpen hVU).grad x)
            (fun j =>
              φ x * (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
                euclideanForwardDifferenceQuotient step i u.toFun x *
                  (fderiv ℝ φ x) (basisVec j)) ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hgrad_ae] with x hx
    simp [hx]
  simpa [hleft] using htest

/-- Expanded weak-test identity for a backward localized difference quotient. -/
theorem restrict_test_cutoffBackwardDifferenceQuotient_expanded
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet (step • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    ∫ x in V,
        vecDot ((u.restrict hV.isOpen hVU).grad x)
          (fun j =>
            φ x * (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
              euclideanBackwardDifferenceQuotient step i u.toFun x *
                (fderiv ℝ φ x) (basisVec j)) ∂MeasureTheory.volume =
      ∫ x in V,
        f x * (φ x * euclideanBackwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume := by
  have htest :=
    h.restrict_test_cutoffBackwardDifferenceQuotientToH10
      hV hVU hfV step i hVshift hφ hφ_compact hφ_sub
  have hgrad_ae :=
    cutoffBackwardDifferenceQuotientToH10_grad_ae
      u hV hVU step i hVshift hφ hφ_compact hφ_sub
  have hleft :
      ∫ x in V,
          vecDot ((u.restrict hV.isOpen hVU).grad x)
            ((u.cutoffBackwardDifferenceQuotientToH10 step i hV hVU hVshift
              hφ hφ_compact hφ_sub).toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in V,
          vecDot ((u.restrict hV.isOpen hVU).grad x)
            (fun j =>
              φ x * (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
                euclideanBackwardDifferenceQuotient step i u.toFun x *
                  (fderiv ℝ φ x) (basisVec j)) ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hgrad_ae] with x hx
    simp [hx]
  simpa [hleft] using htest

end WeakPoissonEquationOn

end

end Homogenization
