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

public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SqCutoffH10

/-! # Integral Identity -/

@[expose] public section

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {U V : Set (Vec d)}
variable {u : H1Function U} {f : Vec d → ℝ}


/-- The same direct-test identity with the explicit ambient gradient expanded
as the difference of the unshifted and shifted localized gradients. -/
theorem test_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_gradientSplit
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in U,
        vecDot (u.grad x)
          (step⁻¹ •
            ((localizedSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x -
              (localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
                (U := U) (V := V) u hV hVU step i hVshift
                hη hη_compact hη_sub).grad x))
        ∂MeasureTheory.volume =
      ∫ x in U,
        f x *
          euclideanBackwardDifferenceQuotient step i
            (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x
        ∂MeasureTheory.volume := by
  simpa using
    h.test_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_explicitGradient
      hU hf hV hVU step i hVshift hη hη_compact hη_sub

/-- The split direct-test gradient pairing reduces to two interior pairings:
the unshifted pairing against `G(x)` and the transported shifted pairing
against `G(x+h e_i)`. -/
theorem integral_vecDot_backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient_grad_eq_sub_integrals_on
    {G : Vec d → Vec d} (hG : MemVectorL2 U G)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in U,
        vecDot (G x)
          ((backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume =
      step⁻¹ *
        (∫ x in V,
            vecDot (G x)
              ((localizedSqCutoffForwardDifferenceQuotientToAmbient
                (U := U) (V := V) u hV hVU step i hVshift
                hη hη_compact hη_sub).grad x)
            ∂MeasureTheory.volume -
          ∫ x in V,
            vecDot (G (euclideanCoordShift step i x))
              ((localizedSqCutoffForwardDifferenceQuotientToAmbient
                (U := U) (V := V) u hV hVU step i hVshift
                hη hη_compact hη_sub).grad x)
            ∂MeasureTheory.volume) := by
  let F : H1Function U :=
    localizedSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  let S : H1Function U :=
    localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  let T : H1Function U :=
    backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  have hFInt : MeasureTheory.IntegrableOn (fun x => vecDot (G x) (F.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG F.grad_memVectorL2
  have hSInt : MeasureTheory.IntegrableOn (fun x => vecDot (G x) (S.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG S.grad_memVectorL2
  have hFtransport :
      ∫ x in U, vecDot (G x) (F.grad x) ∂MeasureTheory.volume =
        ∫ x in V, vecDot (G x) (F.grad x) ∂MeasureTheory.volume := by
    simpa [F] using
      integral_vecDot_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_eq_integral_on
        (U := U) (V := V) G u hV hVU step i hVshift hη hη_compact hη_sub
  have hStransport :
      ∫ x in U, vecDot (G x) (S.grad x) ∂MeasureTheory.volume =
        ∫ x in V, vecDot (G (euclideanCoordShift step i x)) (F.grad x)
          ∂MeasureTheory.volume := by
    simpa [F, S] using
      integral_vecDot_localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient_grad_eq_integral_on
        (U := U) (V := V) G u hV hVU step i hVshift hη hη_compact hη_sub
  calc
    ∫ x in U, vecDot (G x) (T.grad x) ∂MeasureTheory.volume =
        ∫ x in U,
          step⁻¹ * (vecDot (G x) (F.grad x) - vecDot (G x) (S.grad x))
          ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro x
          simp [T, F, S, vecDot_smul_right, vecDot_add_right, vecDot_neg_right,
            sub_eq_add_neg]
          ring
    _ = step⁻¹ *
        ∫ x in U, (vecDot (G x) (F.grad x) - vecDot (G x) (S.grad x))
          ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_const_mul]
    _ = step⁻¹ *
        (∫ x in U, vecDot (G x) (F.grad x) ∂MeasureTheory.volume -
          ∫ x in U, vecDot (G x) (S.grad x) ∂MeasureTheory.volume) := by
          rw [MeasureTheory.integral_sub hFInt hSInt]
    _ = step⁻¹ *
        (∫ x in V, vecDot (G x) (F.grad x) ∂MeasureTheory.volume -
          ∫ x in V, vecDot (G (euclideanCoordShift step i x)) (F.grad x)
            ∂MeasureTheory.volume) := by
          rw [hFtransport, hStransport]
    _ = step⁻¹ *
        (∫ x in V,
            vecDot (G x)
              ((localizedSqCutoffForwardDifferenceQuotientToAmbient
                (U := U) (V := V) u hV hVU step i hVshift
                hη hη_compact hη_sub).grad x)
            ∂MeasureTheory.volume -
          ∫ x in V,
            vecDot (G (euclideanCoordShift step i x))
              ((localizedSqCutoffForwardDifferenceQuotientToAmbient
                (U := U) (V := V) u hV hVU step i hVshift
                hη hη_compact hη_sub).grad x)
          ∂MeasureTheory.volume) := by
          rfl

/-- The transported split is the negative of the interior pairing with the
forward quotient of the vector field `G`. -/
theorem integral_vecDot_backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient_grad_eq_neg_integral_forwardDifferenceQuotient_on
    {G : Vec d → Vec d} (hG : MemVectorL2 U G)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hGshiftV : MemVectorL2 V (fun x => G (euclideanCoordShift step i x)))
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in U,
        vecDot (G x)
          ((backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume =
      -∫ x in V,
        vecDot
          (fun j => euclideanForwardDifferenceQuotient step i (fun y => G y j) x)
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume := by
  let F : H1Function U :=
    localizedSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  have hsplit :
      ∫ x in U,
          vecDot (G x)
            ((backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x)
          ∂MeasureTheory.volume =
        step⁻¹ *
          (∫ x in V, vecDot (G x) (F.grad x) ∂MeasureTheory.volume -
            ∫ x in V, vecDot (G (euclideanCoordShift step i x)) (F.grad x)
              ∂MeasureTheory.volume) := by
    simpa [F] using
      integral_vecDot_backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient_grad_eq_sub_integrals_on
        (U := U) (V := V) (G := G) hG u hV hVU step i hVshift
        hη hη_compact hη_sub
  have hGV : MemVectorL2 V G := by
    exact hG.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU)
  have hFV : MemVectorL2 V F.grad := by
    exact F.grad_memVectorL2.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU)
  have hAInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (G x) (F.grad x)) V :=
    integrableOn_vecDot_of_memVectorL2 hGV hFV
  have hBInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (G (euclideanCoordShift step i x)) (F.grad x)) V :=
    integrableOn_vecDot_of_memVectorL2 hGshiftV hFV
  have hquot :
      ∫ x in V,
          vecDot
            (fun j => euclideanForwardDifferenceQuotient step i (fun y => G y j) x)
            (F.grad x)
          ∂MeasureTheory.volume =
        step⁻¹ *
          (∫ x in V, vecDot (G (euclideanCoordShift step i x)) (F.grad x)
              ∂MeasureTheory.volume -
            ∫ x in V, vecDot (G x) (F.grad x) ∂MeasureTheory.volume) := by
    calc
      ∫ x in V,
          vecDot
            (fun j => euclideanForwardDifferenceQuotient step i (fun y => G y j) x)
            (F.grad x)
          ∂MeasureTheory.volume =
          ∫ x in V,
            step⁻¹ *
              (vecDot (G (euclideanCoordShift step i x)) (F.grad x) -
                vecDot (G x) (F.grad x))
          ∂MeasureTheory.volume := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            simp [vecDot, euclideanForwardDifferenceQuotient, div_eq_mul_inv]
            calc
              ∑ j,
                  (G (x + step • basisVec i) j - G x j) * step⁻¹ * F.grad x j =
                  ∑ j,
                    step⁻¹ *
                      (G (x + step • basisVec i) j * F.grad x j -
                        G x j * F.grad x j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j _hj
                    ring
              _ = step⁻¹ *
                  ∑ j,
                    (G (x + step • basisVec i) j * F.grad x j -
                      G x j * F.grad x j) := by
                    rw [Finset.mul_sum]
              _ = step⁻¹ *
                  (∑ j, G (x + step • basisVec i) j * F.grad x j -
                    ∑ j, G x j * F.grad x j) := by
                    rw [Finset.sum_sub_distrib]
      _ = step⁻¹ *
          ∫ x in V,
            (vecDot (G (euclideanCoordShift step i x)) (F.grad x) -
              vecDot (G x) (F.grad x))
            ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
      _ = step⁻¹ *
          (∫ x in V, vecDot (G (euclideanCoordShift step i x)) (F.grad x)
              ∂MeasureTheory.volume -
            ∫ x in V, vecDot (G x) (F.grad x) ∂MeasureTheory.volume) := by
            rw [MeasureTheory.integral_sub hBInt hAInt]
  rw [hsplit, hquot]
  ring

/-- Shifted gradients remain `L²` on a shift-safe interior set. -/
theorem memVectorL2_grad_comp_euclideanCoordShift_of_shift_subset
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U) :
    MemVectorL2 V (fun x => u.grad (euclideanCoordShift step i x)) := by
  let uShift : H1Function V :=
    (u.translate ((-step) • basisVec i)).restrict hV.isOpen hVshift
  simpa [uShift, H1Function.restrict, H1Function.translate, euclideanCoordShift,
    sub_eq_add_neg, neg_smul] using uShift.grad_memVectorL2

/-- The gradient of the forward quotient is the coordinatewise forward
quotient of the gradient. -/
theorem forwardDifferenceQuotientOn_grad_eq_vectorForwardDifferenceQuotient
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U) (x : Vec d) :
    (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x =
      fun j => euclideanForwardDifferenceQuotient step i (fun y => u.grad y j) x := by
  ext j
  simp [euclideanForwardDifferenceQuotient, div_eq_mul_inv]
  ring

/-- Weak-gradient identity for one coordinate of a forward difference quotient.

This is the distributional handoff used by the Hessian limit argument: each
coordinate of `∇D_i^+u` pairs against a test as `D_i^+u` paired against the
corresponding test derivative. -/
theorem integral_forwardDifferenceQuotientOn_grad_coord_mul_eq_neg_integral_forwardDifferenceQuotient_mul_fderiv
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    ∫ x in V,
        (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j * φ x
        ∂MeasureTheory.volume =
      -∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume := by
  have hweak :=
    (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).hasWeakGradient
      j φ hφ hφ_compact hφ_sub
  have hweak' :
      ∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume =
        -∫ x in V,
          (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j * φ x
          ∂MeasureTheory.volume := by
    simpa using hweak
  linarith

/-- Coordinatewise `L²` pairing bound by the full vector energy and the scalar
test energy. -/
theorem abs_integral_coord_mul_le_half_integral_vecNormSq_add_half_integral_sq_of_memVectorL2_memScalarL2
    {G : Vec d → Vec d} {φ : Vec d → ℝ}
    (hG : MemVectorL2 U G) (hφ : MemScalarL2 U φ) (j : Fin d) :
    |∫ x in U, G x j * φ x ∂MeasureTheory.volume| ≤
      (1 / 2 : ℝ) * ∫ x in U, vecNormSq (G x) ∂MeasureTheory.volume +
        (1 / 2 : ℝ) * ∫ x in U, φ x ^ 2 ∂MeasureTheory.volume := by
  have hGj : MemScalarL2 U (fun x => G x j) :=
    memScalarL2_coord_of_memVectorL2 hG j
  have hprod : MeasureTheory.IntegrableOn (fun x => G x j * φ x) U :=
    hGj.integrable_mul hφ
  have hprod_abs :
      MeasureTheory.IntegrableOn (fun x => |G x j * φ x|) U := by
    simpa [Real.norm_eq_abs] using! hprod.norm
  have hGsq :
      MeasureTheory.IntegrableOn (fun x => vecNormSq (G x)) U := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hG hG
  have hφsq :
      MeasureTheory.IntegrableOn (fun x => φ x ^ 2) U := by
    simpa [pow_two, MeasureTheory.IntegrableOn, volumeMeasureOn] using!
      hφ.integrable_mul hφ
  have hright_int :
      MeasureTheory.IntegrableOn
        (fun x => (1 / 2 : ℝ) * vecNormSq (G x) + (1 / 2 : ℝ) * φ x ^ 2) U :=
    (hGsq.const_mul (1 / 2 : ℝ)).add (hφsq.const_mul (1 / 2 : ℝ))
  have hpoint :
      (fun x => |G x j * φ x|) ≤ᵐ[MeasureTheory.volume.restrict U]
        fun x => (1 / 2 : ℝ) * vecNormSq (G x) + (1 / 2 : ℝ) * φ x ^ 2 := by
    filter_upwards with x
    have hyoung :
        |G x j * φ x| ≤
          (1 / 2 : ℝ) * (G x j) ^ 2 + (1 / 2 : ℝ) * φ x ^ 2 := by
      have hsq := sq_nonneg (|G x j| - |φ x|)
      rw [sub_sq, sq_abs, sq_abs] at hsq
      have habs_mul : |G x j * φ x| = |G x j| * |φ x| :=
        abs_mul (G x j) (φ x)
      nlinarith
    have hcoord : (G x j) ^ 2 ≤ vecNormSq (G x) :=
      coord_sq_le_vecNormSq (G x) j
    nlinarith
  have hmono :=
    MeasureTheory.integral_mono_ae hprod_abs hright_int hpoint
  have habs_integral :
      |∫ x in U, G x j * φ x ∂MeasureTheory.volume| ≤
        ∫ x in U, |G x j * φ x| ∂MeasureTheory.volume := by
    simpa using
      (MeasureTheory.abs_integral_le_integral_abs
        (f := fun x => G x j * φ x)
        (μ := MeasureTheory.volume.restrict U))
  have hright_eq :
      ∫ x in U,
          ((1 / 2 : ℝ) * vecNormSq (G x) + (1 / 2 : ℝ) * φ x ^ 2)
          ∂MeasureTheory.volume =
        (1 / 2 : ℝ) * ∫ x in U, vecNormSq (G x) ∂MeasureTheory.volume +
          (1 / 2 : ℝ) * ∫ x in U, φ x ^ 2 ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_add (hGsq.const_mul (1 / 2 : ℝ))
      (hφsq.const_mul (1 / 2 : ℝ))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  exact habs_integral.trans (hmono.trans_eq hright_eq)

/-- Version of the coordinatewise `L²` pairing bound localized by support:
when the scalar test is supported in `S ⊆ V`, only the energy on `S` appears. -/
theorem abs_integral_coord_mul_le_half_integral_subset_vecNormSq_add_half_integral_subset_sq_of_support_subset
    {S V : Set (Vec d)} {G : Vec d → Vec d} {φ : Vec d → ℝ}
    (hSV : S ⊆ V) (hφ_support : Function.support φ ⊆ S)
    (hG : MemVectorL2 V G) (hφS : MemScalarL2 S φ) (j : Fin d) :
    |∫ x in V, G x j * φ x ∂MeasureTheory.volume| ≤
      (1 / 2 : ℝ) * ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume +
        (1 / 2 : ℝ) * ∫ x in S, φ x ^ 2 ∂MeasureTheory.volume := by
  have hprod_support :
      Function.support (fun x => G x j * φ x) ⊆ S := by
    intro x hx
    exact hφ_support (by
      intro hφx
      exact hx (by simp [hφx]))
  have hrestrict :
      ∫ x in V, G x j * φ x ∂MeasureTheory.volume =
        ∫ x in S, G x j * φ x ∂MeasureTheory.volume :=
    integral_subset_of_support_subset (U := V) (V := S) hSV hprod_support
  have hGS : MemVectorL2 S G :=
    hG.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hSV)
  rw [hrestrict]
  exact
    abs_integral_coord_mul_le_half_integral_vecNormSq_add_half_integral_sq_of_memVectorL2_memScalarL2
      (U := S) hGS hφS j

/-- Coordinatewise Cauchy-Schwarz pairing bound in `L²`.  Unlike the Young
form above, this is homogeneous in the test norm and is the shape needed for a
Riesz/weak-limit handoff. -/
theorem abs_integral_coord_mul_le_l2_mul_l2_of_memVectorL2_memScalarL2
    {G : Vec d → Vec d} {φ : Vec d → ℝ}
    (hG : MemVectorL2 U G) (hφ : MemScalarL2 U φ) (j : Fin d) :
    |∫ x in U, G x j * φ x ∂MeasureTheory.volume| ≤
      (∫ x in U, ‖G x j‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) *
        (∫ x in U, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
  have hGj : MemScalarL2 U (fun x => G x j) :=
    memScalarL2_coord_of_memVectorL2 hG j
  have hprod : MeasureTheory.IntegrableOn (fun x => G x j * φ x) U :=
    hGj.integrable_mul hφ
  have habs_integral :
      |∫ x in U, G x j * φ x ∂MeasureTheory.volume| ≤
        ∫ x in U, |G x j * φ x| ∂MeasureTheory.volume := by
    simpa using
      (MeasureTheory.abs_integral_le_integral_abs
        (f := fun x => G x j * φ x)
        (μ := MeasureTheory.volume.restrict U))
  have hnorm_eq :
      ∫ x in U, |G x j * φ x| ∂MeasureTheory.volume =
        ∫ x in U, ‖G x j‖ * ‖φ x‖ ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    simp [abs_mul, Real.norm_eq_abs]
  have hGj_ofReal :
      MeasureTheory.MemLp (fun x => G x j) (ENNReal.ofReal (2 : ℝ))
        (MeasureTheory.volume.restrict U) := by
    simpa [MemScalarL2, volumeMeasureOn] using hGj
  have hφ_ofReal :
      MeasureTheory.MemLp φ (ENNReal.ofReal (2 : ℝ))
        (MeasureTheory.volume.restrict U) := by
    simpa [MemScalarL2, volumeMeasureOn] using hφ
  have hholder :
      ∫ x in U, ‖G x j‖ * ‖φ x‖ ∂MeasureTheory.volume ≤
        (∫ x in U, ‖G x j‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) *
          (∫ x in U, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
    simpa using
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        (μ := MeasureTheory.volume.restrict U)
        (f := fun x => G x j) (g := φ)
        Real.HolderConjugate.two_two hGj_ofReal hφ_ofReal
  exact habs_integral.trans (hnorm_eq.trans_le hholder)

/-- Support-localized Cauchy-Schwarz pairing bound. -/
theorem abs_integral_coord_mul_le_l2_mul_l2_subset_of_support_subset
    {S V : Set (Vec d)} {G : Vec d → Vec d} {φ : Vec d → ℝ}
    (hSV : S ⊆ V) (hφ_support : Function.support φ ⊆ S)
    (hG : MemVectorL2 V G) (hφS : MemScalarL2 S φ) (j : Fin d) :
    |∫ x in V, G x j * φ x ∂MeasureTheory.volume| ≤
      (∫ x in S, ‖G x j‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) *
        (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
  have hprod_support :
      Function.support (fun x => G x j * φ x) ⊆ S := by
    intro x hx
    exact hφ_support (by
      intro hφx
      exact hx (by simp [hφx]))
  have hrestrict :
      ∫ x in V, G x j * φ x ∂MeasureTheory.volume =
        ∫ x in S, G x j * φ x ∂MeasureTheory.volume :=
    integral_subset_of_support_subset (U := V) (V := S) hSV hprod_support
  have hGS : MemVectorL2 S G :=
    hG.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hSV)
  rw [hrestrict]
  exact
    abs_integral_coord_mul_le_l2_mul_l2_of_memVectorL2_memScalarL2
      (U := S) hGS hφS j

/-- The `L²` energy of one coordinate is bounded by the full vector-field
energy. -/
theorem integral_coord_norm_rpow_two_le_integral_vecNormSq_of_memVectorL2
    {G : Vec d → Vec d} (hG : MemVectorL2 U G) (j : Fin d) :
    ∫ x in U, ‖G x j‖ ^ (2 : ℝ) ∂MeasureTheory.volume ≤
      ∫ x in U, vecNormSq (G x) ∂MeasureTheory.volume := by
  have hGj : MemScalarL2 U (fun x => G x j) :=
    memScalarL2_coord_of_memVectorL2 hG j
  have hleft_int :
      MeasureTheory.IntegrableOn (fun x => ‖G x j‖ ^ (2 : ℝ)) U := by
    simpa [Real.rpow_two, Real.norm_eq_abs, sq_abs, pow_two,
      MeasureTheory.IntegrableOn, volumeMeasureOn] using! hGj.integrable_mul hGj
  have hright_int :
      MeasureTheory.IntegrableOn (fun x => vecNormSq (G x)) U := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hG hG
  have hpoint :
      (fun x => ‖G x j‖ ^ (2 : ℝ)) ≤ᵐ[MeasureTheory.volume.restrict U]
        fun x => vecNormSq (G x) := by
    filter_upwards with x
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    exact coord_sq_le_vecNormSq (G x) j
  exact MeasureTheory.integral_mono_ae hleft_int hright_int hpoint

/-- Homogeneous weak-Hessian handoff from the quotient-gradient coordinate to
the distributional second-derivative test functional. -/
theorem abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_le_l2_mul_l2_on_inner
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {S : Set (Vec d)} (hSV : S ⊆ V)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_subS : tsupport φ ⊆ S) :
    |(-∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume)| ≤
      (∫ x in S,
          ‖(u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j‖ ^
            (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) *
        (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
  let G : Vec d → Vec d :=
    fun x => (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x
  have hpair :=
    integral_forwardDifferenceQuotientOn_grad_coord_mul_eq_neg_integral_forwardDifferenceQuotient_mul_fderiv
      (U := U) (V := V) u hV hVU i j hVshift
      hφ hφ_compact (hφ_subS.trans hSV)
  have hφS : MemScalarL2 S φ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (hφ.continuous.memLp_of_hasCompactSupport hφ_compact).restrict S
  have hbound :
      |∫ x in V, G x j * φ x ∂MeasureTheory.volume| ≤
        (∫ x in S, ‖G x j‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) *
          (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) :=
    abs_integral_coord_mul_le_l2_mul_l2_subset_of_support_subset
      (S := S) (V := V) (G := G) (φ := φ)
      hSV ((subset_tsupport φ).trans hφ_subS)
      (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad_memVectorL2
      hφS j
  rw [← hpair]
  simpa [G] using hbound

/-- Homogeneous weak-Hessian handoff controlled by the full quotient-gradient
energy on the inner set. -/
theorem abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_le_grad_l2_mul_l2_on_inner
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {S : Set (Vec d)} (hSV : S ⊆ V)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_subS : tsupport φ ⊆ S) :
    |(-∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume)| ≤
      (∫ x in S,
          vecNormSq
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) *
        (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
  let G : Vec d → Vec d :=
    fun x => (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x
  have hbase :
      |(-∫ x in V,
          euclideanForwardDifferenceQuotient step i u.toFun x *
            (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume)| ≤
        (∫ x in S, ‖G x j‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) *
          (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
    simpa [G] using
      abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_le_l2_mul_l2_on_inner
        (U := U) (V := V) u hV hVU i j hVshift hSV
        hφ hφ_compact hφ_subS
  have hG : MemVectorL2 S G :=
    (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad_memVectorL2.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hSV)
  have hcoord_le :
      ∫ x in S, ‖G x j‖ ^ (2 : ℝ) ∂MeasureTheory.volume ≤
        ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume :=
    integral_coord_norm_rpow_two_le_integral_vecNormSq_of_memVectorL2
      (U := S) hG j
  have hcoord_nonneg :
      0 ≤ ∫ x in S, ‖G x j‖ ^ (2 : ℝ) ∂MeasureTheory.volume :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have hroot_le :
      (∫ x in S, ‖G x j‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) ≤
        (∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow hcoord_nonneg hcoord_le (by norm_num)
  have htest_root_nonneg :
      0 ≤ (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) :=
    Real.rpow_nonneg
      (MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)) _
  have hmul :
      (∫ x in S, ‖G x j‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) *
          (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) ≤
        (∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) *
          (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) :=
    mul_le_mul_of_nonneg_right hroot_le htest_root_nonneg
  exact hbase.trans (by simpa [G] using hmul)

/-- Homogeneous weak-Hessian handoff from an inner full-gradient energy bound. -/
theorem abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_le_sqrt_energy_bound_mul_l2
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step R : ℝ} (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {S : Set (Vec d)} (hSV : S ⊆ V)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_subS : tsupport φ ⊆ S)
    (henergy :
      (1 / 4 : ℝ) *
          ∫ x in S,
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume ≤ R) :
    |(-∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume)| ≤
      ((4 : ℝ) * R) ^ (1 / (2 : ℝ)) *
        (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
  let E : ℝ :=
    ∫ x in S,
      vecNormSq
        ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
      ∂MeasureTheory.volume
  have hbase :
      |(-∫ x in V,
          euclideanForwardDifferenceQuotient step i u.toFun x *
            (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume)| ≤
        E ^ (1 / (2 : ℝ)) *
          (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
    simpa [E] using
      abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_le_grad_l2_mul_l2_on_inner
        (U := U) (V := V) u hV hVU i j hVshift hSV
        hφ hφ_compact hφ_subS
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)
  have hE_le : E ≤ (4 : ℝ) * R := by
    change (1 / 4 : ℝ) * E ≤ R at henergy
    nlinarith
  have hroot_le : E ^ (1 / (2 : ℝ)) ≤ ((4 : ℝ) * R) ^ (1 / (2 : ℝ)) :=
    Real.rpow_le_rpow hE_nonneg hE_le (by norm_num)
  have htest_root_nonneg :
      0 ≤ (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) :=
    Real.rpow_nonneg
      (MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)) _
  have hmul :
      E ^ (1 / (2 : ℝ)) *
          (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) ≤
        ((4 : ℝ) * R) ^ (1 / (2 : ℝ)) *
          (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) :=
    mul_le_mul_of_nonneg_right hroot_le htest_root_nonneg
  exact hbase.trans hmul

/-- If the inner `L²` seminorm of the smooth test is zero, then the
distributional quotient-Hessian pairing vanishes.  This is the elementary
well-definedness plank needed before extending the bounded test functional to
the `L²` quotient space. -/
theorem neg_integral_forwardDifferenceQuotient_mul_fderiv_eq_zero_of_l2_norm_zero_on_inner
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step R : ℝ} (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {S : Set (Vec d)} (hSV : S ⊆ V)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_subS : tsupport φ ⊆ S)
    (henergy :
      (1 / 4 : ℝ) *
          ∫ x in S,
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume ≤ R)
    (hφ_zero :
      ∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume = 0) :
    -∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume = 0 := by
  let T : ℝ :=
    -∫ x in V,
      euclideanForwardDifferenceQuotient step i u.toFun x *
        (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume
  change T = 0
  have hbound :
      |T| ≤
        ((4 : ℝ) * R) ^ (1 / (2 : ℝ)) *
          (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) := by
    simpa [T] using
      abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_le_sqrt_energy_bound_mul_l2
        (U := U) (V := V) u hV hVU
        (step := step) (R := R) i j hVshift hSV
        hφ hφ_compact hφ_subS henergy
  have hroot_zero :
      (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) = 0 := by
    rw [hφ_zero, Real.zero_rpow]
    norm_num
  have hle_zero : |T| ≤ 0 := by
    calc
      |T| ≤
          ((4 : ℝ) * R) ^ (1 / (2 : ℝ)) *
            (∫ x in S, ‖φ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume) ^ (1 / (2 : ℝ)) :=
        hbound
      _ = 0 := by
        rw [hroot_zero, mul_zero]
  exact abs_eq_zero.mp (le_antisymm hle_zero (abs_nonneg T))

/-- If two smooth compact tests have zero `L²` distance on the inner support
set, then they give the same distributional quotient-Hessian pairing.  The
proof rewrites the derivative-side pairing through the weak-gradient identity,
so the linearity step happens on the value side as ordinary `L²` algebra. -/
theorem neg_integral_forwardDifferenceQuotient_mul_fderiv_eq_of_l2_dist_zero_on_inner
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step R : ℝ} (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {S : Set (Vec d)} (hSV : S ⊆ V)
    {φ ψ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hφ_compact : HasCompactSupport φ) (hψ_compact : HasCompactSupport ψ)
    (hφ_subS : tsupport φ ⊆ S) (hψ_subS : tsupport ψ ⊆ S)
    (henergy :
      (1 / 4 : ℝ) *
          ∫ x in S,
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume ≤ R)
    (hφψ_zero :
      ∫ x in S, ‖φ x - ψ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume = 0) :
    -∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume =
      -∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ ψ x) (basisVec j) ∂MeasureTheory.volume := by
  let χ : Vec d → ℝ := fun x => φ x - ψ x
  let w : H1Function V := u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift
  let G : Vec d → ℝ := fun x => w.grad x j
  let Tφ : ℝ :=
    -∫ x in V,
      euclideanForwardDifferenceQuotient step i u.toFun x *
        (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume
  let Tψ : ℝ :=
    -∫ x in V,
      euclideanForwardDifferenceQuotient step i u.toFun x *
        (fderiv ℝ ψ x) (basisVec j) ∂MeasureTheory.volume
  let Tχ : ℝ :=
    -∫ x in V,
      euclideanForwardDifferenceQuotient step i u.toFun x *
        (fderiv ℝ χ x) (basisVec j) ∂MeasureTheory.volume
  change Tφ = Tψ
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := by
    simpa [χ] using hφ.sub hψ
  have hχ_compact : HasCompactSupport χ := by
    simpa [χ] using! hφ_compact.sub hψ_compact
  have hχ_subS : tsupport χ ⊆ S := by
    intro x hx
    have hx' : x ∈ tsupport φ ∪ tsupport ψ := by
      simpa [χ] using tsupport_sub φ ψ hx
    rcases hx' with hxφ | hxψ
    · exact hφ_subS hxφ
    · exact hψ_subS hxψ
  have hχ_zero :
      ∫ x in S, ‖χ x‖ ^ (2 : ℝ) ∂MeasureTheory.volume = 0 := by
    simpa [χ] using hφψ_zero
  have hTχ_zero : Tχ = 0 := by
    simpa [Tχ, χ] using
      neg_integral_forwardDifferenceQuotient_mul_fderiv_eq_zero_of_l2_norm_zero_on_inner
        (U := U) (V := V) u hV hVU
        (step := step) (R := R) i j hVshift hSV
        hχ hχ_compact hχ_subS henergy hχ_zero
  have hpairχ :
      ∫ x in V, G x * χ x ∂MeasureTheory.volume = Tχ := by
    simpa [G, w, Tχ] using
      integral_forwardDifferenceQuotientOn_grad_coord_mul_eq_neg_integral_forwardDifferenceQuotient_mul_fderiv
        (U := U) (V := V) u hV hVU
        (step := step) i j hVshift hχ hχ_compact (hχ_subS.trans hSV)
  have hpairφ :
      ∫ x in V, G x * φ x ∂MeasureTheory.volume = Tφ := by
    simpa [G, w, Tφ] using
      integral_forwardDifferenceQuotientOn_grad_coord_mul_eq_neg_integral_forwardDifferenceQuotient_mul_fderiv
        (U := U) (V := V) u hV hVU
        (step := step) i j hVshift hφ hφ_compact (hφ_subS.trans hSV)
  have hpairψ :
      ∫ x in V, G x * ψ x ∂MeasureTheory.volume = Tψ := by
    simpa [G, w, Tψ] using
      integral_forwardDifferenceQuotientOn_grad_coord_mul_eq_neg_integral_forwardDifferenceQuotient_mul_fderiv
        (U := U) (V := V) u hV hVU
        (step := step) i j hVshift hψ hψ_compact (hψ_subS.trans hSV)
  have hG : MemScalarL2 V G := by
    simpa [G, w] using (w.gradMemL2 j)
  have hφV : MemScalarL2 V φ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (hφ.continuous.memLp_of_hasCompactSupport hφ_compact).restrict V
  have hψV : MemScalarL2 V ψ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (hψ.continuous.memLp_of_hasCompactSupport hψ_compact).restrict V
  have hGφ_int :
      MeasureTheory.Integrable (fun x => G x * φ x)
        (MeasureTheory.volume.restrict V) := by
    simpa [volumeMeasureOn] using! hG.integrable_mul hφV
  have hGψ_int :
      MeasureTheory.Integrable (fun x => G x * ψ x)
        (MeasureTheory.volume.restrict V) := by
    simpa [volumeMeasureOn] using! hG.integrable_mul hψV
  have hlin :
      ∫ x in V, G x * χ x ∂MeasureTheory.volume =
        ∫ x in V, G x * φ x ∂MeasureTheory.volume -
          ∫ x in V, G x * ψ x ∂MeasureTheory.volume := by
    calc
      ∫ x in V, G x * χ x ∂MeasureTheory.volume =
          ∫ x in V, (G x * φ x) - (G x * ψ x) ∂MeasureTheory.volume := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        simp [χ]
        ring
      _ = ∫ x in V, G x * φ x ∂MeasureTheory.volume -
          ∫ x in V, G x * ψ x ∂MeasureTheory.volume := by
        rw [MeasureTheory.integral_sub hGφ_int hGψ_int]
  have hTχ_eq : Tχ = Tφ - Tψ := by
    calc
      Tχ = ∫ x in V, G x * χ x ∂MeasureTheory.volume := hpairχ.symm
      _ = ∫ x in V, G x * φ x ∂MeasureTheory.volume -
          ∫ x in V, G x * ψ x ∂MeasureTheory.volume := hlin
      _ = Tφ - Tψ := by rw [hpairφ, hpairψ]
  have hdiff_zero : Tφ - Tψ = 0 := by
    rw [← hTχ_eq]
    exact hTχ_zero
  exact sub_eq_zero.mp hdiff_zero

end WeakPoissonEquationOn

end

end Homogenization
