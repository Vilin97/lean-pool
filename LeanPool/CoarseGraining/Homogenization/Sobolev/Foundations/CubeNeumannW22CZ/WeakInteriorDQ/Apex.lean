/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.DifferenceQuotientH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph.Preliminaries
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.QuantitativeCutoff
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Order.Filter.Finite

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.InnerCubeAndHessian

/-! # Apex -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {U V : Set (Vec d)}
variable {u : H1Function U} {f : Vec d → ℝ}


/-- The forward difference quotient of a weak Poisson solution satisfies the
corresponding weak equation on an interior domain whose forward shifts remain
inside the original domain. -/
theorem forwardDifferenceQuotientOn_weakPoissonEquationOn
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    (hfShiftV : MemScalarL2 V (fun x => f (x - ((-step) • basisVec i)))) :
    WeakPoissonEquationOn V
      (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift)
      (euclideanForwardDifferenceQuotient step i f) := by
  intro φ hφ hφs hφ_sub
  let z : Vec d := (-step) • basisVec i
  let uShift : H1Function V := (u.translate z).restrict hV.isOpen hVshift
  let uOrig : H1Function V := u.restrict hV.isOpen hVU
  have hshift :=
    ((h.translate z).restrict hV.isOpen hVshift).test φ hφ hφs hφ_sub
  have horig :=
    (h.restrict hV.isOpen hVU).test φ hφ hφs hφ_sub
  have hgradTest : MemVectorL2 V (euclideanGradient φ) :=
    memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hφ hφs
  have hshiftInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (uShift.grad x) (euclideanGradient φ x)) V :=
    integrableOn_vecDot_of_memVectorL2 uShift.grad_memVectorL2 hgradTest
  have horigInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (uOrig.grad x) (euclideanGradient φ x)) V :=
    integrableOn_vecDot_of_memVectorL2 uOrig.grad_memVectorL2 hgradTest
  have hφL2 : MemScalarL2 V φ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (hφ.continuous.memLp_of_hasCompactSupport hφs).restrict V
  have hforceShiftInt :
      MeasureTheory.IntegrableOn (fun x => f (x - z) * φ x) V :=
    hfShiftV.integrable_mul hφL2
  have hforceOrigInt :
      MeasureTheory.IntegrableOn (fun x => f x * φ x) V :=
    hfV.integrable_mul hφL2
  have hleft :
      ∫ x in V,
          vecDot
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            (euclideanGradient φ x) ∂MeasureTheory.volume =
        step⁻¹ *
          (∫ x in V, vecDot (uShift.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume -
            ∫ x in V, vecDot (uOrig.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume) := by
    calc
      ∫ x in V,
          vecDot
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            (euclideanGradient φ x) ∂MeasureTheory.volume
          = ∫ x in V,
              step⁻¹ *
                (vecDot (uShift.grad x) (euclideanGradient φ x) -
                  vecDot (uOrig.grad x) (euclideanGradient φ x))
              ∂MeasureTheory.volume := by
            congr with x
            simp [H1Function.forwardDifferenceQuotientOn, uShift, uOrig,
              vecDot_smul_left, vecDot_add_left, vecDot_neg_left, sub_eq_add_neg]
            ring
      _ = step⁻¹ *
            ∫ x in V,
              (vecDot (uShift.grad x) (euclideanGradient φ x) -
                vecDot (uOrig.grad x) (euclideanGradient φ x))
              ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
      _ = step⁻¹ *
          (∫ x in V, vecDot (uShift.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume -
            ∫ x in V, vecDot (uOrig.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume) := by
            rw [MeasureTheory.integral_sub hshiftInt horigInt]
  have hright :
      ∫ x in V, euclideanForwardDifferenceQuotient step i f x * φ x
          ∂MeasureTheory.volume =
        step⁻¹ *
          (∫ x in V, f (x - z) * φ x ∂MeasureTheory.volume -
            ∫ x in V, f x * φ x ∂MeasureTheory.volume) := by
    calc
      ∫ x in V, euclideanForwardDifferenceQuotient step i f x * φ x
          ∂MeasureTheory.volume
          = ∫ x in V, step⁻¹ * (f (x - z) * φ x - f x * φ x)
              ∂MeasureTheory.volume := by
            congr with x
            simp [euclideanForwardDifferenceQuotient, euclideanCoordShift, z,
              sub_eq_add_neg]
            ring
      _ = step⁻¹ *
          ∫ x in V, (f (x - z) * φ x - f x * φ x)
              ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
      _ = step⁻¹ *
          (∫ x in V, f (x - z) * φ x ∂MeasureTheory.volume -
            ∫ x in V, f x * φ x ∂MeasureTheory.volume) := by
            rw [MeasureTheory.integral_sub hforceShiftInt hforceOrigInt]
  calc
    ∫ x in V,
        vecDot
          ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          (euclideanGradient φ x) ∂MeasureTheory.volume
        = step⁻¹ *
          (∫ x in V, vecDot (uShift.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume -
            ∫ x in V, vecDot (uOrig.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume) := hleft
    _ = step⁻¹ *
          (∫ x in V, f (x - z) * φ x ∂MeasureTheory.volume -
            ∫ x in V, f x * φ x ∂MeasureTheory.volume) := by
          rw [hshift, horig]
    _ = ∫ x in V, euclideanForwardDifferenceQuotient step i f x * φ x
          ∂MeasureTheory.volume := hright.symm

/-- The backward difference quotient of a weak Poisson solution satisfies the
corresponding weak equation on an interior domain whose backward shifts remain
inside the original domain. -/
theorem backwardDifferenceQuotientOn_weakPoissonEquationOn
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet (step • basisVec i) U)
    (hfShiftV : MemScalarL2 V (fun x => f (x - (step • basisVec i)))) :
    WeakPoissonEquationOn V
      (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift)
      (euclideanBackwardDifferenceQuotient step i f) := by
  intro φ hφ hφs hφ_sub
  let z : Vec d := step • basisVec i
  let uShift : H1Function V := (u.translate z).restrict hV.isOpen hVshift
  let uOrig : H1Function V := u.restrict hV.isOpen hVU
  have hshift :=
    ((h.translate z).restrict hV.isOpen hVshift).test φ hφ hφs hφ_sub
  have horig :=
    (h.restrict hV.isOpen hVU).test φ hφ hφs hφ_sub
  have hgradTest : MemVectorL2 V (euclideanGradient φ) :=
    memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hφ hφs
  have hshiftInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (uShift.grad x) (euclideanGradient φ x)) V :=
    integrableOn_vecDot_of_memVectorL2 uShift.grad_memVectorL2 hgradTest
  have horigInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (uOrig.grad x) (euclideanGradient φ x)) V :=
    integrableOn_vecDot_of_memVectorL2 uOrig.grad_memVectorL2 hgradTest
  have hφL2 : MemScalarL2 V φ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (hφ.continuous.memLp_of_hasCompactSupport hφs).restrict V
  have hforceShiftInt :
      MeasureTheory.IntegrableOn (fun x => f (x - z) * φ x) V :=
    hfShiftV.integrable_mul hφL2
  have hforceOrigInt :
      MeasureTheory.IntegrableOn (fun x => f x * φ x) V :=
    hfV.integrable_mul hφL2
  have hleft :
      ∫ x in V,
          vecDot
            ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            (euclideanGradient φ x) ∂MeasureTheory.volume =
        step⁻¹ *
          (∫ x in V, vecDot (uOrig.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume -
            ∫ x in V, vecDot (uShift.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume) := by
    calc
      ∫ x in V,
          vecDot
            ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            (euclideanGradient φ x) ∂MeasureTheory.volume
          = ∫ x in V,
              step⁻¹ *
                (vecDot (uOrig.grad x) (euclideanGradient φ x) -
                  vecDot (uShift.grad x) (euclideanGradient φ x))
              ∂MeasureTheory.volume := by
            congr with x
            simp [H1Function.backwardDifferenceQuotientOn, uShift, uOrig,
              vecDot_smul_left, vecDot_add_left, vecDot_neg_left, sub_eq_add_neg]
            ring
      _ = step⁻¹ *
            ∫ x in V,
              (vecDot (uOrig.grad x) (euclideanGradient φ x) -
                vecDot (uShift.grad x) (euclideanGradient φ x))
              ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
      _ = step⁻¹ *
          (∫ x in V, vecDot (uOrig.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume -
            ∫ x in V, vecDot (uShift.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume) := by
            rw [MeasureTheory.integral_sub horigInt hshiftInt]
  have hright :
      ∫ x in V, euclideanBackwardDifferenceQuotient step i f x * φ x
          ∂MeasureTheory.volume =
        step⁻¹ *
          (∫ x in V, f x * φ x ∂MeasureTheory.volume -
            ∫ x in V, f (x - z) * φ x ∂MeasureTheory.volume) := by
    calc
      ∫ x in V, euclideanBackwardDifferenceQuotient step i f x * φ x
          ∂MeasureTheory.volume
          = ∫ x in V, step⁻¹ * (f x * φ x - f (x - z) * φ x)
              ∂MeasureTheory.volume := by
            congr with x
            simp [euclideanBackwardDifferenceQuotient, euclideanCoordShift, z,
              sub_eq_add_neg]
            ring
      _ = step⁻¹ *
          ∫ x in V, (f x * φ x - f (x - z) * φ x)
              ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
      _ = step⁻¹ *
          (∫ x in V, f x * φ x ∂MeasureTheory.volume -
            ∫ x in V, f (x - z) * φ x ∂MeasureTheory.volume) := by
            rw [MeasureTheory.integral_sub hforceOrigInt hforceShiftInt]
  calc
    ∫ x in V,
        vecDot
          ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          (euclideanGradient φ x) ∂MeasureTheory.volume
        = step⁻¹ *
          (∫ x in V, vecDot (uOrig.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume -
            ∫ x in V, vecDot (uShift.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume) := hleft
    _ = step⁻¹ *
          (∫ x in V, f x * φ x ∂MeasureTheory.volume -
            ∫ x in V, f (x - z) * φ x ∂MeasureTheory.volume) := by
          rw [hshift, horig]
    _ = ∫ x in V, euclideanBackwardDifferenceQuotient step i f x * φ x
          ∂MeasureTheory.volume := hright.symm

/-- Cutoff energy identity for the forward difference quotient `D_h^+ u`. -/
theorem forwardDifferenceQuotientOn_cutoff_energy_identity
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    (hfShiftV : MemScalarL2 V (fun x => f (x - ((-step) • basisVec i))))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    ∫ x in V,
        vecDot
          ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          (fun j =>
            φ x * (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
              euclideanForwardDifferenceQuotient step i u.toFun x *
                (fderiv ℝ φ x) (basisVec j)) ∂MeasureTheory.volume =
      ∫ x in V,
        euclideanForwardDifferenceQuotient step i f x *
          (φ x * euclideanForwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume := by
  let z : Vec d := (-step) • basisVec i
  have hfDQ : MemScalarL2 V (euclideanForwardDifferenceQuotient step i f) := by
    have hsub : MemScalarL2 V (fun x => f (x - z) - f x) :=
      hfShiftV.sub hfV
    refine MeasureTheory.MemLp.ae_eq ?_ (hsub.const_mul step⁻¹)
    filter_upwards with x
    simp [euclideanForwardDifferenceQuotient, euclideanCoordShift, z,
      div_eq_mul_inv, sub_eq_add_neg]
    ring
  have hdq :=
    h.forwardDifferenceQuotientOn_weakPoissonEquationOn
      hV hVU hfV step i hVshift hfShiftV
  simpa [z] using
    hdq.test_mulContDiffHasCompactSupport_expanded
      hV hfDQ hφ hφ_compact hφ_sub

/-- Cutoff energy identity for `D_h^+ u`, with the `vecDot` integrand split
into the coercive and cutoff-error terms. -/
theorem forwardDifferenceQuotientOn_cutoff_energy_identity_split_integrand
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    (hfShiftV : MemScalarL2 V (fun x => f (x - ((-step) • basisVec i))))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    ∫ x in V,
        (φ x *
            vecDot
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x) +
          euclideanForwardDifferenceQuotient step i u.toFun x *
            vecDot
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
              (euclideanGradient φ x)) ∂MeasureTheory.volume =
      ∫ x in V,
        euclideanForwardDifferenceQuotient step i f x *
          (φ x * euclideanForwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume := by
  have henergy :=
    h.forwardDifferenceQuotientOn_cutoff_energy_identity
      hV hVU hfV step i hVshift hfShiftV hφ hφ_compact hφ_sub
  have hleft :
      ∫ x in V,
          vecDot
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            (fun j =>
              φ x * (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
                euclideanForwardDifferenceQuotient step i u.toFun x *
                  (fderiv ℝ φ x) (basisVec j)) ∂MeasureTheory.volume =
        ∫ x in V,
          (φ x *
              vecDot
                ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
                ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x) +
            euclideanForwardDifferenceQuotient step i u.toFun x *
              vecDot
                ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
                (euclideanGradient φ x)) ∂MeasureTheory.volume := by
    congr with x
    exact vecDot_cutoff_energy_integrand
      ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
      (euclideanGradient φ x) (φ x)
      (euclideanForwardDifferenceQuotient step i u.toFun x)
  exact hleft.symm.trans henergy

/-- Cutoff energy identity for `D_h^+ u` specialized to a squared smooth
cutoff `η²`.  This is the form whose cross term is controlled by
`abs_sq_cutoff_error_integrand_le`. -/
theorem forwardDifferenceQuotientOn_sq_cutoff_energy_identity
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    (hfShiftV : MemScalarL2 V (fun x => f (x - ((-step) • basisVec i))))
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in V,
        (η x ^ 2 *
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x) +
          euclideanForwardDifferenceQuotient step i u.toFun x *
            vecDot
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
              (fun j => 2 * η x * euclideanGradient η x j))
          ∂MeasureTheory.volume =
      ∫ x in V,
        euclideanForwardDifferenceQuotient step i f x *
          (η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume := by
  have hη_sq_sub : tsupport (fun x => η x ^ 2) ⊆ V :=
    (tsupport_sq_subset η).trans hη_sub
  have hbase :=
    h.forwardDifferenceQuotientOn_cutoff_energy_identity_split_integrand
      hV hVU hfV step i hVshift hfShiftV
      (φ := fun x => η x ^ 2)
      (contDiff_sq hη) (hasCompactSupport_sq hη_compact) hη_sq_sub
  simpa [vecNormSq, euclideanGradient_sq hη] using hbase

/-- Forward squared-cutoff Caccioppoli absorption.  The integrability needed by
the abstract absorption lemma is supplied by the quotient's `L²` data and the
smooth compact cutoff. -/
theorem forwardDifferenceQuotientOn_sq_cutoff_energy_half_le_forcing_add_error
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    (hfShiftV : MemScalarL2 V (fun x => f (x - ((-step) • basisVec i))))
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (1 / 2 : ℝ) *
        ∫ x in V,
          η x ^ 2 *
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      ∫ x in V,
        euclideanForwardDifferenceQuotient step i f x *
          (η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume +
        ∫ x in V,
          2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
            vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
  let w : Vec d → ℝ := euclideanForwardDifferenceQuotient step i u.toFun
  let G : Vec d → Vec d :=
    fun x => (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x
  let m : Vec d → ℝ := fun x => η x ^ 2 * vecNormSq (G x)
  let c : Vec d → ℝ :=
    fun x => w x * vecDot (G x) (fun j => 2 * η x * euclideanGradient η x j)
  let r : Vec d → ℝ :=
    fun x => euclideanForwardDifferenceQuotient step i f x * (η x ^ 2 * w x)
  let e : Vec d → ℝ :=
    fun x => 2 * (w x) ^ 2 * vecNormSq (euclideanGradient η x)
  have henergy_raw :=
    h.forwardDifferenceQuotientOn_sq_cutoff_energy_identity
      hV hVU hfV step i hVshift hfShiftV hη hη_compact hη_sub
  have henergy :
      ∫ x in V, (m x + c x) ∂MeasureTheory.volume =
        ∫ x in V, r x ∂MeasureTheory.volume := by
    simpa [m, c, r, w, G] using henergy_raw
  have hpoint :
      (fun x => -c x) ≤ᵐ[MeasureTheory.volume.restrict V]
        fun x => m x / 2 + e x := by
    filter_upwards with x
    have hbound :=
      neg_sq_cutoff_error_integrand_le
        (η x) (w x) (G x) (euclideanGradient η x)
    simpa [m, c, e, w, G, div_eq_mul_inv, neg_mul, mul_assoc, mul_comm, mul_left_comm]
      using hbound
  have hm : MeasureTheory.IntegrableOn m V := by
    have hG : MemVectorL2 V G :=
      (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad_memVectorL2
    simpa [m, G] using
      integrableOn_sq_cutoff_vecNormSq_of_memVectorL2
        (V := V) (G := G) (η := η) hG hη hη_compact
  have hc : MeasureTheory.IntegrableOn c V := by
    have hw : MemScalarL2 V w := by
      refine MeasureTheory.MemLp.ae_eq ?_
        (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).memL2
      filter_upwards with x
      simp [w]
    have hG : MemVectorL2 V G :=
      (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad_memVectorL2
    simpa [c, w, G] using
      integrableOn_sq_cutoff_cross_of_memScalarL2_memVectorL2
        (V := V) (w := w) (G := G) (η := η) hw hG hη hη_compact
  have he : MeasureTheory.IntegrableOn e V := by
    have hw : MemScalarL2 V w := by
      refine MeasureTheory.MemLp.ae_eq ?_
        (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).memL2
      filter_upwards with x
      simp [w]
    simpa [e, w] using
      integrableOn_two_mul_sq_mul_vecNormSq_euclideanGradient_of_memScalarL2
        (V := V) (w := w) (η := η) hw hη hη_compact
  have hhalf :=
    integral_half_main_le_rhs_add_error_of_add_energy_identity
      (V := V) (m := m) (c := c) (r := r) (e := e)
      henergy hpoint hm hc he
  simpa [m, r, e, w, G] using hhalf

/-- Cutoff energy identity for the backward difference quotient `D_h^- u`. -/
theorem backwardDifferenceQuotientOn_cutoff_energy_identity
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet (step • basisVec i) U)
    (hfShiftV : MemScalarL2 V (fun x => f (x - (step • basisVec i))))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    ∫ x in V,
        vecDot
          ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          (fun j =>
            φ x * (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
              euclideanBackwardDifferenceQuotient step i u.toFun x *
                (fderiv ℝ φ x) (basisVec j)) ∂MeasureTheory.volume =
      ∫ x in V,
        euclideanBackwardDifferenceQuotient step i f x *
          (φ x * euclideanBackwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume := by
  let z : Vec d := step • basisVec i
  have hfDQ : MemScalarL2 V (euclideanBackwardDifferenceQuotient step i f) := by
    have hsub : MemScalarL2 V (fun x => f x - f (x - z)) :=
      hfV.sub hfShiftV
    refine MeasureTheory.MemLp.ae_eq ?_ (hsub.const_mul step⁻¹)
    filter_upwards with x
    simp [euclideanBackwardDifferenceQuotient, euclideanCoordShift, z,
      div_eq_mul_inv, sub_eq_add_neg]
    ring
  have hdq :=
    h.backwardDifferenceQuotientOn_weakPoissonEquationOn
      hV hVU hfV step i hVshift hfShiftV
  simpa [z] using
    hdq.test_mulContDiffHasCompactSupport_expanded
      hV hfDQ hφ hφ_compact hφ_sub

/-- Cutoff energy identity for `D_h^- u`, with the `vecDot` integrand split
into the coercive and cutoff-error terms. -/
theorem backwardDifferenceQuotientOn_cutoff_energy_identity_split_integrand
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet (step • basisVec i) U)
    (hfShiftV : MemScalarL2 V (fun x => f (x - (step • basisVec i))))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    ∫ x in V,
        (φ x *
            vecDot
              ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
              ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x) +
          euclideanBackwardDifferenceQuotient step i u.toFun x *
            vecDot
              ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
              (euclideanGradient φ x)) ∂MeasureTheory.volume =
      ∫ x in V,
        euclideanBackwardDifferenceQuotient step i f x *
          (φ x * euclideanBackwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume := by
  have henergy :=
    h.backwardDifferenceQuotientOn_cutoff_energy_identity
      hV hVU hfV step i hVshift hfShiftV hφ hφ_compact hφ_sub
  have hleft :
      ∫ x in V,
          vecDot
            ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            (fun j =>
              φ x * (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
                euclideanBackwardDifferenceQuotient step i u.toFun x *
                  (fderiv ℝ φ x) (basisVec j)) ∂MeasureTheory.volume =
        ∫ x in V,
          (φ x *
              vecDot
                ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
                ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x) +
            euclideanBackwardDifferenceQuotient step i u.toFun x *
              vecDot
                ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
                (euclideanGradient φ x)) ∂MeasureTheory.volume := by
    congr with x
    exact vecDot_cutoff_energy_integrand
      ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
      (euclideanGradient φ x) (φ x)
      (euclideanBackwardDifferenceQuotient step i u.toFun x)
  exact hleft.symm.trans henergy

/-- Cutoff energy identity for `D_h^- u` specialized to a squared smooth
cutoff `η²`. -/
theorem backwardDifferenceQuotientOn_sq_cutoff_energy_identity
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet (step • basisVec i) U)
    (hfShiftV : MemScalarL2 V (fun x => f (x - (step • basisVec i))))
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in V,
        (η x ^ 2 *
            vecNormSq
              ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x) +
          euclideanBackwardDifferenceQuotient step i u.toFun x *
            vecDot
              ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
              (fun j => 2 * η x * euclideanGradient η x j))
          ∂MeasureTheory.volume =
      ∫ x in V,
        euclideanBackwardDifferenceQuotient step i f x *
          (η x ^ 2 * euclideanBackwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume := by
  have hη_sq_sub : tsupport (fun x => η x ^ 2) ⊆ V :=
    (tsupport_sq_subset η).trans hη_sub
  have hbase :=
    h.backwardDifferenceQuotientOn_cutoff_energy_identity_split_integrand
      hV hVU hfV step i hVshift hfShiftV
      (φ := fun x => η x ^ 2)
      (contDiff_sq hη) (hasCompactSupport_sq hη_compact) hη_sq_sub
  simpa [vecNormSq, euclideanGradient_sq hη] using hbase

/-- Backward squared-cutoff Caccioppoli absorption.  The integrability needed by
the abstract absorption lemma is supplied by the quotient's `L²` data and the
smooth compact cutoff. -/
theorem backwardDifferenceQuotientOn_sq_cutoff_energy_half_le_forcing_add_error
    (h : WeakPoissonEquationOn U u f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (hfV : MemScalarL2 V f) (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet (step • basisVec i) U)
    (hfShiftV : MemScalarL2 V (fun x => f (x - (step • basisVec i))))
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (1 / 2 : ℝ) *
        ∫ x in V,
          η x ^ 2 *
            vecNormSq
              ((u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      ∫ x in V,
        euclideanBackwardDifferenceQuotient step i f x *
          (η x ^ 2 * euclideanBackwardDifferenceQuotient step i u.toFun x)
          ∂MeasureTheory.volume +
        ∫ x in V,
          2 * (euclideanBackwardDifferenceQuotient step i u.toFun x) ^ 2 *
            vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
  let w : Vec d → ℝ := euclideanBackwardDifferenceQuotient step i u.toFun
  let G : Vec d → Vec d :=
    fun x => (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x
  let m : Vec d → ℝ := fun x => η x ^ 2 * vecNormSq (G x)
  let c : Vec d → ℝ :=
    fun x => w x * vecDot (G x) (fun j => 2 * η x * euclideanGradient η x j)
  let r : Vec d → ℝ :=
    fun x => euclideanBackwardDifferenceQuotient step i f x * (η x ^ 2 * w x)
  let e : Vec d → ℝ :=
    fun x => 2 * (w x) ^ 2 * vecNormSq (euclideanGradient η x)
  have henergy_raw :=
    h.backwardDifferenceQuotientOn_sq_cutoff_energy_identity
      hV hVU hfV step i hVshift hfShiftV hη hη_compact hη_sub
  have henergy :
      ∫ x in V, (m x + c x) ∂MeasureTheory.volume =
        ∫ x in V, r x ∂MeasureTheory.volume := by
    simpa [m, c, r, w, G] using henergy_raw
  have hpoint :
      (fun x => -c x) ≤ᵐ[MeasureTheory.volume.restrict V]
        fun x => m x / 2 + e x := by
    filter_upwards with x
    have hbound :=
      neg_sq_cutoff_error_integrand_le
        (η x) (w x) (G x) (euclideanGradient η x)
    simpa [m, c, e, w, G, div_eq_mul_inv, neg_mul, mul_assoc, mul_comm, mul_left_comm]
      using hbound
  have hm : MeasureTheory.IntegrableOn m V := by
    have hG : MemVectorL2 V G :=
      (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad_memVectorL2
    simpa [m, G] using
      integrableOn_sq_cutoff_vecNormSq_of_memVectorL2
        (V := V) (G := G) (η := η) hG hη hη_compact
  have hc : MeasureTheory.IntegrableOn c V := by
    have hw : MemScalarL2 V w := by
      refine MeasureTheory.MemLp.ae_eq ?_
        (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).memL2
      filter_upwards with x
      simp [w]
    have hG : MemVectorL2 V G :=
      (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad_memVectorL2
    simpa [c, w, G] using
      integrableOn_sq_cutoff_cross_of_memScalarL2_memVectorL2
        (V := V) (w := w) (G := G) (η := η) hw hG hη hη_compact
  have he : MeasureTheory.IntegrableOn e V := by
    have hw : MemScalarL2 V w := by
      refine MeasureTheory.MemLp.ae_eq ?_
        (u.backwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).memL2
      filter_upwards with x
      simp [w]
    simpa [e, w] using
      integrableOn_two_mul_sq_mul_vecNormSq_euclideanGradient_of_memScalarL2
        (V := V) (w := w) (η := η) hw hη hη_compact
  have hhalf :=
    integral_half_main_le_rhs_add_error_of_add_energy_identity
      (V := V) (m := m) (c := c) (r := r) (e := e)
      henergy hpoint hm hc he
  simpa [m, r, e, w, G] using hhalf

end WeakPoissonEquationOn

end

end Homogenization
