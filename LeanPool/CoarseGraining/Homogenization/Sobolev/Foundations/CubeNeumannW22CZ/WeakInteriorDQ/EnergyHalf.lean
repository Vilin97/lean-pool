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

public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.IntegralIdentity

/-! # Energy Half -/

@[expose] public section

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {U V : Set (Vec d)}
variable {u : H1Function U} {f : Vec d → ℝ}


/-- Additivity of the quotient-Hessian pairing on smooth weak tests. -/
theorem neg_integral_forwardDifferenceQuotient_mul_fderiv_h1WeakTest_add
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {S : Set (Vec d)} (hSV : S ⊆ V)
    (φ ψ : H1WeakTestFunction S) :
    -∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ (φ.add ψ : Vec d → ℝ) x) (basisVec j)
        ∂MeasureTheory.volume =
      (-∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ (φ : Vec d → ℝ) x) (basisVec j)
        ∂MeasureTheory.volume) +
      (-∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ (ψ : Vec d → ℝ) x) (basisVec j)
        ∂MeasureTheory.volume) := by
  let w : H1Function V := u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift
  let G : Vec d → ℝ := fun x => w.grad x j
  let T : H1WeakTestFunction S → ℝ := fun τ =>
    -∫ x in V,
      euclideanForwardDifferenceQuotient step i u.toFun x *
        (fderiv ℝ (τ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume
  change T (φ.add ψ) = T φ + T ψ
  have hpair :
      ∀ τ : H1WeakTestFunction S,
        ∫ x in V, G x * τ x ∂MeasureTheory.volume = T τ := by
    intro τ
    change
      ∫ x in V,
          (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j *
            τ x ∂MeasureTheory.volume =
        -∫ x in V,
          euclideanForwardDifferenceQuotient step i u.toFun x *
            (fderiv ℝ (τ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume
    exact
      integral_forwardDifferenceQuotientOn_grad_coord_mul_eq_neg_integral_forwardDifferenceQuotient_mul_fderiv
        (U := U) (V := V) u hV hVU
        (step := step) i j hVshift
        τ.smooth τ.compactSupport (τ.support_subset.trans hSV)
  have hpair_add :
      ∫ x in V, G x * (φ.add ψ) x ∂MeasureTheory.volume = T (φ.add ψ) := by
    exact hpair (φ.add ψ)
  have hpairφ :
      ∫ x in V, G x * φ x ∂MeasureTheory.volume = T φ := by
    exact hpair φ
  have hpairψ :
      ∫ x in V, G x * ψ x ∂MeasureTheory.volume = T ψ := by
    exact hpair ψ
  have hG : MemScalarL2 V G := by
    simpa [G, w] using (w.gradMemL2 j)
  have hφV : MemScalarL2 V φ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (φ.smooth.continuous.memLp_of_hasCompactSupport φ.compactSupport).restrict V
  have hψV : MemScalarL2 V ψ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (ψ.smooth.continuous.memLp_of_hasCompactSupport ψ.compactSupport).restrict V
  have hGφ_int :
      MeasureTheory.Integrable (fun x => G x * φ x)
        (MeasureTheory.volume.restrict V) := by
    simpa [volumeMeasureOn] using! hG.integrable_mul hφV
  have hGψ_int :
      MeasureTheory.Integrable (fun x => G x * ψ x)
        (MeasureTheory.volume.restrict V) := by
    simpa [volumeMeasureOn] using! hG.integrable_mul hψV
  have hlin :
      ∫ x in V, G x * (φ.add ψ) x ∂MeasureTheory.volume =
        ∫ x in V, G x * φ x ∂MeasureTheory.volume +
          ∫ x in V, G x * ψ x ∂MeasureTheory.volume := by
    calc
      ∫ x in V, G x * (φ.add ψ) x ∂MeasureTheory.volume =
          ∫ x in V, (G x * φ x) + (G x * ψ x) ∂MeasureTheory.volume := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        simp [H1WeakTestFunction.add]
        ring
      _ = ∫ x in V, G x * φ x ∂MeasureTheory.volume +
          ∫ x in V, G x * ψ x ∂MeasureTheory.volume := by
        rw [MeasureTheory.integral_add hGφ_int hGψ_int]
  calc
    T (φ.add ψ) = ∫ x in V, G x * (φ.add ψ) x ∂MeasureTheory.volume := hpair_add.symm
    _ = ∫ x in V, G x * φ x ∂MeasureTheory.volume +
          ∫ x in V, G x * ψ x ∂MeasureTheory.volume := hlin
    _ = T φ + T ψ := by rw [hpairφ, hpairψ]

/-- Scalar-multiplicativity of the quotient-Hessian pairing on smooth weak
tests. -/
theorem neg_integral_forwardDifferenceQuotient_mul_fderiv_h1WeakTest_smul
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {S : Set (Vec d)} (hSV : S ⊆ V)
    (c : ℝ) (φ : H1WeakTestFunction S) :
    -∫ x in V,
        euclideanForwardDifferenceQuotient step i u.toFun x *
          (fderiv ℝ (φ.smul c : Vec d → ℝ) x) (basisVec j)
        ∂MeasureTheory.volume =
      c *
        (-∫ x in V,
          euclideanForwardDifferenceQuotient step i u.toFun x *
            (fderiv ℝ (φ : Vec d → ℝ) x) (basisVec j)
          ∂MeasureTheory.volume) := by
  let w : H1Function V := u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift
  let G : Vec d → ℝ := fun x => w.grad x j
  let T : H1WeakTestFunction S → ℝ := fun τ =>
    -∫ x in V,
      euclideanForwardDifferenceQuotient step i u.toFun x *
        (fderiv ℝ (τ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume
  change T (φ.smul c) = c * T φ
  have hpair :
      ∀ τ : H1WeakTestFunction S,
        ∫ x in V, G x * τ x ∂MeasureTheory.volume = T τ := by
    intro τ
    change
      ∫ x in V,
          (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j *
            τ x ∂MeasureTheory.volume =
        -∫ x in V,
          euclideanForwardDifferenceQuotient step i u.toFun x *
            (fderiv ℝ (τ : Vec d → ℝ) x) (basisVec j) ∂MeasureTheory.volume
    exact
      integral_forwardDifferenceQuotientOn_grad_coord_mul_eq_neg_integral_forwardDifferenceQuotient_mul_fderiv
        (U := U) (V := V) u hV hVU
        (step := step) i j hVshift
        τ.smooth τ.compactSupport (τ.support_subset.trans hSV)
  have hpair_smul :
      ∫ x in V, G x * (φ.smul c) x ∂MeasureTheory.volume = T (φ.smul c) := by
    exact hpair (φ.smul c)
  have hpairφ :
      ∫ x in V, G x * φ x ∂MeasureTheory.volume = T φ := by
    exact hpair φ
  have hG : MemScalarL2 V G := by
    simpa [G, w] using (w.gradMemL2 j)
  have hφV : MemScalarL2 V φ := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (φ.smooth.continuous.memLp_of_hasCompactSupport φ.compactSupport).restrict V
  have hGφ_int :
      MeasureTheory.Integrable (fun x => G x * φ x)
        (MeasureTheory.volume.restrict V) := by
    simpa [volumeMeasureOn] using! hG.integrable_mul hφV
  have hlin :
      ∫ x in V, G x * (φ.smul c) x ∂MeasureTheory.volume =
        c * ∫ x in V, G x * φ x ∂MeasureTheory.volume := by
    calc
      ∫ x in V, G x * (φ.smul c) x ∂MeasureTheory.volume =
          ∫ x in V, c * (G x * φ x) ∂MeasureTheory.volume := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        simp [H1WeakTestFunction.smul]
        ring
      _ = c * ∫ x in V, G x * φ x ∂MeasureTheory.volume := by
        rw [MeasureTheory.integral_const_mul]
  calc
    T (φ.smul c) = ∫ x in V, G x * (φ.smul c) x ∂MeasureTheory.volume :=
      hpair_smul.symm
    _ = c * ∫ x in V, G x * φ x ∂MeasureTheory.volume := hlin
    _ = c * T φ := by rw [hpairφ]

/-- Quantitative weak-Hessian handoff from an inner energy estimate: if the
forward quotient-gradient energy is controlled on a support set `S`, then the
distributional second-derivative test functional is controlled there. -/
theorem abs_neg_integral_forwardDifferenceQuotient_mul_fderiv_le_of_inner_energy_quarter_le
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
      (2 : ℝ) * R +
        (1 / 2 : ℝ) * ∫ x in S, φ x ^ 2 ∂MeasureTheory.volume := by
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
        (1 / 2 : ℝ) * ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume +
          (1 / 2 : ℝ) * ∫ x in S, φ x ^ 2 ∂MeasureTheory.volume :=
    abs_integral_coord_mul_le_half_integral_subset_vecNormSq_add_half_integral_subset_sq_of_support_subset
      (S := S) (V := V) (G := G) (φ := φ)
      hSV ((subset_tsupport φ).trans hφ_subS)
      (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad_memVectorL2
      hφS j
  have hbase :
      |(-∫ x in V,
          euclideanForwardDifferenceQuotient step i u.toFun x *
            (fderiv ℝ φ x) (basisVec j) ∂MeasureTheory.volume)| ≤
        (1 / 2 : ℝ) *
            ∫ x in S,
              vecNormSq
                ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
              ∂MeasureTheory.volume +
          (1 / 2 : ℝ) * ∫ x in S, φ x ^ 2 ∂MeasureTheory.volume := by
    rw [← hpair]
    change
      |∫ x in V, G x j * φ x ∂MeasureTheory.volume| ≤
        (1 / 2 : ℝ) * ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume +
          (1 / 2 : ℝ) * ∫ x in S, φ x ^ 2 ∂MeasureTheory.volume
    exact hbound
  have henergy_half :
      (1 / 2 : ℝ) *
          ∫ x in S,
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume ≤
        (2 : ℝ) * R := by
    change
      (1 / 2 : ℝ) * ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume ≤
        (2 : ℝ) * R
    calc
      (1 / 2 : ℝ) * ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume =
          2 * ((1 / 4 : ℝ) * ∫ x in S, vecNormSq (G x) ∂MeasureTheory.volume) := by
            ring
      _ ≤ 2 * R := mul_le_mul_of_nonneg_left henergy (by norm_num)
  exact hbase.trans
    (add_le_add_left henergy_half
      ((1 / 2 : ℝ) * ∫ x in S, φ x ^ 2 ∂MeasureTheory.volume))

/-- Specialization of the direct-test summation-by-parts identity to
`G = ∇u`. -/
theorem integral_vecDot_grad_backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient_grad_eq_neg_integral_forwardDifferenceQuotientOn_grad_on
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in U,
        vecDot (u.grad x)
          ((backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume =
      -∫ x in V,
        vecDot
          ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume := by
  have hshift :
      MemVectorL2 V (fun x => u.grad (euclideanCoordShift step i x)) :=
    memVectorL2_grad_comp_euclideanCoordShift_of_shift_subset
      (U := U) (V := V) u hV step i hVshift
  have hbase :=
    integral_vecDot_backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient_grad_eq_neg_integral_forwardDifferenceQuotient_on
      (U := U) (V := V) (G := u.grad) u.grad_memVectorL2 u hV hVU step i hshift
      hVshift hη hη_compact hη_sub
  have hright :
      -∫ x in V,
        vecDot
          (fun j => euclideanForwardDifferenceQuotient step i (fun y => u.grad y j) x)
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume =
      -∫ x in V,
        vecDot
          ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume := by
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    change
      vecDot (fun j => euclideanForwardDifferenceQuotient step i (fun y => u.grad y j) x)
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x) =
        vecDot ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
    rw [← forwardDifferenceQuotientOn_grad_eq_vectorForwardDifferenceQuotient
      (U := U) (V := V) u hV hVU step i hVshift x]
  exact hbase.trans hright

/-- Direct difference-quotient energy identity obtained by testing the
original weak equation with `D_i^-(η²D_i^+u)` and summing by parts. -/
theorem directDifferenceQuotient_sqCutoff_energy_identity
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    -∫ x in V,
        vecDot
          ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume =
      ∫ x in U,
        f x *
          euclideanBackwardDifferenceQuotient step i
            (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x
        ∂MeasureTheory.volume := by
  have hweak :=
    h.test_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_explicitGradient
      hU hf hV hVU step i hVshift hη hη_compact hη_sub
  have hsummation :=
    integral_vecDot_grad_backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient_grad_eq_neg_integral_forwardDifferenceQuotientOn_grad_on
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  exact hsummation.symm.trans hweak

/-- Direct difference-quotient energy identity with the localized test
gradient expanded into its main and cutoff-error pieces. -/
theorem directDifferenceQuotient_sqCutoff_energy_identity_expanded
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    -∫ x in V,
        vecDot
          ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          (fun j =>
            η x ^ 2 *
                (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
              euclideanForwardDifferenceQuotient step i u.toFun x *
                (2 * η x * euclideanGradient η x j))
        ∂MeasureTheory.volume =
      ∫ x in U,
        f x *
          euclideanBackwardDifferenceQuotient step i
            (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x
        ∂MeasureTheory.volume := by
  simpa using
    h.directDifferenceQuotient_sqCutoff_energy_identity
      hU hf hV hVU step i hVshift hη hη_compact hη_sub

/-- A squared smooth compact cutoff times the squared norm of an `L²` vector
field is integrable. -/
theorem integrableOn_sq_cutoff_vecNormSq_of_memVectorL2
    {G : Vec d → Vec d} {η : Vec d → ℝ}
    (hG : MemVectorL2 V G)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η) :
    MeasureTheory.IntegrableOn
      (fun x => η x ^ 2 * vecNormSq (G x)) V := by
  have hGsq : MeasureTheory.IntegrableOn (fun x => vecNormSq (G x)) V := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hG hG
  exact integrableOn_mul_left_of_continuous_hasCompactSupport
    (V := V) (φ := fun x => η x ^ 2) (F := fun x => vecNormSq (G x))
    (contDiff_sq hη).continuous (hasCompactSupport_sq hη_compact) hGsq

/-- The squared quotient term weighted by the squared cutoff-gradient norm is
integrable whenever the quotient is scalar `L²` and the cutoff is smooth compact
support. -/
theorem integrableOn_two_mul_sq_mul_vecNormSq_euclideanGradient_of_memScalarL2
    {w η : Vec d → ℝ}
    (hw : MemScalarL2 V w)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η) :
    MeasureTheory.IntegrableOn
      (fun x => 2 * w x ^ 2 * vecNormSq (euclideanGradient η x)) V := by
  have hw_sq :
      MeasureTheory.Integrable (fun x => w x * w x) (volumeMeasureOn V) :=
    hw.integrable_mul hw
  have hgrad_top :
      MeasureTheory.MemLp
        (fun x => vecNormSq (euclideanGradient η x)) ⊤ (volumeMeasureOn V) :=
    (continuous_vecNormSq_euclideanGradient_of_contDiff hη).memLp_top_of_hasCompactSupport
      (hasCompactSupport_vecNormSq_euclideanGradient hη_compact) (volumeMeasureOn V)
  have hmul :
      MeasureTheory.Integrable
        (fun x => vecNormSq (euclideanGradient η x) * (w x * w x))
        (volumeMeasureOn V) :=
    hw_sq.mul_of_top_right hgrad_top
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, pow_two,
    mul_assoc, mul_comm, mul_left_comm] using hmul.const_mul (2 : ℝ)

/-- The mixed squared-cutoff cross term is integrable when the scalar quotient
and vector quotient-gradient are both `L²`. -/
theorem integrableOn_sq_cutoff_cross_of_memScalarL2_memVectorL2
    {w : Vec d → ℝ} {G : Vec d → Vec d} {η : Vec d → ℝ}
    (hw : MemScalarL2 V w) (hG : MemVectorL2 V G)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_compact : HasCompactSupport η) :
    MeasureTheory.IntegrableOn
      (fun x =>
        w x * vecDot (G x) (fun j => 2 * η x * euclideanGradient η x j)) V := by
  have hsum :
      MeasureTheory.Integrable
        (fun x =>
          ∑ j : Fin d,
            w x * (G x j * (2 * η x * euclideanGradient η x j)))
        (volumeMeasureOn V) := by
    refine MeasureTheory.integrable_finsetSum (μ := volumeMeasureOn V)
      Finset.univ ?_
    intro j hj
    have hGj : MemScalarL2 V (fun x => G x j) :=
      memScalarL2_coord_of_memVectorL2 hG j
    have hwGj :
        MeasureTheory.Integrable (fun x => w x * G x j) (volumeMeasureOn V) :=
      hw.integrable_mul hGj
    have hBj_cont :
        Continuous (fun x => η x * (2 * euclideanGradient η x j)) :=
      hη.continuous.mul
        (continuous_const.mul ((contDiff_euclideanCoordDeriv hη j).continuous))
    have hBj_compact :
        HasCompactSupport (fun x => η x * (2 * euclideanGradient η x j)) :=
      hη_compact.mul_right
    have hBj_top :
        MeasureTheory.MemLp
          (fun x => η x * (2 * euclideanGradient η x j)) ⊤
          (volumeMeasureOn V) :=
      hBj_cont.memLp_top_of_hasCompactSupport hBj_compact (volumeMeasureOn V)
    have hprod :
        MeasureTheory.Integrable
          (fun x => (η x * (2 * euclideanGradient η x j)) * (w x * G x j))
          (volumeMeasureOn V) :=
      hwGj.mul_of_top_right hBj_top
    simpa [mul_assoc, mul_comm, mul_left_comm] using hprod
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn, vecDot, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm] using hsum

/-- Direct squared-cutoff Caccioppoli absorption.

This is the useful output of the direct test
`D_i^-(η² D_i^+u)`: it controls the localized `L²` norm of the gradient
difference quotient by the original forcing paired with the same direct test,
plus the usual cutoff-gradient error.  No difference quotient of `f` appears. -/
theorem directDifferenceQuotient_sqCutoff_energy_half_le_neg_forcing_add_error
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (1 / 2 : ℝ) *
        ∫ x in V,
          η x ^ 2 *
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (-(∫ x in U,
          f x *
            euclideanBackwardDifferenceQuotient step i
              (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x
          ∂MeasureTheory.volume)) +
        ∫ x in V,
          2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
            vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
  let w : Vec d → ℝ := euclideanForwardDifferenceQuotient step i u.toFun
  let G : Vec d → Vec d :=
    fun x => (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x
  let m : Vec d → ℝ := fun x => η x ^ 2 * vecNormSq (G x)
  let c : Vec d → ℝ :=
    fun x => w x * vecDot (G x) (fun j => 2 * η x * euclideanGradient η x j)
  let e : Vec d → ℝ :=
    fun x => 2 * (w x) ^ 2 * vecNormSq (euclideanGradient η x)
  let R : ℝ :=
    -∫ x in U,
      f x *
        euclideanBackwardDifferenceQuotient step i
          (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x
      ∂MeasureTheory.volume
  have henergy_raw :=
    h.directDifferenceQuotient_sqCutoff_energy_identity_expanded
      hU hf hV hVU step i hVshift hη hη_compact hη_sub
  have hleft :
      ∫ x in V,
          vecDot
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            (fun j =>
              η x ^ 2 *
                  (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
                euclideanForwardDifferenceQuotient step i u.toFun x *
                  (2 * η x * euclideanGradient η x j))
          ∂MeasureTheory.volume =
        ∫ x in V, (m x + c x) ∂MeasureTheory.volume := by
    congr with x
    have hpoint :=
      vecDot_cutoff_energy_integrand
        ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
        (fun j => 2 * η x * euclideanGradient η x j)
        (η x ^ 2) (w x)
    simpa [m, c, w, G, vecNormSq] using hpoint
  have henergy_vec :
      ∫ x in V,
          vecDot
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            (fun j =>
              η x ^ 2 *
                  (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
                euclideanForwardDifferenceQuotient step i u.toFun x *
                  (2 * η x * euclideanGradient η x j))
          ∂MeasureTheory.volume = R := by
    have hneg := congrArg (fun t : ℝ => -t) henergy_raw
    simpa [R] using hneg
  have henergy :
      ∫ x in V, (m x + c x) ∂MeasureTheory.volume = R := by
    exact hleft.symm.trans henergy_vec
  have hpoint :
      (fun x => -c x) ≤ᵐ[MeasureTheory.volume.restrict V]
        fun x => m x / 2 + e x := by
    filter_upwards with x
    have hbound :=
      neg_sq_cutoff_error_integrand_le
        (η x) (w x) (G x) (euclideanGradient η x)
    change
      -(w x *
        vecDot (G x) (fun j => 2 * η x * euclideanGradient η x j)) ≤
        η x ^ 2 * vecNormSq (G x) / 2 +
          2 * w x ^ 2 * vecNormSq (euclideanGradient η x)
    rw [← neg_mul]
    exact hbound
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
    integral_half_main_le_scalar_rhs_add_error_of_add_energy_identity
      (V := V) (m := m) (c := c) (e := e) (R := R)
      henergy hpoint hm hc he
  change
    (1 / 2 : ℝ) * ∫ x in V, m x ∂MeasureTheory.volume ≤
      R + ∫ x in V, e x ∂MeasureTheory.volume
  exact hhalf

/-- Direct squared-cutoff Caccioppoli after the elementary forcing Young
estimate.

The only remaining analytic input needed after this statement is the
localized difference-quotient estimate controlling the squared direct test
`D_i^-(η²D_i^+u)` by the gradient of `η²D_i^+u`. -/
theorem directDifferenceQuotient_sqCutoff_energy_half_le_forcing_sq_add_test_sq_add_error
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (1 / 2 : ℝ) *
        ∫ x in V,
          η x ^ 2 *
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (1 / 2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        (1 / 2 : ℝ) *
          ∫ x in U,
            (euclideanBackwardDifferenceQuotient step i
              (fun y =>
                η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x) ^ 2
            ∂MeasureTheory.volume +
        ∫ x in V,
          2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
            vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
  let T : Vec d → ℝ :=
    euclideanBackwardDifferenceQuotient step i
      (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y)
  have hbase :=
    h.directDifferenceQuotient_sqCutoff_energy_half_le_neg_forcing_add_error
      hU hf hV hVU step i hVshift hη hη_compact hη_sub
  have hT : MemScalarL2 U T := by
    let ψ : H10Function U :=
      backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
        (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
    simpa [T, ψ] using ψ.toH1Function.memL2
  have hforce :=
    neg_integral_mul_le_half_integral_sq_add_half_integral_sq_of_memScalarL2
      (U := U) (F := f) (G := T) hf hT
  let Eterm : ℝ :=
    ∫ x in V,
      2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
        vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume
  have hforce_with_error :
      (-(∫ x in U, f x * T x ∂MeasureTheory.volume)) + Eterm ≤
        (1 / 2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
          (1 / 2 : ℝ) * ∫ x in U, T x ^ 2 ∂MeasureTheory.volume + Eterm := by
    exact add_le_add_left hforce Eterm
  exact hbase.trans (by
    change
      (-(∫ x in U, f x * T x ∂MeasureTheory.volume)) + Eterm ≤
        (1 / 2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
          (1 / 2 : ℝ) * ∫ x in U, T x ^ 2 ∂MeasureTheory.volume + Eterm
    exact hforce_with_error)

/-- Direct squared-cutoff Caccioppoli with a smaller coefficient on the
test-square term, tuned for later absorption. -/
theorem directDifferenceQuotient_sqCutoff_energy_half_le_two_forcing_sq_add_eighth_test_sq_add_error
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (1 / 2 : ℝ) *
        ∫ x in V,
          η x ^ 2 *
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        (1 / 8 : ℝ) *
          ∫ x in U,
            (euclideanBackwardDifferenceQuotient step i
              (fun y =>
                η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x) ^ 2
            ∂MeasureTheory.volume +
        ∫ x in V,
          2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
            vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
  let T : Vec d → ℝ :=
    euclideanBackwardDifferenceQuotient step i
      (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y)
  have hbase :=
    h.directDifferenceQuotient_sqCutoff_energy_half_le_neg_forcing_add_error
      hU hf hV hVU step i hVshift hη hη_compact hη_sub
  have hT : MemScalarL2 U T := by
    let ψ : H10Function U :=
      backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
        (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
    simpa [T, ψ] using ψ.toH1Function.memL2
  have hforce :=
    neg_integral_mul_le_two_integral_sq_add_eighth_integral_sq_of_memScalarL2
      (U := U) (F := f) (G := T) hf hT
  let Eterm : ℝ :=
    ∫ x in V,
      2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
        vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume
  have hforce_with_error :
      (-(∫ x in U, f x * T x ∂MeasureTheory.volume)) + Eterm ≤
        (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
          (1 / 8 : ℝ) * ∫ x in U, T x ^ 2 ∂MeasureTheory.volume + Eterm := by
    exact add_le_add_left hforce Eterm
  exact hbase.trans (by
    change
      (-(∫ x in U, f x * T x ∂MeasureTheory.volume)) + Eterm ≤
        (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
          (1 / 8 : ℝ) * ∫ x in U, T x ^ 2 ∂MeasureTheory.volume + Eterm
    exact hforce_with_error)

/-- Direct squared-cutoff Caccioppoli with the test-square term replaced by
the product-rule gradient of `η²D_i^+u`. -/
theorem directDifferenceQuotient_sqCutoff_energy_half_le_forcing_sq_add_localizedSqCutoffForwardGradient_sq_add_error
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (1 / 2 : ℝ) *
        ∫ x in V,
          η x ^ 2 *
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (1 / 2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        (1 / 2 : ℝ) *
          ∫ x in U,
            ((localizedSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x i) ^ 2
            ∂MeasureTheory.volume +
        ∫ x in V,
          2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
            vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
  let T : Vec d → ℝ :=
    euclideanBackwardDifferenceQuotient step i
      (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y)
  let G : Vec d → ℝ :=
    fun x =>
      (localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad x i
  have hbase :=
    h.directDifferenceQuotient_sqCutoff_energy_half_le_forcing_sq_add_test_sq_add_error
      hU hf hV hVU step i hVshift hη hη_compact hη_sub
  have htest :=
    integral_sq_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_le_integral_sq_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad
      (U := U) (V := V) hU u hV hVU hstep i hVshift hη hη_compact hη_sub
  have hhalf :
      (1 / 2 : ℝ) * ∫ x in U, T x ^ 2 ∂MeasureTheory.volume ≤
        (1 / 2 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume := by
    exact mul_le_mul_of_nonneg_left
      (by
        change
          ∫ x in U,
            (euclideanBackwardDifferenceQuotient step i
              (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x) ^ 2
            ∂MeasureTheory.volume ≤
          ∫ x in U,
            ((localizedSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x i) ^ 2
            ∂MeasureTheory.volume
        exact htest)
      (by norm_num)
  have hreplace :
      (1 / 2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
            (1 / 2 : ℝ) * ∫ x in U, T x ^ 2 ∂MeasureTheory.volume +
          ∫ x in V,
            2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume ≤
        (1 / 2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
            (1 / 2 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume +
          ∫ x in V,
            2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
    exact add_le_add_left
      (add_le_add_right hhalf
        ((1 / 2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume))
      (∫ x in V,
        2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
          vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume)
  exact hbase.trans (by
    change
      (1 / 2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
            (1 / 2 : ℝ) * ∫ x in U, T x ^ 2 ∂MeasureTheory.volume +
          ∫ x in V,
            2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume ≤
        (1 / 2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
            (1 / 2 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume +
          ∫ x in V,
            2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume
    exact hreplace)

/-- Direct squared-cutoff Caccioppoli with both the small test-square
coefficient and the product-rule gradient replacement. -/
theorem directDifferenceQuotient_sqCutoff_energy_half_le_two_forcing_sq_add_eighth_localizedSqCutoffForwardGradient_sq_add_error
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (1 / 2 : ℝ) *
        ∫ x in V,
          η x ^ 2 *
            vecNormSq
              ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
          ∂MeasureTheory.volume ≤
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
        (1 / 8 : ℝ) *
          ∫ x in U,
            ((localizedSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x i) ^ 2
            ∂MeasureTheory.volume +
        ∫ x in V,
          2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
            vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
  let T : Vec d → ℝ :=
    euclideanBackwardDifferenceQuotient step i
      (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y)
  let G : Vec d → ℝ :=
    fun x =>
      (localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad x i
  have hbase :=
    h.directDifferenceQuotient_sqCutoff_energy_half_le_two_forcing_sq_add_eighth_test_sq_add_error
      hU hf hV hVU step i hVshift hη hη_compact hη_sub
  have htest :=
    integral_sq_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_le_integral_sq_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad
      (U := U) (V := V) hU u hV hVU hstep i hVshift hη hη_compact hη_sub
  have heighth :
      (1 / 8 : ℝ) * ∫ x in U, T x ^ 2 ∂MeasureTheory.volume ≤
        (1 / 8 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume := by
    exact mul_le_mul_of_nonneg_left
      (by
        change
          ∫ x in U,
            (euclideanBackwardDifferenceQuotient step i
              (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x) ^ 2
            ∂MeasureTheory.volume ≤
          ∫ x in U,
            ((localizedSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x i) ^ 2
            ∂MeasureTheory.volume
        exact htest)
      (by norm_num)
  have hreplace :
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
            (1 / 8 : ℝ) * ∫ x in U, T x ^ 2 ∂MeasureTheory.volume +
          ∫ x in V,
            2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume ≤
        (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
            (1 / 8 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume +
          ∫ x in V,
            2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
    exact add_le_add_left
      (add_le_add_right heighth
        ((2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume))
      (∫ x in V,
        2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
          vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume)
  exact hbase.trans (by
    change
      (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
            (1 / 8 : ℝ) * ∫ x in U, T x ^ 2 ∂MeasureTheory.volume +
          ∫ x in V,
            2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume ≤
        (2 : ℝ) * ∫ x in U, f x ^ 2 ∂MeasureTheory.volume +
            (1 / 8 : ℝ) * ∫ x in U, G x ^ 2 ∂MeasureTheory.volume +
          ∫ x in V,
            2 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume
    exact hreplace)

/-- Pointwise control of the product-rule gradient term produced by
`η²D_i^+u`.  The bound only needs the usual cutoff size condition
`|η| ≤ 1`. -/
theorem sq_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_coord_le
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V)
    (hη_abs_le_one : ∀ x, |η x| ≤ 1) (x : Vec d) :
    ((localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad x i) ^ 2 ≤
      2 * η x ^ 2 *
          vecNormSq
            ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x) +
        8 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
          vecNormSq (euclideanGradient η x) := by
  let A : Vec d := (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x
  let w : ℝ := euclideanForwardDifferenceQuotient step i u.toFun x
  let B : Vec d := euclideanGradient η x
  have hgrad :
      (localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad x i =
        η x ^ 2 * A i + w * (2 * η x * B i) := by
    simp [A, w, B]
  have hη_sq_le_one : η x ^ 2 ≤ 1 := by
    have hsq :=
      (sq_le_sq₀ (abs_nonneg (η x)) (by norm_num : 0 ≤ (1 : ℝ))).2
        (hη_abs_le_one x)
    simpa [sq_abs] using hsq
  have hη_sq_nonneg : 0 ≤ η x ^ 2 := sq_nonneg _
  have hη_four_le_sq : (η x ^ 2) ^ 2 ≤ η x ^ 2 := by
    calc
      (η x ^ 2) ^ 2 = η x ^ 2 * η x ^ 2 := by ring
      _ ≤ η x ^ 2 * 1 := mul_le_mul_of_nonneg_left hη_sq_le_one hη_sq_nonneg
      _ = η x ^ 2 := by ring
  have hA_coord : A i ^ 2 ≤ vecNormSq A := coord_sq_le_vecNormSq A i
  have hB_coord : B i ^ 2 ≤ vecNormSq B := coord_sq_le_vecNormSq B i
  have hA_nonneg : 0 ≤ A i ^ 2 := sq_nonneg _
  have hB_nonneg : 0 ≤ B i ^ 2 := sq_nonneg _
  have htermA :
      2 * (η x ^ 2 * A i) ^ 2 ≤ 2 * η x ^ 2 * vecNormSq A := by
    have hmul := mul_le_mul hη_four_le_sq hA_coord hA_nonneg hη_sq_nonneg
    calc
      2 * (η x ^ 2 * A i) ^ 2 =
          2 * ((η x ^ 2) ^ 2 * A i ^ 2) := by ring
      _ ≤ 2 * (η x ^ 2 * vecNormSq A) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 2 * η x ^ 2 * vecNormSq A := by ring
  have hηB :
      η x ^ 2 * B i ^ 2 ≤ vecNormSq B := by
    have hmul := mul_le_mul hη_sq_le_one hB_coord hB_nonneg (by norm_num : 0 ≤ (1 : ℝ))
    calc
      η x ^ 2 * B i ^ 2 ≤ 1 * vecNormSq B := hmul
      _ = vecNormSq B := by ring
  have htermB :
      2 * (w * (2 * η x * B i)) ^ 2 ≤
        8 * w ^ 2 * vecNormSq B := by
    have hw_nonneg : 0 ≤ w ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hηB hw_nonneg
    have hscaled := mul_le_mul_of_nonneg_left hmul (by norm_num : 0 ≤ (8 : ℝ))
    calc
      2 * (w * (2 * η x * B i)) ^ 2 =
          8 * (w ^ 2 * (η x ^ 2 * B i ^ 2)) := by ring
      _ ≤ 8 * (w ^ 2 * vecNormSq B) := hscaled
      _ = 8 * w ^ 2 * vecNormSq B := by ring
  have hyoung :
      (η x ^ 2 * A i + w * (2 * η x * B i)) ^ 2 ≤
        2 * (η x ^ 2 * A i) ^ 2 + 2 * (w * (2 * η x * B i)) ^ 2 := by
    rw [show
      (η x ^ 2 * A i + w * (2 * η x * B i)) ^ 2 =
        2 * (η x ^ 2 * A i) ^ 2 + 2 * (w * (2 * η x * B i)) ^ 2 -
          (η x ^ 2 * A i - w * (2 * η x * B i)) ^ 2 by ring]
    exact sub_le_self _ (sq_nonneg _)
  rw [hgrad]
  change
    (η x ^ 2 * A i + w * (2 * η x * B i)) ^ 2 ≤
      2 * η x ^ 2 * vecNormSq A + 8 * w ^ 2 * vecNormSq B
  exact hyoung.trans (add_le_add htermA htermB)

/-- Integral absorption form of
`sq_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_coord_le`. -/
theorem eighth_integral_sq_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_coord_le_quarter_energy_add_error
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V)
    (hη_abs_le_one : ∀ x, |η x| ≤ 1) :
    (1 / 8 : ℝ) *
        ∫ x in U,
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x i) ^ 2
          ∂MeasureTheory.volume ≤
      (1 / 4 : ℝ) *
          ∫ x in V,
            η x ^ 2 *
              vecNormSq
                ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x)
            ∂MeasureTheory.volume +
        ∫ x in V,
          (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
            vecNormSq (euclideanGradient η x) ∂MeasureTheory.volume := by
  let F : H1Function U :=
    localizedSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  let G : Vec d → ℝ := fun x => F.grad x i
  let A : Vec d → Vec d :=
    fun x => (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x
  let w : Vec d → ℝ := euclideanForwardDifferenceQuotient step i u.toFun
  let E : Vec d → ℝ := fun x => w x ^ 2 * vecNormSq (euclideanGradient η x)
  have hG_support : Function.support G ⊆ V := by
    change
      Function.support
          (fun x =>
            (localizedSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x i) ⊆
        V
    exact
      support_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_subset
        (U := U) (V := V) u hV hVU step i i hVshift hη hη_compact hη_sub
  have hGsq_support : Function.support (fun x => G x ^ 2) ⊆ V := by
    intro x hx
    exact hG_support (by
      intro hGzero
      exact hx (by simp [hGzero]))
  have hrestrict :
      ∫ x in U, G x ^ 2 ∂MeasureTheory.volume =
        ∫ x in V, G x ^ 2 ∂MeasureTheory.volume :=
    integral_subset_of_support_subset hVU hGsq_support
  rw [hrestrict]
  have hG_memV : MeasureTheory.MemLp G 2 (volumeMeasureOn V) := by
    exact (F.gradMemL2 i).mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hVU)
  have hGsq_int : MeasureTheory.IntegrableOn (fun x => G x ^ 2) V := by
    simpa [pow_two, MeasureTheory.IntegrableOn, volumeMeasureOn] using!
      hG_memV.integrable_mul hG_memV
  have hleft_int :
      MeasureTheory.IntegrableOn (fun x => (1 / 8 : ℝ) * G x ^ 2) V :=
    hGsq_int.const_mul (1 / 8 : ℝ)
  have hmain_int :
      MeasureTheory.IntegrableOn
        (fun x => η x ^ 2 * vecNormSq (A x)) V := by
    have hA : MemVectorL2 V A := by
      change MemVectorL2 V
        ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad)
      exact
        (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad_memVectorL2
    simpa [A] using
      integrableOn_sq_cutoff_vecNormSq_of_memVectorL2
        (V := V) (G := A) (η := η) hA hη hη_compact
  have hquarter_int :
      MeasureTheory.IntegrableOn
        (fun x => (1 / 4 : ℝ) * (η x ^ 2 * vecNormSq (A x))) V :=
    hmain_int.const_mul (1 / 4 : ℝ)
  have hw : MemScalarL2 V w := by
    refine MeasureTheory.MemLp.ae_eq ?_
      (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).memL2
    filter_upwards with x
    simp [w]
  have hE_two :
      MeasureTheory.IntegrableOn
        (fun x => 2 * w x ^ 2 * vecNormSq (euclideanGradient η x)) V := by
    simpa [w] using
      integrableOn_two_mul_sq_mul_vecNormSq_euclideanGradient_of_memScalarL2
        (V := V) (w := w) (η := η) hw hη hη_compact
  have hE_int : MeasureTheory.IntegrableOn E V := by
    have hhalf := hE_two.const_mul ((2 : ℝ)⁻¹)
    simpa [E, mul_assoc, mul_left_comm, mul_comm] using! hhalf
  have hright_int :
      MeasureTheory.IntegrableOn
        (fun x => (1 / 4 : ℝ) * (η x ^ 2 * vecNormSq (A x)) + E x) V :=
    hquarter_int.add hE_int
  have hpoint :
      (fun x => (1 / 8 : ℝ) * G x ^ 2) ≤ᵐ[MeasureTheory.volume.restrict V]
        fun x => (1 / 4 : ℝ) * (η x ^ 2 * vecNormSq (A x)) + E x := by
    filter_upwards with x
    have hsq :
        G x ^ 2 ≤
          2 * η x ^ 2 * vecNormSq (A x) +
            8 * w x ^ 2 * vecNormSq (euclideanGradient η x) := by
      change
        ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x i) ^ 2 ≤
          2 * η x ^ 2 *
              vecNormSq
                ((u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x) +
            8 * (euclideanForwardDifferenceQuotient step i u.toFun x) ^ 2 *
              vecNormSq (euclideanGradient η x)
      exact
        sq_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_coord_le
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub hη_abs_le_one x
    nlinarith
  have hmono := MeasureTheory.integral_mono_ae hleft_int hright_int hpoint
  have hleft_eq :
      ∫ x in V, (1 / 8 : ℝ) * G x ^ 2 ∂MeasureTheory.volume =
        (1 / 8 : ℝ) * ∫ x in V, G x ^ 2 ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_const_mul]
  have hquarter_eq :
      ∫ x in V, (1 / 4 : ℝ) * (η x ^ 2 * vecNormSq (A x))
          ∂MeasureTheory.volume =
        (1 / 4 : ℝ) * ∫ x in V, η x ^ 2 * vecNormSq (A x)
          ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_const_mul]
  have hright_eq :
      ∫ x in V,
          ((1 / 4 : ℝ) * (η x ^ 2 * vecNormSq (A x)) + E x)
          ∂MeasureTheory.volume =
        (1 / 4 : ℝ) * ∫ x in V, η x ^ 2 * vecNormSq (A x)
          ∂MeasureTheory.volume +
          ∫ x in V, E x ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_add hquarter_int hE_int]
    rw [hquarter_eq]
  rw [hleft_eq, hright_eq] at hmono
  change
    (1 / 8 : ℝ) * ∫ x in V, G x ^ 2 ∂MeasureTheory.volume ≤
      (1 / 4 : ℝ) *
          ∫ x in V, η x ^ 2 * vecNormSq (A x) ∂MeasureTheory.volume +
        ∫ x in V, E x ∂MeasureTheory.volume
  exact hmono

end WeakPoissonEquationOn

end

end Homogenization
