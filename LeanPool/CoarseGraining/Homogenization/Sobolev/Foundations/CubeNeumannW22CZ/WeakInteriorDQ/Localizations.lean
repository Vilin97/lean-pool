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

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.DiffQuotientLp

/-! # Localizations -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {U V : Set (Vec d)}
variable {u : H1Function U} {f : Vec d → ℝ}


/-- The support of a coordinate derivative is contained in the topological
support of the original scalar function. -/
theorem support_euclideanGradient_coord_subset_tsupport
    {φ : Vec d → ℝ} (j : Fin d) :
    Function.support (fun x => euclideanGradient φ x j) ⊆ tsupport φ := by
  intro x hx
  by_contra hxt
  have hzero : euclideanGradient φ x j = 0 := by
    unfold euclideanGradient euclideanCoordDeriv
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt]
    simp
  exact hx hzero

/-- A coordinate derivative of a smooth compactly supported cutoff localizes a
scalar `L²(V)` function to an ambient scalar `L²(U)` function when the original
cutoff support lies in `V`. -/
theorem memScalarL2_mul_euclideanGradient_coord_of_contDiff_hasCompactSupport_tsupport_subset
    {φ F : Vec d → ℝ} (hV_meas : MeasurableSet V)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ V) (hF : MemScalarL2 V F) (j : Fin d) :
    MemScalarL2 U (fun x => euclideanGradient φ x j * F x) := by
  have hdφ_top :
      MeasureTheory.MemLp (fun x => euclideanGradient φ x j) ⊤
        (MeasureTheory.volume.restrict V) :=
    (contDiff_euclideanCoordDeriv hφ j).continuous.memLp_top_of_hasCompactSupport
      (hasCompactSupport_euclideanCoordDeriv hφ_compact j)
      (MeasureTheory.volume.restrict V)
  have hprodV :
      MeasureTheory.MemLp (fun x => euclideanGradient φ x j * F x) 2
        (MeasureTheory.volume.restrict V) := by
    simpa [MemScalarL2, volumeMeasureOn, mul_comm] using hF.mul' hdφ_top
  have hsupport : Function.support (fun x => euclideanGradient φ x j * F x) ⊆ V :=
    (Function.support_mul_subset_left (fun x => euclideanGradient φ x j) F).trans
      ((support_euclideanGradient_coord_subset_tsupport j).trans hφ_sub)
  simpa [MemScalarL2, volumeMeasureOn] using
    memLp_restrict_of_support_subset_of_memLp
      (U := U) (V := V) hV_meas hsupport hprodV

/-- Localize an interior `H¹(V)` function by a smooth compactly supported
cutoff and regard the product as an ambient `H¹(U)` function.

This is the support-sensitive replacement for pretending that the ambient
bounded domain is translation-invariant: only the cutoff product is promoted to
`U`, and every weak-gradient test on `U` is reduced to the interior set `V`
because the product and its gradient are supported in `V`. -/
noncomputable def localizedMulContDiffHasCompactSupportToAmbient
    (w : H1Function V) (hV_meas : MeasurableSet V) (hVU : V ⊆ U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    H1Function U := by
  let Dφ : Vec d → Vec d := fun x i => (fderiv ℝ φ x) (basisVec i)
  refine
    { toFun := fun x => φ x * w x
      grad := fun x i => φ x * w.grad x i + w x * Dφ x i
      memL2 := ?_
      gradMemL2 := ?_
      hasWeakGradient := ?_ }
  · exact memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
      (U := U) (V := V) hV_meas hφ hφ_compact hφ_sub w.memL2
  · intro i
    have hfirst :
        MemScalarL2 U (fun x => φ x * w.grad x i) :=
      memScalarL2_mul_of_contDiff_hasCompactSupport_tsupport_subset
        (U := U) (V := V) hV_meas hφ hφ_compact hφ_sub (w.gradMemL2 i)
    have hsecond :
        MemScalarL2 U (fun x => w x * Dφ x i) := by
      have hderiv :
          MemScalarL2 U (fun x => euclideanGradient φ x i * w x) :=
        memScalarL2_mul_euclideanGradient_coord_of_contDiff_hasCompactSupport_tsupport_subset
          (U := U) (V := V) hV_meas hφ hφ_compact hφ_sub w.memL2 i
      simpa [Dφ, euclideanGradient, euclideanCoordDeriv, mul_comm] using hderiv
    simpa [Dφ, Pi.add_apply, MemScalarL2, volumeMeasureOn] using! hfirst.add hsecond
  · intro i ψ hψ_smooth hψ_compact hψ_sub
    let ei : Vec d := basisVec i
    let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) ei
    let dψ : Vec d → ℝ := fun x => (fderiv ℝ ψ x) ei
    let ψφ : Vec d → ℝ := fun x => φ x * ψ x
    change
      ∫ x in U, (φ x * w x) * dψ x ∂MeasureTheory.volume =
        -∫ x in U, (φ x * w.grad x i + w x * dφ x) * ψ x
          ∂MeasureTheory.volume
    have hleft_support :
        Function.support (fun x => (φ x * w x) * dψ x) ⊆ V := by
      exact
        (Function.support_mul_subset_left (fun x => φ x * w x) dψ).trans
          ((Function.support_mul_subset_left φ w.toFun).trans
            (subset_tsupport φ |>.trans hφ_sub))
    have hdφ_support : Function.support dφ ⊆ tsupport φ := by
      simpa [dφ, ei, euclideanGradient, euclideanCoordDeriv] using
        support_euclideanGradient_coord_subset_tsupport (φ := φ) i
    have hright_support :
        Function.support (fun x => (φ x * w.grad x i + w x * dφ x) * ψ x) ⊆ V := by
      refine (Function.support_mul_subset_left
        (fun x => φ x * w.grad x i + w x * dφ x) ψ).trans ?_
      refine (Function.support_add _ _).trans (Set.union_subset ?_ ?_)
      · exact (Function.support_mul_subset_left φ (fun x => w.grad x i)).trans
          (subset_tsupport φ |>.trans hφ_sub)
      · exact (Function.support_mul_subset_right w.toFun dφ).trans
          (hdφ_support.trans hφ_sub)
    rw [integral_subset_of_support_subset (U := U) (V := V) hVU hleft_support,
      integral_subset_of_support_subset (U := U) (V := V) hVU hright_support]
    have hψ_cont : Continuous ψ := hψ_smooth.continuous
    have hφ_cont : Continuous φ := hφ.continuous
    have hdφ_cont : Continuous dφ := by
      simpa [dφ, ei] using
        (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψ_cont : Continuous dψ := by
      simpa [dψ, ei] using
        (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφ_compact : HasCompactSupport dφ := by
      simpa [dφ, ei] using hφ_compact.fderiv_apply (𝕜 := ℝ) ei
    have hdψ_compact : HasCompactSupport dψ := by
      simpa [dψ, ei] using hψ_compact.fderiv_apply (𝕜 := ℝ) ei
    have hψφ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψφ := hφ.mul hψ_smooth
    have hψφ_compact : HasCompactSupport ψφ := by
      simpa [ψφ] using! hψ_compact.mul_left (f := φ)
    have hψφ_sub : tsupport ψφ ⊆ V :=
      (tsupport_mul_subset_left (f := φ) (g := ψ)).trans hφ_sub
    have hdψφ_cont : Continuous (fun x => (fderiv ℝ ψφ x) ei) := by
      simpa [ei] using
        (hψφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψφ_compact : HasCompactSupport (fun x => (fderiv ℝ ψφ x) ei) := by
      simpa [ei] using hψφ_compact.fderiv_apply (𝕜 := ℝ) ei
    have hw_eq :
        ∫ x in V, w x * ((fderiv ℝ ψφ x) ei) ∂MeasureTheory.volume =
          -∫ x in V, w.grad x i * ψφ x ∂MeasureTheory.volume := by
      simpa using w.hasWeakGradient i ψφ hψφ_smooth hψφ_compact hψφ_sub
    have hw_loc : MeasureTheory.LocallyIntegrable w (MeasureTheory.volume.restrict V) :=
      w.memL2.locallyIntegrable (by norm_num)
    have hgrad_loc :
        MeasureTheory.LocallyIntegrable (fun x => w.grad x i)
          (MeasureTheory.volume.restrict V) :=
      (w.gradMemL2 i).locallyIntegrable (by norm_num)
    have hmul1_cont : Continuous (fun x => φ x * dψ x) :=
      hφ_cont.mul hdψ_cont
    have hmul1_compact : HasCompactSupport (fun x => φ x * dψ x) := by
      simpa using! hdψ_compact.mul_left (f := φ)
    have hw_mul1_int :
        MeasureTheory.Integrable (fun x => w x * (φ x * dψ x))
          (MeasureTheory.volume.restrict V) := by
      simpa [smul_eq_mul, mul_assoc] using
        hw_loc.integrable_smul_right_of_hasCompactSupport hmul1_cont hmul1_compact
    have hmul2_cont : Continuous (fun x => ψ x * dφ x) :=
      hψ_cont.mul hdφ_cont
    have hmul2_compact : HasCompactSupport (fun x => ψ x * dφ x) := by
      simpa [mul_comm] using! hdφ_compact.mul_left (f := ψ)
    have hw_mul2_int :
        MeasureTheory.Integrable (fun x => w x * (ψ x * dφ x))
          (MeasureTheory.volume.restrict V) := by
      simpa [smul_eq_mul, mul_assoc] using
        hw_loc.integrable_smul_right_of_hasCompactSupport hmul2_cont hmul2_compact
    have hw_ψφ_int :
        MeasureTheory.Integrable (fun x => w x * ((fderiv ℝ ψφ x) ei))
          (MeasureTheory.volume.restrict V) := by
      simpa [smul_eq_mul] using
        hw_loc.integrable_smul_right_of_hasCompactSupport hdψφ_cont hdψφ_compact
    have hgrad_mul1_int :
        MeasureTheory.Integrable (fun x => w.grad x i * (φ x * ψ x))
          (MeasureTheory.volume.restrict V) := by
      simpa [smul_eq_mul, mul_assoc] using
        hgrad_loc.integrable_smul_right_of_hasCompactSupport
          (hφ_cont.mul hψ_cont) hψφ_compact
    have hw_mul2ψ_int :
        MeasureTheory.Integrable (fun x => (w x * dφ x) * ψ x)
          (MeasureTheory.volume.restrict V) := by
      simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        hw_loc.integrable_smul_right_of_hasCompactSupport hmul2_cont hmul2_compact
    have hprod_deriv :
        ∀ x, (fderiv ℝ ψφ x) ei = φ x * dψ x + ψ x * dφ x := by
      intro x
      have hφ_diff : DifferentiableAt ℝ φ x :=
        (hφ.contDiffAt).differentiableAt (by simp)
      have hψ_diff : DifferentiableAt ℝ ψ x :=
        (hψ_smooth.contDiffAt).differentiableAt (by simp)
      rw [show ψφ = φ * ψ by rfl, fderiv_mul hφ_diff hψ_diff]
      simp [dφ, dψ, ei, add_apply, smul_eq_mul]
    have hleft_eq :
        ∫ x in V, (φ x * w x) * dψ x ∂MeasureTheory.volume =
          ∫ x in V, w x * (φ x * dψ x) ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro x
      ring
    have hsplit :
          ∫ x in V, w x * (φ x * dψ x) ∂MeasureTheory.volume =
          ∫ x in V, w x * ((fderiv ℝ ψφ x) ei) ∂MeasureTheory.volume -
            ∫ x in V, w x * (ψ x * dφ x) ∂MeasureTheory.volume := by
      calc
        ∫ x in V, w x * (φ x * dψ x) ∂MeasureTheory.volume
            = ∫ x in V,
                (w x * ((fderiv ℝ ψφ x) ei)) - w x * (ψ x * dφ x)
                ∂MeasureTheory.volume := by
                refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
                intro x
                calc
                  w x * (φ x * dψ x) =
                      w x * ((φ x * dψ x + ψ x * dφ x) - ψ x * dφ x) := by
                        ring
                  _ = w x * (((fderiv ℝ ψφ x) ei) - ψ x * dφ x) := by
                        rw [← hprod_deriv x]
                  _ = w x * ((fderiv ℝ ψφ x) ei) - w x * (ψ x * dφ x) := by
                        ring
        _ = ∫ x in V, w x * ((fderiv ℝ ψφ x) ei) ∂MeasureTheory.volume -
              ∫ x in V, w x * (ψ x * dφ x) ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_sub hw_ψφ_int hw_mul2_int]
    have hright_eq :
        -∫ x in V, w.grad x i * ψφ x ∂MeasureTheory.volume -
            ∫ x in V, w x * (ψ x * dφ x) ∂MeasureTheory.volume =
          -∫ x in V, (φ x * w.grad x i + w x * dφ x) * ψ x
            ∂MeasureTheory.volume := by
      have hgrad_term :
          ∫ x in V, w.grad x i * ψφ x ∂MeasureTheory.volume =
            ∫ x in V, w.grad x i * (φ x * ψ x) ∂MeasureTheory.volume := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        simp [ψφ]
      have hw_term :
          ∫ x in V, w x * (ψ x * dφ x) ∂MeasureTheory.volume =
            ∫ x in V, (w x * dφ x) * ψ x ∂MeasureTheory.volume := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        ring
      have hsum :
          ∫ x in V, (φ x * w.grad x i + w x * dφ x) * ψ x
              ∂MeasureTheory.volume =
            ∫ x in V, w.grad x i * (φ x * ψ x) ∂MeasureTheory.volume +
              ∫ x in V, (w x * dφ x) * ψ x ∂MeasureTheory.volume := by
        calc
          ∫ x in V, (φ x * w.grad x i + w x * dφ x) * ψ x
              ∂MeasureTheory.volume
              = ∫ x in V,
                  w.grad x i * (φ x * ψ x) + (w x * dφ x) * ψ x
                  ∂MeasureTheory.volume := by
                  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
                  intro x
                  ring
          _ = ∫ x in V, w.grad x i * (φ x * ψ x) ∂MeasureTheory.volume +
                ∫ x in V, (w x * dφ x) * ψ x ∂MeasureTheory.volume := by
                  rw [MeasureTheory.integral_add hgrad_mul1_int hw_mul2ψ_int]
      rw [hgrad_term, hw_term, hsum]
      ring
    calc
      ∫ x in V, (φ x * w x) * dψ x ∂MeasureTheory.volume
          = ∫ x in V, w x * (φ x * dψ x) ∂MeasureTheory.volume := hleft_eq
      _ = ∫ x in V, w x * ((fderiv ℝ ψφ x) ei) ∂MeasureTheory.volume -
            ∫ x in V, w x * (ψ x * dφ x) ∂MeasureTheory.volume := hsplit
      _ = -∫ x in V, w.grad x i * ψφ x ∂MeasureTheory.volume -
            ∫ x in V, w x * (ψ x * dφ x) ∂MeasureTheory.volume := by
            rw [hw_eq]
      _ = -∫ x in V, (φ x * w.grad x i + w x * dφ x) * ψ x
            ∂MeasureTheory.volume := hright_eq

@[simp] theorem localizedMulContDiffHasCompactSupportToAmbient_toFun
    (w : H1Function V) (hV_meas : MeasurableSet V) (hVU : V ⊆ U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    (localizedMulContDiffHasCompactSupportToAmbient
      (U := U) (V := V) w hV_meas hVU hφ hφ_compact hφ_sub).toFun =
      fun x => φ x * w x :=
  rfl

@[simp] theorem localizedMulContDiffHasCompactSupportToAmbient_grad
    (w : H1Function V) (hV_meas : MeasurableSet V) (hVU : V ⊆ U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V) :
    (localizedMulContDiffHasCompactSupportToAmbient
      (U := U) (V := V) w hV_meas hVU hφ hφ_compact hφ_sub).grad =
      fun x i => φ x * w.grad x i + w x * (fderiv ℝ φ x) (basisVec i) :=
  rfl

/-- Ambient `H¹` representative of the squared-cutoff forward difference
quotient `η² D_i^+ u`, localized through an interior shift-safe set. -/
noncomputable def localizedSqCutoffForwardDifferenceQuotientToAmbient
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    H1Function U :=
  localizedMulContDiffHasCompactSupportToAmbient
    (U := U) (V := V)
    (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift)
    hV.isOpen.measurableSet hVU
    (φ := fun x => η x ^ 2)
    (contDiff_sq hη) (hasCompactSupport_sq hη_compact)
    ((tsupport_sq_subset η).trans hη_sub)

@[simp] theorem localizedSqCutoffForwardDifferenceQuotientToAmbient_toFun
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (localizedSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift
      hη hη_compact hη_sub).toFun =
      fun x => η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x := by
  simp [localizedSqCutoffForwardDifferenceQuotientToAmbient]

@[simp] theorem localizedSqCutoffForwardDifferenceQuotientToAmbient_grad
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (localizedSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift
      hη hη_compact hη_sub).grad =
      fun x j =>
        η x ^ 2 *
            (u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift).grad x j +
          euclideanForwardDifferenceQuotient step i u.toFun x *
            (2 * η x * euclideanGradient η x j) := by
  funext x j
  simp [localizedSqCutoffForwardDifferenceQuotientToAmbient]
  rw [show (fderiv ℝ (fun x => η x ^ 2) x) (basisVec j) =
      2 * η x * euclideanGradient η x j by
        simpa [euclideanCoordDeriv] using! euclideanCoordDeriv_sq hη j x]
  ring_nf
  exact Or.inl trivial

/-- Each coordinate of the localized squared-cutoff forward quotient gradient
is supported inside the interior set carrying the cutoff. -/
theorem support_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_subset
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    Function.support
      (fun x =>
        (localizedSqCutoffForwardDifferenceQuotientToAmbient
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub).grad x j) ⊆ V := by
  intro x hx
  by_contra hxV
  have hη_zero : η x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hxt => hxV (hη_sub hxt))
  have hdη_zero : euclideanGradient η x j = 0 := by
    by_contra hne
    exact hxV (hη_sub ((support_euclideanGradient_coord_subset_tsupport (φ := η) j) hne))
  have hzero :
      (localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad x j = 0 := by
    simp [hη_zero, hdη_zero]
  exact hx hzero

/-- Pairing against the localized squared-cutoff forward quotient gradient is
also supported inside the cutoff interior set. -/
theorem support_vecDot_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_subset
    (G : Vec d → Vec d)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    Function.support
      (fun x =>
        vecDot (G x)
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)) ⊆ V := by
  intro x hx
  by_contra hxV
  have hgrad_zero :
      (localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad x = 0 := by
    ext j
    by_contra hne
    exact hxV
      (support_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_subset
        (U := U) (V := V) u hV hVU step i j hVshift hη hη_compact hη_sub hne)
  exact hx (by simp [hgrad_zero, vecDot])

/-- The unshifted localized-gradient pairing may be integrated over the
interior set carrying the cutoff. -/
theorem integral_vecDot_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_eq_integral_on
    (G : Vec d → Vec d)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in U,
        vecDot (G x)
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume =
      ∫ x in V,
        vecDot (G x)
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume :=
  integral_subset_of_support_subset hVU
    (support_vecDot_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_subset
      (U := U) (V := V) G u hV hVU step i hVshift hη hη_compact hη_sub)

/-- Localized zero-trace cutoff product.  If `w` is only known as an `H¹`
function on an interior set `V`, multiplying by a smooth compactly supported
cutoff with support in `V` still gives an `H¹₀(U)` function on the ambient
domain. -/
theorem memH10_localizedMul_of_contDiff_hasCompactSupport_tsupport_subset
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {φ F : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ V)
    (hF : MemH1 V F) :
    MemH10 U (fun x => φ x * F x) := by
  rcases hF with ⟨w, rfl⟩
  by_cases hts : tsupport φ = ∅
  · have hφ_zero : φ = 0 := tsupport_eq_empty_iff.mp hts
    simpa [hφ_zero] using! (memH10_zero (U := U))
  · obtain ⟨x0, hx0⟩ : (tsupport φ).Nonempty := Set.nonempty_iff_ne_empty.mpr hts
    have hx0V : x0 ∈ V := hφ_sub hx0
    rcases Metric.mem_nhds_iff.mp (hV.isOpen.mem_nhds hx0V) with ⟨r, hr_pos, hr_sub⟩
    let r0 : ℝ := r / 2
    have hr0_pos : 0 < r0 := by
      dsimp [r0]
      positivity
    have hball : Metric.closedBall x0 r0 ⊆ V := by
      refine (Metric.closedBall_subset_ball ?_).trans hr_sub
      dsimp [r0]
      exact half_lt_self hr_pos
    let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
    let ε : ℕ → ℝ := unitConvexApproxScale
    let ψ : ℕ → Vec d → ℝ := fun n =>
      convexApproxSmoothRepresentative V ρ w x0 r0 (ε n)
    let wφ : H1Function U :=
      localizedMulContDiffHasCompactSupportToAmbient
        (U := U) (V := V) w hV.isOpen.measurableSet hVU hφ hφ_compact hφ_sub
    have hρ : IsConvexApproxKernel ρ := by
      simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
    have hε_pos : ∀ n : ℕ, 0 < ε n := by
      intro n
      dsimp [ε, unitConvexApproxScale]
      positivity
    have hε_eventually_lt_one : ∀ᶠ n : ℕ in Filter.atTop, ε n < 1 := by
      simpa [ε] using
        (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
          (fun _ hn => hn))
    have hψ_smooth : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := by
      intro n
      dsimp [ψ]
      exact contDiff_convexApproxSmoothRepresentative
        hV.isOpen.measurableSet hρ (by norm_num : (1 : ENNReal) ≤ 2) w.memL2 hr0_pos
        (hε_pos n)
    have hψ_memL2 : ∀ n : ℕ, MeasureTheory.MemLp (ψ n) 2 (MeasureTheory.volume.restrict V) := by
      intro n
      let v : H1Function V :=
        H1Function.ofContDiffOnIsOpenBoundedConvexDomain hV ((hψ_smooth n).of_le (by simp))
      simpa [ψ, v, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
        H1Function.ofContDiffOnIsSobolevRegularDomain]
        using v.memL2
    have hψ_grad_memL2 : ∀ n : ℕ, ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => (fderiv ℝ (ψ n) x) (basisVec i))
          2 (MeasureTheory.volume.restrict V) := by
      intro n i
      let v : H1Function V :=
        H1Function.ofContDiffOnIsOpenBoundedConvexDomain hV ((hψ_smooth n).of_le (by simp))
      simpa [ψ, v, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
        H1Function.ofContDiffOnIsSobolevRegularDomain]
        using v.gradMemL2 i
    have hψ_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm (fun x => ψ n x - w x) 2
              (MeasureTheory.volume.restrict V))
          Filter.atTop (nhds 0) := by
      have hraw :=
        tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
          (U := V) hV (by norm_num : (1 : ENNReal) ≤ 2) (by simp : (2 : ENNReal) ≠ ⊤)
          w.memL2 hball hr0_pos
      refine hraw.congr' ?_
      filter_upwards [hε_eventually_lt_one] with n hε1
      apply MeasureTheory.eLpNorm_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hV.isOpen.measurableSet] with x hx
      have hEq :=
        convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
          (u := w) hV hρ hx hball hr0_pos (hε_pos n) hε1
      simpa [ψ, ρ, ε, unitConvexApproxSequence] using hEq.symm
    have hψ_grad_tendsto : ∀ i : Fin d,
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - w.grad x i)
              2 (MeasureTheory.volume.restrict V))
          Filter.atTop (nhds 0) := by
      intro i
      have hraw :=
        tendsto_eLpNorm_sub_zero_one_sub_mul_unitConvexApproxSequence_of_memLpOn
          (U := V) hV (by norm_num : (1 : ENNReal) ≤ 2) (by simp : (2 : ENNReal) ≠ ⊤)
          (w.grad_memL2 i) hball hr0_pos
      refine hraw.congr' ?_
      filter_upwards [hε_eventually_lt_one] with n hε1
      apply MeasureTheory.eLpNorm_congr_ae
      have hbridge :=
        ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
          (U := V) (ρ := ρ) (u := w) (gi := fun y => w.grad y i)
          (i := i) (p := (2 : ENNReal)) hV hρ (by norm_num : (1 : ENNReal) ≤ 2)
          w.memL2 (w.grad_memL2 i) (w.hasWeakPartialDerivOn i)
          hball hr0_pos (hε_pos n) hε1
      filter_upwards [hbridge, MeasureTheory.ae_restrict_mem hV.isOpen.measurableSet] with x hx hxV
      have hEq :=
        convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
          (u := fun y => w.grad y i) hV hρ hxV hball hr0_pos (hε_pos n) hε1
      rw [hx]
      simpa [ψ, ρ, ε, unitConvexApproxSequence] using congrArg
        (fun t : ℝ => (1 - unitConvexApproxScale n) * t - w.grad x i) hEq.symm
    refine ⟨
      { toH1Function := wφ
        approx := fun n x => φ x * ψ n x
        approx_smooth := by
          intro n
          exact hφ.mul (hψ_smooth n)
        approx_hasCompactSupport := by
          intro n
          simpa [mul_comm] using! hφ_compact.mul_left (f := ψ n)
        approx_support_subset := by
          intro n
          exact ((tsupport_mul_subset_left (f := φ) (g := ψ n)).trans hφ_sub).trans hVU
        tendsto_approx := by
          let μV : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict V
          have hφ_top : MeasureTheory.MemLp φ (⊤ : ENNReal) μV :=
            (hφ.continuous.memLp_of_hasCompactSupport hφ_compact).restrict V
          have hconst_tendsto :
              Filter.Tendsto
                (fun n =>
                  MeasureTheory.eLpNorm φ (⊤ : ENNReal) μV *
                    MeasureTheory.eLpNorm (fun x => ψ n x - w x) 2 μV)
                Filter.atTop
                (nhds (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μV * 0)) :=
            ENNReal.Tendsto.const_mul hψ_tendsto
              (Or.inr hφ_top.eLpNorm_lt_top.ne)
          have hupper :
              ∀ n,
                MeasureTheory.eLpNorm (fun x => φ x * ψ n x - wφ.toFun x) 2
                    (MeasureTheory.volume.restrict U) ≤
                  MeasureTheory.eLpNorm φ (⊤ : ENNReal) μV *
                    MeasureTheory.eLpNorm (fun x => ψ n x - w x) 2 μV := by
            intro n
            have hsupport :
                Function.support (fun x => φ x * ψ n x - wφ.toFun x) ⊆ V := by
              have hEq :
                  (fun x => φ x * ψ n x - wφ.toFun x) =
                    fun x => φ x * (ψ n x - w x) := by
                funext x
                simp [wφ]
                ring
              rw [hEq]
              exact (Function.support_mul_subset_left φ (fun x => ψ n x - w x)).trans
                (subset_tsupport φ |>.trans hφ_sub)
            rw [eLpNorm_restrict_eq_restrict_of_support_subset
              (U := U) (V := V) hVU hsupport]
            have hdiff_mem : MeasureTheory.MemLp (fun x => ψ n x - w x) 2 μV :=
              (hψ_memL2 n).sub w.memL2
            have hEq :
                (fun x => φ x * ψ n x - wφ.toFun x) =
                  φ • (fun x => ψ n x - w x) := by
              funext x
              simp [wφ]
              ring
            rw [hEq]
            exact MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2
              hdiff_mem.aestronglyMeasurable φ
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le
            tendsto_const_nhds ?_ (fun n => zero_le) hupper
          simpa using hconst_tendsto
        tendsto_approx_grad := by
          intro i
          let μV : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict V
          let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
          have hφ_top : MeasureTheory.MemLp φ (⊤ : ENNReal) μV :=
            (hφ.continuous.memLp_of_hasCompactSupport hφ_compact).restrict V
          have hdφ_cont : Continuous dφ := by
            simpa [dφ] using
              (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
          have hdφ_compact : HasCompactSupport dφ := by
            simpa [dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
          have hdφ_top : MeasureTheory.MemLp dφ (⊤ : ENNReal) μV :=
            (hdφ_cont.memLp_of_hasCompactSupport hdφ_compact).restrict V
          have hfirst_tendsto :
              Filter.Tendsto
                (fun n =>
                  MeasureTheory.eLpNorm φ (⊤ : ENNReal) μV *
                    MeasureTheory.eLpNorm
                      (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - w.grad x i) 2 μV)
                Filter.atTop
                (nhds (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μV * 0)) :=
            ENNReal.Tendsto.const_mul (hψ_grad_tendsto i)
              (Or.inr hφ_top.eLpNorm_lt_top.ne)
          have hsecond_tendsto :
              Filter.Tendsto
                (fun n =>
                  MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μV *
                    MeasureTheory.eLpNorm (fun x => ψ n x - w x) 2 μV)
                Filter.atTop
                (nhds (MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μV * 0)) :=
            ENNReal.Tendsto.const_mul hψ_tendsto
              (Or.inr hdφ_top.eLpNorm_lt_top.ne)
          have hsum_tendsto :
              Filter.Tendsto
                (fun n =>
                  MeasureTheory.eLpNorm φ (⊤ : ENNReal) μV *
                      MeasureTheory.eLpNorm
                        (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - w.grad x i) 2 μV +
                    MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μV *
                      MeasureTheory.eLpNorm (fun x => ψ n x - w x) 2 μV)
                Filter.atTop
                (nhds
                  (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μV * 0 +
                    MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μV * 0)) :=
            hfirst_tendsto.add hsecond_tendsto
          have hupper :
              ∀ n,
                MeasureTheory.eLpNorm
                    (fun x =>
                      (fderiv ℝ (fun y => φ y * ψ n y) x) (basisVec i) -
                        wφ.grad x i)
                    2 (MeasureTheory.volume.restrict U) ≤
                  MeasureTheory.eLpNorm φ (⊤ : ENNReal) μV *
                      MeasureTheory.eLpNorm
                        (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - w.grad x i) 2 μV +
                    MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μV *
                      MeasureTheory.eLpNorm (fun x => ψ n x - w x) 2 μV := by
            intro n
            let A : Vec d → ℝ := fun x => φ x *
              ((fderiv ℝ (ψ n) x) (basisVec i) - w.grad x i)
            let B : Vec d → ℝ := fun x => dφ x * (ψ n x - w x)
            have hsupport :
                Function.support
                  (fun x =>
                    (fderiv ℝ (fun y => φ y * ψ n y) x) (basisVec i) -
                      wφ.grad x i) ⊆ V := by
              intro x hx
              by_contra hxV
              have hφ_zero : φ x = 0 := by
                exact image_eq_zero_of_notMem_tsupport (fun hxt => hxV (hφ_sub hxt))
              have hdφ_zero : dφ x = 0 := by
                by_contra hdφ_ne
                exact hxV ((support_euclideanGradient_coord_subset_tsupport (φ := φ) i)
                  (by simpa [dφ, euclideanGradient, euclideanCoordDeriv] using hdφ_ne) |> hφ_sub)
              have hprod_not :
                  x ∉ tsupport (fun y => φ y * ψ n y) := by
                intro hxt
                exact hxV (((tsupport_mul_subset_left (f := φ) (g := ψ n)).trans hφ_sub) hxt)
              have hfd_zero :
                  (fderiv ℝ (fun y => φ y * ψ n y) x) (basisVec i) = 0 := by
                rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hprod_not]
                simp
              have hgrad_zero : wφ.grad x i = 0 := by
                simp [wφ, dφ, hφ_zero, hdφ_zero]
              exact hx (by simp [hfd_zero, hgrad_zero])
            rw [eLpNorm_restrict_eq_restrict_of_support_subset
              (U := U) (V := V) hVU hsupport]
            have hbase_grad_mem :
                MeasureTheory.MemLp
                  (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - w.grad x i) 2 μV :=
              (hψ_grad_memL2 n i).sub (w.gradMemL2 i)
            have hbase_mem : MeasureTheory.MemLp (fun x => ψ n x - w x) 2 μV :=
              (hψ_memL2 n).sub w.memL2
            have hA_mem : MeasureTheory.MemLp A 2 μV := by
              simpa [A, μV] using hbase_grad_mem.mul' hφ_top
            have hB_mem : MeasureTheory.MemLp B 2 μV := by
              simpa [B, dφ, μV] using hbase_mem.mul' hdφ_top
            have hEq :
                (fun x =>
                  (fderiv ℝ (fun y => φ y * ψ n y) x) (basisVec i) -
                    wφ.grad x i) =
                  fun x => A x + B x := by
              funext x
              have hφ_diff : DifferentiableAt ℝ φ x :=
                (hφ.contDiffAt).differentiableAt (by simp)
              have hψ_diff : DifferentiableAt ℝ (ψ n) x :=
                ((hψ_smooth n).contDiffAt).differentiableAt (by simp)
              rw [show (fun y => φ y * ψ n y) = φ * ψ n by rfl,
                fderiv_mul hφ_diff hψ_diff]
              simp [A, B, dφ, wφ, smul_eq_mul, add_apply]
              ring
            rw [hEq]
            refine (MeasureTheory.eLpNorm_add_le hA_mem.aestronglyMeasurable
              hB_mem.aestronglyMeasurable (by norm_num)).trans ?_
            refine add_le_add ?_ ?_
            · simpa [A, mul_comm, mul_left_comm, mul_assoc] using!
                (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2
                  hbase_grad_mem.aestronglyMeasurable φ)
            · simpa [B, dφ, mul_comm, mul_left_comm, mul_assoc] using!
                (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2
                  hbase_mem.aestronglyMeasurable dφ)
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le
            tendsto_const_nhds ?_ (fun n => zero_le) hupper
          simpa [zero_add] using hsum_tendsto }, rfl⟩

end WeakPoissonEquationOn

end

end Homogenization
