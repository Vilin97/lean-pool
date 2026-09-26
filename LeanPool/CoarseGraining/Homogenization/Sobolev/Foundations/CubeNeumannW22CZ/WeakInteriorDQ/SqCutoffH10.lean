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

public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.Localizations

/-! # Sq Cutoff H10 -/

@[expose] public section

namespace Homogenization

open scoped Manifold
open scoped ENNReal Topology

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {U V : Set (Vec d)}
variable {u : H1Function U} {f : Vec d → ℝ}


/-- The squared-cutoff forward difference quotient `η² D_i^+ u` is an ambient
zero-trace test when the cutoff is supported in a shift-safe interior set. -/
theorem memH10_sqCutoffForwardDifferenceQuotient
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    MemH10 U
      (fun x => η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x) := by
  have hDQ : MemH1 V (euclideanForwardDifferenceQuotient step i u.toFun) := by
    refine ⟨u.forwardDifferenceQuotientOn step i hV.isOpen hVU hVshift, ?_⟩
    funext x
    simp
  simpa using
    memH10_localizedMul_of_contDiff_hasCompactSupport_tsupport_subset
      (U := U) (V := V) hV hVU
      (φ := fun x => η x ^ 2)
      (F := euclideanForwardDifferenceQuotient step i u.toFun)
      (contDiff_sq hη) (hasCompactSupport_sq hη_compact)
      ((tsupport_sq_subset η).trans hη_sub)
      hDQ

/-- The squared-cutoff forward quotient is genuinely supported in the ambient
domain when the cutoff support lies in an interior subset. -/
theorem support_sqCutoffForwardDifferenceQuotient_subset
    (u : H1Function U) (hVU : V ⊆ U) (step : ℝ) (i : Fin d)
    {η : Vec d → ℝ} (hη_sub : tsupport η ⊆ V) :
    Function.support
      (fun x => η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x) ⊆ U :=
  (Function.support_mul_subset_left
    (fun x => η x ^ 2) (euclideanForwardDifferenceQuotient step i u.toFun)).trans
    ((subset_tsupport (fun x => η x ^ 2)).trans
      (((tsupport_sq_subset η).trans hη_sub).trans hVU))

/-- Chosen ambient `H¹₀(U)` representative of `η² D_i^+ u`. -/
noncomputable def sqCutoffForwardDifferenceQuotientToH10
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    H10Function U :=
  Classical.choose
    (memH10_sqCutoffForwardDifferenceQuotient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub)

@[simp] theorem sqCutoffForwardDifferenceQuotientToH10_toFun
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (sqCutoffForwardDifferenceQuotientToH10
      (U := U) (V := V) u hV hVU step i hVshift
      hη hη_compact hη_sub).toH1Function.toFun =
      fun x => η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x :=
  Classical.choose_spec
    (memH10_sqCutoffForwardDifferenceQuotient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub)

/-- Coordinatewise gradient identification between the chosen ambient
`H¹₀(U)` representative of `η²D_i^+u` and the explicit ambient `H¹`
localized product representative. -/
theorem sqCutoffForwardDifferenceQuotientToH10_grad_coord_ae
    (hU : IsOpen U)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (fun x =>
        (sqCutoffForwardDifferenceQuotientToH10
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub).toH1Function.grad x j) =ᵐ[
          MeasureTheory.volume.restrict U]
      fun x =>
        (localizedSqCutoffForwardDifferenceQuotientToAmbient
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub).grad x j := by
  let ψ : H10Function U :=
    sqCutoffForwardDifferenceQuotientToH10
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  let w : H1Function U :=
    localizedSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  have hψ_fun : ψ.toH1Function.toFun = w.toFun := by
    funext x
    simp [ψ, w]
  have hψ_loc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => ψ.toH1Function.grad x j) U MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((ψ.toH1Function.gradMemL2 j).locallyIntegrable (by norm_num))
  have hw_loc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => w.grad x j) U MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((w.gradMemL2 j).locallyIntegrable (by norm_num))
  have hψ_weak :
      HasWeakPartialDerivOn U j ψ.toH1Function.toFun
        (fun x => ψ.toH1Function.grad x j) :=
    ψ.toH1Function.hasWeakPartialDerivOn j
  have hw_weak :
      HasWeakPartialDerivOn U j ψ.toH1Function.toFun
        (fun x => w.grad x j) := by
    rw [hψ_fun]
    exact w.hasWeakPartialDerivOn j
  have hae := HasWeakPartialDerivOn.ae_eq hU hψ_loc hw_loc hψ_weak hw_weak
  simpa [ψ, w] using hae

/-- Vector-valued gradient identification for the chosen ambient `H¹₀(U)`
representative of `η²D_i^+u`. -/
theorem sqCutoffForwardDifferenceQuotientToH10_grad_ae
    (hU : IsOpen U)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (fun x =>
        (sqCutoffForwardDifferenceQuotientToH10
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub).toH1Function.grad x) =ᵐ[
          MeasureTheory.volume.restrict U]
      fun x =>
        (localizedSqCutoffForwardDifferenceQuotientToAmbient
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub).grad x := by
  have hcoord :
      ∀ j : Fin d,
        (fun x =>
            (sqCutoffForwardDifferenceQuotientToH10
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).toH1Function.grad x j) =ᵐ[
              MeasureTheory.volume.restrict U]
          fun x =>
            (localizedSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x j := by
    intro j
    exact sqCutoffForwardDifferenceQuotientToH10_grad_coord_ae
      hU u hV hVU step i j hVshift hη hη_compact hη_sub
  filter_upwards [(Filter.eventually_all (l := MeasureTheory.ae (MeasureTheory.volume.restrict U))).2 hcoord] with x hx
  ext j
  exact hx j

/-- The whole-space backward quotient bound specialized to the squared-cutoff
forward difference quotient test. -/
theorem eLpNorm_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_le_eLpNorm_sqCutoffForwardDifferenceQuotientToH10_grad
    (hU : IsOpen U)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    MeasureTheory.eLpNorm
        (euclideanBackwardDifferenceQuotient step i
          (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y))
        2 MeasureTheory.volume ≤
      MeasureTheory.eLpNorm
        (fun x =>
          (sqCutoffForwardDifferenceQuotientToH10
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).toH1Function.grad x i)
        2 (MeasureTheory.volume.restrict U) := by
  let ψ : H10Function U :=
    sqCutoffForwardDifferenceQuotientToH10
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  have hψ_support : Function.support ψ.toH1Function.toFun ⊆ U := by
    simpa [ψ] using
      support_sqCutoffForwardDifferenceQuotient_subset
        (U := U) (V := V) u hVU step i hη_sub
  simpa [ψ] using
    eLpNorm_h10_backwardDifferenceQuotient_le_eLpNorm_grad
      (U := U) hU.measurableSet ψ hψ_support hstep i

/-- The squared-cutoff direct test is controlled by the explicit product-rule
gradient of `η²D_i^+u`. -/
theorem eLpNorm_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_le_eLpNorm_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad
    (hU : IsOpen U)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    MeasureTheory.eLpNorm
        (euclideanBackwardDifferenceQuotient step i
          (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y))
        2 MeasureTheory.volume ≤
      MeasureTheory.eLpNorm
        (fun x =>
          (localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x i)
        2 (MeasureTheory.volume.restrict U) := by
  have hbase :=
    eLpNorm_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_le_eLpNorm_sqCutoffForwardDifferenceQuotientToH10_grad
      (U := U) (V := V) hU u hV hVU hstep i hVshift hη hη_compact hη_sub
  have hgrad_ae :=
    sqCutoffForwardDifferenceQuotientToH10_grad_coord_ae
      (U := U) (V := V) hU u hV hVU step i i hVshift hη hη_compact hη_sub
  exact hbase.trans (le_of_eq (MeasureTheory.eLpNorm_congr_ae hgrad_ae))

/-- The shifted factor `η(x-h e_i)² D_i^- u(x)` is an ambient zero-trace
test.  It is the translated companion to
`memH10_sqCutoffForwardDifferenceQuotient`, with the backward quotient living
on the translated interior set `V + h e_i`. -/
theorem memH10_sqShiftedCutoffBackwardDifferenceQuotient
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    MemH10 U
      (fun x =>
        η (euclideanCoordShift (-step) i x) ^ 2 *
          euclideanBackwardDifferenceQuotient step i u.toFun x) := by
  let W : Set (Vec d) := translateSet (step • basisVec i) V
  let ηshift : Vec d → ℝ := fun x => η (euclideanCoordShift (-step) i x)
  have hW : IsOpenBoundedConvexDomain W := by
    simpa [W] using IsOpenBoundedConvexDomain.translateSet hV (step • basisVec i)
  have hWU : W ⊆ U := by
    intro x hx
    have hxV : x - step • basisVec i ∈ V := by
      simpa [W] using (mem_translateSet_iff_sub_mem).1 hx
    have hxShift : x - step • basisVec i ∈
        translateSet ((-step) • basisVec i) U :=
      hVshift hxV
    have hxU :
        (x - step • basisVec i) - (-step) • basisVec i ∈ U :=
      (mem_translateSet_iff_sub_mem).1 hxShift
    simpa [sub_eq_add_neg, neg_smul, add_assoc, add_left_comm, add_comm] using hxU
  have hWshift : W ⊆ translateSet (step • basisVec i) U := by
    intro x hx
    have hxV : x - step • basisVec i ∈ V := by
      simpa [W] using (mem_translateSet_iff_sub_mem).1 hx
    exact (mem_translateSet_iff_sub_mem).2 (hVU hxV)
  have hηshift : ContDiff ℝ (⊤ : ℕ∞) ηshift := by
    simpa [ηshift] using contDiff_comp_euclideanCoordShift hη (-step) i
  have hηshift_compact : HasCompactSupport ηshift := by
    simpa [ηshift] using hasCompactSupport_comp_euclideanCoordShift hη_compact (-step) i
  have hηshift_sub : tsupport ηshift ⊆ W := by
    intro x hx
    have hxpre : x - step • basisVec i ∈ tsupport η := by
      have hxpre' : x + (-step) • basisVec i ∈ tsupport η := by
        rw [show ηshift = η ∘ Homeomorph.addRight ((-step) • basisVec i) by
          funext y
          rfl,
          tsupport_comp_eq_preimage η (Homeomorph.addRight ((-step) • basisVec i))] at hx
        exact hx
      simpa [euclideanCoordShift, sub_eq_add_neg, neg_smul] using hxpre'
    exact (mem_translateSet_iff_sub_mem).2 (hη_sub hxpre)
  have hDQ : MemH1 W (euclideanBackwardDifferenceQuotient step i u.toFun) := by
    refine ⟨u.backwardDifferenceQuotientOn step i hW.isOpen hWU hWshift, ?_⟩
    funext x
    simp
  simpa [ηshift] using
    memH10_localizedMul_of_contDiff_hasCompactSupport_tsupport_subset
      (U := U) (V := W) hW hWU
      (φ := fun x => ηshift x ^ 2)
      (F := euclideanBackwardDifferenceQuotient step i u.toFun)
      (contDiff_sq hηshift) (hasCompactSupport_sq hηshift_compact)
      ((tsupport_sq_subset ηshift).trans hηshift_sub)
      hDQ

/-- Ambient `H¹` representative of the shifted term
`η(x-h e_i)² D_i^- u(x)`, localized on the translated interior set
`V + h e_i`. -/
noncomputable def localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    H1Function U := by
  let W : Set (Vec d) := translateSet (step • basisVec i) V
  let ηshift : Vec d → ℝ := fun x => η (euclideanCoordShift (-step) i x)
  have hW : IsOpenBoundedConvexDomain W := by
    simpa [W] using IsOpenBoundedConvexDomain.translateSet hV (step • basisVec i)
  have hWU : W ⊆ U := by
    intro x hx
    have hxV : x - step • basisVec i ∈ V := by
      simpa [W] using (mem_translateSet_iff_sub_mem).1 hx
    have hxShift : x - step • basisVec i ∈
        translateSet ((-step) • basisVec i) U :=
      hVshift hxV
    have hxU :
        (x - step • basisVec i) - (-step) • basisVec i ∈ U :=
      (mem_translateSet_iff_sub_mem).1 hxShift
    simpa [sub_eq_add_neg, neg_smul, add_assoc, add_left_comm, add_comm] using hxU
  have hWshift : W ⊆ translateSet (step • basisVec i) U := by
    intro x hx
    have hxV : x - step • basisVec i ∈ V := by
      simpa [W] using (mem_translateSet_iff_sub_mem).1 hx
    exact (mem_translateSet_iff_sub_mem).2 (hVU hxV)
  have hηshift : ContDiff ℝ (⊤ : ℕ∞) ηshift := by
    simpa [ηshift] using contDiff_comp_euclideanCoordShift hη (-step) i
  have hηshift_compact : HasCompactSupport ηshift := by
    simpa [ηshift] using hasCompactSupport_comp_euclideanCoordShift hη_compact (-step) i
  have hηshift_sub : tsupport ηshift ⊆ W := by
    intro x hx
    have hxpre : x - step • basisVec i ∈ tsupport η := by
      have hxpre' : x + (-step) • basisVec i ∈ tsupport η := by
        rw [show ηshift = η ∘ Homeomorph.addRight ((-step) • basisVec i) by
          funext y
          rfl,
          tsupport_comp_eq_preimage η (Homeomorph.addRight ((-step) • basisVec i))] at hx
        exact hx
      simpa [euclideanCoordShift, sub_eq_add_neg, neg_smul] using hxpre'
    exact (mem_translateSet_iff_sub_mem).2 (hη_sub hxpre)
  exact
    localizedMulContDiffHasCompactSupportToAmbient
      (U := U) (V := W)
      (u.backwardDifferenceQuotientOn step i hW.isOpen hWU hWshift)
      hW.isOpen.measurableSet hWU
      (φ := fun x => ηshift x ^ 2)
      (contDiff_sq hηshift) (hasCompactSupport_sq hηshift_compact)
      ((tsupport_sq_subset ηshift).trans hηshift_sub)

@[simp] theorem localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient_toFun
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift
      hη hη_compact hη_sub).toFun =
      fun x =>
        η (euclideanCoordShift (-step) i x) ^ 2 *
          euclideanBackwardDifferenceQuotient step i u.toFun x := by
  funext x
  unfold localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
  dsimp only
  refine (congrFun (localizedMulContDiffHasCompactSupportToAmbient_toFun
    (w := _) (hV_meas := _) (hVU := _) (hφ := _) (hφ_compact := _) (hφ_sub := _)) x).trans ?_
  exact congrArg (fun y => η (euclideanCoordShift (-step) i x) ^ 2 * y)
    (H1Function.backwardDifferenceQuotientOn_toFun (u := u) (h := step) (i := i)
      (hVopen := _) (hVU := _) (hVshift := _) x)

theorem localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient_grad_eq_shift
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V)
    (x : Vec d) :
    (localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift
      hη hη_compact hη_sub).grad x =
      (localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad (euclideanCoordShift (-step) i x) := by
  have hW : IsOpenBoundedConvexDomain (translateSet (step • basisVec i) V) := by
    simpa using IsOpenBoundedConvexDomain.translateSet hV (step • basisVec i)
  have hWU : translateSet (step • basisVec i) V ⊆ U := by
    intro y hy
    have hyV : y - step • basisVec i ∈ V := by
      simpa using (mem_translateSet_iff_sub_mem).1 hy
    have hyShift : y - step • basisVec i ∈
        translateSet ((-step) • basisVec i) U :=
      hVshift hyV
    have hyU :
        (y - step • basisVec i) - (-step) • basisVec i ∈ U :=
      (mem_translateSet_iff_sub_mem).1 hyShift
    simpa [sub_eq_add_neg, neg_smul, add_assoc, add_left_comm, add_comm] using hyU
  have hWshift : translateSet (step • basisVec i) V ⊆ translateSet (step • basisVec i) U := by
    intro y hy
    have hyV : y - step • basisVec i ∈ V := by
      simpa using (mem_translateSet_iff_sub_mem).1 hy
    exact (mem_translateSet_iff_sub_mem).2 (hVU hyV)
  have hηshift : ContDiff ℝ (⊤ : ℕ∞) (fun y => η (euclideanCoordShift (-step) i y)) := by
    simpa using contDiff_comp_euclideanCoordShift hη (-step) i
  have hηshift_compact : HasCompactSupport (fun y => η (euclideanCoordShift (-step) i y)) := by
    simpa using hasCompactSupport_comp_euclideanCoordShift hη_compact (-step) i
  have hηshift_sub : tsupport (fun y => η (euclideanCoordShift (-step) i y)) ⊆
      translateSet (step • basisVec i) V := by
    intro y hy
    have hxpre : y - step • basisVec i ∈ tsupport η := by
      have hxpre' : y + (-step) • basisVec i ∈ tsupport η := by
        rw [show (fun z => η (euclideanCoordShift (-step) i z)) =
              η ∘ Homeomorph.addRight ((-step) • basisVec i) by
            funext z
            rfl,
            tsupport_comp_eq_preimage η (Homeomorph.addRight ((-step) • basisVec i))] at hy
        exact hy
      simpa [euclideanCoordShift, sub_eq_add_neg, neg_smul] using hxpre'
    exact (mem_translateSet_iff_sub_mem).2 (hη_sub hxpre)
  have hval :
      localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
          (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
        = localizedMulContDiffHasCompactSupportToAmbient
            (U := U) (V := translateSet (step • basisVec i) V)
            (u.backwardDifferenceQuotientOn step i hW.isOpen hWU hWshift)
            hW.isOpen.measurableSet hWU
            (φ := fun y => η (euclideanCoordShift (-step) i y) ^ 2)
            (contDiff_sq hηshift) (hasCompactSupport_sq hηshift_compact)
            ((tsupport_sq_subset
              (fun y => η (euclideanCoordShift (-step) i y))).trans hηshift_sub) :=
    rfl
  rw [hval]
  ext j
  simp [localizedSqCutoffForwardDifferenceQuotientToAmbient,
    euclideanCoordShift, sub_eq_add_neg, neg_smul, add_left_comm, add_comm]
  left
  simpa [euclideanCoordDeriv, euclideanCoordShift, sub_eq_add_neg, neg_smul] using
    euclideanCoordDeriv_comp_euclideanCoordShift (-step) i j (fun x => η x ^ 2) x

/-- Pairing against the shifted localized gradient is supported in the
translated interior set. -/
theorem support_vecDot_localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient_grad_subset
    (G : Vec d → Vec d)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    Function.support
      (fun x =>
        vecDot (G x)
          ((localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)) ⊆
      translateSet (step • basisVec i) V := by
  intro x hx
  by_contra hxW
  have hyV : euclideanCoordShift (-step) i x ∉ V := by
    intro hy
    exact hxW (by
      rw [mem_translateSet_iff_sub_mem]
      simpa [euclideanCoordShift, sub_eq_add_neg, neg_smul] using hy)
  have hforward_zero :
      (localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad (euclideanCoordShift (-step) i x) = 0 := by
    ext j
    by_contra hne
    exact hyV
      (support_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad_subset
        (U := U) (V := V) u hV hVU step i j hVshift hη hη_compact hη_sub hne)
  have hshift_zero :
      (localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad x = 0 := by
    rw [localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient_grad_eq_shift]
    exact hforward_zero
  exact hx (by simp [hshift_zero, vecDot])

/-- Transport the shifted localized-gradient pairing from `U` back to the
interior set `V`. -/
theorem integral_vecDot_localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient_grad_eq_integral_on
    (G : Vec d → Vec d)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in U,
        vecDot (G x)
          ((localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume =
      ∫ x in V,
        vecDot (G (euclideanCoordShift step i x))
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x)
        ∂MeasureTheory.volume := by
  let W : Set (Vec d) := translateSet (step • basisVec i) V
  let F : H1Function U :=
    localizedSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  let S : H1Function U :=
    localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  have hWU : W ⊆ U := by
    intro x hx
    have hxV : x - step • basisVec i ∈ V := by
      simpa [W] using (mem_translateSet_iff_sub_mem).1 hx
    have hxShift : x - step • basisVec i ∈
        translateSet ((-step) • basisVec i) U :=
      hVshift hxV
    have hxU :
        (x - step • basisVec i) - (-step) • basisVec i ∈ U :=
      (mem_translateSet_iff_sub_mem).1 hxShift
    simpa [sub_eq_add_neg, neg_smul, add_assoc, add_left_comm, add_comm] using hxU
  have hsupport :
      Function.support (fun x => vecDot (G x) (S.grad x)) ⊆ W := by
    simpa [S, W] using
      support_vecDot_localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient_grad_subset
        (U := U) (V := V) G u hV hVU step i hVshift hη hη_compact hη_sub
  have hrestrict :
      ∫ x in U, vecDot (G x) (S.grad x) ∂MeasureTheory.volume =
        ∫ x in W, vecDot (G x) (S.grad x) ∂MeasureTheory.volume :=
    integral_subset_of_support_subset hWU hsupport
  have hshift :
      ∫ x in W, vecDot (G x) (S.grad x) ∂MeasureTheory.volume =
        ∫ x in W,
          vecDot (G x) (F.grad (euclideanCoordShift (-step) i x))
          ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    simp [F, S, localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient_grad_eq_shift]
  let z : Vec d := step • basisVec i
  have hchange :=
    (setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z V
      (fun x => vecDot (G x) (F.grad (x - z)))).symm
  calc
    ∫ x in U, vecDot (G x) (S.grad x) ∂MeasureTheory.volume =
        ∫ x in W, vecDot (G x) (S.grad x) ∂MeasureTheory.volume := hrestrict
    _ = ∫ x in W,
          vecDot (G x) (F.grad (euclideanCoordShift (-step) i x))
          ∂MeasureTheory.volume := hshift
    _ = ∫ x in V,
          vecDot (G (euclideanCoordShift step i x)) (F.grad x)
          ∂MeasureTheory.volume := by
          simpa [W, F, z, euclideanCoordShift, sub_eq_add_neg, neg_smul,
            add_assoc, add_left_comm, add_comm] using hchange

/-- Explicit ambient `H¹` representative of the direct test
`D_i^-(η² D_i^+u)`. -/
noncomputable def backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    H1Function U :=
  step⁻¹ •
    (localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub -
      localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub)

@[simp] theorem backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient_toFun
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift
      hη hη_compact hη_sub).toFun =
      euclideanBackwardDifferenceQuotient step i
        (fun x => η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x) := by
  funext x
  rw [euclideanBackwardDifferenceQuotient_sq_mul_forwardDifferenceQuotient]
  simp [backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient]

/-- The direct difference-quotient test `D_i^-(η²D_i^+u)` is genuinely
supported in the ambient domain. -/
theorem support_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_subset
    (u : H1Function U) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη_sub : tsupport η ⊆ V) :
    Function.support
      (euclideanBackwardDifferenceQuotient step i
        (fun x => η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x)) ⊆ U := by
  intro x hx
  by_contra hxU
  have hη_zero : η x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hxt => hxU (hVU (hη_sub hxt)))
  have hη_shift_zero : η (euclideanCoordShift (-step) i x) = 0 := by
    refine image_eq_zero_of_notMem_tsupport ?_
    intro hxt
    have hyV : euclideanCoordShift (-step) i x ∈ V := hη_sub hxt
    have hyShift : euclideanCoordShift (-step) i x ∈
        translateSet ((-step) • basisVec i) U :=
      hVshift hyV
    have hxU' : x ∈ U := by
      have hmem :
          euclideanCoordShift (-step) i x - (-step) • basisVec i ∈ U :=
        (mem_translateSet_iff_sub_mem).1 hyShift
      simpa [euclideanCoordShift, sub_eq_add_neg, neg_smul, add_assoc,
        add_left_comm, add_comm] using hmem
    exact hxU hxU'
  have hzero :
      euclideanBackwardDifferenceQuotient step i
          (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x = 0 := by
    have hη_shift_zero' : η (x + -(step • basisVec i)) = 0 := by
      simpa [euclideanCoordShift, neg_smul] using hη_shift_zero
    rw [euclideanBackwardDifferenceQuotient_sq_mul_forwardDifferenceQuotient]
    simp [hη_zero, hη_shift_zero']
  exact hx hzero

@[simp] theorem backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient_grad
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift
      hη hη_compact hη_sub).grad =
      fun x =>
        step⁻¹ •
          ((localizedSqCutoffForwardDifferenceQuotientToAmbient
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).grad x -
            (localizedSqShiftedCutoffBackwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x) := by
  funext x j
  simp [backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient]

/-- The direct weak-equation test `D_i^- (η² D_i^+ u)` is ambient zero-trace.

This is the key admissibility bridge for the direct difference-quotient
energy estimate: the original weak equation can be tested against a difference
quotient of the cutoff-weighted forward quotient, so the forcing remains `f`
rather than `D_i^+ f`. -/
theorem memH10_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    MemH10 U
      (euclideanBackwardDifferenceQuotient step i
        (fun x => η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x)) := by
  have hforward :
      MemH10 U
        (fun x => η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x) :=
    memH10_sqCutoffForwardDifferenceQuotient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  have hshifted :
      MemH10 U
        (fun x =>
          η (euclideanCoordShift (-step) i x) ^ 2 *
            euclideanBackwardDifferenceQuotient step i u.toFun x) :=
    memH10_sqShiftedCutoffBackwardDifferenceQuotient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  have hdiff :
      MemH10 U
        (fun x =>
          η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x -
            η (euclideanCoordShift (-step) i x) ^ 2 *
              euclideanBackwardDifferenceQuotient step i u.toFun x) :=
    memH10_sub hforward hshifted
  have hscaled :
      MemH10 U
        (fun x =>
          step⁻¹ *
            (η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x -
              η (euclideanCoordShift (-step) i x) ^ 2 *
                euclideanBackwardDifferenceQuotient step i u.toFun x)) :=
    memH10_smul step⁻¹ hdiff
  convert hscaled using 1
  funext x
  exact euclideanBackwardDifferenceQuotient_sq_mul_forwardDifferenceQuotient
    step i η u.toFun x

/-- Chosen `H¹₀(U)` representative of the direct difference-quotient test
`D_i^- (η² D_i^+ u)`. -/
noncomputable def backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    H10Function U :=
  Classical.choose
    (memH10_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub)

@[simp] theorem backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10_toFun
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub).toH1Function.toFun =
      euclideanBackwardDifferenceQuotient step i
        (fun x => η x ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun x) :=
  Classical.choose_spec
    (memH10_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub)

/-- Coordinatewise gradient identification between the chosen `H¹₀`
representative of `D_i^-(η² D_i^+u)` and the explicit ambient `H¹`
representative built from localized shifted pieces. -/
theorem backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10_grad_coord_ae
    (hU : IsOpen U)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i j : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (fun x =>
        (backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub).toH1Function.grad x j) =ᵐ[
          MeasureTheory.volume.restrict U]
      fun x =>
        (backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub).grad x j := by
  let ψ : H10Function U :=
    backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  let w : H1Function U :=
    backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
      (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
  have hψ_fun : ψ.toH1Function.toFun = w.toFun := by
    funext x
    simp [ψ, w]
  have hψ_loc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => ψ.toH1Function.grad x j) U MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((ψ.toH1Function.gradMemL2 j).locallyIntegrable (by norm_num))
  have hw_loc :
      MeasureTheory.LocallyIntegrableOn
        (fun x => w.grad x j) U MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((w.gradMemL2 j).locallyIntegrable (by norm_num))
  have hψ_weak :
      HasWeakPartialDerivOn U j ψ.toH1Function.toFun
        (fun x => ψ.toH1Function.grad x j) :=
    ψ.toH1Function.hasWeakPartialDerivOn j
  have hw_weak :
      HasWeakPartialDerivOn U j ψ.toH1Function.toFun
        (fun x => w.grad x j) := by
    rw [hψ_fun]
    exact w.hasWeakPartialDerivOn j
  have hae := HasWeakPartialDerivOn.ae_eq hU hψ_loc hw_loc hψ_weak hw_weak
  simpa [ψ, w] using hae

/-- Vector-valued gradient identification for the direct difference-quotient
test. -/
theorem backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10_grad_ae
    (hU : IsOpen U)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    (fun x =>
        (backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub).toH1Function.grad x) =ᵐ[
          MeasureTheory.volume.restrict U]
      fun x =>
        (backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub).grad x := by
  have hcoord :
      ∀ j : Fin d,
        (fun x =>
            (backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).toH1Function.grad x j) =ᵐ[
              MeasureTheory.volume.restrict U]
          fun x =>
            (backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x j := by
    intro j
    exact backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10_grad_coord_ae
      hU u hV hVU step i j hVshift hη hη_compact hη_sub
  filter_upwards [(Filter.eventually_all (l := MeasureTheory.ae (MeasureTheory.volume.restrict U))).2 hcoord] with x hx
  ext j
  exact hx j

/-- Integral-square form of the specialized direct-test quotient bound. -/
theorem integral_sq_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_le_integral_sq_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad
    (hU : IsOpen U)
    (u : H1Function U) (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    {step : ℝ} (hstep : step ≠ 0) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in U,
        (euclideanBackwardDifferenceQuotient step i
          (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x) ^ 2
        ∂MeasureTheory.volume ≤
      ∫ x in U,
        ((localizedSqCutoffForwardDifferenceQuotientToAmbient
          (U := U) (V := V) u hV hVU step i hVshift
          hη hη_compact hη_sub).grad x i) ^ 2
        ∂MeasureTheory.volume := by
  let T : Vec d → ℝ :=
    euclideanBackwardDifferenceQuotient step i
      (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y)
  let G : Vec d → ℝ :=
    fun x =>
      (localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).grad x i
  have hnorm_global :=
    eLpNorm_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_le_eLpNorm_localizedSqCutoffForwardDifferenceQuotientToAmbient_grad
      (U := U) (V := V) hU u hV hVU hstep i hVshift hη hη_compact hη_sub
  have hT_support : Function.support T ⊆ U := by
    simpa [T] using
      support_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_subset
        (U := U) (V := V) u hVU step i hVshift hη_sub
  have hT_norm_restrict :
      MeasureTheory.eLpNorm T 2 MeasureTheory.volume =
        MeasureTheory.eLpNorm T 2 (MeasureTheory.volume.restrict U) :=
    eLpNorm_eq_restrict_of_support_subset (U := U) hT_support
  have hnorm :
      MeasureTheory.eLpNorm T 2 (MeasureTheory.volume.restrict U) ≤
        MeasureTheory.eLpNorm G 2 (MeasureTheory.volume.restrict U) := by
    rwa [hT_norm_restrict] at hnorm_global
  have hT_mem : MeasureTheory.MemLp T 2 (MeasureTheory.volume.restrict U) := by
    let ψ : H10Function U :=
      backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
        (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub
    simpa [T, ψ] using ψ.toH1Function.memL2
  have hG_mem : MeasureTheory.MemLp G 2 (MeasureTheory.volume.restrict U) := by
    simpa [G] using
      (localizedSqCutoffForwardDifferenceQuotientToAmbient
        (U := U) (V := V) u hV hVU step i hVshift
        hη hη_compact hη_sub).gradMemL2 i
  have htoReal_le :
      ENNReal.toReal (MeasureTheory.eLpNorm T 2 (MeasureTheory.volume.restrict U)) ≤
        ENNReal.toReal (MeasureTheory.eLpNorm G 2 (MeasureTheory.volume.restrict U)) :=
    (ENNReal.toReal_le_toReal hT_mem.eLpNorm_ne_top hG_mem.eLpNorm_ne_top).2 hnorm
  have hsq_le :
      (ENNReal.toReal (MeasureTheory.eLpNorm T 2 (MeasureTheory.volume.restrict U))) ^ 2 ≤
        (ENNReal.toReal (MeasureTheory.eLpNorm G 2 (MeasureTheory.volume.restrict U))) ^ 2 :=
    (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).2 htoReal_le
  rw [toReal_eLpNorm_two_sq_eq_integral_sq hT_mem,
    toReal_eLpNorm_two_sq_eq_integral_sq hG_mem] at hsq_le
  simpa [T, G] using hsq_le

/-- Original weak equation tested against the direct difference-quotient test.
The right-hand side contains the undifferentiated forcing `f`; the next stage
is to identify the left-hand side by finite-difference summation by parts. -/
theorem test_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotientToH10
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
    (step : ℝ) (i : Fin d)
    (hVshift : V ⊆ translateSet ((-step) • basisVec i) U)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (hη_sub : tsupport η ⊆ V) :
    ∫ x in U,
        vecDot (u.grad x)
          ((backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
            (U := U) (V := V) u hV hVU step i hVshift
            hη hη_compact hη_sub).toH1Function.grad x)
        ∂MeasureTheory.volume =
      ∫ x in U,
        f x *
          euclideanBackwardDifferenceQuotient step i
            (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x
        ∂MeasureTheory.volume := by
  have htest :=
    h.h10 hU hf
      (backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
        (U := U) (V := V) u hV hVU step i hVshift hη hη_compact hη_sub)
  simpa using htest

/-- Original weak equation tested against the direct difference-quotient test,
with the left-hand side rewritten using the explicit ambient `H¹`
representative of that test. -/
theorem test_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotient_explicitGradient
    (h : WeakPoissonEquationOn U u f) (hU : IsOpen U) (hf : MemScalarL2 U f)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U)
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
      ∫ x in U,
        f x *
          euclideanBackwardDifferenceQuotient step i
            (fun y => η y ^ 2 * euclideanForwardDifferenceQuotient step i u.toFun y) x
        ∂MeasureTheory.volume := by
  have hbase :=
    h.test_backwardDifferenceQuotient_sqCutoffForwardDifferenceQuotientToH10
      hU hf hV hVU step i hVshift hη hη_compact hη_sub
  have hgrad_ae :=
    backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10_grad_ae
      hU u hV hVU step i hVshift hη hη_compact hη_sub
  have hleft :
      ∫ x in U,
          vecDot (u.grad x)
            ((backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToH10
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U,
          vecDot (u.grad x)
            ((backwardDifferenceQuotientSqCutoffForwardDifferenceQuotientToAmbient
              (U := U) (V := V) u hV hVU step i hVshift
              hη hη_compact hη_sub).grad x)
          ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hgrad_ae] with x hx
    simp [hx]
  exact hleft.symm.trans hbase

end WeakPoissonEquationOn

end

end Homogenization
