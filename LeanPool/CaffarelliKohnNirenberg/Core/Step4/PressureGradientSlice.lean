/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientBase
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.WeakPressureSlice
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative

/-!
# Pressure Gradient Slice

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-- A function which is (C^1) on an open set has its classical coordinate
derivatives as weak derivatives on that set. -/
theorem pressure_hasWeakPartialDerivOn_of_contDiffOn
    {B : Set Vec3} (hB : IsOpen B) {H : Vec3 → ℝ} {i : Fin 3}
    (hH : ContDiffOn ℝ 1 H B) :
    HasWeakPartialDerivOn B i H
      (fun x => (fderiv ℝ H x) (basisVec i)) := by
  intro ψ hψ hψc hψB
  have hHloc : LocallyIntegrableOn H B volume :=
    hH.continuousOn.locallyIntegrableOn hB.measurableSet
  have hHd : ContinuousOn (fun x => (fderiv ℝ H x) (basisVec i)) B :=
    (hH.continuousOn_fderiv_of_isOpen hB (by simp)).clm_apply
      continuousOn_const
  have hHderivLoc : LocallyIntegrableOn
      (fun x => (fderiv ℝ H x) (basisVec i)) B volume :=
    hHd.locallyIntegrableOn hB.measurableSet
  have hψd : Continuous (fun x => (fderiv ℝ ψ x) (basisVec i)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hleft : IntegrableOn
      (fun x => H x * (fderiv ℝ ψ x) (basisVec i)) B volume := by
    have hmulLoc := hHloc.mul_continuousOn hψd.continuousOn
      hB.isLocallyClosed
    have hmulK := hmulLoc.integrableOn_compact_subset hψB hψc.isCompact
    have hmulFull := hmulK.integrable_of_forall_notMem_eq_zero (by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := fun y =>
        (fderiv ℝ ψ y) (basisVec i))
        (fun hxt => hx ((tsupport_fderiv_apply_subset ℝ (basisVec i)) hxt))]
      simp)
    exact hmulFull.integrableOn
  have hright : IntegrableOn
      (fun x => (fderiv ℝ H x) (basisVec i) * ψ x) B volume := by
    have hmulLoc := hHderivLoc.mul_continuousOn hψ.continuous.continuousOn
      hB.isLocallyClosed
    have hmulK := hmulLoc.integrableOn_compact_subset hψB hψc.isCompact
    have hmulFull := hmulK.integrable_of_forall_notMem_eq_zero (by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := ψ)
        (fun hxt => hx hxt)]
      simp)
    exact hmulFull.integrableOn
  have hprod : IntegrableOn (fun x => H x * ψ x) B volume := by
    have hmulLoc := hHloc.mul_continuousOn hψ.continuous.continuousOn
      hB.isLocallyClosed
    have hmulK := hmulLoc.integrableOn_compact_subset hψB hψc.isCompact
    have hmulFull := hmulK.integrable_of_forall_notMem_eq_zero (by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := ψ)
        (fun hxt => hx hxt)]
      simp)
    exact hmulFull.integrableOn
  have hfdiff : ∀ x ∈ tsupport ψ, DifferentiableAt ℝ H x := by
    intro x hx
    exact (hH.differentiableOn (by simp) x (hψB hx)).differentiableAt
      (hB.mem_nhds (hψB hx))
  have hψdiff : ∀ x ∈ tsupport H, DifferentiableAt ℝ ψ x := by
    intro x _
    exact hψ.differentiable (by simp) x
  have hrightGlobal : Integrable
      (fun x => (fderiv ℝ H x) (basisVec i) * ψ x) volume := by
    have hmulLoc := hHderivLoc.mul_continuousOn hψ.continuous.continuousOn
      hB.isLocallyClosed
    have hmulK := hmulLoc.integrableOn_compact_subset hψB hψc.isCompact
    exact hmulK.integrable_of_forall_notMem_eq_zero (by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := ψ)
        (fun hxt => hx hxt)]
      simp)
  have hleftGlobal : Integrable
      (fun x => H x * (fderiv ℝ ψ x) (basisVec i)) volume := by
    have hmulLoc := hHloc.mul_continuousOn hψd.continuousOn
      hB.isLocallyClosed
    have hmulK := hmulLoc.integrableOn_compact_subset hψB hψc.isCompact
    exact hmulK.integrable_of_forall_notMem_eq_zero (by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := fun y =>
        (fderiv ℝ ψ y) (basisVec i))
        (fun hxt => hx ((tsupport_fderiv_apply_subset ℝ (basisVec i)) hxt))]
      simp)
  have hprodGlobal : Integrable (fun x => H x * ψ x) volume := by
    have hmulLoc := hHloc.mul_continuousOn hψ.continuous.continuousOn
      hB.isLocallyClosed
    have hmulK := hmulLoc.integrableOn_compact_subset hψB hψc.isCompact
    exact hmulK.integrable_of_forall_notMem_eq_zero (by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := ψ)
        (fun hxt => hx hxt)]
      simp)
  have hfull := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) hrightGlobal hleftGlobal hprodGlobal
    hfdiff hψdiff
  have hleftFull : ∫ x, H x * (fderiv ℝ ψ x) (basisVec i) =
      ∫ x in B, H x * (fderiv ℝ ψ x) (basisVec i) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := fun y =>
      (fderiv ℝ ψ y) (basisVec i))
      (fun hxt => hx (hψB ((tsupport_fderiv_apply_subset ℝ (basisVec i)) hxt)))]
    simp
  have hrightFull : ∫ x, (fderiv ℝ H x) (basisVec i) * ψ x =
      ∫ x in B, (fderiv ℝ H x) (basisVec i) * ψ x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := ψ)
      (fun hxt => hx (hψB hxt))]
    simp
  rw [← hleftFull, ← hrightFull]
  exact hfull

end CKN.Core.Step4
