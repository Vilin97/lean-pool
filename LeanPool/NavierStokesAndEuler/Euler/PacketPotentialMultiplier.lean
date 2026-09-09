/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCrossProduct
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Smoothness and actual time differentiation of the normalized cross multiplier. -/

noncomputable section

namespace EulerPacketCrossProduct

open EulerSmoothLimit InnerProductSpace Matrix WithLp
open scoped ContDiff

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : AddCommGroup (Space →L[ℝ] Space) :=
  (inferInstance : NormedAddCommGroup (Space →L[ℝ] Space)).toAddCommGroup
private local instance : Module ℝ (Space →L[ℝ] Space) :=
  (inferInstance : NormedSpace ℝ (Space →L[ℝ] Space)).toModule
private local instance : TopologicalSpace (Space →L[ℝ] Space) :=
  (inferInstance : PseudoMetricSpace (Space →L[ℝ] Space)).toUniformSpace.toTopologicalSpace

def crossOperatorLinear : Space →ₗ[ℝ] (Space →L[ℝ] Space) where
  toFun := crossLeft
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro v
    simp [crossLeft_apply, cross, map_add]
  map_smul' r a := by
    apply ContinuousLinearMap.ext
    intro v
    simp [crossLeft_apply, cross, map_smul]

def crossOperator : Space →L[ℝ] (Space →L[ℝ] Space) :=
  crossOperatorLinear.mkContinuous 1 (fun a => by
    change ‖crossLeft a‖ ≤ 1*‖a‖
    simpa only [one_mul] using crossLeft_norm_le a)

@[simp] theorem crossOperator_apply (a : Space) : crossOperator a = crossLeft a := rfl

theorem potentialMultiplier_eq_inner (m : Space) :
    potentialMultiplier m = -((⟪m,m⟫_ℝ)⁻¹) • crossOperator m := by
  rw [real_inner_self_eq_norm_sq]
  rfl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem potentialMultiplier_contDiff (m : X → Space) (hm : ContDiff ℝ ∞ m)
    (hnz : ∀ x, m x ≠ 0) : ContDiff ℝ ∞ (fun x => potentialMultiplier (m x)) := by
  simp_rw [potentialMultiplier_eq_inner]
  exact ((hm.inner ℝ hm).inv (fun x => by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hnz x)))).neg.smul
    (crossOperator.contDiff.comp hm)

def potentialMultiplierDerivative (m mt : Space) : Space →L[ℝ] Space :=
  (2*⟪m,mt⟫_ℝ/(‖m‖^2)^2) • crossLeft m - ((‖m‖^2)⁻¹) • crossLeft mt

/-- The derivative formula is valid for a time curve on its actual time set. -/
theorem potentialMultiplier_hasDerivWithinAt (s : Set ℝ) (t : ℝ)
    (m : ℝ → Space) (mt : Space) (hm : HasDerivWithinAt m mt s t) (hnz : m t ≠ 0) :
    HasDerivWithinAt (fun r => potentialMultiplier (m r))
      (potentialMultiplierDerivative (m t) mt) s t := by
  have hnorm : HasDerivWithinAt (fun r => ‖m r‖^2) (2*⟪m t,mt⟫_ℝ) s t := by
    simpa only [real_inner_self_eq_norm_sq, real_inner_comm mt (m t), ← two_mul] using hm.inner ℝ hm
  have hInv := hnorm.inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hnz))
  have hcross : HasDerivWithinAt (fun r => crossLeft (m r)) (crossLeft mt) s t :=
    crossOperator.hasFDerivAt.comp_hasDerivWithinAt t hm
  have h := hInv.neg.smul hcross
  simpa only [potentialMultiplier, potentialMultiplierDerivative, Pi.neg_apply,
    Pi.inv_apply, Pi.smul_def', Pi.neg_def, neg_div, neg_neg, sub_eq_add_neg, neg_smul, add_comm]
      using h

end EulerPacketCrossProduct
