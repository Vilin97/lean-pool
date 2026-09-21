/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.PositiveShift
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.DenseCoreConvergence

/-!
# Contractive resolvent families

This module packages the elementary resolvent identity, the Hille--Yosida
bound, and dense range, then derives normalization at large positive shifts.
-/

open Filter Topology

namespace MarkovProcess.Semigroup

/-- A resolvent family on a real normed space with the contraction bound and
dense range needed for normalization at large positive shifts. -/
structure ContractiveResolvent (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The resolvent at a positive real shift. -/
  operator : PositiveShift → E →L[ℝ] E
  /-- The resolvent identity, with the sign convention for `(α + A)⁻¹`. -/
  resolvent_identity : ∀ α β,
    operator α - operator β =
      ((β : ℝ) - (α : ℝ)) • ((operator α).comp (operator β))
  /-- The Hille--Yosida contraction estimate. -/
  opNorm_le_inv : ∀ α, ‖operator α‖ ≤ (α : ℝ)⁻¹
  /-- Every resolvent has dense range. -/
  denseRange : ∀ α, DenseRange (operator α)

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized resolvent `α R_α`. -/
def scaledOperator (R : ContractiveResolvent E) (α : PositiveShift) : E →L[ℝ] E :=
  (α : ℝ) • R.operator α

/-- The normalized resolvent is a contraction in operator norm. -/
theorem opNorm_scaledOperator_le_one (R : ContractiveResolvent E) (α : PositiveShift) :
    ‖R.scaledOperator α‖ ≤ 1 := by
  have hα : 0 ≤ (α : ℝ) := α.property.le
  calc
    ‖R.scaledOperator α‖ ≤ ‖(α : ℝ)‖ * ‖R.operator α‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ = (α : ℝ) * ‖R.operator α‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hα]
    _ ≤ (α : ℝ) * (α : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (R.opNorm_le_inv α) hα
    _ = 1 := mul_inv_cancel₀ α.property.ne'

/-- Pointwise contraction of the normalized resolvent. -/
theorem norm_scaledOperator_apply_le (R : ContractiveResolvent E)
    (α : PositiveShift) (x : E) :
    ‖R.scaledOperator α x‖ ≤ ‖x‖ := by
  calc
    ‖R.scaledOperator α x‖ ≤ ‖R.scaledOperator α‖ * ‖x‖ :=
      R.scaledOperator α |>.le_opNorm x
    _ ≤ 1 * ‖x‖ :=
      mul_le_mul_of_nonneg_right (R.opNorm_scaledOperator_le_one α) (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- Resolvents at two positive shifts commute. -/
theorem operator_comm (R : ContractiveResolvent E) (α β : PositiveShift) :
    (R.operator α).comp (R.operator β) =
      (R.operator β).comp (R.operator α) := by
  by_cases hαβ : (α : ℝ) = (β : ℝ)
  · have : α = β := Subtype.ext hαβ
    subst β
    rfl
  · have hβα : (β : ℝ) - (α : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
    apply (smul_right_injective (E →L[ℝ] E) hβα)
    calc
      ((β : ℝ) - (α : ℝ)) • ((R.operator α).comp (R.operator β)) =
          R.operator α - R.operator β := (R.resolvent_identity α β).symm
      _ = ((β : ℝ) - (α : ℝ)) • ((R.operator β).comp (R.operator α)) := by
        calc
          R.operator α - R.operator β = -(R.operator β - R.operator α) := by abel
          _ = -((α : ℝ) - (β : ℝ)) •
                ((R.operator β).comp (R.operator α)) := by
            rw [R.resolvent_identity β α, neg_smul]
          _ = ((β : ℝ) - (α : ℝ)) •
                ((R.operator β).comp (R.operator α)) := by
            rw [neg_sub]

/-- The resolvent identity arranged as the core normalization formula. -/
theorem scaledOperator_apply_sub_on_range (R : ContractiveResolvent E)
    (α β : PositiveShift) (y : E) :
    R.scaledOperator α (R.operator β y) - R.operator β y =
      R.operator α ((β : ℝ) • R.operator β y - y) := by
  have h := DFunLike.congr_fun (R.resolvent_identity α β) y
  change
    R.operator α y - R.operator β y =
      ((β : ℝ) - (α : ℝ)) • R.operator α (R.operator β y) at h
  change
    (α : ℝ) • R.operator α (R.operator β y) - R.operator β y =
      R.operator α ((β : ℝ) • R.operator β y - y)
  rw [map_sub, map_smul]
  change
    (α : ℝ) • R.operator α (R.operator β y) - R.operator β y =
      (β : ℝ) • R.operator α (R.operator β y) - R.operator α y
  calc
    (α : ℝ) • R.operator α (R.operator β y) - R.operator β y =
        (α : ℝ) • R.operator α (R.operator β y) +
          (R.operator α y - R.operator β y) - R.operator α y := by abel
    _ = (α : ℝ) • R.operator α (R.operator β y) +
          ((β : ℝ) - (α : ℝ)) • R.operator α (R.operator β y) -
            R.operator α y := by rw [h]
    _ = (β : ℝ) • R.operator α (R.operator β y) - R.operator α y := by module

/-- Normalization converges on the range of any fixed resolvent. -/
theorem tendsto_scaledOperator_apply_on_range (R : ContractiveResolvent E)
    (μ : PositiveShift) (y : E) :
    Tendsto (fun α : PositiveShift ↦ R.scaledOperator α (R.operator μ y))
      atTop (nhds (R.operator μ y)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ α : PositiveShift,
      ‖R.scaledOperator α (R.operator μ y) - R.operator μ y‖ ≤
        ‖(μ : ℝ) • R.operator μ y - y‖ * (α : ℝ)⁻¹ := by
    intro α
    rw [R.scaledOperator_apply_sub_on_range α μ y]
    calc
      ‖R.operator α ((μ : ℝ) • R.operator μ y - y)‖ ≤
          ‖R.operator α‖ * ‖(μ : ℝ) • R.operator μ y - y‖ :=
        (R.operator α).le_opNorm _
      _ ≤ (α : ℝ)⁻¹ * ‖(μ : ℝ) • R.operator μ y - y‖ :=
        mul_le_mul_of_nonneg_right (R.opNorm_le_inv α) (norm_nonneg _)
      _ = ‖(μ : ℝ) • R.operator μ y - y‖ * (α : ℝ)⁻¹ := mul_comm _ _
  simpa only [dist_eq_norm] using
    squeeze_zero (fun α => norm_nonneg _) hbound
      (tendsto_const_mul_positiveShift_inv_atTop_zero
        ‖(μ : ℝ) • R.operator μ y - y‖)

/-- The normalized resolvents converge strongly to the identity. -/
theorem tendsto_scaledOperator_apply (R : ContractiveResolvent E) (x : E) :
    Tendsto (fun α : PositiveShift ↦ R.scaledOperator α x) atTop (nhds x) := by
  exact MarkovProcess.tendsto_of_denseRange_of_opNorm_le_one
    R.scaledOperator (R.operator ⟨1, by norm_num⟩)
    R.opNorm_scaledOperator_le_one (R.denseRange ⟨1, by norm_num⟩)
    (R.tendsto_scaledOperator_apply_on_range ⟨1, by norm_num⟩) x

end ContractiveResolvent

end MarkovProcess.Semigroup
