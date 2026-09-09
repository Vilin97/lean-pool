/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse

/-! The vector-potential multiplier is a fixed linear contraction of the normal functional. -/

@[expose] public section


noncomputable section

namespace EulerPacketCrossProduct

open EulerSmoothLimit EulerTransverseGramInverse InnerProductSpace

/-- Normal vector, given by `(ContinuousLinearMap.apply ℝ Space (1 : ℝ)).comp (realAdjoint (U :=
Space) (E := ℝ))`. -/
def normalVector : (Space →L[ℝ] ℝ) →L[ℝ] Space :=
  (ContinuousLinearMap.apply ℝ Space (1 : ℝ)).comp (realAdjoint (U := Space) (E := ℝ))

@[simp] theorem normalVector_apply (N : Space →L[ℝ] ℝ) : normalVector N = N.adjoint 1 := rfl

/-- Normal potential map, given by `-(crossOperator.comp normalVector)`. -/
def normalPotentialMap : (Space →L[ℝ] ℝ) →L[ℝ] (Space →L[ℝ] Space) :=
  -(crossOperator.comp normalVector)

@[simp] theorem normalPotentialMap_apply (N : Space →L[ℝ] ℝ) :
    normalPotentialMap N = -crossLeft (N.adjoint 1) := rfl

theorem normalPotentialMap_norm : ‖normalPotentialMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro N
  simp only [normalPotentialMap_apply, norm_neg, one_mul]
  apply (crossLeft_norm_le (N.adjoint 1)).trans
  simpa only [norm_one, mul_one, LinearIsometryEquiv.norm_map] using N.adjoint.le_opNorm 1

theorem normalVector_eq (m : Space) (N : Space →L[ℝ] ℝ)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / (‖m‖ ^ 2)) : N.adjoint 1 = ((‖m‖^2)⁻¹) • m := by
  apply ext_inner_right ℝ
  intro v
  rw [N.adjoint_inner_left, real_inner_smul_left]
  rw [Real.inner_apply, one_mul, hN, div_eq_mul_inv, mul_comm]

/-- No additional inverse or derivative estimate is needed after constructing the normal functional.
-/
theorem normalPotentialMap_eq (m : Space) (N : Space →L[ℝ] ℝ)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / (‖m‖ ^ 2)) : normalPotentialMap N = potentialMultiplier m := by
  change -(crossOperator (N.adjoint 1)) = potentialMultiplier m
  rw [normalVector_eq m N hN, map_smul, crossOperator_apply]
  apply ContinuousLinearMap.ext
  intro v
  change -(((‖m‖^2)⁻¹) • crossLeft m v) = (-((‖m‖^2)⁻¹)) • crossLeft m v
  exact (neg_smul _ _).symm

end EulerPacketCrossProduct
