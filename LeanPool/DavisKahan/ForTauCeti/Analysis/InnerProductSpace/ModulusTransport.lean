/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-!
# Naturality of the operator modulus

The bounded source modulus is defined in `OperatorModulus.lean` from the real self-adjoint
continuous functional calculus.  This module records its naturality under the two scalar
transports used elsewhere in the Hilbert-space development:

* real complexification;
* transport along an isomorphism between `RCLike` fields.

These theorems live downstream of both the functional-calculus construction and the modulus.
Keeping them here prevents the foundational functional-calculus modules from depending back on
`OperatorModulus.lean`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Canonical conjugation commutes with the operator modulus. -/
theorem conjugateOperator_modulus
    (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator A.modulus = (conjugateOperator A).modulus := by
  refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
    (conjugateOperator_nonneg A.modulus_nonneg) ?_
  rw [← conjugateOperator_mul, A.modulus_mul_self]
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
    conjugateOperator_mul, conjugateOperator_adjoint]

/-- The modulus of a conjugation-fixed operator is conjugation-fixed. -/
theorem conjugateOperator_modulus_of_fixed
    {A : RealComplexification E →L[ℂ] RealComplexification E}
    (hfix : conjugateOperator A = A) :
    conjugateOperator A.modulus = A.modulus := by
  rw [conjugateOperator_modulus, hfix]

/-- Complexification commutes with the operator modulus. -/
@[simp] theorem complexify_modulus (T : E →L[ℝ] E) :
    complexify T.modulus = (complexify T).modulus := by
  refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq ?_ ?_
  · exact complexify_nonneg_iff.2 T.modulus_nonneg
  · have hmul : complexify T.modulus * complexify T.modulus =
        complexify (T.modulus * T.modulus) := (complexify_comp _ _).symm
    rw [hmul, ContinuousLinearMap.modulus_mul_self, complexify_comp, complexify_adjoint]

end RealComplexification

namespace ScalarTransport

universe u w v

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Transport along an `RCLike` isomorphism commutes with the operator modulus. -/
@[simp] theorem clm_modulus (T : E →L[𝕜] E) :
    clm (e := e) T.modulus = (clm (e := e) T).modulus := by
  refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq ?_ ?_
  · exact nonneg_clm_iff.2 T.modulus_nonneg
  · rw [← clm_mul, ContinuousLinearMap.modulus_mul_self]
    change clm (e := e) (ContinuousLinearMap.adjoint T ∘L T) =
      ContinuousLinearMap.adjoint (clm (e := e) T) ∘L clm (e := e) T
    rw [adjoint_clm]
    rfl

end ScalarTransport
end TauCeti
