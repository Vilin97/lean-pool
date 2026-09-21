/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.AngleFunctionalCalculus
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.Reflection
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.Gram

/-!
# The literal ambient `sin 2Θ` of Davis--Kahan, and the reflection identity

`DavisKahan/Geometry/Angle/AngleFunctionalCalculus.lean` builds the paper's literal
Hermitian angle `Θ = arcsin |P_U - P_V|` between two closed subspaces.  This
module applies `t ↦ sin 2t` to it and identifies the result *as an operator*
with the displacement of `P_U` under the reflection through `V`:

`sin 2Θ = |J_V P_U J_V - P_U| = |P_{J_V U} - P_U|`.

Both sides were already known to have the same operator norm
(`subspaceGap_map_reflection_eq_norm_sinTwoAngle`).  Equality of the operators
themselves is strictly stronger and is what a unitarily invariant norm needs:
every such norm is a function of the singular values, so the reflected pair
`(U, J_V U)` computes `sin 2Θ` in *every* source norm, not only in the operator
norm.

This is the operator content of Davis--Kahan Section 7: reflecting a subspace
through another doubles the principal angles, so the `sin 2Θ` theorem is an
ordinary `sin Θ` theorem applied to the reflected pair.

## Main results

* `TauCeti.DavisKahan.Angle.sinTwoAngleOperatorC`: the literal `sin 2Θ`.
* `TauCeti.DavisKahan.Angle.sinTwoAngleOperatorC_nonneg`.
* `TauCeti.DavisKahan.Angle.starProjection_map_reflection_eq`: the reflected
  subspace has projection `J_V P_U J_V`.
* `TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC_eq_modulus_reflect`:
  `sin 2Θ = |J_V P_U J_V - P_U|`.
* `TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub`:
  `sin 2Θ = |P_{J_V U} - P_U|`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Section 7, equations (7.1)--(7.5).
-/

namespace TauCeti
namespace DavisKahan.Angle

open DavisKahan

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The paper's literal ambient `sin 2Θ`, obtained by applying `t ↦ sin 2t` to
the Hermitian operator angle. -/
noncomputable def sinTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[ℂ] E :=
  cfc (fun t : ℝ => Real.sin (2 * t)) (angleOperatorC U V)

/-- `sin 2Θ` is self-adjoint. -/
theorem isSelfAdjoint_sinTwoAngleOperatorC (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    IsSelfAdjoint (sinTwoAngleOperatorC U V) :=
  cfc_predicate _ (angleOperatorC U V)

/-- `sin 2Θ` is nonnegative: the angle has spectrum in `[0, π/2]`, so the doubled
angle has spectrum in `[0, π]`. -/
theorem sinTwoAngleOperatorC_nonneg (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ sinTwoAngleOperatorC U V := by
  refine cfc_nonneg fun t ht => ?_
  have h := spectrum_angleOperatorC_subset_Icc U V ht
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [h.1])
    (by linarith [h.2, Real.pi_pos])

omit [CompleteSpace E] in
/-- The reflection through `V` written as a ring element of the endomorphism
algebra. -/
theorem reflectionOperator_eq_add_sub_one (V : Submodule ℂ E)
    [V.HasOrthogonalProjection] :
    V.reflectionOperator =
      V.starProjection + V.starProjection - 1 := by
  rw [Submodule.reflectionOperator_eq_two_smul_sub_id, two_smul]
  rfl

omit [CompleteSpace E] in
/-- The projection onto the reflected subspace `J_V U` is the conjugate
`J_V P_U J_V`. -/
theorem starProjection_map_reflection_eq (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection =
      V.reflectionOperator * U.starProjection * V.reflectionOperator := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [Submodule.starProjection_map_apply, Submodule.reflection_symm]
  rfl

section Identity

variable (U V : Submodule ℂ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The reflection double-angle identity.**  `sin 2Θ` is exactly the modulus of
the displacement of `P_U` under the reflection through `V`.

The proof is by uniqueness of the positive square root: both sides are
nonnegative, and both have Gram operator `4 (sin²Θ - sin⁴Θ)` — the left by the
scalar identity `sin (2 arcsin s)² = 4 s² (1 - s²)`, the right by the algebraic
commutator identity for a pair of orthogonal projections. -/
theorem directedSinTwoAngleOperatorC_eq_modulus_reflect :
    sinTwoAngleOperatorC U V =
      (V.reflectionOperator * U.starProjection * V.reflectionOperator -
        U.starProjection).modulus := by
  set P : E →L[ℂ] E := U.starProjection with hP
  set Q : E →L[ℂ] E := V.starProjection with hQ
  set S : E →L[ℂ] E := sinAngleOperatorC U V with hS
  have hSsa : IsSelfAdjoint S := isSelfAdjoint_sinAngleOperatorC U V
  have hDsa : IsSelfAdjoint (P - Q) :=
    (isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)
  -- `S² = D²` because `D` is self-adjoint and `S` is its modulus.
  have hSS : S * S = (P - Q) * (P - Q) := by
    rw [hS, sinAngleOperatorC, ContinuousLinearMap.modulus_mul_self,
      hDsa.adjoint_eq]
    rfl
  -- The right-hand Gram operator.
  have hgram :
      ((V.reflectionOperator * P * V.reflectionOperator - P).adjoint ∘L
          (V.reflectionOperator * P * V.reflectionOperator - P)) =
        (4 : ℂ) • (S * S - (S * S) * (S * S)) := by
    have h := TauCeti.gram_reflect_sub (P := P) (Q := Q)
      (Submodule.isIdempotentElem_starProjection U)
      (Submodule.isIdempotentElem_starProjection V)
      (isSelfAdjoint_starProjection U) (isSelfAdjoint_starProjection V)
    rw [reflectionOperator_eq_add_sub_one, hSS]
    exact h
  -- The left-hand square, through the scalar double-angle identity.
  have h4 : S ^ 4 = (S * S) * (S * S) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  have hW : cfc (fun s : ℝ => s ^ 2 - s ^ 4) S = S * S - (S * S) * (S * S) := by
    rw [cfc_sub (fun s : ℝ => s ^ 2) (fun s : ℝ => s ^ 4) S
        (by fun_prop) (by fun_prop),
      cfc_pow_id S 2, cfc_pow_id S 4, h4, pow_two]
  have hsquare :
      sinTwoAngleOperatorC U V * sinTwoAngleOperatorC U V =
        (4 : ℂ) • (S * S - (S * S) * (S * S)) := by
    have hcont : ContinuousOn (fun t : ℝ => Real.sin (2 * t))
        (spectrum ℝ (angleOperatorC U V)) := by fun_prop
    have harcsin : ContinuousOn Real.arcsin (spectrum ℝ S) :=
      Real.continuous_arcsin.continuousOn
    have hcomp : ContinuousOn
        (fun t : ℝ => Real.sin (2 * t) * Real.sin (2 * t))
        (Real.arcsin '' spectrum ℝ S) := by fun_prop
    rw [sinTwoAngleOperatorC,
      ← cfc_mul (fun t : ℝ => Real.sin (2 * t)) (fun t : ℝ => Real.sin (2 * t))
        (angleOperatorC U V) hcont hcont]
    rw [angleOperatorC, ← hS,
      ← cfc_comp (fun t : ℝ => Real.sin (2 * t) * Real.sin (2 * t))
        Real.arcsin S hSsa hcomp harcsin]
    have hcongr : cfc
        ((fun t : ℝ => Real.sin (2 * t) * Real.sin (2 * t)) ∘ Real.arcsin) S =
        cfc (fun s : ℝ =>
          (s ^ 2 - s ^ 4) + (s ^ 2 - s ^ 4) +
            ((s ^ 2 - s ^ 4) + (s ^ 2 - s ^ 4))) S := by
      refine cfc_congr fun s hs => ?_
      have hsi := spectrum_sinAngleOperatorC_subset_Icc U V hs
      have hsq := TauCeti.sin_two_mul_arcsin_sq (s := s)
        (by linarith [hsi.1]) hsi.2
      have : Real.sin (2 * Real.arcsin s) * Real.sin (2 * Real.arcsin s) =
          4 * s ^ 2 * (1 - s ^ 2) := by
        rw [← pow_two]; exact hsq
      simp only [Function.comp_apply]
      rw [this]
      ring
    rw [hcongr]
    have hc2 : ContinuousOn (fun s : ℝ => s ^ 2 - s ^ 4) (spectrum ℝ S) := by
      fun_prop
    rw [cfc_add (a := S) (fun s : ℝ => (s ^ 2 - s ^ 4) + (s ^ 2 - s ^ 4))
        (fun s : ℝ => (s ^ 2 - s ^ 4) + (s ^ 2 - s ^ 4))
        (by fun_prop) (by fun_prop),
      cfc_add (a := S) (fun s : ℝ => s ^ 2 - s ^ 4) (fun s : ℝ => s ^ 2 - s ^ 4)
        hc2 hc2, hW]
    module
  refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
    (sinTwoAngleOperatorC_nonneg U V) ?_
  rw [hsquare, hgram]

/-- **The reflection double-angle identity, in subspace form.**  `sin 2Θ` is the
modulus of the difference of the projections onto `U` and its reflection through
`V`. -/
theorem directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub :
    sinTwoAngleOperatorC U V =
      ((U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection -
        U.starProjection).modulus := by
  rw [directedSinTwoAngleOperatorC_eq_modulus_reflect,
    starProjection_map_reflection_eq]

end Identity

end

end DavisKahan.Angle
end TauCeti
