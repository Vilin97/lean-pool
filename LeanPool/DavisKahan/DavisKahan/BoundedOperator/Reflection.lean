/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem

/-! # Reflection defects for bounded operators -/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Mirror defect used in the reflection proof of `sin 2Θ`. -/
noncomputable def reflectionDefect (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  U.reflectionOperator ∘L A ∘L U.reflectionOperator - A

omit [CompleteSpace E] in
/-- The reflection defect anti-commutes with the reflection that defines it:
`J (J A J - A) = -(J A J - A) J`. -/
theorem reflectionOperator_comp_reflectionDefect
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    U.reflectionOperator ∘L reflectionDefect U A =
      -(reflectionDefect U A ∘L U.reflectionOperator) := by
  ext x
  have hinvol (y : E) :
      U.reflectionOperator (U.reflectionOperator y) = y := by
    have h := congrArg (fun T : E →L[𝕜] E => T y)
      (Submodule.reflectionOperator_involutive U)
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  simp only [reflectionDefect, ContinuousLinearMap.comp_apply, sub_apply,
    neg_apply, map_sub]
  rw [hinvol (A (U.reflectionOperator x)), hinvol x]
  rw [neg_sub]

omit [CompleteSpace E] in
/-- The mirror defect vanishes when the subspace reduces the operator.
-/
theorem reflectionDefect_eq_zero_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) :
    reflectionDefect U A = 0 := by
  ext x
  have hcomm := congrArg (fun T : E →L[𝕜] E => T (U.reflectionOperator x))
    (Submodule.reflectionOperator_comm_of_reduces A U hU)
  have hinvol := congrArg (fun T : E →L[𝕜] E => T x)
    (Submodule.reflectionOperator_involutive U)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hcomm hinvol
  simp only [reflectionDefect, ContinuousLinearMap.comp_apply, sub_apply,
    zero_apply]
  rw [hcomm, hinvol, sub_self]

omit [CompleteSpace E] in
/-- Conjugating and subtracting a reducing comparison operator leaves only
its perturbation.
-/
theorem reflectionDefect_eq_perturbationDefect
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : B.Reduces V) :
    reflectionDefect V A =
      V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator - (A - B) := by
  have hB : reflectionDefect V B = 0 :=
    reflectionDefect_eq_zero_of_reduces B V hV
  unfold reflectionDefect at hB ⊢
  calc
    V.reflectionOperator ∘L A ∘L V.reflectionOperator - A =
        (V.reflectionOperator ∘L A ∘L V.reflectionOperator - A) -
          (V.reflectionOperator ∘L B ∘L V.reflectionOperator - B) := by
      rw [hB, sub_zero]
    _ = V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator - (A - B) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
      abel

omit [CompleteSpace E] in
/-- The reflection defect is bounded by twice the perturbation norm.
-/
theorem norm_reflectionDefect_le_two_mul
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : B.Reduces V) :
    ‖reflectionDefect V A‖ ≤ 2 * ‖A - B‖ := by
  rw [reflectionDefect_eq_perturbationDefect A B V hV]
  have hconj :
      ‖V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator‖ ≤
        ‖A - B‖ := by
    calc
      ‖V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator‖ ≤
          ‖V.reflectionOperator‖ * ‖(A - B) ∘L V.reflectionOperator‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖V.reflectionOperator‖ * (‖A - B‖ * ‖V.reflectionOperator‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg (V.reflectionOperator))
      _ ≤ 1 * (‖A - B‖ * ‖V.reflectionOperator‖) :=
        mul_le_mul_of_nonneg_right (Submodule.norm_reflectionOperator_le_one V) (by positivity)
      _ ≤ 1 * (‖A - B‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Submodule.norm_reflectionOperator_le_one V)
            (norm_nonneg (A - B)))
          zero_le_one
      _ = ‖A - B‖ := by ring
  calc
    ‖V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator - (A - B)‖ ≤
        ‖V.reflectionOperator ∘L (A - B) ∘L V.reflectionOperator‖ +
          ‖A - B‖ := norm_sub_le _ _
    _ ≤ ‖A - B‖ + ‖A - B‖ := add_le_add hconj le_rfl
    _ = 2 * ‖A - B‖ := by ring


end DavisKahan
end TauCeti
