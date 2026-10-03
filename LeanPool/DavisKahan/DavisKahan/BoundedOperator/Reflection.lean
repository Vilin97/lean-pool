/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem

/-! # Reflection defects for bounded operators -/

@[expose] public section

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


omit [CompleteSpace E] in
/-- The reflection defect is `-2` times the sum of the two off-diagonal
blocks: `J A J - A = -2 (P_{Vᗮ} A P_V + P_V A P_{Vᗮ})`. -/
theorem reflectionDefect_eq_neg_two_smul_offdiag (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    reflectionDefect V A =
      (-2 : 𝕜) • (Vᗮ.starProjection ∘L A ∘L V.starProjection +
        V.starProjection ∘L A ∘L Vᗮ.starProjection) := by
  ext x
  change V.reflectionOperator (A (V.reflectionOperator x)) - A x =
    (-2 : 𝕜) • (Vᗮ.starProjection (A (V.starProjection x)) +
      V.starProjection (A (Vᗮ.starProjection x)))
  rw [Submodule.reflectionOperator_apply, Submodule.reflectionOperator_apply,
    Submodule.starProjection_orthogonal' V]
  simp only [map_sub, map_smul, sub_apply, one_apply_eq_self]
  module

/-- The two off-diagonal blocks are mutually adjoint for self-adjoint `A`. -/
theorem offdiag_adjoint (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) :
    (Vᗮ.starProjection ∘L A ∘L V.starProjection).adjoint =
      V.starProjection ∘L A ∘L Vᗮ.starProjection := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint,
    (isSelfAdjoint_starProjection V).star_eq,
    (isSelfAdjoint_starProjection Vᗮ).star_eq, hA.star_eq,
    ContinuousLinearMap.comp_assoc]

/-- **Sharp reflection-defect estimate through the off-diagonal block.**
For self-adjoint `A`, `‖J_V A J_V - A‖ ≤ 2 ‖P_{Vᗮ} A P_V‖` — no reduction
hypothesis on `V`.  This is the analytic input for the residual form of the
`sin 2Θ` theorem. -/
theorem norm_reflectionDefect_le_two_mul_norm_cross (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) :
    ‖reflectionDefect V A‖ ≤
      2 * ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ := by
  set T₁ : E →L[𝕜] E := Vᗮ.starProjection ∘L A ∘L V.starProjection
    with hT₁
  set T₂ : E →L[𝕜] E := V.starProjection ∘L A ∘L Vᗮ.starProjection
    with hT₂
  have hnormT₂ : ‖T₂‖ = ‖T₁‖ := by
    rw [hT₂, ← offdiag_adjoint V hA, ← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star T₁
  -- the sum of the off-diagonal blocks is bounded by the larger block
  have hsum : ‖T₁ + T₂‖ ≤ ‖T₁‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    have h1out : T₁ z ∈ Vᗮ := by
      rw [hT₁]
      exact Vᗮ.starProjection_apply_mem _
    have h2out : T₂ z ∈ V := by
      rw [hT₂]
      exact V.starProjection_apply_mem _
    have horth : ⟪T₂ z, T₁ z⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal V _).mp h1out _ h2out
    have hpyth : ‖(T₁ + T₂) z‖ ^ 2 = ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2 := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (T₂ z) (T₁ z) horth
      have hadd : (T₁ + T₂) z = T₂ z + T₁ z := by
        rw [add_apply]
        abel
      rw [hadd, sq, sq, sq]
      linarith
    have hin1 : ‖T₁ z‖ ≤ ‖T₁‖ * ‖V.starProjection z‖ := by
      have hfac : T₁ z = T₁ (V.starProjection z) := by
        rw [hT₁]
        change Vᗮ.starProjection (A (V.starProjection z)) =
          Vᗮ.starProjection (A (V.starProjection (V.starProjection z)))
        rw [show V.starProjection (V.starProjection z) =
          V.starProjection z from
            Submodule.starProjection_eq_self_iff.mpr
              (V.starProjection_apply_mem z)]
      rw [hfac]
      exact T₁.le_opNorm _
    have hin2 : ‖T₂ z‖ ≤ ‖T₁‖ * ‖Vᗮ.starProjection z‖ := by
      have hfac : T₂ z = T₂ (Vᗮ.starProjection z) := by
        rw [hT₂]
        change V.starProjection (A (Vᗮ.starProjection z)) =
          V.starProjection (A (Vᗮ.starProjection (Vᗮ.starProjection z)))
        rw [show Vᗮ.starProjection (Vᗮ.starProjection z) =
          Vᗮ.starProjection z from
            Submodule.starProjection_eq_self_iff.mpr
              (Vᗮ.starProjection_apply_mem z)]
      rw [hfac]
      calc ‖T₂ (Vᗮ.starProjection z)‖
          ≤ ‖T₂‖ * ‖Vᗮ.starProjection z‖ := T₂.le_opNorm _
        _ = ‖T₁‖ * ‖Vᗮ.starProjection z‖ := by rw [hnormT₂]
    have hzdecomp : ‖z‖ ^ 2 =
        ‖V.starProjection z‖ ^ 2 + ‖Vᗮ.starProjection z‖ ^ 2 := by
      have horth' : ⟪V.starProjection z, Vᗮ.starProjection z⟫_𝕜 = 0 :=
        (Submodule.mem_orthogonal V _).mp
          (Vᗮ.starProjection_apply_mem z) _ (V.starProjection_apply_mem z)
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (V.starProjection z) (Vᗮ.starProjection z) horth'
      rw [V.starProjection_add_starProjection_orthogonal z] at h
      rw [sq, sq, sq]
      linarith
    have hsq : ‖(T₁ + T₂) z‖ ^ 2 ≤ (‖T₁‖ * ‖z‖) ^ 2 := by
      rw [hpyth]
      have h1 := mul_self_le_mul_self (norm_nonneg (T₁ z)) hin1
      have h2 := mul_self_le_mul_self (norm_nonneg (T₂ z)) hin2
      have key : ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2 ≤
          ‖T₁‖ ^ 2 * (‖V.starProjection z‖ ^ 2 +
            ‖Vᗮ.starProjection z‖ ^ 2) := by
        nlinarith [h1, h2]
      calc ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2
          ≤ ‖T₁‖ ^ 2 * (‖V.starProjection z‖ ^ 2 +
              ‖Vᗮ.starProjection z‖ ^ 2) := key
        _ = (‖T₁‖ * ‖z‖) ^ 2 := by rw [← hzdecomp]; ring
    have hs := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg z))] at hs
  calc ‖reflectionDefect V A‖
      = ‖(-2 : 𝕜) • (T₁ + T₂)‖ := by
        rw [reflectionDefect_eq_neg_two_smul_offdiag]
    _ = 2 * ‖T₁ + T₂‖ := by
        rw [norm_smul]
        norm_num
    _ ≤ 2 * ‖T₁‖ := by linarith [hsum]


end DavisKahan
end TauCeti
