/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTimePathGluing
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear

@[expose] public section

/-! Matching time paths glue without any external-word or fixed-Sobolev loss. -/

noncomputable section

namespace EulerPacketTimePathGluing

open Set EulerTimeIntervalGlue EulerParameterWordGevrey
open scoped ContDiff

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] compactInterval

@[simp] theorem glueOperator_apply (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) :
    glueOperator S τ hτ0 hτS u = gluePath S τ hτ0 hτS u := rfl

theorem gluePath_left (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) (t : Icc (0 : ℝ) τ) :
    gluePath S τ hτ0 hτS u ⟨t, t.property.1, t.property.2.trans hτS⟩=u.val.1 t := by
  change glue τ (fun r => u.val.1 (projIcc 0 τ hτ0 r))
    (fun r => u.val.2 (projIcc τ S hτS r)) t = _
  rw [glue_left τ _ _ t t.property.2, projIcc_of_mem hτ0 t.property]

theorem gluePath_right (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (u : Matching (E := E) S τ hτ0 hτS) (t : Icc τ S) :
    gluePath S τ hτ0 hτS u ⟨t, hτ0.trans t.property.1, t.property.2⟩=u.val.2 t := by
  change glue τ (fun r => u.val.1 (projIcc 0 τ hτ0 r))
    (fun r => u.val.2 (projIcc τ S hτS r)) t = _
  rw [glue_right τ _ _ (by
    simpa only [projIcc_of_mem hτ0 ⟨hτ0,le_rfl⟩,
      projIcc_of_mem hτS ⟨le_rfl,hτS⟩] using matching_values S τ hτ0 hτS u)
    t t.property.1, projIcc_of_mem hτS t.property]

theorem glue_family_contDiff (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (f : X → Matching (E := E) S τ hτ0 hτS) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => gluePath S τ hτ0 hτS (f x)) := by
  simpa only [Function.comp_def, glueOperator_apply] using
    (glueOperator (E := E) S τ hτ0 hτS).contDiff.comp hf

theorem glue_word_derivative (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (directions : ι → X) (f : X → Matching (E := E) S τ hτ0 hτS)
    (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) (x : X) :
    wordDerivative directions (fun y => gluePath S τ hτ0 hτS (f y)) w x =
      gluePath S τ hτ0 hτS (wordDerivative directions f w x) := by
  simpa only [Function.comp_def, glueOperator_apply] using
    wordDerivative_comp_clm directions (glueOperator (E := E) S τ hτ0 hτS) f hf w x

variable [Fintype ι]

theorem glue_word_bound (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (directions : ι → X) (f : X → Matching (E := E) S τ hτ0 hτS)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    wordSum directions (fun y => gluePath S τ hτ0 hτS (f y)) n x ≤
      wordSum directions f n x := by
  have h := wordSum_comp_clm_le directions (glueOperator S τ hτ0 hτS) f hf n x
  exact h.trans ((mul_le_mul_of_nonneg_right
    (glueOperator_norm_le_one S τ hτ0 hτS) (wordSum_nonneg directions f n x)).trans_eq (one_mul _))

/-- Fixed H6 is the specialization q=6; no tensor-to-word conversion occurs. -/
theorem glue_block_bound (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
    (directions : ι → X) (q : ℕ) (f : X → Matching (E := E) S τ hτ0 hτS)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : X) :
    block directions q (fun y => gluePath S τ hτ0 hτS (f y)) n x ≤
      block directions q f n x := by
  have h := block_comp_clm_le directions q (glueOperator S τ hτ0 hτS) f hf n x
  exact h.trans ((mul_le_mul_of_nonneg_right
    (glueOperator_norm_le_one S τ hτ0 hτS) (block_nonneg directions q f n x)).trans_eq (one_mul _))

end EulerPacketTimePathGluing
