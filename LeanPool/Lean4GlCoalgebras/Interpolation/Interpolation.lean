/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/

import LeanPool.Lean4GlCoalgebras.Interpolation.PartialInterpolation

/-! ## Interpolation

We use everything we have proven so far to show that GL has interpolation!
-/

namespace Lean4GlCoalgebras

/-- Definition of Craig interpolation. -/
def isInterpolant (φ : Formula) (ψ : Formula) (χ : Formula) :=
  χ.vocab ⊆ φ.vocab ∩ ψ.vocab ∧ ⊨ (φ ↣ χ) ∧ ⊨ (χ ↣ ψ)

/-- Sorry-free interpolation theorem! -/
theorem interpolation (φ ψ : Formula) : ⊨ (φ ↣ ψ) → ∃ χ, isInterpolant φ ψ χ := by
  intro φ_ψ
  have φ_ψ_sseq : ⊨ {Sum.inl (~φ), Sum.inr ψ} := by
    intro α M u
    have h := φ_ψ α M u
    change evaluate (M, u) (~φ) ∨ evaluate (M, u) ψ at h
    rcases h with h | h
    · exact ⟨Sum.inl (~φ), by simp, h⟩
    · exact ⟨Sum.inr ψ, by simp, h⟩
  have ⟨𝕏, 𝕏_proves⟩ := Split.completeness _ φ_ψ_sseq
  have ⟨𝕐, fin_Y, y, y_prop⟩ := Split.finite_proof_of_proof 𝕏 _ 𝕏_proves
  have Fintype_Y := @Fintype.ofFinite _ fin_Y
  refine ⟨interpolant 𝕐 (at (encodeVar y)), ?_, ?_, ?_⟩
  · have := (@interpolant_prop 𝕐 Fintype_Y y).2
    convert this
    · ext n
      simp [y_prop, SplitSequent.left, Sequent.vocab]
    · ext n
      simp [y_prop, SplitSequent.right, Sequent.vocab]
  · have hl := interpolantProofLeft_proves_interpolant y
    have φ_χ := ExtSkip.soundness _ ⟨_, hl⟩
    have φ_χ := by
      simpa [SplitSequent.isValid, evaluateSSeq, leftInterpolantSequent, y_prop] using φ_χ
    simp only [Formula.isValid, evaluate]
    grind
  · have hr := interpolantProofRight_proves_interpolant y
    have φ_χ := ExtSkip.soundness _ ⟨_, hr⟩
    have φ_χ := by
      simpa [SplitSequent.isValid, evaluateSSeq, rightInterpolantSequent, y_prop] using φ_χ
    simp only [Formula.isValid, evaluate]
    grind
end Lean4GlCoalgebras
