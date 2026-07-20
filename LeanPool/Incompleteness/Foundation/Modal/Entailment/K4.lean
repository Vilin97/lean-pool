/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Entailment.K

/-! # K4 -/


namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.K4 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxBoxdotBox : 𝓢 ⊢  □⊡φ ==> □φ := impTrans'' distributeBoxAnd and₁
omit [DecidableEq F] in
@[simp] lemma imply_boxboxdot_box : 𝓢 ⊢! □⊡φ ==> □φ := by
  classical
  exact ⟨implyBoxBoxdotBox⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxBoxBoxdot : 𝓢 ⊢ □φ ==> □⊡φ :=
  impTrans'' (implyRightAnd (impId _) axiomFour) collectBoxAnd
omit [DecidableEq F] in
@[simp] lemma «imply_box_boxboxdot!» : 𝓢 ⊢! □φ ==> □⊡φ := by
  classical
  exact ⟨implyBoxBoxBoxdot⟩

/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxBoxBoxdot' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ □⊡φ := implyBoxBoxBoxdot ⨀ h
omit [DecidableEq F] in
/-- Imported declaration from the Incompleteness formalization. -/
lemma «implyBoxBoxBoxdot'!» (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! □⊡φ := by
  classical
  exact ⟨implyBoxBoxBoxdot' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def iffBoxBoxBoxdot : 𝓢 ⊢ □φ <=> □⊡φ := iffIntro implyBoxBoxBoxdot implyBoxBoxdotBox
omit [DecidableEq F] in
@[simp] lemma «iff_box_boxboxdot!» : 𝓢 ⊢! □φ <=> □⊡φ := by
  classical
  exact ⟨iffBoxBoxBoxdot⟩

/-- Imported declaration from the Incompleteness formalization. -/
def iffBoxBoxdotBox : 𝓢 ⊢ □φ <=> ⊡□φ :=
  iffIntro (impTrans'' (implyRightAnd (impId _) axiomFour) (impId _)) and₁
omit [DecidableEq F] in
@[simp] lemma «iff_box_boxdotbox!» : 𝓢 ⊢! □φ <=> ⊡□φ := by
  classical
  exact ⟨iffBoxBoxdotBox⟩

/-- Imported declaration from the Incompleteness formalization. -/
def iffBoxdotBoxdotBoxdot : 𝓢 ⊢ ⊡φ <=> ⊡⊡φ :=
  iffIntro (implyRightAnd (impId _) (impTrans'' boxdotBox (and₁' iffBoxBoxBoxdot))) and₁
omit [DecidableEq F] in
@[simp] lemma iff_boxdot_boxdotboxdot : 𝓢 ⊢! ⊡φ <=> ⊡⊡φ := by
  classical
  exact ⟨iffBoxdotBoxdotBoxdot⟩

/-- Imported declaration from the Incompleteness formalization. -/
def boxdotAxiomFour : 𝓢 ⊢ ⊡φ ==> ⊡⊡φ := and₁' iffBoxdotBoxdotBoxdot
omit [DecidableEq F] in
@[simp] lemma «boxdot_axiomFour!» : 𝓢 ⊢! ⊡φ ==> ⊡⊡φ := by
  classical
  exact ⟨boxdotAxiomFour⟩

end Entailment
end LO
