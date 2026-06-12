/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Entailment.K4

/-! # GL -/


namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.GL 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def goedel2 : 𝓢 ⊢ (∼(□⊥) <=> ∼(□(∼(□⊥))) : F) := by
  apply negReplaceIff';
  apply iffIntro;
  · apply implyBoxDistribute';
    exact efq;
  · exact impTrans'' (by
      apply implyBoxDistribute';
      exact and₁' negEquiv;
    ) axiomL;
omit [DecidableEq F] in
lemma «goedel2!» : 𝓢 ⊢! (∼(□⊥) <=> ∼(□(∼(□⊥))) : F) := by
  classical
  exact ⟨goedel2⟩

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.goedel2'.mp : 𝓢 ⊢ (∼(□⊥) : F) → 𝓢 ⊢ ∼(□(∼(□⊥)) :
    F) := by
  intro h; exact (and₁' goedel2) ⨀ h;
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Entailment.goedel2'.mpr : 𝓢 ⊢ ∼(□(∼(□⊥)) : F) → 𝓢 ⊢ (∼(□⊥) :
    F) := by
  intro h; exact (and₂' goedel2) ⨀ h;
omit [DecidableEq F] in
lemma «goedel2'!» : 𝓢 ⊢! (∼(□⊥) : F) ↔ 𝓢 ⊢! ∼(□(∼(□⊥)) :
    F) := by
  classical
  exact ⟨fun ⟨h⟩ ↦ ⟨goedel2'.mp h⟩, fun ⟨h⟩ ↦ ⟨goedel2'.mpr h⟩⟩


namespace GL

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomFour : 𝓢 ⊢ Axioms.Four φ := by
  dsimp [Axioms.Four];
  have : 𝓢 ⊢ φ ==> (⊡□φ ==> ⊡φ) := by
    apply deduct';
    apply deduct;
    exact and₃' (FiniteContext.byAxm) (and₁' (ψ := □□φ) <| FiniteContext.byAxm);
  have : 𝓢 ⊢ φ ==> (□⊡φ ==> ⊡φ) := impTrans'' this (implyLeftReplace BoxBoxdotBoxDotbox);
  exact impTrans'' (impTrans'' (implyBoxDistribute' this) axiomL) (implyBoxDistribute' <| and₂);
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ GL.axiomFour⟩
instance : Entailment.K4 𝓢 where

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomH : 𝓢 ⊢ Axioms.H φ := impTrans'' (implyBoxDistribute' and₁) axiomL
instance : HasAxiomH 𝓢 := ⟨fun _ ↦ GL.axiomH⟩

end GL

private noncomputable def lem_boxdot_Grz_of_L :
    𝓢 ⊢ (⊡(⊡(φ ==> ⊡φ) ==> φ)) ==> (□(φ ==> ⊡φ) ==> φ) := by
  have : 𝓢 ⊢ (□(φ ==> ⊡φ) ⋏ ∼φ) ==> ⊡(φ ==> ⊡φ) := by
    apply deduct';
    apply and₃';
    · exact (of efqImplyNot₁) ⨀ and₂;
    · exact (of (impId _)) ⨀ and₁;
  have : 𝓢 ⊢ ∼⊡(φ ==> ⊡φ) ==> (∼□(φ ==> ⊡φ) ⋎ φ) :=
    impTrans'' (contra₀' this) <| impTrans'' demorgan₄ (orReplaceRight dne);
  have : 𝓢 ⊢ (∼⊡(φ ==> ⊡φ) ⋎ φ) ==> (∼□(φ ==> ⊡φ) ⋎ φ) := or₃'' this or₂;
  have : 𝓢 ⊢ ∼⊡(φ ==> ⊡φ) ⋎ φ ==> □(φ ==> ⊡φ) ==> φ := impTrans'' this implyOfNotOr;
  have : 𝓢 ⊢ (⊡(φ ==> ⊡φ) ==> φ) ==> (□(φ ==> ⊡φ) ==> φ) := impTrans'' NotOrOfImply this;
  exact impTrans'' boxdotAxiomT this;

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def boxdotGrzOfL : 𝓢 ⊢ ⊡(⊡(φ ==> ⊡φ) ==> φ) ==> φ := by
  have : 𝓢 ⊢ □(⊡(φ ==> ⊡φ) ==> φ) ==> □⊡(φ ==> ⊡φ) ==> □φ := axiomK;
  have : 𝓢 ⊢ □(⊡(φ ==> ⊡φ) ==> φ) ==> □(φ ==> ⊡φ) ==> □φ :=
    impTrans'' this <| implyLeftReplace <| implyBoxBoxBoxdot;
  have : 𝓢 ⊢ □(⊡(φ ==> ⊡φ) ==> φ) ==> □(φ ==> ⊡φ) ==> (φ ==> ⊡φ) := by
    apply deduct'; apply deduct; apply deduct;
    exact and₃' FiniteContext.byAxm <| (of this) ⨀ (FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
  have : 𝓢 ⊢ □□(⊡(φ ==> ⊡φ) ==> φ) ==> □(□(φ ==> ⊡φ) ==> (φ ==> ⊡φ)) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □(⊡(φ ==> ⊡φ) ==> φ) ==> □(□(φ ==> ⊡φ) ==> (φ ==> ⊡φ)) := impTrans'' axiomFour this;
  have : 𝓢 ⊢ □(⊡(φ ==> ⊡φ) ==> φ) ==> □(φ ==> ⊡φ) := impTrans'' this axiomL;
  have : 𝓢 ⊢ ⊡(⊡(φ ==> ⊡φ) ==> φ) ==> □(φ ==> ⊡φ) := impTrans'' boxdotBox this;
  exact mdp₁ lem_boxdot_Grz_of_L this;
omit [DecidableEq F] in
@[simp] lemma «boxdotGrzOfL!» : 𝓢 ⊢! ⊡(⊡(φ ==> ⊡φ) ==> φ) ==> φ := by
  classical
  exact ⟨boxdotGrzOfL⟩


/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxdotBoxdotOfImplyBoxdotPlain (h : 𝓢 ⊢ ⊡φ ==> ψ) : 𝓢 ⊢ ⊡φ ==> ⊡ψ := by
  have : 𝓢 ⊢ □⊡φ ==> □ψ := implyBoxDistribute' h;
  have : 𝓢 ⊢ □φ ==> □ψ := impTrans'' implyBoxBoxBoxdot this;
  have : 𝓢 ⊢ ⊡φ ==> □ψ := impTrans'' boxdotBox this;
  exact implyRightAnd h this;
omit [DecidableEq F] in
lemma «implyBoxdotBoxdotOfImplyBoxdotPlain!» (h : 𝓢 ⊢! ⊡φ ==> ψ) :
    𝓢 ⊢! ⊡φ ==> ⊡ψ := by
  classical
  exact ⟨implyBoxdotBoxdotOfImplyBoxdotPlain h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxdotAxiomTOfImplyBoxdotBoxdot (h : 𝓢 ⊢ ⊡φ ==> ⊡ψ) : 𝓢 ⊢ ⊡φ ==> (□ψ ==> ψ) := by
  apply deduct';
  apply deduct;
  have : [□ψ, ⊡φ] ⊢[𝓢] ⊡ψ := (FiniteContext.of h) ⨀ (FiniteContext.byAxm);
  exact and₁' this;
omit [DecidableEq F] in
lemma «implyBoxdotAxiomTOfImplyBoxdotBoxdot!» (h : 𝓢 ⊢! ⊡φ ==> ⊡ψ) :
    𝓢 ⊢! ⊡φ ==> (□ψ ==> ψ) := by
  classical
  exact ⟨implyBoxdotAxiomTOfImplyBoxdotBoxdot h.some⟩


/-- Imported declaration from the Incompleteness formalization. -/
def implyBoxBoxOfImplyBoxdotAxiomT (h : 𝓢 ⊢ ⊡φ ==> (□ψ ==> ψ)) : 𝓢 ⊢ □φ ==> □ψ := by
  have : 𝓢 ⊢ □⊡φ ==> □(□ψ ==> ψ) := implyBoxDistribute' h;
  have : 𝓢 ⊢ □⊡φ ==> □ψ := impTrans'' this axiomL;
  exact impTrans'' implyBoxBoxBoxdot this;
omit [DecidableEq F] in
lemma «implyBoxBoxOfImplyBoxdotAxiomT!» (h : 𝓢 ⊢! ⊡φ ==> (□ψ ==> ψ)) :
    𝓢 ⊢! □φ ==> □ψ := by
  classical
  exact ⟨implyBoxBoxOfImplyBoxdotAxiomT h.some⟩


omit [DecidableEq F] in
lemma «imply_box_box_of_imply_boxdot_plain!» (h : 𝓢 ⊢! ⊡φ ==> ψ) : 𝓢 ⊢! □φ ==> □ψ := by
  classical
  exact implyBoxBoxOfImplyBoxdotAxiomT! <| implyBoxdotAxiomTOfImplyBoxdotBoxdot! <|
      implyBoxdotBoxdotOfImplyBoxdotPlain! h

end Entailment
end LO
