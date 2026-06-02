/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Hilbert.K
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.K

/-! # Basic -/



namespace LO
namespace Modal

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Logic := Set (Modal.Formula ℕ)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Hilbert.logic (H : Hilbert ℕ) : Logic := { φ | H ⊢! φ }

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev _root_.LO.Modal.Logic.K : Logic := Hilbert.K.logic


namespace Logic

/-- Imported declaration from the Incompleteness formalization. -/
protected class Unnecessitation (L : Logic) where
  unnec_closed {φ} : □φ ∈ L → φ ∈ L

/-- Imported declaration from the Incompleteness formalization. -/
protected class ModalDisjunctive (L : Logic) where
  modal_disjunctive_closed {φ ψ} : □φ ⋎ □ψ ∈ L → φ ∈ L ∨ ψ ∈ L

/-- Imported declaration from the Incompleteness formalization. -/
protected class QuasiNormal (L : Logic) where
  subset_K : Logic.K ⊆ L
  mdp_closed {φ ψ} : φ ==> ψ ∈ L → φ ∈ L → ψ ∈ L
  subst_closed {φ} : φ ∈ L → ∀ s, φ⟦s⟧ ∈ L

/-- Imported declaration from the Incompleteness formalization. -/
protected class Normal (L : Logic) extends L.QuasiNormal where
  nec_closed {φ} : φ ∈ L → □φ ∈ L

/-- Imported declaration from the Incompleteness formalization. -/
class Sublogic (L₁ L₂ : Logic) where
  subset : L₁ ⊆ L₂

/-- Imported declaration from the Incompleteness formalization. -/
class ProperSublogic (L₁ L₂ : Logic) : Prop where
  ssubset : L₁ ⊂ L₂

end Logic

namespace Hilbert

open Entailment

variable {H : Hilbert ℕ}

instance normal [H.HasK] : (H.logic).Normal where
  subset_K := by
    intro φ hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with ⟨s, rfl⟩; simp;
    | mdp ihφψ ihφ => exact mdp! ihφψ ihφ;
    | nec ih => exact nec! ih;
    | _ => simp;
  mdp_closed := by
    intro φ ψ hφψ hφ;
    exact hφψ ⨀ hφ;
  subst_closed := by
    intro φ hφ s;
    exact Hilbert.Deduction.subst! s hφ;
  nec_closed := by
    intro φ hφ;
    exact Entailment.nec! hφ;

instance [Entailment.Unnecessitation H] : H.logic.Unnecessitation := ⟨fun {_} h => unnec! h⟩

instance [Entailment.ModalDisjunctive H] :
    H.logic.ModalDisjunctive :=
  ⟨fun {_ _} h => modal_disjunctive h⟩

instance : (Logic.K).Normal := Hilbert.normal

end Hilbert


section «lp_section_1»

open Kripke

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FrameClass.logic (C : FrameClass) : Logic := { φ | C ⊧ φ }

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.FiniteFrameClass.logic (C : FiniteFrameClass) : Logic := { φ | C ⊧ φ }

lemma _root_.LO.Modal.Logic.eq_Hilbert_Logic_KripkeFrameClass_Logic
  {H : Hilbert ℕ} {C : FrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  · exact sound.sound;
  · exact complete.complete;

lemma _root_.LO.Modal.Logic.eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic
  {H : Hilbert ℕ} {C : FiniteFrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  · exact sound.sound;
  · exact complete.complete;

lemma _root_.LO.Modal.Logic.K.eq_AllKripkeFrameClass_Logic : Logic.K = AllFrameClass.logic :=
  Logic.eq_Hilbert_Logic_KripkeFrameClass_Logic

lemma _root_.LO.Modal.Logic.K.eq_AllKripkeFiniteFrameClass_Logic :
    Logic.K = AllFiniteFrameClass.logic :=
  Logic.eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic

end «lp_section_1»


end Modal
end LO
