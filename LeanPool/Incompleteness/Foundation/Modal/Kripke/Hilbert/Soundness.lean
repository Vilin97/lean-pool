/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Hilbert.Basic
import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame

/-! # Soundness -/


namespace LO
namespace Modal

open Kripke
open Formula
open Formula.Kripke

namespace Kripke
namespace Hilbert

variable {H : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}


section «lp_section_1»

variable {C : Kripke.FrameClass}

lemma soundness_of_FrameClass_definedBy_axiomInstances [defined : C.DefinedBy H.axiomInstances] :
    H ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Deduction.rec! with
  | maxm h =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h;
    apply defined.defines F |>.mp hF (ψ⟦s⟧);
    exact ⟨ψ, by assumption, s, rfl⟩;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

instance [defs : C.DefinedBy H.axioms] : C.DefinedBy H.axiomInstances := ⟨by
  intro F;
  constructor;
  · rintro hF φ ⟨ψ, hψ, ⟨s, rfl⟩⟩;
    exact ValidOnFrame.subst <| defs.defines F |>.mp hF ψ hψ;
  · intro h;
    apply defs.defines F |>.mpr;
    intro φ hφ;
    apply h;
    exact ⟨φ, by assumption, .id, by simp⟩;
⟩

instance [C.DefinedBy H.axioms] :
    Sound H C :=
  ⟨fun {_} => soundness_of_FrameClass_definedBy_axiomInstances⟩

lemma consistent_of_FrameClass_aux [nonempty : C.IsNonempty] [sound : Sound H C] : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  apply ValidOnFrameClass.not_of_exists_frame;
  obtain ⟨F, hF⟩ := nonempty;
  exact ⟨F, hF, by simp⟩;

lemma consistent_of_FrameClass (C : Kripke.FrameClass) [C.IsNonempty] [Sound H C] :
    Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable;
  exact consistent_of_FrameClass_aux (C := C);

end «lp_section_1»


section «lp_section_2»

variable {C : Kripke.FiniteFrameClass}

lemma soundness_of_FiniteFrameClass_definedBy_axiomInstances [defined :
    C.DefinedBy H.axiomInstances] :
    H ⊢! φ → C ⊧ φ := by
  rintro hφ _ ⟨F, ⟨hF, rfl⟩⟩;
  induction hφ using Hilbert.Deduction.rec! with
  | maxm h =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h;
    apply defined.defines F |>.mp hF (ψ⟦s⟧);
    exact ⟨ψ, by assumption, s, rfl⟩;
  | mdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | nec ih => exact ValidOnFrame.nec ih;
  | imply₁ => exact ValidOnFrame.imply₁;
  | imply₂ => exact ValidOnFrame.imply₂;
  | ec => exact ValidOnFrame.elimContra;

instance [defs : C.DefinedBy H.axioms] : C.DefinedBy H.axiomInstances := ⟨by
  intro F;
  constructor;
  · rintro hF φ ⟨ψ, hψ, ⟨s, rfl⟩⟩;
    exact ValidOnFrame.subst <| defs.defines F |>.mp hF ψ hψ;
  · intro h;
    apply defs.defines F |>.mpr;
    intro φ hφ;
    apply h;
    exact ⟨φ, by assumption, .id, by simp⟩;
⟩

instance [C.DefinedBy H.axioms] :
    Sound H C :=
  ⟨fun {_} => soundness_of_FiniteFrameClass_definedBy_axiomInstances⟩

lemma consistent_of_FiniteFrameClass_aux [nonempty : C.IsNonempty] [sound : Sound H C] : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  apply ValidOnFrameClass.not_of_exists_frame;
  obtain ⟨F, hF⟩ := nonempty;
  exact ⟨F.toFrame, ⟨F, hF, rfl⟩, by simp⟩;

lemma consistent_of_FiniteFrameClass (C : Kripke.FiniteFrameClass) [C.IsNonempty] [Sound H C] :
    Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable;
  exact consistent_of_FiniteFrameClass_aux (C := C);

end «lp_section_2»


end Hilbert
end Kripke

end Modal
end LO
