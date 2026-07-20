/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.GL.Tree
import LeanPool.Incompleteness.Foundation.Modal.Kripke.SimpleExtension

/-! # Unnecessitation -/


namespace LO
namespace Modal

open Entailment
open Kripke
open Formula.Kripke

namespace Hilbert
namespace GL

lemma imply_boxdot_plain_of_imply_box_box : Hilbert.GL ⊢! □φ ==> □ψ → Hilbert.GL ⊢! ⊡φ ==> ψ := by
  contrapose;
  intro h;
  have := Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp h;
  obtain ⟨M, hs⟩ := this;
  have hs : Satisfies M.toModel M.root (⊡φ ⋏ ∼ψ) := by simp_all [Satisfies];
  replace hs :=
    @FiniteTransitiveTreeModel.SimpleExtension.modal_equivalence_original_world M M.root
      (⊡φ ⋏ ∼ψ) |>.mp hs;
  have ⟨hs₁₂, hs₃⟩ := Satisfies.and_def.mp hs;
  have ⟨hs₁, hs₂⟩ := Satisfies.and_def.mp hs₁₂;
  have hbp : Satisfies M↧.toModel (M↧.root) (□φ) := by
    intro x hx;
    rcases @Kripke.FiniteTransitiveTree.SimpleExtension.through_original_root
      M.toFiniteTransitiveTree x hx with (rfl | hr);
    · assumption;
    · apply hs₂;
      exact hr;
  have hbq : ¬(Satisfies M↧.toModel (M↧.root) (□ψ)) := by
    apply Satisfies.box_def.not.mpr;
    push Not;
    use M.root;
    constructor;
    · apply M↧.toRootedFrame.root_rooted M.root;
      simp [FiniteTransitiveTreeModel.SimpleExtension,
        Kripke.FiniteTransitiveTree.SimpleExtension]; -- TODO: extract lemma
    · assumption;
  apply Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mpr;
  use M↧;
  exact Classical.not_imp.mpr ⟨hbp, hbq⟩;

theorem «unnecessitation!» : Hilbert.GL ⊢! □φ → Hilbert.GL ⊢! φ := by
  intro h;
  have : Hilbert.GL ⊢! □⊤ ==> □φ := imply₁'! (ψ := □⊤) h;
  have : Hilbert.GL ⊢! ⊡⊤ ==> φ := imply_boxdot_plain_of_imply_box_box this;
  exact this ⨀ boxdotverum!;

noncomputable instance : Entailment.Unnecessitation Hilbert.GL :=
  ⟨fun h => unnecessitation! ⟨h⟩ |>.some⟩

end GL
end Hilbert

end Modal
end LO
