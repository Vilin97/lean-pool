/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.IntProp.Hilbert.WellKnown
import LeanPool.Incompleteness.Foundation.IntProp.Kripke.Hilbert.Soundness
import LeanPool.Incompleteness.Foundation.IntProp.Kripke.Hilbert.Cl.Basic

/-! # Classical -/


namespace LO
namespace IntProp

open Kripke
open Formula.Kripke


namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
abbrev ClassicalValuation := ℕ → Prop

end Kripke


namespace Formula
namespace Kripke

open IntProp.Kripke

/-- Imported declaration from the Incompleteness formalization. -/
abbrev ClassicalSatisfies (V : ClassicalValuation) (φ : Formula ℕ) :
    Prop :=
  Satisfies (⟨pointFrame, ⟨fun _ => V, by tauto⟩⟩) () φ

namespace ClassicalSatisfies

instance : Semantics (Formula ℕ) (ClassicalValuation) := ⟨ClassicalSatisfies⟩

variable {V : ClassicalValuation} {a : ℕ}

@[simp] lemma atom_def : V ⊧ atom a ↔ V a := by simp only [Semantics.Realize, Satisfies]

instance : Semantics.Tarski (ClassicalValuation) where
  realize_top := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_bot := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_or  := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_and := by simp [Semantics.Realize, ClassicalSatisfies, Satisfies];
  realize_imp := by simp [Semantics.Realize]; tauto;
  realize_not := by simp [Semantics.Realize]; tauto;

end ClassicalSatisfies

end Kripke
end Formula


namespace Hilbert
namespace Cl

lemma classical_sound : (Hilbert.Cl) ⊢! φ → (∀ V : ClassicalValuation, V ⊧ φ) := by
  intro h V;
  apply Hilbert.Cl.Kripke.sound.sound h Kripke.pointFrame;
  simp [Euclidean];

lemma unprovable_of_exists_classicalValuation : (∃ V :
    ClassicalValuation, ¬(V ⊧ φ)) → (Hilbert.Cl) ⊬ φ := by
  contrapose;
  simp only [not_exists, not_not];
  apply classical_sound;

end Cl
end Hilbert


end IntProp
end LO
