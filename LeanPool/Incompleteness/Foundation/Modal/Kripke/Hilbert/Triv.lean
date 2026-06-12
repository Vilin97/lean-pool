/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # Triv -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveCoreflexiveFrameClass :
    FrameClass :=
  { F | Std.Refl F.Rel ∧ Coreflexive F }
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.EqualityFrameClass : FrameClass := { F | Equality F }

lemma _root_.LO.Modal.Kripke.eq_EqualityFrameClass_ReflexiveCoreflexiveFrameClass :
    EqualityFrameClass = ReflexiveCoreflexiveFrameClass := by
  ext F;
  constructor;
  · intro hEq;
    constructor;
    · exact ⟨refl_of_equality hEq⟩;
    · exact corefl_of_equality hEq;
  · rintro ⟨hRefl, hCorefl⟩;
    exact equality_of_refl_corefl hRefl.refl hCorefl;


namespace Hilbert
namespace Triv

instance _root_.LO.Modal.Hilbert.Triv.Kripke.soundReflCorefl :
    Sound (Hilbert.Triv) (Kripke.ReflexiveCoreflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩})
  · exact eq_Geach
  · unfold ReflexiveCoreflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.coreflexive_def];

instance _root_.LO.Modal.Hilbert.Triv.Kripke.soundEquality :
    Sound (Hilbert.Triv) (Kripke.EqualityFrameClass) := by
  rw [eq_EqualityFrameClass_ReflexiveCoreflexiveFrameClass];
  exact Kripke.soundReflCorefl;

instance _root_.LO.Modal.Hilbert.Triv.Kripke.consistent : Entailment.Consistent (Hilbert.Triv) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.Triv.Kripke.completeReflCorefl :
    Complete (Hilbert.Triv) (Kripke.ReflexiveCoreflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩});
  · exact eq_Geach;
  · unfold ReflexiveCoreflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.coreflexive_def];

instance _root_.LO.Modal.Hilbert.Triv.Kripke.completeEquality :
    Complete (Hilbert.Triv) (Kripke.EqualityFrameClass) := by
  rw [eq_EqualityFrameClass_ReflexiveCoreflexiveFrameClass];
  exact Kripke.completeReflCorefl;

end Triv
end Hilbert


end Modal
end LO
