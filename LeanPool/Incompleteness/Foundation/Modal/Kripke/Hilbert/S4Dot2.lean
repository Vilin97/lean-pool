/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # S4Dot2 -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveTransitiveConfluentFrameClass :
    FrameClass :=
  { F | Std.Refl F ∧ IsTrans F.World F.Rel ∧ Confluent F  }

namespace Hilbert
namespace S4Dot2

instance _root_.LO.Modal.Hilbert.S4Dot2.Kripke.sound :
    Sound (Hilbert.S4Dot2) (ReflexiveTransitiveConfluentFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩});
  · exact eq_Geach;
  · unfold ReflexiveTransitiveConfluentFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def, Geachean.confluent_def];

instance _root_.LO.Modal.Hilbert.S4Dot2.Kripke.consistent :
    Entailment.Consistent (Hilbert.S4Dot2) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.S4Dot2.Kripke.complete :
    Complete (Hilbert.S4Dot2) (ReflexiveTransitiveConfluentFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩});
  · exact eq_Geach;
  · unfold ReflexiveTransitiveConfluentFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def, Geachean.confluent_def];

end S4Dot2
end Hilbert

end Modal
end LO
