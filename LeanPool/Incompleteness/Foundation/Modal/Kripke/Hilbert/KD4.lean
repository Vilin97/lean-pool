/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # KD4 -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.SerialTransitiveFrameClass : FrameClass :=
  { F | Serial F ∧ IsTrans F.World F.Rel }

namespace Hilbert
namespace KD4

instance _root_.LO.Modal.Hilbert.KD4.Kripke.sound :
    Sound (Hilbert.KD4) (Kripke.SerialTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩});
  · exact eq_Geach;
  · unfold SerialTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.transitive_def];

instance _root_.LO.Modal.Hilbert.KD4.Kripke.consistent : Entailment.Consistent (Hilbert.KD4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KD4.Kripke.complete :
    Complete (Hilbert.KD4) (Kripke.SerialTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩});
  · exact eq_Geach;
  · unfold SerialTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.transitive_def];

end KD4
end Hilbert

end Modal
end LO
