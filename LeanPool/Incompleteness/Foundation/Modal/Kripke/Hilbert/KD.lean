/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # KD -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.SerialFrameClass : FrameClass := { F | Serial F }

namespace Hilbert
namespace KD

instance _root_.LO.Modal.Hilbert.KD.Kripke.sound :
    Sound (Hilbert.KD) (Kripke.SerialFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩});
  · exact eq_Geach;
  · unfold SerialFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def];

instance _root_.LO.Modal.Hilbert.KD.Kripke.consistent : Entailment.Consistent (Hilbert.KD) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KD.Kripke.complete :
    Complete (Hilbert.KD) (Kripke.SerialFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 1⟩});
  · exact eq_Geach;
  · unfold SerialFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def];

end KD
end Hilbert

end Modal
end LO
