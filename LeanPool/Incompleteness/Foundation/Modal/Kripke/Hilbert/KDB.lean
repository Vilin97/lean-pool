/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # KDB -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.SerialSymmetricFrameClass :
    FrameClass :=
  { F | Serial F ∧ Symmetric F }

namespace Hilbert
namespace KDB

instance _root_.LO.Modal.Hilbert.KDB.Kripke.sound :
    Sound (Hilbert.KDB) (Kripke.SerialSymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SerialSymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.symmetric_def];

instance _root_.LO.Modal.Hilbert.KDB.Kripke.consistent : Entailment.Consistent (Hilbert.KDB) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KDB.Kripke.complete :
    Complete (Hilbert.KDB) (Kripke.SerialSymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SerialSymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.symmetric_def];

end KDB
end Hilbert

end Modal
end LO
