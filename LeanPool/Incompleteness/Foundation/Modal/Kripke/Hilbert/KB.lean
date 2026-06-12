/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # KB -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.SymmetricFrameClass : FrameClass := { F | Symmetric F }

namespace Hilbert
namespace KB

instance _root_.LO.Modal.Hilbert.KB.Kripke.sound :
    Sound (Hilbert.KB) (Kripke.SymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def];

instance _root_.LO.Modal.Hilbert.KB.Kripke.consistent : Entailment.Consistent (Hilbert.KB) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KB.Kripke.complete :
    Complete (Hilbert.KB) (Kripke.SymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def];

end KB
end Hilbert

end Modal
end LO
