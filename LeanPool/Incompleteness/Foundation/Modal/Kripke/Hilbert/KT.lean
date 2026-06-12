/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # KT -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveFrameClass : FrameClass := { F | Std.Refl F }

namespace Hilbert
namespace KT

instance _root_.LO.Modal.Hilbert.KT.Kripke.sound :
    Sound (Hilbert.KT) (Kripke.ReflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩});
  · exact eq_Geach;
  · unfold ReflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def];

instance _root_.LO.Modal.Hilbert.KT.Kripke.consistent : Entailment.Consistent (Hilbert.KT) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KT.Kripke.complete :
    Complete (Hilbert.KT) (Kripke.ReflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩});
  · exact eq_Geach;
  · unfold ReflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def];

end KT
end Hilbert

end Modal
end LO
