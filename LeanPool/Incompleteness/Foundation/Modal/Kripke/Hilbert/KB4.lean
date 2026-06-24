/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # KB4 -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.SymmetricTransitiveFrameClass : FrameClass :=
  { F | IsSymmetric F ∧ IsTrans F.World F.Rel }

namespace Hilbert
namespace KB4

instance _root_.LO.Modal.Hilbert.KB4.Kripke.sound :
    Sound (Hilbert.KB4) (Kripke.SymmetricTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  · exact eq_Geach;
  · unfold SymmetricTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.transitive_def];

instance _root_.LO.Modal.Hilbert.KB4.Kripke.consistent : Entailment.Consistent (Hilbert.KB4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KB4.Kripke.complete :
    Complete (Hilbert.KB4) (Kripke.SymmetricTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  · exact eq_Geach;
  · unfold SymmetricTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.transitive_def];

end KB4
end Hilbert

end Modal
end LO
