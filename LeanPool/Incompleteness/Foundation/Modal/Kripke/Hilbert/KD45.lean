/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # KD45 -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.SerialTransitiveEuclideanFrameClass :
    FrameClass :=
  { F | Serial F ∧ IsTrans F.World F.Rel ∧ Euclidean F }

namespace Hilbert
namespace KD45

instance _root_.LO.Modal.Hilbert.KD45.Kripke.sound :
    Sound (Hilbert.KD45) (Kripke.SerialTransitiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SerialTransitiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.euclidean_def, Geachean.transitive_def];

instance _root_.LO.Modal.Hilbert.KD45.Kripke.consistent : Entailment.Consistent (Hilbert.KD45) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KD45.Kripke.complete :
    Complete (Hilbert.KD45) (Kripke.SerialTransitiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SerialTransitiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.euclidean_def, Geachean.transitive_def];

end KD45
end Hilbert

end Modal
end LO
