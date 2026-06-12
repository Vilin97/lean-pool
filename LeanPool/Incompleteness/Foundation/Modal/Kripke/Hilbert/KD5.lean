/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # KD5 -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.SerialEuclideanFrameClass :
    FrameClass :=
  { F | Serial F ∧ Euclidean F }

namespace Hilbert
namespace KD5

instance _root_.LO.Modal.Hilbert.KD5.Kripke.sound :
    Sound (Hilbert.KD5) (Kripke.SerialEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SerialEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.euclidean_def];

instance _root_.LO.Modal.Hilbert.KD5.Kripke.consistent : Entailment.Consistent (Hilbert.KD5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KD5.Kripke.complete :
    Complete (Hilbert.KD5) (Kripke.SerialEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SerialEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.euclidean_def];

end KD5
end Hilbert

end Modal
end LO
