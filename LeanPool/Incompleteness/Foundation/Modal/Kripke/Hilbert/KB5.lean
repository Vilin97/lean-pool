/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # KB5 -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.SymmetricEuclideanFrameClass :
    FrameClass :=
  { F | Symmetric F ∧ Euclidean F }

namespace Hilbert
namespace KB5

instance _root_.LO.Modal.Hilbert.KB5.Kripke.sound :
    Sound (Hilbert.KB5) (Kripke.SymmetricEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SymmetricEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.euclidean_def];

instance _root_.LO.Modal.Hilbert.KB5.Kripke.consistent : Entailment.Consistent (Hilbert.KB5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KB5.Kripke.complete :
    Complete (Hilbert.KB5) (Kripke.SymmetricEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold SymmetricEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.euclidean_def];

end KB5
end Hilbert

end Modal
end LO
