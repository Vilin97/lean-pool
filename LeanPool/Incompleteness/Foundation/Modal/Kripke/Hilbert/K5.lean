/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach

/-! # K5 -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.EuclideanFrameClass : FrameClass := { F | Euclidean F }
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.EuclideanFiniteFrameClass :
    FiniteFrameClass :=
  { F | Euclidean F.Rel }

namespace Hilbert
namespace K5

instance _root_.LO.Modal.Hilbert.K5.Kripke.sound :
    Sound (Hilbert.K5) (Kripke.EuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨1, 1, 0, 1⟩})
  · exact eq_Geach
  · unfold EuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def];

instance _root_.LO.Modal.Hilbert.K5.Kripke.consistent : Entailment.Consistent (Hilbert.K5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.K5.Kripke.complete :
    Complete (Hilbert.K5) (Kripke.EuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨1, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold EuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def];

end K5
end Hilbert

end Modal
end LO
