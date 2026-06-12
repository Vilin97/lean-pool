/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Filteration
import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame

/-! # K4 -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.TransitiveFrameClass : FrameClass := { F | IsTrans F.World F.Rel }
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.TransitiveFiniteFrameClass :
    FiniteFrameClass :=
  { F | IsTrans F.World F.Rel }

namespace Hilbert
namespace K4

instance _root_.LO.Modal.Hilbert.K4.Kripke.sound :
    Sound (Hilbert.K4) (Kripke.TransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 2, 1, 0⟩})
  · exact eq_Geach
  · unfold TransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.transitive_def];

instance _root_.LO.Modal.Hilbert.K4.Kripke.consistent : Entailment.Consistent (Hilbert.K4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.K4.Kripke.complete :
    Complete (Hilbert.K4) (Kripke.TransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 2, 1, 0⟩});
  · exact eq_Geach;
  · unfold TransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.transitive_def];

open finestFilterationTransitiveClosureModel in
instance _root_.LO.Modal.Hilbert.K4.Kripke.finiteComplete :
    Complete (Hilbert.K4) (TransitiveFiniteFrameClass) :=
  ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F F_trans V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply @filteration M φ.subformulas _ FM ?filterOf x φ (by simp) |>.mpr;
  · apply hp (by
      suffices Finite (FilterEqvQuotient M φ.subformulas) by
        simp only [FiniteFrameClass.toFrameClass];
        use ⟨FM.toFrame⟩;
        refine ⟨?_, rfl⟩;
        · exact transitive;
      apply FilterEqvQuotient.finite;
      simp;
    ) FM.Val;
  · apply finestFilterationTransitiveClosureModel.filterOf;
    exact F_trans;
⟩

end K4
end Hilbert

end Modal
end LO
