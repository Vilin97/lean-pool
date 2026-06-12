/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Filteration
import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame

/-! # KT4B -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveTransitiveSymmetricFrameClass :
    FrameClass :=
  { F | Std.Refl F ∧ IsTrans F.World F.Rel ∧ Symmetric F }
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveTransitiveSymmetricFiniteFrameClass :
    FiniteFrameClass :=
  { F | Std.Refl F.Rel ∧ IsTrans F.World F.Rel ∧ Symmetric F.Rel }

namespace Hilbert
namespace KT4B

instance _root_.LO.Modal.Hilbert.KT4B.Kripke.consistent : Entailment.Consistent (Hilbert.KT4B) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KT4B.Kripke.complete :
    Complete (Hilbert.KT4B) (Kripke.ReflexiveTransitiveSymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold ReflexiveTransitiveSymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.symmetric_def, Geachean.transitive_def];

open finestFilterationTransitiveClosureModel in
instance _root_.LO.Modal.Hilbert.KT4B.Kripke.finiteComplete :
    Complete (Hilbert.KT4B) (ReflexiveTransitiveSymmetricFiniteFrameClass) :=
  ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_trans, F_symm⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply @filteration M φ.subformulas _ FM ?filterOf x φ (by simp) |>.mpr;
  · apply hp (by
      suffices Finite (FilterEqvQuotient M φ.subformulas) by
        simp only [FiniteFrameClass.toFrameClass, Set.mem_image, Set.mem_setOf_eq];
        use ⟨FM.toFrame⟩;
        refine ⟨⟨?refl, transitive, ?symm⟩, rfl⟩;
        · exact reflexive_of_transitive_reflexive (by apply F_trans) F_refl;
        · exact symmetric_of_symmetric F_symm;
      apply FilterEqvQuotient.finite;
      simp;
    ) FM.Val;
  · apply finestFilterationTransitiveClosureModel.filterOf
    exact F_trans;
⟩

end KT4B
end Hilbert


end Modal
end LO
