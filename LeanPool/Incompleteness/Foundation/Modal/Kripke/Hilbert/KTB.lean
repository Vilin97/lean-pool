/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Geach
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Filteration
import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame

/-! # KTB -/


namespace LO
namespace Modal

open Kripke
open Geachean

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveSymmetricFrameClass :
    FrameClass :=
  { F | Std.Refl F ∧ IsSymmetric F }
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.ReflexiveSymmetricFiniteFrameClass :
    FiniteFrameClass :=
  { F | Std.Refl F.Rel ∧ IsSymmetric F.Rel }

namespace Hilbert
namespace KTB

instance _root_.LO.Modal.Hilbert.KTB.Kripke.sound :
    Sound (Hilbert.KTB) (Kripke.ReflexiveSymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold ReflexiveSymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.symmetric_def];

instance _root_.LO.Modal.Hilbert.KTB.Kripke.consistent : Entailment.Consistent (Hilbert.KTB) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance _root_.LO.Modal.Hilbert.KTB.Kripke.complete :
    Complete (Hilbert.KTB) (Kripke.ReflexiveSymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  · exact eq_Geach;
  · unfold ReflexiveSymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.symmetric_def];

instance _root_.LO.Modal.Hilbert.KTB.Kripke.finiteComplete :
    Complete (Hilbert.KTB) (ReflexiveSymmetricFiniteFrameClass) :=
  ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_symm⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationModel M φ.subformulas;
  apply filteration FM (finestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulas) by
      simp only [FiniteFrameClass.toFrameClass, ReflexiveSymmetricFiniteFrameClass,
        Set.mem_image, Set.mem_setOf_eq];
      use ⟨FM.toFrame⟩;
      refine ⟨⟨?_, ?_⟩, ?_⟩;
      · apply reflexive_filterOf_of_reflexive (finestFilterationModel.filterOf);
        exact F_refl;
      · apply finestFilterationModel.symmetric_of_symmetric;
        exact F_symm;
      · rfl;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Val
⟩

end KTB
end Hilbert

end Modal
end LO
