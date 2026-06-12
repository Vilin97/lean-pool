/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Hilbert.K
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Completeness
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Filteration
import LeanPool.Incompleteness.Foundation.Modal.Kripke.FiniteFrame

/-! # K -/


namespace LO
namespace Modal

open Kripke

namespace Hilbert
namespace K

instance _root_.LO.Modal.Hilbert.K.Kripke.sound : Sound (Hilbert.K) AllFrameClass := inferInstance

instance : Entailment.Consistent (Hilbert.K) := Hilbert.consistent_of_FrameClass AllFrameClass

instance : Kripke.Canonical (Hilbert.K) (AllFrameClass) := ⟨by trivial⟩

instance _root_.LO.Modal.Hilbert.K.Kripke.completeAll :
    Complete (Hilbert.K) (AllFrameClass) :=
  inferInstance

instance _root_.LO.Modal.Hilbert.K.Kripke.completeAllFinite :
    Complete (Hilbert.K) (AllFiniteFrameClass) :=
  ⟨by
  intro φ hp;
  apply Kripke.completeAll.complete;
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFilterationModel M ↑φ.subformulas;
  apply filteration FM (coarsestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulas) by
      use ⟨FM.toFrame⟩;
      simp [];
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Val
⟩

end K
end Hilbert

end Modal
end LO
