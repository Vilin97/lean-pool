/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Vorspiel.BinaryRelations
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Completeness

/-! # AxiomVer -/


namespace LO
namespace Modal

open Formula.Kripke

namespace Kripke

/-- Imported declaration from the Incompleteness formalization. -/
abbrev IsolatedFrameClass : FrameClass := { F | Isolated F }

instance : IsolatedFrameClass.IsNonempty := by
  use ⟨Unit, fun _ _ => False⟩;
  tauto;

instance _root_.LO.Modal.Kripke.IsolatedFrameClass.DefinedByAxiomVer :
    IsolatedFrameClass.DefinedByFormula (Axioms.Ver (.atom 0)) :=
  FrameClass.definedByFormula_of_iff_mem_validate <| by
  intro F;
  constructor;
  · intro h V x y Rxy;
    have := h Rxy;
    contradiction;
  · intro h x y Rxy;
    have := h (fun _ _ => False) x y Rxy;
    simp [Formula.Kripke.Satisfies] at this;

end Kripke

end Modal
end LO
