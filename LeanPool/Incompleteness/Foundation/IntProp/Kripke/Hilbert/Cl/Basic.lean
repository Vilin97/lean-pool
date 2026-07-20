/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.IntProp.Hilbert.WellKnown
import LeanPool.Incompleteness.Foundation.IntProp.Kripke.Hilbert.Soundness

/-! # Basic -/


namespace LO
namespace IntProp

open Kripke
open Formula.Kripke


/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.IntProp.Kripke.EuclideanFrameClass : FrameClass := { F | Euclidean F }

instance _root_.LO.IntProp.Kripke.EuclideanFrameClass.definedByLEM :
    Kripke.EuclideanFrameClass.DefinedByFormula (Axioms.LEM (.atom 0)) :=
  ⟨by
  rintro F;
  constructor;
  · rintro hEucl _ ⟨_, rfl⟩;
    exact ValidOnFrame.lem <| symm_of_refl_eucl F.rel_refl.refl hEucl
  · rintro h x y z Rxy Rxz;
    let V : Kripke.Valuation F := ⟨fun {v a} => z ≺ v, by
      intro w v Rwv a Rzw;
      exact F.rel_trans' Rzw Rwv;
    ⟩;
    suffices Satisfies ⟨F, V⟩ y (.atom 0) by simpa [Satisfies] using this;
    apply V.hereditary Rxy;
    have hlem : F ⊧ Axioms.LEM (.atom 0) := h _ rfl;
    have hx := (ValidOnFrame.models_iff.mp hlem) V x;
    simp only [Semantics.Realize, Satisfies, imp_false, or_iff_not_imp_right, not_forall,
      not_not, forall_exists_index, V] at hx;
    exact hx z Rxz (F.rel_refl.refl z)
⟩

instance : Kripke.EuclideanFrameClass.IsNonempty := ⟨by
  use pointFrame;
  simp [Euclidean];
⟩


open Kripke

namespace Hilbert
namespace Cl
namespace Kripke

instance : EuclideanFrameClass.DefinedBy (Hilbert.Cl.axioms) :=
  FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.Cl EuclideanFrameClass := inferInstance

instance consistent : Entailment.Consistent Hilbert.Cl :=
  Kripke.Hilbert.consistent_of_FrameClass EuclideanFrameClass

end Kripke
end Cl
end Hilbert


end IntProp
end LO
