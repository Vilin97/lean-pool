/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomL
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness
import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown

/-! # Soundness -/


namespace LO
namespace Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke

namespace Kripke

instance :
    TransitiveIrreflexiveFiniteFrameClass.DefinedBy {Axioms.K (atom 0) (atom 1),
    Axioms.L (atom 0)} :=
  FiniteFrameClass.definedBy_with_axiomK TransitiveIrreflexiveFiniteFrameClass.DefinedByL

instance : TransitiveIrreflexiveFiniteFrameClass.IsNonempty := by
  use ⟨Unit, fun _ _ => False⟩;
  constructor
  · exact ⟨fun _ _ _ h _ => False.elim h⟩
  · exact ⟨fun _ h => h⟩

end Kripke


namespace Hilbert
namespace GL

instance _root_.LO.Modal.Hilbert.GL.Kripke.finiteSound :
    Sound (Hilbert.GL) TransitiveIrreflexiveFiniteFrameClass :=
  inferInstance

instance _root_.LO.Modal.Hilbert.GL.Kripke.consistent : Entailment.Consistent (Hilbert.GL) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass TransitiveIrreflexiveFiniteFrameClass

end GL
end Hilbert

end Modal
end LO
