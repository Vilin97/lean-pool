/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomGrz
import LeanPool.Incompleteness.Foundation.Modal.Kripke.Hilbert.Soundness

/-! # Soundness -/

@[expose] public section


namespace LO
namespace Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke

namespace Kripke

instance : ReflexiveTransitiveAntiSymmetricFiniteFrameClass.DefinedBy {Axioms.K (atom 0) (atom 1),
    Axioms.Grz (atom 0)} :=
  FiniteFrameClass.definedBy_with_axiomK
    ReflexiveTransitiveAntiSymmetricFiniteFrameClass.definedByAxiomGrz

instance : ReflexiveTransitiveAntiSymmetricFiniteFrameClass.IsNonempty := by
  use ⟨Unit, fun _ _ => True⟩;
  constructor
  · exact ⟨fun _ => trivial⟩
  · constructor
    · exact ⟨fun _ _ _ _ _ => trivial⟩
    · exact ⟨fun x y _ _ => by cases x; cases y; rfl⟩

end Kripke

namespace Hilbert
namespace Grz

instance _root_.LO.Modal.Hilbert.Grz.Kripke.sound :
    Sound (Hilbert.Grz) (Kripke.ReflexiveTransitiveAntiSymmetricFiniteFrameClass) :=
  inferInstance

instance _root_.LO.Modal.Hilbert.Grz.Kripke.consistent : Entailment.Consistent (Hilbert.Grz) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass ReflexiveTransitiveAntiSymmetricFiniteFrameClass

end Grz
end Hilbert

end Modal
end LO
