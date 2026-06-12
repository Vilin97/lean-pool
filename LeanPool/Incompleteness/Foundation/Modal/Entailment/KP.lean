/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Entailment.K

/-! # KP -/


namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.KP 𝓢]

namespace KP

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomD : 𝓢 ⊢ Axioms.D φ := by
  have : 𝓢 ⊢ φ ==> (∼φ ==> ⊥) := impTrans'' dni (and₁' negEquiv);
  have : 𝓢 ⊢ □φ ==> □(∼φ ==> ⊥) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □φ ==> (□(∼φ) ==> □⊥) := impTrans'' this axiomK;
  have : 𝓢 ⊢ □φ ==> (∼□⊥ ==> ∼□(∼φ)) := impTrans'' this contra₀;
  have : 𝓢 ⊢ □φ ==> ∼□(∼φ) := impSwap' this ⨀ axiomP;
  exact impTrans'' this (and₂' diaDuality);
instance : HasAxiomD 𝓢 := ⟨fun _ ↦ KP.axiomD⟩

end KP

end Entailment
end LO
