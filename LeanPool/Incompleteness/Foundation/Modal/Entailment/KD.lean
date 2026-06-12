/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Entailment.K

/-! # KD -/


namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.KD 𝓢]

namespace KD

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomP : 𝓢 ⊢ Axioms.P := by
  have : 𝓢 ⊢ ∼∼□(∼⊥) := dni' <| nec notbot;
  have : 𝓢 ⊢ ∼◇⊥ := (contra₀' <| and₁' diaDuality) ⨀ this;
  exact (contra₀' axiomD) ⨀ this;
instance : HasAxiomP 𝓢 := ⟨KD.axiomP⟩

end KD

end Entailment
end LO
