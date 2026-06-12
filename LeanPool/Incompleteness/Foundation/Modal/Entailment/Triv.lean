/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Entailment.KT
import LeanPool.Incompleteness.Foundation.Modal.Entailment.KTc

/-! # Triv -/


namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Triv 𝓢]

namespace Triv

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomGrz : 𝓢 ⊢ □(□(φ ==> □φ) ==> φ) ==> φ := by
  have : 𝓢 ⊢ φ ==> □φ := axiomTc;
  have d₁ := nec this;
  have d₂ : 𝓢 ⊢ □(φ ==> □φ) ==> ((□(φ ==> □φ)) ==> φ) ==> φ := pPqQ;
  have := d₂ ⨀ d₁;
  exact impTrans'' axiomT this;
instance : HasAxiomGrz 𝓢 := ⟨fun _ ↦ Triv.axiomGrz⟩

end Triv

end Entailment
end LO
