/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Entailment.K
import LeanPool.Incompleteness.Foundation.Modal.Entailment.KP
import LeanPool.Incompleteness.Foundation.Modal.Entailment.KD

/-! # KT -/


namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S}

namespace KT

variable [Entailment.KT 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def axiomDiaTc : 𝓢 ⊢ φ ==> ◇φ := by
  apply impTrans'' ?_ (and₂' diaDuality);
  exact impTrans'' dni <| contra₀' axiomT;
instance : HasAxiomDiaTc 𝓢 := ⟨fun _ ↦ KT.axiomDiaTc⟩

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomP : 𝓢 ⊢ ∼□⊥ := negEquiv'.mpr axiomT
instance : HasAxiomP 𝓢 := ⟨KT.axiomP⟩
instance : Entailment.KP 𝓢 where
instance : Entailment.KD 𝓢 where

end KT


namespace KT'

variable [Entailment.KT' 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomT :
    𝓢 ⊢ □φ ==> φ :=
  impTrans'' boxDni (contra₃' (impTrans'' diaTc diaDualityMp))

instance : HasAxiomT 𝓢 := ⟨fun _ ↦ KT'.axiomT⟩
instance : Entailment.KT 𝓢 where
instance : Entailment.KD 𝓢 where

end KT'


end Entailment
end LO
