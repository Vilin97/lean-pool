/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Entailment.K

/-! # KTc -/


namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S}

namespace KTc

variable [Entailment.KTc 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomFour : 𝓢 ⊢ Axioms.Four φ := axiomTc
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ KTc.axiomFour⟩

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomFive : 𝓢 ⊢ ◇φ ==> □◇φ := axiomTc
instance : HasAxiomFive 𝓢 := ⟨fun _ ↦ KTc.axiomFive⟩

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomDiaT : 𝓢 ⊢ ◇φ ==> φ := impTrans'' (and₁' diaDuality) (contra₂' axiomTc)
instance : HasAxiomDiaT 𝓢 := ⟨fun _ ↦ KTc.axiomDiaT⟩

end KTc


namespace KTc'

variable [Entailment.KTc' 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
protected def axiomTc :
    𝓢 ⊢ φ ==> □φ :=
  impTrans'' (contra₃' (impTrans'' (and₂' diaDuality) diaT)) boxDne
instance : HasAxiomTc 𝓢 := ⟨fun _ ↦ KTc'.axiomTc⟩

end KTc'


end Entailment
end LO
