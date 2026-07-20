/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Entailment.K

/-! # Grz -/


namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Grz 𝓢]

namespace Grz

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def lemmaAxiomFourAxiomT : 𝓢 ⊢ □φ ==> (φ ⋏ (□φ ==> □□φ)) :=
  impTrans'' (lemmaGrz₁ (φ := φ)) axiomGrz

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable def axiomFour : 𝓢 ⊢ □φ ==> □□φ :=
  ppq <| impTrans'' lemmaAxiomFourAxiomT and₂
noncomputable instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ Grz.axiomFour⟩

/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable def axiomT : 𝓢 ⊢ □φ ==> φ := impTrans'' lemmaAxiomFourAxiomT and₁
noncomputable instance : HasAxiomT 𝓢 := ⟨fun _ ↦ Grz.axiomT⟩

end Grz

end Entailment
end LO
