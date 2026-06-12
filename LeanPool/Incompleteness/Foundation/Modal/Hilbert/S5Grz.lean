/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
import LeanPool.Incompleteness.Foundation.Modal.Entailment.S5
import LeanPool.Incompleteness.Foundation.Modal.Entailment.KTc
import LeanPool.Incompleteness.Foundation.Modal.Entailment.Triv

/-! # S5Grz -/


namespace LO
namespace Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S}


section «lp_section_1»

variable [DecidableEq F]
variable [Entailment.S5 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
def lem₁DiaTOfS5Grz :
    𝓢 ⊢ (∼□(∼φ) ==> ∼□(∼□φ)) ==> (◇φ ==> ◇□φ) :=
  impTrans'' (revDhypImp' diaDualityMp) (dhypImp' diaDualityMpr)

/-- Imported declaration from the Incompleteness formalization. -/
def lem₂DiaTOfS5Grz : 𝓢 ⊢ (◇φ ==> ◇□φ) ==> (◇φ ==> φ) := dhypImp' rmDiabox

end «lp_section_1»


/-- Imported declaration from the Incompleteness formalization. -/
protected class S5Grz (𝓢 : S) extends Entailment.S5 𝓢, HasAxiomGrz 𝓢

namespace S5Grz

variable [DecidableEq F]
variable [Entailment.S5Grz 𝓢]

/-- Imported declaration from the Incompleteness formalization. -/
protected def diaT : 𝓢 ⊢ ◇φ ==> φ := by
  have : 𝓢 ⊢ (φ ==> □φ) ==> (∼□φ ==> ∼φ) := contra₀;
  have : 𝓢 ⊢ □(φ ==> □φ) ==> □(∼□φ ==> ∼φ) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □(φ ==> □φ) ==> (□(∼□φ) ==> □(∼φ)) := impTrans'' this axiomK;
  have : 𝓢 ⊢ □(φ ==> □φ) ==> (∼□(∼φ) ==> ∼□(∼□φ)) := impTrans'' this contra₀;
  have : 𝓢 ⊢ □(φ ==> □φ) ==> (◇φ ==> ◇□φ) := impTrans'' this lem₁DiaTOfS5Grz;
  have : 𝓢 ⊢ □(φ ==> □φ) ==> (◇φ ==> □φ) := impTrans'' this <| dhypImp' diaboxBox;
  have : 𝓢 ⊢ □(φ ==> □φ) ==> (◇φ ==> φ) := impTrans'' this <| dhypImp' axiomT;
  have : 𝓢 ⊢ ◇φ ==> □(φ ==> □φ) ==> φ := impSwap' this;
  have : 𝓢 ⊢ □◇φ ==> □(□(φ ==> □φ) ==> φ) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □◇φ ==> φ := impTrans'' this axiomGrz;
  exact impTrans'' axiomFive this;

instance : HasAxiomDiaT 𝓢 := ⟨fun _ ↦ S5Grz.diaT⟩
instance : Entailment.KTc' 𝓢 where

end S5Grz

end Entailment
end LO


namespace LO
namespace Modal
namespace Hilbert

open Entailment

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev S5Grz :
    Hilbert ℕ :=
  ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0), Axioms.Grz (.atom 0)}⟩
instance : (Hilbert.S5Grz).HasK where p := 0; q := 1;
instance : (Hilbert.S5Grz).HasT where p := 0
instance : (Hilbert.S5Grz).HasFive where p := 0
instance : (Hilbert.S5Grz).HasGrz where p := 0
instance : Entailment.S5Grz (Hilbert.S5Grz) where
instance : Entailment.KTc' (Hilbert.S5Grz) where

theorem iff_provable_S5Grz_provable_Triv : (Hilbert.S5Grz ⊢! φ) ↔ (Hilbert.Triv ⊢! φ) := by
  constructor;
  · apply fun h ↦ (weakerThan_of_dominate_axioms @h).subset;
    simp;
  · apply fun h ↦ (weakerThan_of_dominate_axioms @h).subset;
    rintro φ (⟨_, _, rfl⟩ | (⟨_, rfl⟩ | ⟨_, rfl⟩)) <;> simp;

end Hilbert
end Modal
end LO
