/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Entailment.KT
import LeanPool.Incompleteness.Foundation.Modal.Entailment.K5

/-! # S5 -/


namespace LO
namespace Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.S5 𝓢]

-- MEMO: need more simple proof
/-- Imported declaration from the Incompleteness formalization. -/
def diaboxBox : 𝓢 ⊢ ◇□φ ==> □φ := by
  have : 𝓢 ⊢ ◇(∼φ) ==> □◇(∼φ) := axiomFive;
  have : 𝓢 ⊢ ∼□◇(∼φ) ==> ∼◇(∼φ) := contra₀' this;
  have : 𝓢 ⊢ ∼□◇(∼φ) ==> □φ := impTrans'' this boxDualityMpr;
  refine impTrans'' ?_ this;
  refine impTrans'' diaDualityMp <| ?_
  apply contra₀';
  apply implyBoxDistribute';
  refine impTrans'' diaDualityMp ?_;
  apply contra₀';
  apply implyBoxDistribute';
  apply dni;
omit [DecidableEq F] in
@[simp] lemma «diaboxBox!» : 𝓢 ⊢! ◇□φ ==> □φ := by
  classical
  exact ⟨diaboxBox⟩

/-- Imported declaration from the Incompleteness formalization. -/
def diaboxBox' (h : 𝓢 ⊢ ◇□φ) : 𝓢 ⊢ □φ := diaboxBox ⨀ h
omit [DecidableEq F] in
lemma «diaboxBox'!» (h : 𝓢 ⊢! ◇□φ) : 𝓢 ⊢! □φ := by
  classical
  exact ⟨diaboxBox' h.some⟩

/-- Imported declaration from the Incompleteness formalization. -/
def rmDiabox : 𝓢 ⊢ ◇□φ ==> φ := impTrans'' diaboxBox axiomT
omit [DecidableEq F] in
@[simp] lemma «rmDiabox!» : 𝓢 ⊢! ◇□φ ==> φ := by
  classical
  exact ⟨rmDiabox⟩

/-- Imported declaration from the Incompleteness formalization. -/
def rmDiabox' (h : 𝓢 ⊢ ◇□φ) : 𝓢 ⊢ φ := rmDiabox ⨀ h
omit [DecidableEq F] in
lemma «rmDiabox'!» (h : 𝓢 ⊢! ◇□φ) : 𝓢 ⊢! φ := by
  classical
  exact ⟨rmDiabox' h.some⟩

end Entailment
end LO
