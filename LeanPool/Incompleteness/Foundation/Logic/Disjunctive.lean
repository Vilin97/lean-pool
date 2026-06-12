/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Supplemental

/-! # Disjunctive -/


namespace LO
namespace Entailment

variable {F : Type*} [LogicalConnective F]
variable {S : Type*} [Entailment F S]

/-- Imported declaration from the Incompleteness formalization. -/
class Disjunctive (𝓢 : S) : Prop where
  disjunctive : ∀ {φ ψ}, 𝓢 ⊢! φ ⋎ ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ

alias disjunctive := Disjunctive.disjunctive

lemma iff_disjunctive {𝓢 : S} : (Disjunctive 𝓢) ↔ ∀ {φ ψ}, 𝓢 ⊢! φ ⋎ ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ := by
  constructor;
  · apply Disjunctive.disjunctive;
  · exact fun d ↦ ⟨d⟩;

lemma iff_complete_disjunctive {𝓢 : S} [Entailment.Classical 𝓢] :
    (Entailment.Complete 𝓢) ↔ (Disjunctive 𝓢) := by
  classical
  constructor;
  · intro hComp;
    apply iff_disjunctive.mpr;
    intro φ ψ hpq;
    rcases (hComp φ) with (hp | hnp);
    · left; assumption;
    · right; exact or₃'''! (efq_of_neg! hnp) imp_id! hpq;
  · intro hDisj φ;
    replace hDisj : ∀ {φ ψ}, 𝓢 ⊢! φ ⋎ ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ := iff_disjunctive.mp hDisj;
    exact @hDisj φ (∼φ) lem!;

end Entailment
end LO
