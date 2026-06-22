/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.IntProp.Hilbert.Basic

/-! # Int -/


namespace LO
namespace IntProp
namespace Hilbert

variable {H : Hilbert α}

open Deduction

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
class HasEFQ (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_efq : (⊥ ==> (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hEfq : H.HasEFQ] : Entailment.HasAxiomEFQ H where
  efq φ :=
    maxm ⟨Axioms.EFQ (Formula.atom hEfq.p), hEfq.mem_efq,
      fun b => if hEfq.p = b then φ else (.atom b), by simp⟩
instance [DecidableEq α] [H.HasEFQ] : Entailment.Intuitionistic H where

end «lp_section_1»


section «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Int : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0)}⟩
instance : Hilbert.Int.FiniteAxiomatizable where
instance : Hilbert.Int.HasEFQ where p := 0;

end «lp_section_2»

end Hilbert
end IntProp
end LO
