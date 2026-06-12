/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.Modal.Hilbert.Basic

/-! # K -/


namespace LO
namespace Modal
namespace Hilbert

variable {H : Hilbert α}

open Deduction

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
class HasK (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  /-- Imported declaration from the Incompleteness formalization. -/
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hK : H.HasK] : Entailment.HasAxiomK H where
  K φ ψ := by
    apply maxm;
    use Axioms.K (.atom hK.p) (.atom hK.q);
    constructor;
    · exact hK.mem_K;
    · use (fun b => if hK.p = b then φ else if hK.q = b then ψ else (.atom b));
      simp [hK.ne_pq];

end «lp_section_1»


section «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev K : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1)}⟩
instance : Hilbert.K.FiniteAxiomatizable where
instance : Hilbert.K.HasK where p := 0; q := 1
instance : Entailment.K (Hilbert.K) where

end «lp_section_2»

end Hilbert
end Modal
end LO
