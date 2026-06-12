/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Foundation.IntProp.Hilbert.Int

/-! # WellKnown -/


namespace LO
namespace IntProp
namespace Hilbert

variable {H : Hilbert α}

open Deduction

section «lp_section_1»

/-- Imported declaration from the Incompleteness formalization. -/
class HasLEM (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_lem : (.atom p ⋎ ∼(.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hLEM : H.HasLEM] : Entailment.HasAxiomLEM H where
  lem φ := by
    apply maxm;
    use Axioms.LEM (.atom hLEM.p);
    constructor;
    · exact hLEM.mem_lem;
    · use (fun b => if hLEM.p = b then φ else (.atom b));
      simp;


/-- Imported declaration from the Incompleteness formalization. -/
class HasDNE (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_dne : (∼∼(.atom p) ==> (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hDNE : H.HasDNE] : Entailment.HasAxiomDNE H where
  dne φ := by
    apply maxm;
    use Axioms.DNE (.atom hDNE.p);
    constructor;
    · exact hDNE.mem_dne;
    · use (fun b => if hDNE.p = b then φ else (.atom b));
      simp;


/-- Imported declaration from the Incompleteness formalization. -/
class HasWeakLEM (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  mem_wlem : (∼(.atom p) ⋎ ∼∼(.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hWLEM : H.HasWeakLEM] : Entailment.HasAxiomWeakLEM H where
  wlem φ := by
    apply maxm;
    use Axioms.WeakLEM (.atom hWLEM.p);
    constructor;
    · exact hWLEM.mem_wlem;
    · use (fun b => if hWLEM.p = b then φ else (.atom b));
      simp;


/-- Imported declaration from the Incompleteness formalization. -/
class HasDummett (H : Hilbert α) where
  /-- Imported declaration from the Incompleteness formalization. -/
  p : α
  /-- Imported declaration from the Incompleteness formalization. -/
  q : α
  ne_pq : p ≠ q := by tauto;
  mem_dummet : ((.atom p) ==> (.atom q)) ⋎ ((.atom q) ==> (.atom p)) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hDummett : H.HasDummett] : Entailment.HasAxiomDummett H where
  dummett φ ψ := by
    apply maxm;
    use Axioms.Dummett (.atom hDummett.p) (.atom hDummett.q);
    constructor;
    · exact hDummett.mem_dummet;
    · use (fun b =>
        if hDummett.p = b then φ
        else if hDummett.q = b then ψ
        else (.atom b)
      );
      simp [hDummett.ne_pq];

end «lp_section_1»


section «lp_section_2»


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Cl : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.LEM (.atom 0)}⟩
instance : Hilbert.Cl.FiniteAxiomatizable where
instance : Hilbert.Cl.HasEFQ where p := 0;
instance : Hilbert.Cl.HasLEM where p := 0;
instance : Entailment.Classical (Hilbert.Cl) where

lemma Int_weakerThan_Cl : (Hilbert.Int) wkn (Hilbert.Cl) := by
  apply weakerThan_of_subset_axioms;
  tauto;


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev KC : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.WeakLEM (.atom 0)}⟩
instance : Hilbert.KC.FiniteAxiomatizable where
instance : Hilbert.KC.HasEFQ where p := 0;
instance : Hilbert.KC.HasWeakLEM where p := 0;
instance : Entailment.Intuitionistic (Hilbert.KC) where


/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev LC : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.Dummett (.atom 0) (.atom 1)}⟩
instance : Hilbert.LC.FiniteAxiomatizable where
instance : Hilbert.LC.HasEFQ where p := 0;
instance : Hilbert.LC.HasDummett where p := 0; q := 1;
instance : Entailment.Intuitionistic (Hilbert.LC) where

end «lp_section_2»

end Hilbert
end IntProp
end LO
