/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Finite countertheory reduction for entry point (iii).

This isolates the remaining canonical-model obligation: it is enough to build
a pointed model for every locally consistent finite-list theory.  The reduction
itself is purely propositional plus the already pinned finite semantic bridge.
-/
import LeanPool.MatchingLogic.EntryIII.LocalTheory
import LeanPool.MatchingLogic.EntryIII.FiniteReduction

/-!
# MatchingLogic.EntryIII.Countertheory
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-- Finite pointed-model existence: every locally consistent theory presented
by a list has a model, valuation, and point matching all its members. -/
def FiniteLocalModelExistence (S : Signature) (Var : Type) [DecidableEq Var] : Prop :=
  ∀ l : List (Pattern S Var), LocConsistent {delta | delta ∈ l} →
    ∃ (M : Model S) (rho : Var → M.carrier) (u : M.carrier),
      u ∈ M.denoteSet rho {delta | delta ∈ l}

/-- Source Proposition 3.5(3), in the repository's finite-list presentation:
local and ordinary theoremhood coincide for the empty theory. -/
theorem locProvable_empty_iff {phi : Pattern S Var} :
    LocProvable (∅ : Set (Pattern S Var)) phi ↔
      Provable (∅ : Set (Pattern S Var)) phi := by
  constructor
  · rintro ⟨l, hl, hp⟩
    have hlNil : l = [] := by
      cases l with
      | nil => rfl
      | cons psi l => exact False.elim (hl psi (by simp))
    subst l
    exact Provable.mp (provable_top (∅ : Set (Pattern S Var))) (by simpa [conj] using hp)
  · exact LocProvable.of_provable

private theorem countertheory_taut :
    PForm.Taut
      (.imp
        (.imp (.imp (.atom 0) .bot) (.imp (.atom 1) .bot))
        (.imp (.atom 1) (.atom 0))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

/-- If `conj l → phi` is not a theorem, then the finite countertheory consisting
of `conj l` and `¬phi` is locally consistent. -/
theorem countertheory_locConsistent_of_not_provable
    {l : List (Pattern S Var)} {phi : Pattern S Var}
    (hnot : ¬ Provable (∅ : Set (Pattern S Var)) (.imp (conj l) phi)) :
    LocConsistent {delta | delta ∈ [conj l, Pattern.nt phi]} := by
  intro hbot
  have hbot' : LocProvable
      (insert (conj l) (insert (Pattern.nt phi) (∅ : Set (Pattern S Var))))
      (.bot : Pattern S Var) := by
    have hset : {delta : Pattern S Var | delta ∈ [conj l, Pattern.nt phi]} =
        insert (conj l) (insert (Pattern.nt phi) (∅ : Set (Pattern S Var))) := by
      ext delta
      simp
    rwa [← hset]
  have hfirst : LocProvable (insert (Pattern.nt phi) (∅ : Set (Pattern S Var)))
      (.imp (conj l) .bot) := hbot'.deduction_insert
  have hsecond : LocProvable (∅ : Set (Pattern S Var))
      (.imp (Pattern.nt phi) (.imp (conj l) .bot)) := hfirst.deduction_insert
  have hordinary : Provable (∅ : Set (Pattern S Var))
      (.imp (Pattern.nt phi) (.imp (conj l) .bot)) := locProvable_empty_iff.mp hsecond
  have hclassical : Provable (∅ : Set (Pattern S Var))
      (.imp (.imp (Pattern.nt phi) (.imp (conj l) .bot)) (.imp (conj l) phi)) := by
    simpa [PForm.subst, Pattern.nt] using
      (Provable.taut (Γ := (∅ : Set (Pattern S Var)))
        (θ := fun n => if n = 0 then phi else conj l) countertheory_taut)
  exact hnot (Provable.mp hordinary hclassical)

/-- Finite pointed-model existence implies finite local completeness. -/
theorem finiteLocalCompleteness_of_finiteLocalModelExistence
    (hmodel : FiniteLocalModelExistence S Var) :
    FiniteLocalCompleteness S Var := by
  intro l phi hlocal
  by_contra hnot
  have hconsistent :
      LocConsistent {delta | delta ∈ [conj l, Pattern.nt phi]} :=
    countertheory_locConsistent_of_not_provable hnot
  obtain ⟨M, rho, u, hu⟩ := hmodel [conj l, Pattern.nt phi] hconsistent
  have hu' : ∀ delta ∈ [conj l, Pattern.nt phi], u ∈ M.denote rho delta := by
    simpa only [Model.denoteSet, Set.mem_iInter, Set.mem_ofPred_eq] using hu
  have huConj : u ∈ M.denote rho (conj l) := by
    exact hu' (conj l) (by simp)
  have huPremises : u ∈ M.denoteSet rho {delta | delta ∈ l} := by
    rwa [← M.denote_conj_eq_denoteSet_list]
  have huPhi : u ∈ M.denote rho phi := hlocal M rho huPremises
  have huNotPhi : u ∈ M.denote rho (Pattern.nt phi) := by
    exact hu' (Pattern.nt phi) (by simp)
  have hnotPhi : u ∉ M.denote rho phi := by
    simpa only [denote_nt, Set.mem_compl_iff] using huNotPhi
  exact hnotPhi huPhi

end MatchingLogic
