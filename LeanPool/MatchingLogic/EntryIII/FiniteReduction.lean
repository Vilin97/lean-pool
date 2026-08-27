/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

import LeanPool.MatchingLogic.EntryIII.Compactness
import LeanPool.MatchingLogic.ProofSystem

/-!
# MatchingLogic.EntryIII.FiniteReduction
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-- Strong local completeness restricted to theories presented by finite lists. -/
def FiniteLocalCompleteness (S : Signature) (Var : Type) [DecidableEq Var] : Prop :=
  ∀ (l : List (Pattern S Var)) (phi : Pattern S Var),
    LocalCons {delta | delta ∈ l} phi →
      Provable (∅ : Set (Pattern S Var)) (.imp (conj l) phi)

/-- A finite conjunction denotes the same set as the conjunctive denotation of
the corresponding list-membership theory. -/
theorem Model.denote_conj_eq_denoteSet_list (M : Model S)
    (rho : Var → M.carrier) (l : List (Pattern S Var)) :
    M.denote rho (conj l) = M.denoteSet rho {delta | delta ∈ l} := by
  induction l with
  | nil =>
      simp [conj, MatchingLogic.Model.denoteSet]
  | cons delta l ih =>
      ext u
      simp [conj, Pattern.and, Pattern.nt, ih, MatchingLogic.Model.denoteSet]

/-- Pointwise form of local consequence from a finite list. -/
theorem localCons_list_iff (l : List (Pattern S Var)) (phi : Pattern S Var) :
    LocalCons {delta | delta ∈ l} phi ↔
      ∀ (M : Model S) (rho : Var → M.carrier),
        M.denote rho (conj l) ⊆ M.denote rho phi := by
  unfold LocalCons
  constructor
  · intro h M rho
    rw [M.denote_conj_eq_denoteSet_list]
    exact h M rho
  · intro h M rho
    rw [← M.denote_conj_eq_denoteSet_list]
    exact h M rho

/-- Semantic compactness reduces full strong local completeness to its
finite-list form. -/
theorem strongLocalCompleteness_of_finiteLocalCompleteness
    (hfinite : FiniteLocalCompleteness S Var) :
    StrongLocalCompleteness S Var := by
  rw [StrongLocalCompleteness]
  intro Delta phi hlocal
  obtain ⟨l, hl, hlocalFinite⟩ := localCons_compact hlocal
  exact ⟨l, hl, hfinite l phi hlocalFinite⟩

end MatchingLogic
