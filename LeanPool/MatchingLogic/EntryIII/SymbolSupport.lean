/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/- Finite symbol support for reducing arbitrary signatures to finite ones. -/
import LeanPool.MatchingLogic.ProofSystem
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic

/-!
# MatchingLogic.EntryIII.SymbolSupport
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type}

namespace Pattern

/-- The finite set of signature symbols occurring in a pattern. -/
def symbolSupport [DecidableEq S.Sym] : Pattern S Var → Finset S.Sym
  | .var _ => ∅
  | .bot => ∅
  | .app sigma args => insert sigma (Finset.univ.biUnion (fun i => (args i).symbolSupport))
  | .imp phi psi => phi.symbolSupport ∪ psi.symbolSupport
  | .ex _ phi => phi.symbolSupport

/-- Every head symbol belongs to the support of its application pattern. -/
theorem head_mem_symbolSupport [DecidableEq S.Sym]
    (sigma : S.Sym) (args : Fin (S.arity sigma) → Pattern S Var) :
    sigma ∈ (Pattern.app sigma args).symbolSupport := by
  simp [symbolSupport]

/-- Every symbol of an argument belongs to the support of the whole application. -/
theorem argument_symbolSupport_subset [DecidableEq S.Sym]
    (sigma : S.Sym) (args : Fin (S.arity sigma) → Pattern S Var) (i : Fin (S.arity sigma)) :
    (args i).symbolSupport ⊆ (Pattern.app sigma args).symbolSupport := by
  intro tau htau
  simp only [symbolSupport, Finset.mem_insert, Finset.mem_biUnion]
  exact Or.inr ⟨i, Finset.mem_univ i, htau⟩

/-- The support of a finite conjunction is the union of the supports of its members. -/
theorem symbolSupport_conj [DecidableEq S.Sym]
    (l : List (Pattern S Var)) :
    (conj l).symbolSupport =
      l.foldr (fun p support => p.symbolSupport ∪ support) ∅ := by
  induction l with
  | nil => simp [conj, Pattern.tp, symbolSupport]
  | cons phi l ih =>
      simp [conj, Pattern.and, Pattern.nt, symbolSupport, ih,
        Finset.union_comm]

end Pattern

end MatchingLogic
