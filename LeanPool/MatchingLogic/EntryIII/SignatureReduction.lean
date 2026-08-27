/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Semantic finite-signature reduction for entry point (iii).

The source proof first restricts a finite list of patterns to the finite set of
symbols it uses, obtains a pointed model there, and extends that model with
empty interpretations for every other ambient symbol.  This file verifies that
bridge for the raw syntax and semantics in the base development.
-/
import LeanPool.MatchingLogic.EntryIII.Countertheory
import LeanPool.MatchingLogic.EntryIII.SignatureRestriction

/-!
# MatchingLogic.EntryIII.SignatureReduction
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

namespace Pattern

/-- The union of the symbols appearing in a finite list of patterns. -/
def symbolSupportList [DecidableEq S.Sym] (l : List (Pattern S Var)) : Finset S.Sym :=
  l.foldr (fun p support => p.symbolSupport ∪ support) ∅

omit [DecidableEq Var] in
/-- Every pattern in a finite list is supported by that list's support. -/
theorem symbolSupport_subset_symbolSupportList [DecidableEq S.Sym]
    (l : List (Pattern S Var)) {p : Pattern S Var} (hp : p ∈ l) :
    p.symbolSupport ⊆ Pattern.symbolSupportList l := by
  induction l with
  | nil => simp at hp
  | cons q l ih =>
      simp only [symbolSupportList, List.foldr]
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih hp) Finset.subset_union_right

/-- Restrict every member of a supported finite list to the finite sub-signature. -/
def restrictList [DecidableEq S.Sym] (F : Finset S.Sym) (l : List (Pattern S Var))
    (h : ∀ p ∈ l, p.symbolSupport ⊆ F) : List (Pattern (S.restrict F) Var) :=
  match l with
  | [] => []
  | p :: l =>
      p.restrictSignature F (h p (by simp)) ::
        restrictList F l (fun q hq => h q (by simp [hq]))

omit [DecidableEq Var] in
/-- Lifting a restricted finite list recovers the original list. -/
theorem liftSignature_restrictList [DecidableEq S.Sym] (F : Finset S.Sym)
    (l : List (Pattern S Var)) (h : ∀ p ∈ l, p.symbolSupport ⊆ F) :
    (restrictList F l h).map (Pattern.liftSignature F) = l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      simp only [restrictList, List.map_cons]
      rw [Pattern.lift_restrictSignature]
      simpa using ih (fun q hq => h q (by simp [hq]))

omit [DecidableEq Var] in
/-- Lifting distributes through the fixed bracketing of a finite conjunction. -/
theorem liftSignature_conj [DecidableEq S.Sym] (F : Finset S.Sym)
    (l : List (Pattern (S.restrict F) Var)) :
    (conj l).liftSignature F = conj (l.map (Pattern.liftSignature F)) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [conj, Pattern.and, Pattern.nt, Pattern.liftSignature, ih]

end Pattern

namespace Model

/-- Extend a model of the finite sub-signature by interpreting every symbol
outside it as the empty set. -/
abbrev extendSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (M : Model (S.restrict F)) : Model S where
  carrier := M.carrier
  nonempty := M.nonempty
  interp sigma args := if h : sigma ∈ F then M.interp ⟨sigma, h⟩ args else ∅

/-- On a retained symbol, pointwise application is unchanged by extension. -/
theorem app_extendSignature [DecidableEq S.Sym] (F : Finset S.Sym)
    (M : Model (S.restrict F)) (sigma : (S.restrict F).Sym)
    (A : Fin (S.arity sigma.1) → Set M.carrier) :
    (M.extendSignature F).app sigma.1 A = M.app sigma A := by
  rcases sigma with ⟨sigma, hmem⟩
  ext u
  simp only [Model.app, extendSignature]
  simp only [Set.mem_ofPred_eq, dite_eq_left hmem]
  change
    (∃ a : Fin (S.arity sigma) → M.carrier,
      (∀ i, a i ∈ A i) ∧ u ∈ M.interp ⟨sigma, hmem⟩ a) ↔
      (∃ a : Fin (S.arity sigma) → M.carrier,
        (∀ i, a i ∈ A i) ∧ u ∈ M.interp ⟨sigma, hmem⟩ a)
  rfl

/-- Denotation is preserved when a restricted pattern is lifted and its model
is extended by empty interpretations outside the restricted signature. -/
theorem denote_extendSignature_liftSignature [DecidableEq S.Sym]
    (F : Finset S.Sym) (M : Model (S.restrict F)) (rho : Var → M.carrier)
    (p : Pattern (S.restrict F) Var) :
    (M.extendSignature F).denote rho (p.liftSignature F) = M.denote rho p := by
  induction p generalizing rho with
  | var x => rfl
  | bot => rfl
  | app sigma args ih =>
      change (M.extendSignature F).app sigma.1
          (fun i => (M.extendSignature F).denote rho ((args i).liftSignature F)) =
        M.app sigma (fun i => M.denote rho (args i))
      rw [M.app_extendSignature F sigma]
      congr 1
      funext i
      exact ih i rho
  | imp phi psi ihphi ihpsi =>
      change ((M.extendSignature F).denote rho (phi.liftSignature F))ᶜ ∪
          (M.extendSignature F).denote rho (psi.liftSignature F) =
        (M.denote rho phi)ᶜ ∪ M.denote rho psi
      rw [ihphi rho, ihpsi rho]
  | ex x phi ih =>
      change (⋃ a : M.carrier,
        (M.extendSignature F).denote (Function.update rho x a) (phi.liftSignature F)) =
          ⋃ a : M.carrier, M.denote (Function.update rho x a) phi
      apply Set.iUnion_congr
      intro a
      exact ih (Function.update rho x a)

/-- The ambient denotation of a supported pattern equals the denotation of its
restriction in the finite sub-signature. -/
theorem denote_extendSignature_restrictSignature [DecidableEq S.Sym]
    (F : Finset S.Sym) (M : Model (S.restrict F)) (rho : Var → M.carrier)
    (p : Pattern S Var) (h : p.symbolSupport ⊆ F) :
    (M.extendSignature F).denote rho p = M.denote rho (p.restrictSignature F h) := by
  have hp : (p.restrictSignature F h).liftSignature F = p :=
    Pattern.lift_restrictSignature F p h
  calc
    (M.extendSignature F).denote rho p =
        (M.extendSignature F).denote rho ((p.restrictSignature F h).liftSignature F) :=
      congrArg ((M.extendSignature F).denote rho) hp.symm
    _ = M.denote rho (p.restrictSignature F h) :=
      M.denote_extendSignature_liftSignature F rho (p.restrictSignature F h)

/-- Conjunctive denotation of a finite list is unchanged by lifting and model
extension. -/
theorem denoteSet_extendSignature_liftSignature_list [DecidableEq S.Sym]
    (F : Finset S.Sym) (M : Model (S.restrict F)) (rho : Var → M.carrier)
    (l : List (Pattern (S.restrict F) Var)) :
    (M.extendSignature F).denoteSet rho
        {delta | delta ∈ l.map (Pattern.liftSignature F)} =
      M.denoteSet rho {delta | delta ∈ l} := by
  ext u
  simp only [Model.denoteSet, Set.mem_iInter]
  change
    (∀ delta : Pattern S Var, delta ∈ l.map (Pattern.liftSignature F) →
      u ∈ (M.extendSignature F).denote rho delta) ↔
      (∀ delta : Pattern (S.restrict F) Var, delta ∈ l → u ∈ M.denote rho delta)
  constructor
  · intro h p hp
    have hmap : p.liftSignature F ∈ l.map (Pattern.liftSignature F) :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    have hu := h (p.liftSignature F) hmap
    rwa [M.denote_extendSignature_liftSignature] at hu
  · intro h p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    rw [M.denote_extendSignature_liftSignature]
    exact h q hq

end Model

/-- Restricting a locally consistent supported finite list preserves local
consistency: a contradiction over the restricted signature would lift to one
over the original list. -/
theorem restrictList_locConsistent [DecidableEq S.Sym] (F : Finset S.Sym)
    (l : List (Pattern S Var)) (hsupport : ∀ p ∈ l, p.symbolSupport ⊆ F)
    (hconsistent : LocConsistent {delta | delta ∈ l}) :
    LocConsistent {delta | delta ∈ Pattern.restrictList F l hsupport} := by
  intro hbad
  apply hconsistent
  rcases hbad with ⟨k, hk, hp⟩
  refine ⟨k.map (Pattern.liftSignature F), ?_, ?_⟩
  · intro delta hdelta
    rcases List.mem_map.mp hdelta with ⟨q, hq, rfl⟩
    have hq' := hk q hq
    change q ∈ Pattern.restrictList F l hsupport at hq'
    have hlift : q.liftSignature F ∈ l := by
      have hmem : q.liftSignature F ∈
          (Pattern.restrictList F l hsupport).map (Pattern.liftSignature F) :=
        List.mem_map.mpr ⟨q, hq', rfl⟩
      rwa [Pattern.liftSignature_restrictList] at hmem
    exact hlift
  · have hp' := hp.liftSignature F
    simpa [Pattern.liftSignature, Pattern.liftSignature_conj] using hp'

/-- Finite pointed-model existence for every finite sub-signature implies
finite pointed-model existence for the ambient signature. -/
theorem finiteLocalModelExistence_of_restricted
    (hmodel : ∀ F : Finset S.Sym, FiniteLocalModelExistence (S.restrict F) Nat) :
    FiniteLocalModelExistence S Nat := by
  classical
  intro l hconsistent
  let F : Finset S.Sym := Pattern.symbolSupportList l
  have hsupport : ∀ p ∈ l, p.symbolSupport ⊆ F := by
    intro p hp
    exact Pattern.symbolSupport_subset_symbolSupportList l hp
  let restricted : List (Pattern (S.restrict F) Nat) :=
    Pattern.restrictList F l hsupport
  have hrestrictedConsistent : LocConsistent {delta | delta ∈ restricted} := by
    exact restrictList_locConsistent F l hsupport hconsistent
  obtain ⟨M, rho, u, hu⟩ := hmodel F restricted hrestrictedConsistent
  refine ⟨M.extendSignature F, rho, u, ?_⟩
  have huLifted : u ∈ (M.extendSignature F).denoteSet rho
      {delta | delta ∈ restricted.map (Pattern.liftSignature F)} := by
    rw [M.denoteSet_extendSignature_liftSignature_list]
    exact hu
  have hlift : restricted.map (Pattern.liftSignature F) = l := by
    exact Pattern.liftSignature_restrictList F l hsupport
  rwa [hlift] at huLifted

end MatchingLogic
