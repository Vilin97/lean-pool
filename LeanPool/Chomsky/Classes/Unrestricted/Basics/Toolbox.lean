/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.Unrestricted.Basics.Definition

/-!
# Toolbox

Auxiliary lemmas about general-grammar derivations.
-/

namespace Chomsky

variable {T : Type} {g : Grammar T}


/-- The relation `Grammar.derives` is reflexive. -/
lemma gr_deri_self {w : List (Symbol T g.nt)} :
  g.Derives w w :=
Relation.ReflTransGen.refl

lemma gr_deri_of_tran {v w : List (Symbol T g.nt)}
    (hgvw : g.Transforms v w) :
  g.Derives v w :=
Relation.ReflTransGen.single hgvw

/-- The relation `Grammar.derives` is transitive. -/
lemma gr_deri_of_deri_deri {u v w : List (Symbol T g.nt)}
    (hguv : g.Derives u v) (hgvw : g.Derives v w) :
  g.Derives u w :=
Relation.ReflTransGen.trans hguv hgvw

lemma gr_deri_of_deri_tran {u v w : List (Symbol T g.nt)}
    (hguv : g.Derives u v) (hgvw : g.Transforms v w) :
  g.Derives u w :=
gr_deri_of_deri_deri hguv (gr_deri_of_tran hgvw)

lemma gr_deri_of_tran_deri {u v w : List (Symbol T g.nt)}
    (hguv : g.Transforms u v) (hgvw : g.Derives v w) :
  g.Derives u w :=
gr_deri_of_deri_deri (gr_deri_of_tran hguv) hgvw

lemma gr_eq_or_tran_deri_of_deri {u w : List (Symbol T g.nt)} (hguw : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Transforms u v ∧ g.Derives v w  :=
Relation.ReflTransGen.cases_head hguw

lemma gr_eq_or_deri_tran_of_deri {u w : List (Symbol T g.nt)} (hguw : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Derives u v ∧ g.Transforms v w  :=
(Relation.ReflTransGen.cases_tail hguw).casesOn (Or.inl ∘ Eq.symm) Or.inr


lemma gr_append_deri {w₁ w₂ : List (Symbol T g.nt)}
    (pᵣ : List (Symbol T g.nt)) (hgww : g.Derives w₁ w₂) :
  g.Derives (pᵣ ++ w₁) (pᵣ ++ w₂) :=
by
  induction hgww with
  | refl => apply gr_deri_self
  | tail _ hgxy ih =>
    apply gr_deri_of_deri_tran ih
    rcases hgxy with ⟨r, rin, u, v, bef, aft⟩
    use r, rin, pᵣ ++ u, v
    rw [bef, aft]
    constructor <;> simp only [List.append_assoc]

lemma gr_deri_append {w₁ w₂ : List (Symbol T g.nt)}
    (pₒ : List (Symbol T g.nt)) (hgww : g.Derives w₁ w₂) :
  g.Derives (w₁ ++ pₒ) (w₂ ++ pₒ) :=
by
  induction hgww with
  | refl => apply gr_deri_self
  | tail _ hgxy ih =>
    apply gr_deri_of_deri_tran ih
    rcases hgxy with ⟨r, rin, u, v, bef, aft⟩
    use r, rin, u, v ++ pₒ
    rw [bef, aft]
    constructor <;> simp only [List.append_assoc]


/-- Extract the terminal carried by a symbol, if any. -/
def asTerminal {N : Type} : Symbol T N → Option T
  | Symbol.terminal t => some t
  | Symbol.nonterminal _ => none

/-- The list of terminals occurring in a grammar's rules. -/
def allUsedTerminals (g : Grammar T) : List T :=
  (g.rules.map Grule.output).flatten.filterMap asTerminal

end Chomsky
