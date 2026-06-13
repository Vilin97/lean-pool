/-
Copyright (c) 2026 Martin Dvořák. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvořák
-/
import LeanPool.Chomsky.Classes.ContextFree.Basics.Definition

/-!
# Toolbox

Auxiliary lemmas about context-free derivations.
-/

namespace Chomsky

variable {T : Type} {g : CFG T}


/-- The relation `CFG.Derives` is reflexive. -/
lemma cf_deri_self {w : List (Symbol T g.nt)} :
  g.Derives w w := Relation.ReflTransGen.refl

lemma cf_deri_of_tran {v w : List (Symbol T g.nt)} (hgvw : g.Transforms v w) :
  g.Derives v w := Relation.ReflTransGen.single hgvw

/-- The relation `CFG.Derives` is transitive. -/
lemma cf_deri_of_deri_deri {u v w : List (Symbol T g.nt)}
    (hguv : g.Derives u v) (hgvw : g.Derives v w) :
  g.Derives u w := Relation.ReflTransGen.trans hguv hgvw

lemma cf_deri_of_deri_tran {u v w : List (Symbol T g.nt)}
    (hguv : g.Derives u v) (hgvw : g.Transforms v w) :
  g.Derives u w := cf_deri_of_deri_deri hguv (cf_deri_of_tran hgvw)

lemma cf_deri_of_tran_deri {u v w : List (Symbol T g.nt)}
    (hguv : g.Transforms u v) (hgvw : g.Derives v w) :
  g.Derives u w := cf_deri_of_deri_deri (cf_deri_of_tran hguv) hgvw

lemma cf_eq_or_tran_deri_of_deri {u w : List (Symbol T g.nt)} (hguw : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Transforms u v ∧ g.Derives v w  :=
Relation.ReflTransGen.cases_head hguw

lemma cf_eq_or_deri_tran_of_deri {u w : List (Symbol T g.nt)} (hguw : g.Derives u w) :
  u = w  ∨  ∃ v : List (Symbol T g.nt), g.Derives u v ∧ g.Transforms v w  :=
(Relation.ReflTransGen.cases_tail hguw).casesOn (Or.inl ∘ Eq.symm) Or.inr


lemma cf_append_deri {w₁ w₂ : List (Symbol T g.nt)}
    (pᵣ : List (Symbol T g.nt)) (hgww : g.Derives w₁ w₂) :
  g.Derives (pᵣ ++ w₁) (pᵣ ++ w₂) := by
  induction hgww with
  | refl => apply cf_deri_self
  | tail _ hgab ih =>
    apply cf_deri_of_deri_tran ih
    rcases hgab with ⟨r, r_in, v, w, bef, aft⟩
    use r, r_in, pᵣ ++ v, w
    rw [bef, aft]
    constructor <;> simp only [List.append_assoc]

lemma cf_deri_append {w₁ w₂ : List (Symbol T g.nt)}
    (pₒ : List (Symbol T g.nt)) (hgww : g.Derives w₁ w₂) :
  g.Derives (w₁ ++ pₒ) (w₂ ++ pₒ) := by
  induction hgww with
  | refl => apply cf_deri_self
  | tail _ hgab ih =>
    apply cf_deri_of_deri_tran ih
    rcases hgab with ⟨r, r_in, v, w, bef, aft⟩
    use r, r_in, v, w ++ pₒ
    rw [bef, aft]
    constructor <;> simp only [List.append_assoc]

end Chomsky
