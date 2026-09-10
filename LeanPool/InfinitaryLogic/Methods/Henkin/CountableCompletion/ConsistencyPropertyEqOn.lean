/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.GeneratedUniverse
/-!
# The fragment-relative consistency property and Henkin completion (issue #8 tranche 2, commit 2)

`ConsistencyPropertyEqOn U`: a family of `U`-bounded sentence sets closed under the `C0`–`C4`
decompositions, the **atomic** equality/relation congruence fields specialized to constant
indices (`constEq`/`relInst` — the relational-core term model consumes nothing more; arbitrary
closed terms convert to constants at the term-model boundary via `exists_eq_constTerm`), and
the two **minimal** quantifier fields (universal instantiation + a fresh witness for a negated
universal — the negated-universal field *is* the existential witness rule; the forward
constructor-level truth lemma needs no separate existential rule).

`HenkinComplete U S`: the truth-lemma-facing completion predicate — the same closure, but
stated on `S` itself (targets are *in* `S`, not "consistently addable"). The fair enumeration
(commit 3) produces an `S* ⊇ S₀` with `HenkinComplete U S*`.

Deliberately absent (per the audit, §5–§6b): no `extension`, no `chain_closure` (Finding 1),
no general `C6` (a countable `U` cannot close under arbitrary substitution templates), and **no
finiteness** — finiteness belongs to the inseparable-pair instance (commit 4).
-/

namespace FirstOrder.Language

variable {L : Language.{0, 0}}

/-! ## The fragment-relative consistency property -/

/-- **`ConsistencyPropertyEqOn U`**: a `U`-bounded consistency family with atomic equality /
relation congruence and minimal quantifier fields. -/
structure ConsistencyPropertyEqOn (U : Set L[[ℕ]].Sentenceω) where
  /-- The family of consistent sets. -/
  sets : Set (Set L[[ℕ]].Sentenceω)
  /-- Every consistent set lives in the enumeration universe `U`. -/
  subset_U : ∀ S ∈ sets, S ⊆ U
  /-- (C0a) No consistent set contains `⊥`. -/
  C0_no_falsum : ∀ S ∈ sets, (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) ∉ S
  /-- (C0b) No consistent set contains a sentence and its negation. -/
  C0_no_contradiction : ∀ S ∈ sets, ∀ φ : L[[ℕ]].Sentenceω, ¬(φ ∈ S ∧ φ.not ∈ S)
  /-- (C1) Implication. -/
  C1_imp : ∀ S ∈ sets, ∀ φ ψ : L[[ℕ]].Sentenceω,
    φ.imp ψ ∈ S → S ∪ {φ.not} ∈ sets ∨ S ∪ {ψ} ∈ sets
  /-- (C1') Negated implication. -/
  C1_neg_imp : ∀ S ∈ sets, ∀ φ ψ : L[[ℕ]].Sentenceω,
    (φ.imp ψ).not ∈ S → S ∪ {φ} ∈ sets ∧ S ∪ {ψ.not} ∈ sets
  /-- (C2) Double negation. -/
  C2_not_not : ∀ S ∈ sets, ∀ φ : L[[ℕ]].Sentenceω, φ.not.not ∈ S → S ∪ {φ} ∈ sets
  /-- (C3) Countable conjunction. -/
  C3_iInf : ∀ S ∈ sets, ∀ φs : ℕ → L[[ℕ]].Sentenceω,
    BoundedFormulaω.iInf φs ∈ S → ∀ k, S ∪ {φs k} ∈ sets
  /-- (C3') Negated conjunction. -/
  C3_neg_iInf : ∀ S ∈ sets, ∀ φs : ℕ → L[[ℕ]].Sentenceω,
    (BoundedFormulaω.iInf φs).not ∈ S → ∃ k, S ∪ {(φs k).not} ∈ sets
  /-- (C4) Countable disjunction. -/
  C4_iSup : ∀ S ∈ sets, ∀ φs : ℕ → L[[ℕ]].Sentenceω,
    BoundedFormulaω.iSup φs ∈ S → ∃ k, S ∪ {φs k} ∈ sets
  /-- (C4') Negated disjunction. -/
  C4_neg_iSup : ∀ S ∈ sets, ∀ φs : ℕ → L[[ℕ]].Sentenceω,
    (BoundedFormulaω.iSup φs).not ∈ S → ∀ k, S ∪ {(φs k).not} ∈ sets
  /-- **Atomic equality reflexivity** (constant indices). -/
  eq_refl : ∀ S ∈ sets, ∀ c : ℕ, S ∪ {constEq c c} ∈ sets
  /-- **Atomic equality symmetry** (constant indices). -/
  eq_symm : ∀ S ∈ sets, ∀ a b : ℕ, constEq a b ∈ S → S ∪ {constEq b a} ∈ sets
  /-- **Atomic equality transitivity** (constant indices). -/
  eq_trans : ∀ S ∈ sets, ∀ a b d : ℕ,
    constEq a b ∈ S → constEq b d ∈ S → S ∪ {constEq a d} ∈ sets
  /-- **Atomic relation congruence** (one-coordinate replacement). -/
  rel_congr : ∀ S ∈ sets, ∀ (l : ℕ) (R : L.Relations l) (g : Fin l → ℕ) (i : Fin l) (b : ℕ),
    relInst R g ∈ S → constEq (g i) b ∈ S → S ∪ {relInst R (Function.update g i b)} ∈ sets
  /-- **Universal instantiation** (fresh-witness-free): a universal admits every constant
  instance. -/
  all_inst : ∀ S ∈ sets, ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1,
    φ.all ∈ S → ∀ c : ℕ, S ∪ {instConst c φ} ∈ sets
  /-- **Negated-universal witness** (the sole existential rule). -/
  neg_all_witness : ∀ S ∈ sets, ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1,
    φ.all.not ∈ S → ∃ c : ℕ, S ∪ {(instConst c φ).not} ∈ sets

/-! ## The Henkin completion predicate -/

/-- **`HenkinComplete U S`**: the truth-lemma-facing completion — the same closure as
`ConsistencyPropertyEqOn` but with every target *present in* `S`. -/
structure HenkinComplete (U : Set L[[ℕ]].Sentenceω) (S : Set L[[ℕ]].Sentenceω) : Prop where
  subset_U : S ⊆ U
  no_falsum : (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) ∉ S
  no_contradiction : ∀ φ : L[[ℕ]].Sentenceω, ¬(φ ∈ S ∧ φ.not ∈ S)
  imp : ∀ φ ψ : L[[ℕ]].Sentenceω, φ.imp ψ ∈ S → φ.not ∈ S ∨ ψ ∈ S
  neg_imp : ∀ φ ψ : L[[ℕ]].Sentenceω, (φ.imp ψ).not ∈ S → φ ∈ S ∧ ψ.not ∈ S
  not_not : ∀ φ : L[[ℕ]].Sentenceω, φ.not.not ∈ S → φ ∈ S
  iInf : ∀ φs : ℕ → L[[ℕ]].Sentenceω, BoundedFormulaω.iInf φs ∈ S → ∀ k, φs k ∈ S
  neg_iInf : ∀ φs : ℕ → L[[ℕ]].Sentenceω, (BoundedFormulaω.iInf φs).not ∈ S → ∃ k, (φs k).not ∈ S
  iSup : ∀ φs : ℕ → L[[ℕ]].Sentenceω, BoundedFormulaω.iSup φs ∈ S → ∃ k, φs k ∈ S
  neg_iSup : ∀ φs : ℕ → L[[ℕ]].Sentenceω, (BoundedFormulaω.iSup φs).not ∈ S → ∀ k, (φs k).not ∈ S
  eq_refl : ∀ c : ℕ, constEq c c ∈ S
  eq_symm : ∀ a b : ℕ, constEq a b ∈ S → constEq b a ∈ S
  eq_trans : ∀ a b d : ℕ, constEq a b ∈ S → constEq b d ∈ S → constEq a d ∈ S
  rel_congr : ∀ (l : ℕ) (R : L.Relations l) (g : Fin l → ℕ) (i : Fin l) (b : ℕ),
    relInst R g ∈ S → constEq (g i) b ∈ S → relInst R (Function.update g i b) ∈ S
  all_inst : ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1, φ.all ∈ S → ∀ c : ℕ, instConst c φ ∈ S
  neg_all_witness : ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1,
    φ.all.not ∈ S → ∃ c : ℕ, (instConst c φ).not ∈ S

end FirstOrder.Language
