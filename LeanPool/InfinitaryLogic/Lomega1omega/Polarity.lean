/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Syntax
/-!
# Polarity of relation-symbol occurrences (issue #14, Unit 0 layer 1)

The signed occurrence traversal underlying Lyndon interpolation: `relationsInSigned s φ` collects
the relation symbols occurring in `φ` with sign `s`, where

* an **antecedent flips** the sign (`imp`);
* `all`, `iInf`, `iSup` **preserve** it;
* **equality is logical** — it contributes to neither sign.

`positiveRelationsIn` and `negativeRelationsIn` are the two instances.  Negation needs no clause of
its own: `φ.not = φ.imp ⊥`, so the swap laws
`positiveRelationsIn φ.not = negativeRelationsIn φ` and its dual fall out of the `imp` clause, and
the same computation gives `and`, `or`, `ex`, `⊤`, `einf`, `esup`.

This file is deliberately **syntax only** and sits in the `Lomega1omega` layer: it mentions no
occurrence machinery from `Methods/` (in particular not `relationsIn`, `baseRelationsIn`, or the
constant-expansion calculus).  The bridge `relationsIn = positive ∪ negative` and the signed twins
of the `Methods`-level calculus live in `Methods/PolarityCalculus.lean`.

## Simp discipline

Only the **generic** `relationsInSigned` equations are `@[simp]`; the `positiveRelationsIn` /
`negativeRelationsIn` forms are reducible abbreviations of those, so no derived rewrite is
installed alongside them and nothing can loop through `not`, `and`, `or`, or `ex`.
-/

namespace FirstOrder.Language

namespace BoundedFormulaω

variable {L : Language.{0, 0}} {α : Type}

/-- **The signed occurrence traversal.**  `relationsInSigned true φ` is the set of relation
symbols with a positive occurrence in `φ`, and `relationsInSigned false φ` those with a negative
occurrence: antecedents flip the sign, quantifiers and the countable connectives preserve it, and
equality contributes nothing. -/
def relationsInSigned :
    ∀ {n : ℕ}, Bool → L.BoundedFormulaω α n → Set (Σ n, L.Relations n)
  | _, _, .falsum => ∅
  | _, _, .equal _ _ => ∅
  | _, s, .rel R _ => if s then {⟨_, R⟩} else ∅
  | _, s, .imp φ ψ => relationsInSigned (!s) φ ∪ relationsInSigned s ψ
  | _, s, .all φ => relationsInSigned s φ
  | _, s, .iSup φs => ⋃ i, relationsInSigned s (φs i)
  | _, s, .iInf φs => ⋃ i, relationsInSigned s (φs i)

/-- The relation symbols occurring **positively** in `φ`. -/
abbrev positiveRelationsIn {n : ℕ} (φ : L.BoundedFormulaω α n) : Set (Σ n, L.Relations n) :=
  relationsInSigned true φ

/-- The relation symbols occurring **negatively** in `φ`. -/
abbrev negativeRelationsIn {n : ℕ} (φ : L.BoundedFormulaω α n) : Set (Σ n, L.Relations n) :=
  relationsInSigned false φ

/-! ## Constructor equations -/

@[simp] theorem relationsInSigned_falsum {n : ℕ} (s : Bool) :
    relationsInSigned s (BoundedFormulaω.falsum : L.BoundedFormulaω α n) = ∅ := rfl

@[simp] theorem relationsInSigned_bot {n : ℕ} (s : Bool) :
    relationsInSigned s (⊥ : L.BoundedFormulaω α n) = ∅ := rfl

@[simp] theorem relationsInSigned_equal {n : ℕ} (s : Bool)
    (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    relationsInSigned s (BoundedFormulaω.equal t₁ t₂) = ∅ := rfl

@[simp] theorem relationsInSigned_rel {n l : ℕ} (s : Bool) (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    relationsInSigned s (BoundedFormulaω.rel R ts) = if s then {⟨l, R⟩} else ∅ := rfl

@[simp] theorem relationsInSigned_imp {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    relationsInSigned s (φ.imp ψ) = relationsInSigned (!s) φ ∪ relationsInSigned s ψ := rfl

@[simp] theorem relationsInSigned_all {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α (n + 1)) :
    relationsInSigned s φ.all = relationsInSigned s φ := rfl

@[simp] theorem relationsInSigned_iSup {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    relationsInSigned s (BoundedFormulaω.iSup φs) = ⋃ i, relationsInSigned s (φs i) := rfl

@[simp] theorem relationsInSigned_iInf {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    relationsInSigned s (BoundedFormulaω.iInf φs) = ⋃ i, relationsInSigned s (φs i) := rfl

/-! ## Negation swaps and the derived connectives -/

/-- **Negation swaps the signs** (the acceptance gate, generic form). -/
@[simp] theorem relationsInSigned_not {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α n) :
    relationsInSigned s φ.not = relationsInSigned (!s) φ := by
  show relationsInSigned (!s) φ ∪ relationsInSigned s
    (BoundedFormulaω.falsum : L.BoundedFormulaω α n) = _
  rw [relationsInSigned_falsum, Set.union_empty]

/-- Acceptance gate: positive occurrences of `¬φ` are the negative occurrences of `φ`. -/
theorem positiveRelationsIn_not {n : ℕ} (φ : L.BoundedFormulaω α n) :
    positiveRelationsIn φ.not = negativeRelationsIn φ := relationsInSigned_not true φ

/-- Acceptance gate: negative occurrences of `¬φ` are the positive occurrences of `φ`. -/
theorem negativeRelationsIn_not {n : ℕ} (φ : L.BoundedFormulaω α n) :
    negativeRelationsIn φ.not = positiveRelationsIn φ := relationsInSigned_not false φ

@[simp] theorem relationsInSigned_top {n : ℕ} (s : Bool) :
    relationsInSigned s (⊤ : L.BoundedFormulaω α n) = ∅ := by
  show relationsInSigned s (BoundedFormulaω.imp .falsum .falsum) = _
  simp

@[simp] theorem relationsInSigned_and {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    relationsInSigned s (φ.and ψ) = relationsInSigned s φ ∪ relationsInSigned s ψ := by
  show relationsInSigned s ((φ.imp ψ.not).not) = _
  rw [relationsInSigned_not, relationsInSigned_imp, relationsInSigned_not, Bool.not_not]

@[simp] theorem relationsInSigned_or {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    relationsInSigned s (φ.or ψ) = relationsInSigned s φ ∪ relationsInSigned s ψ := by
  show relationsInSigned s (φ.not.imp ψ) = _
  rw [relationsInSigned_imp, relationsInSigned_not, Bool.not_not]

/-- **Existential quantification preserves the signs** (two flips cancel). -/
@[simp] theorem relationsInSigned_ex {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α (n + 1)) :
    relationsInSigned s φ.ex = relationsInSigned s φ := by
  show relationsInSigned s (φ.not.all.not) = _
  rw [relationsInSigned_not, relationsInSigned_all, relationsInSigned_not, Bool.not_not]

/-- An `Encodable`-indexed conjunction collects the branches' signed occurrences (the `⊤` padding
of undecodable indices contributes nothing). -/
theorem relationsInSigned_einf {ι : Type*} [Encodable ι] {n : ℕ} (s : Bool)
    (φs : ι → L.BoundedFormulaω α n) :
    relationsInSigned s (BoundedFormulaω.einf φs) = ⋃ i, relationsInSigned s (φs i) := by
  ext x
  simp only [BoundedFormulaω.einf, relationsInSigned_iInf, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    cases hd : Encodable.decode (α := ι) k with
    | none => rw [hd, relationsInSigned_top] at hk; exact absurd hk (Set.notMem_empty x)
    | some i => rw [hd] at hk; exact ⟨i, hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨Encodable.encode i, by rw [Encodable.encodek]; exact hi⟩

/-- An `Encodable`-indexed disjunction collects the branches' signed occurrences (the `⊥` padding
of undecodable indices contributes nothing). -/
theorem relationsInSigned_esup {ι : Type*} [Encodable ι] {n : ℕ} (s : Bool)
    (φs : ι → L.BoundedFormulaω α n) :
    relationsInSigned s (BoundedFormulaω.esup φs) = ⋃ i, relationsInSigned s (φs i) := by
  ext x
  simp only [BoundedFormulaω.esup, relationsInSigned_iSup, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    cases hd : Encodable.decode (α := ι) k with
    | none => rw [hd, relationsInSigned_bot] at hk; exact absurd hk (Set.notMem_empty x)
    | some i => rw [hd] at hk; exact ⟨i, hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨Encodable.encode i, by rw [Encodable.encodek]; exact hi⟩

/-! ## Countability -/

theorem relationsInSigned_countable {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α n) :
    (relationsInSigned s φ).Countable := by
  induction φ generalizing s with
  | falsum => exact Set.countable_empty
  | equal => exact Set.countable_empty
  | rel R ts =>
    rw [relationsInSigned_rel]
    cases s
    · exact Set.countable_empty
    · exact Set.countable_singleton _
  | imp φ ψ ihφ ihψ => exact (ihφ _).union (ihψ _)
  | all φ ih => exact ih _
  | iSup φs ih => exact Set.countable_iUnion fun i => ih i _
  | iInf φs ih => exact Set.countable_iUnion fun i => ih i _

end BoundedFormulaω

end FirstOrder.Language
