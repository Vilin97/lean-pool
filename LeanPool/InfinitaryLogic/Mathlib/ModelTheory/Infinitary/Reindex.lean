/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import LeanPool.InfinitaryLogic.Mathlib.ModelTheory.Infinitary.Semantics
public import LeanPool.InfinitaryLogic.Mathlib.ModelTheory.Infinitary.IndexCoding
/-!
# Carrier transport for infinitary formulas

Infinitary formulas fix one branching carrier per formula (`Infinitary/Syntax.lean`); this
file provides the transport layer between carriers, along `IndexCoding`s:

- `BoundedFormulaInf.iInfAlong`, `iSupAlong`: an `ι`-indexed conjunction/disjunction at a
  larger carrier `κ`, padding undecodable branches with `⊤`/`⊥` — semantically neutral
  (`realize_iInfAlong`, `realize_iSupAlong`).
- `BoundedFormulaInf.reindex`: whole-formula transport, functorial (`reindex_id`,
  `reindex_trans` — proved from the generic pad laws with no decoder analysis) and
  semantics-preserving (`realize_reindex`). Equivalence codings give genuine syntactic
  transport with an exact round trip (`reindexEquiv`); reindexing fixes the image of the
  finitary embedding (`reindex_toInf`), replacing the embedding triangle of a two-inductive
  design.
- `BoundedFormulaInf.toOmega`: recoding an encodable-carrier formula into `L_{ω₁ω}`.

Karp's theorem is the motivating consumer: its `M`-indexed and `N`-indexed separating
conjunctions are `iInfAlong` at the two sum codings into the single carrier `M ⊕ N`.
-/

@[expose] public section

universe u v u' uι uκ uμ w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ} {μ : Type uμ} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- An `ι`-indexed infinitary conjunction at carrier `κ`, along a coding: decoded indices
select their conjunct, undecodable ones are padded with `⊤`. -/
def iInfAlong (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaInf κ α n) :
    L.BoundedFormulaInf κ α n :=
  .iInf (c.pad ⊤ φs)

/-- An `ι`-indexed infinitary disjunction at carrier `κ`, along a coding: decoded indices
select their disjunct, undecodable ones are padded with `⊥`. -/
def iSupAlong (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaInf κ α n) :
    L.BoundedFormulaInf κ α n :=
  .iSup (c.pad ⊥ φs)

section ReindexEqs

variable (c : IndexCoding ι κ)

end ReindexEqs

section Realize

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

/-- The `⊤`-padding of a coded conjunction is semantically neutral, generically in the
coding. -/
@[simp]
theorem realize_iInfAlong {c : IndexCoding ι κ} {φs : ι → L.BoundedFormulaInf κ α n} :
    (iInfAlong c φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [iInfAlong, realize_iInf]
  constructor
  · intro h i
    have hi := h (c.encode i)
    rwa [IndexCoding.pad_encode] at hi
  · intro h k
    rcases hd : c.decode k with _ | i
    · rw [c.pad_of_decode_none hd]
      simp
    · rw [c.pad_of_decode_some hd]
      exact h i

/-- The `⊥`-padding of a coded disjunction is semantically neutral, generically in the
coding. -/
@[simp]
theorem realize_iSupAlong {c : IndexCoding ι κ} {φs : ι → L.BoundedFormulaInf κ α n} :
    (iSupAlong c φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [iSupAlong, realize_iSup]
  constructor
  · rintro ⟨k, hk⟩
    rcases hd : c.decode k with _ | i
    · rw [c.pad_of_decode_none hd] at hk
      simp at hk
    · rw [c.pad_of_decode_some hd] at hk
      exact ⟨i, hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨c.encode i, by rwa [IndexCoding.pad_encode]⟩

end Realize

end BoundedFormulaInf

end Language

end FirstOrder
