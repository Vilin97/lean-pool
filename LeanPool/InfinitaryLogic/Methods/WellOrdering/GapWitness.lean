/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.Constants
import Mathlib.SetTheory.Ordinal.Enum
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Base diagram, preservation predicate, and the gap witness (issue #12, commit 2)

The three frozen foundations of the well-ordering construction (audit v2, D1/D2/D4/D6):

* `baseDiagram φ lt` — the countable base `Bφ = {φ} ∪ {d_q < d_r : q < r}` that literally
  belongs to every consistency-property member (D4);
* `RelChain` / `RelPreserving` — the raw positive forms: an ordinal-indexed chain strictly
  increasing for the interpreted relation, and a relation-preserving map from `ℚ` (D1/D2 —
  no injectivity, no order-embedding packaging);
* `GapWitness` — the rank-based representation frozen from the audit-§8 probe: a chain of
  length `γ`, marked ranks for the mentioned tuple, and the three α-margins (initial,
  internal, terminal) as explicit fields.

**One addition to the §8 structure** (discovered by the insertion engine, kept as an explicit
field per review): `lt_gamma : α < γ`, the *bottom margin*.  For `m > 0` it is derivable
(`α ≤ rank 0 < γ`), but for `m = 0` the other fields are vacuous and the witness would carry
no information about the chain's length — insertion into empty support (the fourth case of
the uniform insertion lemma) needs the chain to be long enough to contain rank `α`.

`GapWitness.mono` is the downward closure in `α` consumed by the `ω₁` fiber argument (C4).
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## The base diagram -/

/-- The positive order atom `d_q < d_r` (over the rational constants of the coding layer). -/
def ratLtAtom (lt : L.Relations 2) (q r : ℚ) : L[[ℕ]].Sentenceω :=
  relInst lt ![ratConstIdx q, ratConstIdx r]

/-- **The base diagram** `Bφ = {φ} ∪ {d_q < d_r : q < r}`: the lifted sentence together with
the full positive rational diagram.  Per the frozen member shape (D4), `Bφ` literally belongs
to every consistency-property member. -/
def baseDiagram (φ : L.Sentenceω) (lt : L.Relations 2) : Set L[[ℕ]].Sentenceω :=
  insert (φ.mapLanguage (L.lhomWithConstants ℕ)) {χ | ∃ q r : ℚ, q < r ∧ χ = ratLtAtom lt q r}

theorem mapLanguage_mem_baseDiagram (φ : L.Sentenceω) (lt : L.Relations 2) :
    φ.mapLanguage (L.lhomWithConstants ℕ) ∈ baseDiagram φ lt :=
  Set.mem_insert _ _

theorem ratLtAtom_mem_baseDiagram (φ : L.Sentenceω) (lt : L.Relations 2) {q r : ℚ}
    (h : q < r) : ratLtAtom lt q r ∈ baseDiagram φ lt :=
  Set.mem_insert_of_mem _ ⟨q, r, h, rfl⟩



/-! ## The raw positive predicates -/

variable {M : Type} [L.Structure M]

/-- An ordinal-indexed chain in `M`, strictly increasing for the interpreted relation `lt` —
the raw positive form (no injectivity packaged). -/
def RelChain (lt : L.Relations 2) (γ : Ordinal.{0}) (w : γ.ToType → M) : Prop :=
  ∀ x y : γ.ToType, x < y → RelMap lt ![w x, w y]

/-- A relation-preserving map from `ℚ` — the raw positive conclusion form (D2). -/
def RelPreserving (lt : L.Relations 2) (f : ℚ → M) : Prop :=
  ∀ q r : ℚ, q < r → RelMap lt ![f q, f r]

/-- **The hypothesis form (D1)**: for every countable ordinal, a model of `φ` with an
`α`-length `lt`-chain. -/
def HasWellOrderedChains (φ : L.Sentenceω) (lt : L.Relations 2) : Prop :=
  ∀ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord →
    ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M),
      Sentenceω.Realize φ M ∧ ∃ w : α.ToType → M, RelChain lt α w

/-! ## The gap witness (frozen, audit §8 + the bottom margin) -/

/-- **The gap witness** (rank form): a chain of length `γ` containing the marked tuple `b` at
ranks that carry an initial margin `≥ α`, pairwise internal gaps `≥ α`, a terminal margin
`≥ α`, and the bottom margin `α < γ` (explicit even where derivable — see the module
docstring). -/
structure GapWitness (lt : L.Relations 2) (α : Ordinal.{0}) {m : ℕ} (b : Fin m → M) :
    Type 1 where
  /-- the chain length -/
  γ : Ordinal.{0}
  /-- the chain -/
  w : γ.ToType → M
  chain : RelChain lt γ w
  /-- the marked ranks of the tuple -/
  rank : Fin m → Ordinal.{0}
  rank_lt : ∀ i, rank i < γ
  /-- initial margin -/
  initial : ∀ i, α ≤ rank i
  /-- internal gaps -/
  gaps : ∀ i j : Fin m, i < j → rank i + α ≤ rank j
  /-- terminal margin -/
  terminal : ∀ i, rank i + α ≤ γ
  /-- bottom margin: the chain is long enough to contain rank `α` (data for `m = 0`) -/
  lt_gamma : α < γ
  /-- the tuple is the chain at the marked ranks -/
  marks : ∀ i, b i = w (Ordinal.ToType.mk ⟨rank i, rank_lt i⟩)

/-- **Downward closure in `α`** — the monotonicity consumed by the `ω₁` fiber argument: a
witness at `α` is a witness at every `β ≤ α`. -/
def GapWitness.mono {lt : L.Relations 2} {α β : Ordinal.{0}} (hβ : β ≤ α) {m : ℕ}
    {b : Fin m → M} (W : GapWitness lt α b) : GapWitness lt β b where
  γ := W.γ
  w := W.w
  chain := W.chain
  rank := W.rank
  rank_lt := W.rank_lt
  initial := fun i => hβ.trans (W.initial i)
  gaps := fun i j hij => le_trans (add_le_add_right hβ _) (W.gaps i j hij)
  terminal := fun i => le_trans (add_le_add_right hβ _) (W.terminal i)
  lt_gamma := lt_of_le_of_lt hβ W.lt_gamma
  marks := W.marks

end FirstOrder.Language
