/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.GapInsertion
import LeanPool.InfinitaryLogic.Methods.WellOrdering.CofinalFiber
import LeanPool.InfinitaryLogic.Methods.ConstantAbstraction
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# The semantic gap condition (*) and the member predicate (issue #12, commit 4a)

Marker's property (*), in the frozen representation: a consistency-property member is
`S = Bφ ∪ Γ` with `Γ` finite, and for **every** `α < ω₁` there is an approximating model in
which

* the root `φ` holds (in the base `L`-structure),
* every sentence of the **finite remainder** `Γ` holds (in the controlled constant expansion
  `wc`), and
* the rational constants mentioned by `Γ` are **marked** on an `lt`-chain with `α`-margins
  (a `GapWitness` over a strictly monotone enumeration that *covers* — possibly
  over-approximates — the mentioned rationals).

Deliberately, the witness does **not** realize the entire positive diagram `Bφ` (review
acceptance check 1): a mentioned atom `d_q < d_r` is *derived* from the chain through the
marks (`StarWitness.realize_marked_atom`), and unmentioned atoms are represented only by the
chain/gap conditions.

`WOMem` is the member predicate: base containment, finite remainder, finite constant support,
universe containment (the kernel's `GenU`, whose seed already holds every constant relation
atom — in particular all of `Bφ`'s diagram), and (*) at every countable ordinal.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## Mentioned rational constants -/

/-- The rationals whose constants are mentioned by a set of expansion sentences. -/
def ratSupport (Γ : Set L[[ℕ]].Sentenceω) : Set ℚ :=
  {q | ∃ χ ∈ Γ, ratConstIdx q ∈ sentenceJConsts (L' := L) (J := ℕ) χ}

/-- Monotonicity of the mentioned-rationals set. -/
theorem ratSupport_mono {Γ Γ' : Set L[[ℕ]].Sentenceω} (h : Γ ⊆ Γ') :
    ratSupport (L := L) Γ ⊆ ratSupport Γ' := by
  rintro q ⟨χ, hχ, hmem⟩
  exact ⟨χ, h hχ, hmem⟩

/-! ## The star witness -/

/-- **The (*) witness at level `α`**: an approximating model realizing the root and the finite
remainder, with the mentioned rationals marked on an `lt`-chain with `α`-margins. The marking
enumeration may over-approximate the mentioned set (`mark_cover` is `⊆`, not `=`) — closure
rules extend it monotonically. -/
structure StarWitness (φ : L.Sentenceω) (lt : L.Relations 2) (Γ : Set L[[ℕ]].Sentenceω)
    (α : Ordinal.{0}) : Type 1 where
  /-- the approximating model -/
  M : Type
  inst : L.Structure M
  ne : Nonempty M
  /-- the constant interpretation -/
  h : ℕ → M
  /-- the root holds in the base structure -/
  base_realize : Sentenceω.Realize φ M
  /-- every remainder sentence holds in the controlled expansion -/
  rem_realize : ∀ χ ∈ Γ, @Sentenceω.Realize L[[ℕ]] χ M (wc inst h)
  /-- number of marked rationals -/
  m : ℕ
  /-- the marked rationals, in increasing order -/
  mark : Fin m → ℚ
  mark_mono : StrictMono mark
  /-- the marking covers every mentioned rational -/
  mark_cover : ratSupport (L := L) Γ ⊆ Set.range mark
  /-- the marked constants sit on a chain with `α`-margins -/
  witness : @GapWitness L M inst lt α m fun i => h (ratConstIdx (mark i))

/-- **The (*) condition**: a witness exists. -/
def StarCondition (φ : L.Sentenceω) (lt : L.Relations 2) (Γ : Set L[[ℕ]].Sentenceω)
    (α : Ordinal.{0}) : Prop :=
  Nonempty (StarWitness φ lt Γ α)

/-- Downward closure of (*) in `α` (via `GapWitness.mono`) — the consumer of the cofinal-fiber
argument. -/
theorem StarCondition.mono {φ : L.Sentenceω} {lt : L.Relations 2}
    {Γ : Set L[[ℕ]].Sentenceω} {α β : Ordinal.{0}} (hβ : β ≤ α)
    (h : StarCondition φ lt Γ α) : StarCondition φ lt Γ β := by
  obtain ⟨W⟩ := h
  exact ⟨{ W with witness := @GapWitness.mono L W.M W.inst lt α β hβ _ _ W.witness }⟩

/-- Shrinking the remainder preserves (*) (the marking still covers the smaller support). -/
theorem StarCondition.mono_subset {φ : L.Sentenceω} {lt : L.Relations 2}
    {Γ Γ' : Set L[[ℕ]].Sentenceω} (hΓ : Γ' ⊆ Γ) {α : Ordinal.{0}}
    (h : StarCondition φ lt Γ α) : StarCondition φ lt Γ' α := by
  obtain ⟨W⟩ := h
  exact ⟨{ W with
    rem_realize := fun χ hχ => W.rem_realize χ (hΓ hχ)
    mark_cover := le_trans (ratSupport_mono hΓ) W.mark_cover }⟩

/-! ## Atomic realization at the controlled expansion -/

section AtomicRealize

variable {M : Type} {base : L.Structure M} {h : ℕ → M}

/-- The sentence-context constant realizes to its `h`-value at the controlled expansion. -/
theorem realize_constTermS_wc (c : ℕ) (v : Empty ⊕ Fin 0 → M) :
    @Term.realize L[[ℕ]] M (wc base h) _ v (constTermS c) = h c := rfl

/-- A constant relation instance realizes at the controlled expansion to the base relation on
the constant values. -/
theorem realize_relInst_wc {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) :
    @Sentenceω.Realize L[[ℕ]] (relInst R g) M (wc base h) ↔
      @Structure.RelMap L M base l R (fun i => h (g i)) :=
  Iff.rfl

/-- A constant equality realizes at the controlled expansion to equality of the values. -/
theorem realize_constEq_wc (a b : ℕ) :
    @Sentenceω.Realize L[[ℕ]] (constEq a b) M (wc base h) ↔ h a = h b :=
  Iff.rfl

end AtomicRealize

/-! ## The derived diagram: marked atoms hold through the chain -/

/-- **The mentioned-diagram derivation** (review acceptance check 5): a positive diagram atom
whose rationals are both marked holds in the witness's expansion — through `RelChain` and the
marks, never by assuming the model realizes the diagram. Requires `0 < α` (at `α = 0` the
margins are vacuous); consumers instantiate (*) at any positive level. -/
theorem StarWitness.realize_marked_atom {φ : L.Sentenceω} {lt : L.Relations 2}
    {Γ : Set L[[ℕ]].Sentenceω} {α : Ordinal.{0}} (W : StarWitness φ lt Γ α)
    (hα : 0 < α) {i j : Fin W.m} (hij : i < j) :
    @Sentenceω.Realize L[[ℕ]] (ratLtAtom lt (W.mark i) (W.mark j)) W.M (wc W.inst W.h) := by
  let := W.inst
  have hrank : W.witness.rank i < W.witness.rank j :=
    lt_of_lt_of_le (lt_add_of_pos_right _ hα) (W.witness.gaps i j hij)
  have hchain := W.witness.chain
    (Ordinal.ToType.mk ⟨W.witness.rank i, W.witness.rank_lt i⟩)
    (Ordinal.ToType.mk ⟨W.witness.rank j, W.witness.rank_lt j⟩)
    (Ordinal.ToType.mk.lt_iff_lt.mpr hrank)
  rw [← W.witness.marks i, ← W.witness.marks j] at hchain
  refine (realize_relInst_wc (base := W.inst) (h := W.h) lt _).mpr ?_
  convert hchain using 1
  funext k
  induction k using Fin.cases <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]

/-! ## The member predicate -/

/-- **The consistency-property member predicate** (frozen D4): `S = Bφ ∪ Γ` with `Γ` finite —
stated as base containment plus finiteness of the remainder — together with finite constant
support of the remainder, containment in the kernel's enumeration universe (rooted at the
lifted `φ`; the universe's seed already holds every constant relation atom, hence all of
`Bφ`), and the semantic condition (*) at every countable ordinal. -/
structure WOMem (φ : L.Sentenceω) (lt : L.Relations 2) (S : Set L[[ℕ]].Sentenceω) : Prop where
  base_subset : baseDiagram φ lt ⊆ S
  rem_finite : (S \ baseDiagram φ lt).Finite
  rem_support : (⋃ χ ∈ S \ baseDiagram φ lt, sentenceJConsts (L' := L) (J := ℕ) χ).Finite
  subset_U : S ⊆ GenU (φ.mapLanguage (L.lhomWithConstants ℕ))
    (φ.mapLanguage (L.lhomWithConstants ℕ))
  star : ∀ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord →
    StarCondition φ lt (S \ baseDiagram φ lt) α

end FirstOrder.Language
