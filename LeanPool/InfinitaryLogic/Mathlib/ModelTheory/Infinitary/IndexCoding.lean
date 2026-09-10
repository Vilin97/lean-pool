/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Index codings

An `IndexCoding ι κ` is an injection `encode : ι → κ` together with a decoder that is a left
inverse on encoded values (mirroring `Encodable`, the codomain-`ℕ` special case). Codings are
how an `ι`-indexed infinitary connective is expressed at a larger carrier `κ`, and how
infinitary formulas are transported between carriers (`Infinitary/Reindex.lean`).

## Main definitions

- `IndexCoding.id`, `IndexCoding.trans`: identity and forward composition, with `id_trans`,
  `trans_id`, `trans_assoc`.
- `IndexCoding.sumInl`, `IndexCoding.sumInr`: the canonical codings into a sum.
- `IndexCoding.ofEncodable` / `ofEncodableWith`: the coding of an encodable type into `ℕ`,
  by instance search or from an explicitly given `Encodable` value; no choice is involved.
- `IndexCoding.ofEquiv`: the coding induced by an equivalence; its `decode` is total.
- `IndexCoding.pad`: total extension of an `ι`-indexed family to a `κ`-indexed one, sending
  undecodable indices to a default. The laws `pad_trans` and `comp_pad` centralize all
  decoder analysis; consumers chain and commute pads through them.
- `IndexCoding.toEmbedding`: the underlying embedding (`decode_encode` forces injectivity).
-/

@[expose] public section

universe uι uκ uμ uν

namespace FirstOrder

variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} {ν : Type uν}

/-- A coding of the index type `ι` into `κ`: an injection `encode` together with a decoder
that is a left inverse on encoded values. Values outside the range of `encode` may decode to
`none` or to duplicate source branches; the padding semantics only ever relies on
`decode_encode`. -/
structure IndexCoding (ι : Type uι) (κ : Type uκ) where
  /-- The injection. -/
  encode : ι → κ
  /-- The decoder, a left inverse on encoded values. -/
  decode : κ → Option ι
  /-- Decoding recovers every encoded index. -/
  decode_encode : ∀ i, decode (encode i) = some i

namespace IndexCoding

/-- Two codings with the same `encode` and `decode` are equal; the coherence proof is
irrelevant. -/
@[ext]
theorem ext {c₁ c₂ : IndexCoding ι κ} (he : c₁.encode = c₂.encode)
    (hd : c₁.decode = c₂.decode) : c₁ = c₂ := by
  cases c₁
  cases c₂
  cases he
  cases hd
  rfl

/-- `encode` is injective: `decode_encode` already provides a retraction. -/
theorem encode_injective (c : IndexCoding ι κ) : Function.Injective c.encode := fun i j h ↦
  Option.some_injective ι (by rw [← c.decode_encode i, h, c.decode_encode])

/-- The identity coding. -/
protected def id (ι : Type uι) : IndexCoding ι ι :=
  ⟨fun i ↦ i, some, fun _ ↦ rfl⟩

/-- Forward composition of codings, in the `Equiv.trans` argument order: first `c₁ : ι → κ`,
then `c₂ : κ → μ`. -/
def trans (c₁ : IndexCoding ι κ) (c₂ : IndexCoding κ μ) : IndexCoding ι μ where
  encode := c₂.encode ∘ c₁.encode
  decode m := (c₂.decode m).bind c₁.decode
  decode_encode i := by simp [Function.comp, c₂.decode_encode, c₁.decode_encode]

/-- The canonical coding of the left summand into a sum. -/
def sumInl (ι : Type uι) (κ : Type uκ) : IndexCoding ι (ι ⊕ κ) :=
  ⟨Sum.inl, Sum.getLeft?, fun _ ↦ rfl⟩

/-- The canonical coding of the right summand into a sum. -/
def sumInr (ι : Type uι) (κ : Type uκ) : IndexCoding κ (ι ⊕ κ) :=
  ⟨Sum.inr, Sum.getRight?, fun _ ↦ rfl⟩

/-- Explicit-data variant of `ofEncodable`: build the coding from a *given* encoding value
rather than by instance search. Code that stores a particular `Encodable` as data (e.g. a
coded-family presentation that must not consult ambient instances) uses this, so the compiler
enforces that the resulting syntax depends on the stored encoding. -/
def ofEncodableWith (e : Encodable ι) : IndexCoding ι ℕ :=
  letI := e
  ⟨Encodable.encode, Encodable.decode, Encodable.encodek⟩

/-- Total extension of a family along a coding: decoded indices select a branch, undecodable
ones get the default. -/
def pad {β : Sort*} (c : IndexCoding ι κ) (default : β) (f : ι → β) : κ → β :=
  fun k ↦ (c.decode k).elim default f

@[simp]
theorem pad_encode {β : Sort*} (c : IndexCoding ι κ) (default : β) (f : ι → β) (i : ι) :
    c.pad default f (c.encode i) = f i := by
  rw [pad, c.decode_encode]; rfl

theorem pad_of_decode_none {β : Sort*} (c : IndexCoding ι κ) {default : β} {f : ι → β} {k : κ}
    (h : c.decode k = none) : c.pad default f k = default := by
  rw [pad, h]; rfl

theorem pad_of_decode_some {β : Sort*} (c : IndexCoding ι κ) {default : β} {f : ι → β} {k : κ}
    {i : ι} (h : c.decode k = some i) : c.pad default f k = f i := by
  rw [pad, h]; rfl

end IndexCoding

end FirstOrder
