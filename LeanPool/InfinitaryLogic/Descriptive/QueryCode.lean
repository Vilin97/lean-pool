/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.Polish
/-!
# The query-code closed embedding (issue #10, Unit 0a)

The frozen named query encoding of the López–Escobar audit (D3, v2): a fixed embedding
`queryEmbedding : RelQuery L ↪ ℕ` and the induced code map

`queryCode : StructureSpace L → (ℕ → Bool)`

sending a structure code to its bit sequence along the embedding, `false` outside the
embedding's range.  The four gates, plus the capstone:

* `queryCode_embedding` — every query is recovered at its encoded coordinate;
* `queryCode_of_notMem_range` — coordinates outside the embedding's range are `false`;
* `range_queryCode` — range membership *is* the default condition, and the range is closed
  as an intersection of clopen coordinate conditions (`isClosed_range_queryCode`);
* `queryCode_isClosedEmbedding` — the capstone, via the continuous retraction
  `decodeCode` and `Function.LeftInverse.isClosedEmbedding`.

This is the stop/go gate's first half; the analytic tree normal form (Unit 0b) builds the
cylinder tree in `(ℕ → Bool) × (ℕ → ℕ)` on top of it.
-/

namespace FirstOrder.Language

open Set

variable {L : Language.{u, v}} [Countable (Σ l, L.Relations l)]

/-- The frozen query encoding — one named `Encodable` witness, never re-synthesized. -/
@[reducible] noncomputable def queryEncodable : Encodable (RelQuery L) :=
  @Encodable.ofCountable _ inferInstance

/-- **The frozen query embedding** `RelQuery L ↪ ℕ` (audit D3, v2). -/
noncomputable def queryEmbedding : RelQuery L ↪ ℕ :=
  ⟨(queryEncodable (L := L)).encode, (queryEncodable (L := L)).encode_injective⟩

open Classical in
/-- **The query code** of a structure code: the bit at coordinate `n` is the code's value at
the query encoded by `n`, and `false` when `n` encodes no query. -/
noncomputable def queryCode (c : StructureSpace L) (n : ℕ) : Bool :=
  if h : ∃ q, queryEmbedding (L := L) q = n then c h.choose else false

/-- The continuous retraction: read the structure code back off the embedded coordinates. -/
private noncomputable def decodeCode (x : ℕ → Bool) : StructureSpace L :=
  fun q => x (queryEmbedding (L := L) q)

/-- **Gate 1**: every query is recovered at its encoded coordinate. -/
@[simp] theorem queryCode_embedding (c : StructureSpace L) (q : RelQuery L) :
    queryCode c (queryEmbedding (L := L) q) = c q := by
  have hex : ∃ q', queryEmbedding (L := L) q' = queryEmbedding (L := L) q := ⟨q, rfl⟩
  unfold queryCode
  rw [dite_eq_left hex, queryEmbedding.injective hex.choose_spec]

/-- **Gate 2**: coordinates outside the embedding's range are `false`. -/
theorem queryCode_of_notMem_range (c : StructureSpace L) {n : ℕ}
    (h : n ∉ Set.range (queryEmbedding (L := L))) : queryCode c n = false := by
  unfold queryCode
  exact dite_eq_right h

private theorem decodeCode_queryCode : Function.LeftInverse (decodeCode (L := L)) queryCode := by
  intro c
  funext q
  exact queryCode_embedding c q

theorem queryCode_injective : Function.Injective (queryCode (L := L)) :=
  decodeCode_queryCode.injective

theorem continuous_queryCode : Continuous (queryCode (L := L)) := by
  refine continuous_pi fun n => ?_
  unfold queryCode
  by_cases h : ∃ q, queryEmbedding (L := L) q = n
  · simp only [dite_eq_left h]
    exact continuous_apply _
  · simp only [dite_eq_right h]
    exact continuous_const

end FirstOrder.Language
