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

private theorem continuous_decodeCode : Continuous (decodeCode (L := L)) := by
  show Continuous fun (x : ℕ → Bool) (q : RelQueryOn L ℕ) => x (queryEmbedding (L := L) q)
  exact continuous_pi fun q => continuous_apply _

/-- **Gate 3 (range characterization)**: the range of `queryCode` is exactly the default
condition — `false` at every coordinate outside the embedding's range. -/
private theorem range_queryCode :
    Set.range (queryCode (L := L)) =
      {x | ∀ n ∉ Set.range (queryEmbedding (L := L)), x n = false} := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩ n hn
    exact queryCode_of_notMem_range c hn
  · intro hx
    refine ⟨decodeCode x, funext fun n => ?_⟩
    unfold queryCode
    by_cases h : ∃ q, queryEmbedding (L := L) q = n
    · rw [dite_eq_left h]
      exact congrArg x h.choose_spec
    · rw [dite_eq_right h]
      exact (hx n h).symm

/-- **Gate 4**: the range is closed — an intersection of clopen coordinate conditions. -/
private theorem isClosed_range_queryCode : IsClosed (Set.range (queryCode (L := L))) := by
  rw [range_queryCode]
  have heq : {x : ℕ → Bool | ∀ n ∉ Set.range (queryEmbedding (L := L)), x n = false}
      = ⋂ n, {x : ℕ → Bool | n ∈ Set.range (queryEmbedding (L := L)) ∨ x n = false} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hx n
      by_cases h : n ∈ Set.range (queryEmbedding (L := L))
      · exact Or.inl h
      · exact Or.inr (hx n h)
    · intro hx n hn
      exact (hx n).resolve_left hn
  rw [heq]
  refine isClosed_iInter fun n => ?_
  by_cases h : n ∈ Set.range (queryEmbedding (L := L))
  · have : {x : ℕ → Bool | n ∈ Set.range (queryEmbedding (L := L)) ∨ x n = false}
        = Set.univ := by
      ext x; simp [h]
    rw [this]; exact isClosed_univ
  · have : {x : ℕ → Bool | n ∈ Set.range (queryEmbedding (L := L)) ∨ x n = false}
        = {x : ℕ → Bool | x n = false} := by
      ext x; simp [h]
    rw [this]
    exact isClosed_eq (continuous_apply n) continuous_const

/-- **The capstone**: `queryCode` is a closed embedding. -/
private theorem queryCode_isClosedEmbedding :
    Topology.IsClosedEmbedding (queryCode (L := L)) :=
  decodeCode_queryCode.isClosedEmbedding continuous_decodeCode continuous_queryCode

end FirstOrder.Language
