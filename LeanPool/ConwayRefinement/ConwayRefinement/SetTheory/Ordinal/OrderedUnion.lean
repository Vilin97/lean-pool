/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Order type of a separated indexed union

This module formalizes the order-theoretic estimate in Berarducci, Lemma 4.7. A family indexed by
a limit ordinal has union of order type at least `ρ * l` when every nonempty final segment of
each member has order type at least `ρ` and every later member contains an element strictly above
each earlier member. The product is ordinary ordinal multiplication, with the within-block order
in the left factor and the index order in the right factor.

The proof uses the successor indices and replaces each corresponding member by its final segment
strictly above all earlier members. Strictness makes the resulting blocks disjoint and ordered even
when the original family members overlap.

-/

universe u

open Function Order Ordinal

public noncomputable section

namespace Ordinal

/-- The successor positions in the canonical well-order of a limit ordinal have the same order
type as the ordinal. This is Berarducci, Lemma 4.6. -/
theorem typeLT_range_succ_toType (l : Ordinal.{u}) (hl : IsSuccLimit l) :
    typeLT (Set.range (Order.succ : l.ToType → l.ToType)) = l := by
  have hpre : IsSuccPrelimit (typeLT l.ToType) := by
    rw [type_toType]
    exact hl.isSuccPrelimit
  letI : NoMaxOrder l.ToType := isSuccPrelimit_type_lt_iff.mp hpre
  let f : l.ToType → Set.range (Order.succ : l.ToType → l.ToType) :=
    fun i ↦ ⟨Order.succ i, ⟨i, rfl⟩⟩
  have hf : StrictMono f := fun _ _ hij ↦ Order.succ_strictMono hij
  have hsurjective : Surjective f := by
    rintro ⟨_, i, rfl⟩
    exact ⟨i, rfl⟩
  let e : l.ToType ≃o Set.range (Order.succ : l.ToType → l.ToType) :=
    hf.orderIsoOfSurjective f hsurjective
  calc
    typeLT (Set.range (Order.succ : l.ToType → l.ToType)) = typeLT l.ToType :=
      e.symm.toRelIsoLT.ordinalType_congr
    _ = l := type_toType l

end Ordinal

namespace Set.IsPWO

private abbrev successorRange (l : Ordinal.{u}) : Set l.ToType :=
  Set.range Order.succ

private theorem successorRange_orderType (l : Ordinal.{u}) (hl : IsSuccLimit l) :
    typeLT (successorRange l) = l := by
  simpa only [successorRange] using Ordinal.typeLT_range_succ_toType l hl

private def separatedBlock {α ι : Type u} [LinearOrder α] [LinearOrder ι]
    (B : ι → Set α) (i : ι) : Set α :=
  {x | x ∈ B i ∧ ∀ j < i, ∀ y ∈ B j, y < x}

/-- Let `l` be a limit ordinal and let `B` be an `l`-indexed family of well-ordered subsets. If
every later member contains an element strictly above every element of each earlier member, every
nonempty final segment of every member has order type at least `ρ`, and the union is well ordered,
then its order type is at least the ordinary ordinal product `ρ * l`. This is Berarducci,
Lemma 4.7. -/
theorem mul_le_orderType_iUnion_of_isSuccLimit
    {α : Type u} [LinearOrder α] {l ρ : Ordinal.{u}}
    (hl : IsSuccLimit l) (B : l.ToType → Set α)
    (hB : ∀ i, (B i).IsPWO)
    (hseparated : ∀ {i j}, i < j → ∃ y ∈ B j, ∀ x ∈ B i, x < y)
    (hfinal : ∀ (i : l.ToType) (C : Set α)
      (hC : IsRelUpperSet C (· ∈ B i)), C.Nonempty →
        ρ ≤ ((hB i).mono fun _ hx ↦ (hC hx).1).orderType)
    (hUnion : (⋃ i, B i).IsPWO) :
    ρ * l ≤ hUnion.orderType := by
  have hpre : IsSuccPrelimit (typeLT l.ToType) := by
    rw [type_toType]
    exact hl.isSuccPrelimit
  letI : NoMaxOrder l.ToType := isSuccPrelimit_type_lt_iff.mp hpre
  let predecessor : successorRange l → l.ToType :=
    fun i ↦ Classical.choose i.2
  have successor_predecessor (i : successorRange l) :
      Order.succ (predecessor i) = i.1 :=
    Classical.choose_spec i.2
  have predecessor_lt (i : successorRange l) : predecessor i < i.1 := by
    rw [← successor_predecessor i]
    exact Order.lt_succ _
  have block_upper (i : successorRange l) :
      IsRelUpperSet (separatedBlock B i.1) (· ∈ B i.1) := by
    intro x hx
    refine ⟨hx.1, fun y hxy hy ↦ ⟨hy, ?_⟩⟩
    intro j hji z hz
    exact (hx.2 j hji z hz).trans_le hxy
  have block_nonempty (i : successorRange l) :
      (separatedBlock B i.1).Nonempty := by
    obtain ⟨x, hx, hxabove⟩ := hseparated (predecessor_lt i)
    refine ⟨x, hx, ?_⟩
    intro j hji y hy
    have hjle : j ≤ predecessor i := by
      rw [← successor_predecessor i] at hji
      exact Order.le_of_lt_succ hji
    rcases hjle.eq_or_lt with rfl | hjlt
    · exact hxabove y hy
    · obtain ⟨z, hz, hzabove⟩ := hseparated hjlt
      exact (hzabove y hy).trans (hxabove z hz)
  have block_isPWO (i : successorRange l) :
      (separatedBlock B i.1).IsPWO :=
    (hB i.1).mono fun _ hx ↦ hx.1
  have block_embedding_exists (i : successorRange l) :
      Nonempty (ρ.ToType ↪o separatedBlock B i.1) := by
    let hblock := block_isPWO i
    letI : WellFoundedLT (separatedBlock B i.1) := ⟨hblock.isWF⟩
    have hle : typeLT ρ.ToType ≤ typeLT (separatedBlock B i.1) := by
      calc
        typeLT ρ.ToType = ρ := type_toType ρ
        _ ≤ hblock.orderType := hfinal i.1 _ (block_upper i) (block_nonempty i)
        _ = typeLT (separatedBlock B i.1) :=
          hblock.orderType_eq_typeLT_of_orderIso (OrderIso.refl _)
    obtain ⟨e⟩ := Ordinal.type_le_iff'.mp hle
    exact ⟨e.orderEmbeddingOfLTEmbedding⟩
  let blockEmbedding (i : successorRange l) :
      ρ.ToType ↪o separatedBlock B i.1 :=
    Classical.choice (block_embedding_exists i)
  have block_lt_block {i j : successorRange l} (hij : i < j)
      {x y : α} (hx : x ∈ separatedBlock B i.1)
      (hy : y ∈ separatedBlock B j.1) : x < y :=
    hy.2 i.1 hij x hx.1
  let unionEmbedding : successorRange l ×ₗ ρ.ToType ↪o (⋃ i, B i) :=
    OrderEmbedding.ofStrictMono
      (fun p ↦
        let q := ofLex p
        let x := blockEmbedding q.1 q.2
        ⟨x.1, Set.mem_iUnion.mpr ⟨q.1.1, x.2.1⟩⟩)
      (by
        intro p q hpq
        rw [Prod.Lex.lt_iff] at hpq
        rcases hpq with hpq | ⟨hpq, hpq'⟩
        · exact block_lt_block hpq (blockEmbedding (ofLex p).1 (ofLex p).2).2
            (blockEmbedding (ofLex q).1 (ofLex q).2).2
        · change ((blockEmbedding (ofLex p).1 (ofLex p).2).1 : α) <
              (blockEmbedding (ofLex q).1 (ofLex q).2).1
          rw [hpq]
          exact (blockEmbedding (ofLex q).1).strictMono hpq')
  have hdomain : typeLT (successorRange l ×ₗ ρ.ToType) = ρ * l := by
    change type (Prod.Lex (· < · : successorRange l → successorRange l → Prop)
      (· < · : ρ.ToType → ρ.ToType → Prop)) = ρ * l
    rw [type_prod_lex, type_toType, successorRange_orderType l hl]
  letI : WellFoundedLT (⋃ i, B i) := ⟨hUnion.isWF⟩
  calc
    ρ * l = typeLT (successorRange l ×ₗ ρ.ToType) := hdomain.symm
    _ ≤ typeLT (⋃ i, B i) := unionEmbedding.ltEmbedding.ordinal_type_le
    _ = hUnion.orderType :=
      (hUnion.orderType_eq_typeLT_of_orderIso (OrderIso.refl _)).symm

end Set.IsPWO
