/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexBij

/-!
# Block data of the data colouring

The flags of the v-th block enumerate the fragment's flags at the
block's vertex, and the block values of the data colouring are the
colouring data at those flags: participating flags carry the odd
colour (or its partner on partner slots), the rest the even colour.
-/

namespace RS

open Finset

variable {k ℓ : ℕ}

/-- The flag of the j-th slot in the v-th block. -/
noncomputable def blockFlag (W : ClosedFragment)
    (v : Fin (ds W).length) (j : Fin ((ds W).get v)) : W.Flag :=
  (starFlagEnum W).symm (slotEmbed W v j)

/-- Block flags sit at the block's vertex. -/
theorem vertexOf_blockFlag (W : ClosedFragment)
    (v : Fin (ds W).length) (j : Fin ((ds W).get v)) :
    ClosedFragment.vertexOf W (blockFlag W v j) =
      blockVertex W v :=
  vertexOf_slotEmbed W v j

/-- The block-flag enumeration is injective. -/
theorem blockFlag_injective (W : ClosedFragment)
    (v : Fin (ds W).length) :
    Function.Injective (blockFlag W v) :=
  fun _ _ h => slotEmbed_injective W v
    ((starFlagEnum W).symm.injective h)

open scoped Classical in
/-- **Block flags enumerate the vertex's flags**: the image of the
block-flag enumeration is the set of flags at the block's
vertex. -/
theorem image_blockFlag (W : ClosedFragment)
    (v : Fin (ds W).length) :
    Finset.univ.image (blockFlag W v) =
      Finset.univ.filter (fun g =>
        ClosedFragment.vertexOf W g = blockVertex W v) := by
  ext g
  simp only [Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, -, rfl⟩
    exact vertexOf_blockFlag W v j
  · intro hvtx
    have hassign : starAssignEnum W (starFlagEnum W g) =
        finCongr (degList_length (starAssignEnum W)) v := by
      change (Fintype.equivFin W.Vertex)
        (starAssign W (starFlagEnum W g)) = _
      have hv : starAssign W (starFlagEnum W g) =
          blockVertex W v := by
        change ClosedFragment.vertexOf W
          ((starFlagEnum W).symm (starFlagEnum W g)) =
          blockVertex W v
        rw [_root_.Equiv.symm_apply_apply, hvtx]
      rw [hv, blockVertex, _root_.Equiv.apply_symm_apply]
    have hfst : (sortSigma (starAssignEnum W)
        (starFlagEnum W g)).1 = v := by
      rw [sortSigma_fst, hassign]
      exact Fin.ext rfl
    set q := sortSigma (starAssignEnum W) (starFlagEnum W g)
      with hq_def
    obtain ⟨w, jw⟩ := q
    simp only at hfst
    rcases hfst with rfl
    refine ⟨jw, ?_⟩
    change (starFlagEnum W).symm (slotEmbed W w jw) = g
    rw [slotEmbed_recover W w (starFlagEnum W g) jw hq_def,
      _root_.Equiv.symm_apply_apply]

/-- **The block value of the data colouring**: the colouring data
at the block flag, with the odd partner on partner slots. -/
theorem blockRestrict_colouringOf (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length)
    (j : Fin ((ds W).get v)) :
    blockRestrict (ds W)
      (cSorted W (colouringOf W F ψ φ)) v j =
    (if h : blockFlag W v j ∈ F.flags then
      Sum.inr (if (slotEmbed W v j).val < edgeCount W then
        φ.val ⟨blockFlag W v j, h⟩
      else
        oddPartner ℓ (φ.val ⟨blockFlag W v j, h⟩))
    else
      Sum.inl (ψ.val ⟨blockFlag W v j, h⟩)) := by
  rw [blockRestrict_val]
  rfl

/-- Non-participating block flags carry the even colour. -/
theorem blockRestrict_colouringOf_not_mem (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length)
    (j : Fin ((ds W).get v))
    (h : blockFlag W v j ∉ F.flags) :
    blockRestrict (ds W)
      (cSorted W (colouringOf W F ψ φ)) v j =
    Sum.inl (ψ.val ⟨blockFlag W v j, h⟩) := by
  rw [blockRestrict_colouringOf, dite_eq_right h]

/-- Participating block flags carry the odd colour or its
partner. -/
theorem blockRestrict_colouringOf_mem (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length)
    (j : Fin ((ds W).get v))
    (h : blockFlag W v j ∈ F.flags) :
    blockRestrict (ds W)
      (cSorted W (colouringOf W F ψ φ)) v j =
    Sum.inr (if (slotEmbed W v j).val < edgeCount W then
      φ.val ⟨blockFlag W v j, h⟩
    else
      oddPartner ℓ (φ.val ⟨blockFlag W v j, h⟩)) := by
  rw [blockRestrict_colouringOf, dite_eq_left h]

open Classical in
/-- The non-participating slots of a block. -/
noncomputable def evenSlots (W : ClosedFragment)
    (F : EdgeSubset W) (v : Fin (ds W).length) :
    Finset (Fin ((ds W).get v)) :=
  Finset.univ.filter (fun j => blockFlag W v j ∉ F.flags)

open Classical in
/-- Membership in the non-participating slots. -/
theorem mem_evenSlots {W : ClosedFragment} {F : EdgeSubset W}
    {v : Fin (ds W).length} (j : Fin ((ds W).get v)) :
    j ∈ evenSlots W F v ↔ blockFlag W v j ∉ F.flags := by
  rw [evenSlots, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The defining property of a non-participating block slot. -/
theorem blockSlot_not_mem {W : ClosedFragment}
    {F : EdgeSubset W} {v : Fin (ds W).length}
    (j : {j : Fin ((ds W).get v) // j ∈ evenSlots W F v}) :
    blockFlag W v j.val ∉ F.flags :=
  (Finset.mem_filter.mp j.prop).2

-- Raised budget: a filter over flags is matched against a filter
-- over block slots, so both attach-subtypes are unfolded.
open Classical in
/-- **The even colours at a block's vertex** are the even data at
the non-participating block slots. -/
theorem evenColoursAt_blockVertex (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (v : Fin (ds W).length) :
    F.evenColoursAt ψ (blockVertex W v) =
      ((evenSlots W F v).attach.val).map
        (fun j : {j : Fin ((ds W).get v) //
            j ∈ evenSlots W F v} =>
          ψ.val ⟨blockFlag W v j.val,
            blockSlot_not_mem j⟩) := by
  set A := evenSlots W F v with hA
  set B := Finset.univ.filter
    (fun f : {f : W.Flag // f ∉ F.flags} =>
      W.attach f.val = Sum.inl (blockVertex W v)) with hB
  have hforward : ∀ j : {j // j ∈ A},
      (⟨blockFlag W v j.val, blockSlot_not_mem j⟩ :
          {f : W.Flag // f ∉ F.flags}) ∈ B := by
    intro j
    rw [hB, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [ClosedFragment.attach_eq_vertexOf, vertexOf_blockFlag]
  let toB : {j // j ∈ A} →
      {f : {f : W.Flag // f ∉ F.flags} // f ∈ B} :=
    fun j => ⟨⟨blockFlag W v j.val, blockSlot_not_mem j⟩,
      hforward j⟩
  have hinj : Function.Injective toB := by
    intro j₁ j₂ h
    have h1 : blockFlag W v j₁.val = blockFlag W v j₂.val :=
      congrArg (fun x => x.val.val) h
    exact Subtype.ext (blockFlag_injective W v h1)
  have hsurj : Function.Surjective toB := by
    rintro ⟨⟨g, hg⟩, hgB⟩
    rw [hB, Finset.mem_filter] at hgB
    have hvtx : ClosedFragment.vertexOf W g =
        blockVertex W v :=
      Sum.inl.inj
        ((ClosedFragment.attach_eq_vertexOf W g).symm.trans
          hgB.2)
    have hgmem : g ∈ Finset.univ.filter (fun g' =>
        ClosedFragment.vertexOf W g' = blockVertex W v) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hvtx⟩
    rw [← image_blockFlag, Finset.mem_image] at hgmem
    obtain ⟨j, -, hj⟩ := hgmem
    have hjA : j ∈ A := by
      rw [hA, mem_evenSlots, hj]
      exact hg
    exact ⟨⟨j, hjA⟩, Subtype.ext (Subtype.ext hj)⟩
  have h2 : B.val.map ψ.val =
      B.attach.val.map (fun f => ψ.val f.val) := by
    rw [Finset.attach_val]
    exact (Multiset.attach_map_val' B.val ψ.val).symm
  have h3 : B.attach.val.map (fun f => ψ.val f.val) =
      A.attach.val.map
        (fun j : {j : Fin ((ds W).get v) //
            j ∈ evenSlots W F v} =>
          ψ.val ⟨blockFlag W v j.val,
            blockSlot_not_mem j⟩) := by
    rw [← Finset.univ_eq_attach, ← Finset.univ_eq_attach,
      ← Finset.map_univ_equiv (Equiv.ofBijective toB
        ⟨hinj, hsurj⟩), Finset.map_val, Multiset.map_map]
    rfl
  have h1 : F.evenColoursAt ψ (blockVertex W v) =
      B.val.map ψ.val := by
    rw [hB]
    unfold EdgeSubset.evenColoursAt
    refine congrArg (fun s : Finset {f : W.Flag // f ∉ F.flags} =>
      Multiset.map ψ.val s.val) ?_
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h1.trans (h2.trans h3)

open Classical in
/-- The participating slots of a block. -/
noncomputable def oddSlots (W : ClosedFragment)
    (F : EdgeSubset W) (v : Fin (ds W).length) :
    Finset (Fin ((ds W).get v)) :=
  Finset.univ.filter (fun j => blockFlag W v j ∈ F.flags)

open Classical in
/-- Membership in the participating slots. -/
theorem mem_oddSlots {W : ClosedFragment} {F : EdgeSubset W}
    {v : Fin (ds W).length} (j : Fin ((ds W).get v)) :
    j ∈ oddSlots W F v ↔ blockFlag W v j ∈ F.flags := by
  rw [oddSlots, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The defining property of a participating block slot. -/
theorem oddSlot_mem {W : ClosedFragment}
    {F : EdgeSubset W} {v : Fin (ds W).length}
    (j : {j : Fin ((ds W).get v) // j ∈ oddSlots W F v}) :
    blockFlag W v j.val ∈ F.flags :=
  (mem_oddSlots j.val).mp j.prop

-- As for the even colours, for an arbitrary value function.
open Classical in
/-- **Participating flags at a block's vertex reindex over the
participating slots**, for any value function. -/
theorem map_flagsAt_blockVertex {β : Type} (W : ClosedFragment)
    (F : EdgeSubset W) (v : Fin (ds W).length)
    (g : {f : W.Flag // f ∈ F.flags} → β) :
    ((Finset.univ.filter
        (fun f : {f : W.Flag // f ∈ F.flags} =>
          W.attach f.val = Sum.inl (blockVertex W v))).val).map
      g =
    ((oddSlots W F v).attach.val).map
      (fun j : {j : Fin ((ds W).get v) //
          j ∈ oddSlots W F v} =>
        g ⟨blockFlag W v j.val, oddSlot_mem j⟩) := by
  set A := oddSlots W F v with hA
  set B := Finset.univ.filter
    (fun f : {f : W.Flag // f ∈ F.flags} =>
      W.attach f.val = Sum.inl (blockVertex W v)) with hB
  have hforward : ∀ j : {j // j ∈ A},
      (⟨blockFlag W v j.val, oddSlot_mem j⟩ :
          {f : W.Flag // f ∈ F.flags}) ∈ B := by
    intro j
    rw [hB, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [ClosedFragment.attach_eq_vertexOf, vertexOf_blockFlag]
  let toB : {j // j ∈ A} →
      {f : {f : W.Flag // f ∈ F.flags} // f ∈ B} :=
    fun j => ⟨⟨blockFlag W v j.val, oddSlot_mem j⟩,
      hforward j⟩
  have hinj : Function.Injective toB := by
    intro j₁ j₂ h
    have h1 : blockFlag W v j₁.val = blockFlag W v j₂.val :=
      congrArg (fun x => x.val.val) h
    exact Subtype.ext (blockFlag_injective W v h1)
  have hsurj : Function.Surjective toB := by
    rintro ⟨⟨g', hg⟩, hgB⟩
    rw [hB, Finset.mem_filter] at hgB
    have hvtx : ClosedFragment.vertexOf W g' =
        blockVertex W v :=
      Sum.inl.inj
        ((ClosedFragment.attach_eq_vertexOf W g').symm.trans
          hgB.2)
    have hgmem : g' ∈ Finset.univ.filter (fun g'' =>
        ClosedFragment.vertexOf W g'' = blockVertex W v) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hvtx⟩
    rw [← image_blockFlag, Finset.mem_image] at hgmem
    obtain ⟨j, -, hj⟩ := hgmem
    have hjA : j ∈ A := by
      rw [hA, mem_oddSlots, hj]
      exact hg
    exact ⟨⟨j, hjA⟩, Subtype.ext (Subtype.ext hj)⟩
  have h2 : B.val.map g =
      B.attach.val.map (fun f => g f.val) := by
    rw [Finset.attach_val]
    exact (Multiset.attach_map_val' B.val g).symm
  have h3 : B.attach.val.map (fun f => g f.val) =
      A.attach.val.map
        (fun j : {j : Fin ((ds W).get v) //
            j ∈ oddSlots W F v} =>
          g ⟨blockFlag W v j.val, oddSlot_mem j⟩) := by
    rw [← Finset.univ_eq_attach, ← Finset.univ_eq_attach,
      ← Finset.map_univ_equiv (Equiv.ofBijective toB
        ⟨hinj, hsurj⟩), Finset.map_val, Multiset.map_map]
    rfl
  exact h2.trans h3

/-- Vertex products reindex over blocks. -/
theorem prod_blockVertex {M : Type*} [CommMonoid M]
    (W : ClosedFragment) (g : W.Vertex → M) :
    (∏ vtx : W.Vertex, g vtx) =
      ∏ v : Fin (ds W).length, g (blockVertex W v) :=
  (Fintype.prod_equiv
    ((finCongr (degList_length (starAssignEnum W))).trans
      (Fintype.equivFin W.Vertex).symm)
    (fun v => g (blockVertex W v)) g (fun _ => rfl)).symm

/-- Participation of a block slot is participation of its flag. -/
theorem blockRestrict_colouringOf_isRight (W : ClosedFragment)
    (F : EdgeSubset W) (ψ : F.EvenColouring k)
    (φ : F.OddColouring ℓ) (v : Fin (ds W).length)
    (j : Fin ((ds W).get v)) :
    (blockRestrict (ds W)
        (cSorted W (colouringOf W F ψ φ)) v j).isRight = true ↔
      blockFlag W v j ∈ F.flags := by
  constructor
  · intro hr
    by_contra hnot
    rw [blockRestrict_colouringOf_not_mem W F ψ φ v j hnot]
      at hr
    exact Bool.noConfusion hr
  · intro h
    rw [blockRestrict_colouringOf_mem W F ψ φ v j h]
    rfl

end RS
