/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ChainLists
import LeanPool.RegtsSevenster.RS.Common.FinSlots

/-!
# Membership and uniqueness in the edge and oriented enumerations

The edge and oriented pair lists enumerate each participating flag
exactly once. The slot helpers identify the two ends of each edge.
-/

namespace RS

open Classical Finset

/-! ### Edge enumeration -/

/-- The attached edge list for edgePairList is duplicate-free. -/
theorem attachWith_partEdges_nodup (W : ClosedFragment)
    (F : EdgeSubset W) :
    ((partEdges W F).attachWith (· ∈ edgeIndexSet W F)
      (fun _ hi => (Finset.mem_sort _).mp hi)).Nodup := by
  refine List.Nodup.pmap (fun a _ b _ h => Subtype.mk.inj h)
    (Finset.sort_nodup _ _)

/-- The two slots of an edge give distinct flags. -/
theorem castAdd_flag_ne_natAdd_flag (W : ClosedFragment)
    (i : Fin (edgeCount W)) :
    (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ≠
    (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i) :=
  fun h => castAdd_ne_natAdd i ((starFlagEnum W).symm.injective h)

open Classical in
/-- **The edge-interleaved enumeration is duplicate-free.** -/
theorem edgePairList_nodup (W : ClosedFragment)
    (F : EdgeSubset W) :
    (edgePairList W F).Nodup := by
  rw [edgePairList, List.nodup_flatMap]
  constructor
  · intro i _
    refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    intro hmem
    rw [List.mem_singleton] at hmem
    have hval : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i.val) =
        (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i.val) :=
      congrArg (fun z : {f : W.Flag // f ∈ F.flags} => z.val) hmem
    exact castAdd_flag_ne_natAdd_flag W i.val hval
  · have hnd := attachWith_partEdges_nodup W F
    refine List.Pairwise.imp_of_mem ?_
      (List.Pairwise.imp (fun {a b} h => h) hnd)
    intro i₁ i₂ _ _ hne x hx₁ hx₂
    -- x appears in [rep i₁, partner i₁] and [rep i₂, partner i₂]
    -- Extract which slot x occupies in each list
    have slot_of_mem : ∀ (i : {i : Fin (edgeCount W) // i ∈ edgeIndexSet W F}),
        x ∈ [⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) i.val),
              repMem_of_partEdge i.prop⟩,
             ⟨(starFlagEnum W).symm (Fin.natAdd (edgeCount W) i.val),
              partnerMem_of_partEdge i.prop⟩] →
        starFlagEnum W x.val = Fin.castAdd (edgeCount W) i.val ∨
        starFlagEnum W x.val = Fin.natAdd (edgeCount W) i.val := by
      intro i hmem
      rcases List.mem_cons.mp hmem with h | h
      · left; rw [show x.val = (starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i.val) from
            congrArg Subtype.val h, _root_.Equiv.apply_symm_apply]
      · right
        rw [List.mem_singleton] at h
        rw [show x.val = (starFlagEnum W).symm
            (Fin.natAdd (edgeCount W) i.val) from
            congrArg Subtype.val h, _root_.Equiv.apply_symm_apply]
    obtain h₁ | h₁ := slot_of_mem i₁ hx₁ <;>
    obtain h₂ | h₂ := slot_of_mem i₂ hx₂
    · -- castAdd i₁ = castAdd i₂
      have heq : Fin.castAdd (edgeCount W) i₁.val =
          Fin.castAdd (edgeCount W) i₂.val :=
        h₁.symm.trans h₂
      exact hne (Subtype.ext (Fin.castAdd_injective _ _ heq))
    · -- castAdd i₁ = natAdd i₂
      have h := congrArg Fin.val (h₁.symm.trans h₂)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h; omega
    · -- natAdd i₁ = castAdd i₂
      have h := congrArg Fin.val (h₁.symm.trans h₂)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h; omega
    · -- natAdd i₁ = natAdd i₂
      have heq : Fin.natAdd (edgeCount W) i₁.val =
          Fin.natAdd (edgeCount W) i₂.val :=
        h₁.symm.trans h₂
      exact hne (Subtype.ext (Fin.natAdd_injective _ _ heq))

open Classical in
/-- **Every participating flag appears in the edge-interleaved list.** -/
theorem mem_edgePairList (W : ClosedFragment)
    (F : EdgeSubset W) (x : {f : W.Flag // f ∈ F.flags}) :
    x ∈ edgePairList W F := by
  rw [edgePairList, List.mem_flatMap]
  set q := starFlagEnum W x.val with hq_def
  by_cases hlow : q.val < edgeCount W
  · -- x is on the low (rep) half
    set i : Fin (edgeCount W) := ⟨q.val, hlow⟩ with hi_def
    have hslot : Fin.castAdd (edgeCount W) i = q := Fin.ext rfl
    have hmem : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) =
        x.val := by
      rw [hslot, hq_def, _root_.Equiv.symm_apply_apply]
    have hei : i ∈ edgeIndexSet W F := by
      rw [edgeIndexSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hmem ▸ x.prop⟩
    have hsort : i ∈ (partEdges W F) := by
      rw [partEdges, Finset.mem_sort]; exact hei
    refine ⟨⟨i, hei⟩, ?_, ?_⟩
    · rw [show (partEdges W F).attachWith (· ∈ edgeIndexSet W F)
          (fun _ hi => (Finset.mem_sort _).mp hi) =
        (partEdges W F).pmap Subtype.mk
          (fun _ hi => (Finset.mem_sort _).mp hi) from rfl]
      exact List.mem_pmap.mpr ⟨i, hsort, Subtype.ext rfl⟩
    · exact List.mem_cons.mpr (Or.inl (Subtype.ext hmem.symm))
  · -- x is on the high (partner) half
    have hge : q.val ≥ edgeCount W := Nat.le_of_not_lt hlow
    have hlt : q.val - edgeCount W < edgeCount W := by
      have := q.isLt; omega
    set i : Fin (edgeCount W) := ⟨q.val - edgeCount W, hlt⟩ with hi_def
    have hslot : Fin.natAdd (edgeCount W) i = q :=
      Fin.ext (by show edgeCount W + (q.val - edgeCount W) = q.val; omega)
    have hmem : (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i) = x.val := by
      rw [hslot, hq_def, _root_.Equiv.symm_apply_apply]
    -- The partner of x.val is the rep flag for this edge
    have hpair : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) =
        W.pairing x.val := by
      rw [← hmem, ← pairing_starFlagEnum_symm W i, W.pairing_invol]
    have hei : i ∈ edgeIndexSet W F := by
      rw [edgeIndexSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hpair ▸ F.pairing_mem _ x.prop⟩
    have hsort : i ∈ (partEdges W F) := by
      rw [partEdges, Finset.mem_sort]; exact hei
    refine ⟨⟨i, hei⟩, ?_, ?_⟩
    · rw [show (partEdges W F).attachWith (· ∈ edgeIndexSet W F)
          (fun _ hi => (Finset.mem_sort _).mp hi) =
        (partEdges W F).pmap Subtype.mk
          (fun _ hi => (Finset.mem_sort _).mp hi) from rfl]
      exact List.mem_pmap.mpr ⟨i, hsort, Subtype.ext rfl⟩
    · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr (Subtype.ext
      hmem.symm)))

/-! ### Oriented enumeration -/

open Classical in
/-- **The oriented enumeration is duplicate-free.** -/
theorem orientedPairList_nodup (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    (orientedPairList W F o).Nodup := by
  rw [orientedPairList, List.nodup_flatMap]
  constructor
  · intro i _
    -- Each block is either [partner, rep] or [rep, partner]
    by_cases ho : o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i.val)) = true
    · rw [if_pos ho]
      refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      intro hmem
      rw [List.mem_singleton] at hmem
      have hval : (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i.val) =
          (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i.val) :=
        congrArg (fun z : {f : W.Flag // f ∈ F.flags} => z.val) hmem
      exact (castAdd_flag_ne_natAdd_flag W i.val hval.symm)
    · rw [if_neg ho]
      refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      intro hmem
      rw [List.mem_singleton] at hmem
      have hval : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i.val) =
          (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i.val) :=
        congrArg (fun z : {f : W.Flag // f ∈ F.flags} => z.val) hmem
      exact castAdd_flag_ne_natAdd_flag W i.val hval
  · -- Disjoint blocks: same as edgePairList since both blocks contain the same
    --   two flags
    have hnd := attachWith_partEdges_nodup W F
    refine List.Pairwise.imp_of_mem ?_
      (List.Pairwise.imp (fun {a b} h => h) hnd)
    intro i₁ i₂ _ _ hne x hx₁ hx₂
    -- Extract slot from membership, regardless of if-branch
    have slot_of_mem_oriented : ∀ (i : {i : Fin (edgeCount W) // i ∈
      edgeIndexSet W F}),
        x ∈ (if o.isOut ((starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i.val)) = true then
          [⟨(starFlagEnum W).symm (Fin.natAdd (edgeCount W) i.val),
            partnerMem_of_partEdge i.prop⟩,
           ⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) i.val),
            repMem_of_partEdge i.prop⟩]
        else
          [⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) i.val),
            repMem_of_partEdge i.prop⟩,
           ⟨(starFlagEnum W).symm (Fin.natAdd (edgeCount W) i.val),
            partnerMem_of_partEdge i.prop⟩]) →
        starFlagEnum W x.val = Fin.castAdd (edgeCount W) i.val ∨
        starFlagEnum W x.val = Fin.natAdd (edgeCount W) i.val := by
      intro i hmem
      by_cases ho : o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i.val)) = true
      · rw [if_pos ho] at hmem
        rcases List.mem_cons.mp hmem with h | h
        · right
          rw [show x.val = (starFlagEnum W).symm
              (Fin.natAdd (edgeCount W) i.val) from
              congrArg Subtype.val h, _root_.Equiv.apply_symm_apply]
        · left
          rw [List.mem_singleton] at h
          rw [show x.val = (starFlagEnum W).symm
              (Fin.castAdd (edgeCount W) i.val) from
              congrArg Subtype.val h, _root_.Equiv.apply_symm_apply]
      · rw [if_neg ho] at hmem
        rcases List.mem_cons.mp hmem with h | h
        · left
          rw [show x.val = (starFlagEnum W).symm
              (Fin.castAdd (edgeCount W) i.val) from
              congrArg Subtype.val h, _root_.Equiv.apply_symm_apply]
        · right
          rw [List.mem_singleton] at h
          rw [show x.val = (starFlagEnum W).symm
              (Fin.natAdd (edgeCount W) i.val) from
              congrArg Subtype.val h, _root_.Equiv.apply_symm_apply]
    obtain h₁ | h₁ := slot_of_mem_oriented i₁ hx₁ <;>
    obtain h₂ | h₂ := slot_of_mem_oriented i₂ hx₂
    · exact hne (Subtype.ext (Fin.castAdd_injective _ _ (h₁.symm.trans h₂)))
    · have h := congrArg Fin.val (h₁.symm.trans h₂)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h; omega
    · have h := congrArg Fin.val (h₁.symm.trans h₂)
      simp only [Fin.val_castAdd, Fin.val_natAdd] at h; omega
    · exact hne (Subtype.ext (Fin.natAdd_injective _ _ (h₁.symm.trans h₂)))

open Classical in
/-- **Every participating flag appears in the oriented list.** -/
theorem mem_orientedPairList (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) (x : {f : W.Flag // f ∈ F.flags}) :
    x ∈ orientedPairList W F o := by
  -- The oriented list contains the same elements as edgePairList
  -- (same two flags per edge, just possibly swapped)
  rw [orientedPairList, List.mem_flatMap]
  have hep := mem_edgePairList W F x
  rw [edgePairList, List.mem_flatMap] at hep
  obtain ⟨i, hi, hx⟩ := hep
  refine ⟨i, hi, ?_⟩
  by_cases ho : o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) i.val)) = true
  · rw [if_pos ho]
    rcases List.mem_cons.mp hx with h | h
    · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr h))
    · rw [List.mem_singleton] at h
      exact List.mem_cons.mpr (Or.inl h)
  · rw [if_neg ho]
    exact hx

end RS
