/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.ListPairs
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PairList
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CircuitCount

/-!
# The regroup sign

The extraction enumerates a subset's participating flags three
ways: *oriented*, each edge's representative followed by its
pairing partner; *matched*, each incoming flag followed by its
match; and *global*, the per-vertex pair blocks concatenated.  The
sign relating them is the regroup sign, and this module computes
it in two halves.

* **Oriented to matched** (`sign_listIndexPerm_oriented_matched`)
  conjugates the out-permutation: the index permutation between
  the two enumerations acts on edge indices exactly as the
  orientation's out-permutation acts on flags, so the two signs
  agree.
* **Matched to global** (`sign_listIndexPerm_matched_global`) is
  even: both enumerations list the same incoming flags each
  followed by its match, so the index permutation moves whole
  two-element blocks and its sign is a square.

Both run on the flat-map presentations of the three lists and on
the index arithmetic of a list of pairs.
-/

@[expose] public section

namespace RS

open Finset Equiv

variable {k ℓ : ℕ}

/-! ## Slot extraction from block membership -/

/-- Extract slot index from oriented block membership. -/
private theorem slot_of_orientedBlock' {W : ClosedFragment} {F : EdgeSubset W}
    {κ : F.TransitionSystem} {o : κ.Orientation}
    (i : { x : Fin (edgeCount W) // x ∈ edgeIndexSet W F })
    (x : {f : W.Flag // f ∈ F.flags})
    (hx : x ∈ (if o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i.val)) = true then
      [⟨(starFlagEnum W).symm (Fin.natAdd (edgeCount W) i.val),
        partnerMem_of_partEdge i.prop⟩,
       ⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) i.val),
        repMem_of_partEdge i.prop⟩]
    else
      [⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) i.val),
        repMem_of_partEdge i.prop⟩,
       ⟨(starFlagEnum W).symm (Fin.natAdd (edgeCount W) i.val),
        partnerMem_of_partEdge i.prop⟩])) :
    starFlagEnum W x.val = Fin.castAdd (edgeCount W) i.val ∨
    starFlagEnum W x.val = Fin.natAdd (edgeCount W) i.val := by
  by_cases ho : o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) i.val)) = true
  · rw [ite_eq_left ho] at hx
    rcases List.mem_cons.mp hx with h | h
    · right
      rw [show x.val = (starFlagEnum W).symm
          (Fin.natAdd (edgeCount W) i.val) from congrArg Subtype.val h,
        _root_.Equiv.apply_symm_apply]
    · left
      rw [List.mem_singleton] at h
      rw [show x.val = (starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i.val) from congrArg Subtype.val h,
        _root_.Equiv.apply_symm_apply]
  · rw [ite_eq_right ho] at hx
    rcases List.mem_cons.mp hx with h | h
    · left
      rw [show x.val = (starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i.val) from congrArg Subtype.val h,
        _root_.Equiv.apply_symm_apply]
    · right
      rw [List.mem_singleton] at h
      rw [show x.val = (starFlagEnum W).symm
          (Fin.natAdd (edgeCount W) i.val) from congrArg Subtype.val h,
        _root_.Equiv.apply_symm_apply]

/-- For an element in a matched block, classify it as the in-flag
    (with its slot) or as match of the in-flag (outgoing). -/
private theorem matchedBlock_classify {W : ClosedFragment} {F : EdgeSubset W}
    {κ : F.TransitionSystem} {o : κ.Orientation}
    (c : { x : Fin (edgeCount W) // x ∈ edgeIndexSet W F })
    (x : {f : W.Flag // f ∈ F.flags})
    (hx : x ∈ (if o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) c.val)) = true then
      [⟨(starFlagEnum W).symm (Fin.natAdd (edgeCount W) c.val),
        partnerMem_of_partEdge c.prop⟩,
       ⟨κ.match_ ((starFlagEnum W).symm (Fin.natAdd (edgeCount W) c.val)),
        κ.match_mem _ (partnerMem_of_partEdge c.prop)⟩]
    else
      [⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) c.val),
        repMem_of_partEdge c.prop⟩,
       ⟨κ.match_ ((starFlagEnum W).symm (Fin.castAdd (edgeCount W) c.val)),
        κ.match_mem _ (repMem_of_partEdge c.prop)⟩])) :
    -- Either x is the in-flag (incoming, with a known slot)
    (o.isOut x.val = false ∧
      (starFlagEnum W x.val = Fin.castAdd (edgeCount W) c.val ∨
       starFlagEnum W x.val = Fin.natAdd (edgeCount W) c.val)) ∨
    -- Or x = match(inFlag) (outgoing) and inFlag has known slot and membership
    (o.isOut x.val = true ∧ ∃ inF : W.Flag, inF ∈ F.flags ∧ x.val = κ.match_ inF
      ∧
      (starFlagEnum W inF = Fin.castAdd (edgeCount W) c.val ∨
       starFlagEnum W inF = Fin.natAdd (edgeCount W) c.val)) := by
  by_cases ho : o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) c.val)) = true
  · rw [ite_eq_left ho] at hx
    -- block = [partner, match(partner)]
    -- partner = symm(natAdd c.val), which is incoming (pairing_flip)
    have partner_in : o.isOut ((starFlagEnum W).symm
        (Fin.natAdd (edgeCount W) c.val)) = false := by
      have := o.pairing_flip _ (repMem_of_partEdge c.prop)
      rw [pairing_starFlagEnum_symm] at this; rw [this, ho]; rfl
    rcases List.mem_cons.mp hx with h | h
    · -- x = partner (incoming)
      left
      have hxv : x.val = (starFlagEnum W).symm
          (Fin.natAdd (edgeCount W) c.val) :=
        congrArg (fun z : {f : W.Flag // f ∈ F.flags} => z.val) h
      exact ⟨by rw [hxv]; exact partner_in,
             Or.inr (by rw [hxv, _root_.Equiv.apply_symm_apply])⟩
    · -- x = match(partner) (outgoing)
      right
      rw [List.mem_singleton] at h
      have hxv : x.val = κ.match_ ((starFlagEnum W).symm
          (Fin.natAdd (edgeCount W) c.val)) :=
        congrArg (fun z : {f : W.Flag // f ∈ F.flags} => z.val) h
      constructor
      · rw [hxv, o.match_flip _ (partnerMem_of_partEdge c.prop), partner_in];
        rfl
      · exact ⟨_, partnerMem_of_partEdge c.prop, hxv,
               Or.inr (_root_.Equiv.apply_symm_apply _ _)⟩
  · rw [ite_eq_right ho] at hx
    -- block = [rep, match(rep)]
    -- rep = symm(castAdd c.val), which is incoming (by ho)
    have rep_in : o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) c.val)) = false := by
      cases hb : o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) c.val))
      · rfl
      · exact absurd hb ho
    rcases List.mem_cons.mp hx with h | h
    · -- x = rep (incoming)
      left
      have hxv : x.val = (starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) c.val) :=
        congrArg (fun z : {f : W.Flag // f ∈ F.flags} => z.val) h
      exact ⟨by rw [hxv]; exact rep_in,
             Or.inl (by rw [hxv, _root_.Equiv.apply_symm_apply])⟩
    · -- x = match(rep) (outgoing)
      right
      rw [List.mem_singleton] at h
      have hxv : x.val = κ.match_ ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) c.val)) :=
        congrArg (fun z : {f : W.Flag // f ∈ F.flags} => z.val) h
      constructor
      · rw [hxv, o.match_flip _ (repMem_of_partEdge c.prop), rep_in]; rfl
      · exact ⟨_, repMem_of_partEdge c.prop, hxv,
               Or.inl (_root_.Equiv.apply_symm_apply _ _)⟩

/-! ## Slot contradiction helper -/

/-- If two edge indices give the same slot (castAdd or natAdd), the edges
are equal. -/
private theorem edge_eq_of_slot_eq {W : ClosedFragment}
    {f : W.Flag} {a b : Fin (edgeCount W)}
    (ha : starFlagEnum W f = Fin.castAdd (edgeCount W) a ∨
          starFlagEnum W f = Fin.natAdd (edgeCount W) a)
    (hb : starFlagEnum W f = Fin.castAdd (edgeCount W) b ∨
          starFlagEnum W f = Fin.natAdd (edgeCount W) b) :
    a = b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Fin.castAdd_injective _ _ (ha.symm.trans hb)
  · have := congrArg Fin.val (ha.symm.trans hb)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  · have := congrArg Fin.val (ha.symm.trans hb)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  · exact Fin.natAdd_injective _ _ (ha.symm.trans hb)

/-! ## Nodup: matched pair list -/

-- As for the oriented list: block by block, with the matching in
-- place of the pairing.
/-- The matched pair list has no repeats. -/
theorem matchedPairList_nodup' (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    (matchedPairList W F o).Nodup := by
  rw [matchedPairList, List.nodup_flatMap]; constructor
  · -- Each block: [inFlag, match(inFlag)] is nodup since match has no fixed
    --   points
    intro ⟨i, hi⟩ _
    by_cases ho : o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i)) = true
    · rw [ite_eq_left ho]
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, List.nodup_singleton _⟩
      rw [List.mem_singleton] at hmem
      have hval := congrArg (fun z : {f : W.Flag // f ∈ F.flags} => z.val) hmem
      exact κ.match_ne _ (partnerMem_of_partEdge hi) hval.symm
    · rw [ite_eq_right ho]
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, List.nodup_singleton _⟩
      rw [List.mem_singleton] at hmem
      have hval := congrArg (fun z : {f : W.Flag // f ∈ F.flags} => z.val) hmem
      exact κ.match_ne _ (repMem_of_partEdge hi) hval.symm
  · -- Cross-block disjointness
    refine List.Pairwise.imp_of_mem (fun {a b} _ _ hab x hxa hxb => ?_)
      (List.Pairwise.imp (fun {a b} h => h) (attachWith_partEdges_nodup W F))
    have hne : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    obtain ⟨ha_in, ha_slot⟩ | ⟨ha_out, inA, hmemA, hxA, hslotA⟩ :=
      matchedBlock_classify a x hxa
    · -- x is incoming from edge a
      obtain ⟨_, hb_slot⟩ | ⟨hb_out, _, _, _, _⟩ := matchedBlock_classify b x
        hxb
      · -- x also incoming from edge b → slot comparison
        exact hne (edge_eq_of_slot_eq ha_slot hb_slot)
      · -- x incoming from a, outgoing from b → isOut contradiction
        rw [ha_in] at hb_out; exact Bool.noConfusion hb_out
    · -- x is outgoing from edge a (x = match(inA))
      obtain ⟨hb_in, _⟩ | ⟨_, inB, hmemB, hxB, hslotB⟩ :=
        matchedBlock_classify b x hxb
      · -- x outgoing from a, incoming from b → isOut contradiction
        rw [hb_in] at ha_out; exact Bool.noConfusion ha_out
      · -- Both outgoing: match injectivity
        have hmatch_eq : κ.match_ inA = κ.match_ inB := hxA.symm.trans hxB
        have hinAB : inA = inB :=
          (κ.match_invol inA hmemA).symm.trans
            (congrArg κ.match_ hmatch_eq |>.trans (κ.match_invol inB hmemB))
        exact hne (edge_eq_of_slot_eq (hinAB ▸ hslotA) hslotB)

/-! ## Membership: matched pair list -/

-- As for the oriented list: membership through the star
-- enumeration, using involutivity of the matching.
/-- And lists every participating flag — so it is a reordering of
them, and its sign is the regroup sign. -/
theorem mem_matchedPairList' (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (x : {f : W.Flag // f ∈ F.flags}) :
    x ∈ matchedPairList W F o := by
  rw [matchedPairList, List.mem_flatMap]
  by_cases hout : o.isOut x.val = true
  · -- ═══════ x OUTGOING: x = match (inFlag) OF SOME EDGE ═══════
    -- The in-flag is match(x) since match is involutive
    set y : {f : W.Flag // f ∈ F.flags} := ⟨κ.match_ x.val, κ.match_mem _
      x.prop⟩
    have hy_in : o.isOut y.val = false := by
      change o.isOut (κ.match_ x.val) = false
      rw [o.match_flip x.val x.prop, hout]; rfl
    -- Find the edge containing y via its slot
    set q := starFlagEnum W y.val with hq_def
    by_cases hlow : q.val < edgeCount W
    · set i : Fin (edgeCount W) := ⟨q.val, hlow⟩ with hi_def
      have hslot : Fin.castAdd (edgeCount W) i = q := Fin.ext rfl
      have hymem : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) =
          y.val := by
        rw [hslot, hq_def, _root_.Equiv.symm_apply_apply]
      have hei : i ∈ edgeIndexSet W F := by
        rw [edgeIndexSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hymem ▸ y.prop⟩
      have hsort : i ∈ (partEdges W F) := (Finset.mem_sort _).mpr hei
      have h_not_out : ¬(o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)) = true) := by
        rw [hymem, hy_in]; exact Bool.false_ne_true
      refine ⟨⟨i, hei⟩, ?_, ?_⟩
      · rw [show (partEdges W F).attachWith (· ∈ edgeIndexSet W F)
            (fun _ hi => (Finset.mem_sort _).mp hi) =
          (partEdges W F).pmap Subtype.mk
            (fun _ hi => (Finset.mem_sort _).mp hi) from rfl]
        exact List.mem_pmap.mpr ⟨i, hsort, Subtype.ext rfl⟩
      · rw [ite_eq_right h_not_out]
        -- block = [rep, match(rep)] where rep = symm(castAdd i) = y
        apply List.mem_cons.mpr; right; rw [List.mem_singleton]
        apply Subtype.ext
        change x.val = κ.match_ ((starFlagEnum W).symm (Fin.castAdd (edgeCount W)
          i))
        rw [hymem]; exact (κ.match_invol _ x.prop).symm
    · have hge : q.val ≥ edgeCount W := Nat.le_of_not_lt hlow
      have hlt : q.val - edgeCount W < edgeCount W := by have := q.isLt; omega
      set i : Fin (edgeCount W) := ⟨q.val - edgeCount W, hlt⟩ with hi_def
      have hslot : Fin.natAdd (edgeCount W) i = q :=
        Fin.ext (by change edgeCount W + (q.val - edgeCount W) = q.val; omega)
      have hymem : (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i) =
          y.val := by
        rw [hslot, hq_def, _root_.Equiv.symm_apply_apply]
      have hpair : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) =
          W.pairing y.val := by
        rw [← hymem, ← pairing_starFlagEnum_symm W i, W.pairing_invol]
      have hei : i ∈ edgeIndexSet W F := by
        rw [edgeIndexSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hpair ▸ F.pairing_mem _ y.prop⟩
      have hsort : i ∈ (partEdges W F) := (Finset.mem_sort _).mpr hei
      have h_out : o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)) = true := by
        have hflip := o.pairing_flip _ (repMem_of_partEdge hei)
        rw [pairing_starFlagEnum_symm] at hflip
        rw [hymem, hy_in] at hflip
        -- hflip : false = !(o.isOut (symm (castAdd i)))
        cases hc : o.isOut ((starFlagEnum W).symm (Fin.castAdd (edgeCount W) i))
        · simp [hc] at hflip
        · rfl
      refine ⟨⟨i, hei⟩, ?_, ?_⟩
      · rw [show (partEdges W F).attachWith (· ∈ edgeIndexSet W F)
            (fun _ hi => (Finset.mem_sort _).mp hi) =
          (partEdges W F).pmap Subtype.mk
            (fun _ hi => (Finset.mem_sort _).mp hi) from rfl]
        exact List.mem_pmap.mpr ⟨i, hsort, Subtype.ext rfl⟩
      · rw [ite_eq_left h_out]
        -- block = [partner, match(partner)] where partner = symm(natAdd i) = y
        apply List.mem_cons.mpr; right; rw [List.mem_singleton]
        apply Subtype.ext
        change x.val = κ.match_ ((starFlagEnum W).symm (Fin.natAdd (edgeCount W)
          i))
        rw [hymem]; exact (κ.match_invol _ x.prop).symm
  · -- ═══════ x INCOMING ═══════
    have hin : o.isOut x.val = false := by
      cases hb : o.isOut x.val
      · rfl
      · exact absurd hb hout
    set q := (starFlagEnum W) x.val with hq_def
    by_cases hlow : q.val < edgeCount W
    · set i : Fin (edgeCount W) := ⟨q.val, hlow⟩ with hi_def
      have hslot : Fin.castAdd (edgeCount W) i = q := Fin.ext rfl
      have hmem : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) =
          x.val := by
        rw [hslot, hq_def, _root_.Equiv.symm_apply_apply]
      have hei : i ∈ edgeIndexSet W F := by
        rw [edgeIndexSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hmem ▸ x.prop⟩
      have hsort : i ∈ (partEdges W F) := (Finset.mem_sort _).mpr hei
      have h_not_out : ¬(o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)) = true) := by
        rw [hmem, hin]; exact Bool.false_ne_true
      refine ⟨⟨i, hei⟩, ?_, ?_⟩
      · rw [show (partEdges W F).attachWith (· ∈ edgeIndexSet W F)
            (fun _ hi => (Finset.mem_sort _).mp hi) =
          (partEdges W F).pmap Subtype.mk
            (fun _ hi => (Finset.mem_sort _).mp hi) from rfl]
        exact List.mem_pmap.mpr ⟨i, hsort, Subtype.ext rfl⟩
      · rw [ite_eq_right h_not_out]
        exact List.mem_cons.mpr (Or.inl (Subtype.ext hmem.symm))
    · have hge : q.val ≥ edgeCount W := Nat.le_of_not_lt hlow
      have hlt : q.val - edgeCount W < edgeCount W := by have := q.isLt; omega
      set i : Fin (edgeCount W) := ⟨q.val - edgeCount W, hlt⟩ with hi_def
      have hslot : Fin.natAdd (edgeCount W) i = q :=
        Fin.ext (by change edgeCount W + (q.val - edgeCount W) = q.val; omega)
      have hmem : (starFlagEnum W).symm (Fin.natAdd (edgeCount W) i) =
          x.val := by
        rw [hslot, hq_def, _root_.Equiv.symm_apply_apply]
      have hpair : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) =
          W.pairing x.val := by
        rw [← hmem, ← pairing_starFlagEnum_symm W i, W.pairing_invol]
      have hei : i ∈ edgeIndexSet W F := by
        rw [edgeIndexSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hpair ▸ F.pairing_mem _ x.prop⟩
      have hsort : i ∈ (partEdges W F) := (Finset.mem_sort _).mpr hei
      have h_out : o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)) = true := by
        have hflip := o.pairing_flip _ (repMem_of_partEdge hei)
        rw [pairing_starFlagEnum_symm] at hflip
        rw [hmem, hin] at hflip
        cases hc : o.isOut ((starFlagEnum W).symm (Fin.castAdd (edgeCount W) i))
        · simp [hc] at hflip
        · rfl
      refine ⟨⟨i, hei⟩, ?_, ?_⟩
      · rw [show (partEdges W F).attachWith (· ∈ edgeIndexSet W F)
            (fun _ hi => (Finset.mem_sort _).mp hi) =
          (partEdges W F).pmap Subtype.mk
            (fun _ hi => (Finset.mem_sort _).mp hi) from rfl]
        exact List.mem_pmap.mpr ⟨i, hsort, Subtype.ext rfl⟩
      · rw [ite_eq_left h_out]
        exact List.mem_cons.mpr (Or.inl (Subtype.ext hmem.symm))

/-! ## Nodup and membership: global pair list -/

private theorem globalPairList_nodup' (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    (globalPairList W F o).Nodup := by
  rw [globalPairList, List.nodup_flatMap]; constructor
  · intro v _; exact pairFlagList_nodup o (blockVertex W v)
  · refine List.Pairwise.imp_of_mem (fun {a b} _ _ hab x hxa hxb => ?_)
      (List.Pairwise.imp (fun {a b} h => h) (List.nodup_finRange _))
    exact hab (blockVertex_injective' W
      (Sum.inl.inj ((mem_pairFlagList o _ x).mp hxa |>.symm.trans
        ((mem_pairFlagList o _ x).mp hxb))))

private theorem mem_globalPairList' (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (x : {f : W.Flag // f ∈ F.flags}) :
    x ∈ globalPairList W F o := by
  rw [globalPairList, List.mem_flatMap]
  obtain ⟨v, hv⟩ := κ.attach_internal x.val x.prop
  obtain ⟨bv, hbv⟩ := blockVertex_surjective' W v
  exact ⟨bv, List.mem_finRange _, hbv ▸ (mem_pairFlagList o v x).mpr hv⟩

/-! ## Length equalities -/

private theorem len_oriented_eq_matched (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    (orientedPairList W F o).length = (matchedPairList W F o).length :=
  length_eq_of_nodup_mem _ _
    (orientedPairList_nodup W F o) (matchedPairList_nodup' W F o)
    (fun x => ⟨fun _ => mem_matchedPairList' W F o x,
               fun _ => mem_orientedPairList W F o x⟩)

private theorem len_matched_eq_global (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    (matchedPairList W F o).length = (globalPairList W F o).length :=
  length_eq_of_nodup_mem _ _
    (matchedPairList_nodup' W F o) (globalPairList_nodup' W F o)
    (fun x => ⟨fun _ => mem_globalPairList' W F o x,
               fun _ => mem_matchedPairList' W F o x⟩)

/-! ## Match subtype and base lists -/

/-- Match as a subtype-preserving function. -/
private noncomputable def matchSub {W : ClosedFragment} {F : EdgeSubset W}
    (κ : F.TransitionSystem) (f : {f : W.Flag // f ∈ F.flags}) :
    {f : W.Flag // f ∈ F.flags} :=
  ⟨κ.match_ f.val, κ.match_mem _ f.prop⟩

/-- Incoming flag at each edge (edge-ordered base for matched). -/
private noncomputable def matchedInFlag {W : ClosedFragment} {F : EdgeSubset W}
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (e : { x : Fin (edgeCount W) // x ∈ edgeIndexSet W F }) :
    {f : W.Flag // f ∈ F.flags} :=
  if o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) e.val)) = true then
    ⟨(starFlagEnum W).symm (Fin.natAdd (edgeCount W) e.val),
      partnerMem_of_partEdge e.prop⟩
  else
    ⟨(starFlagEnum W).symm (Fin.castAdd (edgeCount W) e.val),
      repMem_of_partEdge e.prop⟩

/-- Edge-ordered incoming-flag base list. -/
private noncomputable def matchedBase (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    List {f : W.Flag // f ∈ F.flags} :=
  ((partEdges W F).attachWith (· ∈ edgeIndexSet W F)
    (fun _ hi => (Finset.mem_sort _).mp hi)).map (matchedInFlag o)

/-- Vertex-ordered incoming-flag base list. -/
private noncomputable def globalBase (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    List {f : W.Flag // f ∈ F.flags} :=
  (List.finRange (ds W).length).flatMap
    (fun v => (F.inFlagsAt o (blockVertex W v)).attachWith (· ∈ F.flags)
      (fun _ hf => F.mem_of_mem_inFlagsAt hf))

/-! ## FlatMap decompositions -/

-- Raised budget: the two flat-map presentations are matched edge
-- by edge, each with its orientation dichotomy.
private theorem matchedPairList_eq_flatMap (W : ClosedFragment) (F : EdgeSubset
  W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    matchedPairList W F o =
    (matchedBase W F o).flatMap (fun f => [f, matchSub κ f]) := by
  rw [matchedPairList, matchedBase, List.flatMap_map]
  congr 1; ext ⟨e, he⟩
  unfold matchedInFlag matchSub
  by_cases ho : o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) e)) = true
  · simp [ho]
  · simp [ho]

-- As for the matched list, over the per-vertex blocks.
private theorem globalPairList_eq_flatMap (W : ClosedFragment) (F : EdgeSubset
  W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    globalPairList W F o =
    (globalBase W F o).flatMap (fun f => [f, matchSub κ f]) := by
  rw [globalPairList, globalBase]
  simp_rw [show ∀ v, pairFlagList (F := F) o (blockVertex W v) =
    ((F.inFlagsAt o (blockVertex W v)).attachWith (· ∈ F.flags)
      (fun _ hf => F.mem_of_mem_inFlagsAt hf)).flatMap
      (fun f => [f, matchSub κ f]) from fun _ => rfl]
  exact List.flatMap_assoc.symm

/-! ## Pairing properties -/

private theorem matchedPairList_paired (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) (j : ℕ) :
    (matchedPairList W F o)[2 * j + 1]? =
    (matchedPairList W F o)[2 * j]?.map (matchSub κ) := by
  rw [matchedPairList_eq_flatMap]
  exact getElem?_self_paired (matchedBase W F o) (matchSub κ) j

private theorem globalPairList_paired (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) (j : ℕ) :
    (globalPairList W F o)[2 * j + 1]? =
    (globalPairList W F o)[2 * j]?.map (matchSub κ) := by
  rw [globalPairList_eq_flatMap]
  exact getElem?_self_paired (globalBase W F o) (matchSub κ) j

/-! ## Orientation properties of base elements -/

/-- The incoming flag at each edge is actually incoming. -/
private theorem matchedInFlag_isIn (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (e : { x : Fin (edgeCount W) // x ∈ edgeIndexSet W F }) :
    o.isOut (matchedInFlag o e).val = false := by
  unfold matchedInFlag
  by_cases ho : o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) e.val)) = true
  · rw [ite_eq_left ho]
    have := o.pairing_flip _ (repMem_of_partEdge e.prop)
    rw [pairing_starFlagEnum_symm] at this
    rw [this, ho]; rfl
  · rw [ite_eq_right ho]
    cases hb : o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) e.val))
    · rfl
    · exact absurd hb ho

/-- Elements of globalBase are incoming. -/
private theorem globalBase_isIn (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (f : {f : W.Flag // f ∈ F.flags}) (hf : f ∈ globalBase W F o) :
    o.isOut f.val = false := by
  rw [globalBase, List.mem_flatMap] at hf
  obtain ⟨v, _, hfv⟩ := hf
  have : f.val ∈ F.inFlagsAt o (blockVertex W v) := by
    rw [show (F.inFlagsAt o (blockVertex W v)).attachWith (· ∈ F.flags)
        (fun _ hf => F.mem_of_mem_inFlagsAt hf) =
      (F.inFlagsAt o (blockVertex W v)).pmap Subtype.mk
        (fun _ hf => F.mem_of_mem_inFlagsAt hf) from rfl] at hfv
    obtain ⟨g, hg, hfg⟩ := List.mem_pmap.mp hfv
    rw [← congrArg Subtype.val hfg]; exact hg
  exact isOut_of_mem_inFlagsAt o this

/-- matchSub flips the isOut bit. -/
private theorem matchSub_flip_isOut {W : ClosedFragment} {F : EdgeSubset W}
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (f : {f : W.Flag // f ∈ F.flags}) :
    o.isOut (matchSub κ f).val = !(o.isOut f.val) := by
  exact o.match_flip f.val f.prop

/-! ## Nodup getElem? injection -/

/-- If a nodup list satisfies l[i]? = some x and l[j]? = some x, then i = j. -/
private theorem nodup_getElem?_inj {α : Type*} {l : List α} (hl : l.Nodup)
    {i j : ℕ} {x : α} (hi : l[i]? = some x) (hj : l[j]? = some x) :
    i = j := by
  have hilt : i < l.length := List.getElem?_eq_some_iff.mp hi |>.1
  have hjlt : j < l.length := List.getElem?_eq_some_iff.mp hj |>.1
  have hvi : l[i] = x := Option.some.inj
    (List.getElem?_eq_getElem hilt ▸ hi)
  have hvj : l[j] = x := Option.some.inj
    (List.getElem?_eq_getElem hjlt ▸ hj)
  exact hl.getElem_inj_iff.mp (hvi.trans hvj.symm)

/-! ## pairBlowup and sign -/

private def fin2ProdEquiv (n : ℕ) : Fin (2 * n) ≃ Fin 2 × Fin n where
  toFun p := (⟨p.val % 2, Nat.mod_lt _ (by omega)⟩,
              ⟨p.val / 2, by omega⟩)
  invFun q := ⟨2 * q.2.val + q.1.val, by
    have := q.1.isLt; have := q.2.isLt; omega⟩
  left_inv p := Fin.ext (by simp; omega)
  right_inv q := Prod.ext (Fin.ext (by simp; omega))
    (Fin.ext (by simp; omega))

private noncomputable def pairBlowup {n : ℕ} (ρ : Perm (Fin n)) :
    Perm (Fin (2 * n)) :=
  (fin2ProdEquiv n).symm.permCongr
    (prodCongrRight (fun _ : Fin 2 => ρ))

private theorem sign_pairBlowup {n : ℕ} (ρ : Perm (Fin n)) :
    Perm.sign (pairBlowup ρ) = 1 := by
  rw [pairBlowup, Perm.sign_permCongr, Perm.sign_prodCongrRight,
    Fin.prod_univ_two]
  rcases Int.units_eq_one_or (Perm.sign ρ) with h1 | h1 <;>
    rw [h1] <;> simp

/-! ## Half 1 infrastructure -/

/-- Pairing as a subtype-preserving function. -/
private noncomputable def pairingSub {W : ClosedFragment} {F : EdgeSubset W}
    (f : {f : W.Flag // f ∈ F.flags}) :
    {f : W.Flag // f ∈ F.flags} :=
  ⟨W.pairing f.val, F.pairing_mem _ f.prop⟩

/-- pairingSub of an incoming flag is outgoing. -/
private theorem pairingSub_isOut {W : ClosedFragment} {F : EdgeSubset W}
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (f : {f : W.Flag // f ∈ F.flags}) (hf : o.isOut f.val = false) :
    o.isOut (pairingSub f).val = true := by
  rw [pairingSub, o.pairing_flip f.val f.prop, hf]; rfl

/-- pairingSub is injective. -/
private theorem pairingSub_injective {W : ClosedFragment} {F : EdgeSubset W} :
    Function.Injective (pairingSub (F := F)) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  have hv := congrArg Subtype.val h
  simp only [pairingSub] at hv
  -- pairing is injective (it's an involution)
  have hab : a = b := by
    calc a = W.pairing (W.pairing a) := (W.pairing_invol a).symm
      _ = W.pairing (W.pairing b) := by rw [hv]
      _ = b := W.pairing_invol b
  exact Subtype.ext hab

-- As for the matched list, with the pairing in place of the
-- matching.
/-- The oriented pair list as a flatMap of the incoming-flag base. -/
private theorem orientedPairList_eq_flatMap (W : ClosedFragment) (F : EdgeSubset
  W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    orientedPairList W F o =
    (matchedBase W F o).flatMap (fun f => [f, pairingSub f]) := by
  rw [orientedPairList, matchedBase, List.flatMap_map]
  congr 1
  funext ⟨e, he⟩
  unfold matchedInFlag
  by_cases ho : o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) e)) = true
  · simp only [ho, ite_true]
    -- [partner, rep] = [partner, pairingSub partner]
    have hval : (starFlagEnum W).symm (Fin.castAdd (edgeCount W) e) =
        W.pairing ((starFlagEnum W).symm (Fin.natAdd (edgeCount W) e)) := by
      rw [← pairing_starFlagEnum_symm W e, W.pairing_invol]
    exact List.cons_eq_cons.mpr ⟨rfl,
      List.cons_eq_cons.mpr ⟨Subtype.ext hval, rfl⟩⟩
  · simp only [show o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) e)) = false from by
      cases h : o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) e)) <;> simp_all]
    -- [rep, partner] = [rep, pairingSub rep]
    exact List.cons_eq_cons.mpr ⟨rfl,
      List.cons_eq_cons.mpr ⟨Subtype.ext (pairing_starFlagEnum_symm W e).symm,
        rfl⟩⟩

/-- matchedBase is nodup. -/
private theorem matchedBase_nodup (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    (matchedBase W F o).Nodup := by
  rw [matchedBase]
  apply List.Nodup.map _ (attachWith_partEdges_nodup W F)
  intro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
  apply Subtype.ext
  have hv : (matchedInFlag o ⟨e₁, he₁⟩).val = (matchedInFlag o ⟨e₂, he₂⟩).val :=
    congrArg Subtype.val h
  unfold matchedInFlag at hv
  by_cases ho₁ : o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) e₁)) = true <;>
  by_cases ho₂ : o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) e₂)) = true
  · rw [ite_eq_left ho₁, ite_eq_left ho₂] at hv
    exact Fin.natAdd_injective _ _ ((starFlagEnum W).symm.injective hv)
  · rw [ite_eq_left ho₁, ite_eq_right ho₂] at hv
    exact absurd (congrArg Fin.val ((starFlagEnum W).symm.injective hv))
      (by simp [Fin.val_castAdd]; omega)
  · rw [ite_eq_right ho₁, ite_eq_left ho₂] at hv
    exact absurd (congrArg Fin.val ((starFlagEnum W).symm.injective hv))
      (by simp [Fin.val_castAdd]; omega)
  · rw [ite_eq_right ho₁, ite_eq_right ho₂] at hv
    exact Fin.castAdd_injective _ _ ((starFlagEnum W).symm.injective hv)

/-- Two getElem calls at the same index are equal regardless of bound proof. -/
private theorem getElem_val_irrel {α : Type*} (l : List α) {a b : Nat}
    (hab : a = b) (h₁ : a < l.length) (h₂ : b < l.length) :
    l[a]'h₁ = l[b]'h₂ := by
  subst hab; rfl

/-! ## Half 1: sign of oriented → matched = sign of outPerm -/

-- Raised budget: the index permutation between the two lists is
-- computed position by position, so both flat-map presentations
-- and the out-permutation unfold together.
private theorem walkPerm_pairingSub {W : ClosedFragment} {F : EdgeSubset W}
    (κ : F.TransitionSystem) (f : {g : W.Flag // g ∈ F.flags}) :
    κ.walkPerm (pairingSub f) = matchSub κ f := by
  apply Subtype.ext
  rw [EdgeSubset.TransitionSystem.walkPerm_val]
  change κ.match_ (W.pairing (W.pairing f.val)) = κ.match_ f.val
  rw [W.pairing_invol]

/-- **Half 1**: the sign of the index permutation from oriented to matched
equals the sign of the out-permutation. -/
theorem sign_listIndexPerm_oriented_matched (W : ClosedFragment) (F : EdgeSubset
  W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    Perm.sign (listIndexPerm (orientedPairList W F o) (matchedPairList W F o)
      (orientedPairList_nodup W F o) (matchedPairList_nodup' W F o)
      (fun x => ⟨fun _ => mem_matchedPairList' W F o x,
                  fun _ => mem_orientedPairList W F o x⟩)
      (len_oriented_eq_matched W F o)) =
    Perm.sign (κ.outPerm o) := by
  -- ═══════ SETUP: BOTH LISTS AS FLAT-MAPPED PAIR BLOCKS ═══════
  -- Oriented and matched lists share the base `mB`, each pairing it
  -- with a different partner map, so both have length `2 * mB.length`
  -- and known entries at even and odd positions.
  set O := orientedPairList W F o
  set M := matchedPairList W F o
  set τ := listIndexPerm O M (orientedPairList_nodup W F o)
    (matchedPairList_nodup' W F o)
    (fun x => ⟨fun _ => mem_matchedPairList' W F o x,
                fun _ => mem_orientedPairList W F o x⟩)
    (len_oriented_eq_matched W F o)
  set mB := matchedBase W F o
  have hO_eq : O = mB.flatMap (fun f => [f, pairingSub f]) :=
    orientedPairList_eq_flatMap W F o
  have hM_eq : M = mB.flatMap (fun f => [f, matchSub κ f]) :=
    matchedPairList_eq_flatMap W F o
  have hOlen : O.length = 2 * mB.length := by rw [hO_eq, len_flatMap_pair]
  have hMlen : M.length = 2 * mB.length := by rw [hM_eq, len_flatMap_pair]
  have hOMlen : O.length = M.length := by omega
  have hτ : ∀ (i : Fin O.length),
      M[(τ i).val]'(by have := (τ i).isLt; omega) = O[i.val] :=
    listIndexPerm_getElem O M _ _ _ _
  -- Helper: O[2k] and O[2k+1] from flatMap
  have hO_even : ∀ (k : ℕ) (hk : k < mB.length),
      O[2 * k]'(by omega) = mB[k] := by
    intro k hk; simp only [O, hO_eq]
    exact getElem_flatMap_pair_even mB id pairingSub k hk
  have hO_odd : ∀ (k : ℕ) (hk : k < mB.length),
      O[2 * k + 1]'(by omega) = pairingSub (mB[k]) := by
    intro k hk; simp only [O, hO_eq]
    exact getElem_flatMap_pair_odd mB id pairingSub k hk
  have hM_even : ∀ (k : ℕ) (hk : k < mB.length),
      M[2 * k]'(by omega) = mB[k] := by
    intro k hk; simp only [M, hM_eq]
    exact getElem_flatMap_pair_even mB id (matchSub κ) k hk
  have hM_odd : ∀ (k : ℕ) (hk : k < mB.length),
      M[2 * k + 1]'(by omega) = matchSub κ (mB[k]) := by
    intro k hk; simp only [M, hM_eq]
    exact getElem_flatMap_pair_odd mB id (matchSub κ) k hk
  -- ═══════ STAGE 1: τ FIXES THE EVEN POSITIONS ═══════
  have hτ_even : ∀ (k : ℕ) (hk : k < mB.length), (τ ⟨2 * k, by omega⟩).val =
      2 * k := by
    intro k hk
    have hkey := hτ ⟨2 * k, by omega⟩
    rw [hO_even k hk] at hkey
    have hMnd : M.Nodup := matchedPairList_nodup' W F o
    have h1 : (τ ⟨2 * k, by omega⟩).val < M.length := by
      have := (τ ⟨2 * k, by omega⟩).isLt; omega
    have h2 : 2 * k < M.length := by omega
    exact hMnd.getElem_inj_iff (hi := h1) (hj := h2) |>.mp
      (hkey.trans (hM_even k hk).symm)
  -- ═══════ STAGE 2: τ SENDS ODD POSITIONS TO ODD POSITIONS ═══════
  -- `pairingSub (mB[k])` is outgoing while every `mB[j]` is incoming,
  -- so the image cannot be an even position.
  have hτ_odd : ∀ (k : ℕ) (hk : k < mB.length), (τ ⟨2 * k + 1, by omega⟩).val %
    2 = 1 := by
    intro k hk
    have hkey := hτ ⟨2 * k + 1, by omega⟩
    rw [hO_odd k hk] at hkey
    -- hkey : M[(τ ⟨2*k+1, _⟩).val]'_ = pairingSub(mB[k])
    by_contra h_even
    have h_mod0 : (τ ⟨2 * k + 1, by omega⟩).val % 2 = 0 := by omega
    have hj_lt : (τ ⟨2 * k + 1, by omega⟩).val / 2 < mB.length := by omega
    -- Connect M at equal indices: τ(2k+1) = 2*(τ(2k+1)/2)
    have hMeq : M[(τ ⟨2 * k + 1, by omega⟩).val]'(by
        have := (τ ⟨2 * k + 1, by omega⟩).isLt; omega) =
        M[2 * ((τ ⟨2 * k + 1, by omega⟩).val / 2)]'(by omega) :=
      getElem_val_irrel M (by omega) _ _
    -- Chain: pairingSub(mB[k]) = M[τ(2k+1)] = M[2j] = mB[j]
    have hmatch : pairingSub (mB[k]) =
        mB[(τ ⟨2 * k + 1, by omega⟩).val / 2] :=
      hkey.symm.trans (hMeq.trans (hM_even _ hj_lt))
    -- pairingSub(mB[k]) is outgoing
    have hout : o.isOut (pairingSub (mB[k])).val = true := by
      apply pairingSub_isOut
      simp only [mB, matchedBase, List.getElem_map]
      exact matchedInFlag_isIn W F o _
    -- mB[j] is incoming
    have hin : o.isOut (mB[(τ ⟨2 * k + 1, by omega⟩).val / 2]).val = false := by
      simp only [mB, matchedBase, List.getElem_map]
      exact matchedInFlag_isIn W F o _
    rw [hmatch] at hout
    simp [hout] at hin
  -- ═══════ STAGE 3: THE ODD-BLOCK PERMUTATION ρ ═══════
  -- ρ(k) = τ(2k+1) / 2
  have hmBlen_pos : 0 < mB.length ∨ mB.length = 0 := by omega
  let ρ_fn : Fin mB.length → Fin mB.length := fun ⟨k, hk⟩ =>
    ⟨(τ ⟨2 * k + 1, by omega⟩).val / 2, by
      have := (τ ⟨2 * k + 1, by omega⟩).isLt
      have := hτ_odd k hk
      omega⟩
  have hρ_inj : Function.Injective ρ_fn := by
    intro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ h
    have hv := congrArg Fin.val h
    change (τ ⟨2 * k₁ + 1, by omega⟩).val / 2 =
        (τ ⟨2 * k₂ + 1, by omega⟩).val / 2 at hv
    have hodd₁ := hτ_odd k₁ hk₁
    have hodd₂ := hτ_odd k₂ hk₂
    have hτ_val_eq : (τ ⟨2 * k₁ + 1, by omega⟩).val =
        (τ ⟨2 * k₂ + 1, by omega⟩).val := by omega
    have hinj := τ.injective (Fin.ext hτ_val_eq)
    have hval : 2 * k₁ + 1 = 2 * k₂ + 1 := congrArg Fin.val hinj
    have hk_eq : k₁ = k₂ := by omega
    subst hk_eq; rfl
  let ρ : Perm (Fin mB.length) :=
    Equiv.ofBijective ρ_fn (Finite.injective_iff_bijective.mp hρ_inj)
  -- ═══════ STAGE 4: τ IS THE PAIR BLOW-UP OF ρ ═══════
  -- τ = permCongr(finCongr)(permCongr(fin2ProdEquiv⁻¹)(prodCongrRight
  --   ![1, ρ]))
  have hτ_eq : τ = (finCongr hOlen).symm.permCongr
      ((fin2ProdEquiv mB.length).symm.permCongr
        (prodCongrRight (![(1 : Perm (Fin mB.length)), ρ]))) := by
    ext j
    -- The permCongr/finCongr/fin2ProdEquiv chain is definitionally transparent
    change (τ j).val = 2 * ((![(1 : Perm (Fin mB.length)), ρ]
      ⟨j.val % 2, Nat.mod_lt _ (by omega)⟩
      ⟨j.val / 2, by omega⟩).val) + j.val % 2
    rcases Nat.even_or_odd j.val with ⟨k, hk_eq⟩ | ⟨k, hk_eq⟩
    · -- Even: j.val = k + k
      have hk_lt : k < mB.length := by omega
      have htj : (τ j).val = j.val := by
        have hconn : (τ j).val = (τ ⟨2 * k, by omega⟩).val :=
          Fin.val_eq_of_eq (congrArg τ (Fin.ext (show j.val = 2 * k by omega)))
        rw [hconn, hτ_even k hk_lt]; omega
      simp only [htj, show j.val % 2 = 0 from by omega]
      -- ![1, ρ] ⟨0, _⟩ = 1 and (1 x).val = x.val, all definitional
      change j.val = 2 * (j.val / 2) + 0
      omega
    · -- Odd: j.val = 2*k + 1
      have hk_lt : k < mB.length := by omega
      simp only [show j.val % 2 = 1 from by omega]
      -- ![1, ρ] ⟨1, _⟩ = ρ, ρ x = ρ_fn x (all definitional via let)
      change (τ j).val = 2 * ((τ ⟨2 * (j.val / 2) + 1, by omega⟩).val / 2) + 1
      have hconn : (τ j).val = (τ ⟨2 * k + 1, by omega⟩).val :=
        Fin.val_eq_of_eq
          (congrArg τ (Fin.ext (show j.val = 2 * k + 1 by omega)))
      have hconn2 : (τ ⟨2 * (j.val / 2) + 1, by omega⟩).val =
          (τ ⟨2 * k + 1, by omega⟩).val :=
        Fin.val_eq_of_eq
          (congrArg τ (Fin.ext (show 2 * (j.val / 2) + 1 = 2 * k + 1 by omega)))
      have hodd := hτ_odd k hk_lt
      omega
  -- ═══════ STAGE 5: sign τ = sign ρ ═══════
  rw [hτ_eq, Perm.sign_permCongr, Perm.sign_permCongr,
      Perm.sign_prodCongrRight, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Perm.sign_one, one_mul]
  -- Goal: Perm.sign ρ = Perm.sign (κ.outPerm o)
  -- Key relationship: matchSub(mB[ρ(j)]) = pairingSub(mB[j])
  have hρ_rel : ∀ (j : Fin mB.length),
      matchSub κ (mB[(ρ j).val]'(ρ j).isLt) =
      pairingSub (mB[j.val]'j.isLt) := by
    intro ⟨j, hj⟩
    have h1 := hτ ⟨2 * j + 1, by omega⟩
    rw [hO_odd j hj] at h1
    have hodd := hτ_odd j hj
    have hτ_val : (τ ⟨2 * j + 1, by omega⟩).val = 2 * (ρ ⟨j, hj⟩).val + 1 := by
      change (τ ⟨2 * j + 1, by omega⟩).val =
        2 * ((τ ⟨2 * j + 1, by omega⟩).val / 2) + 1
      omega
    have h2 := getElem_val_irrel M hτ_val
        (by have := (τ ⟨2 * j + 1, by omega⟩).isLt; omega)
        (by omega)
    have h3 := hM_odd (ρ ⟨j, hj⟩).val (ρ ⟨j, hj⟩).isLt
    exact h3.symm.trans (h2.symm.trans h1)
  -- ═══════ STAGE 6: ρ IS CONJUGATE TO THE OUT-PERMUTATION ═══════
  -- Define e : Fin mB.length → {out-flags}
  let e_fn : Fin mB.length →
      {f : {g : W.Flag // g ∈ F.flags} // o.isOut f.val = true} :=
    fun ⟨k, hk⟩ => ⟨pairingSub (mB[k]'hk), by
      apply pairingSub_isOut
      simp only [mB, matchedBase, List.getElem_map]
      exact matchedInFlag_isIn W F o _⟩
  have e_inj : Function.Injective e_fn := by
    intro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ h
    have hv : pairingSub (mB[k₁]) = pairingSub (mB[k₂]) :=
      congrArg Subtype.val h
    have hps := pairingSub_injective hv
    exact Fin.ext ((matchedBase_nodup W F o).getElem_inj_iff.mp hps)
  have e_surj : Function.Surjective e_fn := by
    intro ⟨f, hf_out⟩
    have hf_mem : f ∈ O := mem_orientedPairList W F o f
    rw [hO_eq] at hf_mem
    simp only [List.mem_flatMap, List.mem_cons,
      List.mem_nil_iff, or_false] at hf_mem
    obtain ⟨g, hg_mem, rfl | rfl⟩ := hf_mem
    · -- g is incoming (in mB), contradiction with hf_out
      exfalso
      simp only [mB, matchedBase, List.mem_map] at hg_mem
      obtain ⟨e, _, rfl⟩ := hg_mem
      exact absurd hf_out (by simp [matchedInFlag_isIn W F o e])
    · -- f = pairingSub g, find g's index in mB
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hg_mem
      exact ⟨⟨k, hk_lt⟩, Subtype.ext (congrArg pairingSub hk_eq)⟩
  let e : Fin mB.length ≃
      {f : {g : W.Flag // g ∈ F.flags} // o.isOut f.val = true} :=
    Equiv.ofBijective e_fn ⟨e_inj, e_surj⟩
  -- Helper: walkPerm ∘ pairingSub = matchSub on matched base
  have hwalk_eq : ∀ (k : ℕ) (hk : k < mB.length),
      κ.walkPerm (pairingSub (mB[k]'hk)) = matchSub κ (mB[k]'hk) := by
    exact fun k hk => walkPerm_pairingSub κ (mB[k]'hk)
  -- Pointwise conjugation: outPerm(e_fn(j)) = e_fn(ρ⁻¹(j))
  have hconj_fn : ∀ (j : Fin mB.length),
      (κ.outPerm o) (e_fn j) = e_fn (ρ⁻¹ j) := by
    intro ⟨k, hk⟩
    apply Subtype.ext
    simp only [EdgeSubset.TransitionSystem.outPerm, Perm.subtypePerm_apply]
    -- Goal: walkPerm(pairingSub(mB[k])) = pairingSub(mB[(ρ⁻¹ k).val])
    rw [hwalk_eq k hk]
    -- Goal: matchSub κ (mB[k]) = pairingSub(mB[(ρ⁻¹ k).val])
    have hrel := hρ_rel (ρ⁻¹ ⟨k, hk⟩)
    rwa [show (ρ (ρ⁻¹ ⟨k, hk⟩) : Fin mB.length) = ⟨k, hk⟩
      from ρ.apply_symm_apply _] at hrel
  -- Permutation conjugation: e.permCongr ρ⁻¹ = outPerm
  have hperm_conj : e.permCongr ρ⁻¹ = κ.outPerm o := by
    ext1 x
    simp only [Equiv.permCongr_apply]
    -- Goal: e (ρ⁻¹ (e.symm x)) = (κ.outPerm o) x
    have h := hconj_fn (e.symm x)
    rw [show (e_fn (e.symm x) :
        {f : {g : W.Flag // g ∈ F.flags} // o.isOut f.val = true}) = x
      from e.apply_symm_apply x] at h
    exact h.symm
  -- sign(ρ) = sign(ρ⁻¹) = sign(e.permCongr ρ⁻¹) = sign(outPerm)
  calc Perm.sign ρ
      = Perm.sign ρ⁻¹ := (Perm.sign_inv ρ).symm
    _ = Perm.sign (e.permCongr ρ⁻¹) := (Perm.sign_permCongr e ρ⁻¹).symm
    _ = Perm.sign (κ.outPerm o) := congrArg Perm.sign hperm_conj

/-! ## Half 2: sign of matched → global = 1 -/

-- As for the first half: the index permutation is computed
-- position by position, here to show it is even.
/-- **Half 2**: the sign of the index permutation from matched to
global pair list is +1. -/
theorem sign_listIndexPerm_matched_global (W : ClosedFragment) (F : EdgeSubset
  W)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    Perm.sign (listIndexPerm (matchedPairList W F o) (globalPairList W F o)
      (matchedPairList_nodup' W F o) (globalPairList_nodup' W F o)
      (fun x => ⟨fun _ => mem_globalPairList' W F o x,
                  fun _ => mem_matchedPairList' W F o x⟩)
      (len_matched_eq_global W F o)) =
    1 := by
  -- ═══════ SETUP: BOTH LISTS AS FLAT-MAPPED PAIR BLOCKS ═══════
  -- Matched and global lists pair their own bases with the same
  -- partner map, so both split into two-element blocks.
  set M := matchedPairList W F o
  set G := globalPairList W F o
  have hM : M.Nodup := matchedPairList_nodup' W F o
  have hG : G.Nodup := globalPairList_nodup' W F o
  have hmem : ∀ x, x ∈ M ↔ x ∈ G := fun x =>
    ⟨fun _ => mem_globalPairList' W F o x,
     fun _ => mem_matchedPairList' W F o x⟩
  have hlen : M.length = G.length := len_matched_eq_global W F o
  set τ := listIndexPerm M G hM hG hmem hlen
  -- Key property of τ: G[(τ i).val] = M[i.val]
  have hτ : ∀ i : Fin M.length,
      G[(τ i).val]'(by have := (τ i).isLt; omega) = M[i.val] :=
    listIndexPerm_getElem M G hM hG hmem hlen
  -- Abbreviations for base lists
  set mB := matchedBase W F o
  set gB := globalBase W F o
  -- matched = mB.flatMap(fun f => [f, matchSub κ f])
  have hMeq : M = mB.flatMap (fun f => [f, matchSub κ f]) :=
    matchedPairList_eq_flatMap W F o
  -- global = gB.flatMap(fun f => [f, matchSub κ f])
  have hGeq : G = gB.flatMap (fun f => [f, matchSub κ f]) :=
    globalPairList_eq_flatMap W F o
  -- Length facts
  have hMlen : M.length = 2 * mB.length := by
    rw [hMeq]; exact len_flatMap_pair mB id (matchSub κ)
  have hGlen : G.length = 2 * gB.length := by
    rw [hGeq]; exact len_flatMap_pair gB id (matchSub κ)
  have hBlen : mB.length = gB.length := by omega
  -- Pairing: M[2k+1]? = M[2k]?.map matchSub
  have hMpair : ∀ j, M[2 * j + 1]? = M[2 * j]?.map (matchSub κ) :=
    matchedPairList_paired W F o
  -- Pairing: G[2j+1]? = G[2j]?.map matchSub
  have hGpair : ∀ j, G[2 * j + 1]? = G[2 * j]?.map (matchSub κ) :=
    globalPairList_paired W F o
  -- For each even index 2k in M, the element is from matchedBase (incoming)
  -- M[2k] = mB[k], M[2k+1] = matchSub(mB[k])
  -- For each even index 2j in G, the element is from globalBase (incoming)
  -- G[2j] = gB[j], G[2j+1] = matchSub(gB[j])
  -- ═══════ STAGE 1: BOTH BASES ARE INCOMING, THE PARTNER FLIPS ═══════
  -- Step 1: matchedBase elements are incoming
  have hmB_in : ∀ e : { x // x ∈ edgeIndexSet W F },
      o.isOut (matchedInFlag o e).val = false :=
    matchedInFlag_isIn W F o
  -- Step 2: globalBase elements are incoming
  have hgB_in : ∀ f, f ∈ gB → o.isOut f.val = false :=
    globalBase_isIn W F o
  -- Step 3: matchSub flips isOut
  have hflip : ∀ f : {f : W.Flag // f ∈ F.flags},
      o.isOut (matchSub κ f).val = !(o.isOut f.val) :=
    matchSub_flip_isOut o
  -- ═══════ STAGE 2: BLOCK STRUCTURE SUFFICES ═══════
  -- Granting that τ carries each two-element block onto a block, the
  -- sign is the blow-up of a permutation of blocks, hence even.
  suffices hblock : ∀ (k : ℕ) (hk : k < mB.length),
      (τ ⟨2 * k, by omega⟩).val % 2 = 0 ∧
      (τ ⟨2 * k + 1, by omega⟩).val = (τ ⟨2 * k, by omega⟩).val + 1 by
    -- Extract individual facts
    have heven : ∀ (k : ℕ) (hk : k < mB.length),
        (τ ⟨2 * k, by omega⟩).val % 2 = 0 := fun k hk => (hblock k hk).1
    have hpair : ∀ (k : ℕ) (hk : k < mB.length),
        (τ ⟨2 * k + 1, by omega⟩).val = (τ ⟨2 * k, by omega⟩).val + 1 :=
      fun k hk => (hblock k hk).2
    -- Define σ(k) = τ(2k) / 2
    have hσ_bound : ∀ (k : ℕ) (hk : k < mB.length),
        (τ ⟨2 * k, by omega⟩).val / 2 < mB.length := fun k hk => by
      have := (τ ⟨2 * k, by omega⟩).isLt; omega
    let σ_fn : Fin mB.length → Fin mB.length := fun ⟨k, hk⟩ =>
      ⟨(τ ⟨2 * k, by omega⟩).val / 2, hσ_bound k hk⟩
    have hσ_inj : Function.Injective σ_fn := by
      intro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ heq
      have h₁ := heven k₁ hk₁
      have h₂ := heven k₂ hk₂
      have hveq : (τ ⟨2 * k₁, by omega⟩).val / 2 =
          (τ ⟨2 * k₂, by omega⟩).val / 2 := Fin.mk.inj heq
      have hτeq : (τ ⟨2 * k₁, by omega⟩).val =
          (τ ⟨2 * k₂, by omega⟩).val := by omega
      have h2keq := Fin.val_eq_of_eq (τ.injective (Fin.ext hτeq))
      change 2 * k₁ = 2 * k₂ at h2keq
      exact Fin.ext (show k₁ = k₂ by omega)
    let σ : Perm (Fin mB.length) :=
      Equiv.ofBijective σ_fn
        ⟨hσ_inj, (Finite.injective_iff_surjective.mp hσ_inj)⟩
    -- τ = (finCongr hMlen).symm.permCongr (pairBlowup σ)
    have hτ_eq : τ = (finCongr hMlen).symm.permCongr (pairBlowup σ) := by
      ext j
      -- Unfold permCongr: e.permCongr p x = e (p (e.symm x))
      -- The permCongr_apply simp lemma should fire but may not work here.
      -- Instead, compute directly using suffices.
      -- The permCongr + finCongr on the RHS is transparent to .val
      -- The permCongr/finCongr and σ/σ_fn are all definitionally transparent
      change (τ j).val = 2 * ((τ ⟨2 * (j.val / 2), by omega⟩).val / 2) + j.val %
        2
      -- Case split on parity of j.val
      rcases Nat.even_or_odd j.val with ⟨k, hk_eq⟩ | ⟨k, hk_eq⟩
      · -- j.val = 2k: τ(j) = τ(⟨2k,_⟩), and 2*(j/2) = 2k
        have htj : (τ j).val = (τ ⟨2 * k, by omega⟩).val :=
          Fin.val_eq_of_eq (congrArg τ (Fin.ext (show j.val = 2 * k by omega)))
        have hconn : (τ ⟨2 * (j.val / 2), by omega⟩).val =
          (τ ⟨2 * k, by omega⟩).val :=
          Fin.val_eq_of_eq
            (congrArg τ (Fin.ext (show 2 * (j.val / 2) = 2 * k by omega)))
        have hev := heven k (by omega)
        have hjm : j.val % 2 = 0 := by omega
        omega
      · -- j.val = 2k+1: use hpair
        have htj : (τ j).val = (τ ⟨2 * k + 1, by omega⟩).val :=
          Fin.val_eq_of_eq
            (congrArg τ (Fin.ext (show j.val = 2 * k + 1 by omega)))
        have hconn : (τ ⟨2 * (j.val / 2), by omega⟩).val =
          (τ ⟨2 * k, by omega⟩).val :=
          Fin.val_eq_of_eq
            (congrArg τ (Fin.ext (show 2 * (j.val / 2) = 2 * k by omega)))
        have hev := heven k (by omega)
        have hpr := hpair k (by omega)
        have hjm : j.val % 2 = 1 := by omega
        omega
    rw [hτ_eq, Equiv.Perm.sign_permCongr, sign_pairBlowup]
  -- ═══════ STAGE 3: THE BLOCK CLAIM ═══════
  -- The image of an even position is even (both entries are incoming,
  -- and only even positions carry incoming flags), and the odd
  -- position of a block follows its even one.
  intro k hk
  have h2k_lt : 2 * k < M.length := by omega
  have h2k1_lt : 2 * k + 1 < M.length := by omega
  set m := (τ ⟨2 * k, h2k_lt⟩).val
  set m1 := (τ ⟨2 * k + 1, h2k1_lt⟩).val
  have hGm : G[m]'(by have := (τ ⟨2 * k, h2k_lt⟩).isLt; omega) = M[2 * k] :=
    hτ ⟨2 * k, h2k_lt⟩
  have hGm1 : G[m1]'(by have := (τ ⟨2 * k + 1, h2k1_lt⟩).isLt; omega) =
    M[2 * k + 1] :=
    hτ ⟨2 * k + 1, h2k1_lt⟩
  have hM_pair_k : M[2 * k + 1]? = (M[2 * k]?).map (matchSub κ) := hMpair k
  have h2k_bound : 2 * k < M.length := h2k_lt
  have h2k1_bound : 2 * k + 1 < M.length := h2k1_lt
  rw [List.getElem?_eq_getElem h2k_bound,
      List.getElem?_eq_getElem h2k1_bound] at hM_pair_k
  have hM2k1_eq : M[2 * k + 1] = matchSub κ (M[2 * k]) :=
    Option.some.inj hM_pair_k
  -- M[2k] = mB[k] (incoming)
  have hM2k_even : M[2 * k]? = (mB[k]?).map id := by
    have key : (fun x : {f : W.Flag // f ∈ F.flags} =>
        ([x, matchSub κ x] : List _)) =
      fun x => [id x, matchSub κ x] := by ext; simp
    rw [hMeq, key]; exact getElem?_flatMap_pair_even mB id (matchSub κ) k
  rw [List.getElem?_eq_getElem h2k_bound, List.getElem?_eq_getElem hk]
    at hM2k_even
  have hM2k_is_mBk : M[2 * k] = mB[k] := by
    have := Option.some.inj hM2k_even; simp? at this; exact this
  have hmBk_in : o.isOut (mB[k]'hk).val = false := by
    simp only [mB, matchedBase, List.getElem_map]
    exact matchedInFlag_isIn W F o _
  have hM2k_in : o.isOut (M[2 * k]'h2k_bound).val = false := by
    rw [hM2k_is_mBk]; exact hmBk_in
  have hGm_in : o.isOut (G[m]'(by have := (τ ⟨2 * k, h2k_lt⟩).isLt; omega)).val
    = false := by
    rw [hGm, hM2k_in]
  -- Evenness: m = τ(2k) is even
  have hm_even : m % 2 = 0 := by
    by_contra hm_odd
    have hm_odd' : m % 2 = 1 := by omega
    set j := m / 2
    have hm_eq : m = 2 * j + 1 := by omega
    have hj_lt : j < gB.length := by
      have : m < M.length := (τ ⟨2 * k, h2k_lt⟩).isLt; omega
    have hGm_odd_eq : G[m]? = (gB[j]?).map (matchSub κ) := by
      rw [hm_eq, hGeq]
      exact getElem?_flatMap_pair_odd gB id (matchSub κ) j
    rw [List.getElem?_eq_getElem (by have := (τ ⟨2 * k, h2k_lt⟩).isLt; omega),
        List.getElem?_eq_getElem hj_lt] at hGm_odd_eq
    have hGm_eq_matchSub : G[m] = matchSub κ (gB[j]) :=
      Option.some.inj hGm_odd_eq
    have : o.isOut (G[m]'(by have := (τ ⟨2 * k, h2k_lt⟩).isLt; omega)).val =
      true := by
      rw [hGm_eq_matchSub, hflip]
      have : o.isOut (gB[j]'hj_lt).val = false :=
        hgB_in _ (List.getElem_mem hj_lt)
      rw [this]; rfl
    rw [hGm_in] at this; exact Bool.noConfusion this
  -- Pairing: m1 = m + 1
  refine ⟨hm_even, ?_⟩
  set j := m / 2
  have hm_eq : m = 2 * j := by omega
  have hm_bound : m < M.length := (τ ⟨2 * k, h2k_lt⟩).isLt
  have hj_lt : j < gB.length := by omega
  have hGpair_j : G[2 * j + 1]? = G[2 * j]?.map (matchSub κ) := hGpair j
  have h2j_lt : 2 * j < G.length := by omega
  have h2j1_lt : 2 * j + 1 < G.length := by omega
  rw [List.getElem?_eq_getElem h2j_lt,
      List.getElem?_eq_getElem h2j1_lt] at hGpair_j
  have hG2j1 : G[2 * j + 1] = matchSub κ (G[2 * j]) :=
    Option.some.inj hGpair_j
  have hG2j_eq : G[2 * j]'h2j_lt = M[2 * k] := by
    convert hGm using 1; congr 1; omega
  have hG2j1_eq : G[2 * j + 1]'h2j1_lt = M[2 * k + 1] := by
    rw [hG2j1, hG2j_eq, hM2k1_eq]
  have hm1_eq : m1 = 2 * j + 1 := by
    have hGm1_opt : G[m1]? = some (M[2 * k + 1]) := by
      rw [List.getElem?_eq_getElem
        (by have := (τ ⟨2 * k + 1, h2k1_lt⟩).isLt; omega)]
      exact congrArg some hGm1
    have hG2j1_opt : G[2 * j + 1]? = some (M[2 * k + 1]) := by
      rw [List.getElem?_eq_getElem h2j1_lt]
      exact congrArg some hG2j1_eq
    exact nodup_getElem?_inj hG hGm1_opt hG2j1_opt
  change m1 = m + 1
  rw [hm1_eq, hm_eq]

end RS
