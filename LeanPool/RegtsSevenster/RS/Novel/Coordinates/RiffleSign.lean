/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PairList
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.EdgeSign

/-!
# The riffle and orientation signs

The canonical index permutation from slot-order to edge-interleaved
order has sign `(−1)^C(n,2)` (the riffle sign), and the permutation
from edge-interleaved to oriented order has sign `(−1)^s` where `s`
is the number of edges whose representative flag is outgoing.
-/

namespace RS

open Finset

variable {k ℓ : ℕ}

/-! ### Part 1 helpers: slot-map computations -/

open Classical in
/-- The slot function applied to globalSlotList recovers sorted partSlots. -/
private theorem globalSlotList_map_slot (W : ClosedFragment)
    (F : EdgeSubset W) :
    (globalSlotList W F).map (fun f : {f : W.Flag // f ∈ F.flags} =>
      starFlagEnum W f.val) =
    (partSlots W F).sort (· ≤ ·) := by
  apply List.ext_getElem (by rw [List.length_map]; exact List.length_pmap)
  intro i hi₁ hi₂
  rw [List.getElem_map]
  unfold globalSlotList at hi₁ ⊢
  rw [List.getElem_pmap]
  exact _root_.Equiv.apply_symm_apply _ _

open Classical in
/-- The slot-mapped global slot list is nodup (needed for sortSign). -/
private theorem globalSlotList_map_slot_nodup (W : ClosedFragment)
    (F : EdgeSubset W) :
    ((globalSlotList W F).map (fun f : {f : W.Flag // f ∈ F.flags} =>
      starFlagEnum W f.val)).Nodup := by
  rw [globalSlotList_map_slot]
  exact Finset.sort_nodup _ _

open Classical in
/-- The slot-mapped global slot list has sortSign 1 (sorted). -/
private theorem sortSign_globalSlotList_map_slot (W : ClosedFragment)
    (F : EdgeSubset W) :
    sortSign ((globalSlotList W F).map (fun f : {f : W.Flag // f ∈ F.flags} =>
      starFlagEnum W f.val)) = 1 := by
  rw [globalSlotList_map_slot]
  exact sortSign_eq_one_of_sorted _
    (Finset.pairwise_sort (partSlots W F) (· ≤ ·))

open Classical in
/-- The slot function maps edgePairList to the interleaved list. -/
private theorem edgePairList_map_slot (W : ClosedFragment)
    (F : EdgeSubset W) :
    (edgePairList W F).map (fun f : {f : W.Flag // f ∈ F.flags} =>
      starFlagEnum W f.val) =
    (partEdges W F).flatMap (fun e =>
      [Fin.castAdd (edgeCount W) e, Fin.natAdd (edgeCount W) e]) := by
  rw [edgePairList, List.map_flatMap]
  simp only [List.map_cons, List.map_nil, _root_.Equiv.apply_symm_apply]
  -- attachWith.flatMap (fun i => [castAdd i.val, natAdd i.val])
  -- = partEdges.flatMap (fun e => [castAdd e, natAdd e])
  -- Prove by a general attachWith-flatMap lemma via induction
  suffices h : ∀ (l : List (Fin (edgeCount W)))
      (H : ∀ x ∈ l, x ∈ edgeIndexSet W F),
      (l.attachWith (· ∈ edgeIndexSet W F) H).flatMap
        (fun i : {i : Fin (edgeCount W) // i ∈ edgeIndexSet W F} =>
          [Fin.castAdd (edgeCount W) i.val, Fin.natAdd (edgeCount W) i.val]) =
      l.flatMap (fun e => [Fin.castAdd (edgeCount W) e,
        Fin.natAdd (edgeCount W) e]) from h _ _
  intro l H
  induction l with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.attachWith, List.pmap_cons, List.flatMap_cons]
    exact congrArg _ (ih (fun x hx => H x (List.mem_cons_of_mem _ hx)))

/-! ### Part 1 helpers: inversions of interleaved lists -/

/-- All entries of the castAdd-natAdd interleave over a tail strictly
    greater than the head are ≥ castAdd of the head. -/
private theorem filter_lt_castAdd_head_eq_zero {n : ℕ}
    (e : Fin n) (rest : List (Fin n))
    (hgt : ∀ x ∈ rest, e < x) :
    ((rest.flatMap (fun i => [Fin.castAdd n i, Fin.natAdd n i])).filter
      (fun b => decide (b < Fin.castAdd n e))).length = 0 := by
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro q hq
  simp only [decide_eq_true_eq, not_lt]
  rw [List.mem_flatMap] at hq
  obtain ⟨x, hx, hq⟩ := hq
  rcases List.mem_cons.mp hq with rfl | hq
  · -- q = castAdd x, x > e
    change (Fin.castAdd n e).val ≤ (Fin.castAdd n x).val
    simp only [Fin.val_castAdd]
    exact Nat.le_of_lt (hgt x hx)
  · -- q = natAdd x
    rw [List.mem_singleton] at hq; subst hq
    change (Fin.castAdd n e).val ≤ (Fin.natAdd n x).val
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    have := e.isLt; omega

/-- natAdd e is not less than castAdd e. -/
private theorem not_natAdd_lt_castAdd {n : ℕ} (e : Fin n) :
    ¬ (Fin.natAdd n e < Fin.castAdd n e) := by
  intro h
  have h1 : (Fin.natAdd n e).val < (Fin.castAdd n e).val :=
    h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at h1
  omega

/-- The count of tail entries less than natAdd of the head equals
    the number of elements in rest (from castAdd entries). -/
private theorem filter_lt_natAdd_head_eq_length {n : ℕ}
    (e : Fin n) (rest : List (Fin n))
    (hgt : ∀ x ∈ rest, e < x) :
    ((rest.flatMap (fun i => [Fin.castAdd n i, Fin.natAdd n i])).filter
      (fun b => decide (b < Fin.natAdd n e))).length = rest.length := by
  -- Each element of rest contributes castAdd x (< natAdd e since x.val < n ≤ n
  --   + e.val)
  -- and natAdd x (≥ natAdd e since x > e)
  -- So exactly one element per rest entry passes the filter
  induction rest with
  | nil => simp [List.flatMap]
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filter_append, List.length_append,
      List.length_cons]
    have hx_gt : e < x := hgt x List.mem_cons_self
    have hxs_gt : ∀ y ∈ xs, e < y := fun y hy => hgt y
      (List.mem_cons_of_mem _ hy)
    rw [ih hxs_gt]
    -- Filter of [castAdd x, natAdd x]: castAdd x passes, natAdd x doesn't
    change (([Fin.castAdd n x, Fin.natAdd n x].filter
      (fun b => decide (b < Fin.natAdd n e)))).length + xs.length =
      xs.length + 1
    -- castAdd x < natAdd e: castAdd x = x.val < n ≤ n + e.val = natAdd e
    have hcast_lt : Fin.castAdd n x < Fin.natAdd n e := by
      change (Fin.castAdd n x).val < (Fin.natAdd n e).val
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      exact x.isLt.trans_le (Nat.le_add_right _ _)
    -- natAdd x ≥ natAdd e: n + x.val > n + e.val
    have hnat_ge : ¬ (Fin.natAdd n x < Fin.natAdd n e) := by
      intro h
      have h1 : (Fin.natAdd n x).val < (Fin.natAdd n e).val := h
      simp only [Fin.val_natAdd] at h1; omega
    simp only [List.filter_cons, decide_eq_true_eq, hcast_lt, ite_true,
      hnat_ge, ite_false, List.filter_nil, List.length_cons, List.length_nil]
    omega

/-- Inversions of the castAdd-natAdd interleave of a strictly sorted
    list equal `Nat.choose n 2`. -/
private theorem inversions_interleave_sorted {n : ℕ} :
    ∀ (E : List (Fin n)), List.Pairwise (· < ·) E →
    inversions (E.flatMap (fun i => [Fin.castAdd n i, Fin.natAdd n i])) =
    Nat.choose E.length 2
  | [], _ => by simp [List.flatMap, inversions]
  | e :: rest, hpw => by
    have hrest := hpw.of_cons
    have hgt : ∀ x ∈ rest, e < x :=
      (List.pairwise_cons.mp hpw).1
    rw [List.flatMap_cons]
    simp only [List.cons_append, List.nil_append]
    -- inversions (castAdd e :: natAdd e :: rest_fm)
    -- = filter(< castAdd e)(natAdd e :: rest_fm).length + inversions(natAdd e
    --   :: rest_fm)
    set rest_fm := rest.flatMap (fun i => [Fin.castAdd n i, Fin.natAdd n i])
    -- Unfold inversions for the cons case (definitional equality)
    change ((Fin.natAdd n e :: rest_fm).filter
        (fun b => decide (b < Fin.castAdd n e))).length +
      ((rest_fm.filter (fun b => decide (b < Fin.natAdd n e))).length +
        inversions rest_fm) = _
    -- Filter for castAdd e: nothing in (natAdd e :: rest_fm) is < castAdd e
    have h_filt_cast : ((Fin.natAdd n e :: rest_fm).filter
        (fun b => decide (b < Fin.castAdd n e))).length = 0 := by
      rw [List.filter_cons]
      simp only [decide_eq_true_eq, not_natAdd_lt_castAdd, ite_false]
      exact filter_lt_castAdd_head_eq_zero e rest hgt
    rw [h_filt_cast, Nat.zero_add]
    -- filter(< natAdd e)(rest_fm).length = rest.length
    rw [filter_lt_natAdd_head_eq_length e rest hgt]
    -- inversions(rest_fm) = C(rest.length, 2) by IH
    rw [inversions_interleave_sorted rest hrest]
    -- rest.length + C(rest.length, 2) = C(rest.length + 1, 2)
    rw [List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right]

open Classical in
/-- The interleaved slot list from edgePairList has inversions equal
    to `Nat.choose n 2` where `n` = number of participating edges. -/
private theorem inversions_edgePairList_slots (W : ClosedFragment)
    (F : EdgeSubset W) :
    inversions ((edgePairList W F).map (fun f : {f : W.Flag // f ∈ F.flags} =>
      starFlagEnum W f.val)) =
    Nat.choose (partEdges W F).length 2 := by
  rw [edgePairList_map_slot]
  exact inversions_interleave_sorted (partEdges W F)
    (List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort (edgeIndexSet W F)))

open Classical in
/-- The length of partEdges equals the card of edgeIndexSet. -/
private theorem partEdges_length (W : ClosedFragment) (F : EdgeSubset W) :
    (partEdges W F).length = (edgeIndexSet W F).card := by
  exact Finset.length_sort _

/-! ### Part 1 helpers: crossings count -/

/-- Ordered pairs from a finset biject with choose 2. -/
private theorem card_ordered_pairs_eq_choose {α : Type*}
    [LinearOrder α] (S : Finset α) :
    ((S ×ˢ S).filter (fun p => p.1 < p.2)).card =
    Nat.choose S.card 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    -- Split into pairs involving a and pairs within s
    have hfilt_sum : (s.filter (fun x => a < x)).card +
        (s.filter (fun x => x < a)).card = s.card := by
      have h1 := Finset.card_filter_add_card_filter_not (s := s)
        (fun x => a < x)
      have h2 : (s.filter (fun x => ¬ a < x)).card =
          (s.filter (fun x => x < a)).card := by
        congr 1; ext x; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hx, hna⟩; exact ⟨hx, lt_of_le_of_ne (not_lt.mp hna)
            (fun h => ha (h ▸ hx))⟩
        · rintro ⟨hx, hlt⟩; exact ⟨hx, not_lt.mpr (le_of_lt hlt)⟩
      omega
    -- Count pairs: pairs with a on left + pairs with a on right + pairs in s
    -- = s.filter(a<·).card + s.filter(·<a).card + old = s.card + old
    -- The new pairs are exactly those (a,y) with a < y and (x,a) with x < a
    have hsplit : ((insert a s ×ˢ insert a s).filter
        (fun p : α × α => p.1 < p.2)).card =
      (s.filter (fun x => a < x)).card +
      (s.filter (fun x => x < a)).card +
      ((s ×ˢ s).filter (fun p => p.1 < p.2)).card := by
      set A := (s.filter (fun x => a < x)).image (Prod.mk a)
      set B := (s.filter (fun x => x < a)).image (fun x => (x, a))
      set C := (s ×ˢ s).filter (fun p : α × α => p.1 < p.2)
      have hset : (insert a s ×ˢ insert a s).filter
          (fun p : α × α => p.1 < p.2) = A ∪ B ∪ C := by
        ext ⟨x, y⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Finset.mem_union, Finset.mem_image, A, B, C]
        constructor
        · rintro ⟨⟨hx, hy⟩, hlt⟩
          rcases hx with rfl | hxs
          · rcases hy with rfl | hys
            · exact absurd hlt (lt_irrefl _)
            · left; left; exact ⟨y, ⟨hys, hlt⟩, rfl⟩
          · rcases hy with rfl | hys
            · left; right; exact ⟨x, ⟨hxs, hlt⟩, rfl⟩
            · right; exact ⟨⟨hxs, hys⟩, hlt⟩
        · rintro ((⟨z, ⟨hzs, hlt⟩, heq⟩ | ⟨z, ⟨hzs, hlt⟩, heq⟩) | ⟨⟨hx, hy⟩,
          hlt⟩)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
            exact ⟨⟨Or.inl rfl, Or.inr hzs⟩, hlt⟩
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
            exact ⟨⟨Or.inr hzs, Or.inl rfl⟩, hlt⟩
          · exact ⟨⟨Or.inr hx, Or.inr hy⟩, hlt⟩
      have hAB : Disjoint A B := by
        rw [Finset.disjoint_left]; intro ⟨x, y⟩ hA hB
        simp only [Finset.mem_image, Finset.mem_filter, A, B] at hA hB
        obtain ⟨z₁, _, heq₁⟩ := hA
        obtain ⟨z₂, ⟨_, hz₂a⟩, heq₂⟩ := hB
        have h1 : a = x := (Prod.mk.inj heq₁).1
        have h2 : z₂ = x := (Prod.mk.inj heq₂).1
        have heq : z₂ = a := h2.trans h1.symm
        rw [heq] at hz₂a
        exact lt_irrefl a hz₂a
      have hABC : Disjoint (A ∪ B) C := by
        rw [Finset.disjoint_left]; intro ⟨x, y⟩ hAB' hC
        rw [Finset.mem_union] at hAB'
        rw [Finset.mem_filter, Finset.mem_product] at hC
        rcases hAB' with hA | hB
        · simp only [Finset.mem_image, A] at hA
          obtain ⟨z, _, heq⟩ := hA
          have := (Prod.mk.inj heq).1
          exact ha (this ▸ hC.1.1)
        · simp only [Finset.mem_image, B] at hB
          obtain ⟨z, _, heq⟩ := hB
          have := (Prod.mk.inj heq).2
          exact ha (this ▸ hC.1.2)
      rw [hset, Finset.card_union_of_disjoint hABC,
        Finset.card_union_of_disjoint hAB]
      congr 1; congr 1
      · exact Finset.card_image_of_injective _
          (fun _ _ h => (Prod.mk.inj h).2)
      · exact Finset.card_image_of_injective _
          (fun _ _ h => (Prod.mk.inj h).1)
    rw [hsplit, ih, hfilt_sum]
    rw [Finset.card_insert_of_notMem ha, Nat.choose_succ_succ,
      Nat.choose_one_right]

open Classical in
/-- The crossings card equals Nat.choose of edge count. -/
private theorem crossings_card_eq_choose (W : ClosedFragment)
    (F : EdgeSubset W) :
    (Finset.univ.filter (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
      p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧ p.2 ∈ edgeIndexSet W F)).card =
    Nat.choose (edgeIndexSet W F).card 2 := by
  -- Rewrite as (edgeIndexSet ×ˢ edgeIndexSet).filter (p.1 < p.2)
  have : (Finset.univ.filter (fun p : Fin (edgeCount W) × Fin (edgeCount W) =>
      p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧ p.2 ∈ edgeIndexSet W F)).card =
    ((edgeIndexSet W F ×ˢ edgeIndexSet W F).filter (fun p => p.1 < p.2)).card :=
      by
    congr 1; ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product]
    tauto
  rw [this]
  exact card_ordered_pairs_eq_choose (edgeIndexSet W F)

/-! ### Part 1: the riffle sign -/

open Classical in
/-- **The riffle sign: the permutation from slot order to edge-interleaved
    order has sign `(-1)^crossings`.** -/
theorem sign_listIndexPerm_slot_edge (W : ClosedFragment)
    (F : EdgeSubset W) :
    (Equiv.Perm.sign (listIndexPerm (globalSlotList W F) (edgePairList W F)
      (globalSlotList_nodup W F) (edgePairList_nodup W F)
      (fun x => ⟨fun _ => mem_edgePairList W F x,
                 fun _ => mem_globalSlotList W F x⟩)
      (length_eq_of_nodup_mem _ _
        (globalSlotList_nodup W F) (edgePairList_nodup W F)
        (fun x => ⟨fun _ => mem_edgePairList W F x,
                   fun _ => mem_globalSlotList W F x⟩))) : ℤ) =
    (-1 : ℤ) ^ (Finset.univ.filter (fun p : Fin (edgeCount W) × Fin (edgeCount
      W) =>
      p.1 < p.2 ∧ p.1 ∈ edgeIndexSet W F ∧ p.2 ∈ edgeIndexSet W F)).card := by
  have hmem : ∀ x : {f : W.Flag // f ∈ F.flags},
      x ∈ globalSlotList W F ↔ x ∈ edgePairList W F :=
    fun x => ⟨fun _ => mem_edgePairList W F x, fun _ => mem_globalSlotList W F
      x⟩
  have hlen := length_eq_of_nodup_mem _ _
    (globalSlotList_nodup W F) (edgePairList_nodup W F) hmem
  set g : {f : W.Flag // f ∈ F.flags} → Fin (edgeCount W + edgeCount W) :=
    fun f => starFlagEnum W f.val
  have hg : ((globalSlotList W F).map g).Nodup :=
    globalSlotList_map_slot_nodup W F
  -- sortSign_map_listIndexPerm: sortSign(l₂.map g) = sign(τ) * sortSign(l₁.map
  --   g)
  have hkey := sortSign_map_listIndexPerm
    (globalSlotList W F) (edgePairList W F)
    (globalSlotList_nodup W F) (edgePairList_nodup W F)
    hmem hlen g hg
  -- sortSign(l₁.map g) = 1
  have hss1 := sortSign_globalSlotList_map_slot W F
  -- sortSign(l₂.map g) = (-1)^inversions = (-1)^C(n,2)
  rw [hss1, mul_one] at hkey
  -- hkey: sortSign(edgePairList.map g) = sign(τ)
  rw [← hkey]
  -- Goal: sortSign(edgePairList.map slot) = (-1)^crossings
  rw [sortSign]
  rw [inversions_edgePairList_slots]
  rw [partEdges_length]
  rw [crossings_card_eq_choose]

/-! ### Part 2 helpers: oriented list inversions -/

open Classical in
/-- The slot function maps orientedPairList to the conditionally-swapped
    interleaved list. -/
private theorem orientedPairList_map_slot (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    (orientedPairList W F o).map (fun f : {f : W.Flag // f ∈ F.flags} =>
      starFlagEnum W f.val) =
    (partEdges W F).flatMap (fun e =>
      if o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) e)) = true then
        [Fin.natAdd (edgeCount W) e, Fin.castAdd (edgeCount W) e]
      else
        [Fin.castAdd (edgeCount W) e, Fin.natAdd (edgeCount W) e]) := by
  rw [orientedPairList, List.map_flatMap]
  simp only [apply_ite (List.map (fun f : {f : W.Flag // f ∈ F.flags}
    => starFlagEnum W f.val)),
    List.map_cons, List.map_nil, _root_.Equiv.apply_symm_apply]
  -- attachWith.flatMap (fun i => sw i.val) = partEdges.flatMap sw
  suffices h : ∀ (l : List (Fin (edgeCount W)))
      (H : ∀ x ∈ l, x ∈ edgeIndexSet W F),
      (l.attachWith (· ∈ edgeIndexSet W F) H).flatMap
        (fun i : {i : Fin (edgeCount W) // i ∈ edgeIndexSet W F} =>
          if o.isOut ((starFlagEnum W).symm (Fin.castAdd (edgeCount W) i.val)) =
            true then
            [Fin.natAdd (edgeCount W) i.val, Fin.castAdd (edgeCount W) i.val]
          else
            [Fin.castAdd (edgeCount W) i.val, Fin.natAdd (edgeCount W) i.val]) =
      l.flatMap (fun e =>
        if o.isOut ((starFlagEnum W).symm (Fin.castAdd (edgeCount W) e)) = true
          then
          [Fin.natAdd (edgeCount W) e, Fin.castAdd (edgeCount W) e]
        else
          [Fin.castAdd (edgeCount W) e, Fin.natAdd (edgeCount W) e]) from h _ _
  intro l H
  induction l with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.attachWith, List.pmap_cons, List.flatMap_cons]
    exact congrArg _ (ih (fun x hx => H x (List.mem_cons_of_mem _ hx)))

/-- Inversions of the oriented interleave with swap count. -/
private theorem inversions_oriented_interleave {n : ℕ}
    (E : List (Fin n)) (sw : Fin n → Bool)
    (hpw : List.Pairwise (· < ·) E) :
    inversions (E.flatMap (fun i =>
      if sw i = true then
        [Fin.natAdd n i, Fin.castAdd n i]
      else
        [Fin.castAdd n i, Fin.natAdd n i])) =
    Nat.choose E.length 2 + (E.filter (fun i => sw i)).length := by
  induction E with
  | nil => simp [List.flatMap, inversions]
  | cons e rest ih =>
    have hrest := hpw.of_cons
    have hgt : ∀ x ∈ rest, e < x :=
      (List.pairwise_cons.mp hpw).1
    rw [List.flatMap_cons]
    set rest_fm := rest.flatMap (fun i =>
      if sw i = true then
        [Fin.natAdd n i, Fin.castAdd n i]
      else
        [Fin.castAdd n i, Fin.natAdd n i])
    -- The cross-tail filter counts don't depend on swap order within pairs,
    -- only on which VALUES appear. Both orderings produce the same set of
    --   values.
    -- Key: filter (< castAdd e) over rest_fm = 0 (same as unswapped)
    -- Key: filter (< natAdd e) over rest_fm = rest.length (same as unswapped)
    -- These hold because the VALUES in rest_fm are the same regardless of swap
    --   order
    -- The oriented rest flatmap is a permutation of the unoriented rest flatmap
    -- (within each pair, values are just swapped). So filters have same length.
    set rest_unsw := rest.flatMap (fun i => [Fin.castAdd n i, Fin.natAdd n i])
    have hperm_rest : rest_fm.Perm rest_unsw := by
      change (rest.flatMap (fun i =>
        if sw i = true then [Fin.natAdd n i, Fin.castAdd n i]
        else [Fin.castAdd n i, Fin.natAdd n i])).Perm
        (rest.flatMap (fun i => [Fin.castAdd n i, Fin.natAdd n i]))
      exact List.Perm.flatMap_left rest (fun x _ => by
        by_cases hsw : sw x = true
        · rw [ite_eq_left hsw]; exact List.Perm.swap _ _ _
        · rw [ite_eq_right hsw])
    have h_rest_filter_cast :
        (rest_fm.filter (fun b => decide (b < Fin.castAdd n e))).length = 0 :=
          by
      rw [(hperm_rest.filter _).length_eq]
      exact filter_lt_castAdd_head_eq_zero e rest hgt
    have h_rest_filter_nat :
        (rest_fm.filter (fun b => decide (b < Fin.natAdd n e))).length =
        rest.length := by
      rw [(hperm_rest.filter _).length_eq]
      exact filter_lt_natAdd_head_eq_length e rest hgt
    -- Now handle the head element's contribution
    by_cases hsw_e : sw e = true
    · -- Swapped: [natAdd e, castAdd e] ++ rest_fm
      rw [ite_eq_left hsw_e]
      simp only [List.cons_append, List.nil_append]
      -- inversions (natAdd :: castAdd :: rest_fm)
      change ((Fin.castAdd n e :: rest_fm).filter
          (fun b => decide (b < Fin.natAdd n e))).length +
        ((rest_fm.filter (fun b => decide (b < Fin.castAdd n e))).length +
          inversions rest_fm) = _
      -- filter (< natAdd e) (castAdd e :: rest_fm) = 1 + rest.length
      have hcast_lt_nat : Fin.castAdd n e < Fin.natAdd n e := by
        change (Fin.castAdd n e).val < (Fin.natAdd n e).val
        simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
      rw [List.filter_cons, ite_eq_left (show decide (Fin.castAdd n e < Fin.natAdd n
        e) = true from
        decide_eq_true_eq.mpr hcast_lt_nat),
        List.length_cons, h_rest_filter_nat]
      rw [h_rest_filter_cast, Nat.zero_add, ih hrest]
      rw [List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right]
      rw [List.filter_cons, ite_eq_left hsw_e, List.length_cons]
      simp only [show Nat.succ 1 = 2 from rfl]; omega
    · -- Not swapped: [castAdd e, natAdd e] ++ rest_fm
      rw [ite_eq_right hsw_e]
      simp only [List.cons_append, List.nil_append]
      -- inversions (castAdd :: natAdd :: rest_fm)
      change ((Fin.natAdd n e :: rest_fm).filter
          (fun b => decide (b < Fin.castAdd n e))).length +
        ((rest_fm.filter (fun b => decide (b < Fin.natAdd n e))).length +
          inversions rest_fm) = _
      -- filter (< castAdd e) (natAdd e :: rest_fm) = 0
      rw [List.filter_cons, ite_eq_right (show ¬ decide (Fin.natAdd n e < Fin.castAdd
        n e) = true from
        fun h => not_natAdd_lt_castAdd e (decide_eq_true_eq.mp h))]
      rw [h_rest_filter_cast, Nat.zero_add, h_rest_filter_nat, ih hrest]
      rw [List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right]
      rw [List.filter_cons, ite_eq_right hsw_e]
      simp only [show Nat.succ 1 = 2 from rfl]; omega

open Classical in
/-- The count of swapped edges in partEdges via filter equals the
    card of the edge orientation filter. -/
private theorem filter_swapped_partEdges_card (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    ((partEdges W F).filter (fun i =>
      o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i)) = true)).length =
    ((edgeIndexSet W F).filter (fun i =>
      o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i)) = true)).card := by
  rw [partEdges]
  set p := fun i : Fin (edgeCount W) =>
    o.isOut ((starFlagEnum W).symm (Fin.castAdd (edgeCount W) i)) = true
  -- (S.sort).filter p has same length as (S.filter p).card
  -- because sort is a permutation of the finset elements
  have hperm : (((edgeIndexSet W F).sort (· ≤ ·)).filter
      (fun i => p i)).Perm (((edgeIndexSet W F).filter (fun i => p i)).sort
        (· ≤ ·)) := by
    apply (List.perm_ext_iff_of_nodup
      ((Finset.sort_nodup _ _).filter _)
      (Finset.sort_nodup _ _)).mpr
    intro x
    simp only [List.mem_filter, Finset.mem_sort, Finset.mem_filter,
      decide_eq_true_eq]
  rw [hperm.length_eq]
  exact Finset.length_sort _

/-! ### Part 2: the orientation sign -/

open Classical in
/-- **The orientation sign: the permutation from edge-interleaved to
    oriented order has sign `(-1)^s` where `s` is the swap count.** -/
theorem sign_listIndexPerm_edge_oriented (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    (Equiv.Perm.sign (listIndexPerm (edgePairList W F) (orientedPairList W F o)
      (edgePairList_nodup W F) (orientedPairList_nodup W F o)
      (fun x => ⟨fun _ => mem_orientedPairList W F o x,
                 fun _ => mem_edgePairList W F x⟩)
      (length_eq_of_nodup_mem _ _
        (edgePairList_nodup W F) (orientedPairList_nodup W F o)
        (fun x => ⟨fun _ => mem_orientedPairList W F o x,
                   fun _ => mem_edgePairList W F x⟩))) : ℤ) =
    (-1 : ℤ) ^ ((edgeIndexSet W F).filter (fun i =>
      o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i)) = true)).card := by
  have hmem : ∀ x : {f : W.Flag // f ∈ F.flags},
      x ∈ edgePairList W F ↔ x ∈ orientedPairList W F o :=
    fun x => ⟨fun _ => mem_orientedPairList W F o x,
              fun _ => mem_edgePairList W F x⟩
  have hlen := length_eq_of_nodup_mem _ _
    (edgePairList_nodup W F) (orientedPairList_nodup W F o) hmem
  set g : {f : W.Flag // f ∈ F.flags} → Fin (edgeCount W + edgeCount W) :=
    fun f => starFlagEnum W f.val
  -- edgePairList.map g is nodup (same elements as globalSlotList.map g)
  have hg : ((edgePairList W F).map g).Nodup := by
    have hperm : ((edgePairList W F).map g).Perm
        ((globalSlotList W F).map g) := by
      apply List.Perm.map g
      exact (List.perm_ext_iff_of_nodup
        (edgePairList_nodup W F) (globalSlotList_nodup W F)).mpr
        (fun x => ⟨fun _ => mem_globalSlotList W F x,
                   fun _ => mem_edgePairList W F x⟩)
    exact hperm.nodup_iff.mpr (globalSlotList_map_slot_nodup W F)
  have hkey := sortSign_map_listIndexPerm
    (edgePairList W F) (orientedPairList W F o)
    (edgePairList_nodup W F) (orientedPairList_nodup W F o)
    hmem hlen g hg
  -- sortSign(edgePairList.map g) = (-1)^C(n,2)
  have hss_edge : sortSign ((edgePairList W F).map g) =
      (-1 : ℤ) ^ Nat.choose (partEdges W F).length 2 := by
    rw [sortSign, inversions_edgePairList_slots]
  -- sortSign(orientedPairList.map g) = (-1)^(C(n,2) + s)
  have hss_oriented : sortSign ((orientedPairList W F o).map g) =
      (-1 : ℤ) ^ (Nat.choose (partEdges W F).length 2 +
        ((partEdges W F).filter (fun i =>
          o.isOut ((starFlagEnum W).symm
            (Fin.castAdd (edgeCount W) i)) = true)).length) := by
    rw [sortSign, orientedPairList_map_slot]
    simp only [partEdges]
    have hfilt_eq : ∀ (l : List (Fin (edgeCount W))),
        (l.filter (fun i => o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)))).length =
        (l.filter (fun i => decide (o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)) = true))).length := by
      intro l; congr 1; congr 1; ext i; exact (Bool.decide_coe _).symm
    rw [inversions_oriented_interleave _ _
      (List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort (edgeIndexSet W F))),
      hfilt_eq]
  -- Combine: sign(τ) = sortSign(oriented) / sortSign(edge) = (-1)^s
  rw [hss_oriented, hss_edge] at hkey
  -- hkey: (-1)^(C + s) = sign(τ) * (-1)^C
  set c := Nat.choose (partEdges W F).length 2
  rw [pow_add] at hkey
  -- hkey: (-1)^c * (-1)^s = sign(τ) * (-1)^c where s = filter length
  have hcc : ((-1 : ℤ) ^ c) * ((-1 : ℤ) ^ c) = 1 := by
    rw [← pow_add, show c + c = 2 * c from by omega,
      pow_mul, neg_one_sq, one_pow]
  -- Cancel (-1)^c to get sign(τ) = (-1)^s
  have hsign : (Equiv.Perm.sign (listIndexPerm (edgePairList W F)
      (orientedPairList W F o) (edgePairList_nodup W F)
      (orientedPairList_nodup W F o) hmem hlen) : ℤ) =
      (-1 : ℤ) ^ ((partEdges W F).filter (fun i =>
        o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)) = true)).length := by
    -- From hkey, multiply both sides by (-1)^c on the right
    have h := congr_arg (· * (-1 : ℤ) ^ c) hkey
    rw [mul_assoc, mul_assoc] at h
    rw [hcc, mul_one] at h
    rw [mul_comm ((-1 : ℤ) ^ _) ((-1 : ℤ) ^ c), ← mul_assoc, hcc, one_mul] at h
    exact h.symm
  rw [hsign, filter_swapped_partEdges_card]

/-! ### Part 3: swap-count complement -/

open Classical in
/-- Every edge's representative is either outgoing or incoming, so
the two counts partition the edges. -/
theorem card_out_add_card_in_edges (W : ClosedFragment)
    (F : EdgeSubset W) {κ : F.TransitionSystem}
    (o : κ.Orientation) :
    ((edgeIndexSet W F).filter (fun i =>
      o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i)) = true)).card
      + inRepCount W F o = (edgeIndexSet W F).card := by
  rw [inRepCount]
  -- inRepCount filters univ for membership AND isOut = false;
  -- first show it equals filtering edgeIndexSet for isOut = false
  have hinrep :
      (Finset.univ.filter (fun i : Fin (edgeCount W) =>
        (starFlagEnum W).symm (Fin.castAdd (edgeCount W) i) ∈
          F.flags ∧
        o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)) = false)).card =
      ((edgeIndexSet W F).filter (fun i =>
        o.isOut ((starFlagEnum W).symm
          (Fin.castAdd (edgeCount W) i)) = false)).card := by
    congr 1
    ext i
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨_, hmem, hout⟩
      exact ⟨by rw [edgeIndexSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _,
        hmem⟩, hout⟩
    · rintro ⟨hi, hout⟩
      rw [edgeIndexSet, Finset.mem_filter] at hi
      exact ⟨Finset.mem_univ _, hi.2, hout⟩
  rw [hinrep]
  have hconv : ((edgeIndexSet W F).filter (fun i =>
      o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i)) = false)).card =
    ((edgeIndexSet W F).filter (fun i =>
      ¬ (o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i)) = true))).card := by
    congr 1; ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hf⟩
      exact ⟨hi, by rw [hf]; exact fun h => Bool.noConfusion h⟩
    · rintro ⟨hi, hnt⟩
      refine ⟨hi, ?_⟩
      cases hb : o.isOut ((starFlagEnum W).symm
        (Fin.castAdd (edgeCount W) i))
      · rfl
      · exact absurd hb hnt
  rw [hconv]
  exact Finset.card_filter_add_card_filter_not
    (fun i => o.isOut ((starFlagEnum W).symm
      (Fin.castAdd (edgeCount W) i)) = true)

end RS
