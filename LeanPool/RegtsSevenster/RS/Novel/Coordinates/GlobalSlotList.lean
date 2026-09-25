/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.TauKey
import LeanPool.RegtsSevenster.RS.Novel.Coordinates.PatternInv

/-!
# The global slot list

The participating flags of an edge subset, enumerated in slot order,
and the link between the pattern inversion count and list inversions.
-/

namespace RS

open Finset

variable {k ℓ : ℕ}

/-- The set of slots whose flags participate in `F`. -/
noncomputable def partSlots (W : ClosedFragment) (F : EdgeSubset W) :
    Finset (Fin (edgeCount W + edgeCount W)) :=
  Finset.univ.filter (fun q => (starFlagEnum W).symm q ∈ F.flags)

/-- Membership in `partSlots`. -/
theorem mem_partSlots {W : ClosedFragment} {F : EdgeSubset W}
    (q : Fin (edgeCount W + edgeCount W)) :
    q ∈ partSlots W F ↔ (starFlagEnum W).symm q ∈ F.flags := by
  rw [partSlots, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The global slot list: participating flags in slot order. -/
noncomputable def globalSlotList (W : ClosedFragment) (F : EdgeSubset W) :
    List {f : W.Flag // f ∈ F.flags} :=
  ((partSlots W F).sort (· ≤ ·)).pmap
    (fun q hq => ⟨(starFlagEnum W).symm q, (mem_partSlots q).mp hq⟩)
    (fun _ hq => (Finset.mem_sort _).mp hq)

/-- The global slot list is duplicate-free. -/
theorem globalSlotList_nodup (W : ClosedFragment) (F : EdgeSubset W) :
    (globalSlotList W F).Nodup := by
  refine List.Nodup.pmap ?_ (Finset.sort_nodup _ _)
  intro a _ b _ h
  have hv := congrArg
    (fun z : {f : W.Flag // f ∈ F.flags} => z.val) h
  exact (starFlagEnum W).symm.injective hv

/-- Every participating flag appears in the global slot list. -/
theorem mem_globalSlotList (W : ClosedFragment) (F : EdgeSubset W)
    (x : {f : W.Flag // f ∈ F.flags}) :
    x ∈ globalSlotList W F := by
  rw [globalSlotList]
  have hslot : starFlagEnum W x.val ∈ partSlots W F := by
    rw [mem_partSlots, _root_.Equiv.symm_apply_apply]
    exact x.prop
  have hsort : starFlagEnum W x.val ∈
      (partSlots W F).sort (· ≤ ·) :=
    (Finset.mem_sort _).mpr hslot
  exact List.mem_pmap.mpr ⟨starFlagEnum W x.val, hsort,
    Subtype.ext (_root_.Equiv.symm_apply_apply _ _)⟩

/-- Filter length of `ofFn` matches finset card. -/
theorem filter_length_ofFn {β : Type}
    {n : ℕ} (g : Fin n → β) (p : β → Bool) :
    ((List.ofFn g).filter p).length =
      (Finset.univ.filter (fun i : Fin n => p (g i) = true)).card := by
  rw [List.ofFn_eq_map, List.filter_map, List.length_map]
  -- Goal: (List.finRange n |>.filter (p ∘ g)).length = ...
  have hperm : ((List.finRange n).filter (p ∘ g)).Perm
      (((Finset.univ : Finset (Fin n)).filter
        (fun i => p (g i) = true)).sort (· ≤ ·)) := by
    rw [List.perm_ext_iff_of_nodup
      ((List.nodup_finRange n).filter _)
      (Finset.sort_nodup _ _)]
    intro x
    rw [List.mem_filter, Finset.mem_sort, Finset.mem_filter]
    simp [List.mem_finRange, Function.comp]
  rw [hperm.length_eq, Finset.length_sort]

/-- Helper: the head-filter count in the successor step. -/
private theorem head_filter_card {β : Type} [LinearOrder β]
    {n : ℕ} (g : Fin (n + 1) → β) :
    ((List.ofFn (fun i : Fin n => g i.succ)).filter
      (fun b => decide (b < g 0))).length =
    (Finset.univ.filter (fun i : Fin n =>
      g i.succ < g 0)).card := by
  classical
  rw [filter_length_ofFn]
  congr 1
  ext i
  simp [decide_eq_true_eq]

/-- Helper: partition of pair inversions by first component. -/
private theorem pair_filter_succ_split {β : Type} [LinearOrder β]
    {n : ℕ} (g : Fin (n + 1) → β) :
    (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 < p.2 ∧ g p.2 < g p.1)).card =
    (Finset.univ.filter (fun i : Fin n =>
      g i.succ < g 0)).card +
    (Finset.univ.filter (fun p : Fin n × Fin n =>
      p.1 < p.2 ∧ g p.2.succ < g p.1.succ)).card := by
  -- Partition pairs (a, b) with a < b into those with a = 0 and
  -- those with a ≠ 0 (i.e. a = i.succ for some i).
  have hdisj : Disjoint
    (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 = 0 ∧ p.1 < p.2 ∧ g p.2 < g p.1))
    (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 ≠ 0 ∧ p.1 < p.2 ∧ g p.2 < g p.1)) := by
    rw [Finset.disjoint_filter]
    intro _ _ ⟨h0, _⟩ ⟨hn, _⟩
    exact hn h0
  have hunion : Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 < p.2 ∧ g p.2 < g p.1) =
    (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 = 0 ∧ p.1 < p.2 ∧ g p.2 < g p.1)) ∪
    (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 ≠ 0 ∧ p.1 < p.2 ∧ g p.2 < g p.1)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
      true_and]
    constructor
    · intro ⟨hab, hgab⟩
      by_cases h0 : a = 0
      · exact Or.inl ⟨h0, hab, hgab⟩
      · exact Or.inr ⟨h0, hab, hgab⟩
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  congr 1
  · -- Pairs with a = 0 biject with {i : Fin n | g i.succ < g 0}
    apply Finset.card_bij
      (fun (p : Fin (n + 1) × Fin (n + 1)) (hp : p ∈ _) =>
        p.2.pred (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          intro h0; rw [hp.1, h0] at hp; exact lt_irrefl _ hp.2.1))
    · intro ⟨a, b⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      obtain ⟨ha0, _, hgba⟩ := hmem
      rw [ha0] at hgba
      rwa [Fin.succ_pred]
    · intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      have ha1 := h₁.1
      have ha2 := h₂.1
      have hb : b₁ = b₂ := by
        rw [Fin.ext_iff] at heq ⊢
        simp only [Fin.val_pred] at heq
        omega
      exact Prod.ext (ha1.trans ha2.symm) hb
    · intro i hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      refine ⟨⟨0, i.succ⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨Fin.succ_pos _, hmem⟩
      · exact Fin.pred_succ _
  · -- Pairs with a ≠ 0 biject with Fin n × Fin n pairs
    apply Finset.card_bij
      (fun (p : Fin (n + 1) × Fin (n + 1)) (hp : p ∈ _) =>
        (p.1.pred (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          exact hp.1),
         p.2.pred (by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          intro h0; rw [h0] at hp
          exact Nat.not_lt.mpr (Fin.zero_le _) hp.2.1)))
    · intro ⟨a, b⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      obtain ⟨hne, hab, hgba⟩ := hmem
      constructor
      · exact Fin.pred_lt_pred_iff.mpr hab
      · rwa [Fin.succ_pred, Fin.succ_pred]
    · intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      have hprod := Prod.ext_iff.mp heq
      have ha : a₁ = a₂ := @Fin.pred_inj _ a₁ a₂ h₁.1 h₂.1 |>.mp hprod.1
      have hb : b₁ = b₂ := by
        have hb1ne : b₁ ≠ 0 := by
          intro h0; rw [h0] at h₁; exact Nat.not_lt.mpr (Fin.zero_le _) h₁.2.1
        have hb2ne : b₂ ≠ 0 := by
          intro h0; rw [h0] at h₂; exact Nat.not_lt.mpr (Fin.zero_le _) h₂.2.1
        exact @Fin.pred_inj _ b₁ b₂ hb1ne hb2ne |>.mp hprod.2
      exact Prod.ext ha hb
    · intro ⟨i, j⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      refine ⟨⟨i.succ, j.succ⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨Fin.succ_ne_zero _,
          Fin.succ_lt_succ_iff.mpr hmem.1, hmem.2⟩
      · ext <;> simp [Fin.pred_succ]

/-- Inversion count of `ofFn g` equals the pair-filter card. -/
theorem inversions_ofFn_eq_card {β : Type} [LinearOrder β]
    {n : ℕ} (g : Fin n → β) :
    inversions (List.ofFn g) =
      (Finset.univ.filter (fun p : Fin n × Fin n =>
        p.1 < p.2 ∧ g p.2 < g p.1)).card := by
  induction n with
  | zero =>
    rw [List.ofFn_zero, inversions]
    simp [Finset.filter_false_of_mem]
  | succ n ih =>
    rw [List.ofFn_succ, inversions, ih]
    rw [head_filter_card, pair_filter_succ_split]

/-- The key of the flag at slot `finCongr ... (sortSplitPerm W x)`
    is `x` itself. -/
theorem sortKey_symm_slot (W : ClosedFragment)
    (x : Fin (ds W).sum) :
    sortKey W ((starFlagEnum W).symm
      (finCongr (degList_sum (starAssignEnum W))
        (sortSplitPerm W x))) = x := by
  rw [sortKey]
  have hsplit : finCongr (degList_sum (starAssignEnum W))
      (sortSplitPerm W x) =
    (sortEquiv (starAssignEnum W)).symm x := by
    exact (congrFun (congrArg _root_.Equiv.toFun
      (sortEquiv_symm_split W)) x).symm
  conv_lhs => rw [hsplit]
  rw [show (starFlagEnum W) ((starFlagEnum W).symm
    ((sortEquiv (starAssignEnum W)).symm x)) =
    (sortEquiv (starAssignEnum W)).symm x from
    _root_.Equiv.apply_symm_apply _ _]
  exact _root_.Equiv.apply_symm_apply _ _

/-- `finCongr` preserves strict order. -/
private theorem finCongr_lt_iff {m n : ℕ} (h : m = n)
    (a b : Fin m) :
    finCongr h a < finCongr h b ↔ a < b := by
  rw [Fin.lt_def, Fin.lt_def, finCongr_apply_coe,
    finCongr_apply_coe]

/-- The slot of a key equals the original flag position. -/
private theorem slot_of_sortKey (W : ClosedFragment)
    (q : Fin (edgeCount W + edgeCount W)) :
    finCongr (degList_sum (starAssignEnum W))
      (sortSplitPerm W
        (sortEquiv (starAssignEnum W) q)) = q := by
  -- sortEquiv_symm_split says:
  -- (sortEquiv _).symm = (sortSplitPerm W).trans (finCongr _)
  -- So finCongr _ (sortSplitPerm W x) = (sortEquiv _).symm x
  -- Applying at x = sortEquiv _ q:
  -- finCongr _ (sortSplitPerm W (sortEquiv _ q))
  --   = (sortEquiv _).symm (sortEquiv _ q) = q
  have step : ∀ y : Fin (ds W).sum,
      finCongr (degList_sum (starAssignEnum W))
        (sortSplitPerm W y) =
      (sortEquiv (starAssignEnum W)).symm y := by
    intro y
    have h := sortEquiv_symm_split W
    exact (congrFun (congrArg _root_.Equiv.toFun h) y).symm
  rw [step, _root_.Equiv.symm_apply_apply]

/-- Length of globalSlotList equals length of sorted partSlots. -/
private theorem globalSlotList_length (W : ClosedFragment)
    (F : EdgeSubset W) :
    (globalSlotList W F).length =
      ((partSlots W F).sort (· ≤ ·)).length := by
  unfold globalSlotList
  exact List.length_pmap

/-- The getElem of the globalSlotList pmap extracts the flag from
the sort. -/
private theorem globalSlotList_getElem_val (W : ClosedFragment)
    (F : EdgeSubset W)
    (i : ℕ) (hi : i < (globalSlotList W F).length) :
    ((globalSlotList W F)[i]).val =
    (starFlagEnum W).symm
      (((partSlots W F).sort (· ≤ ·))[i]'(by
        rw [globalSlotList_length] at hi; exact hi)) := by
  unfold globalSlotList at hi ⊢
  rw [List.getElem_pmap]

/-- The slot list is strictly sorted. -/
private theorem sort_pairwise_lt (W : ClosedFragment) (F : EdgeSubset W) :
    List.Pairwise (· < ·) ((partSlots W F).sort (· ≤ ·)) :=
  List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort (partSlots W F))

/-- The intermediate slot-inversion set. -/
private noncomputable def slotInvPairs (W : ClosedFragment)
    (F : EdgeSubset W) :
    Finset (Fin (edgeCount W + edgeCount W) ×
            Fin (edgeCount W + edgeCount W)) :=
  (partSlots W F ×ˢ partSlots W F).filter
    (fun qp => qp.1 < qp.2 ∧
      sortKey W ((starFlagEnum W).symm qp.2) <
        sortKey W ((starFlagEnum W).symm qp.1))

/-- patternOddInv equals the card of slotInvPairs. -/
private theorem patternOddInv_eq_slotInvPairs
    (W : ClosedFragment) (F : EdgeSubset W) :
    patternOddInv W F = (slotInvPairs W F).card := by
  unfold patternOddInv slotInvPairs
  apply Finset.card_bij
    (fun (p : Fin (ds W).sum × Fin (ds W).sum) _ =>
      (finCongr (degList_sum (starAssignEnum W))
          (sortSplitPerm W p.2),
       finCongr (degList_sum (starAssignEnum W))
          (sortSplitPerm W p.1)))
  · intro ⟨p₁, p₂⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨hlt, hgt, hf1, hf2⟩ := hmem
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [mem_partSlots]; exact hf2
    · rw [mem_partSlots]; exact hf1
    · rw [finCongr_lt_iff]; exact hgt
    · rw [sortKey_symm_slot, sortKey_symm_slot]; exact hlt
  · intro ⟨p₁, p₂⟩ _ ⟨q₁, q₂⟩ _ heq
    have hprod := Prod.ext_iff.mp heq
    have h1 : sortSplitPerm W p₂ = sortSplitPerm W q₂ := by
      have := hprod.1
      rwa [Fin.ext_iff, finCongr_apply_coe, finCongr_apply_coe,
        ← Fin.ext_iff] at this
    have h2 : sortSplitPerm W p₁ = sortSplitPerm W q₁ := by
      have := hprod.2
      rwa [Fin.ext_iff, finCongr_apply_coe, finCongr_apply_coe,
        ← Fin.ext_iff] at this
    exact Prod.ext
      ((sortSplitPerm W).injective h2)
      ((sortSplitPerm W).injective h1)
  · intro ⟨q₁, q₂⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_product] at hmem
    obtain ⟨⟨hq1, hq2⟩, hlt, hkey⟩ := hmem
    have hsk : ∀ q, sortKey W ((starFlagEnum W).symm q) =
        sortEquiv (starAssignEnum W) q := by
      intro q; rw [sortKey, _root_.Equiv.apply_symm_apply]
    refine ⟨⟨sortKey W ((starFlagEnum W).symm q₂),
            sortKey W ((starFlagEnum W).symm q₁)⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hkey, ?_, ?_, ?_⟩
      · rw [show sortSplitPerm W
              (sortKey W ((starFlagEnum W).symm q₂)) =
            sortSplitPerm W (sortEquiv (starAssignEnum W) q₂) from
            congrArg _ (hsk q₂)]
        rw [show sortSplitPerm W
              (sortKey W ((starFlagEnum W).symm q₁)) =
            sortSplitPerm W (sortEquiv (starAssignEnum W) q₁) from
            congrArg _ (hsk q₁)]
        rw [GT.gt, ← finCongr_lt_iff (degList_sum (starAssignEnum W)),
          slot_of_sortKey, slot_of_sortKey]
        exact hlt
      · rw [show finCongr (degList_sum (starAssignEnum W))
              (sortSplitPerm W
                (sortKey W ((starFlagEnum W).symm q₂))) =
            q₂ from by rw [hsk, slot_of_sortKey]]
        rw [mem_partSlots] at hq2; exact hq2
      · rw [show finCongr (degList_sum (starAssignEnum W))
              (sortSplitPerm W
                (sortKey W ((starFlagEnum W).symm q₁))) =
            q₁ from by rw [hsk, slot_of_sortKey]]
        rw [mem_partSlots] at hq1; exact hq1
    · ext <;> simp only
      · rw [hsk, slot_of_sortKey]
      · rw [hsk, slot_of_sortKey]

/-- The sorted slot list's nodup property. -/
private theorem sort_nodup (W : ClosedFragment) (F : EdgeSubset W) :
    ((partSlots W F).sort (· ≤ ·)).Nodup :=
  Finset.sort_nodup _ _

/-- Position lookup: index of element in sorted list. -/
private noncomputable def slotPos (W : ClosedFragment)
    (F : EdgeSubset W)
    (q : Fin (edgeCount W + edgeCount W))
    (hq : q ∈ partSlots W F) :
    Fin ((partSlots W F).sort (· ≤ ·)).length :=
  ⟨((partSlots W F).sort (· ≤ ·)).idxOf q,
   List.idxOf_lt_length_of_mem ((Finset.mem_sort _).mpr hq)⟩

/-- The sort's getElem at slotPos returns the original element. -/
private theorem sort_getElem_slotPos (W : ClosedFragment)
    (F : EdgeSubset W)
    (q : Fin (edgeCount W + edgeCount W))
    (hq : q ∈ partSlots W F) :
    ((partSlots W F).sort (· ≤ ·))[(slotPos W F q hq).val] = q := by
  exact List.getElem_idxOf
    (List.idxOf_lt_length_of_mem ((Finset.mem_sort _).mpr hq))

/-- getElem is injective on nodup lists. -/
private theorem nodup_getElem_injective {α : Type} {l : List α}
    (hnd : l.Nodup) {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (h : l[i] = l[j]) : i = j := by
  exact (List.Nodup.getElem?_inj hi hnd).mp
    (show l[i]? = l[j]? by
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
      exact congrArg _ h)

/-- slotPos is order-preserving. -/
private theorem slotPos_lt_of_lt (W : ClosedFragment)
    (F : EdgeSubset W)
    (q₁ q₂ : Fin (edgeCount W + edgeCount W))
    (hq1 : q₁ ∈ partSlots W F)
    (hq2 : q₂ ∈ partSlots W F)
    (hlt : q₁ < q₂) :
    slotPos W F q₁ hq1 < slotPos W F q₂ hq2 := by
  simp only [slotPos, Fin.mk_lt_mk]
  by_contra h
  push Not at h
  have hi1 : List.idxOf q₁ ((partSlots W F).sort (· ≤ ·)) <
      ((partSlots W F).sort (· ≤ ·)).length :=
    List.idxOf_lt_length_of_mem
      ((Finset.mem_sort (α := Fin (edgeCount W + edgeCount W))
        (· ≤ ·)).mpr hq1)
  have hi2 : List.idxOf q₂ ((partSlots W F).sort (· ≤ ·)) <
      ((partSlots W F).sort (· ≤ ·)).length :=
    List.idxOf_lt_length_of_mem
      ((Finset.mem_sort (α := Fin (edgeCount W + edgeCount W))
        (· ≤ ·)).mpr hq2)
  rcases Nat.lt_or_eq_of_le h with hgt | heq
  · have := List.pairwise_iff_getElem.mp (sort_pairwise_lt W F)
      _ _ hi2 hi1 hgt
    rw [List.getElem_idxOf hi2,
      List.getElem_idxOf hi1] at this
    exact lt_irrefl _ (lt_trans hlt this)
  · -- idxOf q₁ = idxOf q₂, so by nodup: the elements at those positions are
    --   equal
    -- but getElem_idxOf says they are q₁ and q₂ respectively
    exfalso
    have h1 : ((partSlots W F).sort (· ≤ ·))[
        List.idxOf q₁ ((partSlots W F).sort (· ≤ ·))] = q₁ :=
      List.getElem_idxOf hi1
    have h2 : ((partSlots W F).sort (· ≤ ·))[
        List.idxOf q₂ ((partSlots W F).sort (· ≤ ·))] = q₂ :=
      List.getElem_idxOf hi2
    have heq' : ((partSlots W F).sort (· ≤ ·))[
        List.idxOf q₁ ((partSlots W F).sort (· ≤ ·))] =
      ((partSlots W F).sort (· ≤ ·))[
        List.idxOf q₂ ((partSlots W F).sort (· ≤ ·))]'(by omega) := by
      congr 1; omega
    rw [h1, h2] at heq'
    exact lt_irrefl _ (heq' ▸ hlt)

/-- inversions of the key-mapped global slot list equals slotInvPairs. -/
private theorem inversions_eq_slotInvPairs (W : ClosedFragment)
    (F : EdgeSubset W) :
    inversions ((globalSlotList W F).map
      (fun f => sortKey W f.val)) =
    (slotInvPairs W F).card := by
  set l := globalSlotList W F with hl
  set m := l.length with hm
  -- Convert map to ofFn
  have hofFn : l.map (fun f => sortKey W f.val) =
      List.ofFn (fun i : Fin m => sortKey W (l.get i).val) := by
    rw [show l.map (fun f => sortKey W f.val) =
      (List.ofFn l.get).map (fun f => sortKey W f.val) from
        by rw [List.ofFn_get], List.map_ofFn]; rfl
  rw [hofFn, inversions_ofFn_eq_card]
  -- Now: card of {(i,j) : Fin m × Fin m | i < j ∧ key(l[j]) < key(l[i])}
  --    = card of slotInvPairs
  set sortL := (partSlots W F).sort (· ≤ ·) with hsortL
  have hml : m = sortL.length := globalSlotList_length W F
  -- Bijection via getElem: position ↦ slot
  apply Finset.card_bij
    (fun (p : Fin m × Fin m) (_ : p ∈ _) =>
      (sortL[p.1.val]'(hml ▸ p.1.isLt),
       sortL[p.2.val]'(hml ▸ p.2.isLt)))
  · -- mem
    intro ⟨i, j⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨hij, hkey⟩ := hmem
    simp only [slotInvPairs, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨(Finset.mem_sort _).mp (List.getElem_mem _),
            (Finset.mem_sort _).mp (List.getElem_mem _)⟩, ?_, ?_⟩
    · exact List.pairwise_iff_getElem.mp (sort_pairwise_lt W F)
        i j (hml ▸ i.isLt) (hml ▸ j.isLt) hij
    · -- Convert: l.get i's val = (starFlagEnum W).symm sortL[i]
      have hvi : (l.get ⟨i.val, i.isLt⟩).val =
          (starFlagEnum W).symm (sortL[i.val]'(hml ▸ i.isLt)) :=
        globalSlotList_getElem_val W F i.val i.isLt
      have hvj : (l.get ⟨j.val, j.isLt⟩).val =
          (starFlagEnum W).symm (sortL[j.val]'(hml ▸ j.isLt)) :=
        globalSlotList_getElem_val W F j.val j.isLt
      rw [← hvj, ← hvi]
      exact hkey
  · -- inj
    intro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ heq
    have hprod := Prod.ext_iff.mp heq
    have hnd := sort_nodup W F
    have hi := nodup_getElem_injective hnd (hml ▸ i₁.isLt) (hml ▸ i₂.isLt)
      hprod.1
    have hj := nodup_getElem_injective hnd (hml ▸ j₁.isLt) (hml ▸ j₂.isLt)
      hprod.2
    exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  · -- surj
    intro ⟨q₁, q₂⟩ hmem
    simp only [slotInvPairs, Finset.mem_filter,
      Finset.mem_product] at hmem
    obtain ⟨⟨hq1, hq2⟩, hlt, hkey⟩ := hmem
    set i := slotPos W F q₁ hq1 with hi_def
    set j := slotPos W F q₂ hq2 with hj_def
    have hi_lt : i.val < m := by rw [hml]; exact i.isLt
    have hj_lt : j.val < m := by rw [hml]; exact j.isLt
    refine ⟨⟨⟨i.val, hi_lt⟩, ⟨j.val, hj_lt⟩⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact slotPos_lt_of_lt W F q₁ q₂ hq1 hq2 hlt
      · have hvi : (l.get ⟨i.val, hi_lt⟩).val =
            (starFlagEnum W).symm q₁ := by
          change ((globalSlotList W F)[i.val]'hi_lt).val = _
          rw [globalSlotList_getElem_val]
          congr 1
          exact sort_getElem_slotPos W F q₁ hq1
        have hvj : (l.get ⟨j.val, hj_lt⟩).val =
            (starFlagEnum W).symm q₂ := by
          change ((globalSlotList W F)[j.val]'hj_lt).val = _
          rw [globalSlotList_getElem_val]
          congr 1
          exact sort_getElem_slotPos W F q₂ hq2
        rw [hvj, hvi]
        exact hkey
    · exact Prod.ext
        (sort_getElem_slotPos W F q₁ hq1)
        (sort_getElem_slotPos W F q₂ hq2)

/-- **The pattern inversion count equals the key-inversions of the
global slot list.** -/
theorem patternOddInv_eq_inversions (W : ClosedFragment)
    (F : EdgeSubset W) :
    patternOddInv W F =
      inversions ((globalSlotList W F).map
        (fun f => sortKey W f.val)) := by
  rw [patternOddInv_eq_slotInvPairs, inversions_eq_slotInvPairs]

end RS
