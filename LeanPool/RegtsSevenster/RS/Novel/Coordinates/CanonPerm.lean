/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ReindexBij
public import LeanPool.RegtsSevenster.RS.Novel.Coordinates.ListSignPerm

/-!
# The canonical permutation of colour data

A mixed colouring of `d` slots splits into its even colours (a
multiset, since they may repeat) and its odd colours (a list, whose
order the summand's sign remembers).  When the odd list is
duplicate-free the colouring is a permutation of the *canonical*
colouring at the same data — even colours sorted, odd colours in
increasing order — and the permutation's odd inversion count is the
odd list's own sorting sign.

That is what lets the mixed summand be read off the data alone: the
functional sees only the multiset and the set, and the sign the
reindexing costs is exactly the one the list carries.
-/

@[expose] public section

namespace RS

open Equiv Finset

variable {k ℓ : ℕ}

/-! ## Colour data extraction -/

/-- The even colours of a mixed colouring, as a multiset: even
colours may repeat. -/
noncomputable def evenMultisetOf {d : ℕ} (c : MixedColouring k ℓ d)
    : Multiset (Fin k) :=
  ↑((List.ofFn c).filterMap Sum.getLeft?)

/-- The odd colours, in slot order: the list whose sorting sign the
summand carries. -/
noncomputable def oddListOf {d : ℕ} (c : MixedColouring k ℓ d)
    : List (Fin (2 * ℓ)) :=
  (List.ofFn c).filterMap Sum.getRight?

/-- The odd colours as a set — the index the functional is
evaluated at. -/
noncomputable def oddFinsetOf {d : ℕ} (c : MixedColouring k ℓ d)
    : Finset (Fin (2 * ℓ)) :=
  (oddListOf c).toFinset

/-! ## Card bookkeeping -/

private theorem filterMap_sum_length {α β : Type*} (l : List (α ⊕ β)) :
    (l.filterMap Sum.getLeft?).length + (l.filterMap Sum.getRight?).length =
      l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    cases x with
    | inl a =>
      rw [List.filterMap_cons_some (Sum.getLeft?_inl (β := β)),
          List.filterMap_cons_none (Sum.getRight?_inl (α := α))]
      simp only [List.length_cons]; omega
    | inr b =>
      rw [List.filterMap_cons_none (Sum.getLeft?_inr (α := α)),
          List.filterMap_cons_some (Sum.getRight?_inr (β := β))]
      simp only [List.length_cons]; omega

/-- The two parts account for every slot. -/
theorem card_data {d : ℕ} (c : MixedColouring k ℓ d) :
    d = (evenMultisetOf c).card + (oddListOf c).length := by
  have hc : (evenMultisetOf c).card =
      ((List.ofFn c).filterMap Sum.getLeft?).length :=
    Multiset.coe_card _
  have hd : (oddListOf c).length =
      ((List.ofFn c).filterMap Sum.getRight?).length := rfl
  rw [hc, hd]; have h := filterMap_sum_length (List.ofFn c)
  rw [List.length_ofFn] at h; omega

/-- When the odd list is duplicate-free its set has the same
size. -/
theorem card_oddFinset {d : ℕ} (c : MixedColouring k ℓ d)
    (hnodup : (oddListOf c).Nodup) :
    (oddFinsetOf c).card = (oddListOf c).length :=
  List.toFinset_card_of_nodup hnodup

/-! ## Colour value rank -/

private def colourValueRank (k : ℕ) : Fin k ⊕ Fin (2 * ℓ) → ℕ
  | Sum.inl a => a.val
  | Sum.inr b => k + b.val

private theorem colourValueRank_injective :
    Function.Injective (colourValueRank (ℓ := ℓ) k) := by
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl b => simp? [colourValueRank] at hxy; exact congrArg Sum.inl (Fin.ext
      hxy)
    | inr b => simp [colourValueRank] at hxy; omega
  | inr a =>
    cases y with
    | inl b => simp [colourValueRank] at hxy; omega
    | inr b => simp [colourValueRank] at hxy; exact congrArg Sum.inr
                 (Fin.ext (by omega))

/-! ## Colour rank for sorting -/

private noncomputable def colourRank {d : ℕ} (c : MixedColouring k ℓ d) (i : Fin
  d) : ℕ :=
  match c i with
  | Sum.inl a => a.val * d + i.val
  | Sum.inr b => k * d + b.val * d + i.val

private noncomputable def canonSortPerm {d : ℕ} (c : MixedColouring k ℓ d) :
    Equiv.Perm (Fin d) :=
  Tuple.sort (colourRank c)

/-! ## Monotonicity -/

private theorem vr_comp_sigma_mono {d : ℕ} (c : MixedColouring k ℓ d) (_hd : 0 <
  d) :
    Monotone (colourValueRank k ∘ c ∘ canonSortPerm c) := by
  intro i j hij
  have hmono : Monotone (colourRank c ∘ canonSortPerm c) := Tuple.monotone_sort
    _
  have hm := hmono hij
  simp only [Function.comp_apply] at hm ⊢
  set si := canonSortPerm c i
  set sj := canonSortPerm c j
  cases hci : c si with
  | inl ai =>
    cases hcj : c sj with
    | inl aj =>
      change ai.val ≤ aj.val
      have hcri : colourRank c si = ai.val * d + si.val :=
        by unfold colourRank; rw [hci]
      have hcrj : colourRank c sj = aj.val * d + sj.val :=
        by unfold colourRank; rw [hcj]
      rw [hcri, hcrj] at hm
      have hsi := si.isLt; have hsj := sj.isLt
      nlinarith
    | inr bj =>
      change ai.val ≤ k + bj.val
      have hai := ai.isLt; omega
  | inr bi =>
    cases hcj : c sj with
    | inl aj =>
      exfalso
      have hcri : colourRank c si = k * d + bi.val * d + si.val := by
        unfold colourRank; rw [hci]
      have hcrj : colourRank c sj = aj.val * d + sj.val := by
        unfold colourRank; rw [hcj]
      rw [hcri, hcrj] at hm
      have haj := aj.isLt; have hsj := sj.isLt
      nlinarith
    | inr bj =>
      change k + bi.val ≤ k + bj.val
      have hcri : colourRank c si = k * d + bi.val * d + si.val := by
        unfold colourRank; rw [hci]
      have hcrj : colourRank c sj = k * d + bj.val * d + sj.val := by
        unfold colourRank; rw [hcj]
      rw [hcri, hcrj] at hm
      have hsi := si.isLt; have hsj := sj.isLt
      nlinarith

-- Raised budget: monotonicity is checked on all four
-- even/odd cases of the canonical colouring.
private theorem vr_comp_canon_mono (μm : Multiset (Fin k)) (F : Finset (Fin (2 *
  ℓ))) :
    Monotone (colourValueRank k ∘ canonColouring μm F) := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only [Function.comp_apply]
  unfold canonColouring
  have hij' : i ≤ j := hij
  simp only
  split_ifs with h1 h2 h2
  · -- both left: sorted even values
    change colourValueRank k (Sum.inl _) ≤ colourValueRank k (Sum.inl _)
    simp only [colourValueRank]
    have hpw := Multiset.pairwise_sort μm (· ≤ ·)
    have hlen := show (μm.sort (· ≤ ·)).length = μm.card from by simp
    exact hpw.sortedLE (Fin.mk_le_mk.mpr (by omega) :
      (⟨i, hlen ▸ h1⟩ : Fin _) ≤ ⟨j, hlen ▸ h2⟩)
  · -- left ≤ right
    change colourValueRank k (Sum.inl _) ≤ colourValueRank k (Sum.inr _)
    simp only [colourValueRank]
    have hlen := show (μm.sort (· ≤ ·)).length = μm.card from by simp
    have hlt := ((μm.sort (· ≤ ·)).get ⟨i, hlen ▸ h1⟩).isLt
    omega
  · -- right, left: impossible
    exfalso; omega
  · -- both right: sorted odd values
    change colourValueRank k (Sum.inr _) ≤ colourValueRank k (Sum.inr _)
    simp only [colourValueRank]
    show k + _ ≤ k + _
    have hpw := Finset.pairwise_sort F (· ≤ ·)
    have hlen := show (F.sort (· ≤ ·)).length = F.card from by simp
    have hle := hpw.sortedLE (Fin.mk_le_mk.mpr (by omega) :
      (⟨i - μm.card, hlen ▸ (by omega)⟩ : Fin _) ≤
        ⟨j - μm.card, hlen ▸ (by omega)⟩)
    omega

/-! ## Multiset decomposition -/

private theorem sum_list_perm {α β : Type*} :
    ∀ (l : List (α ⊕ β)),
      l.Perm ((l.filterMap Sum.getLeft?).map Sum.inl ++
              (l.filterMap Sum.getRight?).map Sum.inr)
  | [] => List.Perm.refl _
  | Sum.inl a :: t => by
    rw [List.filterMap_cons_some (Sum.getLeft?_inl (β := β)),
        List.filterMap_cons_none (Sum.getRight?_inl (α := α)),
        List.map_cons, List.cons_append]
    exact List.Perm.cons _ (sum_list_perm t)
  | Sum.inr b :: t => by
    rw [List.filterMap_cons_none (Sum.getLeft?_inr (α := α)),
        List.filterMap_cons_some (Sum.getRight?_inr (β := β)),
        List.map_cons]
    exact (List.Perm.cons _ (sum_list_perm t)).trans List.perm_middle.symm

/-! ## Canon list structure -/

private theorem canon_as_concat (μm : Multiset (Fin k)) (F : Finset (Fin (2 *
  ℓ)))
    {d : ℕ} (h : d = μm.card + F.card) :
    List.ofFn (canonColouring μm F ∘ finCongr h) =
      (μm.sort (· ≤ ·)).map Sum.inl ++ (F.sort (· ≤ ·)).map Sum.inr := by
  apply List.ext_getElem
  · simp [List.length_ofFn, List.length_append, List.length_map, h]
  · intro i hi1 hi2
    simp only [List.length_ofFn] at hi1
    rw [List.getElem_ofFn]
    simp only [Function.comp_apply, canonColouring]
    have hlen_l : (List.map (Sum.inl (β := Fin (2 * ℓ)))
        (μm.sort (· ≤ ·))).length = μm.card := by simp
    by_cases hlt : i < μm.card
    · have hfin : (finCongr h ⟨i, hi1⟩).val < μm.card := by simp [hlt]
      rw [dite_eq_left hfin, List.getElem_append_left (by omega)]
      simp [List.getElem_map]
    · have hfin : ¬ (finCongr h ⟨i, hi1⟩).val < μm.card := by simp [hlt]
      rw [dite_eq_right hfin, List.getElem_append_right (by omega)]
      simp [hlen_l, List.getElem_map]

/-! ## Multiset equality between c and canon -/

private theorem nodup_toFinset_val {α : Type*} [DecidableEq α]
    (l : List α) (hnd : l.Nodup) : l.toFinset.val = ↑l := by
  rw [List.toFinset_val]; exact congrArg _ hnd.dedup

private theorem multiset_perm_vr {d : ℕ} (c : MixedColouring k ℓ d)
    (hnodup : (oddListOf c).Nodup)
    (h : d = (evenMultisetOf c).card + (oddFinsetOf c).card) :
    (List.ofFn (colourValueRank k ∘ c)).Perm
      (List.ofFn (colourValueRank k ∘ canonColouring (evenMultisetOf c)
        (oddFinsetOf c) ∘ finCongr h)) := by
  -- Show list-level permutation, then map
  have hcan := canon_as_concat (evenMultisetOf c) (oddFinsetOf c) h
  -- hcan : ofFn (canon ∘ finCongr) = sorted_evens.map inl ++ sorted_odds.map
  --   inr
  -- Show ofFn c ~ ofFn (canon ∘ finCongr h) as lists
  have hevens : (Multiset.sort (evenMultisetOf c) (· ≤ ·)).Perm
      ((List.ofFn c).filterMap Sum.getLeft?) :=
    Multiset.coe_eq_coe.mp (Multiset.sort_eq (evenMultisetOf c) (· ≤ ·))
  have hodds : (Finset.sort (oddFinsetOf c) (· ≤ ·)).Perm (oddListOf c) := by
    have hsort_eq := Finset.sort_eq (oddFinsetOf c) (· ≤ ·)
    have hval : (oddFinsetOf c).val = (↑(oddListOf c) : Multiset _) :=
      nodup_toFinset_val (oddListOf c) hnodup
    exact Multiset.coe_eq_coe.mp (hsort_eq.trans hval)
  have hperm_raw : (List.ofFn c).Perm
      (List.ofFn (canonColouring (evenMultisetOf c) (oddFinsetOf c) ∘
        finCongr h)) := by
    rw [hcan]
    exact (sum_list_perm (List.ofFn c)).trans
      (List.Perm.append (hevens.symm.map Sum.inl) (hodds.symm.map Sum.inr))
  have := hperm_raw.map (colourValueRank k)
  rwa [List.map_ofFn, List.map_ofFn] at this

/-! ## Pair inversions -/

private def pairInv {n : ℕ} {β : Type*} [LinearOrder β] (g : Fin n → β) : ℕ :=
  (univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ g p.1 > g p.2)).card

private theorem pairInv_perm_inv {n : ℕ} (f : Perm (Fin n)) :
    pairInv (⇑f) = pairInv (⇑f.symm) := by
  unfold pairInv
  apply Finset.card_bij (fun p (_hp : p ∈ univ.filter _) => (f p.2, f p.1))
  · intro ⟨a, b⟩ hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨hp.2, by simp only [Equiv.symm_apply_apply, gt_iff_lt]; exact hp.1⟩
  · intro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (f.injective heq.2) (f.injective heq.1)
  · intro ⟨i, j⟩ hmem
    simp only [mem_filter, mem_univ, true_and] at hmem
    refine ⟨(f.symm j, f.symm i), ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact hmem.2
      · change f (f.symm j) > f (f.symm i)
        simp only [Equiv.apply_symm_apply, gt_iff_lt]; exact hmem.1
    · simp only [Prod.mk.injEq]; exact ⟨Equiv.apply_symm_apply f i,
      Equiv.apply_symm_apply f j⟩

private theorem pairInv_congr_order {n : ℕ} {β γ : Type*} [LinearOrder β]
  [LinearOrder γ]
    {g₁ : Fin n → β} {g₂ : Fin n → γ}
    (h : ∀ i j : Fin n, g₁ i > g₁ j ↔ g₂ i > g₂ j) :
    pairInv g₁ = pairInv g₂ := by
  unfold pairInv; congr 1
  exact Finset.filter_congr (fun ⟨i, j⟩ _ => and_congr_right' (h i j))

/-! ## Inversions helpers -/

private theorem card_filter_sum
    {n : ℕ} (P : Fin n × Fin n → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ i : Fin n, ∑ j : Fin n, if P (i, j) then (1 : ℕ)
      else 0 := by
  have h := (Finset.sum_boole (R := ℕ) P univ).symm
  simp only [Nat.cast_id] at h; rw [h, Fintype.sum_prod_type]

private theorem ofFn_filter_length {β : Type} [LinearOrder β]
    {n : ℕ} (g : Fin n → β) (a : β) :
    ((List.ofFn g).filter (· < a)).length =
    (univ.filter (fun i : Fin n => g i < a)).card := by
  have h1 : (List.ofFn g).filter (· < a) =
    ((List.finRange n).filter (fun i => decide (g i < a))).map g := by
    conv_lhs => rw [show List.ofFn g = (List.finRange n).map g
      from List.map_ofFn.symm]
    rw [List.filter_map]; rfl
  rw [h1, List.length_map]
  unfold Finset.card Finset.filter
  simp [Finset.univ, Fintype.elems, List.finRange]

private theorem pairInv_succ {β : Type} [LinearOrder β]
    {n : ℕ} (g : Fin (n + 1) → β) :
    pairInv g = (univ.filter (fun j : Fin n => g j.succ < g 0)).card +
    pairInv (fun i : Fin n => g i.succ) := by
  rw [show pairInv g = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
    if i < j ∧ g i > g j then (1 : ℕ) else 0 from card_filter_sum _]
  rw [show pairInv (fun i : Fin n => g i.succ) = ∑ i : Fin n, ∑ j : Fin n,
    if i < j ∧ g i.succ > g j.succ then (1 : ℕ) else 0 from card_filter_sum _]
  rw [Fin.sum_univ_succ]; congr 1
  · rw [Fin.sum_univ_succ]
    simp only [lt_irrefl, false_and, ite_false, zero_add]
    simp_rw [show ∀ j : Fin n, ((0 : Fin (n + 1)) < j.succ ∧ g 0 > g j.succ) ↔
      g j.succ < g 0 from fun j => by simp [Fin.succ_pos, gt_iff_lt]]
    rw [Finset.sum_boole (R := ℕ)]; simp [Nat.cast_id]
  · congr 1; ext i
    rw [Fin.sum_univ_succ]
    simp only [show ¬(Fin.succ i < (0 : Fin (n + 1))) from not_lt.mpr
      (Fin.zero_le _),
      false_and, ite_false, zero_add]
    congr 1; ext j; simp only [Fin.succ_lt_succ_iff]

/-- `inversions (List.ofFn g) = pairInv g`. -/
private theorem inversions_eq_pairInv {β : Type} [LinearOrder β]
    {n : ℕ} (g : Fin n → β) : inversions (List.ofFn g) = pairInv g := by
  induction n with
  | zero => simp [List.ofFn_zero, inversions, pairInv]
  | succ n ih =>
    rw [List.ofFn_succ, inversions, ih (fun i => g i.succ)]
    rw [ofFn_filter_length (fun i => g i.succ) (g 0)]
    rw [pairInv_succ g]

/-! ## FilterMap structure lemma -/

/-- If `g ∘ f` is `some (vals t)` at positions `ps t` (strictly increasing)
    and `none`
    elsewhere, then `filterMap g (ofFn f)` equals `ofFn vals`. -/
theorem filterMap_ofFn_sorted {β γ : Type*}
    {d n : ℕ} {f : Fin d → β} {g : β → Option γ}
    {ps : Fin n → Fin d} (hps : StrictMono ps)
    {vals : Fin n → γ}
    (hgfp : ∀ t, g (f (ps t)) = some (vals t))
    (hgfn : ∀ q : Fin d, (∀ t, ps t ≠ q) → g (f q) = none) :
    (List.ofFn f).filterMap g = List.ofFn vals := by
  induction d generalizing n with
  | zero =>
    have : n = 0 := by
      by_contra h; exact (ps ⟨0, Nat.pos_of_ne_zero h⟩).elim0
    subst this; rfl
  | succ d ih =>
    rw [List.ofFn_succ]
    cases hg0 : g (f 0) with
    | none =>
      rw [List.filterMap_cons_none hg0]
      have hpos : ∀ t, 0 < (ps t).val := by
        intro t; by_contra hle; push Not at hle
        have h0 : (ps t).val = 0 := Nat.le_zero.mp hle
        have h1 := hgfp t
        rw [show ps t = (0 : Fin (d + 1)) from Fin.ext h0] at h1
        simp [hg0] at h1
      have hbd : ∀ t, (ps t).val - 1 < d := by
        intro t; have := (ps t).isLt; have := hpos t; omega
      refine ih
        (ps := fun t => ⟨(ps t).val - 1, hbd t⟩) ?_ ?_ ?_
      · intro a b hab
        have ha := hpos a
        have hlt : (ps a).val < (ps b).val := hps hab
        change (ps a).val - 1 < (ps b).val - 1
        omega
      · intro t
        have heq : (⟨(ps t).val - 1, hbd t⟩ : Fin d).succ = ps t := by
          apply Fin.ext; simp only [Fin.val_succ]; have := hpos t; omega
        change g (f (⟨(ps t).val - 1, hbd t⟩ : Fin d).succ) = some (vals t)
        rw [heq]; exact hgfp t
      · intro q hne
        show g (f q.succ) = none
        apply hgfn q.succ; intro t ht; apply hne t
        apply Fin.ext; change (ps t).val - 1 = q.val
        have h1 : (ps t).val = q.succ.val := congrArg Fin.val ht
        simp only [Fin.val_succ] at h1; omega
    | some b =>
      have hn_pos : 0 < n := by
        by_contra hle; push Not at hle
        have hn0 : n = 0 := Nat.le_zero.mp hle
        have : g (f (0 : Fin (d + 1))) = none := by
          apply hgfn; intro ⟨t, ht⟩; exact absurd ht (by omega)
        simp [this] at hg0
      have hps0 : ps ⟨0, hn_pos⟩ = (0 : Fin (d + 1)) := by
        by_contra hne
        have hge : 0 < (ps ⟨0, hn_pos⟩).val := by
          by_contra hle; push Not at hle
          exact hne (Fin.ext (Nat.le_zero.mp hle))
        have hall : ∀ t, ps t ≠ (0 : Fin (d + 1)) := by
          intro t ht
          have hle : (ps ⟨0, hn_pos⟩).val ≤ (ps t).val :=
            hps.monotone (show (⟨0, hn_pos⟩ : Fin n) ≤ t from Nat.zero_le _)
          rw [show (ps t).val = 0 from congrArg Fin.val ht] at hle
          omega
        have := hgfn (0 : Fin (d + 1)) hall
        simp [this] at hg0
      have hb : b = vals ⟨0, hn_pos⟩ := by
        have h1 := hgfp ⟨0, hn_pos⟩; rw [hps0] at h1; rw [hg0] at h1
        exact Option.some.inj h1
      subst hb
      rw [List.filterMap_cons_some hg0]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      conv_rhs => rw [List.ofFn_succ]
      congr 1
      have hpos : ∀ t : Fin n', 0 < (ps t.succ).val := by
        intro t
        have h1 : (ps ⟨0, Nat.zero_lt_succ n'⟩).val < (ps t.succ).val :=
          hps (show (⟨0, Nat.zero_lt_succ n'⟩ : Fin (n' + 1)) < t.succ from by
            change 0 < t.val + 1; omega)
        simp only [hps0] at h1; exact h1
      have hbd : ∀ t : Fin n', (ps t.succ).val - 1 < d := by
        intro t; have := (ps t.succ).isLt; have := hpos t; omega
      refine ih
        (ps := fun t : Fin n' => ⟨(ps t.succ).val - 1, hbd t⟩) ?_ ?_ ?_
      · intro a b hab
        have ha := hpos a
        have hlt : (ps a.succ).val < (ps b.succ).val :=
          hps (show a.succ < b.succ from by change a.val + 1 < b.val + 1; omega)
        change (ps a.succ).val - 1 < (ps b.succ).val - 1
        omega
      · intro t
        have heq : (⟨(ps t.succ).val - 1, hbd t⟩ : Fin d).succ = ps t.succ := by
          apply Fin.ext; simp only [Fin.val_succ]; have := hpos t; omega
        change g (f (⟨(ps t.succ).val - 1, hbd t⟩ : Fin d).succ) = some (vals
          t.succ)
        rw [heq]; exact hgfp t.succ
      · intro q hne
        show g (f q.succ) = none
        apply hgfn q.succ
        intro ⟨t, ht⟩
        rcases t with _ | t'
        · intro heq; rw [hps0] at heq
          exact absurd (show (0 : Fin (d + 1)).val = q.succ.val from congrArg
            Fin.val heq)
            (by simp [Fin.val_succ])
        · intro heq; apply hne ⟨t', by omega⟩
          apply Fin.ext; change (ps (⟨t' + 1, ht⟩ : Fin (n' + 1))).val - 1 = q.val
          have h1 : (ps ⟨t' + 1, ht⟩).val = q.succ.val := congrArg Fin.val heq
          simp only [Fin.val_succ] at h1; omega

/-! ## Sign clause -/

/-- The sign clause of `exists_canonPerm`. -/
private theorem canonSortPerm_sign {d : ℕ} (c : MixedColouring k ℓ d)
    (hnodup : (oddListOf c).Nodup)
    (h : d = (evenMultisetOf c).card + (oddFinsetOf c).card)
    (σ : Equiv.Perm (Fin d))
    (comp : c ∘ σ = canonColouring (evenMultisetOf c) (oddFinsetOf c) ∘ finCongr
      h) :
    ((-1 : ℂ) ^ oddInversions σ c = (sortSign (oddListOf c) : ℂ)) := by
  -- ═══════ SETUP: THE HIGH-INDEX FUNCTION AND ITS SORT ═══════
  -- `g` reads the odd half of `σ`; `π` sorts it; `v` is the sorted
  -- odd value sequence.
  set m := (evenMultisetOf c).card with hm_def
  set F := oddFinsetOf c with hF_def
  set n := F.card with hn_def
  have hlen : (oddListOf c).length = n := (card_oddFinset c hnodup).symm
  have hdn : d = m + n := h
  -- g : the high-index function
  set g : Fin n → Fin d := fun t => σ ⟨m + t.val, by omega⟩ with hg_def
  -- π : sorting permutation of g
  set π := Tuple.sort g with hπ_def
  -- v : sorted odd values
  set v : Fin n → Fin (2 * ℓ) := fun t =>
    (F.sort (· ≤ ·)).get ⟨t.val, by rw [Finset.length_sort]; exact t.isLt⟩ with
      hv_def
  -- isRight characterisation from comp
  have isRight_comp : ∀ j : Fin d,
      (c (σ j)).isRight = decide (m ≤ j.val) := by
    intro j
    have hcj : c (σ j) = canonColouring (evenMultisetOf c) F (finCongr h j) :=
      congr_fun comp j
    have hjval : (finCongr h j).val = j.val := by simp [finCongr_apply]
    by_cases hjm : j.val < m
    · rw [hcj, canonColouring_isRight_low _ _ _ (by rwa [hjval])]
      simp [Nat.not_le.mpr hjm]
    · rw [hcj, canonColouring_isRight_high _ _ _ (by rwa [hjval])]
      simp [Nat.le_of_not_lt hjm]
  -- g is injective
  have g_inj : Function.Injective g := by
    intro a b hab
    have hinj := σ.injective hab
    apply Fin.ext
    show a.val = b.val
    have := congrArg Fin.val hinj
    simp? at this; exact this
  -- g ∘ π is strictly monotone
  have gπ_mono : Monotone (g ∘ π) := Tuple.monotone_sort g
  have gπ_smono : StrictMono (g ∘ π) := fun a b hab =>
    lt_of_le_of_ne (gπ_mono hab.le)
      (fun heq => hab.ne (π.injective (g_inj heq)))
  -- ═══════ STAGE 1: THE INVERSIONS OF σ ARE THOSE OF g ═══════
  have step1 : oddInversions σ c = pairInv g := by
    unfold oddInversions pairInv
    refine Finset.card_bij
      (fun (p : Fin d × Fin d) (hp : p ∈ _) =>
        ((⟨p.1.val - m, by
            simp only [mem_filter, mem_univ, true_and] at hp
            obtain ⟨_, _, hr1, _⟩ := hp
            rw [isRight_comp] at hr1
            simp only [decide_eq_true_eq] at hr1; omega⟩ : Fin n),
         (⟨p.2.val - m, by
            simp only [mem_filter, mem_univ, true_and] at hp
            obtain ⟨_, _, _, hr2⟩ := hp
            rw [isRight_comp] at hr2
            simp only [decide_eq_true_eq] at hr2; omega⟩ : Fin n)))
      ?_ ?_ ?_
    · -- image in target
      intro ⟨p₁, p₂⟩ hp
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      obtain ⟨hlt, hgt, hr1, hr2⟩ := hp
      rw [isRight_comp] at hr1 hr2
      simp only [decide_eq_true_eq] at hr1 hr2
      constructor
      · change p₁.val - m < p₂.val - m; omega
      · have he1 : g ⟨p₁.val - m, by omega⟩ = σ p₁ := by
          change σ ⟨m + (p₁.val - m), _⟩ = σ p₁
          congr 1; apply Fin.ext; change m + (p₁.val - m) = p₁.val; omega
        have he2 : g ⟨p₂.val - m, by omega⟩ = σ p₂ := by
          change σ ⟨m + (p₂.val - m), _⟩ = σ p₂
          congr 1; apply Fin.ext; change m + (p₂.val - m) = p₂.val; omega
        rw [he1, he2]; exact hgt
    · -- injective
      intro ⟨a₁, b₁⟩ ha ⟨a₂, b₂⟩ hb heq
      simp only [Prod.mk.injEq, Fin.mk.injEq] at heq
      simp only [mem_filter, mem_univ, true_and] at ha hb
      rw [isRight_comp] at ha hb
      simp only [decide_eq_true_eq] at ha hb
      have ha1 := ha.2.1; have ha2 := ha.2.2
      have hb1 := hb.2.1; have hb2 := hb.2.2
      exact Prod.ext (Fin.ext (by change a₁.val = a₂.val; omega))
        (Fin.ext (by change b₁.val = b₂.val; omega))
    · -- surjective
      intro ⟨t₁, t₂⟩ ht
      simp only [mem_filter, mem_univ, true_and] at ht
      obtain ⟨hlt_t, hgt_t⟩ := ht
      refine ⟨(⟨m + t₁.val, by omega⟩, ⟨m + t₂.val, by omega⟩), ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        refine ⟨by change m + t₁.val < m + t₂.val; omega, hgt_t, ?_, ?_⟩
        · rw [isRight_comp]; simp [show m ≤ m + t₁.val from Nat.le_add_right _
          _]
        · rw [isRight_comp]; simp [show m ≤ m + t₂.val from Nat.le_add_right _
          _]
      · ext <;> simp
  -- ═══════ STAGE 2: g AND ITS SORTING PERMUTATION INVERT ALIKE ═══════
  have step2 : pairInv g = pairInv (⇑π) := by
    have h1 : pairInv g = pairInv (⇑π.symm) := pairInv_congr_order fun i j => by
      constructor
      · intro hij
        by_contra hle; push Not at hle
        exact absurd (gπ_smono.monotone hle) (by
          simp only [Function.comp_apply, Equiv.apply_symm_apply];
            exact not_le.mpr hij)
      · intro hij
        have := gπ_smono hij
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        exact this
    rw [h1]; exact (pairInv_perm_inv π).symm
  -- ═══════ STAGE 3: THE ODD LIST IS `v ∘ π` ═══════
  -- Step 3: getRight? of c at sorted odd positions gives v ∘ π
  have step3_some : ∀ t : Fin n,
      Sum.getRight? (c (g (π t))) = some (v (π t)) := by
    intro t
    have hcj : c (σ ⟨m + (π t).val, _⟩) =
        canonColouring (evenMultisetOf c) F (finCongr h ⟨m + (π t).val, _⟩) :=
      congr_fun comp ⟨m + (π t).val, by omega⟩
    simp only [hg_def] at hcj ⊢
    rw [hcj]
    unfold canonColouring
    have hge : ¬ (finCongr h ⟨m + (π t).val, by omega⟩).val < m := by
      simp [finCongr_apply]
    rw [dite_eq_right hge]
    simp only [Sum.getRight?_inr, Option.some.injEq]
    change (F.sort (· ≤ ·)).get
      ⟨(finCongr h ⟨m + (π t).val, by omega⟩).val - m, _⟩ = v (π t)
    have hval : (finCongr h ⟨m + (π t).val, by omega⟩).val - m = (π t).val := by
      simp [finCongr_apply]
    congr 1; apply Fin.ext; exact hval
  -- Step 3b: getRight? of c at non-odd positions is none
  have step3_none : ∀ q : Fin d,
      (∀ t : Fin n, g (π t) ≠ q) → Sum.getRight? (c q) = none := by
    intro q hne
    have hq_low : (σ.symm q).val < m := by
      by_contra hge; push Not at hge
      have : g ⟨(σ.symm q).val - m, by omega⟩ = q := by
        change σ ⟨m + ((σ.symm q).val - m), _⟩ = q
        rw [show (⟨m + ((σ.symm q).val - m), _⟩ : Fin d) = σ.symm q from
          Fin.ext (by change m + ((σ.symm q).val - m) = (σ.symm q).val; omega)]
        exact σ.apply_symm_apply q
      have hmem : q ∈ Set.range (g ∘ ⇑π) := by
        rw [Set.range_comp]
        exact ⟨⟨(σ.symm q).val - m, by omega⟩, Equiv.surjective π _, ‹_›⟩
      obtain ⟨s, hs⟩ := hmem
      exact hne s hs
    rw [show c q = c (σ (σ.symm q)) from by rw [Equiv.apply_symm_apply],
        show c (σ (σ.symm q)) =
          canonColouring (evenMultisetOf c) F (finCongr h (σ.symm q))
            from congr_fun comp _]
    unfold canonColouring
    rw [dite_eq_left (by simp? [finCongr_apply]; exact hq_low)]
    exact Sum.getRight?_inl
  -- Step 3c: structural claim
  have step3 : oddListOf c = List.ofFn (v ∘ π) := by
    change (List.ofFn c).filterMap Sum.getRight? = List.ofFn (v ∘ π)
    exact filterMap_ofFn_sorted (ps := fun t => g
      (π t)) gπ_smono step3_some step3_none
  -- ═══════ STAGE 4: v IS STRICTLY MONOTONE ═══════
  have v_smono : StrictMono v := by
    intro a b hab
    have hpw : List.Pairwise (· ≤ ·) (F.sort (· ≤ ·)) := F.pairwise_sort (· ≤ ·)
    have hnd : (F.sort (· ≤ ·)).Nodup := F.sort_nodup (· ≤ ·)
    have hslt : (F.sort (· ≤ ·)).SortedLT := hpw.sortedLE.sortedLT_of_nodup hnd
    -- SortedLT = StrictMono l.get
    exact hslt (show (⟨a.val, _⟩ : Fin (F.sort (· ≤ ·)).length) < ⟨b.val, _⟩
      from hab)
  -- ═══════ STAGE 5: THE ODD LIST'S INVERSIONS ARE π'S ═══════
  have step5 : inversions (oddListOf c) = pairInv (⇑π) := by
    rw [step3, inversions_eq_pairInv]
    exact pairInv_congr_order fun i j =>
      ⟨fun h => v_smono.lt_iff_lt.mp h, fun h => v_smono.lt_iff_lt.mpr h⟩
  -- ═══════ ASSEMBLY ═══════
  have key : oddInversions σ c = inversions (oddListOf c) := by
    rw [step1, step2]; exact step5.symm
  simp only [sortSign, key]; push_cast; ring

/-! ## Main theorem -/

-- Raised budget: the permutation, its arity equality and its sign
-- are produced together, so the sort of the odd list and the
-- inversion count elaborate in one term.
/-- **The canonical permutation**: any colouring with a
duplicate-free odd list is a permutation of the canonical one at
its own data, and the permutation's odd inversion sign is exactly
the odd list's sorting sign. -/
theorem exists_canonPerm {d : ℕ} (c : MixedColouring k ℓ d)
    (hnodup : (oddListOf c).Nodup) :
    ∃ (σ : Equiv.Perm (Fin d))
      (h : d = (evenMultisetOf c).card + (oddFinsetOf c).card),
      (c ∘ σ = (canonColouring (evenMultisetOf c) (oddFinsetOf c)) ∘ finCongr h)
        ∧
      ((-1 : ℂ) ^ oddInversions σ c = (sortSign (oddListOf c) : ℂ)) := by
  set m := (evenMultisetOf c).card
  have hnodup_card := card_oddFinset c hnodup
  have h : d = m + (oddFinsetOf c).card := by
    rw [hnodup_card]; exact card_data c
  set n := (oddFinsetOf c).card
  by_cases hd : d = 0
  · subst hd
    refine ⟨1, h, ?_, ?_⟩
    · ext ⟨i, hi⟩; exact absurd hi (by omega)
    · have hodd_nil : oddListOf c = [] := by
        simp only [oddListOf]
        rw [show List.ofFn c = ([] : List (Fin k ⊕ Fin (2 * ℓ))) from
          List.eq_nil_of_length_eq_zero (by simp)]
        simp
      have hinv : oddInversions 1 c = 0 := by
        simp only [oddInversions, Perm.one_apply, gt_iff_lt,
          card_eq_zero, filter_eq_empty_iff, mem_univ, forall_true_left]
        intro ⟨_, _⟩; rintro ⟨hlt, hgt, _⟩
        exact absurd (lt_trans hlt hgt) (lt_irrefl _)
      rw [hinv, hodd_nil]; simp [sortSign, inversions]
  · have hd' : 0 < d := Nat.pos_of_ne_zero hd
    set σ := canonSortPerm c
    set vr := colourValueRank (ℓ := ℓ) k
    -- Composition proof
    have comp : c ∘ σ =
        canonColouring (evenMultisetOf c) (oddFinsetOf c) ∘ finCongr h := by
      set canon_fn := canonColouring (evenMultisetOf c) (oddFinsetOf c) ∘
        finCongr h
      have hmono1 : Monotone (vr ∘ c ∘ σ) := vr_comp_sigma_mono c hd'
      have hmono2 : Monotone (vr ∘ canon_fn) :=
        (vr_comp_canon_mono (evenMultisetOf c) (oddFinsetOf c)).comp (fun _x _y
          h => h)
      have hs1 : (List.ofFn (vr ∘ c ∘ σ)).SortedLE := hmono1.sortedLE_ofFn
      have hs2 : (List.ofFn (vr ∘ canon_fn)).SortedLE := hmono2.sortedLE_ofFn
      have hperm : (List.ofFn (vr ∘ c ∘ σ)).Perm (List.ofFn (vr ∘ canon_fn)) :=
        (σ.ofFn_comp_perm (vr ∘ c)).trans (multiset_perm_vr c hnodup h)
      have heq_list := hperm.eq_of_sortedLE hs1 hs2
      have heq_fn : vr ∘ c ∘ σ = vr ∘ canon_fn := List.ofFn_inj.mp heq_list
      ext j; exact colourValueRank_injective (congr_fun heq_fn j)
    exact ⟨σ, h, comp, canonSortPerm_sign c hnodup h σ comp⟩

end RS
