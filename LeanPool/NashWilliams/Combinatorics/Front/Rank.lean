/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import LeanPool.NashWilliams.Combinatorics.Front.Defs
import Mathlib.SetTheory.Ordinal.Rank

/-!
# The tree of a front is well-founded

The *tree* of a front `F` is the set of all prefixes (initial segments) of elements of `F`, ordered
by *proper end-extension* (`treeExt F a b` : `a` properly extends `b`). This file proves that this
relation is **well-founded**, so a front has an ordinal `rank`.

Well-foundedness is proved directly, by showing there is no infinite descending chain. A
descending chain is an ascending tower `f 0 ⊏ f 1 ⊏ ⋯` of proper extensions inside the tree.
Its lengths grow without bound, so the tower has a limit `b : ℕ → ℕ`, a strictly increasing
subsequence of `M`. By Density some `t ∈ F` is an initial segment of `b`; extending it by one
more entry of `b` lands inside some `u ∈ F` with `t <+: u`, so Incomparability forces `t = u` —
impossible, as `u` is
strictly longer.

## Main results

* `Front.exists_strictMono_comp`: a strictly monotone `b` with `range b ⊆ range M` is a
  subsequence `M ∘ g` of `M` (the enumeration bridge).
* `Front.IsFront.wellFounded_treeExt`: proper end-extension is well-founded on the tree of a front.
* `Front.IsFront.rank`: the ordinal rank of a front.
* `Front.powK_rank`: the uniform front `[M]^k` has rank `k`.
* `Front.schreier_rank`: the Schreier front has rank `ω`.
-/

open Set List Ordinal

universe u

noncomputable section

/-- **A relation homomorphism does not increase rank.** If `f : r →r s` maps `r` into a
well-founded relation `s`, then the `r`-rank of `a` is at most the `s`-rank of `f a`. This is the
cross-relation companion to `IsWellFounded.rank_lt_of_rel` (which only compares ranks within a
single relation), and the tool underlying the rank comparisons for the ray and the restriction of
a front. General; Mathlib-bound (belongs next to `IsWellFounded.rank_lt_of_rel`). -/
theorem RelHom.rank_le {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellFounded α r] [IsWellFounded β s] (f : r →r s) (a : α) :
    IsWellFounded.rank r a ≤ IsWellFounded.rank s (f a) := by
  refine IsWellFounded.induction r a
    (motive := fun a => IsWellFounded.rank r a ≤ IsWellFounded.rank s (f a))
    (fun a IH => ?_)
  rw [IsWellFounded.rank_eq r a]
  apply Ordinal.iSup_le
  rintro ⟨b, hb⟩
  calc Order.succ (IsWellFounded.rank r b)
      ≤ Order.succ (IsWellFounded.rank s (f b)) := Order.succ_le_succ (IH b hb)
    _ ≤ IsWellFounded.rank s (f a) := by
        rw [IsWellFounded.rank_eq s (f a)]
        exact Ordinal.le_iSup
          (fun c : {c // s c (f a)} => Order.succ (IsWellFounded.rank s c))
          ⟨f b, f.map_rel hb⟩

namespace Front

/-- The tree of a front `F`: all prefixes (initial segments) of elements of `F`. -/
def tree (F : Set (List ℕ)) : Set (List ℕ) :=
  {s | ∃ t ∈ F, s <+: t}

/-- Proper end-extension inside the tree of `F`: `treeExt F a b` holds when `a` properly extends
`b` and both lie in the tree. Its well-foundedness is what allows ranking a front. Note the
recursion direction: `IsWellFounded.rank (treeExt F) s` is the supremum of `succ (rank s')` over
the proper extensions `s'` of `s`, matching the usual rank of a front. -/
def treeExt (F : Set (List ℕ)) (a b : List ℕ) : Prop :=
  a ∈ tree F ∧ b ∈ tree F ∧ b <+: a ∧ b ≠ a

/-- If every finite initial segment of `b` is strictly increasing, then `b` is strictly
monotone. -/
theorem strictMono_of_pairwise_map {b : ℕ → ℕ}
    (h : ∀ n, ((List.range n).map b).Pairwise (· < ·)) : StrictMono b := by
  intro i j hij
  have hlen : ((List.range (j + 1)).map b).length = j + 1 := by simp
  have hp := (List.pairwise_iff_getElem.mp (h (j + 1))) i j (by omega) (by omega) hij
  simpa using hp

/-- **Enumeration bridge.** A strictly monotone `b` whose range is contained in that of a
strictly monotone `M` is a subsequence `M ∘ g` of `M`, for a unique strictly monotone `g`. -/
theorem exists_strictMono_comp {M b : ℕ → ℕ} (hM : StrictMono M) (hb : StrictMono b)
    (hsub : ∀ i, b i ∈ Set.range M) : ∃ g : ℕ → ℕ, StrictMono g ∧ M ∘ g = b := by
  choose g hg using hsub
  refine ⟨g, ?_, funext hg⟩
  intro i j hij
  have : M (g i) < M (g j) := by rw [hg, hg]; exact hb hij
  exact hM.lt_iff_lt.mp this

/-- **Proper end-extension is well-founded on the tree of a front.** Proved directly: there is no
infinite descending chain. -/
theorem IsFront.wellFounded_treeExt {F : Set (List ℕ)} {M : ℕ → ℕ} (hF : IsFront F M) :
    WellFounded (treeExt F) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ => ?_⟩
  -- `hf n : treeExt F (f (n+1)) (f n)`, i.e. `f 0 ⊏ f 1 ⊏ ⋯` is an ascending tower.
  have hmem : ∀ n, f n ∈ tree F := fun n => (hf n).2.1
  have hpre : ∀ n, f n <+: f (n + 1) := fun n => (hf n).2.2.1
  have hne : ∀ n, f n ≠ f (n + 1) := fun n => (hf n).2.2.2
  -- The lengths strictly increase, so `n ≤ |f n|`.
  have hlt : ∀ n, (f n).length < (f (n + 1)).length := by
    intro n
    rcases lt_or_eq_of_le (hpre n).length_le with h | h
    · exact h
    · exact absurd ((hpre n).eq_of_length h) (hne n)
  have hlen_ge : ∀ n, n ≤ (f n).length := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ k ih => have := hlt k; omega
  -- The tower is nested.
  have hnest : ∀ {n m : ℕ}, n ≤ m → f n <+: f m := by
    intro n m h
    induction h with
    | refl => exact List.prefix_rfl
    | step _ ih => exact ih.trans (hpre _)
  -- Each node is strictly increasing (a sublist of an element of `F`).
  have hsorted : ∀ n, (f n).Pairwise (· < ·) := by
    intro n
    obtain ⟨u, hu, hpu⟩ := hmem n
    exact List.Pairwise.sublist hpu.sublist (hF.sorted u hu)
  -- The limit `b` of the tower.
  have hlen1 : ∀ i, i < (f (i + 1)).length := fun i =>
    lt_of_lt_of_le (Nat.lt_succ_self i) (hlen_ge (i + 1))
  set b : ℕ → ℕ := fun i => (f (i + 1))[i]'(hlen1 i) with hb_def
  -- `b` agrees with every node long enough to reach the index.
  have hagree : ∀ {i m : ℕ}, i + 1 ≤ m → (h : i < (f m).length) → (f m)[i] = b i := by
    intro i m hm _
    exact ((hnest hm).getElem (hlen1 i)).symm
  -- Every initial segment of `b` is a prefix of a sufficiently long node.
  have hb_pre : ∀ {n m : ℕ}, n ≤ m → (List.range n).map b <+: f m := by
    intro n m hnm
    have hnlen : n ≤ (f m).length := le_trans hnm (hlen_ge m)
    have heq : (List.range n).map b = (f m).take n := by
      apply List.ext_getElem
      · simp [Nat.min_eq_left hnlen]
      · intro i h1 _
        have hi : i < n := by simpa using h1
        rw [List.getElem_take, getElem_map, getElem_range]
        exact (hagree (by omega) (lt_of_lt_of_le hi hnlen)).symm
    rw [heq]
    exact List.take_prefix n (f m)
  -- `b` is strictly increasing with entries in `M`.
  have hbmono : StrictMono b := strictMono_of_pairwise_map fun n =>
    List.Pairwise.sublist (hb_pre (le_refl n)).sublist (hsorted n)
  have hbmem : ∀ i, b i ∈ Set.range M := by
    intro i
    obtain ⟨u, hu, hpu⟩ := hmem (i + 1)
    exact hF.subM u hu (b i) (hpu.subset (List.getElem_mem (hlen1 i)))
  -- Apply Density: some `t ∈ F` is an initial segment of `b`.
  obtain ⟨g, hg, hgb⟩ := exists_strictMono_comp hF.mono hbmono hbmem
  obtain ⟨t, ht, hInit⟩ := hF.dense g hg
  rw [hgb] at hInit
  -- Extend `t` by one entry of `b`; it lands inside some `u ∈ F`.
  obtain ⟨u, hu, hpu⟩ := hmem (t.length + 1)
  have htpre : t <+: (List.range (t.length + 1)).map b := by
    conv_lhs => rw [hInit]
    exact (range_prefix_range (Nat.le_succ _)).map b
  have hbu : (List.range (t.length + 1)).map b <+: f (t.length + 1) := hb_pre (le_refl _)
  have hEq : t = u := hF.incomp t ht u hu ((htpre.trans hbu).trans hpu)
  -- But then `u = t` is a prefix of the strictly longer `f (|t|+1)`.
  have h1 : t.length + 1 ≤ (f (t.length + 1)).length := hlen_ge _
  have h2 : (f (t.length + 1)).length ≤ u.length := hpu.length_le
  have h3 : u.length = t.length := by rw [hEq]
  omega

/-- The ordinal **rank of a front**: the rank of the root `[]` in the well-founded tree of proper
end-extensions. -/
def IsFront.rank {F : Set (List ℕ)} {M : ℕ → ℕ} (hF : IsFront F M) : Ordinal :=
  have : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
  IsWellFounded.rank (treeExt F) []

variable {F : Set (List ℕ)} {M : ℕ → ℕ}

/-- The root `[]` is in the tree of any front (fronts are nonempty by Density). -/
theorem IsFront.nil_mem_tree (hF : IsFront F M) : [] ∈ tree F := by
  obtain ⟨t, ht, _⟩ := hF.dense id strictMono_id
  exact ⟨t, ht, List.nil_prefix⟩

/-- `M` being a strictly monotone enumeration, there is an element of `M` above any bound. -/
theorem exists_gt_range (hM : StrictMono M) (n : ℕ) : ∃ x ∈ Set.range M, n < x :=
  (Set.infinite_range_of_injective hM.injective).exists_gt n

/-- An increasing list contained in `M` can be extended by one further element of `M`. -/
theorem exists_extend_gt (hM : StrictMono M) (s : List ℕ) :
    ∃ x ∈ Set.range M, ∀ y ∈ s, y < x := by
  obtain ⟨x, hx, hlt⟩ := exists_gt_range hM (s.toFinset.sup id)
  refine ⟨x, hx, fun y hy => ?_⟩
  exact lt_of_le_of_lt (Finset.le_sup (f := id) (List.mem_toFinset.mpr hy)) hlt

/-- Any increasing list in `M` extends to an increasing list in `M` of any prescribed length. -/
theorem exists_extend_len (hM : StrictMono M) (L : ℕ) :
    ∀ (s : List ℕ), s.Pairwise (· < ·) → (∀ x ∈ s, x ∈ Set.range M) →
      s.length ≤ L → ∃ t, s <+: t ∧ t.Pairwise (· < ·) ∧
        (∀ x ∈ t, x ∈ Set.range M) ∧ t.length = L := by
  suffices H : ∀ d s, s.Pairwise (· < ·) → (∀ x ∈ s, x ∈ Set.range M) →
      L - s.length = d → s.length ≤ L → ∃ t, s <+: t ∧ t.Pairwise (· < ·) ∧
        (∀ x ∈ t, x ∈ Set.range M) ∧ t.length = L by
    intro s hs hsM hL; exact H _ s hs hsM rfl hL
  intro d
  induction d with
  | zero => intro s hs hsM hd hL; exact ⟨s, List.prefix_rfl, hs, hsM, by omega⟩
  | succ e ih =>
    intro s hs hsM hd hL
    obtain ⟨x, hxM, hxgt⟩ := exists_extend_gt hM s
    have hs' : (s ++ [x]).Pairwise (· < ·) := by
      rw [List.pairwise_append]
      refine ⟨hs, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; exact hxgt a ha
    have hs'M : ∀ z ∈ s ++ [x], z ∈ Set.range M := by
      intro z hz; rw [List.mem_append] at hz
      rcases hz with h | h
      · exact hsM z h
      · simp only [List.mem_singleton] at h; subst h; exact hxM
    obtain ⟨t, hpre, ht, htM, htlen⟩ := ih (s ++ [x]) hs' hs'M (by simp; omega) (by simp; omega)
    exact ⟨t, (List.prefix_append s [x]).trans hpre, ht, htM, htlen⟩

/-- **General rank formula.** If, above a fixed node `s0`, every tree node has length `≤ L` and
every tree node of length `< L` has a one-step extension in the tree, then the rank of a node `s`
above `s0` is `L - s.length`. -/
theorem rank_eq_sub (hF : IsFront F M) {s0 : List ℕ} (L : ℕ)
    (hbound : ∀ s, s0 <+: s → s ∈ tree F → s.length ≤ L)
    (hext : ∀ s, s0 <+: s → s ∈ tree F → s.length < L → ∃ x, treeExt F (s ++ [x]) s)
    (s : List ℕ) (hs0 : s0 <+: s) (hs : s ∈ tree F) :
    haveI : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
    IsWellFounded.rank (treeExt F) s = ((L - s.length : ℕ) : Ordinal) := by
  have : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
  suffices H : ∀ d s, s0 <+: s → s ∈ tree F → L - s.length = d →
      IsWellFounded.rank (treeExt F) s = (d : Ordinal) by
    exact H _ s hs0 hs rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro s hs0 hs hd
    rw [IsWellFounded.rank_eq]
    apply le_antisymm
    · apply Ordinal.iSup_le
      rintro ⟨y, hytree, -, hsy, hsney⟩
      have hslt : s.length < y.length :=
        lt_of_le_of_ne hsy.length_le fun h => hsney (hsy.eq_of_length h)
      have hs0y : s0 <+: y := hs0.trans hsy
      have hyL : y.length ≤ L := hbound y hs0y hytree
      have hsL : s.length ≤ L := hbound s hs0 hs
      have := IH _ (show L - y.length < d by omega) y hs0y hytree rfl
      rw [this, Order.succ_eq_add_one, ← Nat.cast_add_one, Nat.cast_le]
      omega
    · rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · simp [hd0]
      · have hsL : s.length ≤ L := hbound s hs0 hs
        obtain ⟨x, hx⟩ := hext s hs0 hs (by omega)
        have hs0x : s0 <+: s ++ [x] := hs0.trans (List.prefix_append s [x])
        have hrank := IH (d - 1) (by omega) (s ++ [x]) hs0x hx.1 (by simp; omega)
        calc ((d : ℕ) : Ordinal) = Order.succ (((d - 1 : ℕ) : Ordinal)) := by
              rw [Order.succ_eq_add_one, ← Nat.cast_add_one]
              congr 1
              omega
          _ = Order.succ (IsWellFounded.rank (treeExt F) (s ++ [x])) := by rw [hrank]
          _ ≤ _ := Ordinal.le_iSup
              (fun b : {b // treeExt F b s} =>
                Order.succ (IsWellFounded.rank (treeExt F) (b : List ℕ)))
              ⟨s ++ [x], hx⟩

/-- Membership in the tree of `[M]^k`: increasing lists in `M` of length at most `k`. -/
theorem mem_tree_powK (hM : StrictMono M) {k : ℕ} {s : List ℕ} :
    s ∈ tree (powK M k) ↔
      s.Pairwise (· < ·) ∧ (∀ x ∈ s, x ∈ Set.range M) ∧ s.length ≤ k := by
  constructor
  · rintro ⟨t, ⟨htlen, htp, htM⟩, hpre⟩
    exact ⟨List.Pairwise.sublist hpre.sublist htp, fun x hx => htM x (hpre.subset hx),
      le_trans hpre.length_le (le_of_eq htlen)⟩
  · rintro ⟨hs, hsM, hlen⟩
    obtain ⟨t, hpre, ht, htM, htlen⟩ := exists_extend_len hM k s hs hsM hlen
    exact ⟨t, ⟨htlen, ht, htM⟩, hpre⟩

/-- **The uniform front `[M]^k` has rank `k`.** -/
theorem powK_rank (hM : StrictMono M) (k : ℕ) : (isFront_powK hM k).rank = (k : Ordinal) := by
  have hb : ∀ s, ([] : List ℕ) <+: s → s ∈ tree (powK M k) → s.length ≤ k :=
    fun s _ hs => ((mem_tree_powK hM).mp hs).2.2
  have he : ∀ s, ([] : List ℕ) <+: s → s ∈ tree (powK M k) → s.length < k →
      ∃ x, treeExt (powK M k) (s ++ [x]) s := by
    intro s _ hs hlt
    obtain ⟨hsp, hsM, -⟩ := (mem_tree_powK hM).mp hs
    obtain ⟨x, hxM, hxgt⟩ := exists_extend_gt hM s
    have hs'p : (s ++ [x]).Pairwise (· < ·) := by
      rw [List.pairwise_append]
      refine ⟨hsp, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; exact hxgt a ha
    have hs'M : ∀ z ∈ s ++ [x], z ∈ Set.range M := by
      intro z hz; rw [List.mem_append] at hz
      rcases hz with h | h
      · exact hsM z h
      · simp only [List.mem_singleton] at h; subst h; exact hxM
    refine ⟨x, (mem_tree_powK hM).mpr ⟨hs'p, hs'M, by simp; omega⟩, hs,
      List.prefix_append s [x], ?_⟩
    intro h; have := congrArg List.length h; simp at this
  have := rank_eq_sub (isFront_powK hM k) k hb he [] List.nil_prefix
    (isFront_powK hM k).nil_mem_tree
  simpa [IsFront.rank] using this

/-- Membership in the tree of the Schreier front. -/
theorem mem_tree_schreier (hM : StrictMono M) {s : List ℕ} :
    s ∈ tree (schreier M) ↔
      s.Pairwise (· < ·) ∧ (∀ x ∈ s, x ∈ Set.range M) ∧
        (∀ a, s.head? = some a → s.length ≤ a + 1) := by
  constructor
  · rintro ⟨u, ⟨⟨c, huc, hulen⟩, hup, huM⟩, hpre⟩
    refine ⟨List.Pairwise.sublist hpre.sublist hup, fun x hx => huM x (hpre.subset hx), ?_⟩
    intro a hsa
    have hsne : s ≠ [] := by rintro rfl; simp at hsa
    have huhead : u.head? = some a := by rw [hpre.head_eq hsne]; exact hsa
    have hca : c = a := Option.some.inj (huc.symm.trans huhead)
    calc s.length ≤ u.length := hpre.length_le
      _ = c + 1 := hulen
      _ = a + 1 := by rw [hca]
  · rintro ⟨hs, hsM, hcase⟩
    rcases eq_or_ne s [] with rfl | hne
    · exact (isFront_schreier hM).nil_mem_tree
    · obtain ⟨a, hsa⟩ : ∃ a, s.head? = some a := by
        cases s with
        | nil => exact absurd rfl hne
        | cons c t => exact ⟨c, rfl⟩
      have hlen : s.length ≤ a + 1 := hcase a hsa
      obtain ⟨t, hpre, ht, htM, htlen⟩ := exists_extend_len hM (a + 1) s hs hsM hlen
      have hthead : t.head? = some a := by rw [hpre.head_eq hne]; exact hsa
      exact ⟨t, ⟨⟨a, hthead, htlen⟩, ht, htM⟩, hpre⟩

/-- **Interior of the Schreier front.** A node `s` in the tree with first element `a` has rank
`a + 1 - s.length`. -/
theorem schreier_rank_node (hM : StrictMono M) {s : List ℕ} {a : ℕ}
    (hsmem : s ∈ tree (schreier M)) (hhead : s.head? = some a) :
    haveI : IsWellFounded (List ℕ) (treeExt (schreier M)) :=
      ⟨(isFront_schreier hM).wellFounded_treeExt⟩
    IsWellFounded.rank (treeExt (schreier M)) s = ((a + 1 - s.length : ℕ) : Ordinal) := by
  have : IsWellFounded (List ℕ) (treeExt (schreier M)) :=
    ⟨(isFront_schreier hM).wellFounded_treeExt⟩
  have hpre_a : [a] <+: s := by
    obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp hhead
    exact ⟨ys, rfl⟩
  have hhead' : ∀ s', [a] <+: s' → s'.head? = some a := by
    intro s' hp
    rw [hp.head_eq (by simp), List.head?_cons]
  have hbound : ∀ s', [a] <+: s' → s' ∈ tree (schreier M) → s'.length ≤ a + 1 :=
    fun s' hp hmem => ((mem_tree_schreier hM).mp hmem).2.2 a (hhead' s' hp)
  have hext : ∀ s', [a] <+: s' → s' ∈ tree (schreier M) → s'.length < a + 1 →
      ∃ x, treeExt (schreier M) (s' ++ [x]) s' := by
    intro s' hp hmem hlt
    obtain ⟨hsp, hsM, -⟩ := (mem_tree_schreier hM).mp hmem
    have hne' : s' ≠ [] := by rintro rfl; simpa using hp.length_le
    obtain ⟨x, hxM, hxgt⟩ := exists_extend_gt hM s'
    have hs'p : (s' ++ [x]).Pairwise (· < ·) := by
      rw [List.pairwise_append]
      refine ⟨hsp, List.pairwise_singleton _ _, ?_⟩
      intro c hc b hb; simp only [List.mem_singleton] at hb; subst hb; exact hxgt c hc
    have hs'M : ∀ z ∈ s' ++ [x], z ∈ Set.range M := by
      intro z hz; rw [List.mem_append] at hz
      rcases hz with h | h
      · exact hsM z h
      · simp only [List.mem_singleton] at h; subst h; exact hxM
    have hs'head : (s' ++ [x]).head? = some a := by
      rw [(List.prefix_append s' [x]).head_eq hne']; exact hhead' s' hp
    refine ⟨x, (mem_tree_schreier hM).mpr ⟨hs'p, hs'M, ?_⟩, hmem,
      List.prefix_append s' [x], ?_⟩
    · intro c hc
      rw [hs'head] at hc
      obtain rfl := Option.some.inj hc
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro h; have := congrArg List.length h; simp at this
  exact rank_eq_sub (isFront_schreier hM) (a + 1) hbound hext s hpre_a hsmem

/-- **The Schreier front has rank `ω`.** -/
theorem schreier_rank (hM : StrictMono M) : (isFront_schreier hM).rank = ω := by
  have : IsWellFounded (List ℕ) (treeExt (schreier M)) :=
    ⟨(isFront_schreier hM).wellFounded_treeExt⟩
  rw [IsFront.rank, IsWellFounded.rank_eq]
  apply le_antisymm
  · apply Ordinal.iSup_le
    rintro ⟨y, hytree, -, -, hbne⟩
    have hyne : y ≠ [] := hbne.symm
    obtain ⟨a, hya⟩ : ∃ a, y.head? = some a := by
      cases y with
      | nil => exact absurd rfl hyne
      | cons c t => exact ⟨c, rfl⟩
    rw [schreier_rank_node hM hytree hya, Order.succ_eq_add_one, ← Nat.cast_add_one]
    exact le_of_lt (Ordinal.natCast_lt_omega0 _)
  · rw [← Ordinal.iSup_natCast]
    apply Ordinal.iSup_le
    intro n
    obtain ⟨x, hxM, hxgt⟩ := exists_gt_range hM n
    have hxtree : [x] ∈ tree (schreier M) := by
      refine (mem_tree_schreier hM).mpr ⟨List.pairwise_singleton _ _, ?_, ?_⟩
      · intro z hz; simp only [List.mem_singleton] at hz; subst hz; exact hxM
      · intro c hc
        rw [List.head?_cons] at hc
        obtain rfl := Option.some.inj hc
        simp only [List.length_cons, List.length_nil]; omega
    have hte : treeExt (schreier M) [x] [] :=
      ⟨hxtree, (isFront_schreier hM).nil_mem_tree, List.nil_prefix, by simp⟩
    have hrank : IsWellFounded.rank (treeExt (schreier M)) [x] = (x : Ordinal) := by
      rw [schreier_rank_node hM hxtree List.head?_cons]; simp
    calc (n : Ordinal) ≤ ((x + 1 : ℕ) : Ordinal) := by rw [Nat.cast_le]; omega
      _ = Order.succ (IsWellFounded.rank (treeExt (schreier M)) [x]) := by
            rw [hrank, Order.succ_eq_add_one, Nat.cast_add_one]
      _ ≤ _ := Ordinal.le_iSup
            (fun b : {b // treeExt (schreier M) b []} =>
              Order.succ (IsWellFounded.rank (treeExt (schreier M)) (b : List ℕ)))
            ⟨[x], hte⟩

end Front
