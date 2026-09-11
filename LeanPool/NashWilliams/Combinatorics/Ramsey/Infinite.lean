/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import LeanPool.NashWilliams.Data.Fintype.Pigeonhole
import LeanPool.NashWilliams.Data.Nat.Nth

/-!
# The infinite Ramsey theorem

This file proves the infinite Ramsey theorem for finite colourings of the `r`-element subsets of
`ℕ`, for arbitrary arity `r`, and derives the classical pairs (`RT²`) and triples (`RT³`) cases in
their relational form.

## Main results

* `infinite_ramsey`: for every finite colouring `c : Finset ℕ → κ` of the `r`-subsets and every
  infinite `M ⊆ ℕ`, there is an infinite `N ⊆ M` all of whose `r`-subsets get one colour. Proved
  by induction on `r` (the "fan" argument).
* `infinite_ramsey_seq`: the enumeration form — the monochromatic set is the range of a strictly
  monotone `e : ℕ → ℕ`.
* `infinite_ramsey_pairs`, `infinite_ramsey_triples`: the classical RT²/RT³ statements for
  colourings of ordered pairs `m < n` and triples `m < n < l`, obtained from `infinite_ramsey_seq`
  at arity `2` and `3` by colouring a finite set through its least/greatest (and, for triples,
  middle) element.

The `Finset ℕ` colouring interface follows B. Mehta's Lean 3 `inf_ramsey.lean`. See also the
standalone project https://github.com/yannpequignot/lean-infinite-ramsey.

## Two proofs of infinite Ramsey

The proof here is direct and self-contained. `Front.ramsey_seq_of_nashWilliams`, in
`NashWilliams.Combinatorics.Front.NashWilliams`, proves the same statement a second way, by
instantiating the Nash-Williams theorem at the uniform front `[M]^k`. Both are kept, and neither
file imports the other: they share only the generic helpers in `NashWilliams.Data`.
-/

open Set

noncomputable section

variable {κ : Type*}

private structure RamseyState (c : Finset ℕ → κ) (r : ℕ) where
  vert : ℕ
  col : κ
  succ : Set ℕ
  hInf : succ.Infinite
  hgt : ∀ x ∈ succ, vert < x
  hprop : ∀ t : Finset ℕ, ↑t ⊆ succ → t.card = r → c (insert vert t) = col

theorem infinite_ramsey [Finite κ] (r : ℕ) (c : Finset ℕ → κ)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N ⊆ M, N.Infinite ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c t = col := by
  induction r generalizing c M with
  | zero =>
    refine ⟨M, subset_rfl, hM, c ∅, fun t _ ht => ?_⟩
    rw [Finset.card_eq_zero.mp ht]
  | succ r ih =>
    have stepCore : ∀ S : Set ℕ, S.Infinite →
        ∃ a' ∈ S, ∃ (col' : κ) (N : Set ℕ),
          N.Infinite ∧ N ⊆ S ∧ (∀ x ∈ N, a' < x) ∧
          ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c (insert a' t) = col' := by
      intro S hS
      refine ⟨sInf S, Nat.sInf_mem hS.nonempty, ?_⟩
      have hle : ∀ x ∈ S, sInf S ≤ x := fun x hx => Nat.sInf_le hx
      have hdiff : (S \ {sInf S}).Infinite := hS.sdiff (Set.finite_singleton _)
      obtain ⟨N, hNsub, hNinf, col', hmono⟩ := ih (fun e => c (insert (sInf S) e)) hdiff
      refine ⟨col', N, hNinf, hNsub.trans Set.sdiff_subset, ?_, hmono⟩
      intro x hxN
      have hxd := hNsub hxN
      exact lt_of_le_of_ne (hle x hxd.1) fun h => hxd.2 (h ▸ rfl)
    have advance : ∀ s : RamseyState c r, ∃ s' : RamseyState c r,
        s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
      intro s
      obtain ⟨a', ha'mem, col', N, hNinf, hNsub, hNgt, hNprop⟩ := stepCore s.succ s.hInf
      exact ⟨⟨a', col', N, hNinf, hNgt, hNprop⟩, ha'mem, hNsub⟩
    obtain ⟨a₀, ha₀M, col₀, N₀, hN₀inf, hN₀sub, hN₀gt, hN₀prop⟩ := stepCore M hM
    let s₀ : RamseyState c r := ⟨a₀, col₀, N₀, hN₀inf, hN₀gt, hN₀prop⟩
    let states : ℕ → RamseyState c r := fun n => n.rec s₀ fun _ s => (advance s).choose
    have I1 : ∀ n, (states (n + 1)).vert ∈ (states n).succ :=
      fun n => (advance (states n)).choose_spec.1
    have I2 : ∀ n, (states (n + 1)).succ ⊆ (states n).succ :=
      fun n => (advance (states n)).choose_spec.2
    have I3 : ∀ n, (states n).vert < (states (n + 1)).vert :=
      fun n => (states n).hgt _ (I1 n)
    have I4 : ∀ m n, m ≤ n → (states n).succ ⊆ (states m).succ := by
      intro m n hmn
      induction n with
      | zero => simp [Nat.le_zero.mp hmn]
      | succ n ih2 =>
        rcases Nat.lt_or_eq_of_le hmn with h | rfl
        · exact (I2 n).trans (ih2 (Nat.lt_succ_iff.mp h))
        · exact subset_rfl
    have I5 : ∀ m n, m < n → (states n).vert ∈ (states m).succ := by
      intro m n hmn
      cases n with
      | zero => exact absurd hmn (Nat.not_lt_zero m)
      | succ n => exact I4 m n (Nat.lt_succ_iff.mp hmn) (I1 n)
    have vmono : StrictMono fun n => (states n).vert := strictMono_nat_of_lt_succ I3
    have hsuccM : ∀ n, (states n).succ ⊆ M := fun n => (I4 0 n (Nat.zero_le n)).trans hN₀sub
    have hvertM : ∀ n, (states n).vert ∈ M := by
      intro n
      cases n with
      | zero => exact ha₀M
      | succ n => exact hsuccM n (I1 n)
    obtain ⟨col, hJinf⟩ := exists_infinite_fiber_nat (fun n => (states n).col)
    set V : ℕ → ℕ := fun n => (states n).vert with hV
    set J : Set ℕ := {n | (states n).col = col} with hJ
    refine ⟨V '' J, ?_, hJinf.image (vmono.injective.injOn), col, ?_⟩
    · rintro x ⟨n, _, rfl⟩; exact hvertM n
    · intro t htN htcard
      have ht_ne : t.Nonempty := Finset.card_pos.mp (by rw [htcard]; exact Nat.succ_pos r)
      set a := t.min' ht_ne with ha
      have ha_mem : a ∈ t := Finset.min'_mem _ _
      obtain ⟨m, hmJ, hVm⟩ : ∃ m, (states m).col = col ∧ (states m).vert = a := by
        obtain ⟨m, hmJ, hVm⟩ := htN (Finset.mem_coe.mpr ha_mem)
        exact ⟨m, hmJ, hVm⟩
      have hsub : ↑(t.erase a) ⊆ (states m).succ := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_erase] at hx
        obtain ⟨hxne, hxt⟩ := hx
        obtain ⟨p, hpJ, hVp⟩ := htN (Finset.mem_coe.mpr hxt)
        have hax : a < x := lt_of_le_of_ne (Finset.min'_le t x hxt) (Ne.symm hxne)
        have hmp : m < p := by
          have h1 : (states m).vert < (states p).vert := by
            rw [hVm, show (states p).vert = x from hVp]; exact hax
          exact vmono.lt_iff_lt.mp h1
        have := I5 m p hmp
        rwa [show (states p).vert = x from hVp] at this
      have hcard : (t.erase a).card = r := by
        rw [Finset.card_erase_of_mem ha_mem, htcard]; omega
      have key := (states m).hprop (t.erase a) hsub hcard
      rw [hVm, Finset.insert_erase ha_mem, hmJ] at key
      exact key

theorem infinite_ramsey_seq [Finite κ] (r : ℕ) (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = r → c t = col := by
  obtain ⟨N, _, hNinf, col, hcol⟩ := infinite_ramsey r c (M := Set.univ) Set.infinite_univ
  obtain ⟨e, he, hmem⟩ := hNinf.exists_strictMono
  exact ⟨e, he, col, fun t htsub htcard =>
    hcol t (htsub.trans (Set.range_subset_iff.mpr hmem)) htcard⟩

/-- **The infinite Ramsey theorem for pairs (RT²)**, in relational form: for a finite colouring
`c` of the ordered pairs `m < n`, there is a strictly monotone `e` and a colour `k` with
`c (e i) (e j) = k` for all `i < j`. Derived from `infinite_ramsey_seq` at arity `2`. -/
theorem infinite_ramsey_pairs {κ : Type*} [Finite κ] (c : ∀ (m n : ℕ), m < n → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ i j : ℕ, (h : i < j) → c (e i) (e j) (he h) = k := by
  classical
  -- Colour a finite set by `c` of its min and max (junk value elsewhere).
  set d : κ := c 0 1 Nat.zero_lt_one with hd
  set C : Finset ℕ → κ := fun t =>
    if h : t.Nonempty then
      if hlt : t.min' h < t.max' h then c (t.min' h) (t.max' h) hlt else d
    else d with hC
  obtain ⟨e, he, k, hk⟩ := infinite_ramsey_seq 2 C
  refine ⟨e, he, k, fun i j hij => ?_⟩
  have hlt : e i < e j := he hij
  set t : Finset ℕ := {e i, e j} with ht
  have hij_ne : e i ∉ ({e j} : Finset ℕ) := by simp [ne_of_lt hlt]
  have htcard : t.card = 2 := by
    rw [ht, Finset.card_insert_of_notMem hij_ne, Finset.card_singleton]
  have htne : t.Nonempty := ⟨e i, by rw [ht]; exact Finset.mem_insert_self _ _⟩
  have htsub : ↑t ⊆ Set.range e := by
    rw [ht]; intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [⟨i, rfl⟩, ⟨j, rfl⟩]
  have hei_mem : e i ∈ t := by rw [ht]; exact Finset.mem_insert_self _ _
  have hej_mem : e j ∈ t := by rw [ht]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmem_iff : ∀ y ∈ t, y = e i ∨ y = e j := by
    intro y hy; rw [ht] at hy
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hy
  have hmin : t.min' htne = e i := by
    apply le_antisymm (Finset.min'_le _ _ hei_mem)
    apply Finset.le_min'
    intro y hy; rcases hmem_iff y hy with rfl | rfl
    exacts [le_refl _, le_of_lt hlt]
  have hmax : t.max' htne = e j := by
    apply le_antisymm _ (Finset.le_max' _ _ hej_mem)
    apply Finset.max'_le
    intro y hy; rcases hmem_iff y hy with rfl | rfl
    exacts [le_of_lt hlt, le_refl _]
  have hCt : C t = c (e i) (e j) hlt := by
    have h1 : C t = if hlt' : t.min' htne < t.max' htne
        then c (t.min' htne) (t.max' htne) hlt' else d := by
      rw [hC]; simp only [htne, dite_eq_left]
    rw [h1, hmin, hmax, dite_eq_left hlt]
  have hkt : C t = k := hk t htsub htcard
  rw [hCt] at hkt
  exact hkt

/-- **The infinite Ramsey theorem for triples (RT³)**, in relational form, derived from
`infinite_ramsey_seq` at arity `3` (colour a `3`-subset by `c` of its least, middle and greatest
element). -/
theorem infinite_ramsey_triples {κ : Type*} [Finite κ]
    (c : ∀ (m n l : ℕ), (m < n ∧ n < l) → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ h i j : ℕ, (hs : h < i ∧ i < j) →
        c (e h) (e i) (e j) ⟨he hs.1, he hs.2⟩ = k := by
  classical
  set d : κ := c 0 1 2 ⟨Nat.zero_lt_one, Nat.one_lt_two⟩ with hd
  set C : Finset ℕ → κ := fun t =>
    if h : t.Nonempty then
      if h2 : (t.erase (t.min' h)).Nonempty then
        if hh : t.min' h < (t.erase (t.min' h)).min' h2 ∧
                (t.erase (t.min' h)).min' h2 < t.max' h then
          c (t.min' h) ((t.erase (t.min' h)).min' h2) (t.max' h) hh
        else d
      else d
    else d with hC
  obtain ⟨e, he, k, hk⟩ := infinite_ramsey_seq 3 C
  refine ⟨e, he, k, fun p q r hpqr => ?_⟩
  obtain ⟨hpq, hqr⟩ := hpqr
  have hlt1 : e p < e q := he hpq
  have hlt2 : e q < e r := he hqr
  have hlt0 : e p < e r := lt_trans hlt1 hlt2
  set t : Finset ℕ := {e p, e q, e r} with ht
  have hmem_iff : ∀ y ∈ t, y = e p ∨ y = e q ∨ y = e r := by
    intro y hy; rw [ht] at hy
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hy
  have hep : e p ∈ t := by rw [ht]; exact Finset.mem_insert_self _ _
  have heq : e q ∈ t := by rw [ht]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have her : e r ∈ t := by
    rw [ht]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have htne : t.Nonempty := ⟨e p, hep⟩
  have hpq_ne : e p ≠ e q := ne_of_lt hlt1
  have hpr_ne : e p ≠ e r := ne_of_lt hlt0
  have hqr_ne : e q ≠ e r := ne_of_lt hlt2
  have htcard : t.card = 3 := by
    rw [ht, Finset.card_insert_of_notMem (by simp [hpq_ne, hpr_ne]),
        Finset.card_insert_of_notMem (by simp [hqr_ne]), Finset.card_singleton]
  have htsub : ↑t ⊆ Set.range e := by
    rw [ht]; intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [⟨p, rfl⟩, ⟨q, rfl⟩, ⟨r, rfl⟩]
  have hmin : t.min' htne = e p := by
    apply le_antisymm (Finset.min'_le _ _ hep)
    apply Finset.le_min'
    intro y hy; rcases hmem_iff y hy with rfl | rfl | rfl
    exacts [le_refl _, le_of_lt hlt1, le_of_lt hlt0]
  have hmax : t.max' htne = e r := by
    apply le_antisymm _ (Finset.le_max' _ _ her)
    apply Finset.max'_le
    intro y hy; rcases hmem_iff y hy with rfl | rfl | rfl
    exacts [le_of_lt hlt0, le_of_lt hlt2, le_refl _]
  -- the middle element is the least element of `t` with the minimum removed
  have hqmem : e q ∈ t.erase (t.min' htne) := by
    rw [Finset.mem_erase, hmin]; exact ⟨Ne.symm hpq_ne, heq⟩
  have H2 : (t.erase (t.min' htne)).Nonempty := ⟨e q, hqmem⟩
  have hmid : (t.erase (t.min' htne)).min' H2 = e q := by
    apply le_antisymm (Finset.min'_le _ _ hqmem)
    apply Finset.le_min'
    intro y hy
    rw [Finset.mem_erase, hmin] at hy
    obtain ⟨hyne, hyt⟩ := hy
    rcases hmem_iff y hyt with rfl | rfl | rfl
    · exact absurd rfl hyne
    · exact le_refl _
    · exact le_of_lt hlt2
  -- the ordering condition holds; evaluate `C t`
  have Hcond : t.min' htne < (t.erase (t.min' htne)).min' H2 ∧
      (t.erase (t.min' htne)).min' H2 < t.max' htne := by
    refine ⟨?_, ?_⟩
    · rw [hmid, hmin]; exact hlt1
    · rw [hmid, hmax]; exact hlt2
  have key : ∀ (A B D : ℕ) (pf : A < B ∧ B < D), A = e p → B = e q → D = e r →
      c A B D pf = c (e p) (e q) (e r) ⟨hlt1, hlt2⟩ := by
    rintro A B D pf rfl rfl rfl; rfl
  have hCt : C t = c (e p) (e q) (e r) ⟨hlt1, hlt2⟩ := by
    have hval : C t =
        c (t.min' htne) ((t.erase (t.min' htne)).min' H2) (t.max' htne) Hcond := by
      simp only [hC]
      rw [dite_eq_left htne, dite_eq_left H2, dite_eq_left Hcond]
    rw [hval]
    exact key _ _ _ Hcond hmin hmid hmax
  have hkt : C t = k := hk t htsub htcard
  rw [hCt] at hkt
  exact hkt

end
