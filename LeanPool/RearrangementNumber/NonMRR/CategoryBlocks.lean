/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import LeanPool.RearrangementNumber.NonMRR.Category

/-!
# Finite-block descriptions of meagre sets in Cantor space

This is the topological coding ingredient of the Bartoszyński–Miller
characterisation. It does not identify any cardinal invariant by definition.
-/

@[expose] public section

open Set Filter

namespace NonMRR

/-- Replace the first `n` coordinates by a prescribed finite word. -/
def replacePrefix (n : ℕ) (s : Fin n → Bool) (x : ℕ → Bool) : ℕ → Bool :=
  fun i => if hi : i < n then s ⟨i, hi⟩ else x i

theorem continuous_replacePrefix (n : ℕ) (s : Fin n → Bool) :
    Continuous (replacePrefix n s) := by
  apply continuous_pi
  intro i
  by_cases hi : i < n
  · simpa only [replacePrefix, dite_eq_left hi] using
      (continuous_const : Continuous (fun _ : ℕ → Bool => s ⟨i, hi⟩))
  · simpa only [replacePrefix, dite_eq_right hi] using
      (continuous_apply i : Continuous (fun x : ℕ → Bool => x i))

/-- Fixing finitely many coordinates pulls a dense set back to a dense set. -/
theorem dense_preimage_replacePrefix (n : ℕ) (s : Fin n → Bool)
    {U : Set (ℕ → Bool)} (hU : Dense U) : Dense (replacePrefix n s ⁻¹' U) := by
  classical
  apply dense_iff_inter_open.mpr
  intro O hO hOne
  obtain ⟨f, hf⟩ := hOne
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hO f hf
  let v (i : ℕ) : Set Bool := if hi : i < n then {s ⟨i, hi⟩} else u i
  let J : Finset ℕ := Finset.range n ∪ I
  have hVopen : IsOpen ((J : Set ℕ).pi v) := by
    apply isOpen_set_pi J.finite_toSet
    intro i hi
    by_cases hin : i < n
    · simp only [v, dite_eq_left hin]
      exact isOpen_discrete _
    · simp only [v, dite_eq_right hin]
      apply (hu i ?_).1
      have hi' : i ∈ Finset.range n ∪ I := hi
      simpa [Finset.mem_union, Finset.mem_range, hin] using hi'
  have hVne : ((J : Set ℕ).pi v).Nonempty := by
    refine ⟨replacePrefix n s f, ?_⟩
    intro i hi
    by_cases hin : i < n
    · simp [replacePrefix, v, hin]
    · have hiI : i ∈ I := by
        have hi' : i ∈ Finset.range n ∪ I := hi
        simpa [Finset.mem_union, Finset.mem_range, hin] using hi'
      simpa only [replacePrefix, v, dite_eq_right hin] using (hu i hiI).2
  obtain ⟨y, hyU, hyV⟩ := hU.exists_mem_open hVopen hVne
  let z : ℕ → Bool := fun i => if i < n then f i else y i
  refine ⟨z, hsub ?_, ?_⟩
  · intro i hi
    by_cases hin : i < n
    · simpa only [z, ite_eq_left hin] using (hu i hi).2
    · have hy := hyV i (Finset.mem_union_right (Finset.range n) hi)
      simpa only [z, ite_eq_right hin, v, dite_eq_right hin] using hy
  · have heq : replacePrefix n s z = y := by
      funext i
      by_cases hin : i < n
      · have hy := hyV i (Finset.mem_union_left I (Finset.mem_range.mpr hin))
        have hys : y i = s ⟨i, hin⟩ := by
          simpa only [v, dite_eq_left hin, Set.mem_singleton_iff] using hy
        simp only [replacePrefix, dite_eq_left hin, hys]
      · simp only [replacePrefix, dite_eq_right hin, z, ite_eq_right hin]
    simpa only [Set.mem_preimage, heq] using hyU

/-- A dense open subset of Cantor space contains a cylinder determined
by a finite block starting at any prescribed coordinate. -/
theorem exists_tail_block_subset_of_dense_open (n : ℕ)
    {U : Set (ℕ → Bool)} (hUopen : IsOpen U) (hUdense : Dense U) :
    ∃ m > n, ∃ a : ℕ → Bool,
      ∀ x : ℕ → Bool, (∀ i, n ≤ i → i < m → x i = a i) → x ∈ U := by
  classical
  let V : Set (ℕ → Bool) := ⋂ s : Fin n → Bool, replacePrefix n s ⁻¹' U
  have hVopen : IsOpen V := isOpen_iInter_of_finite fun s =>
    hUopen.preimage (continuous_replacePrefix n s)
  have hVdense : Dense V := dense_iInter_of_isOpen
    (fun s => hUopen.preimage (continuous_replacePrefix n s))
    (fun s => dense_preimage_replacePrefix n s hUdense)
  obtain ⟨a, ha⟩ := hVdense.nonempty
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hVopen a ha
  let m := max (n + 1) (I.sup id + 1)
  have hnm : n < m := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_left _ _)
  refine ⟨m, hnm, a, ?_⟩
  intro x hx
  let z : ℕ → Bool := fun i => if i < n then a i else x i
  have hz : z ∈ V := by
    apply hsub
    intro i hi
    by_cases hin : i < n
    · simpa only [z, ite_eq_left hin] using (hu i hi).2
    · have him : i < m := by
        have hle : i ≤ I.sup id := Finset.le_sup (f := id) hi
        exact lt_of_lt_of_le (Nat.lt_succ_of_le hle) (le_max_right _ _)
      simpa only [z, ite_eq_right hin, hx i (Nat.le_of_not_gt hin) him] using (hu i hi).2
  have heq : replacePrefix n (fun i : Fin n => x i) z = x := by
    funext i
    by_cases hin : i < n <;> simp [replacePrefix, z, hin]
  have hzx : replacePrefix n (fun i : Fin n => x i) z ∈ U :=
    Set.mem_iInter.mp hz (fun i => x i)
  rwa [heq] at hzx

/-- Every meagre set in Cantor space is contained in a set described by
eventual failure to match prescribed finite blocks. -/
theorem meagre_subset_eventually_misses_blocks {M : Set (ℕ → Bool)}
    (hM : IsMeagre M) :
    ∃ g : ℕ → ℕ, ∃ a : ℕ → ℕ → Bool,
      (∀ n, n < g n) ∧ ∀ x ∈ M, ∀ᶠ n in atTop,
        ¬ (∀ i, n ≤ i → i < g n → x i = a n i) := by
  classical
  obtain ⟨S, hS, hc, hcover⟩ := isMeagre_iff_countable_union_isNowhereDense.mp hM
  let F : ℕ → Set (ℕ → Bool) := Set.enumerateCountable hc ∅
  have hF (n : ℕ) : IsNowhereDense (F n) := by
    have hn : F n ∈ insert ∅ S :=
      Set.range_enumerateCountable_subset hc ∅ (Set.mem_range_self n)
    rcases Set.mem_insert_iff.mp hn with he | hs
    · rw [he]
      exact isNowhereDense_empty
    · exact hS _ hs
  let U (n : ℕ) : Set (ℕ → Bool) := ⋂ i : Fin (n + 1), (closure (F i))ᶜ
  have hUopen (n : ℕ) : IsOpen (U n) :=
    isOpen_iInter_of_finite fun _ => isClosed_closure.isOpen_compl
  have hUdense (n : ℕ) : Dense (U n) := by
    apply dense_iInter_of_isOpen (fun _ => isClosed_closure.isOpen_compl)
    intro i
    exact ((isClosed_isNowhereDense_iff_compl).mp
      ⟨isClosed_closure, (hF i).closure⟩).2
  choose g hg a ha using fun n =>
    exists_tail_block_subset_of_dense_open n (hUopen n) (hUdense n)
  refine ⟨g, a, hg, ?_⟩
  intro x hx
  obtain ⟨s, hsS, hxs⟩ := Set.mem_sUnion.mp (hcover hx)
  obtain ⟨j, hj⟩ := Set.subset_range_enumerate hc ∅ hsS
  have hxF : x ∈ F j := by simpa only [F, hj] using hxs
  filter_upwards [eventually_ge_atTop j] with n hn
  intro hmatches
  have hxU := ha n x hmatches
  have hxnot : x ∉ closure (F j) :=
    Set.mem_iInter.mp hxU ⟨j, by omega⟩
  exact hxnot (subset_closure hxF)

/-- A set of eventual failures to match blocks is itself meagre. -/
theorem isMeagre_eventually_misses_blocks (g : ℕ → ℕ) (a : ℕ → ℕ → Bool) :
    IsMeagre {x : ℕ → Bool | ∀ᶠ n in atTop,
      ¬ (∀ i, n ≤ i → i < g n → x i = a n i)} := by
  classical
  let B (n : ℕ) : Set (ℕ → Bool) :=
    {x | ∀ i, n ≤ i → i < g n → x i = a n i}
  have hBopen (n : ℕ) : IsOpen (B n) := by
    have heq : B n = (Finset.Ico n (g n) : Set ℕ).pi (fun i => {a n i}) := by
      ext x
      simp [B, Set.mem_pi, and_imp]
    rw [heq]
    exact isOpen_set_pi (Finset.finite_toSet _) (fun _ _ => isOpen_discrete _)
  let F (N : ℕ) : Set (ℕ → Bool) := {x | ∀ n, N ≤ n → x ∉ B n}
  have hFclosed (N : ℕ) : IsClosed (F N) := by
    have heq : F N = ⋂ n, ⋂ (_ : N ≤ n), (B n)ᶜ := by
      ext x
      simp [F]
    rw [heq]
    exact isClosed_iInter fun n => isClosed_iInter fun _ => (hBopen n).isClosed_compl
  have hFnowhere (N : ℕ) : IsNowhereDense (F N) := by
    rw [(hFclosed N).isNowhereDense_iff]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp isOpen_interior f hf
    let n := max N (I.sup id + 1)
    let y : ℕ → Bool := fun i => if n ≤ i ∧ i < g n then a n i else f i
    have hy : y ∈ interior (F N) := by
      apply hsub
      intro i hi
      have hin : ¬ n ≤ i := by
        have hi' : i ≤ I.sup id := Finset.le_sup (f := id) hi
        have hn' : I.sup id + 1 ≤ n := le_max_right _ _
        omega
      simpa only [y, hin, false_and, ite_false] using (hu i hi).2
    have hyB : y ∈ B n := by
      intro i hi hig
      simp only [y, hi, hig, and_self, ite_true]
    exact interior_subset hy n (le_max_left _ _) hyB
  have heq : {x : ℕ → Bool | ∀ᶠ n in atTop,
      ¬ (∀ i, n ≤ i → i < g n → x i = a n i)} = ⋃ N, F N := by
    ext x
    simp only [Set.mem_ofPred_eq, eventually_atTop, Set.mem_iUnion, F, B]
  rw [heq]
  exact isMeagre_iUnion fun N => (hFnowhere N).isMeagre

/-- The finite-block coding characterisation of meagre sets in Cantor space. -/
theorem isMeagre_iff_eventually_misses_blocks {M : Set (ℕ → Bool)} :
    IsMeagre M ↔ ∃ g : ℕ → ℕ, ∃ a : ℕ → ℕ → Bool,
      (∀ n, n < g n) ∧ ∀ x ∈ M, ∀ᶠ n in atTop,
        ¬ (∀ i, n ≤ i → i < g n → x i = a n i) := by
  constructor
  · exact meagre_subset_eventually_misses_blocks
  · rintro ⟨g, a, _, h⟩
    exact (isMeagre_eventually_misses_blocks g a).mono h

/-- Blocks fitting between consecutive points of a strictly increasing
sequence can be pasted into one element of Cantor space. -/
theorem exists_pasted_blocks (t : ℕ → ℕ) (ht : StrictMono t)
    (g : ℕ → ℕ) (a : ℕ → ℕ → Bool) :
    ∃ x : ℕ → Bool, ∀ k, g (t k) < t (k + 1) →
      ∀ i, t k ≤ i → i < g (t k) → x i = a (t k) i := by
  classical
  let P (i k : ℕ) : Prop := g (t k) < t (k + 1) ∧ t k ≤ i ∧ i < g (t k)
  have huniq {i k l : ℕ} (hk : P i k) (hl : P i l) : k = l := by
    rcases lt_trichotomy k l with hkl | hkl | hkl
    · have hle : t (k + 1) ≤ t l := ht.monotone (Nat.succ_le_of_lt hkl)
      have hki : i < t (k + 1) := hk.2.2.trans hk.1
      exact False.elim ((not_lt_of_ge (hle.trans hl.2.1)) hki)
    · exact hkl
    · have hle : t (l + 1) ≤ t k := ht.monotone (Nat.succ_le_of_lt hkl)
      have hli : i < t (l + 1) := hl.2.2.trans hl.1
      exact False.elim ((not_lt_of_ge (hle.trans hk.2.1)) hli)
  let x : ℕ → Bool := fun i =>
    if hi : ∃ k, P i k then a (t (Classical.choose hi)) i else false
  refine ⟨x, ?_⟩
  intro k hk i hki hig
  have hex : ∃ l, P i l := ⟨k, hk, hki, hig⟩
  have heq : Classical.choose hex = k := huniq (Classical.choose_spec hex) ⟨hk, hki, hig⟩
  simp only [x, dite_eq_left hex, heq]

/-- Infinitely many shared fitting blocks force the pasted point outside
the meagre set coded by the second collection of blocks. -/
theorem pasted_blocks_frequently_match
    {t : ℕ → ℕ} (ht : StrictMono t) {g h : ℕ → ℕ}
    {a b : ℕ → ℕ → Bool} {x : ℕ → Bool}
    (hxpaste : ∀ k, g (t k) < t (k + 1) →
      ∀ i, t k ≤ i → i < g (t k) → x i = a (t k) i)
    (hmatch : ∃ᶠ k in atTop, h (t k) < t (k + 1) ∧
      g (t k) = h (t k) ∧
      (∀ i, t k ≤ i → i < h (t k) → a (t k) i = b (t k) i)) :
    ∃ᶠ n in atTop, ∀ i, n ≤ i → i < h n → x i = b n i := by
  rw [frequently_atTop] at hmatch ⊢
  intro N
  obtain ⟨k, hkN, hkgap, hkend, hkbits⟩ := hmatch N
  refine ⟨t k, hkN.trans (ht.id_le k), ?_⟩
  intro i hki hig
  have hgap : g (t k) < t (k + 1) := by rwa [hkend]
  have hig' : i < g (t k) := by rwa [hkend]
  exact (hxpaste k hgap i hki hig').trans (hkbits i hki hig)

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
