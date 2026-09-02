/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import LeanPool.NashWilliams.Combinatorics.Front.Rank

/-!
# The ray of a front

Given a front `F` on `M` and a node `[a]` of its tree (i.e. `a` is the least element of some
element of `F`), the *ray* `F after a` (terminology from the author's EMS survey *Towards better:
A motivated introduction to better-quasi-orders*) is the front obtained by stripping the leading
`a` from the elements of `F` that start with `a`. It is a front on `M after a`, the infinite set
`{n ∈ M : n > a}`, itself represented enumeration-first as the subsequence `M ∘ (· + j)` where
`j` is the least index at which `M` passes `a`.

("Ray" is not to be confused with the *derivative*, the tree-to-tree leaf-removal operation whose
iteration computes the rank.)

## Main definitions

* `rayEnum M a` : the enumeration `M ∘ (· + afterShift M a)` of `{n ∈ M : n > a}` (front-
  independent).
* `Front.ray F a` : the ray `{t | a :: t ∈ F}`.

## Main results

* `Front.ray_isFront` : the ray `F after a` is a front on `M after a`.
* `Front.IsFront.singleton_mem_tree` : in a nontrivial front (`[] ∉ F`) every `n ∈ M` heads an
  element, i.e. `[n] ∈ tree F`.
* `Front.IsFront.ray_isFront_mem` : for a nontrivial front and `n ∈ M`, `F after n` is a front
  on `M after n`.

## Nontriviality

The trivial front is `{[]}` (rank `0`). For a front, `[] ∉ F`, `F ≠ {[]}`, `⋃ F = M`, and
"`[n] ∈ tree F` for every `n ∈ M`" are all equivalent; `[] ∉ F` is the canonical working flag
(see `IsFront.nil_not_mem_iff`).
-/

open Set List

noncomputable section

variable {M : ℕ → ℕ}

/-! ### Enumeration operations

`afterShift` and `rayEnum` operate on a strictly monotone enumeration `M : ℕ → ℕ`; they do not
depend on any front, so they live outside the `Front` namespace. -/

/-- The least index at which `M` passes `a`. -/
def afterShift (M : ℕ → ℕ) (a : ℕ) : ℕ := sInf {j | a < M j}

/-- `M after a`: the increasing enumeration of `{n ∈ M : n > a}`, as the subsequence
`M ∘ (· + afterShift M a)`. A `StrictMono`-to-`StrictMono` operation on enumerations. -/
def rayEnum (M : ℕ → ℕ) (a : ℕ) : ℕ → ℕ := fun i => M (i + afterShift M a)

theorem afterShift_spec (hM : StrictMono M) (a : ℕ) : a < M (afterShift M a) := by
  have hne : {j | a < M j}.Nonempty :=
    ⟨a + 1, lt_of_lt_of_le (Nat.lt_succ_self a) (hM.le_apply : a + 1 ≤ M (a + 1))⟩
  exact Nat.sInf_mem hne

theorem lt_of_lt_afterShift {a k : ℕ} (hk : k < afterShift M a) : M k ≤ a := by
  by_contra h
  have hle : afterShift M a ≤ k := Nat.sInf_le (Nat.lt_of_not_le h)
  omega

theorem rayEnum_strictMono (hM : StrictMono M) (a : ℕ) : StrictMono (rayEnum M a) :=
  fun _ _ hxy => hM (by omega)

theorem rayEnum_gt (hM : StrictMono M) (a i : ℕ) : a < rayEnum M a i :=
  lt_of_lt_of_le (afterShift_spec hM a) (hM.monotone (by omega))

theorem rayEnum_mem_range (a i : ℕ) : rayEnum M a i ∈ Set.range M :=
  ⟨i + afterShift M a, rfl⟩

theorem mem_range_rayEnum_iff (hM : StrictMono M) (a n : ℕ) :
    n ∈ Set.range (rayEnum M a) ↔ n ∈ Set.range M ∧ a < n := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨rayEnum_mem_range a i, rayEnum_gt hM a i⟩
  · rintro ⟨⟨k, rfl⟩, hlt⟩
    have hk : afterShift M a ≤ k := Nat.sInf_le hlt
    exact ⟨k - afterShift M a, by rw [rayEnum]; congr 1; omega⟩

namespace Front

variable {F : Set (List ℕ)}

/-- `F after a` (the *ray* of `F` at `a`): strip the leading `a` from the elements of `F` that
start with `a`. -/
def ray (F : Set (List ℕ)) (a : ℕ) : Set (List ℕ) := {t | a :: t ∈ F}

/-- Density transported: any strictly monotone subsequence of `M` has an initial segment in `F`. -/
theorem exists_frontElem_isInit (hF : IsFront F M) {N : ℕ → ℕ} (hN : StrictMono N)
    (hsub : Set.range N ⊆ Set.range M) : ∃ u ∈ F, IsInit u N := by
  obtain ⟨h, hh, hcomp⟩ := exists_strictMono_comp hF.mono hN fun i => hsub ⟨i, rfl⟩
  obtain ⟨u, hu, hInit⟩ := hF.dense h hh
  rw [hcomp] at hInit
  exact ⟨u, hu, hInit⟩

theorem nil_not_mem (hF : IsFront F M) {a : ℕ} (ha : [a] ∈ tree F) : [] ∉ F := by
  intro hnil
  obtain ⟨w, hw, hpre⟩ := ha
  have := hF.incomp [] hnil w hw List.nil_prefix
  rw [← this] at hpre
  simpa using hpre.length_le

/-- A front is *nontrivial* (`[] ∉ F`) iff it is not the trivial front `{[]}`. -/
theorem IsFront.nil_not_mem_iff (hF : IsFront F M) : [] ∉ F ↔ F ≠ {[]} := by
  constructor
  · intro h heq; exact h (by simp [heq])
  · intro hne hnil
    apply hne
    ext t
    simp only [Set.mem_singleton_iff]
    exact ⟨fun ht => (hF.incomp [] hnil t ht List.nil_prefix).symm, fun h => h ▸ hnil⟩

/-- **In a nontrivial front, every element of `M` heads some element of `F`.** For `[] ∉ F` and
`n ∈ M`, the singleton `[n]` is a node of the tree of `F`. -/
theorem IsFront.singleton_mem_tree (hF : IsFront F M) (h0 : [] ∉ F) {n : ℕ}
    (hn : n ∈ Set.range M) : [n] ∈ tree F := by
  obtain ⟨k, rfl⟩ := hn
  set N : ℕ → ℕ := fun i => M (i + k) with hN
  have hNmono : StrictMono N := fun x y h => hF.mono (by omega)
  have hNsub : Set.range N ⊆ Set.range M := by rintro _ ⟨i, rfl⟩; exact ⟨i + k, rfl⟩
  obtain ⟨u, hu, hInit⟩ := exists_frontElem_isInit hF hNmono hNsub
  have hune : u ≠ [] := fun h => h0 (h ▸ hu)
  have hhead : u.head? = some (M k) := by rw [hInit.head_eq hune]; simp [hN]
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hhead
  exact ⟨u, hu, hys ▸ ⟨ys, rfl⟩⟩

/-- The head-stripping construction: if `[a]` is in the tree and `Q` is a strictly monotone
subsequence of `M` with `a < Q 0`, then some `a :: t ∈ F` with `t` an initial segment of `Q`. -/
theorem exists_cons_mem (hF : IsFront F M) {a : ℕ} (ha : [a] ∈ tree F)
    {Q : ℕ → ℕ} (hQ : StrictMono Q) (haQ : a < Q 0) (hQM : ∀ i, Q i ∈ Set.range M) :
    ∃ t, a :: t ∈ F ∧ IsInit t Q := by
  have haM : a ∈ Set.range M := by
    obtain ⟨w, hw, hpre⟩ := ha
    exact hF.subM w hw a (hpre.subset (List.mem_singleton_self a))
  set N : ℕ → ℕ := fun i => if i = 0 then a else Q (i - 1) with hN
  have hN0 : N 0 = a := by simp [hN]
  have hNsucc : ∀ k, N (k + 1) = Q k := by intro k; simp [hN]
  have hNmono : StrictMono N := by
    apply strictMono_nat_of_lt_succ
    intro i
    cases i with
    | zero => rw [hN0, hNsucc]; exact haQ
    | succ k => rw [hNsucc, hNsucc]; exact hQ (Nat.lt_succ_self k)
  have hNsub : Set.range N ⊆ Set.range M := by
    rintro _ ⟨i, rfl⟩
    cases i with
    | zero => rw [hN0]; exact haM
    | succ k => rw [hNsucc]; exact hQM k
  obtain ⟨u, hu, hInit⟩ := exists_frontElem_isInit hF hNmono hNsub
  have hune : u ≠ [] := fun h => nil_not_mem hF ha (h ▸ hu)
  obtain ⟨m, hm⟩ : ∃ m, u.length = m + 1 := ⟨u.length - 1, by
    have : 0 < u.length := List.length_pos_iff.mpr hune; omega⟩
  have hu_eq : u = a :: (List.range m).map Q := by
    rw [hInit, hm, List.range_succ_eq_map, List.map_cons, hN0]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro k _
    exact hNsucc k
  refine ⟨(List.range m).map Q, ?_, isInit_take Q m⟩
  rw [← hu_eq]; exact hu

/-- **`F after a` is a front on `M after a`**, whenever `[a]` is a node of the tree of `F`
(i.e. `a` is the least element of some element of `F`). -/
theorem ray_isFront (hF : IsFront F M) {a : ℕ} (ha : [a] ∈ tree F) :
    IsFront (ray F a) (rayEnum M a) where
  mono := rayEnum_strictMono hF.mono a
  sorted t ht := (hF.sorted (a :: t) ht).of_cons
  subM t ht x hx := by
    have hxM : x ∈ Set.range M := hF.subM (a :: t) ht x (List.mem_cons_of_mem a hx)
    have hax : a < x := (List.pairwise_cons.mp (hF.sorted (a :: t) ht)).1 x hx
    exact (mem_range_rayEnum_iff hF.mono a x).mpr ⟨hxM, hax⟩
  incomp s hs t ht hst := by
    have heq : a :: s = a :: t :=
      hF.incomp (a :: s) hs (a :: t) ht ((List.prefix_cons_inj a).mpr hst)
    injection heq with _ h
  dense g hg := by
    have hQmono : StrictMono (rayEnum M a ∘ g) := (rayEnum_strictMono hF.mono a).comp hg
    obtain ⟨t, htF, htInit⟩ := exists_cons_mem hF ha hQmono
      (by exact rayEnum_gt hF.mono a (g 0)) (fun i => rayEnum_mem_range a (g i))
    exact ⟨t, htF, htInit⟩
  base := by
    by_cases haF : [a] ∈ F
    · left
      ext t
      simp only [ray, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro ht
        have heq := hF.incomp [a] haF (a :: t) ht ((List.prefix_cons_inj a).mpr List.nil_prefix)
        injection heq with _ h; exact h.symm
      · rintro rfl; exact haF
    · right
      ext n
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨t, ht, hnt⟩
        have hxM : n ∈ Set.range M := hF.subM (a :: t) ht n (List.mem_cons_of_mem a hnt)
        have hax : a < n := (List.pairwise_cons.mp (hF.sorted (a :: t) ht)).1 n hnt
        exact (mem_range_rayEnum_iff hF.mono a n).mpr ⟨hxM, hax⟩
      · intro hn
        obtain ⟨hnM, hax⟩ := (mem_range_rayEnum_iff hF.mono a n).mp hn
        obtain ⟨k, rfl⟩ := hnM
        have hQmono : StrictMono (fun i => M (i + k)) := fun x y hxy => hF.mono (by omega)
        obtain ⟨t, htF, htInit⟩ := exists_cons_mem hF ha hQmono (by simpa using hax)
          (fun i => ⟨i + k, rfl⟩)
        have htne : t ≠ [] := by rintro rfl; exact haF htF
        have hhead : t.head? = some (M k) := by rw [htInit.head_eq htne]; simp
        refine ⟨t, htF, ?_⟩
        obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hhead
        rw [hys]; simp

/-- For a nontrivial front and `n ∈ M`, `F after n` is a front on `M after n`. -/
theorem IsFront.ray_isFront_mem (hF : IsFront F M) (h0 : [] ∉ F) {n : ℕ}
    (hn : n ∈ Set.range M) : IsFront (ray F n) (rayEnum M n) :=
  ray_isFront hF (hF.singleton_mem_tree h0 hn)

/-! ### Rank of the ray

The ray strictly lowers the rank. This is what makes the Nash-Williams recursion well-founded.

The tree of `ray F a` is the subtree of `tree F` sitting above the node `[a]`, transported by
`t ↦ a :: t`; `mem_tree_ray` is the membership bridge (the single point of contact with the
concrete `tree` representation — a later switch to `Descriptive.Tree.subAt` would rewrite only
this lemma). -/

/-- The tree of the ray at `a` is `tree F` above `[a]`, stripped of the leading `a`. -/
theorem mem_tree_ray {a : ℕ} {t : List ℕ} : t ∈ tree (ray F a) ↔ a :: t ∈ tree F := by
  constructor
  · rintro ⟨u, hu, hpre⟩
    exact ⟨a :: u, hu, (List.prefix_cons_inj a).mpr hpre⟩
  · rintro ⟨w, hw, hpre⟩
    obtain ⟨v, rfl⟩ := hpre
    exact ⟨t ++ v, hw, List.prefix_append t v⟩

/-- **The ray strictly lowers the rank.** For a nontrivial front and `n ∈ M`, the front
`F after n` has rank strictly below that of `F`. -/
theorem IsFront.ray_rank_lt (hF : IsFront F M) (h0 : [] ∉ F) {n : ℕ}
    (hn : n ∈ Set.range M) : (hF.ray_isFront_mem h0 hn).rank < hF.rank := by
  have ha : [n] ∈ tree F := hF.singleton_mem_tree h0 hn
  have iF : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
  have iR : IsWellFounded (List ℕ) (treeExt (ray F n)) :=
    ⟨(hF.ray_isFront_mem h0 hn).wellFounded_treeExt⟩
  -- The head-attaching map `t ↦ n :: t` is a relation homomorphism into `treeExt F`.
  let φ : treeExt (ray F n) →r treeExt F :=
    ⟨fun t => n :: t, by
      rintro x y ⟨hx, hy, hyx, hne⟩
      refine ⟨mem_tree_ray.mp hx, mem_tree_ray.mp hy, (List.prefix_cons_inj n).mpr hyx, ?_⟩
      intro hc; injection hc with _ h; exact hne h⟩
  have hle : IsWellFounded.rank (treeExt (ray F n)) [] ≤ IsWellFounded.rank (treeExt F) [n] :=
    φ.rank_le []
  have hlt : IsWellFounded.rank (treeExt F) [n] < IsWellFounded.rank (treeExt F) [] :=
    IsWellFounded.rank_lt_of_rel
      ⟨ha, hF.nil_mem_tree, List.nil_prefix, (List.cons_ne_nil n []).symm⟩
  change IsWellFounded.rank (treeExt (ray F n)) [] < IsWellFounded.rank (treeExt F) []
  exact lt_of_le_of_lt hle hlt

end Front
