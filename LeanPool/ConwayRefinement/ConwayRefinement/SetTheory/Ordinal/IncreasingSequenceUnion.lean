/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.SetOrderType
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPrincipal

/-!
# The union of an increasing sequence of well-ordered sets

A sequence `Y_0 < Y_1 < Y_2 < ⋯` of subsets of a linear order (Lean `B : ℕ → Set α`) is
*increasing* if every element of a later member lies strictly above every element of an earlier
one (the hypothesis `hord`). The union of an increasing sequence of partially well-ordered sets is
partially well ordered (`iUnion_of_ordered`): a strictly decreasing sequence in the union has
non-increasing indices of members, so from some point on it lies in a single member. Its order type
is bounded by any ordinal greater than every finite Hessenberg sum of copies of `ρ` when every
member has order type at most `ρ` (`orderType_iUnion_le_of_ordered`), and at most `ω^e` when every
member has order type below `ω^e`
(`orderType_iUnion_le_wpow_of_ordered`).

[Ber00, Lem. 4.1] is the case of two sets; [Ber00, Lem. 4.7], formalised in
`ConwayRefinement.SetTheory.Ordinal.OrderedUnion`, bounds a union indexed by an ordinal
from below.
-/

universe u v

open Order Ordinal
open scoped NatOrdinal

public noncomputable section

namespace Set.IsPWO

variable {α : Type u} [LinearOrder α] {B : ℕ → Set α}

/-- The union of a family of partially well-ordered sets, ordered by a partially well-ordered
linear index, is partially well ordered. -/
theorem iUnion_of_ordered_index {ι : Type v} [LinearOrder ι]
    (hι : (Set.univ : Set ι).IsPWO) (B : ι → Set α) (hB : ∀ i, (B i).IsPWO)
    (hord : ∀ i j, i < j → ∀ x ∈ B i, ∀ y ∈ B j, x < y) :
    (⋃ i, B i).IsPWO := by
  classical
  rw [Set.isPWO_iff_isWF, Set.isWF_iff_no_descending_seq]
  intro f hf hmem
  have hidx : ∀ n, ∃ i, f n ∈ B i := fun n ↦ Set.mem_iUnion.mp (hmem n)
  choose idx hidx using hidx
  have hanti : ∀ m n, m ≤ n → idx n ≤ idx m := by
    intro m n hmn
    by_contra hlt
    rw [not_le] at hlt
    rcases eq_or_lt_of_le hmn with rfl | hmn'
    · exact hlt.false
    · exact absurd (hord _ _ hlt (f m) (hidx m) (f n) (hidx n)) (hf hmn').not_gt
  have hrange : (Set.range idx).IsWF :=
    Set.IsWF.mono hι.isWF (Set.subset_univ (Set.range idx))
  have hrange_ne : (Set.range idx).Nonempty := Set.range_nonempty idx
  obtain ⟨N, hNval⟩ := hrange.min_mem hrange_ne
  have hNval' : idx N = hrange.min hrange_ne := hNval
  have hN : ∀ n, N ≤ n → idx n = idx N := by
    intro n hn
    exact le_antisymm (hanti N n hn)
      (not_lt.mp fun h ↦ hrange.not_lt_min hrange_ne ⟨n, rfl⟩ (hNval' ▸ h))
  have htail : ∀ n, f (N + n) ∈ B (idx N) := fun n ↦ by
    have := hidx (N + n)
    rwa [hN (N + n) (Nat.le_add_right N n)] at this
  have hstrict : StrictAnti fun n ↦ f (N + n) := fun m n hmn ↦ hf (by omega)
  exact (Set.isWF_iff_no_descending_seq.mp (hB (idx N)).isWF) _ hstrict htail

/-- The members of an increasing sequence of sets are pairwise disjoint. -/
theorem ordered_disjoint (hord : ∀ j k, j < k → ∀ x ∈ B j, ∀ y ∈ B k, x < y) {j k : ℕ}
    (hjk : j ≠ k) {x : α} (hj : x ∈ B j) (hk : x ∈ B k) : False := by
  rcases hjk.lt_or_gt with h | h
  · exact (hord j k h x hj x hk).false
  · exact (hord k j h x hk x hj).false

/-- An element of the union of an increasing sequence of sets lies in exactly one member. -/
theorem exists_unique_index (hord : ∀ j k, j < k → ∀ x ∈ B j, ∀ y ∈ B k, x < y) {x : α}
    (hx : x ∈ ⋃ k, B k) : ∃! k, x ∈ B k := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  exact ⟨k, hk, fun j hj ↦ by
    by_contra hne
    exact ordered_disjoint hord hne hj hk⟩

/-- The union of an ordered sequence of well-ordered subsets of a linear order is well ordered. -/
@[blueprint "lem:increasing-union"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Well-ordering of a countable ordered union")
  (statement := /--
    Let $(Y_n)$ be well-ordered subsets of a linear order, and suppose $x<y$
    whenever $x\in Y_j$, $y\in Y_k$, and $j<k$. Then $\bigcup_nY_n$ is
    well ordered.
  -/)
  (proof := /--
  A decreasing sequence in the union determines a nonincreasing sequence of
  block indices, hence eventually lies in one $Y_n$, contradicting that $Y_n$
  is well ordered.
  -/)]
theorem iUnion_of_ordered (hB : ∀ k, (B k).IsPWO)
    (hord : ∀ j k, j < k → ∀ x ∈ B j, ∀ y ∈ B k, x < y) : (⋃ k, B k).IsPWO := by
  classical
  rw [Set.isPWO_iff_isWF, Set.isWF_iff_no_descending_seq]
  intro f hf hmem
  -- the index of the member containing `f n`
  have hidx : ∀ n, ∃ k, f n ∈ B k := fun n ↦ Set.mem_iUnion.mp (hmem n)
  choose idx hidx using hidx
  -- the indices are non-increasing
  have hanti : ∀ m n, m ≤ n → idx n ≤ idx m := by
    intro m n hmn
    by_contra hlt
    rw [not_le] at hlt
    rcases eq_or_lt_of_le hmn with rfl | hmn'
    · exact hlt.false
    · exact absurd (hord _ _ hlt (f m) (hidx m) (f n) (hidx n)) (hf hmn').not_gt
  -- a non-increasing sequence of naturals is eventually constant
  obtain ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n → idx n = idx N := by
    obtain ⟨N, hN⟩ := Nat.lt_wfRel.wf.has_min (Set.range idx) ⟨idx 0, 0, rfl⟩
    obtain ⟨N, rfl⟩ := hN.1
    exact ⟨N, fun n hn ↦ le_antisymm (hanti N n hn)
      (not_lt.mp fun h ↦ hN.2 (idx n) ⟨n, rfl⟩ h)⟩
  -- from `N` on the sequence lies in one member, contradicting its well-foundedness
  have htail : ∀ n, f (N + n) ∈ B (idx N) := fun n ↦ by
    have := hidx (N + n)
    rwa [hN (N + n) (Nat.le_add_right N n)] at this
  have hstrict : StrictAnti fun n ↦ f (N + n) := fun m n hmn ↦ hf (by omega)
  exact (Set.isWF_iff_no_descending_seq.mp (hB (idx N)).isWF) _ hstrict htail

/-! ### The order type of the union -/

variable {ρ : Ordinal.{u}}

/-- The union of the first `n` members is partially well ordered. -/
private theorem isPWO_iUnion_lt (hB : ∀ k, (B k).IsPWO) (n : ℕ) :
    (⋃ k ∈ Finset.range n, B k).IsPWO := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    have : (⋃ k ∈ Finset.range (n + 1), B k) = (⋃ k ∈ Finset.range n, B k) ∪ B n := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨k, hk, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact Or.inl ⟨k, hk, hx⟩
        · exact Or.inr hx
      · rintro (⟨k, hk, hx⟩ | hx)
        · exact ⟨k, by omega, hx⟩
        · exact ⟨n, by omega, hx⟩
    rw [this]
    exact ih.union (hB n)

/-- The order type of the union of the first `n` members is at most the natural sum of `n` copies
of a common bound `ρ`. -/
private theorem orderType_iUnion_lt_le (hB : ∀ k, (B k).IsPWO) (hρ : ∀ k, (hB k).orderType ≤ ρ)
    (n : ℕ) : (isPWO_iUnion_lt hB n).orderType ≤ (n • NatOrdinal.of ρ).val := by
  classical
  induction n with
  | zero =>
    have hempty : (⋃ k ∈ Finset.range 0, B k) = (∅ : Set α) := by simp
    rw [Set.IsPWO.orderType_congr _ (Set.isPWO_empty) hempty, zero_nsmul]
    simp [(Set.isPWO_empty (α := α)).orderType_eq_zero.mpr rfl]
  | succ n ih =>
    have hsplit : (⋃ k ∈ Finset.range (n + 1), B k) = (⋃ k ∈ Finset.range n, B k) ∪ B n := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨k, hk, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact Or.inl ⟨k, hk, hx⟩
        · exact Or.inr hx
      · rintro (⟨k, hk, hx⟩ | hx)
        · exact ⟨k, by omega, hx⟩
        · exact ⟨n, by omega, hx⟩
    rw [Set.IsPWO.orderType_congr _ ((isPWO_iUnion_lt hB n).union (hB n)) hsplit]
    refine ((isPWO_iUnion_lt hB n).orderType_union_le_naturalAdd (hB n)).trans ?_
    rw [succ_nsmul]
    exact NatOrdinal.val.le_iff_le.mpr
      (add_le_add (NatOrdinal.of.le_iff_le.mpr ih) (NatOrdinal.of.le_iff_le.mpr (hρ n)))

/-- **The order type of the union of an increasing sequence of sets** is at most any `o` exceeding
every natural sum of finitely many copies of a common bound `ρ` on the order types of the
members. -/
@[blueprint "lem:increasing-union-order-type"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Order type of a countable ordered union")
  (statement := /--
    Let $(Y_n)$ be well-ordered subsets of a linear order, and suppose $x<y$
    whenever $x\in Y_j$, $y\in Y_k$, and $j<k$. If
    $\operatorname{ot}(Y_n)\le\rho$ for every $n$, and
    $n\odot\rho<o$ for every $n\in\mathbb N$, then
    $\operatorname{ot}(\bigcup_nY_n)\le o$.
  -/)
  (proof := /--
  By \ref{lem:increasing-union}, the union is well ordered. Every initial
  segment ending in $Y_n$ lies in the finite union of the first $n+1$ blocks,
  whose order type is at most the Hessenberg sum of $n+1$ copies of $\rho$.
  -/)]
theorem orderType_iUnion_le_of_ordered (hB : ∀ k, (B k).IsPWO)
    (hord : ∀ j k, j < k → ∀ x ∈ B j, ∀ y ∈ B k, x < y)
    (hρ : ∀ k, (hB k).orderType ≤ ρ) {o : Ordinal.{u}}
    (ho : ∀ n : ℕ, (n • NatOrdinal.of ρ).val < o) :
    (iUnion_of_ordered hB hord).orderType ≤ o := by
  classical
  let hU := iUnion_of_ordered hB hord
  change hU.orderType ≤ o
  refine hU.orderType_le_of_forall_inter_Iic_lt fun x hx ↦ ?_
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  have hsub : (⋃ j, B j) ∩ Set.Iic x ⊆ ⋃ j ∈ Finset.range (k + 1), B j := by
    rintro y ⟨hy, hyx⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨?_, hj⟩⟩
    rw [Finset.mem_range]
    by_contra hjk
    rw [not_lt, Nat.succ_le_iff] at hjk
    exact absurd (hord k j hjk x hk y hj) (not_lt.mpr hyx)
  calc (hU.mono (s := (⋃ j, B j) ∩ Set.Iic x) Set.inter_subset_left).orderType
      ≤ (isPWO_iUnion_lt hB (k + 1)).orderType :=
        Set.IsPWO.orderType_mono _ _ hsub
    _ ≤ ((k + 1) • NatOrdinal.of ρ).val := orderType_iUnion_lt_le hB hρ (k + 1)
    _ < o := ho (k + 1)

/-- **The order type of the union of an increasing sequence of sets of order types below `ω^e`**
is at most `ω^e`. -/
@[blueprint "lem:increasing-union-below-principal-ordinal"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Countable ordered unions below $\\omega^e$")
  (statement := /--
    Let $(Y_n)$ be well-ordered subsets of a linear order, and suppose $x<y$
    whenever $x\in Y_j$, $y\in Y_k$, and $j<k$. If
    $\operatorname{ot}(Y_n)<\omega^e$ for every $n$, then
    $\operatorname{ot}(\bigcup_nY_n)\le\omega^e$.
  -/)
  (proof := /--
  By \ref{lem:increasing-union}, the union is well ordered. Induction on $m$
  shows that the union of the first $m$ blocks has order type below $\omega^e$:
  the order type of a union is bounded by the Hessenberg sum, and the
  Hessenberg sum of two ordinals below $\omega^e$ remains below $\omega^e$.
  Every initial segment of the full union is contained in one such finite union.
  -/)]
theorem orderType_iUnion_le_wpow_of_ordered (hB : ∀ k, (B k).IsPWO)
    (hord : ∀ j k, j < k → ∀ x ∈ B j, ∀ y ∈ B k, x < y) {e : NatOrdinal.{u}}
    (hρ : ∀ k, (hB k).orderType < (ω^ e).val) :
    (iUnion_of_ordered hB hord).orderType ≤ (ω^ e).val := by
  classical
  let hU := iUnion_of_ordered hB hord
  change hU.orderType ≤ (ω^ e).val
  have hfin : ∀ n, (isPWO_iUnion_lt hB n).orderType < (ω^ e).val := by
    intro n
    induction n with
    | zero =>
      have hempty : (⋃ k ∈ Finset.range 0, B k) = (∅ : Set α) := by simp
      rw [Set.IsPWO.orderType_congr _ (Set.isPWO_empty) hempty,
        (Set.isPWO_empty (α := α)).orderType_eq_zero.mpr rfl]
      exact Ordinal.opow_pos _ Ordinal.omega0_pos
    | succ n ih =>
      have hsplit : (⋃ k ∈ Finset.range (n + 1), B k) = (⋃ k ∈ Finset.range n, B k) ∪ B n := by
        ext x
        simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
        constructor
        · rintro ⟨k, hk, hx⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact Or.inl ⟨k, hk, hx⟩
          · exact Or.inr hx
        · rintro (⟨k, hk, hx⟩ | hx)
          · exact ⟨k, by omega, hx⟩
          · exact ⟨n, by omega, hx⟩
      rw [Set.IsPWO.orderType_congr _ ((isPWO_iUnion_lt hB n).union (hB n)) hsplit]
      refine ((isPWO_iUnion_lt hB n).orderType_union_le_naturalAdd (hB n)).trans_lt ?_
      have h1 : NatOrdinal.of (isPWO_iUnion_lt hB n).orderType < ω^ e := by
        rw [← NatOrdinal.of_val (ω^ e)]
        exact NatOrdinal.of.lt_iff_lt.mpr ih
      have h2 : NatOrdinal.of (hB n).orderType < ω^ e := by
        rw [← NatOrdinal.of_val (ω^ e)]
        exact NatOrdinal.of.lt_iff_lt.mpr (hρ n)
      exact NatOrdinal.val.lt_iff_lt.mpr (NatOrdinal.add_lt_wpow h1 h2)
  refine hU.orderType_le_of_forall_inter_Iic_lt fun x hx ↦ ?_
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  have hsub : (⋃ j, B j) ∩ Set.Iic x ⊆ ⋃ j ∈ Finset.range (k + 1), B j := by
    rintro y ⟨hy, hyx⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨?_, hj⟩⟩
    rw [Finset.mem_range]
    by_contra hjk
    rw [not_lt, Nat.succ_le_iff] at hjk
    exact absurd (hord k j hjk x hk y hj) (not_lt.mpr hyx)
  calc (hU.mono (s := (⋃ j, B j) ∩ Set.Iic x) Set.inter_subset_left).orderType
      ≤ (isPWO_iUnion_lt hB (k + 1)).orderType :=
        Set.IsPWO.orderType_mono _ _ hsub
    _ < (ω^ e).val := hfin (k + 1)

end Set.IsPWO
