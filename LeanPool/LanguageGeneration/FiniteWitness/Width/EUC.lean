/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Width.Barriers
public import Mathlib.Tactic.Choose

/-!
# Eventually unbounded positive closure and bounded witnesses
-/

public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

/-- Each target contains a finite sample with infinite positive closure. -/
def EventuallyUnboundedClosure (H : Set (Set α)) : Prop :=
  ∀ L ∈ H, ∃ F : Finset α, (↑F : Set α) ⊆ L ∧ (positiveClosure H F).Infinite

theorem positiveClosure_mono_sample {H : Set (Set α)} {F S : Finset α} (hFS : F ⊆ S) :
    positiveClosure H F ⊆ positiveClosure H S :=
  fun _ hx L hL hSL => hx L hL (fun _ hx => hSL (hFS hx))

theorem euc_uus {H : Set (Set α)} (hH : EventuallyUnboundedClosure H) : Generic.UUS H := by
  intro L hL
  obtain ⟨F, hFL, hC⟩ := hH L hL
  exact hC.mono (fun x (hx : x ∈ positiveClosure H F) => hx L hL hFL)

theorem euc_iff_eventual_on_texts [Countable α] (H : Set (Set α)) (hUUS : Generic.UUS H) :
    EventuallyUnboundedClosure H ↔
      ∀ L ∈ H, ∀ stream : Generic.Stream α, Generic.Presents stream L →
        ∃ N, ∀ n ≥ N, (positiveClosure H (Generic.sample stream n)).Infinite := by
  constructor
  · intro h L hL stream hp
    obtain ⟨F, hFL, hC⟩ := h L hL
    obtain ⟨N, hN⟩ := Generic.finset_eventually_subset_sample hp F hFL
    exact ⟨N, fun n hn => hC.mono
      (positiveClosure_mono_sample (hN.trans (Generic.sample_mono hn)))⟩
  · intro h L hL
    obtain ⟨stream, hs⟩ := (Set.to_countable L).exists_eq_range (hUUS L hL).nonempty
    have hp : Generic.Presents stream L := hs.symm
    obtain ⟨N, hN⟩ := h L hL stream hp
    exact ⟨Generic.sample stream N,
      fun _ hx => Generic.mem_language_of_mem_sample_of_presents hp hx, hN N le_rfl⟩

/-- The increasing cover is only a sufficient condition; necessity is not asserted. -/
theorem increasing_euc_cover {H : Set (Set α)} (K : ℕ → Set (Set α))
    (hmono : Monotone K) (hcover : H = ⋃ n, K n)
    (hEUC : ∀ n, EventuallyUnboundedClosure (K n)) : HasFiniteWitnesses H := by
  classical
  have hex : ∀ L : H, ∃ n, ∃ F : Finset α,
      (↑F : Set α) ⊆ L.val ∧ (positiveClosure (K n) F).Infinite ∧ L.val ∈ K n := by
    intro L
    have hL : L.val ∈ ⋃ n, K n := hcover ▸ L.property
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hL
    obtain ⟨F, hFL, hC⟩ := hEUC n L.val hn
    exact ⟨n, F, hFL, hC, hn⟩
  choose idx base hbase hcore hmem using hex
  have hinf (L : H) : L.val.Infinite :=
    (hcore L).mono (fun x (hx : x ∈ positiveClosure (K (idx L)) (base L)) =>
      hx L.val (hmem L) (hbase L))
  choose extra hExtra hcard using (fun L : H => (hinf L).exists_subset_card_eq (idx L))
  let T : Set α → Finset α := fun L => if h : L ∈ H then
    base ⟨L, h⟩ ∪ extra ⟨L, h⟩ else ∅
  have hpos : Positive H T := by
    intro L hL x hx
    change x ∈ (if h : L ∈ H then base ⟨L, h⟩ ∪ extra ⟨L, h⟩ else ∅) at hx
    rw [dite_eq_left hL] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hbase ⟨L, hL⟩ hx
    · exact hExtra ⟨L, hL⟩ hx
  have hbaseT (L : H) : base L ⊆ T L.val := by
    simp only [T, dite_eq_left L.property]
    exact Finset.subset_union_left
  have hidx (L : H) : idx L ≤ (T L.val).card := by
    rw [← hcard L]
    apply Finset.card_le_card
    simp only [T, dite_eq_left L.property]
    exact Finset.subset_union_right
  apply Valid.hasFiniteWitnesses (T := T)
  refine ⟨hpos, ?_⟩
  intro S hS
  let I : Set ℕ := {n | ∃ L : H, L.val ∈ active H T S ∧ idx L = n}
  have hI : I.Finite := by
    apply (Finset.range (S.card + 1)).finite_toSet.subset
    rintro n ⟨L, hL, rfl⟩
    exact Finset.mem_range.mpr (by have := (hidx L).trans (Finset.card_le_card hL.2.1); omega)
  have hIne : I.Nonempty := by
    obtain ⟨L, hL⟩ := hS
    exact ⟨idx ⟨L, hL.1⟩, ⟨L, hL.1⟩, hL, rfl⟩
  obtain ⟨m, ⟨L, hL, hLm⟩, hmax⟩ := Set.exists_max_image I id hI hIne
  have hcl : (positiveClosure (K m) S).Infinite := by
    rw [← hLm]
    exact (hcore L).mono (positiveClosure_mono_sample ((hbaseT L).trans hL.2.1))
  apply hcl.mono
  intro x hx J hJ
  have hj : idx ⟨J, hJ.1⟩ ≤ m := hmax _ ⟨⟨J, hJ.1⟩, hJ, rfl⟩
  exact hx J (hmono hj (hmem ⟨J, hJ.1⟩)) hJ.2.2

theorem increasing_euc_cover_ordinary [Countable α] [Infinite α]
    {H : Set (Set α)} (K : ℕ → Set (Set α)) (hmono : Monotone K)
    (hcover : H = ⋃ n, K n) (hEUC : ∀ n, EventuallyUnboundedClosure (K n)) :
    Generic.GeneratableInLimit H := by
  have hUUS : Generic.UUS H := by
    intro L hL
    rw [hcover] at hL
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hL
    exact euc_uus (hEUC n) L hn
  exact (ordinary_iff_finiteWitnesses H hUUS).mpr (increasing_euc_cover K hmono hcover hEUC)

end GenLimit.FiniteWitness
