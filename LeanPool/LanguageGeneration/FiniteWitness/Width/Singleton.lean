/-
Copyright (c) 2026 Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaoyu Li, Andi Han, Jiaojiao Jiang, Junbin Gao
-/
module

public import LeanPool.LanguageGeneration.FiniteWitness.Width.Foundation
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Push

/-!
# Singleton witnesses for countable language families
-/

public section

namespace GenLimit.FiniteWitness

variable {α : Type*}

theorem exists_injective_choice_avoiding (A : ℕ → Set α)
    (hA : ∀ n, (A n).Infinite) (B : ℕ → Finset α) :
    ∃ p : ℕ → α, Function.Injective p ∧ ∀ n, p n ∈ A n ∧ p n ∉ B n := by
  classical
  have hex : ∀ n (S : Finset α), ∃ x ∈ A n, x ∉ B n ∪ S :=
    fun n S => (hA n).exists_notMem_finset _
  choose pick hp hf using hex
  let used : ℕ → Finset α := Nat.rec ∅ (fun n S => insert (pick n S) S)
  let p : ℕ → α := fun n => pick n (used n)
  have hs (n) : used (n + 1) = insert (p n) (used n) := rfl
  have hm : Monotone used := monotone_nat_of_le_succ (fun n => by
    rw [hs]; exact Finset.subset_insert _ _)
  have hnew (n) : p n ∉ used n := fun h => hf n (used n) (Finset.mem_union_right _ h)
  have hprev {i j} (hij : i < j) : p i ∈ used j :=
    hm hij (by rw [hs]; exact Finset.mem_insert_self _ _)
  refine ⟨p, ?_, fun n => ⟨hp n (used n), fun h => hf n (used n)
    (Finset.mem_union_left _ h)⟩⟩
  intro i j heq
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hnew j (heq ▸ hprev h))
  · exact h
  · exact False.elim (hnew i (heq.symm ▸ hprev h))

/-- The union of the finite intersections of subfamilies of a finite language family. -/
noncomputable def finiteCoreForbidden (V : Finset (Set α)) : Finset α := by
  classical
  exact V.powerset.biUnion (fun F => if h : (⋂₀ (↑F : Set (Set α))).Finite
    then h.toFinset else ∅)

theorem mem_finiteCoreForbidden {V : Finset (Set α)} {F : Set (Set α)}
    (hF : F.Finite) (hFV : F ⊆ ↑V) (hC : (⋂₀ F).Finite) {x : α}
    (hx : x ∈ ⋂₀ F) : x ∈ finiteCoreForbidden V := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨hF.toFinset, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro L hL
    exact hFV (hF.mem_toFinset.mp hL)
  · simp only [Set.Finite.coe_toFinset]
    rw [dite_eq_left hC]
    exact hC.mem_toFinset.mpr hx

theorem countable_singleton_witnesses [Infinite α] {H : Set (Set α)}
    (hH : H.Countable) (hUUS : Generic.UUS H) :
    ∃ p : H → α, Function.Injective p ∧
      ∃ T : Set α → Finset α, Valid H T ∧ ∀ L : H, T L = {p L} := by
  classical
  let : Countable H := hH.to_subtype
  let : Encodable H := Encodable.ofCountable H
  let A : ℕ → Set α := fun n => ((Encodable.decode (α := H) n).map Subtype.val).getD Set.univ
  have hA : ∀ n, (A n).Infinite := by
    intro n
    cases hd : Encodable.decode (α := H) n with
    | none => simpa [A, hd] using (Set.infinite_univ : (Set.univ : Set α).Infinite)
    | some L => simpa [A, hd] using hUUS L.val L.property
  let initialSegment : ℕ → Finset H := fun n =>
    ((List.range (n + 1)).filterMap (Encodable.decode (α := H))).toFinset
  have hprefix {L : H} {n} (h : Encodable.encode L ≤ n) : L ∈ initialSegment n := by
    simp only [initialSegment, List.mem_toFinset, List.mem_filterMap, List.mem_range]
    exact ⟨Encodable.encode L, by omega, by simp⟩
  let V : ℕ → Finset (Set α) := fun n => (initialSegment n).image Subtype.val
  obtain ⟨p, hpinj, hp⟩ := exists_injective_choice_avoiding A hA
    (fun n => finiteCoreForbidden (V n))
  let rank : Set α → ℕ := fun L => if h : L ∈ H then Encodable.encode (⟨L, h⟩ : H) else 0
  have hrank (L : H) : rank L = Encodable.encode L := by simp [rank]
  have hrankinj : H.InjOn rank := by
    intro L hL K hK heq
    have hh : Encodable.encode (⟨L, hL⟩ : H) = Encodable.encode (⟨K, hK⟩ : H) := by
      simpa [rank, hL, hK] using heq
    exact congrArg Subtype.val (Encodable.encode_injective hh)
  let T : Set α → Finset α := fun L => {p (rank L)}
  have hpos : Positive H T := by
    intro L hL x hx
    have heq : x = p (rank L) := Finset.mem_singleton.mp hx
    subst x
    have h := (hp (rank L)).1
    simpa [A, rank, hL] using h
  have hsep : Separates H T := by
    intro F hFH hF hC
    by_contra hn
    push Not at hn
    have hall : ∀ L ∈ F, p (rank L) ∈ ⋂₀ F := by
      intro L hL K hK
      exact hn L hL K hK _ (Finset.mem_singleton_self _)
    have hfinite : F.Finite := by
      have hi : ((fun L => p (rank L)) '' F) ⊆ ⋂₀ F := by
        rintro _ ⟨L, hL, rfl⟩
        exact hall L hL
      exact (hC.subset hi).of_finite_image (fun L hL K hK h =>
        hrankinj (hFH hL) (hFH hK) (hpinj h))
    obtain ⟨L, hL, hmax⟩ := Set.exists_max_image F rank hfinite hF
    have hFV : F ⊆ (↑(V (rank L)) : Set (Set α)) := by
      intro K hK
      apply Finset.mem_image.mpr
      refine ⟨⟨K, hFH hK⟩, hprefix ?_, rfl⟩
      rw [← hrank ⟨K, hFH hK⟩]
      exact hmax K hK
    exact (hp (rank L)).2 (mem_finiteCoreForbidden hfinite hFV hC (hall L hL))
  refine ⟨fun L => p (Encodable.encode L), hpinj.comp Encodable.encode_injective,
    T, (valid_iff_positive_separates H T).mpr ⟨hpos, hsep⟩, ?_⟩
  intro L
  simp [T, hrank]

theorem countable_hasBoundedWitnesses_one [Infinite α] {H : Set (Set α)}
    (hH : H.Countable) (hUUS : Generic.UUS H) : HasBoundedWitnesses H 1 := by
  obtain ⟨p, _, T, hT, hp⟩ := countable_singleton_witnesses hH hUUS
  refine ⟨T, hT, ?_⟩
  intro L hL
  rw [hp ⟨L, hL⟩]
  simp

theorem countable_ordinary [Infinite α] {H : Set (Set α)}
    (hH : H.Countable) (hUUS : Generic.UUS H) : Generic.GeneratableInLimit H := by
  obtain ⟨T, hT, _⟩ := countable_hasBoundedWitnesses_one hH hUUS
  exact finiteWitnesses_imply_ordinary hT.hasFiniteWitnesses

end GenLimit.FiniteWitness
