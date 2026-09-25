/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SameCycleQuot

/-!
# Orbit-size multiset identity

The multiset of orbit sizes of a permutation `π : Equiv.Perm (Fin n)` equals
its cycle type plus singleton fixed-point orbits.
-/

namespace RS

open Finset Equiv Equiv.Perm

variable {n : ℕ}

/-! ## Helper lemmas -/

section Helpers

variable (π : Equiv.Perm (Fin n))

/-- The fibre of a fixed-point orbit is a singleton. -/
private lemma orbFibre_of_fixed {i : Fin n} (hi : π i = i) :
    orbFibre π (orbitOf π i) = {i} := by
  classical
  ext j
  simp only [mem_orbFibre, Finset.mem_singleton]
  rw [eq_comm, orbitOf_eq_iff]
  exact ⟨fun h => (h.eq_of_left hi).symm, fun h => h ▸ SameCycle.refl _ _⟩

/-- The fibre of a non-fixed-point orbit equals the `cycleOf` support. -/
private lemma orbFibre_of_nonfixed {i : Fin n} (hi : π i ≠ i) :
    orbFibre π (orbitOf π i) = (π.cycleOf i).support := by
  classical
  ext j
  simp only [mem_orbFibre]
  rw [eq_comm, orbitOf_eq_iff]
  exact (mem_support_cycleOf_iff' hi).symm

/-- An orbit has size 1 iff its representative is a fixed point. -/
private lemma orbCard_orbitOf_eq_one (i : Fin n) :
    orbCard π (orbitOf π i) = 1 ↔ π i = i := by
  classical
  constructor
  · intro h
    by_contra hi
    rw [orbCard, orbFibre_of_nonfixed π hi] at h
    exact absurd h (Nat.ne_of_gt (isCycle_cycleOf π hi).two_le_card_support)
  · intro hi
    rw [orbCard, orbFibre_of_fixed π hi, card_singleton]

/-- A non-fixed-point orbit has size equal to the support of its `cycleOf`. -/
private lemma orbCard_eq_cycleOf_support {i : Fin n} (hi : π i ≠ i) :
    orbCard π (orbitOf π i) = (π.cycleOf i).support.card := by
  classical
  rw [orbCard, orbFibre_of_nonfixed π hi]

/-- Pick a canonical representative from an orbit fibre. -/
private noncomputable def orbRep (O : OrbitSpace π) : Fin n :=
  (orbFibre π O).min' (orbFibre_nonempty π O)

private lemma orbRep_mem (O : OrbitSpace π) : orbitOf π (orbRep π O) = O :=
  (mem_orbFibre π).mp ((orbFibre π O).min'_mem (orbFibre_nonempty π O))

/-- Singleton orbits biject with fixed points of `π`. -/
private lemma card_singleton_orbits :
    ((Finset.univ : Finset (OrbitSpace π)).filter (fun O => orbCard π O =
      1)).card =
      n - π.cycleType.sum := by
  -- n - cycleType.sum = supportᶜ.card
  suffices h : ((Finset.univ : Finset (OrbitSpace π)).filter
      (fun O => orbCard π O = 1)).card = π.supportᶜ.card by
    rwa [Finset.card_compl, Fintype.card_fin, ← sum_cycleType] at h
  symm
  apply Finset.card_bij (fun i _ => orbitOf π i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.mem_compl, mem_support, not_not] at hi
    exact (orbCard_orbitOf_eq_one π i).mpr hi
  · intro i hi j hj hij
    rw [Finset.mem_compl, mem_support, not_not] at hi hj
    exact ((orbitOf_eq_iff π).mp hij).eq_of_left hi
  · intro O hO
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hO
    obtain ⟨i, hi⟩ := orbFibre_nonempty π O
    rw [mem_orbFibre] at hi
    refine ⟨i, ?_, hi⟩
    rw [Finset.mem_compl, mem_support, not_not]
    exact (orbCard_orbitOf_eq_one π i).mp (hi ▸ hO)

/-- Big orbits (size ≥ 2) biject with cycle factors, preserving sizes. -/
private lemma card_big_orbits_count (m : ℕ) (hm : 2 ≤ m) :
    ((Finset.univ : Finset (OrbitSpace π)).filter (fun O => orbCard π O =
      m)).card =
    (π.cycleFactorsFinset.filter (fun c => c.support.card = m)).card := by
  apply Finset.card_bij (fun O _ => π.cycleOf (orbRep π O))
  · -- MapsTo
    intro O hO
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hO
    rw [Finset.mem_filter]
    set r := orbRep π O
    have hr := orbRep_mem π O
    have hr_supp : r ∈ π.support := by
      rw [mem_support]; intro heq
      have := hr ▸ (orbCard_orbitOf_eq_one π r).mpr heq; omega
    refine ⟨cycleOf_mem_cycleFactorsFinset_iff.mpr hr_supp, ?_⟩
    rw [← orbCard_eq_cycleOf_support π (mem_support.mp hr_supp), hr, hO]
  · -- Injective
    intro O₁ hO₁ O₂ hO₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hO₁ hO₂
    set r₁ := orbRep π O₁
    set r₂ := orbRep π O₂
    have hr₁ := orbRep_mem π O₁
    have hr₂ := orbRep_mem π O₂
    have hs₁ : r₁ ∈ π.support := by
      rw [mem_support]
      intro h
      have := hr₁ ▸ (orbCard_orbitOf_eq_one π r₁).mpr h
      omega
    have hmem : r₁ ∈ (π.cycleOf r₂).support := by
      rw [← heq, mem_support_cycleOf_iff' (mem_support.mp hs₁)]
    rw [mem_support_cycleOf_iff] at hmem
    rw [← hr₁, ← hr₂, (orbitOf_eq_iff π).mpr hmem.1.symm]
  · -- Surjective
    intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hc_mem, hc_card⟩ := hc
    obtain ⟨a, ha⟩ := (mem_cycleFactorsFinset_iff.mp hc_mem).1.nonempty_support
    have ha_supp : a ∈ π.support := mem_cycleFactorsFinset_support_le hc_mem ha
    have hO_mem : orbitOf π a ∈ (Finset.univ : Finset (OrbitSpace π)).filter
        (fun O => orbCard π O = m) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [orbCard_eq_cycleOf_support π (mem_support.mp ha_supp),
          ← cycle_is_cycleOf ha hc_mem, hc_card]
    refine ⟨orbitOf π a, hO_mem, ?_⟩
    set r := orbRep π (orbitOf π a)
    have hr := orbRep_mem π (orbitOf π a)
    have hsc : π.SameCycle r a := (orbitOf_eq_iff π).mp hr
    rw [hsc.cycleOf_eq, (cycle_is_cycleOf ha hc_mem).symm]

end Helpers

/-! ## Main theorem -/

-- Raised budget: the orbit cardinality is computed by rewriting a
-- `Finset` sum into a `Multiset` count, which unfolds both sides
-- of the correspondence.
/-- The orbit sizes are the cycle type together with a singleton per
fixed point. -/
theorem orbCard_multiset (π : Equiv.Perm (Fin n)) :
    ((Finset.univ : Finset (OrbitSpace π)).val.map (orbCard π)) =
      π.cycleType + Multiset.replicate (n - π.cycleType.sum) 1 := by
  classical
  ext m
  simp only [Multiset.count_add, Multiset.count_map, Multiset.count_replicate]
  -- Convert Multiset.filter to Finset.filter
  have hconv : (Multiset.filter (fun a => m = orbCard π a)
      (Finset.univ : Finset (OrbitSpace π)).val).card =
      ((Finset.univ : Finset (OrbitSpace π)).filter (fun O => orbCard π O =
        m)).card := by
    congr 1; exact Multiset.filter_congr (fun _ _ => eq_comm)
  rw [hconv]
  by_cases hm0 : m = 0
  · -- m = 0: both sides are 0
    subst hm0
    have h1 : ((Finset.univ : Finset (OrbitSpace π)).filter
        (fun O => orbCard π O = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro O _
      exact Nat.pos_of_ne_zero (fun h => absurd (orbCard_pos π O) (by omega))
        |>.ne'
    rw [h1]
    have h2 : Multiset.count 0 π.cycleType = 0 :=
      Multiset.count_eq_zero.mpr (fun h => absurd (two_le_of_mem_cycleType h)
        (by omega))
    rw [h2, zero_add, ite_eq_right (by omega : ¬(1 : ℕ) = 0)]
  by_cases hm1 : m = 1
  · -- m = 1
    subst hm1
    have ct_no_ones : Multiset.count 1 π.cycleType = 0 :=
      Multiset.count_eq_zero.mpr (fun h => absurd (two_le_of_mem_cycleType h)
        (by omega))
    rw [ct_no_ones, zero_add, ite_eq_left rfl]
    exact card_singleton_orbits π
  · -- m ≥ 2
    have hm_ge2 : 2 ≤ m := by omega
    rw [ite_eq_right (fun h : (1 : ℕ) = m => hm1 h.symm), add_zero]
    rw [cycleType_def, Multiset.count_map]
    have hconv2 : (Multiset.filter (fun a => m = (Finset.card ∘
      Equiv.Perm.support) a)
        π.cycleFactorsFinset.val).card =
        (π.cycleFactorsFinset.filter (fun c => c.support.card = m)).card := by
      congr 1; exact Multiset.filter_congr (fun _ _ => by simp [eq_comm])
    rw [hconv2]
    exact card_big_orbits_count π m hm_ge2

end RS
