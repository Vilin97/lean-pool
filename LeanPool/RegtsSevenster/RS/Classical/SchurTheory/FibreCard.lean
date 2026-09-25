/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PowerSurj

/-!
# Fibres of a colouring

Shared definitions for the cycle sums: the fibre counts of
a function `Fin n → Fin N` and its content multiset.
-/

@[expose] public section

namespace RS

open Finset

variable {n N : ℕ}

/-- The size of the fibre of a colouring over a colour. -/
noncomputable def fibreCard (f : Fin n → Fin N) (j : Fin N) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => f i = j)).card

/-- The content of a colouring: the multiset of its values. -/
def content (f : Fin n → Fin N) : Sym (Fin N) n :=
  ⟨Finset.univ.val.map f, by
    rw [Multiset.card_map]
    simp⟩

/-- Counts over all colours total the size of a multiset. -/
theorem sum_count_univ (m : Multiset (Fin N)) :
    ∑ j : Fin N, m.count j = Multiset.card m := by
  classical
  rw [← Multiset.toFinset_sum_count_eq m]
  exact (Finset.sum_subset (Finset.subset_univ _)
    (fun a _ ha => Multiset.count_eq_zero.mpr
      (fun hmem => ha (Multiset.mem_toFinset.mpr hmem)))).symm

/-- A fibre's size is the colour's multiplicity in the content. -/
theorem fibreCard_eq_count (f : Fin n → Fin N) (j : Fin N) :
    fibreCard f j = (content f).1.count j := by
  classical
  rw [fibreCard, content, Multiset.count_map]
  rw [Multiset.filter_congr
    (fun x _ => (eq_comm : j = f x ↔ f x = j))]
  rfl

/-- The fibres partition the domain. -/
theorem sum_fibreCard (f : Fin n → Fin N) :
    ∑ j : Fin N, fibreCard f j = n := by
  classical
  rw [Finset.sum_congr rfl (fun j _ => fibreCard_eq_count f j),
    sum_count_univ]
  exact (content f).2

end RS
