/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Exercise 1.14 (Scott 1981, PRG-19, §1) — finite non-empty subsets of `ℕ`

Let `Δ = ℕ` and take as neighbourhoods the **finite non-empty** subsets of `ℕ`,
together with `Δ`
itself. This is the infinite analogue of Example 1.5 (where `Δ` was finite).

Deliverables:

* `neighborhoodSystem : NeighborhoodSystem ℕ` — "Show that this is a neighbourhood
system." Unlike
  the tail/binary examples this is *not* nested-or-disjoint (two finite sets may
  overlap partially),
  so condition (ii) is checked by hand: the consistency witness `Z ⊆ X ∩ Y` keeps
  `X ∩ Y` non-empty,
  and `X ∩ Y` is finite as soon as either factor is.
* **Finite elements.** `fin h = ↑X` (the principal filters), Scott's finite
elements.
* **Total elements.** "What are the total elements?" The maximal filters are
exactly the principals
  of *singletons*: `singleton_isTotal` shows `↑{n}` is total (a filter strictly
  above it would have
  to contain a set missing `n`, forcing `∅ ∈ 𝒟`).

Constructive (`[propext, Quot.sound]`).
-/

namespace Domain.Neighborhood.Exercise114

open Domain.Neighborhood NeighborhoodSystem

/-- Membership: `X` is a neighbourhood iff `X = ℕ` (the master `Δ`) or `X` is
finite and
non-empty. -/
def mem (X : Set ℕ) : Prop := X = Set.univ ∨ (X.Finite ∧ X.Nonempty)

theorem empty_not_mem : ¬ mem (∅ : Set ℕ) := by
  rintro (h | ⟨_, h⟩)
  · exact Set.empty_ne_univ h
  · exact Set.not_nonempty_empty h

theorem nonempty_of_mem {X : Set ℕ} (h : mem X) : X.Nonempty := by
  rcases h with rfl | h
  · exact Set.univ_nonempty
  · exact h.2

theorem mem_singleton (n : ℕ) : mem {n} :=
  Or.inr ⟨Set.finite_singleton n, Set.singleton_nonempty n⟩

/-- **Exercise 1.14.** The neighbourhood system of finite non-empty subsets of `ℕ`
(plus `Δ =
ℕ`). -/
def neighborhoodSystem : NeighborhoodSystem ℕ where
  mem := mem
  master := Set.univ
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    have hne : (X ∩ Y).Nonempty := (nonempty_of_mem hZ).mono hZsub
    rcases hX with hX | hX
    · rw [hX, Set.univ_inter]; exact hY
    · rcases hY with hY | hY
      · rw [hY, Set.inter_univ]; exact Or.inr hX
      · exact Or.inr ⟨hX.1.inter_of_left Y, hne⟩
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem ns_mem {X : Set ℕ} : neighborhoodSystem.mem X ↔ mem X := Iff.rfl

/-! ### Finite elements (principals) and total elements (singletons). -/

/-- The finite element `↑X` for a neighbourhood `X` (Scott's finite elements). -/
def fin {X : Set ℕ} (h : neighborhoodSystem.mem X) : neighborhoodSystem.Element :=
  neighborhoodSystem.principal h

/-- `⊥ = ↑Δ = ↑ℕ`, the least element. -/
def bot : neighborhoodSystem.Element := neighborhoodSystem.bot

/-- **Exercise 1.14 (total elements).** The principal filter of a *singleton*
`{n}` is a total
(maximal) element: any `y` it approximates approximates it back. (A `y ⊋ ↑{n}`
would contain some
`W ∌ n`; then `{n} ∩ W = ∅ ∈ y ⊆ 𝒟`, impossible.) These are exactly the total
elements. -/
theorem singleton_isTotal (n : ℕ) :
    neighborhoodSystem.IsTotal (neighborhoodSystem.principal (mem_singleton n)) := by
  intro y hy W hW
  have hn : y.mem {n} := hy {n} ⟨mem_singleton n, subset_rfl⟩
  refine ⟨y.sub hW, ?_⟩
  by_contra hc
  rw [Set.singleton_subset_iff] at hc
  have hempty : ({n} : Set ℕ) ∩ W = (∅ : Set ℕ) := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, hk⟩
    exact hc hk
  have hi := y.inter_mem hn hW
  rw [hempty] at hi
  exact empty_not_mem (y.sub hi)

end Domain.Neighborhood.Exercise114
