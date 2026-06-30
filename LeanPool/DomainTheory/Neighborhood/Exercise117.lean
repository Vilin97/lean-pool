/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

/-!
# Exercise 1.17 (Scott 1981, PRG-19, §1) — rational open intervals on `ℝ`

`Δ = ℝ`; `𝒟 =` the non-empty open intervals with rational endpoints, plus `Δ`
itself
(`ratIntervalSystem`). The system law (`inter_mem`) reduces to the fact that the
intersection of
two rational intervals is empty or again a rational interval
(`Set.Ioo_inter_Ioo` with `max`/`min` of the rational endpoints): `inter_mem'`.

For each real `t`, `filterAt t = {X ∈ 𝒟 ∣ t ∈ X}` is a filter (`filterAt`). These
embed `ℝ` into
`|𝒟|` injectively (`filterAt_injective`, using rational density), so `|𝒟|`
contains a faithful
copy of the reals.

**Scope.** Scott's full classification of the *total* elements (the hint: for
rational `t`,
intervals with `t` as a right-hand endpoint give a *second* total element at `t`)
needs more
real analysis and is left to prose; we deliver the system, the point-filters, and
their
injectivity. This is the first **uncountable** `Δ` of the block.

The constructions are `[propext, Quot.sound]`; injectivity uses `exists_rat_btwn`
(Archimedean,
classical).
-/

namespace Domain.Neighborhood

namespace RatInterval

open NeighborhoodSystem

/-- A neighbourhood of `ratIntervalSystem`: either `Δ = ℝ`, or a non-empty open
interval with
rational endpoints. -/
def ratIntervalMem (X : Set ℝ) : Prop :=
  X = Set.univ ∨ ∃ a b : ℚ, a < b ∧ X = Set.Ioo (a : ℝ) (b : ℝ)

/-- Every neighbourhood is non-empty (`Δ`, or `Ioo a b` with `a < b`). -/
theorem ratIntervalMem_nonempty {X : Set ℝ} (hX : ratIntervalMem X) : X.Nonempty := by
  rcases hX with rfl | ⟨a, b, hab, rfl⟩
  · exact ⟨0, Set.mem_univ 0⟩
  · rw [Set.nonempty_Ioo]; exact_mod_cast hab

/-- **Exercise 1.17 — intersections.** The intersection of two neighbourhoods that
share a point
is again a neighbourhood: `Ioo a b ∩ Ioo c d = Ioo (max a c) (min b d)`, with
rational endpoints,
non-empty because it contains the shared point. -/
theorem inter_mem' {X Y : Set ℝ} (hX : ratIntervalMem X) (hY : ratIntervalMem Y)
    (hne : (X ∩ Y).Nonempty) : ratIntervalMem (X ∩ Y) := by
  rcases hX with rfl | ⟨a, b, hab, rfl⟩
  · rw [Set.univ_inter]; exact hY
  · rcases hY with rfl | ⟨c, d, hcd, rfl⟩
    · rw [Set.inter_univ]; exact Or.inr ⟨a, b, hab, rfl⟩
    · obtain ⟨z, ⟨hza, hzb⟩, hzc, hzd⟩ := hne
      have had : a < d := by exact_mod_cast hza.trans hzd
      have hcb : c < b := by exact_mod_cast hzc.trans hzb
      have hlt : max a c < min b d := by
        simp only [max_lt_iff, lt_min_iff]
        exact ⟨⟨hab, hcb⟩, had, hcd⟩
      have hset : Set.Ioo (a : ℝ) b ∩ Set.Ioo (c : ℝ) d
          = Set.Ioo ((max a c : ℚ) : ℝ) ((min b d : ℚ) : ℝ) := by
        rw [Set.Ioo_inter_Ioo, Rat.cast_max, Rat.cast_min]
      exact Or.inr ⟨max a c, min b d, hlt, hset⟩

/-- **Exercise 1.17 — the rational-interval neighbourhood system over `ℝ`.** -/
def ratIntervalSystem : NeighborhoodSystem ℝ where
  mem := ratIntervalMem
  master := Set.univ
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    exact inter_mem' hX hY ((ratIntervalMem_nonempty hZ).mono hZsub)
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem ratIntervalSystem_mem {X : Set ℝ} :
    ratIntervalSystem.mem X ↔ ratIntervalMem X := Iff.rfl

/-- **Exercise 1.17 — the point filter `{X ∈ 𝒟 ∣ t ∈ X}`.** For any real `t` this
is a filter:
closure under `∩` uses `inter_mem'` with `t` itself as the shared point. -/
def filterAt (t : ℝ) : ratIntervalSystem.Element where
  mem X := ratIntervalMem X ∧ t ∈ X
  sub h := h.1
  master_mem := ⟨Or.inl rfl, Set.mem_univ t⟩
  inter_mem := by
    rintro X Y ⟨hX, htX⟩ ⟨hY, htY⟩
    exact ⟨inter_mem' hX hY ⟨t, htX, htY⟩, htX, htY⟩
  up_mem := by
    rintro X Y ⟨_, htX⟩ hY hXY
    exact ⟨hY, hXY htX⟩

@[simp] theorem mem_filterAt {t : ℝ} {X : Set ℝ} :
    (filterAt t).mem X ↔ ratIntervalMem X ∧ t ∈ X := Iff.rfl

/-- **Exercise 1.17 — `ℝ ↪ |𝒟|`.** Distinct reals give distinct point filters:
between any two
reals lies a rational interval separating them. -/
theorem filterAt_injective {s t : ℝ} (h : filterAt s = filterAt t) : s = t := by
  by_contra hst
  rcases lt_or_gt_of_ne hst with hlt | hlt
  · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
    obtain ⟨b, hb⟩ := exists_rat_gt t
    have hint : ratIntervalMem (Set.Ioo (a : ℝ) (b : ℝ)) :=
      Or.inr ⟨a, b, by exact_mod_cast ha2.trans hb, rfl⟩
    have htmem : (filterAt t).mem (Set.Ioo (a : ℝ) (b : ℝ)) := ⟨hint, ha2, hb⟩
    rw [← h] at htmem
    exact absurd htmem.2.1 (not_lt.mpr ha1.le)
  · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
    obtain ⟨b, hb⟩ := exists_rat_gt s
    have hint : ratIntervalMem (Set.Ioo (a : ℝ) (b : ℝ)) :=
      Or.inr ⟨a, b, by exact_mod_cast ha2.trans hb, rfl⟩
    have hsmem : (filterAt s).mem (Set.Ioo (a : ℝ) (b : ℝ)) := ⟨hint, ha2, hb⟩
    rw [h] at hsmem
    exact absurd hsmem.2.1 (not_lt.mpr ha1.le)

end RatInterval

end Domain.Neighborhood
