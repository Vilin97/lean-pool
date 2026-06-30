/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.FunctionSpace

/-!
# Exercise 3.21 (Scott 1981, PRG-19, §3) — when does `[Y, Z]` determine `Y` and
`Z`?

In the proof of Theorem 3.12 it is tacitly assumed that the function-space
neighbourhood `[Y, Z]`
(the set `step Y Z = {f ∣ Y f Z}` of approximable mappings) uniquely determines
its endpoints `Y`, `Z`.
Scott's Exercise 3.21 asks to make this precise.

* **If `Z ≠ Δ₂`** the pair is determined: `[Y, Z] = [Y', Z']` forces `Y = Y'` and
`Z = Z'`
  (`step_eq_of_ne_master`). The hint is to use the *least* element of `[Y, Z]` —
  here the single-step
  map `leastMap [(Y, Z)]` of Proposition 3.9.
* **If `Z = Δ₂`** then `[Y, Δ₂] = |𝒟₁ → 𝒟₂|` is the whole space for *every* `Y`
(`step_master_right`),
  so `Y` is not determined; nevertheless the biconditional of Theorem 3.12 stays
  valid because
  `Δ₁ g Δ₂` always holds.
* **General criterion** (`step_eq_iff`): `[Y, Z] = [Y', Z']` iff either both
outputs are `Δ₂`, or
  `Y = Y'` and `Z = Z'`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-! ### The intersection `interYs` of a single step. -/

/-- For a single step `[Y, Z]` and a *sharp enough* input `X ⊆ Y`, the
intersection is just `Z`. -/
theorem interYs_single_subset_eq {YX : Set α} {Z : Set β} {X : Set α} (hZ : V₁.mem Z)
    (hXY : X ⊆ YX) : interYs V₁.master [(YX, Z)] X = Z := by
  ext z
  rw [mem_interYs]
  constructor
  · rintro ⟨_, hall⟩; exact hall (YX, Z) (List.mem_singleton.mpr rfl) hXY
  · intro hz
    exact ⟨V₁.sub_master hZ hz, fun p hp _ => by rw [List.mem_singleton] at hp; subst hp; exact hz⟩

/-- For a single step `[Y, Z]` and an input `X ⊄ Y`, the intersection is the whole
master `Δ₂`. -/
theorem interYs_single_not_subset_eq {YX : Set α} {Z : Set β} {X : Set α}
    (hXY : ¬ X ⊆ YX) : interYs V₁.master [(YX, Z)] X = V₁.master := by
  ext z
  rw [mem_interYs]
  constructor
  · rintro ⟨hm, _⟩; exact hm
  · intro hz
    exact ⟨hz, fun p hp hXp => by rw [List.mem_singleton] at hp; subst hp; exact absurd hXp hXY⟩

/-! ### The least element of a single step neighbourhood. -/

/-- Consistency (`hcons`) for a single step `[Y, Z]`: the intersection over the
relevant outputs is
either `Z` (sharp input) or `Δ₂` (blunt input), both neighbourhoods. -/
theorem stepCons {Y : Set α} {Z : Set β} (hZ : V₁.mem Z) :
    ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master [(Y, Z)] X) := by
  intro X _
  by_cases hXY : X ⊆ Y
  · rw [interYs_single_subset_eq hZ hXY]; exact hZ
  · rw [interYs_single_not_subset_eq hXY]; exact V₁.master_mem

/-- The single-step least map `f₀ ∈ [Y, Z]`: `leastMap [(Y, Z)]`, the minimal
approximable mapping
relating `Y` to `Z`. -/
def leastStep (Y : Set α) (Z : Set β) (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    ApproximableMap V₀ V₁ :=
  by
    have _hY : V₀.mem Y := hY
    exact leastMap [(Y, Z)] (stepCons hZ)

theorem leastStep_mem {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    leastStep Y Z hY hZ ∈ step Y Z := by
  have := leastMap_mem_stepFun (V₀ := V₀) (V₁ := V₁)
    (L := [(Y, Z)]) (by rintro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hY, hZ⟩)
    (stepCons hZ)
  rw [stepFun_singleton] at this
  exact this

theorem leastStep_le {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {f : ApproximableMap V₀ V₁} (hf : f ∈ step Y Z) : leastStep Y Z hY hZ ≤ f := by
  apply leastMap_le (stepCons hZ)
  rw [stepFun_singleton]; exact hf

/-- `f₀ = leastStep Y Z` relates `Y'` to `Z'` iff (`Y' ⊆ Y` and `Z ⊆ Z'`) or `Z' =
Δ₂`. -/
theorem leastStep_rel {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') :
    (leastStep Y Z hY hZ).rel Y' Z' ↔ interYs V₁.master [(Y, Z)] Y' ⊆ Z' := by
  rw [leastStep, leastMap_rel]
  exact ⟨fun h => h.2.2, fun h => ⟨hY', hZ', h⟩⟩

/-! ### `[Y, Z]` is the whole space exactly when `Z = Δ₂`. -/

/-- **Exercise 3.21.** If the output is the master, `[Y, Δ₂]` is the whole
function space. -/
theorem step_master_right (Y : Set α) (hY : V₀.mem Y) :
    (step Y V₁.master : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f
  simp only [mem_step, Set.mem_univ, iff_true]
  exact f.mono f.master_rel (V₀.sub_master hY) subset_rfl hY V₁.master_mem

theorem step_eq_univ_iff {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    (step Y Z : Set (ApproximableMap V₀ V₁)) = Set.univ ↔ Z = V₁.master := by
  constructor
  · intro h
    -- the empty-list least map relates `Y` only to `Δ₂`; it lies in `[Y, Z] =
    -- univ`
    have hmem : leastMap (V₀ := V₀) (V₁ := V₁) ([] : List (Set α × Set β))
        (fun {X} _ => by rw [interYs_nil]; exact V₁.master_mem) ∈ step Y Z := by
      rw [h]; exact Set.mem_univ _
    rw [mem_step, leastMap_rel] at hmem
    have : V₁.master ⊆ Z := by rw [← interYs_nil V₁.master Y]; exact hmem.2.2
    exact Set.Subset.antisymm (V₁.sub_master hZ) this
  · rintro rfl; exact step_master_right Y hY

/-! ### Uniqueness when `Z ≠ Δ₂`. -/

/-- The least elements of equal step neighbourhoods coincide. -/
theorem leastStep_eq_of_step_eq {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z')
    (h : (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z') :
    leastStep Y Z hY hZ = leastStep Y' Z' hY' hZ' := by
  apply le_antisymm
  · exact leastStep_le hY hZ (h ▸ leastStep_mem hY' hZ')
  · exact leastStep_le hY' hZ' (h.symm ▸ leastStep_mem hY hZ)

/-- **Exercise 3.21 (Scott 1981, PRG-19).** If `Z ≠ Δ₂`, the neighbourhood `[Y,
Z]` determines both
endpoints: `[Y, Z] = [Y', Z']` implies `Y = Y'` and `Z = Z'`. -/
theorem step_eq_of_ne_master {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') (hZne : Z ≠ V₁.master)
    (h : (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z') : Y = Y' ∧ Z = Z' := by
  -- `Z' ≠ Δ₂` too, else `[Y', Z']` is the whole space and so is `[Y, Z]`, forcing
  -- `Z = Δ₂`
  have hZ'ne : Z' ≠ V₁.master := by
    intro hZ'eq
    rw [hZ'eq, step_master_right Y' hY'] at h
    exact hZne ((step_eq_univ_iff hY hZ).mp h)
  have hfeq := leastStep_eq_of_step_eq hY hZ hY' hZ' h
  -- `f₀.rel Y' Z'` and `f₀'.rel Y Z`, both with non-master outputs
  have h1 : (leastStep Y Z hY hZ).rel Y' Z' := by
    rw [hfeq]; exact (leastStep_mem hY' hZ')
  have h2 : (leastStep Y' Z' hY' hZ').rel Y Z := by
    rw [← hfeq]; exact (leastStep_mem hY hZ)
  rw [leastStep_rel hY hZ hY' hZ'] at h1
  rw [leastStep_rel hY' hZ' hY hZ] at h2
  -- from `h1`: `Y' ⊆ Y` and `Z ⊆ Z'`
  have hY'Y : Y' ⊆ Y := by
    by_contra hns
    rw [interYs_single_not_subset_eq hns] at h1
    exact hZ'ne (Set.Subset.antisymm (V₁.sub_master hZ') h1)
  have hZZ' : Z ⊆ Z' := by
    rw [interYs_single_subset_eq hZ hY'Y] at h1; exact h1
  -- from `h2`: `Y ⊆ Y'` and `Z' ⊆ Z`
  have hYY' : Y ⊆ Y' := by
    by_contra hns
    rw [interYs_single_not_subset_eq hns] at h2
    exact hZne (Set.Subset.antisymm (V₁.sub_master hZ) h2)
  have hZ'Z : Z' ⊆ Z := by
    rw [interYs_single_subset_eq hZ' hYY'] at h2; exact h2
  exact ⟨Set.Subset.antisymm hYY' hY'Y, Set.Subset.antisymm hZZ' hZ'Z⟩

/-! ### The general identity criterion. -/

/-- **Exercise 3.21 (Scott 1981, PRG-19).** The simple criterion for identity of
function-space
neighbourhoods: `[Y, Z] = [Y', Z']` iff both outputs are the master `Δ₂`, or the
pairs coincide. -/
theorem step_eq_iff {Y : Set α} {Z : Set β} (hY : V₀.mem Y) (hZ : V₁.mem Z)
    {Y' : Set α} {Z' : Set β} (hY' : V₀.mem Y') (hZ' : V₁.mem Z') :
    (step Y Z : Set (ApproximableMap V₀ V₁)) = step Y' Z' ↔
      (Z = V₁.master ∧ Z' = V₁.master) ∨ (Y = Y' ∧ Z = Z') := by
  constructor
  · intro h
    by_cases hZeq : Z = V₁.master
    · refine Or.inl ⟨hZeq, ?_⟩
      rw [hZeq, step_master_right Y hY] at h
      exact (step_eq_univ_iff hY' hZ').mp h.symm
    · exact Or.inr (step_eq_of_ne_master hY hZ hY' hZ' hZeq h)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [step_master_right Y hY, step_master_right Y' hY']
    · rfl

end Domain.Neighborhood
