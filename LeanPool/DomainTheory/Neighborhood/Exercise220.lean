/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.ApproximableExercises
import Mathlib.Data.Set.Finite.Basic

/-!
# Exercise 2.20 (Scott 1981, PRG-19, §2) — the powerset domain `𝒫`

> **EXERCISE 2.20.** Discuss again the example of Exercise 1.15 where the domain
turns out to be the
> powerset of `ℕ`. Show how the finite elements can be taken to be the finite
subsets of `ℕ` and can
> be identified with the tokens of a suitable neighbourhood system `𝒫`. (Hint:
Define `↑F` for finite
> sets `F ⊆ ℕ`.) Show that both `x ∪ y` and `x ∩ y` are approximable functions of
two variables, and
> that `x + 1 = {n + 1 ∣ n ∈ x}` and `x − 1 = {n ∣ n + 1 ∈ x}` are approximable.

> ⚠ **Numbering note.** Our `Exercise115.lean` formalized the *flat*/*stem*
systems, **not** the
> powerset domain; so `𝒫` is built fresh here.

**Token encoding.** We take tokens `Δ = ℕ` and let the neighbourhoods of `𝒫` be
the **cofinite**
subsets of `ℕ`. Since the principal-filter map `X ↦ ↑X` is inclusion-*reversing*,
the finite element
`↑X` represents the finite set `Xᶜ`; as `Xᶜ` grows (more elements known to be *in*
the set), the
neighbourhood `X` shrinks (more information). Concretely a finite subset `F ⊆ ℕ`
is the finite
element `↑(Fᶜ)`, and `⊥ = ↑ℕ` is the empty set.

* `powerSet : NeighborhoodSystem ℕ` — cofinite sets (closed under finite `∩`).
* `toSet x := {n ∣ {n}ᶜ ∈ x}` and `ofSet S` — the identification, packaged as
  **`equivSetNat : |𝒫| ≃o (Set ℕ, ⊆)`** (`toSet`/`ofSet` mutually inverse,
  order-iso).
* `unionMap`, `interMap₂ : ApproximableMap₂ 𝒫 𝒫 𝒫` — `x ∪ y`, `x ∩ y` (Exercise
2.19), with
  `toSet_unionMap`/`toSet_interMap₂` proving the elementwise action is `∪`/`∩` on
  `Set ℕ`.
* `succMap`, `predMap : ApproximableMap 𝒫 𝒫` — `x + 1`, `x − 1`, with
`toSet_succMap`/`toSet_predMap`.

Choice-free (`#print axioms ⊆ {propext, Quot.sound}`); the
`Set.Finite.induction_on` in
`mem_compl_of_finite` is structural recursion on a finiteness proof, not
`Classical.choice`. -/

namespace Domain.Neighborhood.Exercise220

open Domain.Neighborhood NeighborhoodSystem

/-! ### The neighbourhood system `𝒫` (cofinite sets). -/

/-- **Exercise 2.20 — the powerset system `𝒫`.** Tokens `ℕ`; the neighbourhoods
are the cofinite
sets, closed under finite intersection (`(X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ`). -/
def powerSet : NeighborhoodSystem ℕ where
  mem X := Xᶜ.Finite
  master := Set.univ
  master_mem := by rw [Set.compl_univ]; exact Set.finite_empty
  inter_mem := by
    intro X Y _ hX hY _ _
    rw [Set.compl_inter]; exact hX.union hY
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem mem_powerSet {X : Set ℕ} : powerSet.mem X ↔ Xᶜ.Finite := Iff.rfl
@[simp] theorem powerSet_master : powerSet.master = (Set.univ : Set ℕ) := rfl

/-- Cofinite sets are closed under intersection (witness-free form). -/
theorem powerSet_inter_mem {A B : Set ℕ} (hA : powerSet.mem A) (hB : powerSet.mem B) :
    powerSet.mem (A ∩ B) := by
  rw [mem_powerSet, Set.compl_inter]; exact hA.union hB

/-- The complement of a singleton is a neighbourhood (it represents the finite
element `{n}`). -/
theorem mem_compl_singleton (n : ℕ) : powerSet.mem ({n}ᶜ) := by
  rw [mem_powerSet, compl_compl]; exact Set.finite_singleton n

/-! ### The identification `|𝒫| ≃o Set ℕ`. -/

/-- The subset of `ℕ` represented by an element: `n ∈ toSet x ↔ {n}ᶜ ∈ x`. -/
def toSet (x : powerSet.Element) : Set ℕ := {n | x.mem ({n}ᶜ)}

@[simp] theorem mem_toSet {x : powerSet.Element} {n : ℕ} : n ∈ toSet x ↔ x.mem ({n}ᶜ) := Iff.rfl

/-- The filter of a subset `S ⊆ ℕ`: the cofinite `Z` with `Zᶜ ⊆ S`. -/
def ofSet (S : Set ℕ) : powerSet.Element where
  mem Z := powerSet.mem Z ∧ Zᶜ ⊆ S
  sub h := h.1
  master_mem := ⟨powerSet.master_mem, by
    rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset S⟩
  inter_mem := by
    rintro Z W ⟨hZ, hZS⟩ ⟨hW, hWS⟩
    refine ⟨powerSet_inter_mem hZ hW, ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hZS hWS
  up_mem := by
    rintro Z W ⟨hZ, hZS⟩ hW hZW
    exact ⟨hW, (Set.compl_subset_compl.mpr hZW).trans hZS⟩

/-- **Filters are determined on cofinite sets by their singleton-complements.**
For cofinite `Z`,
`Z ∈ x ↔ ∀ n ∈ Zᶜ, {n}ᶜ ∈ x` (since `Z = ⋂_{n ∈ Zᶜ} {n}ᶜ`, a *finite*
intersection). -/
theorem mem_compl_of_finite (x : powerSet.Element) {t : Set ℕ} (ht : t.Finite)
    (h : ∀ n ∈ t, x.mem ({n}ᶜ)) : x.mem (tᶜ) := by
  revert h
  induction t, ht using Set.Finite.induction_on with
  | empty => intro _; rw [Set.compl_empty]; exact x.master_mem
  | @insert a s _ha _hsfin ih =>
    intro h
    have hcompl : (insert a s)ᶜ = ({a}ᶜ) ∩ (sᶜ) := by rw [Set.insert_eq, Set.compl_union]
    rw [hcompl]
    exact x.inter_mem (h a (Set.mem_insert a s))
      (ih (fun n hn => h n (Set.mem_insert_of_mem a hn)))

theorem toSet_ofSet (S : Set ℕ) : toSet (ofSet S) = S := by
  ext n
  simp only [mem_toSet]
  constructor
  · rintro ⟨_, hsub⟩
    rw [compl_compl] at hsub
    exact hsub (Set.mem_singleton n)
  · intro hn
    exact ⟨mem_compl_singleton n, by rw [compl_compl]; exact Set.singleton_subset_iff.mpr hn⟩

theorem ofSet_toSet (x : powerSet.Element) : ofSet (toSet x) = x := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨hZ, hZsub⟩
    have hmem := mem_compl_of_finite x hZ (fun n hn => hZsub hn)
    rwa [compl_compl] at hmem
  · intro hZ
    refine ⟨x.sub hZ, ?_⟩
    intro n hn
    rw [mem_toSet]
    exact x.up_mem hZ (mem_compl_singleton n) (Set.subset_compl_singleton_iff.mpr hn)

/-- `ofSet` is monotone in the set. -/
theorem ofSet_mono {S S' : Set ℕ} (h : S ⊆ S') : ofSet S ≤ ofSet S' :=
  fun _ hZ => ⟨hZ.1, hZ.2.trans h⟩

/-- **Exercise 2.20 — the identification `|𝒫| ≅ (Set ℕ, ⊆)`.** -/
def equivSetNat : powerSet.Element ≃o Set ℕ where
  toFun := toSet
  invFun := ofSet
  left_inv := ofSet_toSet
  right_inv := toSet_ofSet
  map_rel_iff' := by
    intro x y
    change toSet x ≤ toSet y ↔ x ≤ y
    constructor
    · intro h
      have hmono := ofSet_mono h
      rwa [ofSet_toSet, ofSet_toSet] at hmono
    · intro h n hn
      exact h _ hn

/-! ### The shift maps `x + 1` and `x − 1`. -/

/-- `S + 1 = {n + 1 ∣ n ∈ S}`. -/
def succSet (S : Set ℕ) : Set ℕ := (· + 1) '' S
/-- `S − 1 = {n ∣ n + 1 ∈ S}`. -/
def predSet (S : Set ℕ) : Set ℕ := {n | n + 1 ∈ S}

@[simp] theorem mem_predSet {S : Set ℕ} {n : ℕ} : n ∈ predSet S ↔ n + 1 ∈ S := Iff.rfl

theorem succSet_mono {S T : Set ℕ} (h : S ⊆ T) : succSet S ⊆ succSet T := Set.image_mono h
theorem predSet_mono {S T : Set ℕ} (h : S ⊆ T) : predSet S ⊆ predSet T := fun _ hn => h hn

/-- **Exercise 2.20 — `x + 1` is approximable.** `X f Z ↔ Zᶜ ⊆ (Xᶜ + 1)`. -/
def succMap : ApproximableMap powerSet powerSet where
  rel X Z := powerSet.mem X ∧ powerSet.mem Z ∧ Zᶜ ⊆ succSet Xᶜ
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨powerSet.master_mem, powerSet.master_mem, ?_⟩
    rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset _
  inter_right := by
    rintro X Z Z' ⟨hX, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    refine ⟨hX, powerSet_inter_mem hZ hZ', ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hsub hsub'
  mono := by
    rintro X X' Z Z' ⟨_, _, hsub⟩ hX'X hZZ' hX' hZ'
    refine ⟨hX', hZ', ?_⟩
    exact (Set.compl_subset_compl.mpr hZZ').trans
      (hsub.trans (succSet_mono (Set.compl_subset_compl.mpr hX'X)))

/-- **Exercise 2.20 — `x − 1` is approximable.** `X f Z ↔ Zᶜ ⊆ (Xᶜ − 1)`. -/
def predMap : ApproximableMap powerSet powerSet where
  rel X Z := powerSet.mem X ∧ powerSet.mem Z ∧ Zᶜ ⊆ predSet Xᶜ
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨powerSet.master_mem, powerSet.master_mem, ?_⟩
    rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset _
  inter_right := by
    rintro X Z Z' ⟨hX, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    refine ⟨hX, powerSet_inter_mem hZ hZ', ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hsub hsub'
  mono := by
    rintro X X' Z Z' ⟨_, _, hsub⟩ hX'X hZZ' hX' hZ'
    refine ⟨hX', hZ', ?_⟩
    exact (Set.compl_subset_compl.mpr hZZ').trans
      (hsub.trans (predSet_mono (Set.compl_subset_compl.mpr hX'X)))

theorem toSet_succMap (x : powerSet.Element) :
    toSet (succMap.toElementMap x) = succSet (toSet x) := by
  ext k
  simp only [mem_toSet, ApproximableMap.mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, _, _, hsub⟩
    rw [compl_compl] at hsub
    obtain ⟨m, hm, rfl⟩ := hsub (Set.mem_singleton k)
    exact ⟨m, x.up_mem hxX (mem_compl_singleton m) (Set.subset_compl_singleton_iff.mpr hm), rfl⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨{m}ᶜ, hm, mem_compl_singleton m, mem_compl_singleton (m + 1), ?_⟩
    rw [compl_compl]
    intro a ha
    rw [Set.mem_singleton_iff] at ha; subst ha
    exact ⟨m, by rw [compl_compl]; exact Set.mem_singleton m, rfl⟩

theorem toSet_predMap (x : powerSet.Element) :
    toSet (predMap.toElementMap x) = predSet (toSet x) := by
  ext k
  simp only [mem_toSet, ApproximableMap.mem_toElementMap, mem_predSet]
  constructor
  · rintro ⟨X, hxX, _, _, hsub⟩
    rw [compl_compl] at hsub
    have hk : k + 1 ∈ Xᶜ := hsub (Set.mem_singleton k)
    exact x.up_mem hxX (mem_compl_singleton (k + 1)) (Set.subset_compl_singleton_iff.mpr hk)
  · intro hk
    refine ⟨{k + 1}ᶜ, hk, mem_compl_singleton (k + 1), mem_compl_singleton k, ?_⟩
    rw [compl_compl]
    intro a ha
    rw [Set.mem_singleton_iff] at ha; subst ha
    rw [mem_predSet, compl_compl]
    exact Set.mem_singleton (a + 1)

/-! ### Union and intersection as two-variable approximable maps. -/

/-- **Exercise 2.20 — `x ∪ y` is approximable (two variables).** `X, Y f Z ↔ X ∩ Y
⊆ Z`
(`(Xᶜ ∪ Yᶜ)ᶜ = X ∩ Y`). -/
def unionMap : ApproximableMap₂ powerSet powerSet powerSet where
  rel X Y Z := powerSet.mem X ∧ powerSet.mem Y ∧ powerSet.mem Z ∧ X ∩ Y ⊆ Z
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨powerSet.master_mem, powerSet.master_mem, powerSet.master_mem,
    Set.inter_subset_left⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hsub⟩ ⟨_, _, hZ', hsub'⟩
    exact ⟨hX, hY, powerSet_inter_mem hZ hZ', Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨_, _, _, hsub⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    exact ⟨hX', hY', hZ', (Set.inter_subset_inter hX'X hY'Y).trans (hsub.trans hZZ')⟩

/-- **Exercise 2.20 — `x ∩ y` is approximable (two variables).** `X, Y f Z ↔ X ∪ Y
⊆ Z`
(`(Xᶜ ∩ Yᶜ)ᶜ = X ∪ Y`). -/
def interMap₂ : ApproximableMap₂ powerSet powerSet powerSet where
  rel X Y Z := powerSet.mem X ∧ powerSet.mem Y ∧ powerSet.mem Z ∧ X ∪ Y ⊆ Z
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨powerSet.master_mem, powerSet.master_mem, powerSet.master_mem,
    Set.union_subset (Set.subset_univ _) (Set.subset_univ _)⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hsub⟩ ⟨_, _, hZ', hsub'⟩
    exact ⟨hX, hY, powerSet_inter_mem hZ hZ', Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨_, _, _, hsub⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    exact ⟨hX', hY', hZ', (Set.union_subset_union hX'X hY'Y).trans (hsub.trans hZZ')⟩

theorem toSet_unionMap (x y : powerSet.Element) :
    toSet (unionMap.toElementMap₂ x y) = toSet x ∪ toSet y := by
  ext k
  simp only [mem_toSet, ApproximableMap₂.mem_toElementMap₂, Set.mem_union]
  constructor
  · rintro ⟨X, Y, hxX, hyY, _, _, _, hsub⟩
    by_cases hkX : k ∈ X
    · refine Or.inr ?_
      have hkY : k ∉ Y := fun hkY => (hsub ⟨hkX, hkY⟩) rfl
      exact y.up_mem hyY (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkY)
    · exact Or.inl (x.up_mem hxX (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkX))
  · rintro (hkx | hky)
    · exact ⟨{k}ᶜ, Set.univ, hkx, y.master_mem, mem_compl_singleton k, powerSet.master_mem,
        mem_compl_singleton k, Set.inter_subset_left⟩
    · exact ⟨Set.univ, {k}ᶜ, x.master_mem, hky, powerSet.master_mem, mem_compl_singleton k,
        mem_compl_singleton k, Set.inter_subset_right⟩

theorem toSet_interMap₂ (x y : powerSet.Element) :
    toSet (interMap₂.toElementMap₂ x y) = toSet x ∩ toSet y := by
  ext k
  simp only [mem_toSet, ApproximableMap₂.mem_toElementMap₂, Set.mem_inter_iff]
  constructor
  · rintro ⟨X, Y, hxX, hyY, _, _, _, hsub⟩
    have hkX : k ∉ X := fun h => (hsub (Or.inl h)) rfl
    have hkY : k ∉ Y := fun h => (hsub (Or.inr h)) rfl
    exact ⟨x.up_mem hxX (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkX),
      y.up_mem hyY (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkY)⟩
  · rintro ⟨hkx, hky⟩
    exact ⟨{k}ᶜ, {k}ᶜ, hkx, hky, mem_compl_singleton k, mem_compl_singleton k,
      mem_compl_singleton k, Set.union_subset subset_rfl subset_rfl⟩

end Domain.Neighborhood.Exercise220
