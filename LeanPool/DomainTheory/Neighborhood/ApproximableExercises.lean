/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Approximable
import Mathlib.Data.Set.Image

/-!
# Lecture II (§2) — Exercises 2.8–2.12 and 2.19 (the algebra of approximable
mappings)

Following Dana Scott, PRG-19 (1981), Lecture II. This file collects the
*structural* exercises about
approximable mappings, all built on `Approximable.lean`:

* **Exercise 2.8** — an approximable map is determined by its action on finite
(principal) elements
  (`eq_of_toElementMap_principal`); and **any** monotone function on finite
  elements extends to an
  approximable map (`ofMono`, `toElementMap_ofMono_principal`).
* **Exercise 2.9** — Scott's formula `f(x) = ⋃ {f(↑X) ∣ X ∈ x}`
(`toElementMap_mem_iff_principal`).
* **Exercise 2.10** — the pointwise **meet** of two maps: `h(x) = f(x) ∩ g(x)`
(`interMap`).
* **Exercise 2.11** — `|𝒟|` is closed under **directed unions** (`iSupDirected`,
with
  `mem_iSupDirected`/`le_iSupDirected`/`iSupDirected_le`), and approximable maps
  **preserve** them
  (`toElementMap_iSupDirected`).
* **Exercise 2.12** — a directed family of approximable maps has a **pointwise
union** that is again
  approximable (`iSupMap`, `mem_toElementMap_iSupMap`).
* **Exercise 2.19** — **two-variable** approximable maps `f : 𝒟₀ × 𝒟₁ → 𝒟₂` as
ternary relations
  (`ApproximableMap₂`), with the Proposition 2.2 analogue (`toElementMap₂`,
  `rel₂_iff_mem_principal`).

All constructions are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`);
the two
`eq_of_…`/uniqueness lemmas decide membership by `by_cases` and are therefore
classical, exactly like
`ext_of_toElementMap`. -/

namespace Domain.Neighborhood

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem

/-- **Exercise 2.11 — directed union (indexed form).** For a directed family `a :
I → |𝒟|` (any two
`a i, a j` have a common upper bound `a k`), the union `⋃ᵢ a i` is again an
element of `|𝒟|`. Built
on `sSupDirected` over the range. -/
def iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) : V.Element :=
  V.sSupDirected (Set.range a) (Set.range_nonempty a) (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨a k, ⟨k, rfl⟩, hik, hjk⟩)

theorem mem_iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) {Z : Set α} :
    (iSupDirected a hdir).mem Z ↔ ∃ i, (a i).mem Z := by
  constructor
  · rintro ⟨s, ⟨i, rfl⟩, hsZ⟩; exact ⟨i, hsZ⟩
  · rintro ⟨i, hi⟩; exact ⟨a i, ⟨i, rfl⟩, hi⟩

theorem le_iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) (i : I) :
    a i ≤ iSupDirected a hdir :=
  fun _ hZ => (mem_iSupDirected a hdir).mpr ⟨i, hZ⟩

theorem iSupDirected_le {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) {y : V.Element}
    (hy : ∀ i, a i ≤ y) : iSupDirected a hdir ≤ y := by
  intro Z hZ
  obtain ⟨i, hi⟩ := (mem_iSupDirected a hdir).mp hZ
  exact hy i Z hi

end NeighborhoodSystem

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-! ### Exercise 2.8 — determination by, and extension from, finite elements. -/

/-- **Exercise 2.8 (uniqueness).** An approximable mapping is *uniquely determined
by its
elementwise
effect on finite elements*: if `f(↑X) = g(↑X)` for every neighbourhood `X`, then
`f = g`. (Off `𝒟₀`
both relations are empty; on `𝒟₀` use `rel_iff_mem_principal`.) -/
theorem eq_of_toElementMap_principal {f g : ApproximableMap V₀ V₁}
    (h : ∀ (X : Set α) (hX : V₀.mem X),
      f.toElementMap (V₀.principal hX) = g.toElementMap (V₀.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : V₀.mem X
  · rw [f.rel_iff_mem_principal hX, g.rel_iff_mem_principal hX, h X hX]
  · constructor
    · intro hr; exact absurd (f.rel_dom hr) hX
    · intro hr; exact absurd (g.rel_dom hr) hX

/-- **Exercise 2.8 (extension).** *Any* monotone function on finite elements comes
from an
approximable map. Here a "monotone function on finite elements" is a map `m`
sending each
neighbourhood `X` (a finite element `↑X`) to an element `m X hX : |𝒟₁|`, monotone
in the sense
`X' ⊆ X → m X hX ≤ m X' hX'` (i.e. `↑X ⊑ ↑X' ⟹ m(↑X) ⊑ m(↑X')`). The induced
relation is
`X f Y ↔ Y ∈ m(↑X)`. -/
def ofMono (m : (X : Set α) → V₀.mem X → V₁.Element)
    (hmono : ∀ (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X'), X' ⊆ X → m X hX ≤ m X' hX') :
    ApproximableMap V₀ V₁ where
  rel X Y := ∃ hX : V₀.mem X, (m X hX).mem Y
  rel_dom := fun ⟨hX, _⟩ => hX
  rel_cod := fun ⟨hX, hY⟩ => (m _ hX).sub hY
  master_rel := ⟨V₀.master_mem, (m _ V₀.master_mem).master_mem⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    exact ⟨hX, (m X hX).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    have hle : m X hX ≤ m X' hX' := hmono X X' hX hX' hX'X
    exact ⟨hX', (m X' hX').up_mem (hle Y hY) hY' hYY'⟩

/-- **Exercise 2.8 (extension, computed).** The map `ofMono m` realizes `m` on
finite elements:
`(ofMono m)(↑X) = m(↑X)`. -/
theorem toElementMap_ofMono_principal
    (m : (X : Set α) → V₀.mem X → V₁.Element)
    (hmono : ∀ (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X'), X' ⊆ X → m X hX ≤ m X' hX')
    (X : Set α) (hX : V₀.mem X) :
    (ofMono m hmono).toElementMap (V₀.principal hX) = m X hX := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨Z, ⟨hZmem, hXZ⟩, hZ', hmY⟩
    have hle : m Z hZ' ≤ m X hX := hmono Z X hZ' hX hXZ
    exact hle Y hmY
  · intro hmY
    exact ⟨X, ⟨hX, subset_rfl⟩, hX, hmY⟩

/-! ### Exercise 2.9 — the elementwise map as a union over finite approximants. -/

/-- **Exercise 2.9 (Scott 1981, PRG-19).** `f(x) = ⋃ {f(↑X) ∣ X ∈ x}`: a
neighbourhood `Y` lies in
`f(x)` iff it lies in `f(↑X)` for some `X ∈ x`. (Immediate from
`rel_iff_mem_principal`.) -/
theorem toElementMap_mem_iff_principal (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β} :
    (f.toElementMap x).mem Y ↔
      ∃ (X : Set α) (hx : x.mem X), (f.toElementMap (V₀.principal (x.sub hx))).mem Y := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, hrel⟩
    exact ⟨X, hxX, (f.rel_iff_mem_principal (x.sub hxX)).mp hrel⟩
  · rintro ⟨X, hxX, hmem⟩
    exact ⟨X, hxX, (f.rel_iff_mem_principal (x.sub hxX)).mpr hmem⟩

/-! ### Exercise 2.10 — the pointwise meet of two approximable maps. -/

/-- **Exercise 2.10 (Scott 1981, PRG-19).** The pointwise **intersection** `h` of
two approximable
maps: `X h Z ↔ X f Z ∧ X g Z`. It is approximable, and
(`mem_toElementMap_interMap`)
`h(x) = f(x) ∩ g(x)`. -/
def interMap (f g : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₁ where
  rel X Z := f.rel X Z ∧ g.rel X Z
  rel_dom h := f.rel_dom h.1
  rel_cod h := f.rel_cod h.1
  master_rel := ⟨f.master_rel, g.master_rel⟩
  inter_right := fun ⟨hf, hg⟩ ⟨hf', hg'⟩ => ⟨f.inter_right hf hf', g.inter_right hg hg'⟩
  mono := fun ⟨hf, hg⟩ hX'X hZZ' hX' hZ' =>
    ⟨f.mono hf hX'X hZZ' hX' hZ', g.mono hg hX'X hZZ' hX' hZ'⟩

/-- **Exercise 2.10.** `h(x) = f(x) ∩ g(x)` (the meet in `|𝒟₁|`). The non-trivial
direction combines
witnesses `X ∈ x` (for `f`) and `X' ∈ x` (for `g`) through `X ∩ X' ∈ x` using
`mono`. -/
theorem mem_toElementMap_interMap (f g : ApproximableMap V₀ V₁) (x : V₀.Element) {Z : Set β} :
    ((interMap f g).toElementMap x).mem Z ↔
      (f.toElementMap x).mem Z ∧ (g.toElementMap x).mem Z := by
  constructor
  · rintro ⟨X, hxX, hf, hg⟩
    exact ⟨⟨X, hxX, hf⟩, ⟨X, hxX, hg⟩⟩
  · rintro ⟨⟨X, hxX, hf⟩, ⟨X', hxX', hg⟩⟩
    have hxXX' : x.mem (X ∩ X') := x.inter_mem hxX hxX'
    have hXX' : V₀.mem (X ∩ X') := x.sub hxXX'
    refine ⟨X ∩ X', hxXX', ?_, ?_⟩
    · exact f.mono hf Set.inter_subset_left subset_rfl hXX' (f.rel_cod hf)
    · exact g.mono hg Set.inter_subset_right subset_rfl hXX' (g.rel_cod hg)

/-! ### Exercise 2.11 — approximable maps preserve directed unions. -/

/-- **Exercise 2.11 (Scott 1981, PRG-19).** Approximable mappings *preserve
directed unions*:
`f(⋃ᵢ a i) = ⋃ᵢ f(a i)`. Both sides have member `Y` iff `∃ i X, X ∈ a i ∧ X f Y`. -/
theorem toElementMap_iSupDirected (f : ApproximableMap V₀ V₁) {I : Type*} [Nonempty I]
    (a : I → V₀.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) :
    f.toElementMap (NeighborhoodSystem.iSupDirected a hdir) =
      NeighborhoodSystem.iSupDirected (fun i => f.toElementMap (a i))
        (fun i j => by
          obtain ⟨k, hik, hjk⟩ := hdir i j
          exact ⟨k, f.toElementMap_mono hik, f.toElementMap_mono hjk⟩) := by
  apply Element.ext
  intro Y
  rw [mem_toElementMap, NeighborhoodSystem.mem_iSupDirected]
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨i, hi⟩ := (NeighborhoodSystem.mem_iSupDirected a hdir).mp hX
    exact ⟨i, X, hi, hrel⟩
  · rintro ⟨i, X, hi, hrel⟩
    exact ⟨X, (NeighborhoodSystem.mem_iSupDirected a hdir).mpr ⟨i, hi⟩, hrel⟩

/-! ### Exercise 2.12 — the pointwise union of a directed family of maps. -/

/-- **Exercise 2.12 (Scott 1981, PRG-19).** The pointwise union of a *directed*
family of
approximable
maps is approximable. Directedness is stated on the relations: any two `f i, f j`
are dominated by
some `f k`. The union relation is `X g Z ↔ ∃ i, X (f i) Z`. -/
def iSupMap {I : Type*} [Nonempty I] (f : I → ApproximableMap V₀ V₁)
    (hdir : ∀ i j, ∃ k, (∀ X Y, (f i).rel X Y → (f k).rel X Y) ∧
      (∀ X Y, (f j).rel X Y → (f k).rel X Y)) : ApproximableMap V₀ V₁ where
  rel X Z := ∃ i, (f i).rel X Z
  rel_dom := fun ⟨i, h⟩ => (f i).rel_dom h
  rel_cod := fun ⟨i, h⟩ => (f i).rel_cod h
  master_rel := by obtain ⟨i⟩ := (inferInstance : Nonempty I); exact ⟨i, (f i).master_rel⟩
  inter_right := by
    rintro X Z Z' ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, (f k).inter_right (hik X Z hi) (hjk X Z' hj)⟩
  mono := by
    rintro X X' Z Z' ⟨i, hi⟩ hX'X hZZ' hX' hZ'
    exact ⟨i, (f i).mono hi hX'X hZZ' hX' hZ'⟩

/-- **Exercise 2.12.** The induced elementwise map is the pointwise union: `g(x) =
⋃ᵢ f i (x)`. -/
theorem mem_toElementMap_iSupMap {I : Type*} [Nonempty I] (f : I → ApproximableMap V₀ V₁)
    (hdir : ∀ i j, ∃ k, (∀ X Y, (f i).rel X Y → (f k).rel X Y) ∧
      (∀ X Y, (f j).rel X Y → (f k).rel X Y)) (x : V₀.Element) {Y : Set β} :
    ((iSupMap f hdir).toElementMap x).mem Y ↔ ∃ i, ((f i).toElementMap x).mem Y := by
  constructor
  · rintro ⟨X, hxX, i, hrel⟩
    exact ⟨i, X, hxX, hrel⟩
  · rintro ⟨i, X, hxX, hrel⟩
    exact ⟨X, hxX, i, hrel⟩

end ApproximableMap

/-! ### Exercise 2.19 — approximable mappings of two variables. -/

/-- **Exercise 2.19 (Scott 1981, PRG-19).** An *approximable mapping of two
variables*
`f : 𝒟₀ × 𝒟₁ → 𝒟₂` is a ternary relation `X, Y f Z` confined to `𝒟₀ × 𝒟₁ × 𝒟₂`
with the natural
generalization of Definition 2.1: (i) `Δ₀, Δ₁ f Δ₂`; (ii) intersectivity on the
output; (iii)
monotonicity jointly in both inputs (sharper) and the output (blunter). -/
structure ApproximableMap₂ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) where
  /-- The underlying ternary relation `X, Y f Z`. -/
  rel : Set α → Set β → Set γ → Prop
  rel_dom₀ : ∀ {X Y Z}, rel X Y Z → V₀.mem X
  rel_dom₁ : ∀ {X Y Z}, rel X Y Z → V₁.mem Y
  rel_cod : ∀ {X Y Z}, rel X Y Z → V₂.mem Z
  /-- (i) `Δ₀, Δ₁ f Δ₂`. -/
  master_rel : rel V₀.master V₁.master V₂.master
  /-- (ii) intersectivity on the output. -/
  inter_right : ∀ {X Y Z Z'}, rel X Y Z → rel X Y Z' → rel X Y (Z ∩ Z')
  /-- (iii) joint monotonicity: sharper inputs `X' ⊆ X`, `Y' ⊆ Y`; blunter output
  `Z ⊆ Z'`. -/
  mono : ∀ {X X' Y Y' Z Z'}, rel X Y Z → X' ⊆ X → Y' ⊆ Y → Z ⊆ Z' →
    V₀.mem X' → V₁.mem Y' → V₂.mem Z' → rel X' Y' Z'

namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 2.19 (Proposition 2.2 analogue).** A two-variable approximable
mapping determines an
elementwise function of two arguments: `f(x, y) = {Z ∣ ∃ X ∈ x, ∃ Y ∈ y, X, Y f
Z}`. The filter
laws use all three conditions: `inter_mem` pulls both outputs back to `(X ∩ X', Y
∩ Y')` via `mono`
then `inter_right`. -/
def toElementMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) (x : V₀.Element) (y : V₁.Element) :
  V₂.Element where
  mem Z := ∃ X Y, x.mem X ∧ y.mem Y ∧ f.rel X Y Z
  sub := fun ⟨_, _, _, _, hrel⟩ => f.rel_cod hrel
  master_mem := ⟨V₀.master, V₁.master, x.master_mem, y.master_mem, f.master_rel⟩
  inter_mem := by
    rintro Z Z' ⟨X, Y, hX, hY, hrel⟩ ⟨X', Y', hX', hY', hrel'⟩
    have hXX' : x.mem (X ∩ X') := x.inter_mem hX hX'
    have hYY' : y.mem (Y ∩ Y') := y.inter_mem hY hY'
    have hXX'm : V₀.mem (X ∩ X') := x.sub hXX'
    have hYY'm : V₁.mem (Y ∩ Y') := y.sub hYY'
    refine ⟨X ∩ X', Y ∩ Y', hXX', hYY', ?_⟩
    have h1 : f.rel (X ∩ X') (Y ∩ Y') Z :=
      f.mono hrel Set.inter_subset_left Set.inter_subset_left subset_rfl hXX'm hYY'm
        (f.rel_cod hrel)
    have h2 : f.rel (X ∩ X') (Y ∩ Y') Z' :=
      f.mono hrel' Set.inter_subset_right Set.inter_subset_right subset_rfl hXX'm hYY'm
        (f.rel_cod hrel')
    exact f.inter_right h1 h2
  up_mem := by
    rintro Z Z' ⟨X, Y, hX, hY, hrel⟩ hZ' hZZ'
    exact ⟨X, Y, hX, hY, f.mono hrel subset_rfl subset_rfl hZZ' (x.sub hX) (y.sub hY) hZ'⟩

@[simp] theorem mem_toElementMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) (x : V₀.Element) (y : V₁.Element)
    {Z : Set γ} : (f.toElementMap₂ x y).mem Z ↔ ∃ X Y, x.mem X ∧ y.mem Y ∧ f.rel X Y Z := Iff.rfl

/-- **Exercise 2.19 (recovery of the relation).** `X, Y f Z ↔ Z ∈ f(↑X, ↑Y)`, the
two-variable
analogue of Proposition 2.2(ii). -/
theorem rel₂_iff_mem_principal (f : ApproximableMap₂ V₀ V₁ V₂) {X : Set α} (hX : V₀.mem X)
    {Y : Set β} (hY : V₁.mem Y) {Z : Set γ} :
    f.rel X Y Z ↔ (f.toElementMap₂ (V₀.principal hX) (V₁.principal hY)).mem Z := by
  constructor
  · intro hrel
    exact ⟨X, Y, ⟨hX, subset_rfl⟩, ⟨hY, subset_rfl⟩, hrel⟩
  · rintro ⟨X', Y', ⟨_, hXX'⟩, ⟨_, hYY'⟩, hrel⟩
    exact f.mono hrel hXX' hYY' subset_rfl hX hY (f.rel_cod hrel)

/-- **Exercise 2.19 (monotonicity).** The two-variable elementwise map is monotone
in each argument
jointly: `x ⊑ x'`, `y ⊑ y'` imply `f(x, y) ⊑ f(x', y')`. -/
theorem toElementMap₂_mono (f : ApproximableMap₂ V₀ V₁ V₂) {x x' : V₀.Element} {y y' : V₁.Element}
    (hx : x ≤ x') (hy : y ≤ y') : f.toElementMap₂ x y ≤ f.toElementMap₂ x' y' := by
  rintro Z ⟨X, Y, hX, hY, hrel⟩
  exact ⟨X, Y, hx X hX, hy Y hY, hrel⟩

end ApproximableMap₂

end Domain.Neighborhood
