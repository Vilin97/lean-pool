/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Definition610
import LeanPool.DomainTheory.Neighborhood.FunctionSpace

/-!
# Lecture VI — Lemma 6.15 (Scott 1981, PRG-19): the converse of Proposition 6.12

Proposition 6.12 says a subdomain relation `D ◁ E` yields a *projection pair* `i :
D → E`,
`j : E → D` with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`. **Lemma 6.15** is the converse:
*any* projection
pair — between two neighbourhood systems `D` and `E` over possibly **different**
token types —
exhibits `D` as (isomorphic to) a subdomain of `E`. Scott writes `D ⊴ E` as short
for "`D ≅ D'`
for some `D' ◁ E`."

**Lemma 6.15.** If there exist approximable maps `i : D → E` and `j : E → D` with
`j ∘ i = I_D`
and `i ∘ j ⊆ I_E`, then `D ⊴ E`.

## The construction (cleaner than Scott's, fully relational)

Scott's proof works with the ideal elements (filters) and shows that `i` carries
finite (principal)
elements to finite elements. We avoid the filter-by-filter argument by isolating
one relational
predicate:

`IsGen i j X Y := X i Y ∧ Y j X`   ("`Y` generates `i(↑X)`").

Everything follows from three relational facts:

* **`isGen_exists`** (uses `j ∘ i = I_D`): every `X ∈ D` has a generator `Y`
(apply `j∘i = I` to the
  identity relation `X I_D X`).
* **`isGen_mono`** (uses `j ∘ i = I_D`) and **`isGen_mono'`** (uses `i ∘ j ⊆
I_E`): the generator
  correspondence is inclusion-monotone in both directions — `Y ⊆ Y' ↔ X ⊆ X'`.
  Their two-way use
  gives that generators are unique in each argument
  (`isGen_fst_unique`/`isGen_snd_unique`).
* **`isGen_inter`** (just `mono`/`inter_right` of `i, j`): if `Y, Y'` are
generators and `Y ∩ Y' ∈ E`,
  then `Y ∩ Y'` generates `X ∩ X'`.

The image system `Dprime i j` has `Y` as a neighbourhood iff `Y` generates some `X
∈ D`; its master
is `E`'s master. `isGen_inter` makes it a neighbourhood system **and** gives the
crucial
`inter_closed` clause of `◁` (consistency inherited from `E`), so `Dprime i j ◁
E`. The
order-isomorphism `D ≅ Dprime i j` is `x ↦ {Y ∣ ∃ X ∈ x, IsGen i j X Y}` with
inverse
`y ↦ {X ∣ ∃ Y ∈ y, IsGen i j X Y}`, the inverse laws and order-reflection coming
from generator
uniqueness.

Everything is built at the level of Definition 2.1 relations, so the whole
development is
**choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Scott's `⊴` (the prose before Lemma 6.15).** `D ⊴ E` means `D ≅ D'` for some
subdomain
`D' ◁ E`: `D` *embeds as a subdomain* of `E`. -/
def Trianglelefteq (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) : Prop :=
  ∃ D' : NeighborhoodSystem β, D' ◁ E ∧ (D ≅ᴰ D')

@[inherit_doc] infix:50 " ⊴ " => Trianglelefteq

section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)

/-- The generator predicate: `Y` generates `i(↑X)`. Relationally, `X i Y` and `Y j
X`. -/
def IsGen (X : Set α) (Y : Set β) : Prop := i.rel X Y ∧ j.rel Y X

/-- The masters generate each other: `IsGen Δ_D Δ_E` (from `i.master_rel`,
`j.master_rel`). -/
theorem isGen_master : IsGen i j D.master E.master :=
  ⟨i.master_rel, j.master_rel⟩

/-- **Generators exist** (uses `j ∘ i = I_D`). Every `D`-neighbourhood `X` has a
generator: apply
`j ∘ i = I_D` to the identity relation `X I_D X`. -/
theorem isGen_exists (hji : j.comp i = idMap D) {X : Set α} (hX : D.mem X) :
    ∃ Y, IsGen i j X Y := by
  have hrel : (j.comp i).rel X X := by rw [hji]; exact ⟨hX, hX, subset_rfl⟩
  obtain ⟨Y, hiXY, hjYX⟩ := hrel
  exact ⟨Y, hiXY, hjYX⟩

/-- **The generator correspondence is monotone** (uses `j ∘ i = I_D`): if `Y, Y'`
generate `X, X'`
and `Y ⊆ Y'`, then `X ⊆ X'`. (Widen `X i Y` to `X i Y'` by `mono`, compose with
`Y' j X'`, and read
off `X ⊆ X'` from `j ∘ i = I_D`.) -/
theorem isGen_mono (hji : j.comp i = idMap D) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hZW : Z ⊆ W) : X ⊆ X' := by
  obtain ⟨hiXZ, _⟩ := h
  obtain ⟨_, hjWX'⟩ := h'
  have hiXW : i.rel X W :=
    i.mono hiXZ subset_rfl hZW (i.rel_dom hiXZ) (j.rel_dom hjWX')
  have hrel : (j.comp i).rel X X' := ⟨W, hiXW, hjWX'⟩
  rw [hji] at hrel
  exact hrel.2.2

/-- **The generator correspondence is monotone, other direction** (uses `i ∘ j ⊆
I_E`): if `Z, W`
generate `X, X'` and `X ⊆ X'`, then `Z ⊆ W`. (Widen `Z j X` to `Z j X'` by `mono`,
compose with
`X' i W`, and read off `Z ⊆ W` from `i ∘ j ⊆ I_E`.) -/
theorem isGen_mono' (hij : i.comp j ≤ idMap E) {X X' : Set α} {Z W : Set β}
    (h : IsGen i j X Z) (h' : IsGen i j X' W) (hXX' : X ⊆ X') : Z ⊆ W := by
  obtain ⟨_, hjZX⟩ := h
  obtain ⟨hiX'W, _⟩ := h'
  have hjZX' : j.rel Z X' :=
    j.mono hjZX subset_rfl hXX' (j.rel_dom hjZX) (i.rel_dom hiX'W)
  have hrel : (i.comp j).rel Z W := ⟨X', hjZX', hiX'W⟩
  exact (hij Z W hrel).2.2

/-- Generators are unique in the first argument (`isGen_mono` both ways). -/
theorem isGen_fst_unique (hji : j.comp i = idMap D) {X X' : Set α} {Y : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y) : X = X' :=
  Set.Subset.antisymm (isGen_mono i j hji h h' subset_rfl)
    (isGen_mono i j hji h' h subset_rfl)

/-- Generators are unique in the second argument (`isGen_mono'` both ways). -/
theorem isGen_snd_unique (hij : i.comp j ≤ idMap E) {X : Set α} {Y Y' : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X Y') : Y = Y' :=
  Set.Subset.antisymm (isGen_mono' i j hij h h' subset_rfl)
    (isGen_mono' i j hij h' h subset_rfl)

/-- **Generators are closed under intersection.** If `Y, Y'` generate `X, X'` and
`Y ∩ Y' ∈ E`, then
`Y ∩ Y'` generates `X ∩ X'`. Needs only `mono`/`inter_right` of `i` and `j` (the
hypothesis
`E.mem (Y ∩ Y')` is what licenses the `j.mono` steps). -/
theorem isGen_inter {X X' : Set α} {Y Y' : Set β}
    (h : IsGen i j X Y) (h' : IsGen i j X' Y') (hE : E.mem (Y ∩ Y')) :
    IsGen i j (X ∩ X') (Y ∩ Y') := by
  obtain ⟨hiXY, hjYX⟩ := h
  obtain ⟨hiX'Y', hjY'X'⟩ := h'
  have hj1 : j.rel (Y ∩ Y') X :=
    j.mono hjYX Set.inter_subset_left subset_rfl hE (j.rel_cod hjYX)
  have hj2 : j.rel (Y ∩ Y') X' :=
    j.mono hjY'X' Set.inter_subset_right subset_rfl hE (j.rel_cod hjY'X')
  have hjInter : j.rel (Y ∩ Y') (X ∩ X') := j.inter_right hj1 hj2
  have hDXX' : D.mem (X ∩ X') := j.rel_cod hjInter
  have hi1 : i.rel (X ∩ X') Y :=
    i.mono hiXY Set.inter_subset_left subset_rfl hDXX' (i.rel_cod hiXY)
  have hi2 : i.rel (X ∩ X') Y' :=
    i.mono hiX'Y' Set.inter_subset_right subset_rfl hDXX' (i.rel_cod hiX'Y')
  exact ⟨i.inter_right hi1 hi2, hjInter⟩

/-- **The image subdomain `D'`.** A `β`-set `Y` is a neighbourhood iff it
generates some
`D`-neighbourhood; the master is `E`'s master. `isGen_inter` supplies condition
(ii). -/
def Dprime : NeighborhoodSystem β where
  mem Y := ∃ X, IsGen i j X Y
  master := E.master
  master_mem := ⟨D.master, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ Z ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ ⟨_, hgz⟩ hZsub
    have hEY₁ : E.mem Y₁ := i.rel_cod hg₁.1
    have hEY₂ : E.mem Y₂ := i.rel_cod hg₂.1
    have hEZ : E.mem Z := i.rel_cod hgz.1
    have hEinter : E.mem (Y₁ ∩ Y₂) := E.inter_mem hEY₁ hEY₂ hEZ hZsub
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hEinter⟩
  sub_master := by
    rintro Y ⟨X, hg⟩
    exact E.sub_master (i.rel_cod hg.1)

@[simp] theorem mem_Dprime {Y : Set β} : (Dprime i j).mem Y ↔ ∃ X, IsGen i j X Y := Iff.rfl

/-- **`D' ◁ E`.** Same master (`rfl`); `D' ⊆ E` since a generator's `Y` is an
`E`-neighbourhood; and
the consistency clause `inter_closed` is exactly `isGen_inter`. -/
theorem Dprime_subsystem : Dprime i j ◁ E where
  master_eq := rfl
  sub := by rintro Y ⟨X, hg⟩; exact i.rel_cod hg.1
  inter_closed := by
    rintro Y₁ Y₂ ⟨X₁, hg₁⟩ ⟨X₂, hg₂⟩ hE
    exact ⟨X₁ ∩ X₂, isGen_inter i j hg₁ hg₂ hE⟩

/-- **Forward map of the isomorphism `D ≅ D'`.** `x ↦ {Y ∣ ∃ X ∈ x, IsGen i j X
Y}` — the
generators of the members of `x`. (Needs `j ∘ i = I_D` for upward closure, via
`isGen_mono`.) -/
def toEl (hji : j.comp i = idMap D) (x : D.Element) : (Dprime i j).Element where
  mem Y := ∃ X, x.mem X ∧ IsGen i j X Y
  sub := by rintro Y ⟨X, _, hg⟩; exact ⟨X, hg⟩
  master_mem := ⟨D.master, x.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro Y₁ Y₂ ⟨X₁, hX₁x, hg₁⟩ ⟨X₂, hX₂x, hg₂⟩
    have hxInter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁x hX₂x
    have hDInter : D.mem (X₁ ∩ X₂) := x.sub hxInter
    have hi1 : i.rel (X₁ ∩ X₂) Y₁ :=
      i.mono hg₁.1 Set.inter_subset_left subset_rfl hDInter (i.rel_cod hg₁.1)
    have hi2 : i.rel (X₁ ∩ X₂) Y₂ :=
      i.mono hg₂.1 Set.inter_subset_right subset_rfl hDInter (i.rel_cod hg₂.1)
    have hEinter : E.mem (Y₁ ∩ Y₂) := i.rel_cod (i.inter_right hi1 hi2)
    exact ⟨X₁ ∩ X₂, hxInter, isGen_inter i j hg₁ hg₂ hEinter⟩
  up_mem := by
    rintro Y Y' ⟨X, hXx, hg⟩ ⟨X', hg'⟩ hYY'
    have hXX' : X ⊆ X' := isGen_mono i j hji hg hg' hYY'
    exact ⟨X', x.up_mem hXx (i.rel_dom hg'.1) hXX', hg'⟩

/-- **Inverse map of the isomorphism `D ≅ D'`.** `y ↦ {X ∣ ∃ Y ∈ y, IsGen i j X
Y}`. (Needs both
laws: `j ∘ i = I_D` for generator existence and `i ∘ j ⊆ I_E` for `isGen_mono'`.) -/
def ofEl (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E)
    (y : (Dprime i j).Element) : D.Element where
  mem X := ∃ Y, y.mem Y ∧ IsGen i j X Y
  sub := by rintro X ⟨Y, _, hg⟩; exact i.rel_dom hg.1
  master_mem := ⟨E.master, y.master_mem, isGen_master i j⟩
  inter_mem := by
    rintro X₁ X₂ ⟨Y₁, hY₁y, hg₁⟩ ⟨Y₂, hY₂y, hg₂⟩
    have hyInter : y.mem (Y₁ ∩ Y₂) := y.inter_mem hY₁y hY₂y
    have hEInter : E.mem (Y₁ ∩ Y₂) := (Dprime_subsystem i j).sub (y.sub hyInter)
    exact ⟨Y₁ ∩ Y₂, hyInter, isGen_inter i j hg₁ hg₂ hEInter⟩
  up_mem := by
    rintro X X' ⟨Y, hYy, hg⟩ hDX' hXX'
    obtain ⟨Y', hg'⟩ := isGen_exists i j hji hDX'
    have hYY' : Y ⊆ Y' := isGen_mono' i j hij hg hg' hXX'
    exact ⟨Y', y.up_mem hYy ⟨X', hg'⟩ hYY', hg'⟩

/-- **The domain isomorphism `D ≅ D'`** (Scott's "inclusion-preserving one-one
correspondence").
Built from `toEl`/`ofEl`; the inverse laws and order-reflection come from
generator uniqueness. -/
def dprimeEquiv (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E) :
    D.Element ≃o (Dprime i j).Element where
  toFun := toEl i j hji
  invFun := ofEl i j hji hij
  left_inv := by
    intro x
    apply Element.ext
    intro X
    constructor
    · rintro ⟨Y, ⟨X₁, hX₁x, hg₁⟩, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x
    · intro hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      exact ⟨Y, ⟨X, hXx, hg⟩, hg⟩
  right_inv := by
    intro y
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨X, ⟨Y₁, hY₁y, hg₁⟩, hg⟩
      rw [isGen_snd_unique i j hij hg hg₁]; exact hY₁y
    · intro hYy
      obtain ⟨X, hg⟩ := y.sub hYy
      exact ⟨X, ⟨Y, hYy, hg⟩, hg⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hXx
      obtain ⟨Y, hg⟩ := isGen_exists i j hji (x.sub hXx)
      obtain ⟨X₁, hX₁x', hg₁⟩ := h Y ⟨X, hXx, hg⟩
      rw [isGen_fst_unique i j hji hg hg₁]; exact hX₁x'
    · rintro h Y ⟨X, hXx, hg⟩
      exact ⟨X, h X hXx, hg⟩

/-- **Lemma 6.15 (Scott 1981, PRG-19).** A projection pair `i : D → E`, `j : E →
D` with
`j ∘ i = I_D` and `i ∘ j ⊆ I_E` exhibits `D` as a subdomain of `E`: `D ⊴ E`. This
is the converse
of Proposition 6.12 (`Subsystem.projectionPair`). -/
theorem trianglelefteq_of_projectionPair (hji : j.comp i = idMap D)
    (hij : i.comp j ≤ idMap E) : D ⊴ E :=
  ⟨Dprime i j, Dprime_subsystem i j, ⟨dprimeEquiv i j hji hij⟩⟩

end ProjectionPair

/-- **Proposition 6.12 + Lemma 6.15 packaged.** A subdomain relation `D ◁ E` is in
particular a
witness of `D ⊴ E` (take `D' = D`). Together with
`trianglelefteq_of_projectionPair`, this shows
`D ⊴ E` holds **iff** there is a projection pair `D ⇄ E`. -/
theorem Subsystem.trianglelefteq {D E : NeighborhoodSystem α} (h : D ◁ E) : D ⊴ E :=
  ⟨D, h, Isomorphic.refl D⟩

end Domain.Neighborhood
