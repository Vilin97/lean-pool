/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Basic
import Mathlib.Tactic.Set

/-!
# Lecture II (§2) — approximable mappings: Definitions 2.1, 2.2 and Theorems
2.5–2.7

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19
(1981), Lecture II,
*Approximable mappings*. A mapping of domains that "preserves the spirit of
approximation" is given
not by a function on ideal elements but by a **relation between neighbourhoods**:
`X f Y` reads "if
the input is approximated at least as well as by `X`, then the output is
approximated at least as
well as by `Y`."

This file formalizes the §2 core:

* **Definition 2.1** — `ApproximableMap V₀ V₁`: a relation `f ⊆ 𝒟₀ × 𝒟₁` with
  (i) `Δ₀ f Δ₁` (`master_rel`),
  (ii) `X f Y → X f Y' → X f (Y ∩ Y')` (`inter_right`, the
  consistency/intersectivity condition),
  (iii) `X f Y → X' ⊆ X → Y ⊆ Y' → X' f Y'` (`mono`, monotonicity: sharper input,
  blunter output).
  We carry `rel_dom`/`rel_cod` recording `f ⊆ 𝒟₀ × 𝒟₁`.
* **Proposition 2.2** — every approximable mapping determines an elementwise
function
  `toElementMap f : |𝒟₀| → |𝒟₁|`, `f(x) = {Y ∣ ∃ X ∈ x, X f Y}`, which is a filter
  (i)–(iii) are
  *all* used); the relation is recovered by `rel_iff_mem_principal` (`X f Y ↔ Y ∈
  f(↑X)`); the map
  is monotone (`toElementMap_mono`); and two approximable maps are equal iff they
  induce the same
  elementwise map (`ext_of_toElementMap`).
* **Theorem 2.5** — neighbourhood systems and approximable maps form a
**category**: identity
  `idMap` (`X I_D Y ↔ X ⊆ Y`), composition `comp g f` (`X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y
  g Z`), with the
  identity laws `idMap_comp`/`comp_idMap` and associativity `comp_assoc`.
* **Proposition 2.6** — the elementwise action is a **functor** to sets and
functions:
  `toElementMap_idMap` (`I_D(x) = x`) and `toElementMap_comp` (`(g∘f)(x) =
  g(f(x))`).
* **Theorem 2.7** — every domain **isomorphism** `e : |𝒟₀| ≃o |𝒟₁|` (Definition
1.9) comes from an
  approximable map: `ofIso e` with `toElementMap_ofIso` (`(ofIso e)(x) = e(x)`),
  packaged as
  `exists_approximable_of_iso`; moreover `e` carries finite (principal) elements
  to finite elements
  (`exists_principal_eq_apply_principal`), via the directed-union construction
  `sSupDirected`.

Everything in this file is **choice-free** (`#print axioms ⊆ {propext,
Quot.sound}`); the only
classical lemma is `ext_of_toElementMap`, which decides neighbourhood membership
by `by_cases`
(`Classical.em`). -/

namespace Domain.Neighborhood

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace NeighborhoodSystem

/-- **Directed union of filters.** The union `⋃ S = {Z ∣ ∃ s ∈ S, Z ∈ s}` of a
*non-empty directed*
family `S` of elements (any two members have an upper bound in `S`) is again an
element. The only
non-trivial law is `inter_mem`: given `Z ∈ a` and `Z' ∈ b`, an upper bound `c ⊇ a,
b` contains both,
hence `Z ∩ Z' ∈ c`. (Generalizes `chainUnion` of Exercise 1.24 from chains to
directed sets; this is
the construction behind Exercise 2.11 and Scott's finiteness argument in Theorem
2.7.) -/
def sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) : V.Element where
  mem Z := ∃ s ∈ S, s.mem Z
  sub := fun ⟨s, _, hs⟩ => s.sub hs
  master_mem := by obtain ⟨s, hs⟩ := hne; exact ⟨s, hs, s.master_mem⟩
  inter_mem := by
    rintro Z Z' ⟨a, haS, haZ⟩ ⟨b, hbS, hbZ⟩
    obtain ⟨c, hcS, hac, hbc⟩ := hdir a haS b hbS
    exact ⟨c, hcS, c.inter_mem (hac Z haZ) (hbc Z' hbZ)⟩
  up_mem := by
    rintro Z Z' ⟨a, haS, haZ⟩ hZ' hZZ'
    exact ⟨a, haS, a.up_mem haZ hZ' hZZ'⟩

/-- Each member of a directed family approximates the directed union. -/
theorem le_sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {a : V.Element} (ha : a ∈ S) :
    a ≤ V.sSupDirected S hne hdir :=
  fun _ hZ => ⟨a, ha, hZ⟩

/-- The directed union is the least upper bound: an upper bound of every member
dominates it. -/
theorem sSupDirected_le (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {y : V.Element}
    (hy : ∀ s ∈ S, s ≤ y) : V.sSupDirected S hne hdir ≤ y := by
  rintro Z ⟨s, hs, hsZ⟩
  exact hy s hs Z hsZ

end NeighborhoodSystem

/-- **Definition 2.1 (Scott 1981, PRG-19).** An *approximable mapping* `f : 𝒟₀ →
𝒟₁` is a relation
`rel` between neighbourhoods (`rel X Y`, Scott's `X f Y`) confined to `𝒟₀ × 𝒟₁`
and satisfying
Scott's three conditions:

* (i)   `Δ₀ f Δ₁`                                   — `master_rel`;
* (ii)  `X f Y` and `X f Y'` imply `X f (Y ∩ Y')`   — `inter_right`;
* (iii) `X f Y`, `X' ⊆ X`, `Y ⊆ Y'` imply `X' f Y'` — `mono` (the targets `X'`,
`Y'` must be
  neighbourhoods, as Scott's relation lives on `𝒟₀ × 𝒟₁`). -/
structure ApproximableMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) where
  /-- The underlying neighbourhood relation `X f Y`. -/
  rel : Set α → Set β → Prop
  /-- `f ⊆ 𝒟₀ × 𝒟₁` (domain side): related inputs are neighbourhoods. -/
  rel_dom : ∀ {X Y}, rel X Y → V₀.mem X
  /-- `f ⊆ 𝒟₀ × 𝒟₁` (codomain side): related outputs are neighbourhoods. -/
  rel_cod : ∀ {X Y}, rel X Y → V₁.mem Y
  /-- (i) `Δ₀ f Δ₁`. -/
  master_rel : rel V₀.master V₁.master
  /-- (ii) intersectivity on the output: `X f Y → X f Y' → X f (Y ∩ Y')`. -/
  inter_right : ∀ {X Y Y'}, rel X Y → rel X Y' → rel X (Y ∩ Y')
  /-- (iii) monotonicity: a sharper input `X' ⊆ X` with a blunter output `Y ⊆ Y'`
  is still related,
  provided `X'`, `Y'` are neighbourhoods. -/
  mono : ∀ {X X' Y Y'}, rel X Y → X' ⊆ X → Y ⊆ Y' → V₀.mem X' → V₁.mem Y' → rel X' Y'

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Extensionality for the relation.** Two approximable maps with the same
neighbourhood relation
are equal (the remaining fields are propositions). -/
theorem ext {f g : ApproximableMap V₀ V₁} (h : ∀ X Y, f.rel X Y ↔ g.rel X Y) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y; exact propext (h X Y)
  subst this; rfl

/-- **Proposition 2.2(i) (Scott 1981, PRG-19).** The elementwise function
determined by an
approximable mapping: `f(x) = {Y ∈ 𝒟₁ ∣ ∃ X ∈ x, X f Y}`. The four filter laws use
*all* of
Definition 2.1: `master_mem` uses (i); `inter_mem` uses (ii) together with (iii)
(to pull both
outputs back along the common input `X ∩ X'`); `up_mem` uses (iii). -/
def toElementMap (f : ApproximableMap V₀ V₁) (x : V₀.Element) : V₁.Element where
  mem Y := ∃ X, x.mem X ∧ f.rel X Y
  sub := fun ⟨_, _, hXY⟩ => f.rel_cod hXY
  master_mem := ⟨V₀.master, x.master_mem, f.master_rel⟩
  inter_mem := by
    rintro Y Y' ⟨X, hX, hXY⟩ ⟨X', hX', hX'Y'⟩
    have hXX'mem : x.mem (X ∩ X') := x.inter_mem hX hX'
    have hXX' : V₀.mem (X ∩ X') := x.sub hXX'mem
    refine ⟨X ∩ X', hXX'mem, ?_⟩
    have h1 : f.rel (X ∩ X') Y :=
      f.mono hXY Set.inter_subset_left subset_rfl hXX' (f.rel_cod hXY)
    have h2 : f.rel (X ∩ X') Y' :=
      f.mono hX'Y' Set.inter_subset_right subset_rfl hXX' (f.rel_cod hX'Y')
    exact f.inter_right h1 h2
  up_mem := by
    rintro Y Y' ⟨X, hX, hXY⟩ hY' hYY'
    exact ⟨X, hX, f.mono hXY subset_rfl hYY' (x.sub hX) hY'⟩

@[simp] theorem mem_toElementMap (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β} :
    (f.toElementMap x).mem Y ↔ ∃ X, x.mem X ∧ f.rel X Y := Iff.rfl

/-- **Proposition 2.2(ii) (Scott 1981, PRG-19).** The relation is recovered from
the elementwise
map: for `X ∈ 𝒟₀`, `X f Y ↔ Y ∈ f(↑X)`. (`→` since `X ∈ ↑X`; `←` since any `Z ∈
↑X` has `X ⊆ Z`,
so `Z f Y` monotonically yields `X f Y`.) -/
theorem rel_iff_mem_principal (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) {Y : Set β} :
    f.rel X Y ↔ (f.toElementMap (V₀.principal hX)).mem Y := by
  constructor
  · intro hXY
    exact ⟨X, ⟨hX, subset_rfl⟩, hXY⟩
  · rintro ⟨Z, ⟨_, hXZ⟩, hZY⟩
    exact f.mono hZY hXZ subset_rfl hX (f.rel_cod hZY)

/-- **Proposition 2.2(iii) (Scott 1981, PRG-19).** Approximable maps are monotone
on elements:
`x ⊑ y ⟹ f(x) ⊑ f(y)`. -/
theorem toElementMap_mono (f : ApproximableMap V₀ V₁) {x y : V₀.Element} (hxy : x ≤ y) :
    f.toElementMap x ≤ f.toElementMap y := by
  rintro Y ⟨X, hX, hXY⟩
  exact ⟨X, hxy X hX, hXY⟩

/-- **Proposition 2.2(iv) (Scott 1981, PRG-19).** Two approximable maps are
*identical as relations*
iff they induce the same elementwise function: `(∀ x, f(x) = g(x)) ⟹ f = g`. For
neighbourhoods `X`
the relation is read off `f(↑X)` (`rel_iff_mem_principal`); off `𝒟₀` both
relations are empty. -/
theorem ext_of_toElementMap {f g : ApproximableMap V₀ V₁}
    (h : ∀ x, f.toElementMap x = g.toElementMap x) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : V₀.mem X
  · rw [f.rel_iff_mem_principal hX, g.rel_iff_mem_principal hX, h]
  · constructor
    · intro hr; exact absurd (f.rel_dom hr) hX
    · intro hr; exact absurd (g.rel_dom hr) hX

/-! ### Theorem 2.5 — the category of neighbourhood systems and approximable
mappings. -/

/-- **Theorem 2.5(i) (Scott 1981, PRG-19) — the identity mapping `I_D`.** `X I_D Y
↔ X ⊆ Y`
(confined to `𝒟 × 𝒟`). It is approximable: (i) `Δ ⊆ Δ`; (ii) `X ⊆ Y`, `X ⊆ Y'`
give `X ⊆ Y ∩ Y'`
with witness `X`; (iii) is transitivity `X' ⊆ X ⊆ Y ⊆ Y'`. -/
def idMap (V : NeighborhoodSystem α) : ApproximableMap V V where
  rel X Y := V.mem X ∧ V.mem Y ∧ X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V.master_mem, V.master_mem, subset_rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    exact ⟨hX, V.inter_mem hY hY' hX (Set.subset_inter hXY hXY'), Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (hX'X.trans hXY).trans hYY'⟩

@[simp] theorem idMap_rel {V : NeighborhoodSystem α} {X Y : Set α} :
    (idMap V).rel X Y ↔ V.mem X ∧ V.mem Y ∧ X ⊆ Y := Iff.rfl

/-- **Theorem 2.5(ii) (Scott 1981, PRG-19) — composition `g ∘ f`.** `X (g∘f) Z ↔ ∃
Y, X f Y ∧ Y
g Z`.
Approximability is Scott's verification: (i) use `Y = Δ₁`; (ii) intersect both
witnesses via
`f.inter_right` then `g.inter_right` (narrowing the inner neighbourhood with
`g.mono`); (iii) narrow
the input with `f.mono` and widen the output with `g.mono`, keeping the same
witness. -/
def comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₂ where
  rel X Z := ∃ Y, f.rel X Y ∧ g.rel Y Z
  rel_dom := fun ⟨_, hXY, _⟩ => f.rel_dom hXY
  rel_cod := fun ⟨_, _, hYZ⟩ => g.rel_cod hYZ
  master_rel := ⟨V₁.master, f.master_rel, g.master_rel⟩
  inter_right := by
    rintro X Z Z' ⟨Y, hXY, hYZ⟩ ⟨Y', hXY', hY'Z'⟩
    refine ⟨Y ∩ Y', f.inter_right hXY hXY', ?_⟩
    have hYY'mem : V₁.mem (Y ∩ Y') := f.rel_cod (f.inter_right hXY hXY')
    have h1 : g.rel (Y ∩ Y') Z :=
      g.mono hYZ Set.inter_subset_left subset_rfl hYY'mem (g.rel_cod hYZ)
    have h2 : g.rel (Y ∩ Y') Z' :=
      g.mono hY'Z' Set.inter_subset_right subset_rfl hYY'mem (g.rel_cod hY'Z')
    exact g.inter_right h1 h2
  mono := by
    rintro X X' Z Z' ⟨Y, hXY, hYZ⟩ hX'X hZZ' hX' hZ'
    refine ⟨Y, f.mono hXY hX'X subset_rfl hX' (f.rel_cod hXY), ?_⟩
    exact g.mono hYZ subset_rfl hZZ' (g.rel_dom hYZ) hZ'

@[simp] theorem comp_rel {g : ApproximableMap V₁ V₂} {f : ApproximableMap V₀ V₁} {X : Set α}
    {Z : Set γ} : (g.comp f).rel X Z ↔ ∃ Y, f.rel X Y ∧ g.rel Y Z := Iff.rfl

/-- **Theorem 2.5 — left identity law.** `I_{D₁} ∘ f = f`. (`→`: a witness `Y ⊆ Z`
widens the output
of `f` by `f.mono`; `←`: take `Y = Z`.) -/
theorem idMap_comp (f : ApproximableMap V₀ V₁) : (idMap V₁).comp f = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, hXY, _, hZ, hYZ⟩
    exact f.mono hXY subset_rfl hYZ (f.rel_dom hXY) hZ
  · intro hXZ
    exact ⟨Z, hXZ, f.rel_cod hXZ, f.rel_cod hXZ, subset_rfl⟩

/-- **Theorem 2.5 — right identity law.** `f ∘ I_{D₀} = f`. (`→`: a witness `X ⊆
Y` sharpens the
input of `f` by `f.mono`; `←`: take `Y = X`.) -/
theorem comp_idMap (f : ApproximableMap V₀ V₁) : f.comp (idMap V₀) = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, hYZ⟩
    exact f.mono hYZ hXY subset_rfl hX (f.rel_cod hYZ)
  · intro hXZ
    exact ⟨X, ⟨f.rel_dom hXZ, f.rel_dom hXZ, subset_rfl⟩, hXZ⟩

/-- **Theorem 2.5 — associativity.** `h ∘ (g ∘ f) = (h ∘ g) ∘ f`. Pure
reassociation of the
existential witnesses. -/
theorem comp_assoc {V₃ : NeighborhoodSystem δ} (h : ApproximableMap V₂ V₃)
    (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ApproximableMap.ext
  intro X W
  constructor
  · rintro ⟨Y, hXY, Z, hYZ, hZW⟩
    exact ⟨Z, ⟨Y, hXY, hYZ⟩, hZW⟩
  · rintro ⟨Z, ⟨Y, hXY, hYZ⟩, hZW⟩
    exact ⟨Y, hXY, Z, hYZ, hZW⟩

/-! ### Proposition 2.6 — the functor to sets and functions. -/

/-- **Proposition 2.6(i) (Scott 1981, PRG-19).** The identity mapping acts as the
identity on
elements: `I_D(x) = x`. (`→`: `X ∈ x`, `X ⊆ Y ∈ 𝒟` gives `Y ∈ x` by `up_mem`; `←`:
take `X = Y`.) -/
@[simp] theorem toElementMap_idMap (x : V₀.Element) : (idMap V₀).toElementMap x = x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXx, _, hY, hXY⟩
    exact x.up_mem hXx hY hXY
  · intro hY
    exact ⟨Y, hY, x.sub hY, x.sub hY, subset_rfl⟩

/-- **Proposition 2.6(ii) (Scott 1981, PRG-19).** Composition of approximable
mappings becomes
composition of the elementwise functions: `(g ∘ f)(x) = g(f(x))`. Both sides
unfold to
`∃ Y X, x.mem X ∧ X f Y ∧ Y g Z`; the proof is a reassociation of existentials. -/
theorem toElementMap_comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) (x : V₀.Element) :
    (g.comp f).toElementMap x = g.toElementMap (f.toElementMap x) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, hXx, Y, hXY, hYZ⟩
    exact ⟨Y, ⟨X, hXx, hXY⟩, hYZ⟩
  · rintro ⟨Y, ⟨X, hXx, hXY⟩, hYZ⟩
    exact ⟨X, hXx, Y, hXY, hYZ⟩

/-! ### Theorem 2.7 — every domain isomorphism comes from an approximable mapping. -/

/-- **Theorem 2.7 (Scott 1981, PRG-19) — the approximable map of an isomorphism.**
Given a domain
isomorphism `e : |𝒟₀| ≃o |𝒟₁|` (Definition 1.9), Scott's "only way to define a
neighbourhood
mapping" is the relation `X f Y ↔ Y ∈ e(↑X)`. The conditions of 2.1 hold because
`e` is monotone:
(i) `Δ₁ ∈ e(⊥₀)` is `master_mem`; (ii) is `inter_mem` of the filter `e(↑X)`; (iii)
sharpening `X' ⊆ X`
means `↑X ⊑ ↑X'`, so `e(↑X) ⊑ e(↑X')` and the output transports along, then widens
by `up_mem`. -/
def ofIso (e : V₀.Element ≃o V₁.Element) : ApproximableMap V₀ V₁ where
  rel X Y := ∃ _ : V₀.mem X, (e (V₀.principal ‹V₀.mem X›)).mem Y
  rel_dom := fun ⟨hX, _⟩ => hX
  rel_cod := fun ⟨_, hY⟩ => (e _).sub hY
  master_rel := ⟨V₀.master_mem, (e _).master_mem⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    exact ⟨hX, (e (V₀.principal hX)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', ?_⟩
    have hle : V₀.principal hX ≤ V₀.principal hX' := (V₀.principal_le_iff hX hX').mpr hX'X
    have hmem : (e (V₀.principal hX')).mem Y := (e.monotone hle) Y hY
    exact (e (V₀.principal hX')).up_mem hmem hY' hYY'

/-- **Theorem 2.7 — the relation re-defines the function.** The elementwise map of
`ofIso e` is `e`
itself: `(ofIso e)(x) = e(x)` for every `x`. The forward inclusion uses that `X ∈
x` implies
`↑X ⊑ x`, hence `e(↑X) ⊑ e(x)`; the reverse uses surjectivity of `e` (via
`e.symm`) exactly as in
Scott's proof — one shows `x = e⁻¹((ofIso e)(x))` by antisymmetry. -/
theorem toElementMap_ofIso (e : V₀.Element ≃o V₁.Element) (x : V₀.Element) :
    (ofIso e).toElementMap x = e x := by
  have hgxle : (ofIso e).toElementMap x ≤ e x := by
    rintro Y ⟨X, hXx, hX, hY⟩
    have hpx : V₀.principal hX ≤ x := fun Z hZ => x.up_mem hXx hZ.1 hZ.2
    exact (e.monotone hpx) Y hY
  have key : x = e.symm ((ofIso e).toElementMap x) := by
    apply le_antisymm
    · intro X hXx
      have hX : V₀.mem X := x.sub hXx
      have hsub : e (V₀.principal hX) ≤ (ofIso e).toElementMap x :=
        fun Y hY => ⟨X, hXx, hX, hY⟩
      have hple : V₀.principal hX ≤ e.symm ((ofIso e).toElementMap x) := by
        have h := e.symm.monotone hsub
        rwa [e.symm_apply_apply] at h
      exact hple X ⟨hX, subset_rfl⟩
    · have h := e.symm.monotone hgxle
      rwa [e.symm_apply_apply] at h
  have h1 : e x = e (e.symm ((ofIso e).toElementMap x)) := congrArg e key
  rw [e.apply_symm_apply] at h1
  exact h1.symm

/-- **Theorem 2.7 (statement) (Scott 1981, PRG-19).** "Every isomorphism between
domains results
from
an approximable mapping." For any domain isomorphism `e`, there is an approximable
mapping whose
elementwise action is exactly `e`. -/
theorem exists_approximable_of_iso (e : V₀.Element ≃o V₁.Element) :
    ∃ f : ApproximableMap V₀ V₁, ∀ x, f.toElementMap x = e x :=
  ⟨ofIso e, toElementMap_ofIso e⟩

/-- **Theorem 2.7 (Scott 1981, PRG-19) — finite elements go to finite elements.**
A domain
isomorphism `e` carries the finite (principal) element `↑X` to a finite element
`↑Y` of the other
domain. Following Scott: with `w = e(↑X)`, the set `S = {e⁻¹(↑Y) ∣ Y ∈ w}` is
directed (intersections
of members of `w` give upper bounds), so its union `z = ⋃ S` is an element
(`sSupDirected`). One shows
`z = ↑X` (each `e⁻¹(↑Y) ⊑ e⁻¹(w) = ↑X`, and conversely `w ⊑ e(z)` forces `↑X =
e⁻¹(w) ⊑ z`); then
`X ∈ z` lands in some `e⁻¹(↑Y)`, giving `w ⊑ ↑Y`, while `↑Y ⊑ w` is automatic — so
`w = ↑Y`. -/
theorem exists_principal_eq_apply_principal (e : V₀.Element ≃o V₁.Element)
    {X : Set α} (hX : V₀.mem X) :
    ∃ (Y : Set β) (hY : V₁.mem Y), e (V₀.principal hX) = V₁.principal hY := by
  -- `w = e(↑X)`, and the directed family `S` of inverse images of principals of
  -- members of `w`.
  set w : V₁.Element := e (V₀.principal hX) with hw
  set S : Set V₀.Element :=
    {z | ∃ (Y : Set β) (hY : V₁.mem Y), w.mem Y ∧ z = e.symm (V₁.principal hY)} with hS
  -- `e⁻¹(w) = ↑X`.
  have hsymm_w : e.symm w = V₀.principal hX := by rw [hw, e.symm_apply_apply]
  -- For `Y ∈ w`, `↑Y ⊑ w`.
  have hprin_le_w : ∀ {Y : Set β} (hY : V₁.mem Y), w.mem Y → V₁.principal hY ≤ w :=
    fun hY hYw Z hZ => w.up_mem hYw hZ.1 hZ.2
  -- `S` is non-empty (use `Y = Δ₁`).
  have hne : S.Nonempty :=
    ⟨e.symm (V₁.principal V₁.master_mem), V₁.master, V₁.master_mem, w.master_mem, rfl⟩
  -- `S` is directed: intersect the two members of `w`.
  have hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c := by
    rintro a ⟨Y, hY, hYw, rfl⟩ b ⟨Y', hY', hY'w, rfl⟩
    have hYY'w : w.mem (Y ∩ Y') := w.inter_mem hYw hY'w
    have hYY' : V₁.mem (Y ∩ Y') := w.sub hYY'w
    refine ⟨e.symm (V₁.principal hYY'), ⟨Y ∩ Y', hYY', hYY'w, rfl⟩, ?_, ?_⟩
    · exact e.symm.monotone ((V₁.principal_le_iff hY hYY').mpr Set.inter_subset_left)
    · exact e.symm.monotone ((V₁.principal_le_iff hY' hYY').mpr Set.inter_subset_right)
  -- The directed union `z = ⋃ S`.
  set z : V₀.Element := V₀.sSupDirected S hne hdir with hz
  -- `z ⊑ ↑X`: every member `e⁻¹(↑Y) ⊑ e⁻¹(w) = ↑X`.
  have hz_le : z ≤ V₀.principal hX := by
    apply V₀.sSupDirected_le
    rintro s ⟨Y, hY, hYw, rfl⟩
    have : e.symm (V₁.principal hY) ≤ e.symm w := e.symm.monotone (hprin_le_w hY hYw)
    rwa [hsymm_w] at this
  -- `↑X ⊑ z`: show `w ⊑ e(z)`, then `↑X = e⁻¹(w) ⊑ z`.
  have hw_le_ez : w ≤ e z := by
    intro Y hYw
    have hY : V₁.mem Y := w.sub hYw
    have hmem_S : e.symm (V₁.principal hY) ∈ S := ⟨Y, hY, hYw, rfl⟩
    have h1 : e.symm (V₁.principal hY) ≤ z := V₀.le_sSupDirected S hne hdir hmem_S
    have h2 : V₁.principal hY ≤ e z := by
      have := e.monotone h1
      rwa [e.apply_symm_apply] at this
    exact h2 Y ⟨hY, subset_rfl⟩
  have hX_le_z : V₀.principal hX ≤ z := by
    have : e.symm w ≤ e.symm (e z) := e.symm.monotone hw_le_ez
    rwa [hsymm_w, e.symm_apply_apply] at this
  -- Hence `z = ↑X`, so `X ∈ z` lands in some member `e⁻¹(↑Y)`.
  have hz_eq : z = V₀.principal hX := le_antisymm hz_le hX_le_z
  have hXz : z.mem X := hz_eq ▸ ⟨hX, subset_rfl⟩
  obtain ⟨s, ⟨Y, hY, hYw, rfl⟩, hXs⟩ := hXz
  -- `↑X ⊑ e⁻¹(↑Y)` (it contains `X`), so `w = e(↑X) ⊑ ↑Y`; with `↑Y ⊑ w` we get
  -- `w = ↑Y`.
  refine ⟨Y, hY, ?_⟩
  have hprinX_le : V₀.principal hX ≤ e.symm (V₁.principal hY) :=
    fun Z hZ => (e.symm (V₁.principal hY)).up_mem hXs hZ.1 hZ.2
  have hw_le_prinY : w ≤ V₁.principal hY := by
    have := e.monotone hprinX_le
    rw [e.apply_symm_apply] at this
    rwa [← hw] at this
  exact le_antisymm hw_le_prinY (hprin_le_w hY hYw)

end ApproximableMap

end Domain.Neighborhood
