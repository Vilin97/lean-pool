/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Theorem41

/-!
# Exercise 4.10 (Scott 1981, PRG-19, Lecture IV) — the relativized domain `Dₐ`

Given a domain `𝒟` and an element `a ∈ |𝒟|`, construct a domain `Dₐ` whose
elements are exactly
the elements below `a`:

  `|Dₐ| = {x ∈ |𝒟| ∣ x ⊑ a}`.

**Construction.** `relSystem a` keeps the same tokens and master `Δ`, but takes as
neighbourhoods
exactly the *members of the filter `a`* (`mem X := a.mem X`). This is a
neighbourhood system because
`a`, being a filter, contains `Δ` and is closed under consistent intersections.
Its filters are in
order-isomorphism with the elements of `𝒟` below `a` (`relIso`): a `Dₐ`-filter `g`
is sent to its
`𝒟`-upward-closure `embed a g`, and an element `x ⊑ a` is sent to its restriction
`restrict a x`
(automatically a `Dₐ`-filter since `x.mem ⊆ a.mem`).

**Restriction of `f`.** If `f : 𝒟 → 𝒟` is approximable and `f(a) = a` (e.g. `a =
fix(f)`, by
Theorem 4.1), then `f` restricts to an approximable `f' : Dₐ → Dₐ` (`relMap`) with
the same
action (`embed a (f'(g)) = f(embed a g)`, `relMap_toElementMap_embed`). The
codomain condition
`f.rel X Y ⟹ a.mem Y` for `a`-neighbourhoods `X` holds because `↑X ⊑ a`, so `Y ∈
f(↑X) ⊑ f(a) = a`.

**How many fixed points does `f'` have?** When `a = fix(f)`, *exactly one*
(`relMap_unique_fixed`):
the top element of `Dₐ` (corresponding to `fix(f)` itself). Any fixed point of `f`
below `fix(f)` is
a pre-fixed point, hence `⊒ fix(f)` by leastness (`fixElement_below_unique`), so
it *equals* `fix(f)`.

All constructions are **choice-free**; equalities of `Element`/maps use the
project's permitted
`Element.ext`.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-! ### The relativized domain `Dₐ`. -/

/-- **Exercise 4.10 (Scott 1981, PRG-19).** The relativized neighbourhood system
`Dₐ`: same tokens
and master, neighbourhoods exactly the members of the filter `a`. -/
def relSystem (a : V.Element) : NeighborhoodSystem α where
  mem X := a.mem X
  master := V.master
  master_mem := a.master_mem
  sub_master := fun hX => V.sub_master (a.sub hX)
  inter_mem := fun hX hY _ _ => a.inter_mem hX hY

@[simp] theorem relSystem_mem (a : V.Element) {X : Set α} :
    (relSystem a).mem X ↔ a.mem X := Iff.rfl

@[simp] theorem relSystem_master (a : V.Element) : (relSystem a).master = V.master := rfl

/-- The `𝒟`-element obtained from a `Dₐ`-filter by upward closure in `𝒟`. -/
def embed (a : V.Element) (g : (relSystem a).Element) : V.Element where
  mem X := V.mem X ∧ ∃ W, a.mem W ∧ g.mem W ∧ W ⊆ X
  sub := fun h => h.1
  master_mem := ⟨V.master_mem, V.master, a.master_mem, g.master_mem, subset_rfl⟩
  inter_mem := by
    rintro X Y ⟨hVX, Wx, haWx, hgWx, hWxX⟩ ⟨hVY, Wy, haWy, hgWy, hWyY⟩
    have haWxy : a.mem (Wx ∩ Wy) := a.inter_mem haWx haWy
    have hgWxy : g.mem (Wx ∩ Wy) := g.inter_mem hgWx hgWy
    have hsub : Wx ∩ Wy ⊆ X ∩ Y := Set.inter_subset_inter hWxX hWyY
    refine ⟨V.inter_mem hVX hVY (a.sub haWxy) hsub, Wx ∩ Wy, haWxy, hgWxy, hsub⟩
  up_mem := by
    rintro X Y ⟨hVX, W, haW, hgW, hWX⟩ hVY hXY
    exact ⟨hVY, W, haW, hgW, subset_trans hWX hXY⟩

/-- The `Dₐ`-filter obtained from an element `x ⊑ a` by restriction (same
membership). -/
def restrict (a : V.Element) (x : V.Element) (hx : x ≤ a) : (relSystem a).Element where
  mem X := x.mem X
  sub := fun h => hx _ h
  master_mem := x.master_mem
  inter_mem := fun hX hY => x.inter_mem hX hY
  up_mem := fun hX hY hXY => x.up_mem hX (a.sub hY) hXY

/-- `embed a g ⊑ a`: the embedding lands below `a`. -/
theorem embed_le (a : V.Element) (g : (relSystem a).Element) : embed a g ≤ a := by
  rintro X ⟨hVX, W, haW, _, hWX⟩
  exact a.up_mem haW hVX hWX

theorem embed_restrict (a : V.Element) (x : V.Element) (hx : x ≤ a) :
    embed a (restrict a x hx) = x := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, _, hxW, hWX⟩
    exact x.up_mem hxW hVX hWX
  · intro hxX
    exact ⟨x.sub hxX, X, hx _ hxX, hxX, subset_rfl⟩

theorem restrict_embed (a : V.Element) (g : (relSystem a).Element) :
    restrict a (embed a g) (embed_le a g) = g := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, haW, hgW, hWX⟩
    exact g.up_mem hgW (a.up_mem haW hVX hWX) hWX
  · intro hgX
    exact ⟨a.sub (g.sub hgX), X, g.sub hgX, hgX, subset_rfl⟩

theorem embed_mono (a : V.Element) {g₁ g₂ : (relSystem a).Element} (h : g₁ ≤ g₂) :
    embed a g₁ ≤ embed a g₂ := by
  rintro X ⟨hVX, W, haW, hgW, hWX⟩
  exact ⟨hVX, W, haW, h _ hgW, hWX⟩

theorem le_of_embed_le (a : V.Element) {g₁ g₂ : (relSystem a).Element}
    (h : embed a g₁ ≤ embed a g₂) : g₁ ≤ g₂ := by
  intro X hg₁X
  have hVX : V.mem X := a.sub (g₁.sub hg₁X)
  have : (embed a g₂).mem X := h X ⟨hVX, X, g₁.sub hg₁X, hg₁X, subset_rfl⟩
  obtain ⟨_, W, haW, hg₂W, hWX⟩ := this
  exact g₂.up_mem hg₂W (g₁.sub hg₁X) hWX

/-- **Exercise 4.10 (Scott 1981, PRG-19).** `|Dₐ| ≃o {x ∈ |𝒟| ∣ x ⊑ a}`: the
relativized domain has
exactly the elements below `a` as its points, with the inherited order. -/
def relIso (a : V.Element) : (relSystem a).Element ≃o {x : V.Element // x ≤ a} where
  toFun g := ⟨embed a g, embed_le a g⟩
  invFun x := restrict a x.1 x.2
  left_inv g := restrict_embed a g
  right_inv x := Subtype.ext (embed_restrict a x.1 x.2)
  map_rel_iff' := by
    intro g₁ g₂
    constructor
    · intro h; exact le_of_embed_le a h
    · intro h; exact embed_mono a h

/-! ### Restricting an endomap with `f(a) = a`. -/

/-- **Exercise 4.10 (Scott 1981, PRG-19).** When `f(a) = a`, the restriction `f' :
Dₐ → Dₐ`
(`f'(x) = f(x)`). The codomain condition uses `↑X ⊑ a ⟹ f(↑X) ⊑ f(a) = a`. -/
def relMap (f : ApproximableMap V V) {a : V.Element} (ha : f.toElementMap a = a) :
    ApproximableMap (relSystem a) (relSystem a) where
  rel X Y := a.mem X ∧ f.rel X Y
  rel_dom := fun h => h.1
  rel_cod := by
    rintro X Y ⟨haX, hXY⟩
    have hVX : V.mem X := a.sub haX
    have hpr : V.principal hVX ≤ a := fun Z ⟨hVZ, hXZ⟩ => a.up_mem haX hVZ hXZ
    have hmemfX : (f.toElementMap (V.principal hVX)).mem Y := (f.rel_iff_mem_principal hVX).mp hXY
    have hle : f.toElementMap (V.principal hVX) ≤ f.toElementMap a := f.toElementMap_mono hpr
    have : (f.toElementMap a).mem Y := hle Y hmemfX
    rw [ha] at this
    exact this
  master_rel := ⟨a.master_mem, f.master_rel⟩
  inter_right := by
    rintro X Y Y' ⟨haX, hXY⟩ ⟨_, hXY'⟩
    exact ⟨haX, f.inter_right hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, hXY⟩ hX'X hYY' haX' haY'
    exact ⟨haX', f.mono hXY hX'X hYY' (a.sub haX') (a.sub haY')⟩

/-- The restriction `f'` has the same action as `f`: `embed a (f'(g)) = f(embed a
g)`. -/
theorem relMap_toElementMap_embed (f : ApproximableMap V V) {a : V.Element}
    (ha : f.toElementMap a = a) (g : (relSystem a).Element) :
    embed a ((relMap f ha).toElementMap g) = f.toElementMap (embed a g) := by
  apply Element.ext
  intro X
  constructor
  · rintro ⟨hVX, W, haW, ⟨U, hgU, haU, hUW⟩, hWX⟩
    -- `U ∈ g`, `U f W`, `W ⊆ X`; so `X ∈ f(embed g)` via the member `U` of `embed
    -- g`.
    refine ⟨U, ⟨a.sub haU, U, haU, hgU, subset_rfl⟩, ?_⟩
    exact f.mono hUW subset_rfl hWX (a.sub haU) hVX
  · rintro ⟨U, ⟨hVU, W, haW, hgW, hWU⟩, hUX⟩
    -- `W ∈ g`, `W ⊆ U`, `U f X`; so `W f X` and `X ∈ embed a (f'(g))`.
    have hVX : V.mem X := f.rel_cod hUX
    have hWX : f.rel W X := f.mono hUX hWU subset_rfl (a.sub haW) hVX
    have haX : a.mem X := by
      have hpr : V.principal (a.sub haW) ≤ a := fun Z ⟨hVZ, hXZ⟩ => a.up_mem haW hVZ hXZ
      have hmemfW : (f.toElementMap (V.principal (a.sub haW))).mem X :=
        (f.rel_iff_mem_principal (a.sub haW)).mp hWX
      have := (f.toElementMap_mono hpr) X hmemfW
      rw [ha] at this; exact this
    exact ⟨hVX, X, haX, ⟨W, hgW, haW, hWX⟩, subset_rfl⟩

/-! ### How many fixed points does `f'` have? -/

/-- **Exercise 4.10 (Scott 1981, PRG-19).** Any fixed point of `f` below `fix(f)`
*is* `fix(f)`:
a fixed point is a pre-fixed point, so leastness forces `fix(f) ⊑ x`. -/
theorem fixElement_below_unique (f : ApproximableMap V V) {x : V.Element}
    (hxle : x ≤ f.fixElement) (hxfix : f.toElementMap x = x) : x = f.fixElement := by
  have hge : f.fixElement ≤ x := fixElement_le_of_toElementMap_le f (le_of_eq hxfix)
  exact le_antisymm hxle hge

/-- **Exercise 4.10 (Scott 1981, PRG-19).** With `a = fix(f)`, the restricted map
`f'` has *exactly
one* fixed point: the top element of `D_{fix f}`, namely `restrict (fix f)` of
`fix f` itself. Every
`Dₐ`-fixed point `g` of `f'` satisfies `embed a g = fix f`, hence is this top
element. -/
theorem relMap_unique_fixed (f : ApproximableMap V V)
    (ha : f.toElementMap f.fixElement = f.fixElement) (g : (relSystem f.fixElement).Element)
    (hg : (relMap f ha).toElementMap g = g) :
    g = restrict f.fixElement f.fixElement (le_refl _) := by
  -- `embed g` is a fixed point of `f` below `fix f`, hence equals `fix f`.
  have hembfix : f.toElementMap (embed f.fixElement g) = embed f.fixElement g := by
    rw [← relMap_toElementMap_embed f ha g, hg]
  have heq : embed f.fixElement g = f.fixElement :=
    fixElement_below_unique f (embed_le f.fixElement g) hembfix
  -- transport along the iso.
  have h1 : restrict f.fixElement (embed f.fixElement g) (embed_le f.fixElement g) = g :=
    restrict_embed f.fixElement g
  -- both restricts agree because their underlying elements agree.
  have h2 : restrict f.fixElement (embed f.fixElement g) (embed_le f.fixElement g)
      = restrict f.fixElement f.fixElement (le_refl _) := by
    apply Element.ext
    intro X
    change (embed f.fixElement g).mem X ↔ f.fixElement.mem X
    rw [heq]
  rw [← h1, h2]

end ApproximableMap

end Domain.Neighborhood
