/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise407
import LeanPool.DomainTheory.Neighborhood.Exercise410

/-!
# Exercise 4.11 (Scott 1981, PRG-19, Lecture IV) — Plotkin's uniqueness of `fix`

(Suggested by G. Plotkin.) Regard `fix` as assigning a fixed-point operator `F_𝒟 :
(𝒟 → 𝒟) → 𝒟`
to each domain `𝒟`. Scott asks to show `fix` is the **unique** such assignment `𝒟
↝ F_𝒟` subject to:

* (i)   `F_𝒟 : (𝒟 → 𝒟) → 𝒟`;
* (ii)  `F_𝒟(f) = f(F_𝒟(f))` for all `f : 𝒟 → 𝒟`  (each value is a fixed point);
* (iii) *(uniformity)* whenever `f₀ : 𝒟₀ → 𝒟₀`, `f₁ : 𝒟₁ → 𝒟₁` and `h : 𝒟₀ → 𝒟₁`
satisfy
        `h(⊥) = ⊥` and `h ∘ f₀ = f₁ ∘ h`, then `h(F_{𝒟₀}(f₀)) = F_{𝒟₁}(f₁)`.

**`fix` satisfies (iii)** (`fixElement_uniform`): writing `fix(f₀) = ⊔ₙ f₀ⁿ(⊥)`
(Theorem 4.2(iii)),
the intertwining `h ∘ f₀ = f₁ ∘ h` together with `h(⊥) = ⊥` gives `h(f₀ⁿ(⊥)) =
f₁ⁿ(⊥)` by induction,
and `h` preserves directed unions, so `h(fix f₀) = ⊔ₙ f₁ⁿ(⊥) = fix f₁`.

**Uniqueness** (`fix_unique_of_uniform`): given *any* `F` obeying (ii) and (iii),
and any `f : 𝒟 → 𝒟`,
apply (iii) with the inclusion `h = ι : 𝒟_{fix f} ↪ 𝒟` of the relativized domain
(Exercise 4.10).
`ι(⊥) = ⊥` (`inclMap_bot`) and `ι ∘ f' = f ∘ ι` (`inclMap_intertwine`, from
`relMap_toElementMap_embed`). Hence `ι(F_{𝒟_{fix f}}(f')) = F_𝒟(f)`. But
`F_{𝒟_{fix f}}(f')` is a
fixed point of `f'` by (ii), and `f'` has **exactly one** fixed point (Exercise
4.10,
`relMap_unique_fixed`) — the top point `fix f` — so the left side is `ι(fix f) =
fix f`. Therefore
`F_𝒟(f) = fix f`.

`fix` satisfying (i)/(ii) is Theorem 4.2 (`fixMap`, `fixMap_fixed`). The
uniqueness proof uses only
the project's permitted `Element.ext`; the inclusion data `inclMap` is
**choice-free**.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-! ### `fix` satisfies the uniformity condition (iii). -/

/-- `fⁿ(⊥) ⊑ fix(f)`: every approximant lies below the least fixed point. -/
theorem iterElem_le_fixElement (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n ≤ f.fixElement :=
  fun _ hX => ⟨n, (mem_iterElem f n).mp hX⟩

/-- **Exercise 4.11(iii) (Scott 1981, PRG-19).** `fix` is *uniform*: if `h(⊥) = ⊥`
and
`h ∘ f₀ = f₁ ∘ h`, then `h(fix f₀) = fix f₁`. -/
theorem fixElement_uniform {β γ : Type*} {W₀ : NeighborhoodSystem β} {W₁ : NeighborhoodSystem γ}
    (f₀ : ApproximableMap W₀ W₀) (f₁ : ApproximableMap W₁ W₁) (h : ApproximableMap W₀ W₁)
    (hbot : h.toElementMap W₀.bot = W₁.bot)
    (hintw : ∀ x, h.toElementMap (f₀.toElementMap x) = f₁.toElementMap (h.toElementMap x)) :
    h.toElementMap f₀.fixElement = f₁.fixElement := by
  -- `h` carries the `n`-th approximant of `f₀` to that of `f₁`.
  have hiter : ∀ n, h.toElementMap (f₀.iterElem n) = f₁.iterElem n := by
    intro n
    rw [iterElem_eq_iterate f₀ n, iterElem_eq_iterate f₁ n]
    induction n with
    | zero => simpa using hbot
    | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, Function.iterate_succ',
        Function.comp_apply, hintw, ih]
  apply le_antisymm
  · -- `h(fix f₀) = ⊔ₙ h(f₀ⁿ(⊥)) = ⊔ₙ f₁ⁿ(⊥) ⊑ fix f₁`.
    rw [fixElement_eq_iSupDirected f₀, toElementMap_iSupDirected]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    rw [hiter n]
    exact iterElem_le_fixElement f₁ n
  · -- `h(fix f₀)` is a fixed point of `f₁`, so `fix f₁ ⊑ h(fix f₀)` by minimality.
    have hfp : f₁.toElementMap (h.toElementMap f₀.fixElement) = h.toElementMap f₀.fixElement := by
      rw [← hintw f₀.fixElement, toElementMap_fixElement]
    exact fixElement_le_of_toElementMap_le f₁ (le_of_eq hfp)

/-! ### The inclusion `ι : 𝒟ₐ ↪ 𝒟` of the relativized domain (Exercise 4.10). -/

/-- The inclusion `𝒟ₐ → 𝒟` as an approximable map: an `a`-neighbourhood `X`
relates to any larger
`𝒟`-neighbourhood `Y ⊇ X`. Its elementwise action is `embed a`
(`inclMap_toElementMap`). -/
def inclMap (a : V.Element) : ApproximableMap (relSystem a) V where
  rel X Y := a.mem X ∧ V.mem Y ∧ X ⊆ Y
  rel_dom := fun h => h.1
  rel_cod := fun h => h.2.1
  master_rel := ⟨a.master_mem, V.master_mem, subset_rfl⟩
  inter_right := by
    rintro X Y Y' ⟨haX, hVY, hXY⟩ ⟨_, hVY', hXY'⟩
    exact ⟨haX, V.inter_mem hVY hVY' (a.sub haX) (Set.subset_inter hXY hXY'),
      Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' haX' hVY'
    exact ⟨haX', hVY', (hX'X.trans hXY).trans hYY'⟩

/-- The inclusion's elementwise action is `embed a` (Exercise 4.10). -/
theorem inclMap_toElementMap (a : V.Element) (g : (relSystem a).Element) :
    (inclMap a).toElementMap g = embed a g := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hgX, haX, hVY, hXY⟩
    exact ⟨hVY, X, haX, hgX, hXY⟩
  · rintro ⟨hVY, W, haW, hgW, hWY⟩
    exact ⟨W, hgW, haW, hVY, hWY⟩

/-- The inclusion is strict: `ι(⊥) = ⊥`. -/
theorem inclMap_bot (a : V.Element) : (inclMap a).toElementMap (relSystem a).bot = V.bot := by
  rw [inclMap_toElementMap]
  apply Element.ext
  intro Y
  rw [mem_bot]
  constructor
  · rintro ⟨hVY, W, _, hbW, hWY⟩
    rw [mem_bot] at hbW
    rw [hbW] at hWY
    exact Set.Subset.antisymm (V.sub_master hVY) hWY
  · rintro rfl
    exact ⟨V.master_mem, V.master, a.master_mem, (relSystem a).bot.master_mem, subset_rfl⟩

/-- The inclusion intertwines `f'` with `f`: `ι ∘ f' = f ∘ ι` (from
`relMap_toElementMap_embed`). -/
theorem inclMap_intertwine (f : ApproximableMap V V) {a : V.Element} (ha : f.toElementMap a = a)
    (g : (relSystem a).Element) :
    (inclMap a).toElementMap ((relMap f ha).toElementMap g) =
      f.toElementMap ((inclMap a).toElementMap g) := by
  rw [inclMap_toElementMap, inclMap_toElementMap, relMap_toElementMap_embed]

end ApproximableMap

/-! ### Plotkin's uniqueness theorem. -/

open ApproximableMap

universe u

/-- **Exercise 4.11 (Scott 1981, PRG-19) — Plotkin's uniqueness.** Any assignment
`F` of a
fixed-point operator to every domain satisfying (ii) `F_𝒟(f) = f(F_𝒟(f))` and
(iii) the uniformity
law coincides with `fix`: `F_𝒟(f) = fix(f)` for every domain `𝒟` and every `f : 𝒟
→ 𝒟`. -/
theorem fix_unique_of_uniform
    (F : ∀ {β : Type u} (W : NeighborhoodSystem β), ApproximableMap W W → W.Element)
    (hfixed : ∀ {β : Type u} (W : NeighborhoodSystem β) (g : ApproximableMap W W),
      g.toElementMap (F W g) = F W g)
    (huniform : ∀ {β γ : Type u} (W₀ : NeighborhoodSystem β) (W₁ : NeighborhoodSystem γ)
      (g₀ : ApproximableMap W₀ W₀) (g₁ : ApproximableMap W₁ W₁) (h : ApproximableMap W₀ W₁),
      h.toElementMap W₀.bot = W₁.bot →
      (∀ x, h.toElementMap (g₀.toElementMap x) = g₁.toElementMap (h.toElementMap x)) →
      h.toElementMap (F W₀ g₀) = F W₁ g₁)
    {α : Type u} (V : NeighborhoodSystem α) (f : ApproximableMap V V) :
    F V f = f.fixElement := by
  have ha : f.toElementMap f.fixElement = f.fixElement := toElementMap_fixElement f
  -- `F` of the restricted map `f'` is a fixed point of `f'` (by (ii))…
  have hfix' : (relMap f ha).toElementMap (F (relSystem f.fixElement) (relMap f ha)) =
      F (relSystem f.fixElement) (relMap f ha) := hfixed (relSystem f.fixElement) (relMap f ha)
  -- …hence it is the unique fixed point `restrict (fix f) (fix f)` of `f'`
  -- (Exercise 4.10).
  have huniq : F (relSystem f.fixElement) (relMap f ha) =
      restrict f.fixElement f.fixElement (le_refl _) :=
    relMap_unique_fixed f ha _ hfix'
  -- uniformity along the inclusion `ι` transports `F(f')` to `F(f)`.
  have huse := huniform (relSystem f.fixElement) V (relMap f ha) f (inclMap f.fixElement)
    (inclMap_bot f.fixElement) (inclMap_intertwine f ha)
  rw [huniq, inclMap_toElementMap, embed_restrict] at huse
  exact huse.symm

end Domain.Neighborhood
