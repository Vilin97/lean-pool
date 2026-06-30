/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.FunctionSpace

/-!
# Exercise 5.10 (Scott 1981, PRG-19, §5) — the smash product and the strict
function space

> Suppose `𝒟₀` and `𝒟₁` are neighbourhood systems over disjoint sets `Δ₀` and
`Δ₁`. Define the
> *smash product* `𝒟₀ ⊗ 𝒟₁` with neighbourhoods
> `{Δ₀ ∪ Δ₁} ∪ {X ∪ Y ∣ X ∈ 𝒟₀ ∖ {Δ₀} and Y ∈ 𝒟₁ ∖ {Δ₁}}`.
> Show that this *is* a neighbourhood system. Define `(𝒟₀ →⊥ 𝒟₁)` so that `|𝒟₀ →⊥
𝒟₁|` consists
> exactly of the *strict functions*. By introducing appropriate combinators, show
that
> `(𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))` and `((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂)` are isomorphic.

We model the disjoint union of token sets by the **sum type** `α ⊕ β`, exactly as
for the ordinary
product (`Domain/Neighborhood/Product.lean`), reusing `prodNbhd X Y = Sum.inl '' X
∪ Sum.inr '' Y`
and its algebra (`prodNbhd_inter`, `prodNbhd_subset_iff`, `prodNbhd_injective`).

This file is organised as follows.

* **The smash product** `smash V₀ V₁` (`§ smash`): a genuine neighbourhood system.
The neighbourhoods
  are the master `Δ₀ ∪ Δ₁` together with the *proper* product neighbourhoods `X ∪
  Y` whose factors are
  both *proper* (`X ≠ Δ₀`, `Y ≠ Δ₁`). Closure under consistent intersection is the
  new content: the
  consistency witness rules out the degenerate cases, and a proper factor stays
  proper under
  intersection.
* **The smash collapses bottoms** (`§ elements`): the element `smashPair x y` (the
strict pairing) and
  the order-isomorphism showing `|𝒟₀ ⊗ 𝒟₁|` is the *smash* of the pointed domains
  — every element is
  either `⊥` or a pair `⟨x, y⟩` of *non-`⊥`* elements.
* **The strict function space** `strictFun V₀ V₁` (`§ strict`): a neighbourhood
system whose elements
  are exactly the *strict* approximable maps (`IsStrict f`, i.e. `f(⊥) = ⊥`). We
  realise it as the
  function space generated only by step neighbourhoods `[X, Y]` with *proper*
  input `X`, and prove the
  representation `strictFunEquiv : |𝒟₀ →⊥ 𝒟₁| ≃o {f ∣ IsStrict f}`.
* **The adjunction** (`§ iso`): the "appropriate combinators" Scott asks for — a
strict curry
  `smashCurryMap` and strict uncurry `smashUncurryMap` — assembled into the
  order-isomorphism
  `smashCurryEquiv : ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) ≃o (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))`. The decisive
  computation is
  `section_uncurry_rel`: `g(⟨x, y⟩⊗) = curry⊥(g)(x)(y)`, with the boundary (a
  master factor) handled
  by strictness — exactly the bottom-gluing the smash performs.

The *data* (`smash`, `strictFun`, `smashCurryMap`, `smashUncurryMap`) and the
representation
`strictFunEquiv` are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`);
`Classical.choice`
enters only the `smashCurryEquiv` *proof*, through the genuinely-classical `X =
Δ₀?` / `Y = Δ₁?`
boundary case analysis.
-/

namespace Domain.Neighborhood.Exercise510

open Domain.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

/-! ### The smash product `𝒟₀ ⊗ 𝒟₁`. -/

/-- A *proper* product neighbourhood of the smash: `X ∪ Y` with `X ∈ 𝒟₀ ∖ {Δ₀}`
and
`Y ∈ 𝒟₁ ∖ {Δ₁}` (both factors strictly below their masters). -/
def SmashProper (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (W : Set (α ⊕ β)) : Prop :=
  ∃ X Y, V₀.mem X ∧ X ≠ V₀.master ∧ V₁.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A neighbourhood that is `⊆ Δ₀` and equals `Δ₀` exactly when it contains `Δ₀`.
A proper factor
`X ≠ Δ₀` stays proper after intersecting with anything: `X ∩ X' ≠ Δ₀`. -/
theorem inter_ne_master_left {X X' : Set α} (hX : V₀.mem X) (hXne : X ≠ V₀.master) :
    X ∩ X' ≠ V₀.master := by
  intro h
  apply hXne
  refine Set.Subset.antisymm (V₀.sub_master hX) ?_
  rw [← h]; exact Set.inter_subset_left

theorem inter_ne_master_right {Y Y' : Set β} (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) :
    Y ∩ Y' ≠ V₁.master :=
  inter_ne_master_left (V₀ := V₁) hY hYne

/-- **Exercise 5.10 (Scott 1981, PRG-19) — the smash product `𝒟₀ ⊗ 𝒟₁`.**
Neighbourhoods are the
master `Δ₀ ∪ Δ₁` together with the *proper* product neighbourhoods `X ∪ Y` (both
factors proper).

*This is a neighbourhood system.* Condition (i) is the master clause. Condition
(ii) is the new
content: given two smash neighbourhoods with a consistency witness `Z`,

* if either is the master, the intersection collapses to the other (since `X ⊆
Δ₀`, `Y ⊆ Δ₁`);
* if both are proper, `Z` cannot be the master (that would force a factor to be
`Δ₀`/`Δ₁`), so `Z` is
  a *proper* `U ∪ V`; `U ⊆ X ∩ X'` and `V ⊆ Y ∩ Y'` then witness `X ∩ X' ∈ 𝒟₀`, `Y
  ∩ Y' ∈ 𝒟₁`, both
  still proper (`inter_ne_master_*`). -/
def smash (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : NeighborhoodSystem (α ⊕ β) where
  mem W := W = prodNbhd V₀.master V₁.master ∨ SmashProper V₀ V₁ W
  master := prodNbhd V₀.master V₁.master
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' Z (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hZ hZsub
    · -- W = master
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        refine ⟨X', Y', hX', hX'ne, hY', hY'ne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_right.mpr (V₀.sub_master hX'),
          Set.inter_eq_right.mpr (V₁.sub_master hY')]
    · -- W = X ∪ Y proper
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        refine ⟨X, Y, hX, hXne, hY, hYne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master hX),
          Set.inter_eq_left.mpr (V₁.sub_master hY)]
      · -- both proper: use the witness Z
        right
        rw [prodNbhd_inter] at hZsub ⊢
        rcases hZ with hZeq | ⟨U, V, hU, _, hV, _, rfl⟩
        · -- Z = master is impossible
          exfalso
          rw [hZeq] at hZsub
          obtain ⟨hΔ₀, _⟩ := prodNbhd_subset_iff.mp hZsub
          exact hXne (Set.Subset.antisymm (V₀.sub_master hX) (hΔ₀.trans Set.inter_subset_left))
        · obtain ⟨hUsub, hVsub⟩ := prodNbhd_subset_iff.mp hZsub
          refine ⟨X ∩ X', Y ∩ Y', ?_, ?_, ?_, ?_, rfl⟩
          · exact V₀.inter_mem hX hX' hU hUsub
          · exact inter_ne_master_left hX hXne
          · exact V₁.inter_mem hY hY' hV hVsub
          · exact inter_ne_master_right hY hYne
  sub_master := by
    rintro W (rfl | ⟨X, Y, hX, _, hY, _, rfl⟩)
    · exact subset_rfl
    · exact prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩

@[simp] theorem smash_master :
    (smash V₀ V₁).master = prodNbhd V₀.master V₁.master := rfl

theorem smash_mem_iff {W : Set (α ⊕ β)} :
    (smash V₀ V₁).mem W ↔
      W = prodNbhd V₀.master V₁.master ∨ SmashProper V₀ V₁ W := Iff.rfl

/-- A proper product neighbourhood is a neighbourhood of the smash. -/
theorem smash_mem_proper {X : Set α} {Y : Set β} (hX : V₀.mem X) (hXne : X ≠ V₀.master)
    (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) : (smash V₀ V₁).mem (prodNbhd X Y) :=
  Or.inr ⟨X, Y, hX, hXne, hY, hYne, rfl⟩

/-- `⊥` of the smash is exactly `{Δ₀ ∪ Δ₁}`. -/
theorem smash_mem_bot {W : Set (α ⊕ β)} :
    (smash V₀ V₁).bot.mem W ↔ W = prodNbhd V₀.master V₁.master := by
  rw [NeighborhoodSystem.mem_bot, smash_master]

/-! ### The smash collapses bottoms: the strict pairing `⟨x, y⟩⊗`.

The smash identifies all elements that have a `⊥` in either coordinate. We realise
this by the *strict
pairing* `smashPair x y`: when both `x, y` are non-`⊥` it is the genuine pair `⟨x,
y⟩`, and when either
is `⊥` it collapses to `⊥` (`smashPair_eq_bot_iff`). Every element of `|𝒟₀ ⊗ 𝒟₁|`
arises this way. -/

/-- The *strict pairing* `⟨x, y⟩⊗`: the filter generated by the proper product
neighbourhoods
`X ∪ Y` with `X ∈ x ∖ {Δ₀}`, `Y ∈ y ∖ {Δ₁}` (plus the master). When either `x` or
`y` is `⊥` (i.e.
contains only its master), this collapses to `⊥`. -/
def smashPair (x : V₀.Element) (y : V₁.Element) : (smash V₀ V₁).Element where
  mem W := W = prodNbhd V₀.master V₁.master ∨
    ∃ X Y, x.mem X ∧ X ≠ V₀.master ∧ y.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y
  sub := by
    rintro W (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩)
    · exact (smash V₀ V₁).master_mem
    · exact smash_mem_proper (x.sub hX) hXne (y.sub hY) hYne
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW'
    · rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        exact ⟨X', Y', hX', hX'ne, hY', hY'ne, by
          rw [prodNbhd_inter, Set.inter_eq_right.mpr (V₀.sub_master (x.sub hX')),
            Set.inter_eq_right.mpr (V₁.sub_master (y.sub hY'))]⟩
    · rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        exact ⟨X, Y, hX, hXne, hY, hYne, by
          rw [prodNbhd_inter, Set.inter_eq_left.mpr (V₀.sub_master (x.sub hX)),
            Set.inter_eq_left.mpr (V₁.sub_master (y.sub hY))]⟩
      · right
        refine ⟨X ∩ X', Y ∩ Y', x.inter_mem hX hX', inter_ne_master_left (x.sub hX) hXne,
          y.inter_mem hY hY', inter_ne_master_right (y.sub hY) hYne, ?_⟩
        rw [prodNbhd_inter]
  up_mem := by
    rintro W W' (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hsub
    · left
      exact Set.Subset.antisymm ((smash V₀ V₁).sub_master hW') hsub
    · rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rfl
      · obtain ⟨hXX', hYY'⟩ := prodNbhd_subset_iff.mp hsub
        right
        exact ⟨X', Y', x.up_mem hX hX' hXX', hX'ne, y.up_mem hY hY' hYY', hY'ne, rfl⟩

@[simp] theorem mem_smashPair {x : V₀.Element} {y : V₁.Element} {W : Set (α ⊕ β)} :
    (smashPair x y).mem W ↔ W = prodNbhd V₀.master V₁.master ∨
      ∃ X Y, x.mem X ∧ X ≠ V₀.master ∧ y.mem Y ∧ Y ≠ V₁.master ∧ W = prodNbhd X Y := Iff.rfl

/-- An element is `⊥` iff every neighbourhood it contains is the master: `x ≠ ⊥`
exactly when `x`
contains a *proper* neighbourhood. -/
theorem exists_proper_of_ne_bot {x : V₀.Element} (hx : x ≠ V₀.bot) :
    ∃ X, x.mem X ∧ X ≠ V₀.master := by
  by_contra hc
  refine hx (le_antisymm (fun W hW => ?_) (V₀.bot_le x))
  rw [NeighborhoodSystem.mem_bot]
  by_contra hWne
  exact hc ⟨W, hW, hWne⟩

theorem eq_bot_of_no_proper {x : V₀.Element} (hx : ∀ X, x.mem X → X = V₀.master) :
    x = V₀.bot :=
  le_antisymm (fun W hW => by rw [NeighborhoodSystem.mem_bot]; exact hx W hW)
    (V₀.bot_le x)

/-- The strict pairing is `⊥` iff one of the components is `⊥`: the smash glues
`(⊥, y)` and
`(x, ⊥)`
to a single bottom. -/
theorem smashPair_eq_bot_iff {x : V₀.Element} {y : V₁.Element} :
    smashPair x y = (smash V₀ V₁).bot ↔ x = V₀.bot ∨ y = V₁.bot := by
  constructor
  · intro h
    by_contra hcon
    obtain ⟨hx, hy⟩ := not_or.mp hcon
    obtain ⟨X, hxX, hXne⟩ := exists_proper_of_ne_bot hx
    obtain ⟨Y, hyY, hYne⟩ := exists_proper_of_ne_bot hy
    -- `prodNbhd X Y` is a proper member of `smashPair x y`, but `⊥` contains only
    -- the master.
    have hmem : (smashPair x y).mem (prodNbhd X Y) :=
      Or.inr ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩
    rw [h, smash_mem_bot] at hmem
    obtain ⟨hX, _⟩ := prodNbhd_injective hmem
    exact hXne hX
  · intro h
    apply eq_bot_of_no_proper
    rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
    · rfl
    · exfalso
      rcases h with hx | hy
      · rw [hx, NeighborhoodSystem.mem_bot] at hxX; exact hXne hxX
      · rw [hy, NeighborhoodSystem.mem_bot] at hyY; exact hYne hyY

/-- The strict pairing is monotone in both arguments. -/
theorem smashPair_mono {x x' : V₀.Element} {y y' : V₁.Element} (hx : x ≤ x') (hy : y ≤ y') :
    smashPair x y ≤ smashPair x' y' := by
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨X, Y, hx X hxX, hXne, hy Y hyY, hYne, rfl⟩

/-- The principal filter of the master is `⊥`. -/
theorem principal_master_eq_bot {X : Set α} (hX : V₀.mem X) (hXm : X = V₀.master) :
    V₀.principal hX = V₀.bot := by
  subst hXm; rfl

/-- A `⊥` left factor collapses the strict pairing to `⊥` (choice-free). -/
theorem smashPair_bot_left (y : V₁.Element) : smashPair V₀.bot y = (smash V₀ V₁).bot := by
  apply eq_bot_of_no_proper
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · rfl
  · rw [NeighborhoodSystem.mem_bot] at hxX; exact absurd hxX hXne

/-- A `⊥` right factor collapses the strict pairing to `⊥` (choice-free). -/
theorem smashPair_bot_right (x : V₀.Element) : smashPair x V₁.bot = (smash V₀ V₁).bot := by
  apply eq_bot_of_no_proper
  rintro W (rfl | ⟨X, Y, hxX, hXne, hyY, hYne, rfl⟩)
  · rfl
  · rw [NeighborhoodSystem.mem_bot] at hyY; exact absurd hyY hYne

/-! ### The strict function space `(𝒟₀ →⊥ 𝒟₁)`.

A map `f : 𝒟₀ → 𝒟₁` is **strict** when `f(⊥) = ⊥`. In relational terms (since
`f(⊥)` is the filter
`{Y ∣ Δ₀ f Y}`), this says `f` relates the master input `Δ₀` only to the master
output `Δ₁`:
`Δ₀ f Y ⟹ Y = Δ₁`.

We realise `(𝒟₀ →⊥ 𝒟₁)` as the function space whose *tokens* are the **strict**
approximable maps and
whose neighbourhoods are the non-empty finite intersections of step sets `[X, Y] =
{f ∣ X f Y}`. The
crucial point — making `|𝒟₀ →⊥ 𝒟₁|` consist *exactly* of the strict functions — is
automatic: a step
`[Δ₀, Y]` with `Y ≠ Δ₁` contains *no* strict map, so it is empty, hence never a
neighbourhood; thus no
filter can force a non-strict value at `⊥`. The representation `strictFunEquiv`
then mirrors
Theorem 3.10. -/

/-- **A map is *strict* when `f(⊥) = ⊥`.** Relationally: `f` sends the master
input only to the
master
output. -/
def IsStrict (f : ApproximableMap V₀ V₁) : Prop :=
  ∀ ⦃Y⦄, f.rel V₀.master Y → Y = V₁.master

/-- Strictness is exactly `f(⊥) = ⊥`. -/
theorem isStrict_iff_apply_bot {f : ApproximableMap V₀ V₁} :
    IsStrict f ↔ f.toElementMap V₀.bot = V₁.bot := by
  constructor
  · intro h
    apply Element.ext
    intro Y
    rw [NeighborhoodSystem.mem_bot]
    constructor
    · rintro ⟨X, hX, hrel⟩
      rw [NeighborhoodSystem.mem_bot] at hX; subst hX
      exact h hrel
    · rintro rfl
      exact ⟨V₀.master, V₀.bot.master_mem, f.master_rel⟩
  · intro h Y hrel
    have : (f.toElementMap V₀.bot).mem Y := ⟨V₀.master, V₀.bot.master_mem, hrel⟩
    rw [h, NeighborhoodSystem.mem_bot] at this
    exact this

/-- Strictness is downward closed: a map below a strict map is strict. -/
theorem IsStrict.mono {f g : ApproximableMap V₀ V₁} (hf : IsStrict f) (hgf : g ≤ f) : IsStrict g :=
  fun _ hrel => hf (hgf _ _ hrel)

/-- The constant map at `⊥` is strict. -/
theorem isStrict_constBot : IsStrict (constMap V₀ (V₁.bot)) := by
  rintro Y ⟨_, hY⟩
  rwa [NeighborhoodSystem.mem_bot] at hY

/-- The identity is strict. -/
theorem isStrict_idMap : IsStrict (idMap V₀) := by
  rintro Y ⟨_, hY, hsub⟩
  exact Set.Subset.antisymm (V₀.sub_master hY) hsub

/-- The strict maps `𝒟₀ →⊥ 𝒟₁`, as a subtype carrying the inherited approximation
order. -/
abbrev StrictMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :=
  {f : ApproximableMap V₀ V₁ // IsStrict f}

/-- A step set among strict maps: `[X, Y] = {f strict ∣ X f Y}`. -/
def sstep (X : Set α) (Y : Set β) : Set (StrictMap V₀ V₁) := {f | f.1.rel X Y}

@[simp] theorem mem_sstep {X : Set α} {Y : Set β} {f : StrictMap V₀ V₁} :
    f ∈ sstep X Y ↔ f.1.rel X Y := Iff.rfl

/-- A finite intersection of strict step sets. -/
def sstepFun (L : List (Set α × Set β)) : Set (StrictMap V₀ V₁) :=
  {f | ∀ p ∈ L, f.1.rel p.1 p.2}

@[simp] theorem mem_sstepFun {L : List (Set α × Set β)} {f : StrictMap V₀ V₁} :
    f ∈ sstepFun L ↔ ∀ p ∈ L, f.1.rel p.1 p.2 := Iff.rfl

@[simp] theorem sstepFun_nil : (sstepFun [] : Set (StrictMap V₀ V₁)) = Set.univ := by
  ext f; simp

theorem sstepFun_cons (p : Set α × Set β) (L : List (Set α × Set β)) :
    (sstepFun (p :: L) : Set (StrictMap V₀ V₁)) = sstep p.1 p.2 ∩ sstepFun L := by
  ext f
  simp only [mem_sstepFun, List.mem_cons, Set.mem_inter_iff, mem_sstep]
  constructor
  · intro h; exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨hp, hrest⟩ q (rfl | hq)
    · exact hp
    · exact hrest q hq

theorem sstepFun_append (L L' : List (Set α × Set β)) :
    (sstepFun (L ++ L') : Set (StrictMap V₀ V₁)) = sstepFun L ∩ sstepFun L' := by
  ext f
  simp only [mem_sstepFun, List.mem_append, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨hL, hL'⟩ p (hp | hp)
    · exact hL p hp
    · exact hL' p hp

theorem sstepFun_singleton (X : Set α) (Y : Set β) :
    (sstepFun [(X, Y)] : Set (StrictMap V₀ V₁)) = sstep X Y := by
  rw [sstepFun_cons, sstepFun_nil, Set.inter_univ]

/-- `[Δ₀, Δ₁] = |𝒟₀ →⊥ 𝒟₁|`: every (strict) map relates the masters. -/
@[simp] theorem sstep_master_eq :
    (sstep V₀.master V₁.master : Set (StrictMap V₀ V₁)) = Set.univ := by
  ext f; simpa using f.1.master_rel

theorem sstep_inter_right {X : Set α} {Y Y' : Set β} (hY : V₁.mem Y) (hY' : V₁.mem Y') :
    (sstep X Y ∩ sstep X Y' : Set (StrictMap V₀ V₁)) = sstep X (Y ∩ Y') := by
  ext f
  simp only [Set.mem_inter_iff, mem_sstep]
  constructor
  · rintro ⟨h, h'⟩; exact f.1.inter_right h h'
  · intro h
    exact ⟨f.1.mono h subset_rfl Set.inter_subset_left (f.1.rel_dom h) hY,
           f.1.mono h subset_rfl Set.inter_subset_right (f.1.rel_dom h) hY'⟩

theorem sstep_subset {X X' : Set α} {Y Y' : Set β} (hX' : V₀.mem X') (hY' : V₁.mem Y')
    (hX'X : X' ⊆ X) (hYY' : Y ⊆ Y') : (sstep X Y : Set (StrictMap V₀ V₁)) ⊆ sstep X' Y' := by
  intro f hf
  exact f.1.mono hf hX'X hYY' hX' hY'

/-- **Exercise 5.10 — the strict function space `(𝒟₀ →⊥ 𝒟₁)`.** Tokens are the
strict approximable
maps; neighbourhoods are non-empty finite intersections of step sets. -/
def strictFun (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    NeighborhoodSystem (StrictMap V₀ V₁) where
  mem W := (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = sstepFun L)
    ∧ W.Nonempty
  master := Set.univ
  master_mem := ⟨⟨[], by simp, sstepFun_nil.symm⟩,
    ⟨⟨constMap V₀ V₁.bot, isStrict_constBot⟩, Set.mem_univ _⟩⟩
  inter_mem := by
    rintro W W' Z ⟨⟨L, hL, rfl⟩, _⟩ ⟨⟨L', hL', rfl⟩, _⟩ ⟨_, hZne⟩ hZsub
    refine ⟨⟨L ++ L', ?_, (sstepFun_append _ _).symm⟩, hZne.mono hZsub⟩
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hL p h
    · exact hL' p h
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem strictFun_master : (strictFun V₀ V₁).master = Set.univ := rfl

theorem strictFun_mem_iff {W : Set (StrictMap V₀ V₁)} :
    (strictFun V₀ V₁).mem W ↔
      (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = sstepFun L)
        ∧ W.Nonempty := Iff.rfl

/-- A step set is a neighbourhood as soon as it has a (strict) witness. -/
theorem sstep_mem_of_mem {g : StrictMap V₀ V₁} {X : Set α} {Y : Set β} (h : g.1.rel X Y) :
    (strictFun V₀ V₁).mem (sstep X Y) := by
  refine ⟨⟨[(X, Y)], ?_, (sstepFun_singleton X Y).symm⟩, ⟨g, h⟩⟩
  intro p hp; rw [List.mem_singleton] at hp; subst hp
  exact ⟨g.1.rel_dom h, g.1.rel_cod h⟩

/-- Intersection of two neighbourhoods, when non-empty, is again one. -/
theorem strictFun_mem_inter {W W' : Set (StrictMap V₀ V₁)}
    (hW : (strictFun V₀ V₁).mem W) (hW' : (strictFun V₀ V₁).mem W') (hne : (W ∩ W').Nonempty) :
    (strictFun V₀ V₁).mem (W ∩ W') := by
  obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
  obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
  refine ⟨⟨L ++ L', ?_, (sstepFun_append _ _).symm⟩, hne⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hL' p h

theorem sstepFun_up_closed {L : List (Set α × Set β)} {f f' : StrictMap V₀ V₁}
    (hf : f ∈ sstepFun L) (hff' : f ≤ f') : f' ∈ sstepFun L := by
  intro p hp
  exact hff' p.1 p.2 (hf p hp)

theorem strictFun_mem_up_closed {W : Set (StrictMap V₀ V₁)} (hW : (strictFun V₀ V₁).mem W)
    {f f' : StrictMap V₀ V₁} (hf : f ∈ W) (hff' : f ≤ f') : f' ∈ W := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hW
  exact sstepFun_up_closed hf hff'

/-- The generation lemma: a filter contains `sstepFun L` iff it contains each step
`[Xᵢ, Yᵢ]`. -/
theorem mem_sstepFun_iff (φ : (strictFun V₀ V₁).Element) {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    φ.mem (sstepFun L) ↔ ∀ p ∈ L, φ.mem (sstep p.1 p.2) := by
  induction L with
  | nil => simp only [sstepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
           exact φ.master_mem
  | cons p L ih =>
    rw [sstepFun_cons]
    have hLtail : ∀ q ∈ L, V₀.mem q.1 ∧ V₁.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      obtain ⟨g, hg⟩ := (φ.sub hmem).2
      have hstep : φ.mem (sstep p.1 p.2) :=
        φ.up_mem hmem (sstep_mem_of_mem (g := g) (hg.1)) Set.inter_subset_left
      have hne : (sstep p.1 p.2 ∩ sstepFun L).Nonempty := (φ.sub hmem).2
      have htail : φ.mem (sstepFun L) :=
        φ.up_mem hmem ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩ Set.inter_subset_right
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : φ.mem (sstep p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : φ.mem (sstepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact φ.inter_mem hstep htail

/-- **The strict map represented by a filter.** `X (toStrictMap φ) Y ↔ [X, Y] ∈
φ`. It is *strict*
because the step `[Δ₀, Y]` with `Y ≠ Δ₁` is empty (no strict map relates `Δ₀` to a
proper output),
hence not a neighbourhood, so it cannot belong to `φ`. -/
def toStrictMap (φ : (strictFun V₀ V₁).Element) : StrictMap V₀ V₁ :=
  ⟨{ rel := fun X Y => φ.mem (sstep X Y)
     rel_dom := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.1.rel_dom hf
     rel_cod := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.1.rel_cod hf
     master_rel := by
       show φ.mem (sstep V₀.master V₁.master); rw [sstep_master_eq]; exact φ.master_mem
     inter_right := by
       intro X Y Y' h h'
       obtain ⟨f, hf⟩ := (φ.sub h).2
       obtain ⟨f', hf'⟩ := (φ.sub h').2
       have hY : V₁.mem Y := f.1.rel_cod hf
       have hY' : V₁.mem Y' := f'.1.rel_cod hf'
       change φ.mem (sstep X (Y ∩ Y'))
       rw [← sstep_inter_right hY hY']
       exact φ.inter_mem h h'
     mono := by
       intro X X' Y Y' h hX'X hYY' hX' hY'
       obtain ⟨g, hg⟩ := (φ.sub h).2
       have hg' : g.1.rel X' Y' := g.1.mono hg hX'X hYY' hX' hY'
       change φ.mem (sstep X' Y')
       exact φ.up_mem h (sstep_mem_of_mem (g := g) hg') (sstep_subset hX' hY' hX'X hYY') },
   by
     intro Y h
     obtain ⟨g, hg⟩ := (φ.sub h).2
     exact g.2 hg⟩

@[simp] theorem toStrictMap_rel {φ : (strictFun V₀ V₁).Element} {X : Set α} {Y : Set β} :
    (toStrictMap φ).1.rel X Y ↔ φ.mem (sstep X Y) := Iff.rfl

/-- **The filter `f̂ = {F ∣ f ∈ F}` of a strict map.** -/
def toStrictFilter (f : StrictMap V₀ V₁) : (strictFun V₀ V₁).Element where
  mem W := (strictFun V₀ V₁).mem W ∧ f ∈ W
  sub h := h.1
  master_mem := ⟨(strictFun V₀ V₁).master_mem, Set.mem_univ f⟩
  inter_mem := by
    rintro W W' ⟨hW, hfW⟩ ⟨hW', hfW'⟩
    exact ⟨strictFun_mem_inter hW hW' ⟨f, Set.mem_inter hfW hfW'⟩, Set.mem_inter hfW hfW'⟩
  up_mem := by rintro W W' ⟨hW, hfW⟩ hW' hWW'; exact ⟨hW', hWW' hfW⟩

@[simp] theorem mem_toStrictFilter {f : StrictMap V₀ V₁} {W : Set (StrictMap V₀ V₁)} :
    (toStrictFilter f).mem W ↔ (strictFun V₀ V₁).mem W ∧ f ∈ W := Iff.rfl

/-- **Exercise 5.10 — the strict function space is complete.** `|𝒟₀ →⊥ 𝒟₁|` is
order-isomorphic to
the strict approximable maps `𝒟₀ → 𝒟₁`. -/
def strictFunEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (strictFun V₀ V₁).Element ≃o StrictMap V₀ V₁ where
  toFun := toStrictMap
  invFun := toStrictFilter
  left_inv φ := by
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hWmem, hfW⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
      exact (mem_sstepFun_iff φ hL).mpr (fun p hp => hfW p hp)
    · intro hW
      refine ⟨φ.sub hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      intro p hp
      exact (mem_sstepFun_iff φ hL).mp hW p hp
  right_inv f := by
    apply Subtype.ext
    apply ApproximableMap.ext
    intro X Y
    constructor
    · rintro ⟨_, hf⟩; exact hf
    · intro hf; exact ⟨sstep_mem_of_mem (g := f) hf, hf⟩
  map_rel_iff' := by
    intro φ φ'
    constructor
    · intro h W hW
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      refine (mem_sstepFun_iff φ' hL).mpr (fun p hp => ?_)
      exact h p.1 p.2 ((mem_sstepFun_iff φ hL).mp hW p hp)
    · intro h X Y hrel
      exact h _ hrel

/-! ### The adjunction `(𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂)) ≅ ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂)`.

The smash product is *left adjoint* to the strict function space: strict maps out
of a smash product
are the same as strict maps into a strict function space. We realise the iso with
the "appropriate
combinators" Scott asks for — a *strict curry* and *strict uncurry* — connected by
the computation
`g(⟨x, y⟩⊗) = (curry g)(x)(y)`.

The decisive computation is `smashPair_principal_apply`: for *proper* `X, Y`,
applying `g` to the
strict pairing of the principal elements is the same as `g` relating the proper
neighbourhood
`X ∪ Y`. At the bottom (a master factor) the strict pairing collapses to `⊥`,
where strictness forces
the master output — exactly the gluing the smash performs. -/

variable {V₂ : NeighborhoodSystem γ}

/-- Every smash neighbourhood is a product neighbourhood `A ∪ B` (the master is
`Δ₀ ∪ Δ₁`). -/
theorem smash_mem_prodNbhd_form {W : Set (α ⊕ β)} (hW : (smash V₀ V₁).mem W) :
    ∃ A B, V₀.mem A ∧ V₁.mem B ∧ W = prodNbhd A B := by
  rcases hW with rfl | ⟨X, Y, hX, _, hY, _, rfl⟩
  · exact ⟨_, _, V₀.master_mem, V₁.master_mem, rfl⟩
  · exact ⟨X, Y, hX, hY, rfl⟩

/-- **The key computation.** For *proper* `X, Y`, `g(⟨↑X, ↑Y⟩⊗)` contains `Z` iff
`g` relates the
proper neighbourhood `X ∪ Y` to `Z`. (Coarser members of the strict pairing are
absorbed by
monotonicity; the master member needs only that `X ∪ Y ⊆ Δ₀ ∪ Δ₁`.) -/
theorem smashPair_principal_apply (g : ApproximableMap (smash V₀ V₁) V₂)
    {X : Set α} {Y : Set β} (hX : V₀.mem X) (hXne : X ≠ V₀.master)
    (hY : V₁.mem Y) (hYne : Y ≠ V₁.master) {Z : Set γ} :
    (g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY))).mem Z
      ↔ g.rel (prodNbhd X Y) Z := by
  constructor
  · rintro ⟨W, hW, hrel⟩
    rcases hW with rfl | ⟨A, B, ⟨_, hXA⟩, _, ⟨_, hYB⟩, _, rfl⟩
    · exact g.mono hrel (prodNbhd_subset_iff.mpr ⟨V₀.sub_master hX, V₁.sub_master hY⟩) subset_rfl
        (smash_mem_proper hX hXne hY hYne) (g.rel_cod hrel)
    · exact g.mono hrel (prodNbhd_subset_iff.mpr ⟨hXA, hYB⟩) subset_rfl
        (smash_mem_proper hX hXne hY hYne) (g.rel_cod hrel)
  · intro hrel
    exact ⟨prodNbhd X Y, Or.inr ⟨X, Y, ⟨hX, subset_rfl⟩, hXne, ⟨hY, subset_rfl⟩, hYne, rfl⟩, hrel⟩

/-- The `X`-section of `g : 𝒟₀ ⊗ 𝒟₁ → 𝒟₂`, as a map `𝒟₁ → 𝒟₂`: `y ↦ g(⟨↑X, y⟩⊗)`.
Built with
Exercise 2.8's `ofMono` from its values on principal inputs. -/
def smashSection (g : ApproximableMap (smash V₀ V₁) V₂) {X : Set α} (hX : V₀.mem X) :
    ApproximableMap V₁ V₂ :=
  ofMono (fun Y hY => g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY)))
    (by
      intro Y Y' hY hY' hY'Y
      exact toElementMap_mono g (smashPair_mono le_rfl ((V₁.principal_le_iff hY hY').mpr hY'Y)))

theorem smashSection_rel {g : ApproximableMap (smash V₀ V₁) V₂} {X : Set α} (hX : V₀.mem X)
    {Y : Set β} {Z : Set γ} :
    (smashSection g hX).rel Y Z ↔
      ∃ hY : V₁.mem Y, (g.toElementMap (smashPair (V₀.principal hX) (V₁.principal hY))).mem Z :=
  Iff.rfl

/-- The section is monotone in the neighbourhood `X` (a smaller input gives a
larger section). -/
theorem smashSection_mono {g : ApproximableMap (smash V₀ V₁) V₂} {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) :
    smashSection g hX ≤ smashSection g hX' := by
  intro Y Z hrel
  obtain ⟨hY, hmem⟩ := hrel
  exact ⟨hY, toElementMap_mono g
    (smashPair_mono ((V₀.principal_le_iff hX hX').mpr hX'X) le_rfl) Z hmem⟩

/-- The section of a *strict* `g` is itself strict: `g(⟨↑X, ⊥⟩⊗) = g(⊥) = ⊥`. -/
theorem isStrict_smashSection {g : ApproximableMap (smash V₀ V₁) V₂} (hg : IsStrict g)
    {X : Set α} (hX : V₀.mem X) : IsStrict (smashSection g hX) := by
  rw [isStrict_iff_apply_bot, smashSection,
    show (V₁.bot) = V₁.principal V₁.master_mem from rfl, toElementMap_ofMono_principal,
    show smashPair (V₀.principal hX) (V₁.principal V₁.master_mem) = (smash V₀ V₁).bot from
      smashPair_bot_right _]
  exact isStrict_iff_apply_bot.mp hg

/-- The generation lemma for maps into the strict function space: `X h
(⋂ᵢ[Yᵢ,Zᵢ])` iff
`X h [Yᵢ,Zᵢ]` for all `i`. -/
theorem rel_sstepFun_iff (h : ApproximableMap V₀ (strictFun V₁ V₂)) {X : Set α} (hX : V₀.mem X)
    {L : List (Set β × Set γ)} (hL : ∀ p ∈ L, V₁.mem p.1 ∧ V₂.mem p.2) :
    h.rel X (sstepFun L) ↔ ∀ p ∈ L, h.rel X (sstep p.1 p.2) := by
  induction L with
  | nil =>
    simp only [sstepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    change h.rel X (strictFun V₁ V₂).master
    exact h.rel_master hX
  | cons p L ih =>
    rw [sstepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₁.mem q.1 ∧ V₂.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.rel_cod hmem)).2
      have hstep : h.rel X (sstep p.1 p.2) :=
        h.mono hmem subset_rfl Set.inter_subset_left hX (sstep_mem_of_mem (g := f) (hf.1))
      have hne : (sstep p.1 p.2 ∩ sstepFun L).Nonempty := (h.rel_cod hmem).2
      have htail : h.rel X (sstepFun L) :=
        h.mono hmem subset_rfl Set.inter_subset_right hX
          ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : h.rel X (sstep p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : h.rel X (sstepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact h.inter_right hstep htail

/-- **Strict curry combinator.** `curry⊥ : ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) → (𝒟₀ →⊥ (𝒟₁ →⊥
𝒟₂))`, sending `g`
to `x ↦ (y ↦ g(⟨x, y⟩⊗))`. -/
def smashCurryMap (g : StrictMap (smash V₀ V₁) V₂) : StrictMap V₀ (strictFun V₁ V₂) :=
  ⟨{ rel := fun X N => ∃ hX : V₀.mem X, (strictFun V₁ V₂).mem N ∧
       (⟨smashSection g.1 hX, isStrict_smashSection g.2 hX⟩ : StrictMap V₁ V₂) ∈ N
     rel_dom := fun ⟨hX, _⟩ => hX
     rel_cod := fun ⟨_, hN, _⟩ => hN
     master_rel := ⟨V₀.master_mem, (strictFun V₁ V₂).master_mem, Set.mem_univ _⟩
     inter_right := by
       rintro X N N' ⟨hX, hN, hmem⟩ ⟨_, hN', hmem'⟩
       exact ⟨hX, strictFun_mem_inter hN hN' ⟨_, hmem, hmem'⟩, Set.mem_inter hmem hmem'⟩
     mono := by
       rintro X X' N N' ⟨hX, hN, hmem⟩ hX'X hNN' hX' hN'
       refine ⟨hX', hN', strictFun_mem_up_closed hN' (hNN' hmem) ?_⟩
       exact Subtype.coe_le_coe.mp (smashSection_mono hX hX' hX'X) },
  by
    rintro N ⟨hΔ₀, hN, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    have hall : ∀ p ∈ L, p.2 = V₂.master := by
      intro p hp
      have hpr : (smashSection g.1 hΔ₀).rel p.1 p.2 := hmem p hp
      rw [smashSection_rel] at hpr
      obtain ⟨hp1, hpmem⟩ := hpr
      have hbot : smashPair (V₀.principal hΔ₀) (V₁.principal hp1) = (smash V₀ V₁).bot := by
        rw [principal_master_eq_bot hΔ₀ rfl]; exact smashPair_bot_left _
      rw [hbot, isStrict_iff_apply_bot.mp g.2, NeighborhoodSystem.mem_bot] at hpmem
      exact hpmem
    apply Set.eq_univ_of_forall
    intro f q hq
    rw [hall q hq]
    exact (f.1).rel_master (hL q hq).1⟩

/-- **Strict uncurry combinator.** `uncurry⊥ : (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂)) → ((𝒟₀ ⊗ 𝒟₁) →⊥
𝒟₂)`,
`X ∪ Y (uncurry⊥ h) Z ↔ X h [Y, Z]`. -/
def smashUncurryMap (h : StrictMap V₀ (strictFun V₁ V₂)) : StrictMap (smash V₀ V₁) V₂ :=
  ⟨{ rel := fun W Z => (smash V₀ V₁).mem W ∧ h.1.rel (Sum.inl ⁻¹' W) (sstep (Sum.inr ⁻¹' W) Z)
     rel_dom := fun hh => hh.1
     rel_cod := by
       rintro W Z ⟨_, hrel⟩
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       exact f.1.rel_cod hf
     master_rel := by
       refine ⟨(smash V₀ V₁).master_mem, ?_⟩
       rw [show (smash V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
         inl_preimage_prodNbhd, inr_preimage_prodNbhd, sstep_master_eq]
       exact h.1.master_rel
     inter_right := by
       rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       obtain ⟨f', hf'⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel')).2
       refine ⟨hW, ?_⟩
       rw [← sstep_inter_right (f.1.rel_cod hf) (f'.1.rel_cod hf')]
       exact h.1.inter_right hrel hrel'
     mono := by
       rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
       have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
       have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
       obtain ⟨A, B, hA, hB, rfl⟩ := smash_mem_prodNbhd_form hW₂
       refine ⟨hW₂, ?_⟩
       rw [inl_preimage_prodNbhd] at hinl
       rw [inr_preimage_prodNbhd] at hinr
       rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       have hfB : f.1.rel B Z' := f.1.mono hf hinr hZZ' hB hZ'
       exact h.1.mono hrel hinl (sstep_subset hB hZ' hinr hZZ') hA
         (sstep_mem_of_mem (g := f) hfB) },
   by
     rintro Z ⟨_, hrel⟩
     rw [show (smash V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
       inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hrel
     have huniv : sstep V₁.master Z = (Set.univ : Set (StrictMap V₁ V₂)) := h.2 hrel
     have hcb : (⟨constMap V₁ V₂.bot,
       isStrict_constBot⟩ : StrictMap V₁ V₂) ∈ sstep V₁.master Z := by
       rw [huniv]; exact Set.mem_univ _
     obtain ⟨_, hZ⟩ := hcb
     rwa [NeighborhoodSystem.mem_bot] at hZ⟩

/-! ### The roundtrip identities and the adjunction isomorphism. -/

/-- A step with master codomain is everything: every strict map relates `Y` to
`Δ₁`. -/
theorem sstep_cod_master {Y : Set α} (hY : V₀.mem Y) :
    (sstep Y V₁.master : Set (StrictMap V₀ V₁)) = Set.univ := by
  ext f
  simp only [mem_sstep, Set.mem_univ, iff_true]
  exact f.1.mono f.1.master_rel (V₀.sub_master hY) subset_rfl hY V₁.master_mem

/-- **The decisive computation for the adjunction.** The `X`-section of `uncurry⊥
h` evaluated on a
neighbourhood `Y` is exactly the strict-function value `X h [Y, Z]`. At the
boundary (a master
factor) both sides collapse via strictness; off the boundary it is
`smashPair_principal_apply`. -/
theorem section_uncurry_rel (h : StrictMap V₀ (strictFun V₁ V₂))
    {X : Set α} (hX : V₀.mem X) {Y : Set β} (hY : V₁.mem Y) {Z : Set γ} :
    (smashSection (smashUncurryMap h).1 hX).rel Y Z ↔ h.1.rel X (sstep Y Z) := by
  rw [smashSection_rel]
  by_cases hXm : X = V₀.master
  · subst hXm
    constructor
    · rintro ⟨hY', hmem⟩
      rw [principal_master_eq_bot hX rfl,
        show smashPair V₀.bot (V₁.principal hY') = (smash V₀ V₁).bot from
          smashPair_eq_bot_iff.mpr (Or.inl rfl),
        isStrict_iff_apply_bot.mp (smashUncurryMap h).2, NeighborhoodSystem.mem_bot] at hmem
      subst hmem
      rw [sstep_cod_master hY]
      exact h.1.rel_master hX
    · intro hrel
      have huniv : sstep Y Z = (Set.univ : Set (StrictMap V₁ V₂)) := h.2 hrel
      have hZ : Z = V₂.master := by
        have hcb : (⟨constMap V₁ V₂.bot, isStrict_constBot⟩ : StrictMap V₁ V₂) ∈ sstep Y Z := by
          rw [huniv]; exact Set.mem_univ _
        obtain ⟨_, hbz⟩ := hcb
        rwa [NeighborhoodSystem.mem_bot] at hbz
      subst hZ
      exact ⟨hY, ((smashUncurryMap h).1.toElementMap _).master_mem⟩
  · by_cases hYm : Y = V₁.master
    · subst hYm
      constructor
      · rintro ⟨hY', hmem⟩
        rw [principal_master_eq_bot hY' rfl,
          show smashPair (V₀.principal hX) V₁.bot = (smash V₀ V₁).bot from
            smashPair_eq_bot_iff.mpr (Or.inr rfl),
          isStrict_iff_apply_bot.mp (smashUncurryMap h).2, NeighborhoodSystem.mem_bot] at hmem
        subst hmem
        rw [sstep_master_eq]
        exact h.1.rel_master hX
      · intro hrel
        obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
        have hZ : Z = V₂.master := f.2 hf
        subst hZ
        exact ⟨hY, ((smashUncurryMap h).1.toElementMap _).master_mem⟩
    · constructor
      · rintro ⟨hY', hmem⟩
        obtain ⟨_, hrel⟩ :=
          (smashPair_principal_apply (smashUncurryMap h).1 hX hXm hY hYm).mp hmem
        simpa only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] using hrel
      · intro hrel
        refine ⟨hY, (smashPair_principal_apply (smashUncurryMap h).1 hX hXm hY hYm).mpr ?_⟩
        refine ⟨smash_mem_proper hX hXm hY hYm, ?_⟩
        simpa only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] using hrel

/-- **Roundtrip (i): `uncurry⊥ ∘ curry⊥ = id`.** -/
theorem smashUncurry_curry (g : StrictMap (smash V₀ V₁) V₂) :
    smashUncurryMap (smashCurryMap g) = g := by
  apply Subtype.ext
  apply ApproximableMap.ext
  intro W Z
  constructor
  · rintro ⟨hW, hcurry⟩
    rcases hW with rfl | ⟨X, Y, hXp, hXne, hYp, hYne, rfl⟩
    · simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hcurry
      obtain ⟨hXm, _, hsec⟩ := hcurry
      have hZ : Z = V₂.master := isStrict_smashSection g.2 hXm hsec
      rw [hZ]; exact g.1.master_rel
    · simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hcurry
      obtain ⟨hX, _, hY, hmem⟩ := hcurry
      exact (smashPair_principal_apply g.1 hXp hXne hYp hYne).mp hmem
  · intro hrel
    have hW : (smash V₀ V₁).mem W := g.1.rel_dom hrel
    rcases hW with rfl | ⟨X, Y, hXp, hXne, hYp, hYne, rfl⟩
    · have hZ : Z = V₂.master := g.2 hrel
      subst hZ
      refine ⟨Or.inl rfl, ?_⟩
      simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd, sstep_master_eq]
      exact ⟨V₀.master_mem, (strictFun V₁ V₂).master_mem, Set.mem_univ _⟩
    · refine ⟨smash_mem_proper hXp hXne hYp hYne, ?_⟩
      simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
      have hsec : (smashSection g.1 hXp).rel Y Z :=
        ⟨hYp, (smashPair_principal_apply g.1 hXp hXne hYp hYne).mpr hrel⟩
      exact ⟨hXp, sstep_mem_of_mem
        (g := ⟨smashSection g.1 hXp, isStrict_smashSection g.2 hXp⟩) hsec, hsec⟩

/-- **Roundtrip (ii): `curry⊥ ∘ uncurry⊥ = id`.** -/
theorem smashCurry_uncurry (h : StrictMap V₀ (strictFun V₁ V₂)) :
    smashCurryMap (smashUncurryMap h) = h := by
  apply Subtype.ext
  apply ApproximableMap.ext
  intro X N
  constructor
  · rintro ⟨hX, hN, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    refine (rel_sstepFun_iff h.1 hX hL).mpr (fun p hp => ?_)
    exact (section_uncurry_rel h hX (hL p hp).1).mp (hmem p hp)
  · intro hrel
    have hX : V₀.mem X := h.1.rel_dom hrel
    have hN : (strictFun V₁ V₂).mem N := h.1.rel_cod hrel
    refine ⟨hX, hN, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
    intro p hp
    exact (section_uncurry_rel h hX (hL p hp).1).mpr
      ((rel_sstepFun_iff h.1 hX hL).mp hrel p hp)

/-- **Exercise 5.10 (Scott 1981, PRG-19) — the adjunction.** The strict currying
combinator is an
order isomorphism `((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂) ≃ (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂))`: the smash product is
left adjoint to
the strict function space. -/
def smashCurryEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    StrictMap (smash V₀ V₁) V₂ ≃o StrictMap V₀ (strictFun V₁ V₂) where
  toFun := smashCurryMap
  invFun := smashUncurryMap
  left_inv := smashUncurry_curry
  right_inv := smashCurry_uncurry
  map_rel_iff' := by
    intro g g'
    constructor
    · intro hcurry W Z hrel
      have h1 : (smashCurryMap g).1.rel (Sum.inl ⁻¹' W) (sstep (Sum.inr ⁻¹' W) Z) := by
        have hu : (smashUncurryMap (smashCurryMap g)).1.rel W Z := by
          rw [smashUncurry_curry]; exact hrel
        exact hu.2
      have h2 := hcurry _ _ h1
      have hu' : (smashUncurryMap (smashCurryMap g')).1.rel W Z := ⟨g.1.rel_dom hrel, h2⟩
      rw [smashUncurry_curry] at hu'
      exact hu'
    · intro hg X N hrel
      obtain ⟨hX, hN, hmem⟩ := hrel
      refine ⟨hX, hN, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hN
      intro p hp
      obtain ⟨hY, hmm⟩ := hmem p hp
      obtain ⟨W, hWmem, hWrel⟩ := hmm
      exact ⟨hY, W, hWmem, hg W p.2 hWrel⟩

end Domain.Neighborhood.Exercise510
