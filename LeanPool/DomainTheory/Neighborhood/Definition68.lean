/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Definition63
import LeanPool.DomainTheory.Neighborhood.Exercise510

/-!
# Lecture VI — Definition 6.8 (Scott 1981, PRG-19): functors *continuous on maps*

> **DEFINITION 6.8.** On the category of domains and strict approximable maps a
functor `T` is
> *continuous on maps* if for any systems `D` and `E` the induced mapping
> `λf. T(f) : (D →⊥ E) → (T(D) →⊥ T(E))` is approximable.

This is the continuity condition that powers Theorem 6.9 (existence of
homomorphisms out of a fixed
point `D ≅ T(D)`): the homomorphism equation `h = k ∘ T(h) ∘ j` is a fixed-point
equation for the map
`λh. k ∘ T(h) ∘ j`, and it has a solution precisely because `λh. T(h)` — hence the
whole operator — is
itself an approximable (so continuous) self-map of a function-space domain.

## What the formalization uses

* **The category and the functor.** `T` is an `Endofunctor DomainObj` (Definition
6.3): an action
  `T.obj` on domains and `T.map` on the morphisms (here approximable maps, Theorem
  2.5 laws).
* **The strict function space `(D →⊥ E)`.** This is *exactly* Scott's domain on
the left of the
  induced map. The project already constructs it in `Exercise510.lean`: `strictFun
  D E` is the
  neighbourhood system whose elements are the **strict** approximable maps
  (`IsStrict f`, i.e.
  `f(⊥) = ⊥`), with the representation `strictFunEquiv : |D →⊥ E| ≃o StrictMap D
  E` mirroring
  Theorem 3.10. So this Definition is stated over Scott's strict maps verbatim,
  **not** the full
  function space.
* **"is approximable".** In this framework a function between domains is
*approximable* exactly when
  it is the elementwise action (`toElementMap`) of an approximable map
  (Proposition 2.2 / Theorem
  3.10). So `λf. T(f)` being approximable is rendered as the existence of a
  witnessing
  `Φ : (D →⊥ E) → (T(D) →⊥ T(E))` (an `ApproximableMap` between the two strict
  function-space
  *domains*) whose action reproduces `T` on the underlying maps — transported
  across the
  representation `strictFunEquiv` via `toStrictFilter`/`toStrictMap`.

Because the witnessing equation reads off the underlying map of a `StrictMap`, it
automatically forces
`T.map f` to be strict whenever `f` is (lemma `ContinuousOnMaps.isStrict_map`): a
`T` continuous on
maps does restrict to Scott's subcategory of strict maps, as required.

## A design note on the category (strict maps vs. all maps)

Scott states 6.8 on the category of domains and *strict* maps, whereas the
project's abstract spine
(Definitions 6.3–6.7) is built on the all-maps `DomainObj` category (its `Hom` is
the full
`ApproximableMap`). We bridge the two faithfully without introducing a second,
strict-map category
abstraction: the functor here is still `T : Endofunctor DomainObj` (acting on
*all* maps), but the
continuity condition is stated over the *strict* function spaces `(D →⊥ E)`, and
strictness-preservation
is then *derived* (`ContinuousOnMaps.isStrict_map`) rather than assumed. So `T`
lives on the all-maps
category, yet "continuous on maps" pins down exactly the behaviour Scott asks for
on the strict
subcategory — keeping Definition 6.8 coherent with the rest of the Lecture VI
spine while remaining
literally about Scott's strict maps.

The identity functor is continuous on maps (`continuousOnMaps_id`), witnessing
non-vacuity; its
representing `Φ` is the identity on the function space. Everything here is
**choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap Domain.Neighborhood.Exercise510

universe u

/-- The **identity endofunctor** on any category: it fixes objects and morphisms.
(A convenient
witness that `Endofunctor` is inhabited; used to show Definition 6.8 is
non-vacuous.) -/
def idEndofunctor (Obj : Type u) [Category Obj] : Endofunctor Obj where
  obj X := X
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem idEndofunctor_obj {Obj : Type u} [Category Obj] (X : Obj) :
    (idEndofunctor Obj).obj X = X := rfl

@[simp] theorem idEndofunctor_map {Obj : Type u} [Category Obj] {X Y : Obj}
    (f : Category.Hom X Y) : (idEndofunctor Obj).map f = f := rfl

/-- **Definition 6.8 (Scott 1981, PRG-19).** An endofunctor `T` on the category of
domains is
*continuous on maps* when, for every pair of domains `D` and `E`, the induced
action `λf. T(f)` on the
**strict** function space `(D →⊥ E)` is approximable: there is an approximable map
`Φ` from
`(D →⊥ E)` to `(T(D) →⊥ T(E))` whose elementwise action (read through the
representation
`strictFunEquiv`) sends each strict map `f` to `T(f)`. -/
def ContinuousOnMaps (T : Endofunctor DomainObj) : Prop :=
  ∀ D E : DomainObj,
    ∃ Φ : ApproximableMap (strictFun D.sys E.sys) (strictFun (T.obj D).sys (T.obj E).sys),
      ∀ f : StrictMap D.sys E.sys,
        (toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map (X := D) (Y := E) f.1

/-- A functor continuous on maps **preserves strictness** (so it genuinely lives
on Scott's category
of domains and strict maps): if `f` is strict then so is `T(f)`. This is automatic
from the witnessing
equation, whose left-hand side is the underlying map of a `StrictMap`. -/
theorem ContinuousOnMaps.isStrict_map {T : Endofunctor DomainObj} (h : ContinuousOnMaps T)
    {D E : DomainObj} (f : StrictMap D.sys E.sys) :
    IsStrict (T.map (X := D) (Y := E) f.1) := by
  obtain ⟨Φ, hΦ⟩ := h D E
  rw [← hΦ f]
  exact (toStrictMap (Φ.toElementMap (toStrictFilter f))).2

/-- `toStrictMap ∘ toStrictFilter = id` (the right inverse of the
strict-function-space
representation, Exercise 5.10). -/
theorem toStrictMap_toStrictFilter {α β : Type*} {V₀ : NeighborhoodSystem α}
    {V₁ : NeighborhoodSystem β} (f : StrictMap V₀ V₁) :
    toStrictMap (toStrictFilter f) = f :=
  (strictFunEquiv V₀ V₁).right_inv f

/-- **The identity functor is continuous on maps** — the basic witness that
Definition 6.8 is
satisfiable. The representing approximable map is the identity on `(D →⊥ E)`. -/
theorem continuousOnMaps_id : ContinuousOnMaps (idEndofunctor DomainObj) := by
  intro D E
  refine ⟨idMap (strictFun D.sys E.sys), fun f => ?_⟩
  change (toStrictMap ((idMap (strictFun D.sys E.sys)).toElementMap (toStrictFilter f))).1 = f.1
  rw [toElementMap_idMap, toStrictMap_toStrictFilter]

end Domain.Neighborhood
