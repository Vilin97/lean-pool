/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Definition68
import LeanPool.DomainTheory.Neighborhood.Proposition611
import LeanPool.DomainTheory.Neighborhood.Proposition612

/-!
# Lecture VI — Definition 6.13 (Scott 1981, PRG-19): functors *monotone /
continuous on domains*

> **DEFINITION 6.13.** A functor `T` is *monotone on domains* iff whenever `D ◁
E`, then not only do
> we have `T(D) ◁ T(E)` but the projection pair `i, j` of 6.12 is mapped to the
same kind of
> projection pair `T(i), T(j)`. A monotone functor is *continuous on domains* iff
whenever `E` is a
> domain, then the mapping `λD. T(D) : {D ∣ D ◁ E} → {D' ∣ D' ◁ T(E)}` is
approximable.

This is the second of Scott's two continuity conditions on a functor (the first
being Definition 6.8,
*continuous on maps*). Together with a generating set `Γ` they power the existence
Theorem 6.14
(initial `T`-algebras as iterated-functor colimits `𝒟 = ⋃ₙ Tⁿ({Γ})`).

## What the formalization uses

* **The functor.** `T` is an `Endofunctor DomainObj` (Definition 6.3), acting on
objects (`T.obj`)
  and on the approximable maps between them (`T.map`).
* **The subdomain relation `◁`.** Definition 6.10 (`Subsystem`), between two
systems over the *same*
  token type, with the projection pair `i = Subsystem.inj`, `j = Subsystem.proj`
  of Proposition 6.12.
* **The domain of subsystems `{D ∣ D ◁ E}`.** Proposition 6.11 shows this *is* a
domain; here it is
  the subtype `{D // D ◁ E}` and the directed-union sups are the union subsystems
  `unionSys`.

### The carrier-type subtlety, and how it is handled

`D ◁ E` requires `D, E` to be systems over a *common* token type `α`. The abstract
functor `T` need
not preserve token types: `T.obj ⟨α, D⟩` and `T.obj ⟨α, E⟩` may have different
carriers. So
"`T(D) ◁ T(E)`" only makes sense once we *assert* that `T` preserves the token
type along `◁`, i.e.
once the carriers of the two images agree. **Monotone on domains** therefore
packages, for each
`h : D ◁ E`:

* `carrier_eq`: the two image carriers coincide;
* `sub`: the transported subdomain relation `T(D) ◁ T(E)`;
* `inj_heq`/`proj_heq`: Scott's "the projection pair `i, j` is mapped to `T(i),
T(j)`", i.e. the
  canonical 6.12 pair of `T(D) ◁ T(E)` is exactly `(T.map i, T.map j)` (stated up
  to the carrier
  transport, hence `HEq`).

**Continuous on domains** then adds Scott's approximability of `λD. T(D)`,
rendered in the concrete
neighbourhood framework as *preservation of directed unions of subsystems*: for
any directed family
`ℱ` of subsystems of `E` whose union is the subsystem `U`, the (target-side)
neighbourhood family of
`T(U)` is the union of those of the `T(D)`. This is exactly the continuity Scott
invokes in the proof
of 6.14 (`T(⋃ₙ Tⁿ{Γ}) = ⋃ₙ T(Tⁿ⁺¹{Γ})`).

The identity functor is monotone and continuous on domains
(`monotoneOnDomains_id`,
`continuousOnDomains_id`), witnessing non-vacuity. Everything is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

universe w

/-! ### Monotone on domains -/

/-- **Definition 6.13, monotone part (pointwise).** Given a subdomain relation `h
: D ◁ E`, the data
witnessing that the functor `T` carries it to `T(D) ◁ T(E)` *and* carries the
projection pair `i, j`
of 6.12 to the projection pair of `T(D) ◁ T(E)`.

Because `T` may change the token type, the two image systems live a priori over
different carriers;
`carrier_eq` records that they coincide, `sub` is the resulting subdomain relation
(with `T(E)`'s
system transported into `T(D)`'s carrier), and `inj_heq`/`proj_heq` say the
canonical 6.12 maps of
`sub` are `T(i)` and `T(j)` (up to that transport, hence `HEq`). -/
structure MonotoneAt (T : Endofunctor DomainObj.{w}) {α : Type w}
    {D E : NeighborhoodSystem α} (h : D ◁ E) : Prop where
  /-- The two image carriers coincide, so `T(D) ◁ T(E)` can be stated. -/
  carrier_eq : (T.obj ⟨α, E⟩).carrier = (T.obj ⟨α, D⟩).carrier
  /-- The image subdomain relation `T(D) ◁ T(E)` (with `T(E)`'s system carried
  into `T(D)`'s
  carrier). -/
  sub : (T.obj ⟨α, D⟩).sys ◁
    (carrier_eq ▸ (T.obj ⟨α, E⟩).sys : NeighborhoodSystem (T.obj ⟨α, D⟩).carrier)
  /-- The injection of `T(D) ◁ T(E)` is `T(i)` (Scott: the pair is mapped to
  `T(i), T(j)`). -/
  inj_heq : HEq (T.map (X := ⟨α, D⟩) (Y := ⟨α, E⟩) h.inj) sub.inj
  /-- The projection of `T(D) ◁ T(E)` is `T(j)`. -/
  proj_heq : HEq (T.map (X := ⟨α, E⟩) (Y := ⟨α, D⟩) h.proj) sub.proj

/-- **Definition 6.13 (Scott 1981, PRG-19), monotone on domains.** A functor `T`
is *monotone on
domains* iff every subdomain relation `D ◁ E` is carried to a subdomain relation
`T(D) ◁ T(E)` whose
projection pair is `(T(i), T(j))` — see `MonotoneAt`. -/
def MonotoneOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∀ {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E), MonotoneAt T h

/-- The **identity functor is monotone on domains**: it fixes objects and maps, so
`T(D) ◁ T(E)` is
just `D ◁ E` and the projection pair is unchanged. -/
theorem monotoneOnDomains_id : MonotoneOnDomains (idEndofunctor DomainObj.{w}) := by
  intro α D E h
  exact ⟨rfl, h, HEq.rfl, HEq.rfl⟩

/-! ### Continuous on domains -/

/-- The **target-side neighbourhood family** of the image `T(D)` of a subsystem `h
: D ◁ E`, viewed
over `T(E)`'s carrier (using `MonotoneAt.carrier_eq` to transport neighbourhoods
of `T(D)` to that
carrier). This is the data on which "`λD. T(D)` is approximable" is expressed. -/
def targetFam (T : Endofunctor DomainObj.{w}) (hmono : MonotoneOnDomains T)
    {α : Type w} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    Set (Set (T.obj ⟨α, E⟩).carrier) :=
  {Y | (T.obj ⟨α, D⟩).sys.mem ((hmono h).carrier_eq ▸ Y)}

/-- **Definition 6.13 (Scott 1981, PRG-19), continuous on domains.** A monotone
functor `T` is
*continuous on domains* iff `λD. T(D) : {D ∣ D ◁ E} → {D' ∣ D' ◁ T(E)}` is
approximable. In the
neighbourhood framework this is *preservation of directed unions of subsystems*:
for any non-empty
directed family `ℱ` of subsystems of `E` whose union is the subsystem `U` (`hU`),
the target-side
neighbourhood family of `T(U)` is the union of those of the `T(D)` for `D ∈ ℱ`. -/
def ContinuousOnDomains (T : Endofunctor DomainObj.{w}) : Prop :=
  ∃ hmono : MonotoneOnDomains T,
    ∀ {α : Type w} {E : NeighborhoodSystem α}
      (ℱ : Set (NeighborhoodSystem α)) (hℱ : ∀ ⦃D⦄, D ∈ ℱ → D ◁ E)
      (_hne : ℱ.Nonempty) (_hdir : DirectedOn (· ◁ ·) ℱ)
      {U : NeighborhoodSystem α} (hUE : U ◁ E)
      (_hU : ∀ X, U.mem X ↔ ∃ D ∈ ℱ, D.mem X),
      targetFam T hmono hUE = ⋃ D, ⋃ hD : D ∈ ℱ, targetFam T hmono (hℱ hD)

/-- The **identity functor is continuous on domains**: `targetFam` reduces to the
plain
neighbourhood
family, so directed-union preservation is exactly the hypothesis `hU` that `U` is
the union. -/
theorem continuousOnDomains_id : ContinuousOnDomains (idEndofunctor DomainObj.{w}) := by
  refine ⟨monotoneOnDomains_id, ?_⟩
  intro α E ℱ hℱ _hne _hdir U hUE hU
  apply Set.ext
  intro Y
  simp only [targetFam, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact hU Y

end Domain.Neighborhood
