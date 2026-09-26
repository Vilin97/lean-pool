/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Algebra.Homology.Opposite
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularCohomology
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.HomotopyInvariance
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.Backports.PrismSimplicialHomotopy

/-!
# Homotopy invariance of singular cohomology — UNCONDITIONAL

This file proves **homotopy invariance for the library's singular cohomology
functor `singularCohomologyFunctor`**, unconditionally, for an arbitrary
coefficient module `M : ModuleCat R` (and in particular for `ZMod 2`).

The argument has two parts.

* **Dualization (algebraic).** A chain homotopy between the singular chain maps of
 two continuous maps (at *any* coefficient module `M : ModuleCat R`) dualizes to
 equal pullbacks on singular cohomology `Hⁿ(-; M)`. This is the cohomology
 analogue of the homology consumer
 `singularHomologyMap_eq_of_singularChainHomotopy`
 (`HomotopyToChainHomotopy.lean`) and needs no prism operator. It is
 `singularCohomologyMap_eq_of_chainHomotopy`.

* **Prism (topological → chain homotopy).** Turning a *topological* homotopy into
 that chain homotopy is exactly the prism operator. Pinned Mathlib has no such
 operator, but the library's backported algebraic prism together with its
 singular cylinder constructs it, at integer coefficients
 (`singularChainHomotopyOfHomotopy`) and — what we use here — at an **arbitrary**
 coefficient module (`singularChainHomotopyOfHomotopyModule`,
 `Backports/PrismSimplicialHomotopy.lean`). Hence the prism hypothesis
 `SingularCohomologyPrism R M` isolated below is a **theorem**
 (`singularCohomologyPrism`), and full homotopy invariance of cohomology is
 unconditional in every form downstream code needs (`TopCat` maps, the
 `Homotopic` relation, the `C(X, Y)` interface), with `ZMod 2` specializations.

## Logical shape

```text
topological homotopy ──singularChainHomotopyOfHomotopyModule──▶ chain homotopy (coeff M)
 │
 homotopyOpFunctorMap │
 + Functor.mapHomotopy │
 + Homotopy.homologyMap_eq │
 ▼
 equal pullbacks on Hⁿ(-; M)
```
-/

@[expose] public section

open CategoryTheory AlgebraicTopology HomologicalComplex Opposite Limits

namespace SphereOddDegree

universe u v w

/--
**Unconditional dualization step.** If the singular chain maps (with
coefficients in `M : ModuleCat R`) induced by two continuous maps `f, g : X ⟶ Y`
are chain-homotopic, then the induced pullbacks on the `n`-th singular cohomology
`Hⁿ(-; M)` are equal.

This is the genuine cohomology consumer of a chain homotopy: it requires no prism
operator.
-/
theorem singularCohomologyMap_eq_of_chainHomotopy
    (R : Type) [CommRing R] (M : ModuleCat.{0} R) (n : ℕ)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : Homotopy (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map f)
                  (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map g)) :
    (singularCohomologyFunctor R M n).map f.op
      = (singularCohomologyFunctor R M n).map g.op := by
  have cochainH := (((linearYoneda R (ModuleCat R)).obj M).mapHomotopy H.op)
  exact cochainH.homologyMap_eq n

/-- **The cohomology prism-operator hypothesis** (coefficient-`M` form).

A `SingularCohomologyPrism R M` asserts that every topological homotopy between
two `TopCat` maps gives rise to a chain homotopy of the induced singular chain
maps with coefficients in `M`. This is exactly the classical prism operator at
coefficient module `M`. It is **no longer a hypothesis**: it is discharged by
`singularCohomologyPrism` below using the library's backported algebraic prism.
The definition is kept for documentation and as a reusable interface. -/
def SingularCohomologyPrism (R : Type) [CommRing R] (M : ModuleCat.{0} R) : Prop :=
  ∀ {X Y : TopCat.{0}} {f g : X ⟶ Y},
    ContinuousMap.Homotopy f.hom g.hom →
      Nonempty (Homotopy (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map f)
                         (((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).map g))

/-- **The cohomology prism operator, discharged (unconditional).** For any
coefficient module `M : ModuleCat R`, the prism hypothesis holds: a topological
homotopy gives a chain homotopy of the singular chain maps with coefficients in
`M`. Witnessed by `singularChainHomotopyOfHomotopyModule`. -/
theorem singularCohomologyPrism (R : Type) [CommRing R] (M : ModuleCat.{0} R) :
    SingularCohomologyPrism R M :=
  fun H => ⟨singularChainHomotopyOfHomotopyModule R M H⟩

/-- **Homotopy invariance of cohomology (topological homotopy form), unconditional.**

A topological homotopy between two `TopCat` maps `f, g : X ⟶ Y` induces equal
pullbacks on the `n`-th singular cohomology `Hⁿ(-; M)`. -/
theorem singularCohomologyMap_eq_of_homotopy
    (R : Type) [CommRing R] (M : ModuleCat.{0} R) (n : ℕ)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    (singularCohomologyFunctor R M n).map f.op
      = (singularCohomologyFunctor R M n).map g.op :=
  singularCohomologyMap_eq_of_chainHomotopy R M n
    (singularChainHomotopyOfHomotopyModule R M H)

/-- **Homotopy invariance of cohomology (`Homotopic` form), unconditional.** -/
theorem singularCohomologyMap_eq_of_homotopic
    (R : Type) [CommRing R] (M : ModuleCat.{0} R) (n : ℕ)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) :
    (singularCohomologyFunctor R M n).map f.op
      = (singularCohomologyFunctor R M n).map g.op := by
  obtain ⟨H⟩ := h
  exact singularCohomologyMap_eq_of_homotopy R M n H

/-- **Homotopy invariance of cohomology (`C(X, Y)` interface), unconditional.** -/
theorem singularCohomologyMap_eq_of_homotopic_continuousMap
    (R : Type) [CommRing R] (M : ModuleCat.{0} R) (n : ℕ)
    {X Y : TopCat.{0}} {f g : C(X, Y)}
    (h : ContinuousMap.Homotopic f g) :
    (singularCohomologyFunctor R M n).map (TopCat.ofHom f).op
      = (singularCohomologyFunctor R M n).map (TopCat.ofHom g).op :=
  singularCohomologyMap_eq_of_homotopic R M n h

/-! ## `ZMod 2` specializations -/

/-- **`ZMod 2` cohomology consumer of a chain homotopy.** If the `ZMod 2`-singular
chain maps of `f, g` are chain-homotopic, the `ZMod 2`-cohomology pullbacks
agree. -/
theorem singularCohomologyZMod2_map_eq_of_chainHomotopy (n : ℕ)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : Homotopy
          (((singularChainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj
              (ModuleCat.of (ZMod 2) (ZMod 2))).map f)
          (((singularChainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj
              (ModuleCat.of (ZMod 2) (ZMod 2))).map g)) :
    (singularCohomologyZMod2 n).map f.op = (singularCohomologyZMod2 n).map g.op :=
  singularCohomologyMap_eq_of_chainHomotopy (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) n H

/-- **`ZMod 2` homotopy invariance (`Homotopic` form), unconditional.** -/
theorem singularCohomologyZMod2_map_eq_of_homotopic (n : ℕ)
    {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) :
    (singularCohomologyZMod2 n).map f.op = (singularCohomologyZMod2 n).map g.op :=
  singularCohomologyMap_eq_of_homotopic (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) n h

/-- **`ZMod 2` homotopy invariance (`C(X, Y)` interface), unconditional.** Two
homotopic continuous maps `f, g : C(X, Y)` induce equal pullbacks on the `ZMod 2`
singular cohomology. -/
theorem singularCohomologyZMod2_map_eq_of_homotopic_continuousMap (n : ℕ)
    {X Y : TopCat.{0}} {f g : C(X, Y)}
    (h : ContinuousMap.Homotopic f g) :
    (singularCohomologyZMod2 n).map (TopCat.ofHom f).op
      = (singularCohomologyZMod2 n).map (TopCat.ofHom g).op :=
  singularCohomologyMap_eq_of_homotopic_continuousMap (ZMod 2)
    (ModuleCat.of (ZMod 2) (ZMod 2)) n h

end SphereOddDegree
