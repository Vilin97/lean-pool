/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.HomotopyToChainHomotopy

/-!
# Singular homology functor API (specialization layer)

This file stabilizes a small, formalized local API for Mathlib's singular
homology functor, specialized to integer coefficients, so later topological
degree work can use it without re-deriving functoriality each time.

It introduces **no** degree definition and **no** sphere homology computation; it
only repackages the generic `CategoryTheory.Functor` API
(`Functor.map_id`, `Functor.map_comp`, congruence) for the integral singular
chain / homology functors

* `SphereOddDegree.singularChainℤ : TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ`
* `SphereOddDegree.singularHomologyℤ n : TopCat ⥤ ModuleCat ℤ`

defined in `HomotopyToChainHomotopy.lean`.

## Conventions recorded here

* **Domain / codomain.** `singularChainComplexFunctor C : C ⥤ TopCat ⥤
 ChainComplex C ℕ` and `singularHomologyFunctor C n : C ⥤ TopCat ⥤ C`. The
 first `.obj` argument is the *coefficient object* in `C`; the second `.obj`
 argument is the topological space (an object of `TopCat`).
* **Coefficients.** We fix `C := ModuleCat.{0} ℤ` and the coefficient object
 `ModuleCat.of ℤ ℤ`, i.e. ordinary integral singular homology.
* **Grading.** `ChainComplex _ ℕ` is graded over `ℕ`; the homology index is
 `n : ℕ`.
* **Induced maps.** A continuous map becomes a `TopCat` morphism via
 `TopCat.ofHom`; the functor's `.map` produces the induced map on homology.
* **Functoriality.** Identities and composites are preserved
 (`singularHomologyℤ_map_id`, `singularHomologyℤ_map_comp`).
* **Equality of induced maps.** Equal `TopCat` morphisms induce equal maps
 (`singularHomologyℤ_map_congr`); chain-homotopic singular chain maps induce
 equal homology maps (`singularHomologyMap_eq_of_singularChainHomotopy`, from
 `HomotopyToChainHomotopy.lean`).
-/

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- Functoriality: the integral singular homology functor preserves identities. -/
theorem singularHomologyℤ_map_id (X : TopCat.{0}) (n : ℕ) :
    (singularHomologyℤ n).map (𝟙 X) = 𝟙 _ :=
  (singularHomologyℤ n).map_id X

/-- Functoriality: the integral singular homology functor preserves composition. -/
theorem singularHomologyℤ_map_comp {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (singularHomologyℤ n).map (f ≫ g)
      = (singularHomologyℤ n).map f ≫ (singularHomologyℤ n).map g :=
  (singularHomologyℤ n).map_comp f g

/-- Congruence: equal `TopCat` morphisms induce equal maps on integral singular
homology. -/
theorem singularHomologyℤ_map_congr {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : f = g) (n : ℕ) :
    (singularHomologyℤ n).map f = (singularHomologyℤ n).map g := by
  rw [h]

/-- Functoriality: the integral singular chain complex functor preserves
identities. -/
theorem singularChainℤ_map_id (X : TopCat.{0}) :
    singularChainℤ.map (𝟙 X) = 𝟙 _ :=
  singularChainℤ.map_id X

/-- Functoriality: the integral singular chain complex functor preserves
composition. -/
theorem singularChainℤ_map_comp {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularChainℤ.map (f ≫ g) = singularChainℤ.map f ≫ singularChainℤ.map g :=
  singularChainℤ.map_comp f g

end SphereOddDegree
