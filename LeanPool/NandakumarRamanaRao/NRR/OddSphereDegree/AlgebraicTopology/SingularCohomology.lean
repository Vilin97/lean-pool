/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularHomologyFunctorAPI
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Singular cohomology functor (dualization of the singular chain complex)

This file builds a functorial singular cohomology theory by dualizing
Mathlib's singular chain complex functor.

Pinned Mathlib (`v4.28.0`, commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`)
has **no** packaged singular cohomology theory (no `singularCohomologyFunctor`,
no named `Hⁿ(X; M)`, no cup product, no universal coefficient theorem). It does,
however, provide every building block needed to *construct* singular cohomology
with coefficients in a module by dualizing the existing singular chain complex:

* `AlgebraicTopology.singularChainComplexFunctor` — the singular chains
 `C_•(X)`, covariantly functorial in `X`;
* `HomologicalComplex.opFunctor` / `Functor.op` — make the construction
 contravariant in `X` (so the pullback `f^*` comes for free, structurally);
* `CategoryTheory.linearYoneda` — the dualizing `Hom(-, M)` into `R`-modules;
* `Functor.mapHomologicalComplex` — apply the dualizer objectwise;
* `HomologicalComplex.homologyFunctor` — take `n`-th (co)homology.

## Construction

For a commutative ring `R` and a coefficient module `M : ModuleCat R`, the
**singular cochain complex functor** is the composite

```text
singularCochainComplexFunctor R M
 : TopCatᵒᵖ ⥤ CochainComplex (ModuleCat R) ℕ
 := ((singularChainComplexFunctor (ModuleCat R)).obj M).op
 ⋙ HomologicalComplex.opFunctor _ _
 ⋙ ((linearYoneda R (ModuleCat R)).obj M).mapHomologicalComplex _
```

and the **singular cohomology functor** in degree `n` is

```text
singularCohomologyFunctor R M n
 : TopCatᵒᵖ ⥤ ModuleCat R
 := singularCochainComplexFunctor R M ⋙ HomologicalComplex.homologyFunctor _ _ n.
```

The codomain is recorded as `CochainComplex (ModuleCat R) ℕ` rather than
`HomologicalComplex (ModuleCat R) (ComplexShape.down ℕ).symm`; these are
**definitionally equal** since `(ComplexShape.down ℕ).symm = ComplexShape.up ℕ`
by `rfl`, so no shape-isomorphism lemma is needed.

## Conventions

* **Coefficients.** `M : ModuleCat R` is the coefficient module; the coefficient
 *ring* is `R`. The relevant downstream case is `R = ZMod 2`, for which the
 abbreviation `singularCohomologyZMod2` fixes `M = ModuleCat.of (ZMod 2) (ZMod 2)`.
* **Contravariance.** The functor is contravariant in the space: a continuous
 map `f : X → Y` becomes a `TopCat` morphism `TopCat.ofHom f : X ⟶ Y`, whose
 opposite `(TopCat.ofHom f).op : Opposite.op Y ⟶ Opposite.op X` is sent by the
 functor to the pullback `f^* : Hⁿ(Y; M) → Hⁿ(X; M)`.
* **Functoriality.** Identities and composites are preserved
 (`singularCohomologyFunctor_map_id`, `singularCohomologyFunctor_map_comp`), and
 equal morphisms induce equal pullbacks (`singularCohomologyFunctor_map_congr`).
 These are the generic `CategoryTheory.Functor` laws on the composite.

## Scope

This is the construction layer only (the analogue of `PR-coh1a` in the design
inventories). It does **not** include homotopy invariance, the universal
coefficient theorem, any cohomology computation, or the cup product; those remain
downstream work.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

/-- The **singular cochain complex functor** with coefficients in a module
`M : ModuleCat R`, obtained by dualizing the singular chain complex functor.

It sends a space `X` (as an object of `TopCatᵒᵖ`) to the cochain complex
`Hom(C_•(X), M)` and is contravariant in `X`: a continuous map induces a cochain
map in the opposite direction. The codomain `CochainComplex (ModuleCat R) ℕ` is
definitionally `HomologicalComplex (ModuleCat R) (ComplexShape.down ℕ).symm`,
since `(ComplexShape.down ℕ).symm = ComplexShape.up ℕ`. -/
noncomputable def singularCochainComplexFunctor (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) :
    TopCat.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj M).op
    ⋙ HomologicalComplex.opFunctor _ _
    ⋙ ((linearYoneda R (ModuleCat.{0} R)).obj M).mapHomologicalComplex _

/-- The **`n`-th singular cohomology functor** `Hⁿ(-; M) : TopCatᵒᵖ ⥤ ModuleCat R`
with coefficients in a module `M : ModuleCat R`, obtained by taking `n`-th
homology of the singular cochain complex `Hom(C_•(X), M)`.

Contravariance in the space is structural: a continuous map `f` induces the
pullback `f^* : Hⁿ(Y; M) → Hⁿ(X; M)` via the functor's action on `(TopCat.ofHom
f).op`. -/
noncomputable def singularCohomologyFunctor (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (n : ℕ) :
    TopCat.{0}ᵒᵖ ⥤ ModuleCat.{0} R :=
  singularCochainComplexFunctor R M ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- Functoriality: the singular cohomology functor preserves identities. -/
theorem singularCohomologyFunctor_map_id (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (n : ℕ) (X : TopCat.{0}ᵒᵖ) :
    (singularCohomologyFunctor R M n).map (𝟙 X) = 𝟙 _ :=
  (singularCohomologyFunctor R M n).map_id X

/-- Functoriality: the singular cohomology functor preserves composition. Note
that, being contravariant in the space, this reverses the order of the induced
pullbacks at the level of `TopCat`. -/
theorem singularCohomologyFunctor_map_comp (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (n : ℕ) {X Y Z : TopCat.{0}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (singularCohomologyFunctor R M n).map (f ≫ g)
      = (singularCohomologyFunctor R M n).map f
          ≫ (singularCohomologyFunctor R M n).map g :=
  (singularCohomologyFunctor R M n).map_comp f g

/-- Congruence: equal morphisms induce equal maps on singular cohomology. -/
theorem singularCohomologyFunctor_map_congr (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (n : ℕ) {X Y : TopCat.{0}ᵒᵖ} {f g : X ⟶ Y}
    (h : f = g) :
    (singularCohomologyFunctor R M n).map f
      = (singularCohomologyFunctor R M n).map g := by
  rw [h]

/-- Functoriality: the singular cochain complex functor preserves identities. -/
theorem singularCochainComplexFunctor_map_id (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (X : TopCat.{0}ᵒᵖ) :
    (singularCochainComplexFunctor R M).map (𝟙 X) = 𝟙 _ :=
  (singularCochainComplexFunctor R M).map_id X

/-- Functoriality: the singular cochain complex functor preserves composition. -/
theorem singularCochainComplexFunctor_map_comp (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) {X Y Z : TopCat.{0}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (singularCochainComplexFunctor R M).map (f ≫ g)
      = (singularCochainComplexFunctor R M).map f
          ≫ (singularCochainComplexFunctor R M).map g :=
  (singularCochainComplexFunctor R M).map_comp f g

/-- The `n`-th singular cohomology functor with `ZMod 2` coefficients,
`Hⁿ(-; ZMod 2) : TopCatᵒᵖ ⥤ ModuleCat (ZMod 2)`. This is the coefficient target
needed for the downstream odd-degree / real projective space work. -/
noncomputable abbrev singularCohomologyZMod2 (n : ℕ) :
    TopCat.{0}ᵒᵖ ⥤ ModuleCat.{0} (ZMod 2) :=
  singularCohomologyFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) n

/-- The singular cochain complex functor with `ZMod 2` coefficients. -/
noncomputable abbrev singularCochainComplexZMod2 :
    TopCat.{0}ᵒᵖ ⥤ CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  singularCochainComplexFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2))

end SphereOddDegree
