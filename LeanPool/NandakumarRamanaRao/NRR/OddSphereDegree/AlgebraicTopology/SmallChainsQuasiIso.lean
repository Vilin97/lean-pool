/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SmallChainsHomologySurjectivity
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SmallChainsHomologyInjectivity

/-!
# The small-simplices theorem: small chains include as a quasi-isomorphism

For an open cover `𝒰` of a space `X`, the inclusion chain map
`smallChainsInclusion R X 𝒰 : C_*^𝒰(X; R) ⟶ C_*(X; R)` of small singular chains
into all singular chains is a **quasi-isomorphism**: it induces an isomorphism on
homology in every degree.

This is the classical **small-simplices theorem** (a key step towards singular
Mayer–Vietoris and excision). It is assembled here from the two halves proved
earlier:

* `smallChainsInclusion_surjective_on_homology` (surjectivity on homology, every
 full homology class has a small representative via iterated barycentric
 subdivision), and
* `smallChainsInclusion_injective_on_homology` (injectivity on homology, a small
 cycle that bounds in the full complex already bounds in the small complex after
 a small homotopy correction).

Together they show the induced map on homology is bijective in every degree, hence
an isomorphism of `ModuleCat`-modules, hence the chain map is a quasi-isomorphism.

## Main results

* `SphereOddDegree.smallChainsInclusion_bijective_on_homology` — the induced map on
 degree-`n` homology is bijective.
* `SphereOddDegree.smallChains_inclusion_homology_iso` — the degreewise statement:
 the induced homology map `HomologicalComplex.homologyMap` is an isomorphism.
* `SphereOddDegree.smallChains_homologyIso` — the explicit module isomorphism in
 every degree.
* `SphereOddDegree.smallChains_inclusion_quasiIso` — the official **small-simplices
 theorem**: `smallChainsInclusion R X 𝒰` is a quasi-isomorphism.
-/

open CategoryTheory AlgebraicTopology
open SphereOddDegree.AffineBarycentricSubdivision

namespace SphereOddDegree

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-- The induced map on degree-`n` homology of the small-chain inclusion is
**bijective** (combine injectivity and surjectivity). -/
theorem smallChainsInclusion_bijective_on_homology
    (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ) :
    Function.Bijective (homologyMapInDegree (smallChainsInclusion R X 𝒰) n) :=
  ⟨smallChainsInclusion_injective_on_homology R X 𝒰 n,
    smallChainsInclusion_surjective_on_homology R X 𝒰 n⟩

/-- **Degreewise small-simplices theorem.** The map induced by the small-chain
inclusion on degree-`n` homology is an isomorphism of `ModuleCat`-modules. -/
theorem smallChains_inclusion_homology_iso
    (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (smallChainsInclusion R X 𝒰) n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (smallChainsInclusion_bijective_on_homology R X 𝒰 n)

/-- The explicit isomorphism of homology modules in degree `n` induced by the
inclusion of small chains. -/
noncomputable def smallChains_homologyIso
    (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ) :
    (smallChainComplex R X 𝒰).homology n ≅ (singularChainComplex R X).homology n :=
  haveI : IsIso (HomologicalComplex.homologyMap (smallChainsInclusion R X 𝒰) n) :=
    smallChains_inclusion_homology_iso R X 𝒰 n
  asIso (HomologicalComplex.homologyMap (smallChainsInclusion R X 𝒰) n)

/-- **The small-simplices theorem.** The inclusion of small chains into singular
chains is a quasi-isomorphism: it induces an isomorphism on homology in every
degree. This is the main hard input for singular Mayer–Vietoris and excision. -/
instance smallChains_inclusion_quasiIso
    (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) :
    QuasiIso (smallChainsInclusion R X 𝒰) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact smallChains_inclusion_homology_iso R X 𝒰 i

end SphereOddDegree
