/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricBoundaryChainMap
public import Mathlib.Tactic

/-!
# Barycentric subdivision as a chain map

This file packages the degree-wise barycentric subdivision maps
`barycentricSubdivisionLinearMap R X n` into a single morphism of chain
complexes from the singular chain complex of `X` to itself.

The chain-map condition is exactly the boundary-commutation identity
`barycentricSubdivisionLinearMap_commutes_boundary` proved earlier.

## Main results

* `barycentricSubdivisionChainMap`: the chain map
 `singularChainComplex R X ⟶ singularChainComplex R X`;
* `barycentricSubdivisionChainMap_f_n`: its degree-`n` component is the
 previously defined degree-wise map `barycentricSubdivisionLinearMap R X n`;
* `barycentricSubdivisionChainMap_map_generator`: on a basis generator `[σ]` the
 chain map gives the signed subdivision sum
 `barycentricSubdivisionGenerator R X n σ`.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-- The singular chain complex `C_•(X; R)` of `X` with coefficients in `R`,
specialized to coefficients `R` as a module over itself. This is the actual
project object underlying `singularChainGroup`, `singularBoundary` and
`barycentricSubdivisionLinearMap`. -/
noncomputable abbrev singularChainComplex (R : Type) [CommRing R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X

/-- **Barycentric subdivision as a chain map.** The degree-wise subdivision maps
`barycentricSubdivisionLinearMap R X n` assemble into a morphism of chain
complexes `singularChainComplex R X ⟶ singularChainComplex R X`. The chain-map
condition is the boundary commutation
`barycentricSubdivisionLinearMap_commutes_boundary`. -/
noncomputable def barycentricSubdivisionChainMap
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularChainComplex R X ⟶ singularChainComplex R X where
  f n := barycentricSubdivisionLinearMap R X n
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    exact barycentricSubdivisionLinearMap_commutes_boundary R X j

/-- **Degree-wise component of the subdivision chain map.** In degree `n` the
chain map is exactly the previously defined degree-wise operator. -/
@[simp] theorem barycentricSubdivisionChainMap_f_n
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (barycentricSubdivisionChainMap R X).f n = barycentricSubdivisionLinearMap R X n :=
  rfl

/-- **Generator formula for the subdivision chain map.** On a basis generator
`[σ]` the chain map returns the signed subdivision sum
`barycentricSubdivisionGenerator R X n σ`. -/
theorem barycentricSubdivisionChainMap_map_generator
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    ((barycentricSubdivisionChainMap R X).f n).hom (chainGenerator R X n σ)
      = barycentricSubdivisionGenerator R X n σ := by
  rw [barycentricSubdivisionChainMap_f_n, barycentricSubdivisionLinearMap_generator]

end AffineBarycentricSubdivision
end SphereOddDegree
