/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricBoundaryCancellation
import Mathlib.Tactic

/-!
# Chain-level barycentric boundary commutation `∂ ∘ sd = sd ∘ ∂`

This file lifts the generator-level cancellation
`expandedBarycentricBoundaryCancellation` (from
`BarycentricBoundaryCancellation.lean`) to all singular chains.

The main results are:

* `barycentricSubdivisionLinearMap_commutes_boundary`: the morphism-level
 identity
 ```text
 sd ≫ ∂ = ∂ ≫ sd
 ```
 in the category of `R`-modules, i.e. degree-wise barycentric subdivision is a
 chain map for the singular boundary;
* `boundary_barycentricSubdivision_apply`: the pointwise version, `∂ (sd c) =
 sd (∂ c)` for every chain `c`.

## Degree convention

The singular boundary `singularBoundary R X n : C_{n+1} → C_n` is the degree
`(n+1) → n` differential of the alternating face map complex, with the library's
`(-1)^i` sign convention on faces. The subdivision operator
`barycentricSubdivisionLinearMap R X n : C_n → C_n` is the signed sum over
permutations. The commutation identity below relates
`barycentricSubdivisionLinearMap R X (n+1) ≫ singularBoundary R X n` with
`singularBoundary R X n ≫ barycentricSubdivisionLinearMap R X n`.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-- **Boundary commutation on a generator (chain-map form).**
On a basis generator `[σ]`, the singular boundary of its subdivision equals the
subdivision of its boundary. -/
theorem boundary_barycentricSubdivision_generator
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X (n + 1)) :
    (singularBoundary R X n).hom
        ((barycentricSubdivisionLinearMap R X (n + 1)).hom (chainGenerator R X (n + 1) σ))
      =
    (barycentricSubdivisionLinearMap R X n).hom
        ((singularBoundary R X n).hom (chainGenerator R X (n + 1) σ)) := by
  rw [barycentricSubdivisionLinearMap_generator]
  exact expandedBarycentricBoundaryCancellation R X n σ

/-- **Chain-level boundary commutation.** Degree-wise barycentric subdivision is
a chain map for the singular boundary:
```text
sd ≫ ∂ = ∂ ≫ sd.
```
This lifts the generator-level cancellation to all chains by coproduct
extensionality. -/
theorem barycentricSubdivisionLinearMap_commutes_boundary
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    barycentricSubdivisionLinearMap R X (n + 1) ≫ singularBoundary R X n
      = singularBoundary R X n ≫ barycentricSubdivisionLinearMap R X n := by
  suffices h : singularBoundary R X n ≫ barycentricSubdivisionLinearMap R X n
      = barycentricSubdivisionLinearMap R X (n + 1) ≫ singularBoundary R X n from h.symm
  apply Sigma.hom_ext
  intro σ
  -- Two morphisms from ModuleCat.of R R (free rank 1) agree iff they agree on 1.
  have hval : ∀ (f g : ModuleCat.of R R ⟶ singularChainGroup R X n),
      f.hom (1 : R) = g.hom (1 : R) → f = g := by
    intro f g h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hf := f.hom.map_smul x (1 : R)
    have hg := g.hom.map_smul x (1 : R)
    simp at hf hg
    rw [hf, hg, h]
  apply hval
  -- Reduce (ι σ ≫ f).hom 1 to f.hom (chainGenerator σ) via erw to handle
  -- the definitional equality between ∐ and singularChainGroup.
  erw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
       LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  exact (boundary_barycentricSubdivision_generator R X n σ).symm

/-- **Pointwise boundary commutation.** For every singular chain `c`,
```text
∂ (sd c) = sd (∂ c).
```
This is the element-level form of
`barycentricSubdivisionLinearMap_commutes_boundary`. -/
theorem boundary_barycentricSubdivision_apply
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (c : singularChainGroup R X (n + 1)) :
    (singularBoundary R X n).hom
        ((barycentricSubdivisionLinearMap R X (n + 1)).hom c)
      =
    (barycentricSubdivisionLinearMap R X n).hom
        ((singularBoundary R X n).hom c) := by
  have h := barycentricSubdivisionLinearMap_commutes_boundary R X n
  have := congrArg (fun (m : singularChainGroup R X (n + 1) ⟶ singularChainGroup R X n) => m.hom c) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this

end AffineBarycentricSubdivision
end SphereOddDegree
