/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.AffineBarycentricSubdivision
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.CupProduct
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.AlexanderWhitneyChainMap

/-!
# Degree-wise barycentric subdivision operator on singular chains

This file builds on `AffineBarycentricSubdivision.lean`.

For a singular `n`-simplex `σ : Δⁿ → X`, barycentric subdivision is defined in
chain degree `n` by the classical signed finite sum

```text
sd(σ) = Σ_{π ∈ Sym(n+1)} sign(π) · (σ ∘ a_π),
```

where `a_π : Δⁿ → Δⁿ` is the affine simplex defined in
`AffineBarycentricSubdivision.lean`, sending the `k`-th vertex of the domain to
`barycenter(π 0, ..., π k)`.

The output here is deliberately **degree-wise**:

* `barycentricSubdivSimplex` composes a singular simplex with one affine
 subdivision simplex;
* `barycentricSubdivisionGenerator` is the signed subdivision of one basis
 simplex as an element of the singular chain group;
* `barycentricSubdivisionLinearMap` extends this assignment linearly to all
 singular chains in a fixed degree.

This file does **not** assert that this degree-wise operator commutes with the
boundary. The required boundary theorem is the face/sign calculation

```text
∂ (sd c) = sd (∂ c).
```

Only after that theorem is proved should one package `sd` as a genuine chain map.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-! ## 1. Continuous affine subdivision maps -/

/-- Coordinate continuity for the affine subdivision map. -/
theorem continuous_affineSubdivMapFun_coord (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    Continuous fun x : Delta n => affineSubdivMapFun n π x j := by
  unfold affineSubdivMapFun
  apply continuous_finsetSum
  intro k _
  exact (((continuous_apply k).comp continuous_subtype_val).mul continuous_const)

/-- The affine subdivision map is continuous. -/
theorem continuous_affineSubdivMap (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    Continuous (affineSubdivMap n π) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun j => continuous_affineSubdivMapFun_coord n π j

/-- The affine subdivision simplex as a bundled continuous self-map of `Δⁿ`. -/
noncomputable def affineSubdivContinuousMap (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) : C(Delta n, Delta n) :=
  ⟨affineSubdivMap n π, continuous_affineSubdivMap n π⟩

@[simp] theorem affineSubdivContinuousMap_apply (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) (x : Delta n) :
    affineSubdivContinuousMap n π x = affineSubdivMap n π x := rfl

/-! ## 2. Singular-simplex summands -/

/-- Coordinate realization of Mathlib's intrinsic simplex. -/
noncomputable def intrinsicSimplexCoordinates (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ Delta n where
  toFun x := ⟨x.weights, x.nonneg, by simpa [Finsupp.sum_fintype] using x.total⟩
  invFun x :=
    { weights := Finsupp.equivFunOnFinite.symm x.1
      nonneg := x.2.1
      total := by simpa [Finsupp.sum_fintype] using x.2.2 }
  left_inv x := by ext i; rfl
  right_inv x := by apply Subtype.ext; rfl
  continuous_toFun :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous.subtype_mk _
  continuous_invFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).isInducing.continuous_iff.mpr
    exact continuous_subtype_val


/-- Convert a singular simplex, represented as a simplex of `TopCat.toSSet.obj X`,
to the corresponding bundled continuous map out of the topological standard
simplex. -/
noncomputable def singularSimplexAsContinuousMap (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X n) : C(Delta n, X) :=
  ((X.toSSetObjEquiv (Opposite.op (⦋n⦌ : SimplexCategory))) σ).comp
    ⟨(intrinsicSimplexCoordinates n).symm, (intrinsicSimplexCoordinates n).symm.continuous⟩

/-- Convert a bundled continuous map out of the standard simplex into the
corresponding simplex of the singular simplicial set. -/
noncomputable def continuousMapAsSingularSimplex (X : TopCat.{0}) (n : ℕ)
    (σ : C(Delta n, X)) : singularSimplices X n :=
  (X.toSSetObjEquiv (Opposite.op (⦋n⦌ : SimplexCategory))).symm
    (σ.comp ⟨intrinsicSimplexCoordinates n, (intrinsicSimplexCoordinates n).continuous⟩)

@[simp] theorem singularSimplexAsContinuousMap_continuousMapAsSingularSimplex
    (X : TopCat.{0}) (n : ℕ) (σ : C(Delta n, X)) :
    singularSimplexAsContinuousMap X n (continuousMapAsSingularSimplex X n σ) = σ := by
  ext x
  simp [singularSimplexAsContinuousMap, continuousMapAsSingularSimplex]

@[simp] theorem continuousMapAsSingularSimplex_singularSimplexAsContinuousMap
    (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    continuousMapAsSingularSimplex X n (singularSimplexAsContinuousMap X n σ) = σ := by
  apply (X.toSSetObjEquiv _).injective
  ext x
  simp [singularSimplexAsContinuousMap, continuousMapAsSingularSimplex]

/-- The `π`-summand of barycentric subdivision of a singular simplex: precompose
`σ : Δⁿ → X` with the affine subdivision simplex `a_π : Δⁿ → Δⁿ`. -/
noncomputable def barycentricSubdivSimplex (X : TopCat.{0}) (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) (σ : singularSimplices X n) :
    singularSimplices X n :=
  continuousMapAsSingularSimplex X n
    ((singularSimplexAsContinuousMap X n σ).comp (affineSubdivContinuousMap n π))

/-- The identity permutation summand is the singular simplex obtained by
precomposition with the identity-order affine subdivision simplex. This is not
simplified to `σ`; the identity-order affine summand is only one subsimplex of
barycentric subdivision, not the identity map. -/
theorem barycentricSubdivSimplex_def (X : TopCat.{0}) (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) (σ : singularSimplices X n) :
    barycentricSubdivSimplex X n π σ =
      continuousMapAsSingularSimplex X n
        ((singularSimplexAsContinuousMap X n σ).comp (affineSubdivContinuousMap n π)) := rfl

/-! ## 3. Degree-wise chain groups and generators -/

/-- The singular chain group `C_n(X; R)` with coefficients in `R`, specialized to
coefficients `R` as a module over itself. -/
noncomputable abbrev singularChainGroup (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :=
  (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).X n

/-- The basis chain associated to a singular simplex. -/
noncomputable def chainGenerator (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X n) : singularChainGroup R X n :=
  ((Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ).hom (1 : R))

/-- The sign of a finite permutation, interpreted in a coefficient ring. For
`R = ℤ` this is `±1`; for `R = ZMod 2` both signs become `1`. -/
noncomputable def permSignCoeff (R : Type) [CommRing R] {n : ℕ}
    (π : Equiv.Perm (Fin (n + 1))) : R :=
  ((Equiv.Perm.sign π : ℤ) : R)

/-- The barycentric subdivision of a basis singular simplex as a chain in the
same degree. -/
noncomputable def barycentricSubdivisionGenerator (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) : singularChainGroup R X n :=
  ∑ π : Equiv.Perm (Fin (n + 1)),
    permSignCoeff R π • chainGenerator R X n (barycentricSubdivSimplex X n π σ)

/-- The `R`-linear map `R → C_n(X; R)` sending `1` to the barycentric subdivision
of a fixed basis simplex. -/
noncomputable def barycentricSubdivisionGeneratorHom (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    ModuleCat.of R R ⟶ singularChainGroup R X n :=
  ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight (barycentricSubdivisionGenerator R X n σ))

/-- The degree-`n` barycentric subdivision operator on singular chains. It is
obtained from the coproduct universal property by prescribing its value on each
basis simplex. -/
noncomputable def barycentricSubdivisionLinearMap (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) :
    singularChainGroup R X n ⟶ singularChainGroup R X n :=
  Sigma.desc fun σ : singularSimplices X n =>
    barycentricSubdivisionGeneratorHom R X n σ

/-- The degree-wise subdivision operator has the prescribed value on basis
simplices. -/
theorem barycentricSubdivisionLinearMap_generator (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    (barycentricSubdivisionLinearMap R X n).hom (chainGenerator R X n σ)
      = barycentricSubdivisionGenerator R X n σ := by
  have key : Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ
        ≫ barycentricSubdivisionLinearMap R X n
      = barycentricSubdivisionGeneratorHom R X n σ := Sigma.ι_desc _ _
  have h := congrArg (fun (f : ModuleCat.of R R ⟶ singularChainGroup R X n) => f.hom (1 : R)) key
  dsimp [chainGenerator, barycentricSubdivisionGeneratorHom] at h
  have hone : (1 : R) • barycentricSubdivisionGenerator R X n σ = barycentricSubdivisionGenerator R X n σ := one_smul _ _
  exact h.trans hone

/-- Integral degree-wise barycentric subdivision. -/
noncomputable abbrev barycentricSubdivisionLinearMapℤ (X : TopCat.{0}) (n : ℕ) :
    singularChainGroup ℤ X n ⟶ singularChainGroup ℤ X n :=
  barycentricSubdivisionLinearMap ℤ X n

/-- Mod-2 degree-wise barycentric subdivision. The same signed definition is
used; the sign coefficients reduce to `1` in `ZMod 2`. -/
noncomputable abbrev barycentricSubdivisionLinearMapZMod2 (X : TopCat.{0}) (n : ℕ) :
    singularChainGroup (ZMod 2) X n ⟶ singularChainGroup (ZMod 2) X n :=
  barycentricSubdivisionLinearMap (ZMod 2) X n

/-! ## 4. Explicit formulas useful for later boundary computations -/

/-- Expanding the value of the degree-wise operator on a basis simplex. -/
theorem barycentricSubdivisionLinearMap_generator_sum (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    (barycentricSubdivisionLinearMap R X n).hom (chainGenerator R X n σ)
      = ∑ π : Equiv.Perm (Fin (n + 1)),
          permSignCoeff R π • chainGenerator R X n (barycentricSubdivSimplex X n π σ) := by
  rw [barycentricSubdivisionLinearMap_generator]
  rfl

/-- Linearity of the degree-wise subdivision operator, as a concrete formula on
vectors in the degree-`n` singular chain group. -/
theorem barycentricSubdivisionLinearMap_add (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (c d : singularChainGroup R X n) :
    (barycentricSubdivisionLinearMap R X n).hom (c + d)
      = (barycentricSubdivisionLinearMap R X n).hom c
        + (barycentricSubdivisionLinearMap R X n).hom d := by
  exact map_add (barycentricSubdivisionLinearMap R X n).hom c d

/-- Scalar compatibility of the degree-wise subdivision operator. -/
theorem barycentricSubdivisionLinearMap_smul (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (a : R) (c : singularChainGroup R X n) :
    (barycentricSubdivisionLinearMap R X n).hom (a • c)
      = a • (barycentricSubdivisionLinearMap R X n).hom c := by
  exact map_smul (barycentricSubdivisionLinearMap R X n).hom a c

/-! ## 5. The singular boundary on generators -/

/-- The singular boundary map `∂ : C_{n+1}(X; R) → C_n(X; R)`, i.e. the
differential of the singular chain complex with coefficients in `R`. -/
noncomputable def singularBoundary (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    singularChainGroup R X (n + 1) ⟶ singularChainGroup R X n :=
  (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj X).d (n + 1) n

/-- **Coproduct-injection boundary formula.** Pre-composing the coproduct
injection of a basis simplex `σ` with the singular differential yields the
alternating sum of the coproduct injections of the boundary faces of `σ`:
`Sigma.ι σ ≫ ∂ = ∑ i (-1)^i • Sigma.ι (faceSimplex … i σ)`. -/
theorem singularBoundary_sigma_ι_formula (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X (n + 1)) :
    Sigma.ι (fun (_ : singularSimplices X (n + 1)) => ModuleCat.of R R) σ
        ≫ singularBoundary R X n
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R)
            (AlexanderWhitney.faceSimplex X n i σ) :=
  @SSet.ιChainComplex_d (ModuleCat R) _ _ _ (TopCat.toSSet.obj X) (ModuleCat.of R R) n σ

/-- **Singular boundary on a generator.** The differential `∂` of the singular
chain complex acts on a basis chain `[σ]` by the classical alternating sum over
boundary faces:
```text
∂[σ] = ∑_i (-1)^i [σ ∘ δ_i].
```
This is the concrete face/sign formula in the library's actual singular-chain
API; it is `AlternatingFaceMapComplex.obj_d_eq` specialised to the singular
simplicial module, with the integer signs `(-1)^i` interpreted in `R`. -/
theorem singularBoundary_chainGenerator_formula (R : Type) [CommRing R] (X : TopCat.{0})
    (n : ℕ) (σ : singularSimplices X (n + 1)) :
    (singularBoundary R X n).hom (chainGenerator R X (n + 1) σ)
      = ∑ i : Fin (n + 2),
          ((-1 : R) ^ i.val) • chainGenerator R X n (AlexanderWhitney.faceSimplex X n i σ) := by
  let F : Fin (n + 2) → (ModuleCat.of R R ⟶ singularChainGroup R X n) :=
    fun i => Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) (AlexanderWhitney.faceSimplex X n i σ)
  have h := singularBoundary_sigma_ι_formula R X n σ
  have h2 := congrArg (fun (f : ModuleCat.of R R ⟶ singularChainGroup R X n) => f.hom (1 : R)) h
  dsimp [chainGenerator] at h2
  have h_hom : (∑ (i : Fin (n + 2)), (-1 : ℤ) ^ (i : ℕ) • F i).hom (1 : R)
      = ∑ (i : Fin (n + 2)), (-1 : ℤ) ^ (i : ℕ) • (F i).hom (1 : R) := by simp
  have h_sum : ∑ (i : Fin (n + 2)), (-1 : ℤ) ^ (i : ℕ) • (F i).hom (1 : R)
      = ∑ i : Fin (n + 2), ((-1 : R) ^ i.val) • chainGenerator R X n (AlexanderWhitney.faceSimplex X n i σ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ (i : ℕ))]
    congr 1
    push_cast
    rfl
  exact (h2.trans h_hom).trans h_sum

end AffineBarycentricSubdivision
end SphereOddDegree
