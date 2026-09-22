/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SmallChains
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionChainMap

/-!
# The small-chain complex and its inclusion into singular chains

For an open cover `𝒰` of a space `X`, this file packages the degree-wise
small-chain submodules `smallChainSubmodule R X 𝒰 n` (from `SmallChains.lean`)
into a chain complex

```text
C_*^𝒰(X; R)
```

whose differential is the restriction of the singular boundary
(`singularBoundary_maps_smallChainSubmodule` guarantees the restriction is
well-defined), and defines the inclusion chain map

```text
C_*^𝒰(X; R) ⟶ C_*(X; R).
```

## Main definitions

* `SphereOddDegree.smallBoundary` — the restriction of the singular boundary to
 the small-chain submodules.
* `SphereOddDegree.smallChainComplex` — the chain complex of small singular
 chains.
* `SphereOddDegree.smallGenerator` — the small generator associated to a small
 singular simplex, as an element of the degree-`n` small-chain submodule.
* `SphereOddDegree.smallChainsInclusion` — the inclusion chain map into the full
 singular chain complex.

## Main results

* `SphereOddDegree.smallChainsInclusion_f_apply` — the inclusion is degreewise
 the natural inclusion of the submodule.
* `SphereOddDegree.smallChainsInclusion_generator` — the inclusion sends a small
 generator to the corresponding singular basis chain.
* `SphereOddDegree.smallChainsInclusion_boundary_compatible` — the inclusion
 commutes with the restricted differential and the full singular boundary.

We do **not** prove here that `smallChainsInclusion` is a quasi-isomorphism.
-/

open CategoryTheory AlgebraicTopology
open SphereOddDegree.AffineBarycentricSubdivision

namespace SphereOddDegree

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-! ## 1. The restricted boundary -/

/-- The restriction of the singular boundary `∂ : C_{n+1}(X; R) → C_n(X; R)` to
the small-chain submodules. Well-defined by
`singularBoundary_maps_smallChainSubmodule`. -/
noncomputable def smallBoundary (R : Type) [CommRing R] (X : TopCat.{0})
    (𝒰 : OpenCoverData X) (n : ℕ) :
    ModuleCat.of R (smallChainSubmodule R X 𝒰 (n + 1)) ⟶
      ModuleCat.of R (smallChainSubmodule R X 𝒰 n) :=
  ModuleCat.ofHom
    ((singularBoundary R X n).hom.restrict (singularBoundary_maps_smallChainSubmodule n))

@[simp] theorem smallBoundary_hom_apply
    {𝒰 : OpenCoverData X} (n : ℕ) (c : smallChainSubmodule R X 𝒰 (n + 1)) :
    ((smallBoundary R X 𝒰 n).hom c : singularChainGroup R X n)
      = (singularBoundary R X n).hom (c : singularChainGroup R X (n + 1)) := by
  rfl

/-- The composite `∂ ∘ ∂` of restricted boundaries vanishes. -/
theorem smallBoundary_comp_smallBoundary
    {𝒰 : OpenCoverData X} (n : ℕ) :
    smallBoundary R X 𝒰 (n + 1) ≫ smallBoundary R X 𝒰 n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change (singularBoundary R X n).hom ((singularBoundary R X (n + 1)).hom (c : singularChainGroup R X (n + 2))) = 0
  have h := (singularChainComplex R X).d_comp_d (n + 2) (n + 1) n
  have happ := congrArg (fun (m : (singularChainComplex R X).X (n + 2) ⟶ (singularChainComplex R X).X n) => m.hom (c : singularChainGroup R X (n + 2))) h
  exact happ

/-! ## 2. The small-chain complex -/

/-- **The small-chain complex** `C_*^𝒰(X; R)`. In degree `n` the object is the
small-chain submodule `smallChainSubmodule R X 𝒰 n`; the differential is the
restricted singular boundary `smallBoundary`. -/
noncomputable def smallChainComplex (R : Type) [CommRing R] (X : TopCat.{0})
    (𝒰 : OpenCoverData X) : ChainComplex (ModuleCat.{0} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (smallChainSubmodule R X 𝒰 n))
    (fun n => smallBoundary R X 𝒰 n)
    (fun n => smallBoundary_comp_smallBoundary n)

@[simp] theorem smallChainComplex_X
    {𝒰 : OpenCoverData X} (n : ℕ) :
    (smallChainComplex R X 𝒰).X n = ModuleCat.of R (smallChainSubmodule R X 𝒰 n) :=
  rfl

@[simp] theorem smallChainComplex_d
    {𝒰 : OpenCoverData X} (n : ℕ) :
    (smallChainComplex R X 𝒰).d (n + 1) n = smallBoundary R X 𝒰 n :=
  @ChainComplex.of_d (ModuleCat.{0} R) _ _ ℕ _ _ _
    (fun n => ModuleCat.of R (smallChainSubmodule R X 𝒰 n))
    (fun n => smallBoundary R X 𝒰 n) n

/-! ## 3. Small generators -/

/-- The small generator associated to a `𝒰`-small singular simplex `σ`, as an
element of the degree-`n` small-chain submodule. -/
noncomputable def smallGenerator {𝒰 : OpenCoverData X} {n : ℕ}
    (σ : singularSimplices X n) (hσ : IsSmallSimplex 𝒰 σ) :
    smallChainSubmodule R X 𝒰 n :=
  ⟨chainGenerator R X n σ, chainGenerator_mem_smallChainSubmodule hσ⟩

@[simp] theorem smallGenerator_val {𝒰 : OpenCoverData X} {n : ℕ}
    (σ : singularSimplices X n) (hσ : IsSmallSimplex 𝒰 σ) :
    ((smallGenerator (R := R) σ hσ) : singularChainGroup R X n) = chainGenerator R X n σ :=
  rfl

/-! ## 4. The inclusion chain map -/

/-- **The inclusion chain map** `C_*^𝒰(X; R) ⟶ C_*(X; R)`. Degreewise it is the
natural inclusion of the small-chain submodule into the singular chain group. -/
noncomputable def smallChainsInclusion (R : Type) [CommRing R] (X : TopCat.{0})
    (𝒰 : OpenCoverData X) : smallChainComplex R X 𝒰 ⟶ singularChainComplex R X where
  f n := ModuleCat.ofHom (smallChainSubmodule R X 𝒰 n).subtype
  comm' i j hij := by
    subst hij
    rw [smallChainComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    rfl

/-- The inclusion is, degreewise, the natural inclusion of the submodule:
its underlying map sends `c` to its value `c.val`. -/
theorem smallChainsInclusion_f_apply
    {𝒰 : OpenCoverData X} (n : ℕ) (c : smallChainSubmodule R X 𝒰 n) :
    ((smallChainsInclusion R X 𝒰).f n).hom c = (c : singularChainGroup R X n) :=
  rfl

/-- The inclusion sends a small generator to the corresponding singular basis
chain. -/
theorem smallChainsInclusion_generator {𝒰 : OpenCoverData X} {n : ℕ}
    (σ : singularSimplices X n) (hσ : IsSmallSimplex 𝒰 σ) :
    ((smallChainsInclusion R X 𝒰).f n).hom (smallGenerator σ hσ)
      = chainGenerator R X n σ := by
  rw [smallChainsInclusion_f_apply, smallGenerator_val]

/-- **Boundary compatibility.** The inclusion commutes with the restricted
differential of the small complex and the full singular boundary. -/
theorem smallChainsInclusion_boundary_compatible
    {𝒰 : OpenCoverData X} (n : ℕ) (c : smallChainSubmodule R X 𝒰 (n + 1)) :
    ((smallChainsInclusion R X 𝒰).f n).hom ((smallBoundary R X 𝒰 n).hom c)
      = (singularBoundary R X n).hom
          (((smallChainsInclusion R X 𝒰).f (n + 1)).hom c) := by
  rw [smallChainsInclusion_f_apply, smallChainsInclusion_f_apply, smallBoundary_hom_apply]

end SphereOddDegree
