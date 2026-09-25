/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionSmallChains
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionIter
public import Mathlib.Tactic

/-!
# Smallness/carrier control of the subdivision homotopy terms

This file proves the *carrier control* needed for the small-simplices
quasi-isomorphism: the chain-homotopy witnesses relating iterated barycentric
subdivision to the identity become small (with respect to a given open cover)
when applied to small chains.

The accumulated homotopy operator was built in
`BarycentricSubdivisionIter.lean` as

```text
H^(N) = barycentricSubdivisionIterHomotopyLinearMap R X N
 = Σ_{r=0}^{N-1} (sd^r) ∘ H,
```

with `H = barycentricSubdivisionHomotopyLinearMap` the one-step homotopy and
`sd^r = barycentricSubdivisionIterLinearMap`. Its chain-level boundary formula
`barycentricSubdivisionIter_boundary_formula` reads
`c - sd^N(c) = ∂(H^(N) c) + H^(N)(∂ c)`.

## Key geometric fact (carrier control)

The one-step homotopy `H([σ])` is the pushforward, along `σ`, of a *fixed*
universal chain `T_n` on the standard simplex `Δⁿ`. Therefore **every** simplex
appearing in `H([σ])` has image contained in `image(σ)`. Consequently, if `σ`
is `𝒰`-small then `H([σ])` is a `𝒰`-small chain; and the same holds for the
iterated homotopy, because `sd` also preserves smallness (carriers of a
subdivision summand lie inside the carrier of the original simplex).

The clean statement underlying all of this is:

* `singularChainMap_mem_smallChainSubmodule` — the pushforward of *any* chain
 along a continuous map `f` whose image lies inside a member of the cover is a
 small chain.

From it we deduce:

* `subdivisionHomotopy_preserves_smallChains` — the one-step homotopy `H` maps
 small chains to small chains.
* `iteratedSubdivisionHomotopy_preserves_smallChains` — the accumulated homotopy
 `H^(N)` maps small chains to small chains (for every `N`).

Finally we combine with the project (`exists_iteratedSubdivision_chain_mem_smallChains`):

* `exists_iteratedSubdivision_homotopy_mem_smallChains` — for every chain `c`
 there is `N` such that `sd^N(c)` is small and the homotopy term of the small
 subdivided chain `H^(N)(sd^N c)` is small.
* `exists_iteratedSubdivision_homotopy_boundary_mem_smallChains` — the injectivity
 tool: if `b` has a small boundary `z = ∂b` (e.g. `z` is a small cycle bounding
 `b` globally), then there is `N` with both `sd^N(b)` small and the homotopy
 chain `H^(N)(z)` small. By the boundary formula these are exactly the chains
 needed to rewrite `z` as a boundary inside the small subcomplex.

## Faithfulness note

For an *arbitrary* (non-small) chain `c`, the homotopy term `H^(N)(c)` is **not**
small: the boundary formula forces `∂(H^(N) c) + H^(N)(∂ c) = c - sd^N(c)`, so the
carriers of `H^(N)(c)` must cover the carriers of `c` itself. This is why the
`exists`-theorems control the homotopy term of the *subdivided/small* chain (resp.
of the small boundary `z`), which is exactly what the project require; we do not
state the (false) claim that `H^(N)(c)` is small for arbitrary `c`.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory AlgebraicTopology Limits

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

variable {X : TopCat.{0}}

/-! ## 1. Carrier control for pushforward chains -/

/-
**Carrier control / pushforward smallness.** If a continuous map `f : Y ⟶ X`
has image contained in a member `U` of the open cover `𝒰` of `X`, then the
pushforward `f_#(c)` of *any* singular chain `c` on `Y` is a `𝒰`-small chain on
`X`: every basis simplex `σ` appearing in `c` is pushed to `f ∘ σ`, whose image
lies in `image(f) ⊆ U`.
-/
theorem singularChainMap_mem_smallChainSubmodule (R : Type) [CommRing R]
    {Y : TopCat.{0}} (𝒰 : OpenCoverData X) (n : ℕ) (f : Y ⟶ X)
    (hf : ∃ U ∈ 𝒰.sets, Set.range (ConcreteCategory.hom f) ⊆ U)
    (c : singularChainGroup R Y n) :
    (singularChainMap R f n).hom c ∈ smallChainSubmodule R X 𝒰 n := by
  have h_pushforward_small : ∀ (σ : singularSimplices Y n), (singularChainMap R f n).hom
    (chainGenerator R Y n σ) ∈ smallChainSubmodule R X 𝒰 n := by
    intro σ
    have h_small : IsSmallSimplex 𝒰 (pushSimplex f n σ) := by
      obtain ⟨ U, hU₁, hU₂ ⟩ := hf
      generalize_proofs at *; (
      exact ⟨U, hU₁, Set.range_subset_iff.mpr fun x =>
        hU₂ ⟨(singularSimplexAsContinuousMap Y n σ) x, by
          simp +decide [pushSimplex_continuousMap]⟩⟩)
    generalize_proofs at *; (exact (by
    exact singularChainMap_generator R f n σ ▸ chainGenerator_mem_smallChainSubmodule h_small) )
  generalize_proofs at *; (
  have h_span : c ∈ Submodule.span R (Set.range (chainGenerator R Y n)) := by
    exact chainGenerator_span_top R n ▸ Submodule.mem_top
  generalize_proofs at *; (
  refine Submodule.span_induction ?_ ?_ ?_ ?_ h_span <;> aesop ( simp_config := { singlePass :=
    true } );))

/-! ## 2. The one-step homotopy preserves small chains -/

/-
**The one-step subdivision homotopy `H` preserves small chains.** If `c` is a
`𝒰`-small `n`-chain, then `H(c)` is a `𝒰`-small `(n+1)`-chain. On a small
generator `[σ]`, `H([σ])` is the pushforward of the universal chain `T_n` along
`σ`, whose image lies in `image(σ) ⊆ U`.
-/
theorem subdivisionHomotopy_preserves_smallChains (R : Type) [CommRing R]
    (𝒰 : OpenCoverData X) (n : ℕ) :
    ∀ c ∈ smallChainSubmodule R X 𝒰 n,
      (barycentricSubdivisionHomotopyLinearMap R X n).hom c
        ∈ smallChainSubmodule R X 𝒰 (n + 1) := by
  intro c hc;
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc;
  · rintro _ ⟨ σ, hσ, rfl ⟩;
    convert singularChainMap_mem_smallChainSubmodule R 𝒰 ( n + 1 ) ( TopCat.ofHom (
      singularSimplexAsContinuousMap X n σ ) ) _ ( barycentricHomotopyUniversal R n ) using 1;
    · convert barycentricSubdivisionHomotopyLinearMap_apply_generator R X n σ using 1;
    · exact hσ;
  · simp +decide;
  · exact fun x y hx hy hx' hy' => by simpa using Submodule.add_mem _ hx' hy';
  · simp +zetaDelta only [map_smul] at *;
    exact fun a x hx hx' => Submodule.smul_mem _ _ hx'

/-! ## 3. The accumulated homotopy preserves small chains -/

/-
**The accumulated homotopy `H^(N)` preserves small chains.** Since
`H^(N) = Σ_{r<N} sd^r ∘ H`, with both `H` and every `sd^r` preserving smallness,
`H^(N)` maps `𝒰`-small `n`-chains to `𝒰`-small `(n+1)`-chains.
-/
theorem iteratedSubdivisionHomotopy_preserves_smallChains (R : Type) [CommRing R]
    (𝒰 : OpenCoverData X) (N n : ℕ) :
    ∀ c ∈ smallChainSubmodule R X 𝒰 n,
      barycentricSubdivisionIterHomotopyLinearMap R X N n c
        ∈ smallChainSubmodule R X 𝒰 (n + 1) := by
  induction N generalizing n with
  | zero =>
    simp +decide [ barycentricSubdivisionIterHomotopyLinearMap ];
  | succ N ih =>
    intro c hc; rw [ barycentricSubdivisionIterHomotopyLinearMap_succ ]; exact Submodule.add_mem
      _ ( ih n c hc ) ( barycentricSubdivisionIter_maps_smallChainSubmodule R 𝒰 N ( n + 1 ) _ (
      subdivisionHomotopy_preserves_smallChains R 𝒰 n c hc ) );

/-! ## 4. Existence theorems combining shrinking and carrier control -/

/--
**Subdivision-and-homotopy smallness.** For every chain `c` there is `N` with
`sd^N(c)` small and the homotopy term of the (now small) subdivided chain,
`H^(N)(sd^N c)`, small.

(The homotopy term is taken of the *small* subdivided chain `sd^N c`; this is the
form that is actually small. See the faithfulness note in the module docstring.)
-/
theorem exists_iteratedSubdivision_homotopy_mem_smallChains
    (𝒰 : OpenCoverData X) (R : Type) [CommRing R] (n : ℕ)
    (c : singularChainGroup R X n) :
    ∃ N : ℕ,
      barycentricSubdivisionIterLinearMap R X N n c ∈ smallChainSubmodule R X 𝒰 n
      ∧ barycentricSubdivisionIterHomotopyLinearMap R X N n
          (barycentricSubdivisionIterLinearMap R X N n c)
        ∈ smallChainSubmodule R X 𝒰 (n + 1) := by
  obtain ⟨N, hN⟩ := exists_iteratedSubdivision_chain_mem_smallChains 𝒰 R n c
  exact ⟨N, hN, iteratedSubdivisionHomotopy_preserves_smallChains R 𝒰 N n _ hN⟩

/--
**Injectivity tool: small boundary witness.** Suppose `b` is an `(n+1)`-chain
whose boundary `z = ∂b` is `𝒰`-small (for instance, `z` is a small cycle that
bounds `b` globally). Then there is `N` such that both

* `sd^N(b)` is a small `(n+1)`-chain, and
* the homotopy chain `H^(N)(z) = H^(N)(∂b)` relating `sd^N(z)` to `z` is a small
 `(n+1)`-chain.

Combined with the boundary formula
`z - sd^N(z) = ∂(H^(N) z) + H^(N)(∂ z)` (and `∂z = 0` when `z` is a cycle), these
are exactly the small chains needed to exhibit `z` as a boundary inside the small
subcomplex in the project.
-/
theorem exists_iteratedSubdivision_homotopy_boundary_mem_smallChains
    (𝒰 : OpenCoverData X) (R : Type) [CommRing R] (n : ℕ)
    (b : singularChainGroup R X (n + 1))
    (hz : (singularBoundary R X n).hom b ∈ smallChainSubmodule R X 𝒰 n) :
    ∃ N : ℕ,
      barycentricSubdivisionIterLinearMap R X N (n + 1) b
        ∈ smallChainSubmodule R X 𝒰 (n + 1)
      ∧ barycentricSubdivisionIterHomotopyLinearMap R X N n
          ((singularBoundary R X n).hom b)
        ∈ smallChainSubmodule R X 𝒰 (n + 1) := by
  obtain ⟨N, hN⟩ := exists_iteratedSubdivision_chain_mem_smallChains 𝒰 R (n + 1) b
  exact ⟨N, hN,
    iteratedSubdivisionHomotopy_preserves_smallChains R 𝒰 N n _ hz⟩

end AffineBarycentricSubdivision
end SphereOddDegree
