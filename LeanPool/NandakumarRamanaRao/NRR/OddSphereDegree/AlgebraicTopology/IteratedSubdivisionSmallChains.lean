/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionSmallSimplex
public import Mathlib.Tactic

/-! # Iterated Subdivision Small Chains -/

@[expose] public section

open scoped BigOperators
open CategoryTheory AlgebraicTopology Limits
open SphereOddDegree.AffineBarycentricSubdivision

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

variable {X : TopCat.{0}}
@[simp] theorem mvSimplexMap_barycentricSubdivSimplex (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (σ : singularSimplices X n) :
    mvSimplexMap (barycentricSubdivSimplex X n π σ)
      = (mvSimplexMap σ).comp (affineSubdivContinuousMap n π) := by
  rfl

theorem IsSmallSimplex.barycentricSubdivSimplex {𝒰 : OpenCoverData X} {n : ℕ}
    {σ : singularSimplices X n} (hσ : IsSmallSimplex 𝒰 σ) (π : Equiv.Perm (Fin (n + 1))) :
    IsSmallSimplex 𝒰 (barycentricSubdivSimplex X n π σ) := by
  obtain ⟨U, hU_mem, hU_sub⟩ := hσ
  refine ⟨U, hU_mem, ?_⟩
  rw [mvSimplexMap_barycentricSubdivSimplex]
  rw [ContinuousMap.coe_comp, Set.range_comp]
  rintro a ⟨x, ⟨hx_range, rfl⟩⟩
  exact hU_sub (Set.mem_range_self _)

/-- **One subdivision preserves small chains.** The degree-wise barycentric
subdivision maps the small-chain submodule into itself. -/
theorem barycentricSubdivision_maps_smallChainSubmodule (R : Type) [CommRing R]
    (𝒰 : OpenCoverData X) (n : ℕ) :
    ∀ c ∈ smallChainSubmodule R X 𝒰 n,
      (barycentricSubdivisionLinearMap R X n).hom c ∈ smallChainSubmodule R X 𝒰 n := by
  intro c hc
  have hle : smallChainSubmodule R X 𝒰 n ≤ Submodule.comap (barycentricSubdivisionLinearMap R X
    n).hom (smallChainSubmodule R X 𝒰 n) := by
    refine Submodule.span_le.mpr ?_
    rintro c ⟨σ, hσ, rfl⟩
    change (barycentricSubdivisionLinearMap R X n).hom (chainGenerator R X n σ) ∈
      smallChainSubmodule R X 𝒰 n
    rw [barycentricSubdivisionLinearMap_generator_sum]
    exact Submodule.sum_mem _ fun π _ => Submodule.smul_mem _ _
      (chainGenerator_mem_smallChainSubmodule (IsSmallSimplex.barycentricSubdivSimplex hσ π))
  exact hle hc

/-- **Every iterate preserves small chains.** -/
theorem barycentricSubdivisionIter_maps_smallChainSubmodule (R : Type) [CommRing R]
    (𝒰 : OpenCoverData X) (N n : ℕ) :
    ∀ c ∈ smallChainSubmodule R X 𝒰 n,
      barycentricSubdivisionIterLinearMap R X N n c ∈ smallChainSubmodule R X 𝒰 n := by
  induction N with
  | zero =>
    intro c hc
    rw [barycentricSubdivisionIterLinearMap_zero]
    exact hc
  | succ N ih =>
    intro c hc
    rw [barycentricSubdivisionIterLinearMap_succ']
    exact barycentricSubdivision_maps_smallChainSubmodule R 𝒰 n _ (ih c hc)

/-- `sd^(a+b) = sd^a ∘ sd^b` degree-wise. -/
theorem barycentricSubdivisionIterLinearMap_add (R : Type) [CommRing R] (a b n : ℕ)
    (c : singularChainGroup R X n) :
    barycentricSubdivisionIterLinearMap R X (a + b) n c
      = barycentricSubdivisionIterLinearMap R X a n
          (barycentricSubdivisionIterLinearMap R X b n c) := by
  induction a generalizing c with
  | zero =>
    rw [zero_add, barycentricSubdivisionIterLinearMap_zero]
  | succ a ih =>
    rw [Nat.succ_add, barycentricSubdivisionIterLinearMap_succ',
        barycentricSubdivisionIterLinearMap_succ', ih]

/-- **Monotonicity in the number of subdivisions.** If `sd^N c` is a small chain
and `N ≤ M`, then `sd^M c` is a small chain. -/
theorem sdIter_mem_smallChainSubmodule_mono (R : Type) [CommRing R]
    (𝒰 : OpenCoverData X) {N M n : ℕ} (hNM : N ≤ M) {c : singularChainGroup R X n}
    (hc : barycentricSubdivisionIterLinearMap R X N n c ∈ smallChainSubmodule R X 𝒰 n) :
    barycentricSubdivisionIterLinearMap R X M n c ∈ smallChainSubmodule R X 𝒰 n := by
  have heq : M = (M - N) + N := (Nat.sub_add_cancel hNM).symm
  rw [heq, barycentricSubdivisionIterLinearMap_add]
  exact barycentricSubdivisionIter_maps_smallChainSubmodule R 𝒰 (M - N) n _ hc

/-- The basis generators `[σ]` span the singular chain group (it is the free
`R`-module on singular simplices). -/
theorem chainGenerator_span_top (R : Type) [CommRing R] (n : ℕ) :
    Submodule.span R (Set.range (chainGenerator R X n)) = ⊤ := by
  have hq_zero : (ModuleCat.ofHom (Submodule.mkQ (Submodule.span R (Set.range (chainGenerator R
    X n)))) : (singularChainGroup R X n) ⟶ ModuleCat.of R ((singularChainGroup R X n) ⧸
    Submodule.span R (Set.range (chainGenerator R X n)))) = 0 := by
    apply Sigma.hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change Submodule.Quotient.mk (chainGenerator R X n σ) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span (Set.mem_range_self σ)
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  rw [← Submodule.Quotient.mk_eq_zero]
  have h_val := congr_arg (fun (f : (singularChainGroup R X n) ⟶ ModuleCat.of R
    ((singularChainGroup R X n) ⧸ Submodule.span R (Set.range (chainGenerator R X n)))) => f.hom
    x) hq_zero
  exact h_val

/-- **Main theorem.** For every singular chain `c` and every open cover `𝒰`,
some iterated barycentric subdivision `sdᴺ(c)` lies in the submodule of
`𝒰`-small chains. -/
theorem exists_iteratedSubdivision_chain_mem_smallChains
    (𝒰 : OpenCoverData X) (R : Type) [CommRing R] (n : ℕ) (c : singularChainGroup R X n) :
    ∃ N : ℕ,
      barycentricSubdivisionIterLinearMap R X N n c ∈ smallChainSubmodule R X 𝒰 n := by
  have h_chain_span : Submodule.span R (Set.range (chainGenerator R X n)) = ⊤ :=
    chainGenerator_span_top R n
  have hc : c ∈ Submodule.span R (Set.range (chainGenerator R X n)) := by
    rw [h_chain_span]
    exact Submodule.mem_top
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, rfl⟩ := hx
    exact exists_iteratedSubdivision_generator_mem_smallChains R n σ 𝒰
  | zero =>
    exact ⟨0, by rw [barycentricSubdivisionIterLinearMap_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨Nx, hNx⟩ := hx
    obtain ⟨Ny, hNy⟩ := hy
    refine ⟨max Nx Ny, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (sdIter_mem_smallChainSubmodule_mono R 𝒰 (le_max_left _ _) hNx)
                           (sdIter_mem_smallChainSubmodule_mono R 𝒰 (le_max_right _ _) hNy)
  | smul a x _ hx =>
    obtain ⟨N, hN⟩ := hx
    refine ⟨N, ?_⟩
    rw [map_smul]
    exact Submodule.smul_mem _ _ hN

end AffineBarycentricSubdivision
end SphereOddDegree
