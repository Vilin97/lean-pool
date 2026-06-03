/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.GaussianField.SchwartzNuclear.HermiteTensorProduct

/-!
# DyninMityaginSpace Instance for Schwartz Space

Derives the `DyninMityaginSpace (SchwartzMap D ℝ)` instance from the topological
isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq` constructed in
`SchwartzNuclear.HermiteTensorProduct`.

## Main result

- `schwartzDyninMityaginSpace`: the `DyninMityaginSpace` instance for Schwartz space
  on any nontrivial finite-dimensional real normed space.
-/

noncomputable section

open GaussianField TopologicalSpace

namespace GaussianField

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

/-- **Schwartz space is a nuclear Fréchet space.**

The instance uses the Schwartz seminorm family `(k, l) ↦ p_{k,l}` and a
basis/coefficient system derived from the topological isomorphism
`SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`.

Proved via the topological isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`
constructed from multi-dimensional Hermite analysis.
-/
noncomputable instance schwartzDyninMityaginSpace [Nontrivial D] :
    DyninMityaginSpace (SchwartzMap D ℝ) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    (fun (kl : ℕ × ℕ) => SchwartzMap.seminorm ℝ kl.1 kl.2)
    (schwartz_withSeminorms ℝ D ℝ)
    (schwartzRapidDecayEquiv D)

/-- Specialized `DyninMityaginSpace` instance for `SchwartzMap ℝ ℝ` using
`schwartzRapidDecayEquiv1D` directly, avoiding the `toEuclidean` detour.
This is preferred by instance resolution since `ℝ` is more specific than `D`.
-/
noncomputable instance schwartzDyninMityaginSpace1D :
    DyninMityaginSpace (SchwartzMap ℝ ℝ) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    (fun (kl : ℕ × ℕ) => SchwartzMap.seminorm ℝ kl.1 kl.2)
    (schwartz_withSeminorms ℝ ℝ ℝ)
    schwartzRapidDecayEquiv1D

/-- `HasBiorthogonalBasis` for `SchwartzMap ℝ ℝ` from the Hermite basis. -/
noncomputable instance schwartzHasBiorthogonalBasis1D :
    DyninMityaginSpace.HasBiorthogonalBasis (SchwartzMap ℝ ℝ) :=
  DyninMityaginSpace.ofRapidDecayEquiv_hasBiorthogonalBasis
    (fun (kl : ℕ × ℕ) => SchwartzMap.seminorm ℝ kl.1 kl.2)
    (schwartz_withSeminorms ℝ ℝ ℝ)
    schwartzRapidDecayEquiv1D

/-- Specialized `DyninMityaginSpace` instance for `SchwartzMap (EuclideanSpace ℝ (Fin (d+1))) ℝ`
using `schwartzRapidDecayEquivNd` directly, avoiding the `toEuclidean` detour.
This ensures that `DyninMityaginSpace.coeff` produces the Hermite coefficients from the
standard multi-index encoding, matching the basis used by `schwartzPeelOff`.
-/
noncomputable instance schwartzDyninMityaginSpaceEuclidean (d : ℕ) :
    DyninMityaginSpace (SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    (fun (kl : ℕ × ℕ) => SchwartzMap.seminorm ℝ kl.1 kl.2)
    (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (schwartzRapidDecayEquivNd d)

/-! ## Separability

`RapidDecaySeq` is separable because the basis vectors `basisVec m` span a dense subspace
(by `hasSum_basisVec`). Schwartz space inherits separability via the CLE
`schwartzRapidDecayEquiv`.
-/

/-- `RapidDecaySeq` is separable: the countable set `{basisVec m | m ∈ ℕ}` spans a dense
    subspace (every element is the limit of finite linear combinations by `hasSum_basisVec`).
-/
instance rapidDecaySeqSeparableSpace : SeparableSpace RapidDecaySeq := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  have h_dense : (Submodule.span ℝ (Set.range RapidDecaySeq.basisVec)).topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro a _
    exact mem_closure_of_tendsto (RapidDecaySeq.hasSum_basisVec a).tendsto_sum_nat
      (Filter.Eventually.of_forall fun s =>
        Submodule.sum_mem _ fun m _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))
  have h1 := (Set.countable_range RapidDecaySeq.basisVec).isSeparable.span (R := ℝ)
  have h2 := h1.closure
  have h3 : closure (↑(Submodule.span ℝ (Set.range RapidDecaySeq.basisVec)) :
      Set RapidDecaySeq) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, h_dense]; rfl
  rwa [h3] at h2

/-- **Schwartz space is separable.**

    Proved via the topological isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`:
    since `RapidDecaySeq` is separable (countable Hermite basis spans a dense subspace),
    and a CLE is a homeomorphism, Schwartz space is separable.
-/
instance schwartzSeparableSpace [Nontrivial D] :
    SeparableSpace (SchwartzMap D ℝ) := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  have h_range : Set.range (schwartzRapidDecayEquiv D).symm = Set.univ :=
    Function.Surjective.range_eq (schwartzRapidDecayEquiv D).symm.surjective
  rw [← h_range]
  exact isSeparable_range (schwartzRapidDecayEquiv D).symm.continuous

end GaussianField
