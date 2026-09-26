/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.UnboundedPublic

/-!
# Public strong unbounded Riccati API

This module exposes the completed Stream B construction through the original
public names.  The foundational declarations live in `UnboundedBasic`; the
operator, reduction, transport, and coordinate-restriction proofs live in
focused downstream leaves.

Existence is stated as the exact handoff owned by this stream: a selected
contractive reducing graph produces a strong solution.  Constructing that
selected graph from spectral-separation and small-coupling assumptions belongs
to the continuation branch.

The graph-rotation diagonalization is currently established over complex
Hilbert spaces.  Its orientation is from the coordinate-diagonal pullback to
the original block operator, matching the forward graph rotation from the zero
coordinate graph to the Riccati graph.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- Unbounded block operator on the explicit product domain. -/
noncomputable abbrev unboundedBlockOperator
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    WithLp 2 (E0 × E1) →ₗ.[𝕜] WithLp 2 (E0 × E1) :=
  constructedUnboundedBlockOperator H

/-- Domain-controlled graph invariance is equivalent to the strong Riccati
equation. -/
theorem graph_invariant_iff_strongRiccati
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    (PreservesRiccatiDomains H X ∧
      TauCeti.LinearPMap.InvariantSubspace (unboundedBlockOperator H)
        (unboundedBlockGraph X)) ↔
      StrongSolvesRiccati H X := by
  exact constructedUnboundedBlockGraph_invariant_iff_strongRiccati H X

/-- A continuation-selected contractive reducing graph yields the complete
strong unbounded Riccati solution package. -/
theorem exists_strongRiccati_solution
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (hselection : Nonempty (ContractiveReducingGraphSelection H)) :
    ∃ X : E0 →L[𝕜] E1,
      StrongSolvesRiccati H X ∧ ‖X‖ < 1 ∧
      TauCeti.LinearPMap.ReducesSubspace (unboundedBlockOperator H)
        (unboundedBlockGraph X) := by
  exact constructedStrongRiccatiSolution_of_selectedGraph H hselection

section Complex

variable {F0 : Type*} [NormedAddCommGroup F0] [InnerProductSpace ℂ F0]
  [CompleteSpace F0]
variable {F1 : Type*} [NormedAddCommGroup F1] [InnerProductSpace ℂ F1]
  [CompleteSpace F1]

/-- Coordinate-diagonal pullback of the complex unbounded block operator by
the canonical graph rotation. -/
noncomputable abbrev unboundedBlockDiagonalOperator
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := F0) (E1 := F1))
    (X : F0 →L[ℂ] F1) :
    WithLp 2 (F0 × F1) →ₗ.[ℂ] WithLp 2 (F0 × F1) :=
  unboundedBlockDiagonalCore H X

/-- Strong Riccati reduction gives domain-controlled complex block
diagonalization and identifies the two coordinate restrictions. -/
theorem unbounded_blockDiagonalization
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := F0) (E1 := F1))
    {X : F0 →L[ℂ] F1} (hX : StrongSolvesRiccati H X)
    (hred : TauCeti.LinearPMap.ReducesSubspace (unboundedBlockOperator H)
      (unboundedBlockGraph X)) :
    ∃ W Winv : WithLp 2 (F0 × F1) →L[ℂ] WithLp 2 (F0 × F1),
      TauCeti.LinearPMap.UnitaryEquivalent
        (unboundedBlockDiagonalOperator H X)
        (unboundedBlockOperator H) W Winv ∧
      W ∘L Submodule.starProjection (unboundedBlockGraph (0 : F0 →L[ℂ] F1)) =
        Submodule.starProjection (unboundedBlockGraph X) ∘L W ∧
      TauCeti.LinearPMap.ReducesSubspace
        (unboundedBlockDiagonalOperator H X)
        (unboundedBlockGraph (0 : F0 →L[ℂ] F1)) ∧
      TauCeti.LinearPMap.UnitaryEquivalent
        (TauCeti.LinearPMap.directSum
          (unboundedBlockDiagonalRestriction0 H X)
          (unboundedBlockDiagonalRestriction1 H X))
        (unboundedBlockDiagonalOperator H X)
        (ContinuousLinearMap.id ℂ _)
        (ContinuousLinearMap.id ℂ _) := by
  exact complex_unbounded_blockDiagonalization_of_strongSolution H hX hred

end Complex

end DavisKahanExt
end TauCeti
