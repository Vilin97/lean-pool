/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Riccati.UnboundedExistence
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.UnboundedDiagonalRestrictions

/-!
# Proof-complete public surface for unbounded Riccati reduction

This module aggregates the proof-complete unbounded Riccati leaves.  It keeps
spectral branch selection explicit: a selected contractive reducing graph is
converted to a strong solution by `UnboundedExistence`, while the construction
of that selected graph remains continuation work.

For complex Hilbert spaces, the canonical graph rotation transports the
coordinate-diagonal pullback to the original block operator.  The orientation
below follows that map: the forward unitary carries the zero coordinate graph
to the Riccati graph.  The two coordinate restrictions are exposed as a
separate identity-unitary equivalence with the rotated pullback.
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

/-- Canonical proof-complete block core over partial-map block data. -/
noncomputable abbrev constructedUnboundedBlockOperator
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    WithLp 2 (E0 × E1) →ₗ.[𝕜] WithLp 2 (E0 × E1) :=
  unboundedBlockOperatorCore H

/-- Public aggregate form of the domain-controlled graph-invariance
characterization. -/
theorem constructedUnboundedBlockGraph_invariant_iff_strongRiccati
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    (PreservesRiccatiDomains H X ∧
      TauCeti.LinearPMap.InvariantSubspace
        (constructedUnboundedBlockOperator H)
        (unboundedBlockGraph X)) ↔
      StrongSolvesRiccati H X := by
  exact unboundedBlockGraph_invariant_iff_strongRiccatiCore H X

/-- The continuation handoff, exposed from the aggregate module: once the
selected branch is supplied as a contractive reducing graph, the complete
strong Riccati package follows. -/
theorem constructedStrongRiccatiSolution_of_selectedGraph
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (hselection : Nonempty (ContractiveReducingGraphSelection H)) :
    ∃ X : E0 →L[𝕜] E1,
      StrongSolvesRiccati H X ∧ ‖X‖ < 1 ∧
      TauCeti.LinearPMap.ReducesSubspace
        (constructedUnboundedBlockOperator H)
        (unboundedBlockGraph X) := by
  exact exists_strongRiccati_solution_of_selected_reducing_graph H hselection

section Complex

variable {F0 : Type*} [NormedAddCommGroup F0] [InnerProductSpace ℂ F0]
  [CompleteSpace F0]
variable {F1 : Type*} [NormedAddCommGroup F1] [InnerProductSpace ℂ F1]
  [CompleteSpace F1]

/-- Full domain-controlled complex block diagonalization.

The forward unitary maps the coordinate-diagonal pullback to the original
block operator and carries the zero graph to the Riccati graph.  The last
conjunct identifies the pullback with the direct sum of its two coordinate
restrictions. -/
theorem complex_unbounded_blockDiagonalization
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := F0) (E1 := F1))
    (X : F0 →L[ℂ] F1)
    (hred : TauCeti.LinearPMap.ReducesSubspace
      (unboundedBlockOperatorCore H) (unboundedBlockGraph X)) :
    ∃ W Winv : WithLp 2 (F0 × F1) →L[ℂ] WithLp 2 (F0 × F1),
      TauCeti.LinearPMap.UnitaryEquivalent
        (unboundedBlockDiagonalCore H X)
        (unboundedBlockOperatorCore H) W Winv ∧
      W ∘L Submodule.starProjection (unboundedBlockGraph (0 : F0 →L[ℂ] F1)) =
        Submodule.starProjection (unboundedBlockGraph X) ∘L W ∧
      TauCeti.LinearPMap.ReducesSubspace
        (unboundedBlockDiagonalCore H X)
        (unboundedBlockGraph (0 : F0 →L[ℂ] F1)) ∧
      TauCeti.LinearPMap.UnitaryEquivalent
        (TauCeti.LinearPMap.directSum
          (unboundedBlockDiagonalRestriction0 H X)
          (unboundedBlockDiagonalRestriction1 H X))
        (unboundedBlockDiagonalCore H X)
        (ContinuousLinearMap.id ℂ _)
        (ContinuousLinearMap.id ℂ _) := by
  let W := (unboundedGraphRotationEquiv X).toContinuousLinearMap
  let Winv := (unboundedGraphRotationEquiv X).symm.toContinuousLinearMap
  refine ⟨W, Winv, ?_, ?_, ?_, ?_⟩
  · exact unboundedBlockDiagonalCore_unitaryEquivalent H X
  · exact unboundedGraphRotationEquiv_intertwines_projection X
  · exact unboundedBlockDiagonalCore_reduces_zeroGraph H X hred
  · exact unboundedBlockDiagonalCore_coordinateDirectSum H X hred

/-- Strong-solution form of the complex diagonalization theorem.  Reduction is
kept as a separate hypothesis because one-sided graph invariance alone does not
supply the orthogonal-complement domain decomposition. -/
theorem complex_unbounded_blockDiagonalization_of_strongSolution
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := F0) (E1 := F1))
    {X : F0 →L[ℂ] F1} (_hX : StrongSolvesRiccati H X)
    (hred : TauCeti.LinearPMap.ReducesSubspace
      (unboundedBlockOperatorCore H) (unboundedBlockGraph X)) :
    ∃ W Winv : WithLp 2 (F0 × F1) →L[ℂ] WithLp 2 (F0 × F1),
      TauCeti.LinearPMap.UnitaryEquivalent
        (unboundedBlockDiagonalCore H X)
        (unboundedBlockOperatorCore H) W Winv ∧
      W ∘L Submodule.starProjection (unboundedBlockGraph (0 : F0 →L[ℂ] F1)) =
        Submodule.starProjection (unboundedBlockGraph X) ∘L W ∧
      TauCeti.LinearPMap.ReducesSubspace
        (unboundedBlockDiagonalCore H X)
        (unboundedBlockGraph (0 : F0 →L[ℂ] F1)) ∧
      TauCeti.LinearPMap.UnitaryEquivalent
        (TauCeti.LinearPMap.directSum
          (unboundedBlockDiagonalRestriction0 H X)
          (unboundedBlockDiagonalRestriction1 H X))
        (unboundedBlockDiagonalCore H X)
        (ContinuousLinearMap.id ℂ _)
        (ContinuousLinearMap.id ℂ _) :=
  complex_unbounded_blockDiagonalization H X hred

end Complex

end DavisKahanExt
end TauCeti
