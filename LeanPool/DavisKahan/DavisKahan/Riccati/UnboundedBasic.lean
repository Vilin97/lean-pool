/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed

/-!
# Foundational definitions for strong unbounded Riccati theory

This module contains the shared block data, graph, and domain definitions used
by the proof leaves.  It intentionally contains no spectral-selection or
diagonalization theorem, so downstream leaves can import it without creating a
cycle through the public API.

The diagonal blocks are Mathlib `LinearPMap`s: density, closedness, and
self-adjointness are recorded as fields of the data rather than bundled into a
local operator type.  Unitary transport of a partial map is the canonical
`TauCeti.LinearPMap.UnitaryEquivalent`, and needs no local restatement.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- Unbounded diagonal block data with bounded off-diagonal coupling, in the
canonical partial-map representation.  Density, closedness, and
self-adjointness are explicit properties rather than fields of an operator
bundle. -/
structure UnboundedBlockData where
  A0 : E0 →ₗ.[𝕜] E0
  A1 : E1 →ₗ.[𝕜] E1
  B01 : E1 →L[𝕜] E0
  B10 : E0 →L[𝕜] E1
  dense0 : Dense (A0.domain : Set E0)
  dense1 : Dense (A1.domain : Set E1)
  closed0 : A0.IsClosed
  closed1 : A1.IsClosed
  selfAdjoint0 : _root_.IsSelfAdjoint A0
  selfAdjoint1 : _root_.IsSelfAdjoint A1
  offDiagonalAdjoint : ∀ x y, ⟪B01 y, x⟫_𝕜 = ⟪y, B10 x⟫_𝕜

namespace UnboundedBlockData

/-- The first diagonal block is symmetric on its operator domain.  This is the
form the Riccati estimates consume; self-adjointness is the stronger field. -/
theorem isSymmetric0
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    TauCeti.LinearPMap.IsSymmetric H.A0 := by
  have hformal := LinearPMap.adjoint_isFormalAdjoint (T := H.A0) H.dense0
  rw [LinearPMap.isSelfAdjoint_def.mp H.selfAdjoint0] at hformal
  intro x y
  exact hformal x y

/-- The second diagonal block is symmetric on its operator domain. -/
theorem isSymmetric1
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    TauCeti.LinearPMap.IsSymmetric H.A1 := by
  have hformal := LinearPMap.adjoint_isFormalAdjoint (T := H.A1) H.dense1
  rw [LinearPMap.isSelfAdjoint_def.mp H.selfAdjoint1] at hformal
  intro x y
  exact hformal x y

end UnboundedBlockData

/-- A bounded angular operator preserves the unbounded diagonal domains. -/
def PreservesRiccatiDomains
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∀ x : H.A0.domain, X (x : E0) ∈ H.A1.domain

/-- Strong Riccati solution, including the domain condition. -/
def StrongSolvesRiccati
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∃ hdom : PreservesRiccatiDomains H X,
    ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ -
        X (H.A0 x) -
        X (H.B01 (X (x : E0))) + H.B10 (x : E0) = 0

/-- Graph subspace of a bounded angular operator in the Hilbert direct sum. -/
noncomputable def unboundedBlockGraph (X : E0 →L[𝕜] E1) :
    Submodule 𝕜 (WithLp 2 (E0 × E1)) :=
  LinearMap.range ((WithLp.linearEquiv 2 𝕜 (E0 × E1)).symm.toLinearMap ∘ₗ
    LinearMap.id.prod X.toLinearMap)

/-- The block graph of an unbounded Riccati configuration is orthogonally complemented. -/
noncomputable instance unboundedBlockGraph_hasOrthogonalProjection
    (X : E0 →L[𝕜] E1) :
    (unboundedBlockGraph X).HasOrthogonalProjection := by
  set G : E0 →L[𝕜] WithLp 2 (E0 × E1) :=
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).symm :
        (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) ∘L
      (ContinuousLinearMap.id 𝕜 E0).prod X with hG
  have hGmem : ∀ u : E0, G u ∈ unboundedBlockGraph X := fun u => ⟨u, rfl⟩
  have hGfix : ∀ z ∈ unboundedBlockGraph X,
      G (WithLp.fstL 2 𝕜 E0 E1 z) = z := by
    intro z hz
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hz
    rw [← hu]
    rfl
  have hclosed : IsClosed ((unboundedBlockGraph X : Submodule 𝕜 _) :
      Set (WithLp 2 (E0 × E1))) := by
    rw [← isSeqClosed_iff_isClosed]
    intro seq y hseq hlim
    have hfix : ∀ n, seq n = G (WithLp.fstL 2 𝕜 E0 E1 (seq n)) :=
      fun n => (hGfix _ (hseq n)).symm
    have hlim2 : Filter.Tendsto seq Filter.atTop
        (nhds (G (WithLp.fstL 2 𝕜 E0 E1 y))) := by
      refine Filter.Tendsto.congr (fun n => (hfix n).symm) ?_
      exact (((G ∘L WithLp.fstL 2 𝕜 E0 E1)).continuous.tendsto y).comp hlim
    have hy : y = G (WithLp.fstL 2 𝕜 E0 E1 y) :=
      tendsto_nhds_unique hlim hlim2
    rw [hy]
    exact hGmem _
  have : CompleteSpace (unboundedBlockGraph X) := hclosed.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

end DavisKahanExt
end TauCeti
