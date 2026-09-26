/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Riccati.UnboundedExistence
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.BoundedGraphAcute
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Canonical graph-rotation transport for unbounded block operators

This leaf specializes the canonical partial-map pullback construction to the
completed complex direct rotation from the zero block graph to a bounded graph.
It keeps the transported operator domain explicit and records the projection
intertwining needed before the transformed operator can be identified with a
block-diagonal direct sum.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The zero graph and every bounded unbounded-block graph form an acute pair.
The adjective `unbounded` refers to the operator acting on the graph, not to
its bounded angular parametrization. -/
theorem zeroUnboundedGraph_isUniformlyAcute_unboundedBlockGraph
    (X : E0 →L[ℂ] E1) :
    IsUniformlyAcute
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1))
      (unboundedBlockGraph X) := by
  simpa [unboundedBlockGraph, blockGraph] using
    (zeroGraph_isUniformlyAcute_blockGraph X)

/-- Canonical complex rotation from the first coordinate graph to the graph of
`X`. -/
noncomputable def unboundedGraphRotation (X : E0 →L[ℂ] E1) :
    WithLp 2 (E0 × E1) →L[ℂ] WithLp 2 (E0 × E1) :=
  complexDirectRotation
    (unboundedBlockGraph (0 : E0 →L[ℂ] E1))
    (unboundedBlockGraph X)
    (zeroUnboundedGraph_isUniformlyAcute_unboundedBlockGraph X)

/-- The canonical graph rotation is norm preserving and onto. -/
theorem unboundedGraphRotation_unitary (X : E0 →L[ℂ] E1) :
    TauCeti.LinearPMap.IsUnitaryOperator (unboundedGraphRotation X) := by
  exact complexDirectRotation_unitary
    (unboundedBlockGraph (0 : E0 →L[ℂ] E1))
    (unboundedBlockGraph X)
    (zeroUnboundedGraph_isUniformlyAcute_unboundedBlockGraph X)

/-- Kernel and range form of bijectivity, suitable for constructing a
continuous linear equivalence from the canonical graph rotation. -/
theorem unboundedGraphRotation_ker_bot_range_top
    (X : E0 →L[ℂ] E1) :
    LinearMap.ker (unboundedGraphRotation X).toLinearMap = ⊥ ∧
      LinearMap.range (unboundedGraphRotation X).toLinearMap = ⊤ := by
  let W := unboundedGraphRotation X
  have hW : TauCeti.LinearPMap.IsUnitaryOperator W := unboundedGraphRotation_unitary X
  constructor
  · rw [LinearMap.ker_eq_bot]
    intro x y hxy
    have hxyW : W x = W y := by
      change unboundedGraphRotation X x = unboundedGraphRotation X y
      exact hxy
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    calc
      ‖x - y‖ = ‖W (x - y)‖ := (hW.1 (x - y)).symm
      _ = ‖W x - W y‖ := by rw [map_sub]
      _ = 0 := by rw [hxyW, sub_self, norm_zero]
  · rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨x, hx⟩ := hW.2 y
    exact ⟨x, hx⟩

/-- The canonical graph rotation bundled as a continuous linear equivalence. -/
noncomputable def unboundedGraphRotationEquiv (X : E0 →L[ℂ] E1) :
    WithLp 2 (E0 × E1) ≃L[ℂ] WithLp 2 (E0 × E1) :=
  ContinuousLinearEquiv.ofBijective (unboundedGraphRotation X)
    (unboundedGraphRotation_ker_bot_range_top X).1
    (unboundedGraphRotation_ker_bot_range_top X).2

/-- The bundled graph-rotation equivalence acts by the underlying graph rotation. -/
@[simp] theorem unboundedGraphRotationEquiv_apply
    (X : E0 →L[ℂ] E1) (z : WithLp 2 (E0 × E1)) :
    unboundedGraphRotationEquiv X z = unboundedGraphRotation X z :=
  rfl

/-- The equivalence underlying the graph rotation remains unitary. -/
theorem unboundedGraphRotationEquiv_unitary (X : E0 →L[ℂ] E1) :
    TauCeti.LinearPMap.IsUnitaryOperator
      (unboundedGraphRotationEquiv X).toContinuousLinearMap := by
  change TauCeti.LinearPMap.IsUnitaryOperator (unboundedGraphRotation X)
  exact unboundedGraphRotation_unitary X

/-- The graph-rotation equivalence intertwines the coordinate projection with
the projection onto the graph of `X`. -/
theorem unboundedGraphRotationEquiv_intertwines_projection
    (X : E0 →L[ℂ] E1) :
    (unboundedGraphRotationEquiv X).toContinuousLinearMap ∘L
        Submodule.starProjection (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) =
      Submodule.starProjection (unboundedBlockGraph X) ∘L
        (unboundedGraphRotationEquiv X).toContinuousLinearMap := by
  change unboundedGraphRotation X ∘L
        Submodule.starProjection (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) =
      Submodule.starProjection (unboundedBlockGraph X) ∘L unboundedGraphRotation X
  exact complexDirectRotation_intertwines
    (unboundedBlockGraph (0 : E0 →L[ℂ] E1))
    (unboundedBlockGraph X)
    (zeroUnboundedGraph_isUniformlyAcute_unboundedBlockGraph X)

/-- The graph-rotated block core in its canonical partial-map form. -/
noncomputable abbrev unboundedGraphRotationPullback
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    WithLp 2 (E0 × E1) →ₗ.[ℂ] WithLp 2 (E0 × E1) :=
  TauCeti.LinearPMap.pullback (unboundedBlockOperatorCore H)
    (unboundedGraphRotationEquiv X)

/-- Exact domain of the raw graph-rotated block core. -/
theorem mem_unboundedGraphRotationPullback_domain_iff
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) (z : WithLp 2 (E0 × E1)) :
    z ∈ (unboundedGraphRotationPullback H X).domain ↔
      unboundedGraphRotation X z ∈ (unboundedBlockOperatorCore H).domain :=
  Iff.rfl

/-- The raw graph-rotated block core is unitarily equivalent to the original
raw block core. -/
theorem unboundedGraphRotationPullback_unitaryEquivalent
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    TauCeti.LinearPMap.UnitaryEquivalent
      (unboundedGraphRotationPullback H X)
      (unboundedBlockOperatorCore H)
      (unboundedGraphRotationEquiv X).toContinuousLinearMap
      (unboundedGraphRotationEquiv X).symm.toContinuousLinearMap := by
  exact TauCeti.LinearPMap.pullback_unitaryEquivalent
    (unboundedBlockOperatorCore H)
    (unboundedGraphRotationEquiv X)
    (unboundedGraphRotationEquiv_unitary X)

end DavisKahanExt
end TauCeti
