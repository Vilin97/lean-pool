/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.UnboundedRotationTransport

/-!
# Transport of reducing subspaces through an unbounded graph rotation

This leaf proves the domain-sensitive reduction theorem needed for unbounded
block diagonalization.  A partial map pulled back through a continuous linear
equivalence reduces a subspace whenever the original map reduces the
transported subspace and the equivalence intertwines their orthogonal
projections.

The specialization to the canonical graph rotation shows that the pulled-back
unbounded block operator reduces the first coordinate summand and its
orthogonal complement.  This is the precise sense in which the transported
operator is block diagonal before its two coordinate restrictions are
constructed explicitly.

The three projection-intertwining lemmas below are pure orthogonal-projection
facts: they mention no operator at all, and are stated here only because this
is where the reduction transport first needs them.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- Intertwining the orthogonal projections onto `U` and `V` also intertwines
those onto their orthogonal complements. -/
theorem intertwines_orthogonal_projection_of_intertwines_projection
    (e : E ≃L[𝕜] E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hproj : e.toContinuousLinearMap ∘L U.starProjection =
      V.starProjection ∘L e.toContinuousLinearMap) :
    e.toContinuousLinearMap ∘L Uᗮ.starProjection =
      Vᗮ.starProjection ∘L e.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  change e (Uᗮ.starProjection x) = Vᗮ.starProjection (e x)
  rw [Submodule.starProjection_orthogonal_apply,
    Submodule.starProjection_orthogonal_apply, map_sub]
  have hx := congrArg (fun T : E →L[𝕜] E => T x) hproj
  change e (U.starProjection x) = V.starProjection (e x) at hx
  rw [hx]

omit [CompleteSpace E] in
/-- A projection-intertwining equivalence maps membership in the source
subspace to membership in the target subspace. -/
theorem map_mem_of_intertwines_projection
    (e : E ≃L[𝕜] E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hproj : e.toContinuousLinearMap ∘L U.starProjection =
      V.starProjection ∘L e.toContinuousLinearMap)
    {x : E} (hx : x ∈ U) : e x ∈ V := by
  rw [← Submodule.starProjection_eq_self_iff]
  have hintertwine := congrArg (fun T : E →L[𝕜] E => T x) hproj
  change e (U.starProjection x) = V.starProjection (e x) at hintertwine
  rw [Submodule.starProjection_eq_self_iff.mpr hx] at hintertwine
  exact hintertwine.symm

omit [CompleteSpace E] in
/-- The inverse of a projection-intertwining equivalence maps membership in the
target subspace back to membership in the source subspace. -/
theorem symm_map_mem_of_intertwines_projection
    (e : E ≃L[𝕜] E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hproj : e.toContinuousLinearMap ∘L U.starProjection =
      V.starProjection ∘L e.toContinuousLinearMap)
    {y : E} (hy : y ∈ V) : e.symm y ∈ U := by
  rw [← Submodule.starProjection_eq_self_iff]
  apply e.injective
  have hintertwine := congrArg (fun T : E →L[𝕜] E => T (e.symm y)) hproj
  change e (U.starProjection (e.symm y)) =
    V.starProjection (e (e.symm y)) at hintertwine
  rw [e.apply_symm_apply, Submodule.starProjection_eq_self_iff.mpr hy] at hintertwine
  simpa using hintertwine


omit [CompleteSpace E] in
/-- Reduction transports through a canonical partial-map pullback when the
equivalence intertwines the corresponding orthogonal projections. -/
theorem pullback_reducesSubspace_of_intertwines_projection
    (A : E →ₗ.[𝕜] E)
    (e : E ≃L[𝕜] E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hproj : e.toContinuousLinearMap ∘L U.starProjection =
      V.starProjection ∘L e.toContinuousLinearMap)
    (hred : TauCeti.LinearPMap.ReducesSubspace A V) :
    TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.pullback A e) U := by
  have hprojOrth : e.toContinuousLinearMap ∘L Uᗮ.starProjection =
      Vᗮ.starProjection ∘L e.toContinuousLinearMap :=
    intertwines_orthogonal_projection_of_intertwines_projection e U V hproj
  rcases hred with ⟨hVdom, hVOrthDom, hVinv, hVOrthInv⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    change e (U.starProjection (x : E)) ∈ A.domain
    have hintertwine := congrArg (fun T : E →L[𝕜] E => T (x : E)) hproj
    change e (U.starProjection (x : E)) =
      V.starProjection (e (x : E)) at hintertwine
    rw [hintertwine]
    exact hVdom (TauCeti.LinearPMap.pullbackDomainToOriginal A e x)
  · intro x
    change e (Uᗮ.starProjection (x : E)) ∈ A.domain
    have hintertwine := congrArg (fun T : E →L[𝕜] E => T (x : E)) hprojOrth
    change e (Uᗮ.starProjection (x : E)) =
      Vᗮ.starProjection (e (x : E)) at hintertwine
    rw [hintertwine]
    exact hVOrthDom (TauCeti.LinearPMap.pullbackDomainToOriginal A e x)
  · intro x hx
    -- Unfolded directly: `x : (pullback A e).domain` blocks a rewrite with
    -- `pullbackLinearMap_apply`, but the `change` itself is definitional.
    change e.symm (A (TauCeti.LinearPMap.pullbackDomainToOriginal A e x)) ∈ U
    apply symm_map_mem_of_intertwines_projection e U V hproj
    apply hVinv (TauCeti.LinearPMap.pullbackDomainToOriginal A e x)
    exact map_mem_of_intertwines_projection e U V hproj hx
  · intro x hx
    change e.symm (A (TauCeti.LinearPMap.pullbackDomainToOriginal A e x)) ∈ Uᗮ
    apply symm_map_mem_of_intertwines_projection e Uᗮ Vᗮ hprojOrth
    apply hVOrthInv (TauCeti.LinearPMap.pullbackDomainToOriginal A e x)
    exact map_mem_of_intertwines_projection e Uᗮ Vᗮ hprojOrth hx

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Reduction of a raw Riccati graph transports to reduction of the first
coordinate graph by the canonical graph-rotation pullback. -/
theorem unboundedGraphRotationPullback_reduces_zeroGraph
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1)
    (hred : TauCeti.LinearPMap.ReducesSubspace
      (unboundedBlockOperatorCore H) (unboundedBlockGraph X)) :
    TauCeti.LinearPMap.ReducesSubspace
      (unboundedGraphRotationPullback H X)
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) := by
  exact pullback_reducesSubspace_of_intertwines_projection
    (unboundedBlockOperatorCore H) (unboundedGraphRotationEquiv X)
    (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) (unboundedBlockGraph X)
    (unboundedGraphRotationEquiv_intertwines_projection X) hred

/-- The canonical partial-map coordinate-diagonal representative of a raw
unbounded block core. -/
noncomputable abbrev unboundedBlockDiagonalCore
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    WithLp 2 (E0 × E1) →ₗ.[ℂ] WithLp 2 (E0 × E1) :=
  unboundedGraphRotationPullback H X

/-- The raw diagonal representative reduces both coordinate graphs when the
original raw block core reduces the Riccati graph. -/
theorem unboundedBlockDiagonalCore_reduces_zeroGraph
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1)
    (hred : TauCeti.LinearPMap.ReducesSubspace
      (unboundedBlockOperatorCore H) (unboundedBlockGraph X)) :
    TauCeti.LinearPMap.ReducesSubspace
      (unboundedBlockDiagonalCore H X)
      (unboundedBlockGraph (0 : E0 →L[ℂ] E1)) :=
  unboundedGraphRotationPullback_reduces_zeroGraph H X hred

/-- The raw coordinate-diagonal representative is unitarily equivalent to
the original raw block core. -/
theorem unboundedBlockDiagonalCore_unitaryEquivalent
    (H : UnboundedBlockData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    TauCeti.LinearPMap.UnitaryEquivalent
      (unboundedBlockDiagonalCore H X)
      (unboundedBlockOperatorCore H)
      (unboundedGraphRotationEquiv X).toContinuousLinearMap
      (unboundedGraphRotationEquiv X).symm.toContinuousLinearMap :=
  unboundedGraphRotationPullback_unitaryEquivalent H X

end DavisKahanExt
end TauCeti
