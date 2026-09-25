/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
public import Mathlib.Tactic

/-!
# A graph-Hilbert model for fourth-order endpoint traces

Endpoint traces are continuous in a Sobolev or graph norm, not in the ambient
`L²` norm.  Consequently the maximal fourth-derivative domain should first be
represented by its own Hilbert space `V`, equipped with a continuous injective
embedding into the ambient Hilbert space `H`.

This file packages that representation and constructs the free boundary
subspace as the joint kernel of four continuous trace maps.  The free subspace
is automatically closed and complete.  It also supplies the algebraic ambient
domain and the fourth derivative transported to that domain.

The remaining analytic tasks are cleanly separated:

* construct the concrete interval graph space `V`;
* prove density of the free embedding;
* prove closedness of the transported graph;
* prove the Green and energy identities by density from the smooth core.
-/

@[expose] public section

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

/-- Maximal fourth-order graph space with continuous endpoint traces. -/
structure FourthOrderTraceModel where
  /-- The continuous injective embedding of the fourth-order graph space into the ambient space. -/
  embed : V →L[𝕜] H
  embed_injective : Function.Injective embed
  /-- The continuous operator representing the fourth derivative. -/
  fourth : V →L[𝕜] H
  /-- The continuous trace of the second derivative at the left endpoint. -/
  traceSecondLeft : V →L[𝕜] 𝕜
  /-- The continuous trace of the third derivative at the left endpoint. -/
  traceThirdLeft : V →L[𝕜] 𝕜
  /-- The continuous trace of the second derivative at the right endpoint. -/
  traceSecondRight : V →L[𝕜] 𝕜
  /-- The continuous trace of the third derivative at the right endpoint. -/
  traceThirdRight : V →L[𝕜] 𝕜

namespace FourthOrderTraceModel

/-- Joint kernel of the four free-end traces. -/
noncomputable def freeSubspace (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    Submodule 𝕜 V :=
  D.traceSecondLeft.ker ⊓ D.traceThirdLeft.ker ⊓
    D.traceSecondRight.ker ⊓ D.traceThirdRight.ker

omit [CompleteSpace H] [CompleteSpace V] in
/-- Membership in the free subspace is exactly the four endpoint conditions. -/
theorem mem_freeSubspace_iff
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) (x : V) :
    x ∈ D.freeSubspace ↔
      D.traceSecondLeft x = 0 ∧
      D.traceThirdLeft x = 0 ∧
      D.traceSecondRight x = 0 ∧
      D.traceThirdRight x = 0 := by
  simp [freeSubspace, and_assoc]

omit [CompleteSpace H] [CompleteSpace V] in
/-- The joint trace kernel is closed in the graph Hilbert space. -/
theorem isClosed_freeSubspace
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    IsClosed (D.freeSubspace : Set V) := by
  simpa [freeSubspace] using
    (((D.traceSecondLeft.isClosed_ker.inter D.traceThirdLeft.isClosed_ker).inter
      D.traceSecondRight.isClosed_ker).inter D.traceThirdRight.isClosed_ker)

/-- The free trace kernel inherits completeness. -/
noncomputable instance freeSubspaceCompleteSpace
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    CompleteSpace D.freeSubspace :=
  D.isClosed_freeSubspace.completeSpace_coe

/-- Ambient embedding restricted to the free trace kernel. -/
noncomputable def freeEmbed
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.freeSubspace →L[𝕜] H :=
  D.embed.comp (Submodule.subtypeL D.freeSubspace)

/-- Fourth derivative restricted to the free trace kernel. -/
noncomputable def freeFourth
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.freeSubspace →L[𝕜] H :=
  D.fourth.comp (Submodule.subtypeL D.freeSubspace)

omit [CompleteSpace H] [CompleteSpace V] in
/-- The free embedding, unfolded. -/
@[simp] theorem freeEmbed_apply
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.freeSubspace) :
    D.freeEmbed x = D.embed (x : V) := rfl

omit [CompleteSpace H] [CompleteSpace V] in
/-- The fourth-order operator on the free model, unfolded. -/
@[simp] theorem freeFourth_apply
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.freeSubspace) :
    D.freeFourth x = D.fourth (x : V) := rfl

omit [CompleteSpace H] [CompleteSpace V] in
/-- The restricted ambient embedding remains injective. -/
theorem freeEmbed_injective
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    Function.Injective D.freeEmbed := by
  intro x y hxy
  apply Subtype.ext
  exact D.embed_injective hxy

/-- Ambient operator domain obtained from the free graph space. -/
noncomputable def freeAmbientDomain
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    Submodule 𝕜 H :=
  LinearMap.range D.freeEmbed.toLinearMap

/-- Linear equivalence from the free graph space onto its ambient image. -/
noncomputable def freeRangeEquiv
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.freeSubspace ≃ₗ[𝕜] D.freeAmbientDomain :=
  LinearEquiv.ofInjective D.freeEmbed.toLinearMap D.freeEmbed_injective

/-- Recover the graph-space representative of an ambient domain vector. -/
noncomputable def freeAmbientInverse
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.freeAmbientDomain →ₗ[𝕜] D.freeSubspace :=
  D.freeRangeEquiv.symm.toLinearMap

/-- Fourth derivative transported to the ambient domain. -/
noncomputable def freeFourthAmbient
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.freeAmbientDomain →ₗ[𝕜] H :=
  D.freeFourth.toLinearMap.comp D.freeAmbientInverse

omit [CompleteSpace H] [CompleteSpace V] in
/-- The ambient inverse undoes the free embedding. -/
theorem freeAmbientInverse_freeEmbed
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.freeSubspace) :
    D.freeAmbientInverse
      ⟨D.freeEmbed x,
        LinearMap.mem_range_self D.freeEmbed.toLinearMap x⟩ = x := by
  change D.freeRangeEquiv.symm (D.freeRangeEquiv x) = x
  exact D.freeRangeEquiv.symm_apply_apply x

omit [CompleteSpace H] [CompleteSpace V] in
/-- The ambient fourth-order operator agrees with the model one through the embedding. -/
theorem freeFourthAmbient_freeEmbed
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.freeSubspace) :
    D.freeFourthAmbient
      ⟨D.freeEmbed x,
        LinearMap.mem_range_self D.freeEmbed.toLinearMap x⟩ =
      D.freeFourth x := by
  change D.freeFourth
      (D.freeAmbientInverse
        ⟨D.freeEmbed x,
          LinearMap.mem_range_self D.freeEmbed.toLinearMap x⟩) =
    D.freeFourth x
  rw [D.freeAmbientInverse_freeEmbed]

omit [CompleteSpace H] [CompleteSpace V] in
/-- Density of a concrete smooth free core inside the ambient Hilbert space is
 enough to prove density of the transported free operator domain. -/
theorem dense_freeAmbientDomain_of_dense_subset_range
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    {S : Set H} (hS : Dense S)
    (hsub : S ⊆ Set.range D.freeEmbed) :
    Dense (D.freeAmbientDomain : Set H) := by
  apply hS.mono
  intro x hx
  obtain ⟨y, rfl⟩ := hsub hx
  exact LinearMap.mem_range_self D.freeEmbed.toLinearMap y

omit [CompleteSpace H] [CompleteSpace V] in
/-- A dense free embedding gives a dense ambient operator domain. -/
theorem dense_freeAmbientDomain
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (hdense : DenseRange D.freeEmbed) :
    Dense (D.freeAmbientDomain : Set H) := by
  simpa [freeAmbientDomain, DenseRange, LinearMap.coe_range] using hdense

/-- The trace model as a partial map on the ambient space.

Density and graph closedness are properties of this map, proved separately; the
model itself only has to supply the domain and the action. -/
noncomputable def toPartialMap
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) : H →ₗ.[𝕜] H where
  domain := D.freeAmbientDomain
  toFun := D.freeFourthAmbient

omit [CompleteSpace H] [CompleteSpace V] in
/-- The domain of the derived partial map. -/
@[simp] theorem toPartialMap_domain
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.toPartialMap.domain = D.freeAmbientDomain := rfl

omit [CompleteSpace H] [CompleteSpace V] in
/-- Its action, which is the model's fourth-order operator. -/
@[simp] theorem toPartialMap_apply
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.freeAmbientDomain) :
    D.toPartialMap x = D.freeFourthAmbient x := rfl

end FourthOrderTraceModel

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
