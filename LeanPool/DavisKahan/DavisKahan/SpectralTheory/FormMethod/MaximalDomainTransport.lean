/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.TraceKernelModel
public import Mathlib.Tactic

/-!
# Transport of the maximal fourth-order graph space into the ambient Hilbert space

`FourthOrderTraceModel` begins with an abstract graph Hilbert space `V`.  The
paper-facing analytic interface instead expects actual submodules of the
ambient `L²` space.  This file transports the maximal domain, fourth
derivative, and all four traces across the injective embedding.

The free ambient domain from `TraceKernelModel` is then proved to be exactly
the joint kernel of the transported traces inside the maximal ambient domain.
-/

@[expose] public section

open Set
open scoped InnerProductSpace

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

namespace FourthOrderTraceModel

/-- Ambient image of the maximal graph Hilbert space. -/
noncomputable def maximalAmbientDomain
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) : Submodule 𝕜 H :=
  LinearMap.range D.embed.toLinearMap

/-- Equivalence from the graph Hilbert space to its ambient image. -/
noncomputable def maximalRangeEquiv
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    V ≃ₗ[𝕜] D.maximalAmbientDomain :=
  LinearEquiv.ofInjective D.embed.toLinearMap D.embed_injective

/-- Recover the graph-space representative of a maximal ambient-domain
vector. -/
noncomputable def maximalAmbientInverse
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.maximalAmbientDomain →ₗ[𝕜] V :=
  D.maximalRangeEquiv.symm.toLinearMap

omit [CompleteSpace H] [CompleteSpace V] in
/-- The ambient inverse undoes the embedding. -/
@[simp] theorem maximalAmbientInverse_embed
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) (x : V) :
    D.maximalAmbientInverse
      ⟨D.embed x, LinearMap.mem_range_self D.embed.toLinearMap x⟩ = x := by
  change D.maximalRangeEquiv.symm (D.maximalRangeEquiv x) = x
  exact D.maximalRangeEquiv.symm_apply_apply x

omit [CompleteSpace H] [CompleteSpace V] in
/-- And the embedding undoes the ambient inverse, so the two are mutually inverse on the
maximal domain. -/
@[simp] theorem embed_maximalAmbientInverse
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.maximalAmbientDomain) :
    D.embed (D.maximalAmbientInverse x) = (x : H) := by
  have h := D.maximalRangeEquiv.apply_symm_apply x
  exact congrArg Subtype.val h

/-- Fourth derivative transported to the ambient maximal domain. -/
noncomputable def maximalFourthAmbient
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.maximalAmbientDomain →ₗ[𝕜] H :=
  D.fourth.toLinearMap.comp D.maximalAmbientInverse

/-- Transported second-derivative left trace. -/
noncomputable def traceSecondLeftAmbient
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.maximalAmbientDomain →ₗ[𝕜] 𝕜 :=
  D.traceSecondLeft.toLinearMap.comp D.maximalAmbientInverse

/-- Transported third-derivative left trace. -/
noncomputable def traceThirdLeftAmbient
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.maximalAmbientDomain →ₗ[𝕜] 𝕜 :=
  D.traceThirdLeft.toLinearMap.comp D.maximalAmbientInverse

/-- Transported second-derivative right trace. -/
noncomputable def traceSecondRightAmbient
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.maximalAmbientDomain →ₗ[𝕜] 𝕜 :=
  D.traceSecondRight.toLinearMap.comp D.maximalAmbientInverse

/-- Transported third-derivative right trace. -/
noncomputable def traceThirdRightAmbient
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.maximalAmbientDomain →ₗ[𝕜] 𝕜 :=
  D.traceThirdRight.toLinearMap.comp D.maximalAmbientInverse

omit [CompleteSpace H] [CompleteSpace V] in
/-- The free ambient domain lies in the maximal ambient domain. -/
theorem freeAmbientDomain_le_maximalAmbientDomain
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.freeAmbientDomain ≤ D.maximalAmbientDomain := by
  intro x hx
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hx
  refine LinearMap.mem_range.mpr ⟨(u : V), ?_⟩
  exact hu

/-- Coercion of a free-domain vector into the maximal ambient domain. -/
noncomputable def freeToMaximal
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V)) :
    D.freeAmbientDomain →ₗ[𝕜] D.maximalAmbientDomain :=
  Submodule.inclusion D.freeAmbientDomain_le_maximalAmbientDomain

omit [CompleteSpace H] [CompleteSpace V] in
/-- The maximal inverse of a free vector is the underlying free graph-space
representative. -/
theorem maximalAmbientInverse_freeToMaximal
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.freeAmbientDomain) :
    D.maximalAmbientInverse (D.freeToMaximal x) =
      (D.freeAmbientInverse x : D.freeSubspace) := by
  apply D.embed_injective
  rw [D.embed_maximalAmbientInverse]
  change (x : H) = D.freeEmbed (D.freeAmbientInverse x)
  have h := D.freeRangeEquiv.apply_symm_apply x
  exact (congrArg Subtype.val h).symm

omit [CompleteSpace H] [CompleteSpace V] in
/-- The free fourth derivative agrees with the maximal fourth derivative after
domain inclusion. -/
theorem freeFourthAmbient_agrees
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.freeAmbientDomain) :
    D.freeFourthAmbient x =
      D.maximalFourthAmbient (D.freeToMaximal x) := by
  change D.fourth (D.freeAmbientInverse x : D.freeSubspace) =
    D.fourth (D.maximalAmbientInverse (D.freeToMaximal x))
  rw [D.maximalAmbientInverse_freeToMaximal]

omit [CompleteSpace H] [CompleteSpace V] in
/-- The free ambient domain is exactly the joint kernel of the four transported
traces. -/
theorem mem_freeAmbientDomain_iff_traces
    (D : FourthOrderTraceModel (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.maximalAmbientDomain) :
    (x : H) ∈ D.freeAmbientDomain ↔
      D.traceSecondLeftAmbient x = 0 ∧
      D.traceThirdLeftAmbient x = 0 ∧
      D.traceSecondRightAmbient x = 0 ∧
      D.traceThirdRightAmbient x = 0 := by
  let u : V := D.maximalAmbientInverse x
  have hxu : D.embed u = (x : H) := D.embed_maximalAmbientInverse x
  constructor
  · intro hx
    let xf : D.freeAmbientDomain := ⟨(x : H), hx⟩
    have hu : u = (D.freeAmbientInverse xf : D.freeSubspace) := by
      apply D.embed_injective
      rw [hxu]
      change (x : H) = D.freeEmbed (D.freeAmbientInverse xf)
      have h := D.freeRangeEquiv.apply_symm_apply xf
      exact (congrArg Subtype.val h).symm
    have hfree : (D.freeAmbientInverse xf : V) ∈ D.freeSubspace :=
      (D.freeAmbientInverse xf).property
    rw [D.mem_freeSubspace_iff] at hfree
    simpa [traceSecondLeftAmbient, traceThirdLeftAmbient,
      traceSecondRightAmbient, traceThirdRightAmbient, u, hu] using hfree
  · intro htraces
    have hu : u ∈ D.freeSubspace := by
      rw [D.mem_freeSubspace_iff]
      simpa [traceSecondLeftAmbient, traceThirdLeftAmbient,
        traceSecondRightAmbient, traceThirdRightAmbient, u] using htraces
    let uf : D.freeSubspace := ⟨u, hu⟩
    refine LinearMap.mem_range.mpr ⟨uf, ?_⟩
    change D.embed u = (x : H)
    exact hxu

end FourthOrderTraceModel

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
