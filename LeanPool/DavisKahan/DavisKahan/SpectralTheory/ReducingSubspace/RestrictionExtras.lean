/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ReducingSubspace.Restriction

/-!
# Convenience laws for reducing restrictions

This leaf keeps optional compatibility lemmas separate from the compiler-accepted
core restriction construction.  In particular, it records orthogonal-complement
closure and agreement with the ordinary bounded restriction.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

namespace PartialMap
namespace ReducesSubspace

omit [CompleteSpace E] in
/-- Orthogonal complementation preserves the reducing-subspace property. -/
theorem orthogonal
    {A : E →ₗ.[𝕜] E}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : TauCeti.LinearPMap.ReducesSubspace A U) : TauCeti.LinearPMap.ReducesSubspace A Uᗮ :=
  TauCeti.LinearPMap.ReducesSubspace.orthogonal h

end ReducesSubspace

omit [CompleteSpace E] in
/-- A bounded reducing-subspace law induces the domain-aware law for the
full-domain closed operator. -/
theorem ofBounded_reducesSubspace
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.Reduces U) :
    TauCeti.LinearPMap.ReducesSubspace (A.toLinearMap.toPMap ⊤) U := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simp
  · intro x
    simp
  · intro x hx
    change A (x : E) ∈ U
    exact hred.1 (x : E) hx
  · intro x hx
    change A (x : E) ∈ Uᗮ
    exact hred.2 (x : E) hx

/-- The block of a bounded operator on a subspace it reduces, as a partial map.

The Section 6 whole-space statements compare two such blocks through
`FormBoundedSylvesterGap`.  Writing the composite out inline is what made those
hypotheses unreadable, and is why callers were handed a record to fill in
instead of a theorem to apply. -/
noncomputable def boundedReducingBlock
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.Reduces U) : U →ₗ.[𝕜] U :=
  TauCeti.LinearPMap.reducingRestriction (A.toLinearMap.toPMap ⊤) U
    (ofBounded_reducesSubspace A U hred)

/-- The block of a bounded operator on the orthogonal complement of a subspace
it reduces.  A reducing subspace's complement is reducing, so this needs no
hypothesis beyond `hred`. -/
noncomputable def boundedReducingBlockCompl
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : A.Reduces U) : Uᗮ →ₗ.[𝕜] Uᗮ :=
  TauCeti.LinearPMap.reducingRestriction (A.toLinearMap.toPMap ⊤) Uᗮ
    (ofBounded_reducesSubspace A U hred).orthogonal

end PartialMap
end DavisKahanExt
end TauCeti
