/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks

/-!
# Restrictions of closed operators to reducing subspaces

This module gives a scalar-generic restriction construction for a densely
specified closed operator and an orthogonally complemented reducing subspace.
The construction keeps domains explicit, proves density and graph closedness,
and shows that self-adjointness passes to the restriction.

The result is independent of spectral theory.  Spectral packages only need to
produce the reducing-subspace laws; the closed restriction and its inclusion
intertwining are then canonical.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace
open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

noncomputable local instance completeSpaceOfHasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

namespace PartialMap

/-- The canonical inclusion of a reducing subspace. -/
def reducingSubspaceInclusion (U : Submodule 𝕜 E) : U →L[𝕜] E :=
  U.subtypeL

omit [CompleteSpace E] in
/-- The reducing-subspace inclusion is isometric. -/
theorem reducingSubspaceInclusion_isometric (U : Submodule 𝕜 E) :
    IsometricEmbedding (reducingSubspaceInclusion U) :=
  fun _ => rfl

omit [CompleteSpace E] in
/-- The inclusion maps the restricted domain into the ambient domain. -/
theorem reducingRestriction_inclusion_mem_domain
    (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (x : (TauCeti.LinearPMap.reducingRestriction A U hred).domain) :
    reducingSubspaceInclusion U (x : U) ∈ A.domain :=
  x.property

omit [CompleteSpace E] in
/-- The inclusion intertwines the restricted and ambient operators. -/
theorem reducingRestriction_inclusion_intertwines
    (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (x : (TauCeti.LinearPMap.reducingRestriction A U hred).domain) :
    A ⟨reducingSubspaceInclusion U (x : U),
        reducingRestriction_inclusion_mem_domain A U hred x⟩ =
      reducingSubspaceInclusion U
        (TauCeti.LinearPMap.reducingRestriction A U hred x) :=
  rfl

/-- Adjoint-domain membership of the restriction is exactly ambient
adjoint-domain membership for the included vector. -/
theorem mem_reducingRestriction_adjoint_domain_iff
    (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (y : U) :
    y ∈ (TauCeti.LinearPMap.reducingRestriction A U hred).adjoint.domain ↔
      (y : E) ∈ A.adjoint.domain :=
  TauCeti.LinearPMap.mem_reducingRestriction_adjoint_domain_iff
    A U hred y

omit [CompleteSpace E] in
/-- Symmetry passes to the reducing restriction. -/
theorem reducingRestriction_isSymmetric
    (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hA : TauCeti.LinearPMap.IsSymmetric A) :
    TauCeti.LinearPMap.IsSymmetric
      (TauCeti.LinearPMap.reducingRestriction A U hred) :=
  TauCeti.LinearPMap.reducingRestriction_isSymmetric A U hred hA

/-- A self-adjoint operator restricts to a self-adjoint operator on every
reducing subspace. -/
theorem reducingRestriction_isSelfAdjoint
    (A : E →ₗ.[𝕜] E)
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hA : _root_.IsSelfAdjoint A) :
    _root_.IsSelfAdjoint (TauCeti.LinearPMap.reducingRestriction A U hred) :=
  TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A U hred
    hA.dense_domain hA

end PartialMap
end DavisKahanExt
end TauCeti
