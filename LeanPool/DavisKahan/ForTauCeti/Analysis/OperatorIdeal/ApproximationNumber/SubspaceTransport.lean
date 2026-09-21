/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence

/-!
# Approximation-number transport across canonical subspace coordinates

An operator between subspaces of two Hilbert spaces can be read either in subtype
coordinates or as an ambient block.  Passing between the two composes with the canonical
inclusion `U.subtypeL` and with its adjoint, the orthogonal projection.  Both are
contractions, and the two composites are inverse to each other on the relevant side, so the
composition estimates for approximation numbers pinch in both directions: the *entire*
approximation-number sequence is unchanged.

Because the ambient and subtype coordinates are genuinely different Hilbert spaces, the
statements use the heterogeneous relation
`ContinuousLinearMap.HasSameApproximationNumbers` rather than an equality of operators.

## Main results

* `ContinuousLinearMap.hasSameApproximationNumbers_extendDomainByZero`: extending a map out
  of a closed subspace by zero on the orthogonal complement;
* `ContinuousLinearMap.hasSameApproximationNumbers_includeCodomain`: including the target
  subspace into the ambient space;
* `ContinuousLinearMap.hasSameApproximationNumbers_ambientSubspaceBlock`: the two together,
  reading a rectangular subspace block as an ambient operator.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module:
  `DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/SubspaceSingularTransport.lean`.
* Original declarations: `TauCeti.DavisKahan.ExactSinTheta.{`
  `sameApproximationSingularValues_extendDomainByZero,`
  `sameApproximationSingularValues_includeCodomain,`
  `sameApproximationSingularValues_ambientSubspaceBlock}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **copied and renamespaced**.  Not a hypothesis, binder or proof step
  changed; the declarations move from `TauCeti.DavisKahan.ExactSinTheta` to
  `ContinuousLinearMap`, and the conclusions are spelled with
  `ContinuousLinearMap.HasSameApproximationNumbers`, which is what the source layer's
  `SameApproximationSingularSequence` abbreviates.
* Extraction motive: `DavisKahan/Geometry/Polar/RestrictedDisplacementExtremal.lean` — a
  *generic* geometry module — imported the source-layer file above for
  `sameApproximationSingularValues_extendDomainByZero` alone.  Nothing in these three
  statements mentions Davis--Kahan.
* Spectra influence: none.
-/

public section

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace Submodule

omit [CompleteSpace E] in
/-- The canonical inclusion of a subspace has `‖·‖ ≤ 1`. -/
private theorem norm_subtypeL_le_one (U : Submodule 𝕜 E) :
    ‖U.subtypeL‖ ≤ 1 := by
  exact_mod_cast U.norm_subtypeL_le

/-- The adjoint of the canonical inclusion is the orthogonal projection, so it
too has `‖·‖ ≤ 1`. -/
private theorem norm_adjoint_subtypeL_le_one
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    ‖U.subtypeL.adjoint‖ ≤ 1 := by
  rw [Submodule.adjoint_subtypeL]
  exact_mod_cast U.orthogonalProjectionOnto_norm_le

end Submodule

namespace ContinuousLinearMap

open Submodule

omit [CompleteSpace F] in
/-- Extending a map from a closed subspace by zero on its orthogonal complement
preserves every approximation singular value. -/
theorem hasSameApproximationNumbers_extendDomainByZero
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (T : U →L[𝕜] F) :
    HasSameApproximationNumbers
      (T ∘L U.subtypeL.adjoint) T := by
  refine (hasSameApproximationNumbers_iff _ _).mpr ?_
  intro n
  have hfactor : (T ∘L U.subtypeL.adjoint) ∘L U.subtypeL = T := by
    ext x
    simp [Submodule.adjoint_subtypeL]
  have key : (T ∘L U.subtypeL.adjoint).approximationNumber n
      = T.approximationNumber n := by
    refine le_antisymm ?_ ?_
    · calc (T ∘L U.subtypeL.adjoint).approximationNumber n
          ≤ T.approximationNumber n * ‖U.subtypeL.adjoint‖ :=
            T.approximationNumber_comp_le_mul_norm _ n
        _ ≤ T.approximationNumber n * 1 := by
            gcongr <;>
              first
                | exact norm_adjoint_subtypeL_le_one U
                | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
        _ = T.approximationNumber n := mul_one _
    · calc T.approximationNumber n
          = ((T ∘L U.subtypeL.adjoint) ∘L U.subtypeL).approximationNumber n := by
            rw [hfactor]
        _ ≤ (T ∘L U.subtypeL.adjoint).approximationNumber n * ‖U.subtypeL‖ :=
            (T ∘L U.subtypeL.adjoint).approximationNumber_comp_le_mul_norm _ n
        _ ≤ (T ∘L U.subtypeL.adjoint).approximationNumber n * 1 := by
            gcongr <;>
              first
                | exact norm_subtypeL_le_one U
                | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
        _ = (T ∘L U.subtypeL.adjoint).approximationNumber n := mul_one _
  exact key

omit [CompleteSpace E] in
/-- Including the range of a map into the ambient Hilbert space preserves every
approximation singular value. -/
theorem hasSameApproximationNumbers_includeCodomain
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] V) :
    HasSameApproximationNumbers (V.subtypeL ∘L T) T := by
  refine (hasSameApproximationNumbers_iff _ _).mpr ?_
  intro n
  have hfactor : V.subtypeL.adjoint ∘L (V.subtypeL ∘L T) = T := by
    ext x
    simp [Submodule.adjoint_subtypeL]
  have key : (V.subtypeL ∘L T).approximationNumber n
      = T.approximationNumber n := by
    refine le_antisymm ?_ ?_
    · calc (V.subtypeL ∘L T).approximationNumber n
          ≤ ‖V.subtypeL‖ * T.approximationNumber n :=
            ContinuousLinearMap.approximationNumber_comp_le_norm_mul _ T n
        _ ≤ 1 * T.approximationNumber n := by
            gcongr <;>
              first
                | exact norm_subtypeL_le_one V
                | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
        _ = T.approximationNumber n := one_mul _
    · calc T.approximationNumber n
          = (V.subtypeL.adjoint ∘L (V.subtypeL ∘L T)).approximationNumber n := by
            rw [hfactor]
        _ ≤ ‖V.subtypeL.adjoint‖ * (V.subtypeL ∘L T).approximationNumber n :=
            ContinuousLinearMap.approximationNumber_comp_le_norm_mul _ _ n
        _ ≤ 1 * (V.subtypeL ∘L T).approximationNumber n := by
            gcongr <;>
              first
                | exact norm_adjoint_subtypeL_le_one V
                | simpa using ContinuousLinearMap.approximationNumber_nonneg _ _
        _ = (V.subtypeL ∘L T).approximationNumber n := one_mul _
  exact key

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Precomposition with an invertible contraction preserves every
approximation singular value.**

`J` and a right inverse `J'` both have norm at most one -- the case that matters
is a self-adjoint unitary, where `J' = J` -- so each of `T` and `T ∘ J` is a
contraction of the other and the two sequences coincide.

This is unitary invariance of the singular-value sequence in the source
variable, stated without a `LinearIsometryEquiv` so that a reflection operator
already in bounded form can be used directly. -/
theorem hasSameApproximationNumbers_comp_right
    {T : E →L[𝕜] F} {J J' : E →L[𝕜] E}
    (hJ : ‖J‖ ≤ 1) (hJ' : ‖J'‖ ≤ 1) (hinv : ∀ x, J (J' x) = x) :
    HasSameApproximationNumbers (T ∘L J) T := by
  refine (hasSameApproximationNumbers_iff _ _).mpr fun n => ?_
  have hfactor : (T ∘L J) ∘L J' = T := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, hinv]
  refine le_antisymm ?_ ?_
  · calc (T ∘L J).approximationNumber n ≤ T.approximationNumber n * ‖J‖ :=
        T.approximationNumber_comp_le_mul_norm _ n
      _ ≤ T.approximationNumber n * 1 := by
          gcongr
          exact ContinuousLinearMap.approximationNumber_nonneg _ _
      _ = T.approximationNumber n := mul_one _
  · calc T.approximationNumber n
        = ((T ∘L J) ∘L J').approximationNumber n := by rw [hfactor]
      _ ≤ (T ∘L J).approximationNumber n * ‖J'‖ :=
          (T ∘L J).approximationNumber_comp_le_mul_norm _ n
      _ ≤ (T ∘L J).approximationNumber n * 1 := by
          gcongr
          exact ContinuousLinearMap.approximationNumber_nonneg _ _
      _ = (T ∘L J).approximationNumber n := mul_one _

/-- Ambient extension of a rectangular subspace block preserves the complete
singular-value sequence. -/
theorem hasSameApproximationNumbers_ambientSubspaceBlock
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (V : Submodule 𝕜 F) [V.HasOrthogonalProjection]
    (T : U →L[𝕜] V) :
    HasSameApproximationNumbers
      (V.subtypeL ∘L T ∘L U.subtypeL.adjoint) T :=
  (hasSameApproximationNumbers_includeCodomain V
    (T ∘L U.subtypeL.adjoint)).trans
      (hasSameApproximationNumbers_extendDomainByZero U T)

end ContinuousLinearMap

end
