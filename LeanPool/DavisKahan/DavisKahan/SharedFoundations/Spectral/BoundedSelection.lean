/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SelectedReduction

/-!
# Audited bounded spectral selections

A spectral subspace cannot be defined from an arbitrary bounded operator and
an arbitrary set alone.  The reusable data must retain self-adjointness and
measurability.  This record packages the genuine PVM range, its projection,
and its reduction property for downstream sine, tangent, continuation, and
Riesz-projection campaigns.
-/

namespace TauCeti
namespace DavisKahan
namespace SharedFoundations
namespace Spectral

open scoped InnerProductSpace
open DavisKahanExt
open TauCeti.DavisKahan

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A certified measurable spectral selection for a bounded self-adjoint
operator. -/
structure BoundedSpectralSelection (A : H →L[ℂ] H) where
  /-- The measurable subset of the real line selecting the spectral subspace. -/
  carrier : Set ℝ
  measurable_carrier : MeasurableSet carrier
  selfAdjoint : A.IsSymmetric
  /-- The spectral subspace associated with the selected carrier. -/
  subspace : Submodule ℂ H
  /-- The orthogonal spectral projection associated with the selected carrier. -/
  projection : H →L[ℂ] H
  subspace_eq : subspace = boundedSelfAdjointSpectralSubspace A selfAdjoint
    carrier measurable_carrier
  projection_eq : projection = boundedSelfAdjointSpectralProjection A selfAdjoint
    carrier measurable_carrier
  reduces : A.Reduces subspace

/-- Canonical PVM selection. -/
noncomputable def BoundedSpectralSelection.canonical
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) : BoundedSpectralSelection A where
  carrier := s
  measurable_carrier := hs
  selfAdjoint := hA
  subspace := boundedSelfAdjointSpectralSubspace A hA s hs
  projection := boundedSelfAdjointSpectralProjection A hA s hs
  subspace_eq := rfl
  projection_eq := rfl
  reduces := boundedSelfAdjointSpectralSubspace_reduces A hA s hs

namespace BoundedSpectralSelection

omit [CompleteSpace H] in
/-- Every member of an equal pair of projected subspaces has the same pointwise
star projection.  This avoids dependent rewriting through the projection
instance. -/
private theorem starProjection_apply_congr
    {U V : Submodule ℂ H}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U = V) (x : H) : U.starProjection x = V.starProjection x := by
  subst V
  rfl

/-- A certified selection carries the canonical orthogonal projection. -/
noncomputable instance hasOrthogonalProjection
    {A : H →L[ℂ] H} (S : BoundedSpectralSelection A) :
    S.subspace.HasOrthogonalProjection := by
  rw [S.subspace_eq]
  infer_instance

/-- The stored projection is the star projection onto the stored subspace. -/
theorem projection_eq_starProjection
    {A : H →L[ℂ] H} (S : BoundedSpectralSelection A) :
    S.projection = S.subspace.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  rw [S.projection_eq]
  calc
    boundedSelfAdjointSpectralProjection A S.selfAdjoint S.carrier
          S.measurable_carrier x =
        (boundedSelfAdjointSpectralSubspace A S.selfAdjoint S.carrier
          S.measurable_carrier).starProjection x := by
      exact congrArg (fun T : H →L[ℂ] H => T x)
        (boundedSelfAdjointSpectralProjection_eq_starProjection
          A S.selfAdjoint S.carrier S.measurable_carrier)
    _ = S.subspace.starProjection x :=
      starProjection_apply_congr S.subspace_eq.symm x

/-- The stored projection commutes with the operator. -/
theorem projection_comp_comm
    {A : H →L[ℂ] H} (S : BoundedSpectralSelection A) :
    S.projection ∘L A = A ∘L S.projection := by
  apply ContinuousLinearMap.ext
  intro x
  rw [S.projection_eq]
  simpa only [ContinuousLinearMap.comp_apply] using
    (boundedSelfAdjointSpectralProjection_apply_comm
      A S.selfAdjoint S.carrier S.measurable_carrier x).symm

/-- The selected complement also reduces the operator. -/
theorem orthogonal_reduces
    {A : H →L[ℂ] H} (S : BoundedSpectralSelection A) :
    A.Reduces S.subspaceᗮ := by
  constructor
  · exact S.reduces.2
  · intro x hx
    rw [Submodule.orthogonal_orthogonal] at hx ⊢
    exact S.reduces.1 x hx

end BoundedSpectralSelection

end Spectral
end SharedFoundations
end DavisKahan
end TauCeti
