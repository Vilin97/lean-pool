/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Subspace
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure

/-!
# Spectral-subspace domain and intertwining adapters

This file begins the genuine spectral-restriction path needed to specialize the
unbounded sine-theta theorem to spectral projections of an operator and its
bounded perturbation.

For a self-adjoint partial map `A : H →ₗ.[ℂ] H`, the canonical spectral
projection `E_A(B)` is packaged as a continuous linear map and its range as a
closed orthogonally complemented subspace.  The main analytic facts proved here are:

* `E_A(B)` preserves `A.domain` for every measurable set `B`;
* `A (E_A(B)x) = E_A(B) (A x)` on `A.domain`;
* consequently the spectral range is invariant under the domain-aware action
  of `A`.

These are the exact domain/intertwining obligations needed to exhibit the
operator part on the spectral range as a self-adjoint partial map.

## Provenance

Until 2026-07-28 the projections came from `vendor/Spectra` through Stone's
theorem: `genToGroup hA` produced a one-parameter unitary group, and
`spectralProjection`/`PVM.spectralPVM` its projection-valued measure, with
`spectralProjection_mem_generatorDomain_of_mem` and
`generator_spectralProjection_comm` supplying the two facts below.

The native replacement is `TauCeti.LinearPMap.spectralPVM`, built from the
bounded Borel functional calculus of the *Cayley transform* rather than from
Stone's theorem — see
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/` and
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean`.  The
two facts become `specProjection_mem_domain` and `specProjection_apply_domain`,
both of which fall out of one observation: the spectral projections and the
resolvent `(A + i)⁻¹` are both images of the same (commutative) Borel calculus.
The statements here are unchanged.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The canonical spectral projection of a self-adjoint partial map. -/
noncomputable def selfAdjointSpectralProjection
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H :=
  TauCeti.LinearPMap.specProjection hA B hB

/-- The range subspace of a canonical self-adjoint spectral projection. -/
noncomputable def selfAdjointSpectralSubspace
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) : Submodule ℂ H :=
  pvmRangeSubspace (TauCeti.LinearPMap.spectralPVM hA) B hB

/-- The self-adjoint spectral subspace is the range of its spectral projection. -/
@[simp]
theorem selfAdjointSpectralSubspace_eq_range
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    selfAdjointSpectralSubspace A hA B hB =
      (selfAdjointSpectralProjection A hA B hB).range :=
  rfl

/-- A canonical self-adjoint spectral range is complete. -/
noncomputable instance selfAdjointSpectralSubspace_completeSpace
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    CompleteSpace (selfAdjointSpectralSubspace A hA B hB) := by
  unfold selfAdjointSpectralSubspace
  infer_instance

/-- A canonical self-adjoint spectral range is orthogonally complemented. -/
noncomputable instance selfAdjointSpectralSubspace_hasOrthogonalProjection
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (selfAdjointSpectralSubspace A hA B hB).HasOrthogonalProjection := by
  unfold selfAdjointSpectralSubspace
  infer_instance

/-- The canonical inclusion of a spectral range into the ambient Hilbert
space. -/
noncomputable def selfAdjointSpectralSubspaceInclusion
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    selfAdjointSpectralSubspace A hA B hB →L[ℂ] H :=
  Submodule.subtypeL (selfAdjointSpectralSubspace A hA B hB)

/-- The inclusion of the spectral subspace acts as the underlying vector. -/

theorem selfAdjointSpectralSubspaceInclusion_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (x : selfAdjointSpectralSubspace A hA B hB) :
    selfAdjointSpectralSubspaceInclusion A hA B hB x = (x : H) :=
  rfl

/-- Inclusion of a spectral range preserves norms exactly. -/
theorem selfAdjointSpectralSubspaceInclusion_isometric
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    IsometricEmbedding (selfAdjointSpectralSubspaceInclusion A hA B hB) := by
  intro x
  rfl

/-- The canonical spectral projection is the orthogonal projection onto its
range subspace. -/
theorem selfAdjointSpectralProjection_eq_starProjection
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    selfAdjointSpectralProjection A hA B hB =
      (selfAdjointSpectralSubspace A hA B hB).starProjection := by
  exact pvmProjection_eq_starProjection_rangeSubspace
    (TauCeti.LinearPMap.spectralPVM hA) B hB

/-- Every measurable spectral projection preserves the domain of its
self-adjoint operator. -/
theorem selfAdjointSpectralProjection_mem_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {B : Set ℝ} (hB : MeasurableSet B) (x : A.domain) :
    selfAdjointSpectralProjection A hA B hB (x : H) ∈ A.domain :=
  TauCeti.LinearPMap.specProjection_mem_domain hA B hB x

/-- A self-adjoint operator commutes with each measurable spectral projection
on its full operator domain. -/
theorem selfAdjoint_apply_spectralProjection
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {B : Set ℝ} (hB : MeasurableSet B) (x : A.domain) :
    A
        ⟨selfAdjointSpectralProjection A hA B hB (x : H),
          selfAdjointSpectralProjection_mem_domain A hA hB x⟩ =
      selfAdjointSpectralProjection A hA B hB (A x) :=
  TauCeti.LinearPMap.specProjection_apply_domain hA B hB x

/-- The domain-aware image of a vector in a spectral range remains in that
spectral range. -/
theorem selfAdjoint_maps_spectralSubspace
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {B : Set ℝ} (hB : MeasurableSet B) (x : A.domain)
    (hx : (x : H) ∈ selfAdjointSpectralSubspace A hA B hB) :
    A x ∈ selfAdjointSpectralSubspace A hA B hB := by
  let P := TauCeti.LinearPMap.spectralPVM hA
  change A x ∈ pvmRangeSubspace P B hB
  rw [mem_pvmRangeSubspace_iff P B hB]
  change selfAdjointSpectralProjection A hA B hB (A x) =
    A x
  have hfixP : P.proj B hB (x : H) = (x : H) :=
    pvmProjection_eq_self_of_mem_rangeSubspace P B hB hx
  have hfix : selfAdjointSpectralProjection A hA B hB (x : H) = (x : H) := by
    change P.proj B hB (x : H) = (x : H)
    exact hfixP
  have hsub :
      (⟨selfAdjointSpectralProjection A hA B hB (x : H),
        selfAdjointSpectralProjection_mem_domain A hA hB x⟩ : A.domain) = x :=
    Subtype.ext hfix
  calc
    selfAdjointSpectralProjection A hA B hB (A x) =
        A
          ⟨selfAdjointSpectralProjection A hA B hB (x : H),
            selfAdjointSpectralProjection_mem_domain A hA hB x⟩ :=
      (selfAdjoint_apply_spectralProjection A hA hB x).symm
    _ = A x := congrArg A hsub

end DavisKahan
end TauCeti
