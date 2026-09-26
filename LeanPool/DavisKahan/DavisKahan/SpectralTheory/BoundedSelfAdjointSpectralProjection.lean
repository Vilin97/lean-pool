/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.SpectralRestriction
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Canonical spectral projections

This module is the low-level spectral-projection surface used by the concrete
continuation development.  It is deliberately complex at the bounded Spectra
layer: the PVM is the genuine spectral measure of the bridged bounded
self-adjoint operator.  Real projections are supplied independently by the
complexification-and-descent API in
`DavisKahan.SpectralTheory.Real.SpectralRestriction`.

The former scalar-generic `spectralResolution` namespace and the nonexistent
`Spectra.SpectralTheory.SpectralTheorem` import are not reconstructed.  A
uniform `RCLike` PVM would require mathematical structure not present in the
pinned dependencies.  Downstream contour theory should identify its Riesz
operator with `boundedSelfAdjointSpectralProjection` instead.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open Set
open scoped InnerProductSpace
open DavisKahan
open DavisKahan.Foundation

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A spectral point of a self-adjoint operator is its own real part. -/
theorem coe_reCoord (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (w : spectrum ℂ A) :
    ((TauCeti.BorelCalculus.reCoord w : ℝ) : ℂ) = (w : ℂ) := by
  have hAsa : IsSelfAdjoint A := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  obtain ⟨z, hz⟩ := w
  have hmem : z ∈ spectrum ℂ A := hz
  rw [← hAsa.spectrumRestricts.algebraMap_image] at hmem
  obtain ⟨lam, -, hlam⟩ := hmem
  change ((z.re : ℝ) : ℂ) = z
  rw [← hlam]
  simp

/-- The genuine Spectra projection-valued measure of a bounded self-adjoint
operator. -/
noncomputable def boundedSelfAdjointSpectralPVM
    (A : H →L[ℂ] H) (hA : A.IsSymmetric) :
    TauCeti.ProjValMeasure H :=
  TauCeti.BorelCalculus.boundedPVM
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hA)

/-- The genuine measurable spectral projection of a bounded self-adjoint
operator. -/
noncomputable def boundedSelfAdjointSpectralProjection
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) : H →L[ℂ] H :=
  (boundedSelfAdjointSpectralPVM A hA).proj s hs

/-- The selected spectral range of a bounded self-adjoint operator.

This lane still runs on `vendor/Spectra`: it needs the spectral measure of a
*bounded* operator to agree with that operator's own continuous functional
calculus, which the native Cayley construction does not yet supply.  The range
API is therefore kept local here rather than shared with
`DavisKahan.SpectralTheory.PVMSubspace`, which has moved to
`TauCeti.ProjValMeasure`. -/
noncomputable def boundedSelfAdjointSpectralSubspace
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) : Submodule ℂ H :=
  (boundedSelfAdjointSpectralProjection A hA s hs).range

/-- The selected bounded spectral range has the canonical orthogonal
projection supplied by the underlying PVM projection. -/
noncomputable instance boundedSelfAdjointSpectralSubspace_hasOrthogonalProjection
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (boundedSelfAdjointSpectralSubspace A hA s hs).HasOrthogonalProjection := by
  change (boundedSelfAdjointSpectralProjection A hA s hs).range.HasOrthogonalProjection
  exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (show IsIdempotentElem (boundedSelfAdjointSpectralProjection A hA s hs) from
      (boundedSelfAdjointSpectralPVM A hA).proj_idem s hs)

/-- **The bounded spectral projection is the continuous functional calculus of
any continuous symbol agreeing with the indicator on the spectrum.** -/
theorem boundedSelfAdjointSpectralProjection_eq_cfcL_of_agrees
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) (g : C(spectrum ℂ A, ℂ))
    (hg : ∀ w : spectrum ℂ A,
      g w = (TauCeti.BorelCalculus.reCoord ⁻¹' s).indicator (fun _ => (1 : ℂ)) w) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      cfcL ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hA).isStarNormal g :=
  TauCeti.BorelCalculus.boundedPVM_proj_eq_cfcHom _ s hs g hg

/-- The selected spectral subspace is exactly the range of its spectral
projection. -/
@[simp] theorem boundedSelfAdjointSpectralSubspace_eq_range
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralSubspace A hA s hs =
      (boundedSelfAdjointSpectralProjection A hA s hs).range :=
  rfl

/-- The genuine bounded spectral projection is the Mathlib star projection
onto its selected spectral range. -/
theorem boundedSelfAdjointSpectralProjection_eq_starProjection
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      (boundedSelfAdjointSpectralSubspace A hA s hs).starProjection := by
  set P : TauCeti.ProjValMeasure H := boundedSelfAdjointSpectralPVM A hA with hP
  set Q := boundedSelfAdjointSpectralProjection A hA s hs with hQ
  have hidem : ∀ y : H, Q (Q y) = Q y := fun y => by
    have h := congrArg (fun T : H →L[ℂ] H => T y) (P.proj_idem s hs)
    simp only [mul_apply_eq_comp] at h
    exact h
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨x, rfl⟩
  · intro y hy
    obtain ⟨z, rfl⟩ := hy
    change ⟪x - Q x, Q z⟫_ℂ = 0
    have hstarQ : star Q = Q := (P.isSelfAdjoint_proj s hs).star_eq
    have hadj := ContinuousLinearMap.adjoint_inner_right Q (x - Q x) z
    rw [← ContinuousLinearMap.star_eq_adjoint, hstarQ] at hadj
    rw [hadj, map_sub, hidem, sub_self, inner_zero_left]

/-- Every genuine bounded spectral projection is an orthogonal projection in
the continuation-facing predicate. -/
theorem boundedSelfAdjointSpectralProjection_isOrthogonalProjection
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    IsOrthogonalProjection
      (boundedSelfAdjointSpectralProjection A hA s hs) := by
  let P : TauCeti.ProjValMeasure H := boundedSelfAdjointSpectralPVM A hA
  change IsOrthogonalProjection (P.proj s hs)
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change P.proj s hs (P.proj s hs x) = P.proj s hs x
    simpa only [mul_apply_eq_comp] using
      congrArg (fun T : H →L[ℂ] H => T x) (P.proj_idem s hs)
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (P.isSelfAdjoint_proj s hs)

end DavisKahanExt
end TauCeti
