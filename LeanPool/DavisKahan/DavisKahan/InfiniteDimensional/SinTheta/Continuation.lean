/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.Core
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SpectralIdentification
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Spectral projection continuation and branch selection

The old facade accepted only a bare function called a contour.  That type did
not contain differentiability, orientation, resolvent separation, or winding
data, so the claimed spectral-identification theorem could not follow from its
hypotheses.  This replacement uses the repository's proof-carrying
`PiecewiseC1ClosedContour` and `SpectralSeparatingContour` objects.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace Interval unitInterval

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Fixed-contour Riesz projection along an affine operator path. -/
noncomputable def continuedProjection
    (A V : H →L[ℂ] H) (Γ : PiecewiseC1ClosedContour) (t : ℝ) : H →L[ℂ] H :=
  fixedContourRieszOperator Γ (operatorPath A V t)

/-- Quantitative data sufficient for norm continuity of one continued
projection path. -/
structure ContinuedProjectionDatum
    (A V : H →L[ℂ] H) (Γ : PiecewiseC1ClosedContour)
    (parameterSet : Set ℝ) where
  /-- A uniform positive distance separating the contour from the path's spectra. -/
  margin : ℝ
  margin_pos : 0 < margin
  selfAdjoint : ∀ t ∈ parameterSet,
    (operatorPath A V t).IsSymmetric
  spectral_margin : ∀ t ∈ parameterSet, ∀ x : unitInterval,
    ∀ lam ∈ realSpectrum (operatorPath A V t),
      margin ≤ ‖Γ.path x - (lam : ℂ)‖

/-- Norm continuity of a fixed-contour Riesz projection path. -/
theorem continuous_continuedProjection
    (A V : H →L[ℂ] H) (Γ : PiecewiseC1ClosedContour)
    (D : ContinuedProjectionDatum A V Γ (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (continuedProjection A V Γ) (Set.Icc (0 : ℝ) 1) := by
  unfold continuedProjection
  exact continuousOn_fixedContourRieszOperator_operatorPath
    Γ A V (Set.Icc (0 : ℝ) 1) D.margin D.margin_pos
    D.selfAdjoint D.spectral_margin

/-- A separating witness for each path parameter, all sharing one geometric
contour. -/
structure ContinuedSpectralSelection
    (A V : H →L[ℂ] H) (s : Set ℝ)
    (Γ : PiecewiseC1ClosedContour) where
  /-- A separating contour for the selected spectral set at each path parameter. -/
  separating : ∀ t (_ht : t ∈ Set.Icc (0 : ℝ) 1),
    SpectralSeparatingContour (operatorPath A V t) s
  geometric : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
    (separating t ht).geometric = Γ

/-- At every path parameter, the continued Riesz operator is the genuine
spectral projection selected by the proof-carrying contour. -/
theorem continuedProjection_eq_spectralProjection
    (A V : H →L[ℂ] H) (s : Set ℝ)
    (Γ : PiecewiseC1ClosedContour)
    (D : ContinuedSpectralSelection A V s Γ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    continuedProjection A V Γ t =
      boundedSelfAdjointSpectralProjection
        (operatorPath A V t) (D.separating t ht).selfAdjoint s
        (D.separating t ht).measurable_selected := by
  unfold continuedProjection
  let Γt := D.separating t ht
  calc
    fixedContourRieszOperator Γ (operatorPath A V t)
        = Γt.contourRieszProjection := by
          rw [← D.geometric t ht]
          exact fixedContourRieszOperator_eq_contourRieszProjection Γt
    _ = boundedSelfAdjointSpectralProjection
          (operatorPath A V t) Γt.selfAdjoint s Γt.measurable_selected :=
        Γt.contourRieszProjection_eq_boundedSelfAdjointSpectralProjection

/-- Every projection on the continued path is orthogonal. -/
theorem continuedProjection_isOrthogonalProjection
    (A V : H →L[ℂ] H) (s : Set ℝ)
    (Γ : PiecewiseC1ClosedContour)
    (D : ContinuedSpectralSelection A V s Γ) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsOrthogonalProjection (continuedProjection A V Γ t) := by
  intro t ht
  unfold continuedProjection
  exact fixedContourRieszOperator_operatorPath_isOrthogonalProjection
    Γ A V s D.separating D.geometric t ht

end

end DavisKahanExt
end TauCeti
