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
public import LeanPool.DavisKahan.DavisKahan.Sylvester.ClosedSylvesterEquation
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralFormBounds

/-! # Ordered Half Line -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Genuine spectral half-line localization

This leaf converts half-line containment of the spectrum of a closed
self-adjoint operator into the quadratic-form semibounds consumed by the ordered
branches of the unbounded Sylvester theorem.

Until 2026-07-29 the proof ran through Spectra's Born measure: the measure of a
domain vector has its support in the spectrum, its first moment is the diagonal
matrix element, and integrating the pointwise half-line inequality gave the form
bound.  That route needs the identity function to be integrable against the
measure, which is a second-moment fact.

The native route needs no integral at all.  `E((-∞, c)) = 0` is the support
statement of `ForTauCeti/…/LinearPMap/SpectralSupport.lean`, and the form bound
then comes from the *bounded* one on `[c, τ]` in the limit `τ → ∞` —
`TauCeti.LinearPMap.le_re_inner_of_specProjection_Iio_eq_zero`.
-/

open scoped InnerProductSpace
open MeasureTheory

namespace TauCeti
namespace DavisKahan


universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine spectral containment in `[c, ∞)` implies the matching lower
quadratic-form bound. -/
theorem semiboundedBelow_of_spectrum_subset_Ici
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {c : ℝ}
    (hσ : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A ⊆
        Set.Ici c) :
    TauCeti.LinearPMap.SemiboundedBelow A c := by
  intro x
  have hzero :
      TauCeti.LinearPMap.specProjection hA (Set.Iio c) measurableSet_Iio = 0 := by
    refine TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet hA _
      measurableSet_Iio fun lam hlam => ?_
    by_contra hnot
    exact absurd (hσ hnot) (by simpa using not_le.mpr hlam)
  simpa using
    TauCeti.LinearPMap.le_re_inner_of_specProjection_Iio_eq_zero hA hzero x

/-- Genuine spectral containment in `(-∞, c]` implies the matching upper
quadratic-form bound. -/
theorem semiboundedAbove_of_spectrum_subset_Iic
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {c : ℝ}
    (hσ : Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A ⊆
        Set.Iic c) :
    TauCeti.LinearPMap.SemiboundedAbove A c := by
  intro x
  have hzero :
      TauCeti.LinearPMap.specProjection hA (Set.Ioi c) measurableSet_Ioi = 0 := by
    refine TauCeti.LinearPMap.specProjection_eq_zero_of_subset_resolventSet hA _
      measurableSet_Ioi fun lam hlam => ?_
    by_contra hnot
    exact absurd (hσ hnot) (by simpa using not_le.mpr hlam)
  simpa using
    TauCeti.LinearPMap.re_inner_le_of_specProjection_Ioi_eq_zero hA hzero x

end DavisKahan
end TauCeti
