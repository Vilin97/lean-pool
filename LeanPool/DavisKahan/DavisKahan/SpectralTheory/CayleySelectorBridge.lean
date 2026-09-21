/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ResolventOperator
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.BoundedSelfAdjointSpectralProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Selector bridge for bounded spectral projections

The contour-free half of the spectral-identification machinery, split out of
`ContinuationSpectralIdentification` so that consumers that produce their own
continuous spectral symbol (for example the circle Riesz projection in
`SpectralTheory/CircleRieszIntegral.lean`) can identify a bounded spectral projection with a
Mathlib continuous-functional-calculus value without importing the
contour-continuation chain (which is currently blocked on `SinTheta/General`).

Contents: the selected-set spectral selector; the identification of the
genuine bounded spectral projection with the calculus of any continuous symbol
agreeing with the selector on the real spectrum; the project resolvent as a
continuous functional calculus; and the interval-integral / calculus exchange.

The bounded Cayley/Möbius bridge that used to live here was deleted on
2026-07-29 along with the Spectra dependency it existed to serve: it identified
Spectra's `Cayley.cayley` with `cfc boundedMobiusSymbol` so that Spectra's
group calculus of the selector could be recognised as `cfcL`.  The native
`TauCeti.BorelCalculus.boundedPVM_proj_eq_cfcHom` states that identification
directly, and no Cayley transform is needed for a bounded operator.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open Set
open MeasureTheory
open scoped InnerProductSpace
open DavisKahan.Foundation

universe v

section CayleySelectorBridge

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## Scalar contour selector -/

/-- The complex-valued indicator symbol of the selected real spectral set. -/
noncomputable def spectralSelector (s : Set ℝ) : ℝ → ℂ :=
  Set.indicator s (fun _ => (1 : ℂ))

/-- The selected-set indicator is measurable whenever the set is measurable. -/
theorem spectralSelector_measurable (s : Set ℝ) (hs : MeasurableSet s) :
    Measurable (spectralSelector s) := by
  classical
  exact measurable_const.indicator hs

/-- The selected-set indicator is uniformly bounded by one. -/
theorem spectralSelector_bounded (s : Set ℝ) :
    ∃ C : ℝ, ∀ lam : ℝ, ‖spectralSelector s lam‖ ≤ C := by
  classical
  refine ⟨1, fun lam => ?_⟩
  by_cases hlam : lam ∈ s <;> simp [spectralSelector, hlam]

/-- **The genuine bounded spectral projection is the continuous functional
calculus of any continuous symbol agreeing with the selector on the spectrum.**

Until 2026-07-29 this went through Spectra in two steps — the projection was
Spectra's group calculus of the selector, and that calculus was identified with
`cfcL` by a Cayley-transform argument.  Both steps collapse into
`TauCeti.BorelCalculus.boundedPVM_proj_eq_cfcHom`: the native Borel calculus of
a bounded self-adjoint operator is indexed along the real part of its own
spectrum, so a continuous symbol agreeing with the indicator *there* has the
same calculus image, definitionally. -/
theorem boundedSelfAdjointSpectralProjection_eq_cfcL_of_selector
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s)
    (g : C(spectrum ℂ A, ℂ))
    (hg : ∀ (lam : ℝ) (hlam : (lam : ℂ) ∈ spectrum ℂ A),
      g ⟨(lam : ℂ), hlam⟩ = spectralSelector s lam) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      cfcL (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA).isStarNormal g := by
  refine TauCeti.DavisKahanExt.boundedSelfAdjointSpectralProjection_eq_cfcL_of_agrees
    A hA s hs g fun w => ?_
  have hcoe := TauCeti.DavisKahanExt.coe_reCoord A hA w
  have hmem : ((TauCeti.BorelCalculus.reCoord w : ℝ) : ℂ) ∈ spectrum ℂ A := by
    rw [hcoe]; exact w.2
  have h1 : g w = spectralSelector s (TauCeti.BorelCalculus.reCoord w) := by
    rw [← hg (TauCeti.BorelCalculus.reCoord w) hmem]
    congr 1
    exact Subtype.ext hcoe.symm
  rw [h1, spectralSelector]
  by_cases hw : TauCeti.BorelCalculus.reCoord w ∈ s <;> simp [hw, Set.mem_preimage]

/-! ## Resolvent through the bounded continuous functional calculus -/

/-- Under a positive distance bound from the real spectrum, the project
resolvent is the complex continuous functional calculus of the scalar
resolvent symbol. -/
theorem resolventOperator_eq_cfc_resolventSymbol
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (z : ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ lam ∈ realSpectrum A, delta ≤ ‖z - (lam : ℂ)‖) :
    resolventOperator A z = cfc (fun w : ℂ => (w - z)⁻¹) A := by
  let f : ℂ → ℂ := fun w => w - z
  let g : ℂ → ℂ := fun w => (w - z)⁻¹
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hnormal : IsStarNormal A := hAsa.isStarNormal
  have hne : ∀ w ∈ spectrum ℂ A, f w ≠ 0 :=
    sub_ne_zero_of_realSpectrum_separated A hA hdelta hsep
  have hfcont : ContinuousOn f (spectrum ℂ A) :=
    (continuous_id.sub continuous_const).continuousOn
  have hgcont : ContinuousOn g (spectrum ℂ A) := hfcont.inv₀ hne
  let R : H →L[ℂ] H := cfc g A
  have hshift : cfc f A = A - z • (1 : H →L[ℂ] H) :=
    cfc_sub_const_eq A z
  have hright : (A - z • (1 : H →L[ℂ] H)) * R = 1 :=
    shift_mul_cfc_inv_eq_one A z hne hfcont hgcont
  have hz : InResolventSet A z :=
    complex_inResolventSet_of_distance A hA z delta hdelta hsep
  have hchosen := resolventOperator_mul_cancel A hz
  change resolventOperator A z = cfc g A
  calc
    resolventOperator A z = resolventOperator A z * 1 := (mul_one _).symm
    _ = resolventOperator A z *
        ((A - z • (1 : H →L[ℂ] H)) * R) := by rw [hright]
    _ = (resolventOperator A z *
        (A - z • (1 : H →L[ℂ] H))) * R := by rw [mul_assoc]
    _ = R := by rw [hchosen, one_mul]
    _ = cfc g A := rfl

/-! ## Interval-integral calculus bridge -/

/-- The bundled continuous functional calculus commutes with an oriented
interval integral of continuous spectrum-valued symbols. -/
theorem cfcL_intervalIntegral
    (A : H →L[ℂ] H) (hA : IsStarNormal A)
    (f : ℝ → C(spectrum ℂ A, ℂ)) {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, cfcL (a := A) hA (f t)) =
      cfcL (a := A) hA (∫ t in a..b, f t) := by
  change
    (∫ t in Set.Ioc a b, cfcL (a := A) hA (f t)) -
        (∫ t in Set.Ioc b a, cfcL (a := A) hA (f t)) =
      cfcL (a := A) hA
        ((∫ t in Set.Ioc a b, f t) - (∫ t in Set.Ioc b a, f t))
  rw [map_sub]
  congr 1
  · exact cfcL_integral A f hf.1 hA
  · exact cfcL_integral A f hf.2 hA

/-- On an ordered real interval, the unbundled continuous functional calculus
commutes with integration once the restricted scalar symbols form an
integrable continuous-map-valued function. -/
theorem cfc_intervalIntegral_of_le'
    (A : H →L[ℂ] H) (hA : IsStarNormal A)
    (f : ℝ → ℂ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      ContinuousOn (f t) (spectrum ℂ A))
    (hf_int : IntegrableOn
      (fun t : ℝ =>
        ContinuousMap.mkD ((spectrum ℂ A).domRestrict (f t)) 0)
      (Set.Ioc a b) volume) :
    cfc (fun z => ∫ t in a..b, f t z) A =
      ∫ t in a..b, cfc (f t) A := by
  simpa only [intervalIntegral.integral_of_le hab] using
    (cfc_integral' f A hf_cont hf_int hA)

end CayleySelectorBridge

end DavisKahanExt
end TauCeti
