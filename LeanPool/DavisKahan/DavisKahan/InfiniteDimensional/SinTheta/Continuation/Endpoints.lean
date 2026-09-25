/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SpectralIdentification

/-!
# Endpoint identification for spectral continuation

This leaf records the exact affine-path endpoint formulas and rewrites the
fixed-contour Riesz operators at those endpoints as the genuine orthogonal
projections onto the selected bounded spectral subspaces.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace

universe v

section AffineEndpoints

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- The affine perturbation path starts at the unperturbed operator. -/
@[simp] theorem operatorPath_zero (A V : H →L[ℂ] H) :
    operatorPath A V 0 = A := by
  simp [operatorPath]

omit [CompleteSpace H] in
/-- The affine perturbation path ends at the perturbed operator. -/
@[simp] theorem operatorPath_one (A V : H →L[ℂ] H) :
    operatorPath A V 1 = A + V := by
  simp [operatorPath]

/-- A fixed contour attached to a full separation witness is the genuine
bounded spectral projection selected by that witness. -/
theorem SpectralSeparatingContour.fixedContourRieszOperator_eq_boundedSelfAdjointSpectralProjection
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    fixedContourRieszOperator Γ.geometric A =
      boundedSelfAdjointSpectralProjection
        A Γ.selfAdjoint s Γ.measurable_selected := by
  rw [fixedContourRieszOperator_eq_contourRieszProjection Γ]
  exact Γ.contourRieszProjection_eq_boundedSelfAdjointSpectralProjection

/-- The same endpoint operator is the canonical star projection onto the
selected bounded spectral subspace. -/
theorem SpectralSeparatingContour.fixedContourRieszOperator_eq_starProjection
    {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    fixedContourRieszOperator Γ.geometric A =
      (boundedSelfAdjointSpectralSubspace
        A Γ.selfAdjoint s Γ.measurable_selected).starProjection := by
  rw [Γ.fixedContourRieszOperator_eq_boundedSelfAdjointSpectralProjection]
  exact boundedSelfAdjointSpectralProjection_eq_starProjection
    A Γ.selfAdjoint s Γ.measurable_selected

/-- At path parameter zero, a separating contour identifies the continued
operator with the source selected spectral projection. -/
theorem fixedContourRieszOperator_operatorPath_zero_eq_boundedSelfAdjointSpectralProjection
    (A V : H →L[ℂ] H) {s : Set ℝ}
    (Γ₀ : SpectralSeparatingContour A s) :
    fixedContourRieszOperator Γ₀.geometric (operatorPath A V 0) =
      boundedSelfAdjointSpectralProjection
        A Γ₀.selfAdjoint s Γ₀.measurable_selected := by
  rw [operatorPath_zero]
  exact Γ₀.fixedContourRieszOperator_eq_boundedSelfAdjointSpectralProjection

/-- At path parameter one, a separating contour identifies the continued
operator with the target selected spectral projection. -/
theorem fixedContourRieszOperator_operatorPath_one_eq_boundedSelfAdjointSpectralProjection
    (A V : H →L[ℂ] H) {s : Set ℝ}
    (Γ₁ : SpectralSeparatingContour (A + V) s) :
    fixedContourRieszOperator Γ₁.geometric (operatorPath A V 1) =
      boundedSelfAdjointSpectralProjection
        (A + V) Γ₁.selfAdjoint s Γ₁.measurable_selected := by
  rw [operatorPath_one]
  exact Γ₁.fixedContourRieszOperator_eq_boundedSelfAdjointSpectralProjection

/-- The zero endpoint is the canonical projection onto the source selected
spectral subspace. -/
theorem fixedContourRieszOperator_operatorPath_zero_eq_starProjection
    (A V : H →L[ℂ] H) {s : Set ℝ}
    (Γ₀ : SpectralSeparatingContour A s) :
    fixedContourRieszOperator Γ₀.geometric (operatorPath A V 0) =
      (boundedSelfAdjointSpectralSubspace
        A Γ₀.selfAdjoint s Γ₀.measurable_selected).starProjection := by
  rw [operatorPath_zero]
  exact Γ₀.fixedContourRieszOperator_eq_starProjection

/-- The one endpoint is the canonical projection onto the target selected
spectral subspace. -/
theorem fixedContourRieszOperator_operatorPath_one_eq_starProjection
    (A V : H →L[ℂ] H) {s : Set ℝ}
    (Γ₁ : SpectralSeparatingContour (A + V) s) :
    fixedContourRieszOperator Γ₁.geometric (operatorPath A V 1) =
      (boundedSelfAdjointSpectralSubspace
        (A + V) Γ₁.selfAdjoint s Γ₁.measurable_selected).starProjection := by
  rw [operatorPath_one]
  exact Γ₁.fixedContourRieszOperator_eq_starProjection

end AffineEndpoints

end DavisKahanExt
end TauCeti
