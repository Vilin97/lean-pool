/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SelectedBranch
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Quarter Acute -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Quantitative quarter-acuteness for a selected continuation branch

This leaf transfers the fixed-contour Riesz Lipschitz estimate to the genuine
selected spectral-projection path once pointwise contour identification is
available.  It then gives a direct sufficient condition for the selected
endpoint subspaces to lie below the quarter-angle threshold.

The condition is stated using the explicit contour length and spectral margin.
It is a quantitative continuation result, not yet the sharp off-diagonal
`sqrt 2 * d` theorem.  The latter still requires the branch-specific spectral
enclosures and scalar optimization.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace unitInterval

universe v

section SelectedBranchQuarterAcute

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The explicit Lipschitz coefficient supplied by one fixed separating
contour along an affine bounded perturbation path. -/
noncomputable def selectedBranchProjectionLipschitzConstant
    (Γ : PiecewiseC1ClosedContour) (K : H →L[ℂ] H) (delta : ℝ) : ℝ :=
  ‖rieszNormalization‖ *
    (delta⁻¹ ^ 2 * ‖K‖ * Γ.contourLength)

/-- Pointwise contour identification transfers the fixed-contour Riesz
operator estimate to the genuine selected spectral-projection path. -/
theorem norm_selectedSpectralProjectionPath_sub_le_of_identification
    (Γ : PiecewiseC1ClosedContour) (A K : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A K t).IsSymmetric)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A K t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖)
    (hidentify : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      fixedContourRieszOperator Γ (operatorPath A K t) =
        boundedSelfAdjointSpectralProjection (operatorPath A K t)
          (hself t ht) s hs)
    (t u : unitInterval) :
    ‖selectedSpectralProjectionPath A K s hs hself t -
        selectedSpectralProjectionPath A K s hs hself u‖ ≤
      selectedBranchProjectionLipschitzConstant Γ K delta *
        ‖(t : ℝ) - (u : ℝ)‖ := by
  have hmain := norm_fixedContourRieszOperator_operatorPath_sub_le
    Γ A K (Set.Icc (0 : ℝ) 1) delta hdelta hself hsep
      t.property u.property
  rw [hidentify t t.property, hidentify u u.property] at hmain
  simpa only [selectedSpectralProjectionPath,
    selectedBranchProjectionLipschitzConstant] using hmain

/-- The projection-gap version of the selected branch Lipschitz estimate. -/
theorem subspaceGap_selectedSpectralSubspacePath_le_of_identification
    (Γ : PiecewiseC1ClosedContour) (A K : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A K t).IsSymmetric)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A K t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖)
    (hidentify : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      fixedContourRieszOperator Γ (operatorPath A K t) =
        boundedSelfAdjointSpectralProjection (operatorPath A K t)
          (hself t ht) s hs)
    (t u : unitInterval) :
    Submodule.projectionGap
        (selectedSpectralSubspacePath A K s hs hself t)
        (selectedSpectralSubspacePath A K s hs hself u) ≤
      selectedBranchProjectionLipschitzConstant Γ K delta *
        ‖(t : ℝ) - (u : ℝ)‖ := by
  change
    ‖(selectedSpectralSubspacePath A K s hs hself t).starProjection -
        (selectedSpectralSubspacePath A K s hs hself u).starProjection‖ ≤ _
  rw [← selectedSpectralProjectionPath_eq_starProjection A K s hs hself t,
    ← selectedSpectralProjectionPath_eq_starProjection A K s hs hself u]
  exact norm_selectedSpectralProjectionPath_sub_le_of_identification
    Γ A K delta hdelta s hs hself hsep hidentify t u

/-- If the explicit contour Lipschitz coefficient is below the quarter-angle
projection threshold, then the selected endpoint subspaces are quarter-acute. -/
theorem selectedSpectralSubspacePath_endpoints_isQuarterAcute_of_contour_bound
    (Γ : PiecewiseC1ClosedContour) (A K : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A K t).IsSymmetric)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A K t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖)
    (hidentify : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      fixedContourRieszOperator Γ (operatorPath A K t) =
        boundedSelfAdjointSpectralProjection (operatorPath A K t)
          (hself t ht) s hs)
    (hsmall : selectedBranchProjectionLipschitzConstant Γ K delta <
      Real.sqrt 2 / 2) :
    IsQuarterAcute
      (selectedSpectralSubspacePath A K s hs hself
        (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : unitInterval))
      (selectedSpectralSubspacePath A K s hs hself
        (⟨1, ⟨zero_le_one, le_rfl⟩⟩ : unitInterval)) := by
  let t0 : unitInterval := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
  let t1 : unitInterval := ⟨1, ⟨zero_le_one, le_rfl⟩⟩
  have hgap := subspaceGap_selectedSpectralSubspacePath_le_of_identification
    Γ A K delta hdelta s hs hself hsep hidentify t0 t1
  have hdist : ‖(t0 : ℝ) - (t1 : ℝ)‖ = 1 := by
    simp [t0, t1]
  change Submodule.projectionGap
      (selectedSpectralSubspacePath A K s hs hself t0)
      (selectedSpectralSubspacePath A K s hs hself t1) < Real.sqrt 2 / 2
  calc
    Submodule.projectionGap
        (selectedSpectralSubspacePath A K s hs hself t0)
        (selectedSpectralSubspacePath A K s hs hself t1) ≤
      selectedBranchProjectionLipschitzConstant Γ K delta *
        ‖(t0 : ℝ) - (t1 : ℝ)‖ := hgap
    _ = selectedBranchProjectionLipschitzConstant Γ K delta := by
      rw [hdist, mul_one]
    _ < Real.sqrt 2 / 2 := hsmall

/-- Endpoint form stated directly for the selected spectral subspaces of `A`
and `A + K`. -/
theorem boundedSelfAdjointSpectralSubspaces_endpoints_isQuarterAcute_of_contour_bound
    (Γ : PiecewiseC1ClosedContour) (A K : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (s : Set ℝ) (hs : MeasurableSet s)
    (hA : A.IsSymmetric)
    (hAK : (A + K).IsSymmetric)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A K t).IsSymmetric)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A K t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖)
    (hidentify : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      fixedContourRieszOperator Γ (operatorPath A K t) =
        boundedSelfAdjointSpectralProjection (operatorPath A K t)
          (hself t ht) s hs)
    (hsmall : selectedBranchProjectionLipschitzConstant Γ K delta <
      Real.sqrt 2 / 2) :
    IsQuarterAcute
      (boundedSelfAdjointSpectralSubspace A hA s hs)
      (boundedSelfAdjointSpectralSubspace (A + K) hAK s hs) := by
  have hquarter :=
    selectedSpectralSubspacePath_endpoints_isQuarterAcute_of_contour_bound
      Γ A K delta hdelta s hs hself hsep hidentify hsmall
  have hpath0 : operatorPath A K 0 = A := by
    ext x
    simp [operatorPath]
  have hpath1 : operatorPath A K 1 = A + K := by
    ext x
    simp [operatorPath]
  simpa only [selectedSpectralSubspacePath, hpath0, hpath1] using hquarter

end SelectedBranchQuarterAcute

end DavisKahanExt
end TauCeti
