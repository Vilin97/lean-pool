/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.QuarterAcute
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.GraphSubspace
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Selected Graph -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Contractive graph representation of a selected continuation endpoint

A quarter-acute selected endpoint is not merely unitarily equivalent to the
initial selected subspace.  It is the graph of a unique bounded angular
operator over that initial subspace, and the angular operator is contractive.

This leaf packages that graph operator for the continuation-selected branch.
It does not yet identify the operator with a Riccati solution; that subsequent
step requires reduction of the selected spectral subspace by the perturbed
block operator and comparison with the block-coordinate graph API.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace unitInterval

universe v

section QuarterAcuteGraph

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- Quarter-acuteness implies ordinary acuteness. -/
theorem isUniformlyAcute_of_isQuarterAcute
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    IsUniformlyAcute U V := by
  change U.projectionGap V < Real.sqrt 2 / 2 at hquarter
  change U.projectionGap V < 1
  have hsqrt_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_lt_two : Real.sqrt 2 < 2 := by
    nlinarith
  have hthreshold : Real.sqrt 2 / 2 < (1 : ℝ) :=
    (div_lt_one (by norm_num : (0 : ℝ) < 2)).2 hsqrt_lt_two
  exact lt_trans hquarter hthreshold

/-- If an angular graph is quarter-acute to its base, then its angular
operator has norm strictly below one. -/
theorem norm_angularOperator_lt_one_of_isQuarterAcute
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (X : H →L[ℂ] H) (hX : IsAngularOperator U X)
    (hquarter : IsQuarterAcute U (graphSubspace U X)) :
    ‖X‖ < 1 := by
  change U.projectionGap (graphSubspace U X) < Real.sqrt 2 / 2 at hquarter
  rw [subspaceGap_graphSubspace U X hX] at hquarter
  have hpos : (0 : ℝ) < 1 + ‖X‖ ^ 2 := by positivity
  have hs0 : (0 : ℝ) < Real.sqrt (1 + ‖X‖ ^ 2) :=
    Real.sqrt_pos.mpr hpos
  have hg0 : (0 : ℝ) ≤ ‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2) := by
    positivity
  have hs20 : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  have hgsq :
      (‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2)) ^ 2 =
        ‖X‖ ^ 2 / (1 + ‖X‖ ^ 2) := by
    rw [div_pow, Real.sq_sqrt hpos.le]
  have hhalf : (Real.sqrt 2 / 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsq :
      (‖X‖ / Real.sqrt (1 + ‖X‖ ^ 2)) ^ 2 <
        (Real.sqrt 2 / 2) ^ 2 := by
    nlinarith
  rw [hgsq, hhalf,
    div_lt_div_iff₀ hpos (by norm_num : (0 : ℝ) < 2)] at hsq
  nlinarith [norm_nonneg X]

/-- A quarter-acute pair has a unique contractive angular graph
representation. -/
theorem existsUnique_contractiveAngularOperator_of_isQuarterAcute
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    ∃! X : H →L[ℂ] H,
      IsAngularOperator U X ∧ graphSubspace U X = V ∧ ‖X‖ < 1 := by
  obtain ⟨X, hX, hunique⟩ :=
    existsUnique_angularOperator U V
      (isUniformlyAcute_of_isQuarterAcute U V hquarter)
  have hquarterGraph : IsQuarterAcute U (graphSubspace U X) := by
    simpa only [hX.2] using hquarter
  have hcontractive : ‖X‖ < 1 :=
    norm_angularOperator_lt_one_of_isQuarterAcute U X hX.1 hquarterGraph
  refine ⟨X, ⟨hX.1, hX.2, hcontractive⟩, ?_⟩
  intro Y hY
  exact hunique Y ⟨hY.1, hY.2.1⟩

end QuarterAcuteGraph

section SelectedEndpointGraph

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The continuation-selected endpoint is the graph of a unique contractive
angular operator over the initial selected spectral subspace. -/
theorem existsUnique_selectedEndpointAngularOperator_of_contour_bound
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
    ∃! X : H →L[ℂ] H,
      IsAngularOperator (boundedSelfAdjointSpectralSubspace A hA s hs) X ∧
      graphSubspace (boundedSelfAdjointSpectralSubspace A hA s hs) X =
        boundedSelfAdjointSpectralSubspace (A + K) hAK s hs ∧
      ‖X‖ < 1 := by
  have hquarter :=
    boundedSelfAdjointSpectralSubspaces_endpoints_isQuarterAcute_of_contour_bound
      Γ A K delta hdelta s hs hA hAK hself hsep hidentify hsmall
  exact existsUnique_contractiveAngularOperator_of_isQuarterAcute
    (boundedSelfAdjointSpectralSubspace A hA s hs)
    (boundedSelfAdjointSpectralSubspace (A + K) hAK s hs)
    hquarter

/-- The canonical contractive angular operator of the selected endpoint
branch. -/
noncomputable def selectedEndpointAngularOperator
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
      Real.sqrt 2 / 2) : H →L[ℂ] H :=
  Classical.choose
    (existsUnique_selectedEndpointAngularOperator_of_contour_bound
      Γ A K delta hdelta s hs hA hAK hself hsep hidentify hsmall)

/-- The canonical selected endpoint operator is an angular operator over the
initial selected spectral subspace. -/
theorem selectedEndpointAngularOperator_isAngularOperator
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
    IsAngularOperator (boundedSelfAdjointSpectralSubspace A hA s hs)
      (selectedEndpointAngularOperator Γ A K delta hdelta s hs hA hAK
        hself hsep hidentify hsmall) :=
  (Classical.choose_spec
    (existsUnique_selectedEndpointAngularOperator_of_contour_bound
      Γ A K delta hdelta s hs hA hAK hself hsep hidentify hsmall)).1.1

/-- The graph of the canonical selected endpoint angular operator is exactly
the selected spectral subspace of the perturbed operator. -/
theorem graphSubspace_selectedEndpointAngularOperator
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
    graphSubspace (boundedSelfAdjointSpectralSubspace A hA s hs)
        (selectedEndpointAngularOperator Γ A K delta hdelta s hs hA hAK
          hself hsep hidentify hsmall) =
      boundedSelfAdjointSpectralSubspace (A + K) hAK s hs :=
  (Classical.choose_spec
    (existsUnique_selectedEndpointAngularOperator_of_contour_bound
      Γ A K delta hdelta s hs hA hAK hself hsep hidentify hsmall)).1.2.1

/-- The canonical selected endpoint angular operator is contractive. -/
theorem norm_selectedEndpointAngularOperator_lt_one
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
    ‖selectedEndpointAngularOperator Γ A K delta hdelta s hs hA hAK
      hself hsep hidentify hsmall‖ < 1 :=
  (Classical.choose_spec
    (existsUnique_selectedEndpointAngularOperator_of_contour_bound
      Γ A K delta hdelta s hs hA hAK hself hsep hidentify hsmall)).1.2.2

end SelectedEndpointGraph

end DavisKahanExt
end TauCeti
