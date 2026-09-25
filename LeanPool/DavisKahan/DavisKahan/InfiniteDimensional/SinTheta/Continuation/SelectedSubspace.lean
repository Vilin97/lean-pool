/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.RotationChain
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SpectralIdentification
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Selected spectral subspaces along a fixed contour

This module closes the assembly seam between pointwise contour spectral
identification and global endpoint transport.  A common separating contour
makes the normalized Riesz operators Lipschitz.  Once each operator is
identified with the genuine measurable spectral projection, the finite chain
of local direct rotations gives one unitary intertwining the endpoint
projections.  Rewriting those projections as canonical star projections gives
the corresponding statement for the selected spectral subspaces.

The hard analytic identification of the contour integral with the spectral
calculus remains an explicit input.  This leaf therefore does not assume the
conclusion that still has to be proved in the spectral-identification branch.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace unitInterval

universe v

section SelectedSubspaceTransport

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Pointwise identification of a uniformly separated fixed-contour Riesz path
with genuine spectral projections yields a unitary intertwiner between the
endpoint spectral projections. -/
theorem exists_unitary_transport_selectedSpectralProjections_of_identification
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A V t).IsSymmetric)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A V t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖)
    (hidentify : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      fixedContourRieszOperator Γ (operatorPath A V t) =
        boundedSelfAdjointSpectralProjection (operatorPath A V t)
          (hself t ht) s hs) :
    ∃ W : H →L[ℂ] H,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧
      W ∘L boundedSelfAdjointSpectralProjection (operatorPath A V 0)
          (hself 0 (by exact ⟨le_rfl, zero_le_one⟩)) s hs =
        boundedSelfAdjointSpectralProjection (operatorPath A V 1)
          (hself 1 (by exact ⟨zero_le_one, le_rfl⟩)) s hs ∘L W := by
  have hprojection : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsOrthogonalProjection
        (fixedContourRieszOperator Γ (operatorPath A V t)) := by
    intro t ht
    exact
      fixedContourRieszOperator_operatorPath_isOrthogonalProjection_of_identification
        Γ A V (Set.Icc (0 : ℝ) 1) s hs hself hidentify ht
  obtain ⟨W, hWunitary, hWintertwines⟩ :=
    exists_unitary_transport_fixedContourRieszOperator
      Γ A V delta hdelta hself hsep hprojection
  refine ⟨W, hWunitary, ?_⟩
  simpa only [
    hidentify 0 (by exact ⟨le_rfl, zero_le_one⟩),
    hidentify 1 (by exact ⟨zero_le_one, le_rfl⟩)] using hWintertwines

/-- Under the same pointwise spectral identification, the canonical star
projections onto the selected endpoint spectral subspaces are unitarily
intertwined. -/
theorem exists_unitary_transport_selectedSpectralSubspaces_of_identification
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A V t).IsSymmetric)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
      ∀ lam ∈ realSpectrum (operatorPath A V t),
        delta ≤ ‖Γ.path x - (lam : ℂ)‖)
    (hidentify : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      fixedContourRieszOperator Γ (operatorPath A V t) =
        boundedSelfAdjointSpectralProjection (operatorPath A V t)
          (hself t ht) s hs) :
    ∃ W : H →L[ℂ] H,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧
      W ∘L
          (boundedSelfAdjointSpectralSubspace (operatorPath A V 0)
            (hself 0 (by exact ⟨le_rfl, zero_le_one⟩)) s hs).starProjection =
        (boundedSelfAdjointSpectralSubspace (operatorPath A V 1)
          (hself 1 (by exact ⟨zero_le_one, le_rfl⟩)) s hs).starProjection ∘L W := by
  obtain ⟨W, hWunitary, hWintertwines⟩ :=
    exists_unitary_transport_selectedSpectralProjections_of_identification
      Γ A V delta hdelta s hs hself hsep hidentify
  refine ⟨W, hWunitary, ?_⟩
  rw [← boundedSelfAdjointSpectralProjection_eq_starProjection
      (operatorPath A V 0)
      (hself 0 (by exact ⟨le_rfl, zero_le_one⟩)) s hs,
    ← boundedSelfAdjointSpectralProjection_eq_starProjection
      (operatorPath A V 1)
      (hself 1 (by exact ⟨zero_le_one, le_rfl⟩)) s hs]
  exact hWintertwines

end SelectedSubspaceTransport

end DavisKahanExt
end TauCeti
