/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SelectedSubspace
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Selected Branch -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# The selected bounded spectral branch

This leaf packages the genuine measurable spectral projections and their ranges
as paths along an affine bounded self-adjoint perturbation.  It also restates
the fixed-contour endpoint transport theorem directly for the unperturbed
operator and the endpoint operator `A + V`.

The contour-to-spectral-projection identification remains an explicit input.
The purpose of this module is to expose a stable selected-branch API for the
later graph identification and quarter-acuteness arguments without reopening
the already green contour, subdivision, or rotation-chain proofs.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace unitInterval

universe v

section SelectedSpectralBranch

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The genuine spectral projection selected at one point of an affine
self-adjoint path. -/
noncomputable def selectedSpectralProjectionPath
    (A V : H →L[ℂ] H) (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A V t).IsSymmetric)
    (t : unitInterval) : H →L[ℂ] H :=
  boundedSelfAdjointSpectralProjection (operatorPath A V t)
    (hself t t.property) s hs

/-- The genuine selected spectral range at one point of an affine
self-adjoint path. -/
noncomputable def selectedSpectralSubspacePath
    (A V : H →L[ℂ] H) (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A V t).IsSymmetric)
    (t : unitInterval) : Submodule ℂ H :=
  boundedSelfAdjointSpectralSubspace (operatorPath A V t)
    (hself t t.property) s hs

/-- Every member of the selected spectral-subspace path has its canonical
orthogonal projection. -/
noncomputable instance selectedSpectralSubspacePath_hasOrthogonalProjection
    (A V : H →L[ℂ] H) (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A V t).IsSymmetric)
    (t : unitInterval) :
    (selectedSpectralSubspacePath A V s hs hself t).HasOrthogonalProjection := by
  unfold selectedSpectralSubspacePath
  infer_instance

/-- The projection path is exactly the canonical star projection onto the
selected spectral-subspace path. -/
theorem selectedSpectralProjectionPath_eq_starProjection
    (A V : H →L[ℂ] H) (s : Set ℝ) (hs : MeasurableSet s)
    (hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A V t).IsSymmetric)
    (t : unitInterval) :
    selectedSpectralProjectionPath A V s hs hself t =
      (selectedSpectralSubspacePath A V s hs hself t).starProjection := by
  exact boundedSelfAdjointSpectralProjection_eq_starProjection
    (operatorPath A V t) (hself t t.property) s hs

/-- Pointwise fixed-contour identification gives unitary transport between the
zero and one values of the selected spectral-projection path. -/
theorem exists_unitary_transport_selectedSpectralProjectionPath_of_identification
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
      W ∘L selectedSpectralProjectionPath A V s hs hself
          (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : unitInterval) =
        selectedSpectralProjectionPath A V s hs hself
          (⟨1, ⟨zero_le_one, le_rfl⟩⟩ : unitInterval) ∘L W := by
  unfold selectedSpectralProjectionPath
  exact exists_unitary_transport_selectedSpectralProjections_of_identification
    Γ A V delta hdelta s hs hself hsep hidentify

/-- Endpoint form of selected spectral-projection transport, stated directly
for `A` and `A + V`. -/
theorem exists_unitary_transport_selectedSpectralProjections_endpoints_of_identification
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (s : Set ℝ) (hs : MeasurableSet s)
    (hA : A.IsSymmetric)
    (hAV : (A + V).IsSymmetric)
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
      W ∘L boundedSelfAdjointSpectralProjection A hA s hs =
        boundedSelfAdjointSpectralProjection (A + V) hAV s hs ∘L W := by
  obtain ⟨W, hWunitary, hWintertwines⟩ :=
    exists_unitary_transport_selectedSpectralProjections_of_identification
      Γ A V delta hdelta s hs hself hsep hidentify
  have hpath0 : operatorPath A V 0 = A := by
    ext x
    simp [operatorPath]
  have hpath1 : operatorPath A V 1 = A + V := by
    ext x
    simp [operatorPath]
  have hP0 :
      boundedSelfAdjointSpectralProjection (operatorPath A V 0)
          (hself 0 (by exact ⟨le_rfl, zero_le_one⟩)) s hs =
        boundedSelfAdjointSpectralProjection A hA s hs := by
    simp only [hpath0]
  have hP1 :
      boundedSelfAdjointSpectralProjection (operatorPath A V 1)
          (hself 1 (by exact ⟨zero_le_one, le_rfl⟩)) s hs =
        boundedSelfAdjointSpectralProjection (A + V) hAV s hs := by
    simp only [hpath1]
  rw [hP0, hP1] at hWintertwines
  exact ⟨W, hWunitary, hWintertwines⟩

/-- Endpoint form for the canonical star projections onto the selected
spectral ranges of `A` and `A + V`. -/
theorem exists_unitary_transport_selectedSpectralSubspaces_endpoints_of_identification
    (Γ : PiecewiseC1ClosedContour) (A V : H →L[ℂ] H)
    (delta : ℝ) (hdelta : 0 < delta)
    (s : Set ℝ) (hs : MeasurableSet s)
    (hA : A.IsSymmetric)
    (hAV : (A + V).IsSymmetric)
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
      W ∘L (boundedSelfAdjointSpectralSubspace A hA s hs).starProjection =
        (boundedSelfAdjointSpectralSubspace (A + V) hAV s hs).starProjection ∘L W := by
  obtain ⟨W, hWunitary, hWintertwines⟩ :=
    exists_unitary_transport_selectedSpectralProjections_endpoints_of_identification
      Γ A V delta hdelta s hs hA hAV hself hsep hidentify
  refine ⟨W, hWunitary, ?_⟩
  rw [← boundedSelfAdjointSpectralProjection_eq_starProjection A hA s hs,
    ← boundedSelfAdjointSpectralProjection_eq_starProjection (A + V) hAV s hs]
  exact hWintertwines

end SelectedSpectralBranch

end DavisKahanExt
end TauCeti
