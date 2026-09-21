/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SelectedGraph
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Selected Reduction -/

open TauCeti.DavisKahan.Angle


/-!
# Reduction of the selected continuation graph

The selected endpoint constructed by continuation is a genuine spectral
subspace of the perturbed self-adjoint operator.  This leaf proves directly
from the commutation of the Borel calculus that every such bounded spectral
subspace reduces its operator.  Transporting reduction through the
selected-graph identity then shows that the canonical contractive selected
endpoint graph is reducing.

No block-coordinate identification is made here.  The subsequent Riccati
bridge must transport this ambient reducing graph to the direct-sum block
model before invoking the bounded Riccati reduction theorem.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace unitInterval

universe v

section SpectralSubspaceReduction

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A genuine bounded self-adjoint spectral projection commutes pointwise with
its operator.

This used to route through Spectra's Stone group: the operator was realized as
the generator of `genToGroup`, and the commutation came from
`generator_spectralProjection_comm`.  None of that is needed.  A spectral
projection is the Borel calculus of an indicator symbol, the operator is the
Borel calculus of the coordinate symbol, and the calculus is commutative. -/
theorem boundedSelfAdjointSpectralProjection_apply_comm
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) (x : H) :
    A (boundedSelfAdjointSpectralProjection A hA s hs x) =
      boundedSelfAdjointSpectralProjection A hA s hs (A x) := by
  have hcomm := TauCeti.BorelCalculus.boundedPVM_proj_comm
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA) s hs
  exact congrArg (fun T : H →L[ℂ] H => T x) hcomm

/-- Every genuine bounded spectral subspace reduces its self-adjoint
operator. -/
theorem boundedSelfAdjointSpectralSubspace_reduces
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) :
    A.Reduces (boundedSelfAdjointSpectralSubspace A hA s hs) := by
  apply ContinuousLinearMap.IsSymmetric.reduces_of_invariant hA
  intro x hx
  change x ∈ (boundedSelfAdjointSpectralProjection A hA s hs).range at hx
  rcases hx with ⟨y, rfl⟩
  change
    A (boundedSelfAdjointSpectralProjection A hA s hs y) ∈
      (boundedSelfAdjointSpectralProjection A hA s hs).range
  refine ⟨A y, ?_⟩
  exact (boundedSelfAdjointSpectralProjection_apply_comm A hA s hs y).symm

end SpectralSubspaceReduction

section SelectedEndpointReduction

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The graph of the canonical continuation-selected endpoint angular
operator reduces the perturbed bounded self-adjoint operator. -/
theorem selectedEndpointAngularOperator_graph_reduces_of_contour_bound
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
    ContinuousLinearMap.Reduces (A + K)
      (graphSubspace (boundedSelfAdjointSpectralSubspace A hA s hs)
        (selectedEndpointAngularOperator Γ A K delta hdelta s hs hA hAK
          hself hsep hidentify hsmall)) := by
  rw [graphSubspace_selectedEndpointAngularOperator Γ A K delta hdelta
    s hs hA hAK hself hsep hidentify hsmall]
  exact boundedSelfAdjointSpectralSubspace_reduces (A + K) hAK s hs

end SelectedEndpointReduction

end DavisKahanExt
end TauCeti
