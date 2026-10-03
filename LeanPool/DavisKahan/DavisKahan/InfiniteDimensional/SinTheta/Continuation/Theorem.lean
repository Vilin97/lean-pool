/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.Endpoints
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.RotationChain
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Theorem -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Final bounded spectral-continuation theorem

This leaf packages the common-contour hypotheses needed by the analytic
continuation argument and exports the resulting endpoint statement solely in
terms of the selected spectral subspaces.  The public conclusion contains no
contour integral or continuous-functional-calculus expression.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace unitInterval

universe v

section SpectralContinuation

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Proof data showing that one selected spectral component persists along an
affine bounded self-adjoint path with a common positively separated contour. -/
structure SpectralContinuationWitness
    (A V : H →L[ℂ] H) (s : Set ℝ) where
  /-- The common geometric contour. -/
  contour : PiecewiseC1ClosedContour
  /-- Full spectral-separation data at every path parameter. -/
  separating : ∀ t (_ht : t ∈ Set.Icc (0 : ℝ) 1),
    SpectralSeparatingContour (operatorPath A V t) s
  /-- Every pathwise separation witness uses the common contour. -/
  geometric_eq : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
    (separating t ht).geometric = contour
  /-- One quantitative contour-to-spectrum margin for the whole path. -/
  margin : ℝ
  /-- The common margin is positive. -/
  margin_pos : 0 < margin
  /-- The common contour stays at least the recorded margin from every
  pathwise spectral point. -/
  spectrum_separated : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : unitInterval,
    ∀ lam ∈ realSpectrum (operatorPath A V t),
      margin ≤ ‖contour.path x - (lam : ℂ)‖

namespace SpectralContinuationWitness

variable {A V : H →L[ℂ] H} {s : Set ℝ}

/-- The endpoint separation witness at the unperturbed operator. -/
noncomputable def sourceSeparatingContour
    (C : SpectralContinuationWitness A V s) :
    SpectralSeparatingContour A s := by
  let ht : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  let Γ := C.separating 0 ht
  refine
    { geometric := C.contour
      selfAdjoint := ?_
      measurable_selected := Γ.measurable_selected
      spectralMargin := Γ.spectralMargin
      spectralMargin_pos := Γ.spectralMargin_pos
      spectrum_separated := ?_
      winding_selected := ?_
      winding_complement := ?_ }
  · simpa only [operatorPath_zero] using Γ.selfAdjoint
  · intro t lam hlam
    rw [← C.geometric_eq 0 ht]
    exact Γ.spectrum_separated t lam (by simpa only [operatorPath_zero] using hlam)
  · intro lam hlam hls
    rw [← C.geometric_eq 0 ht]
    exact Γ.winding_selected lam (by simpa only [operatorPath_zero] using hlam) hls
  · intro lam hlam hls
    rw [← C.geometric_eq 0 ht]
    exact Γ.winding_complement lam (by simpa only [operatorPath_zero] using hlam) hls

/-- The endpoint separation witness at the perturbed operator. -/
noncomputable def targetSeparatingContour
    (C : SpectralContinuationWitness A V s) :
    SpectralSeparatingContour (A + V) s := by
  let ht : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  let Γ := C.separating 1 ht
  refine
    { geometric := C.contour
      selfAdjoint := ?_
      measurable_selected := Γ.measurable_selected
      spectralMargin := Γ.spectralMargin
      spectralMargin_pos := Γ.spectralMargin_pos
      spectrum_separated := ?_
      winding_selected := ?_
      winding_complement := ?_ }
  · simpa only [operatorPath_one] using Γ.selfAdjoint
  · intro t lam hlam
    rw [← C.geometric_eq 1 ht]
    exact Γ.spectrum_separated t lam (by simpa only [operatorPath_one] using hlam)
  · intro lam hlam hls
    rw [← C.geometric_eq 1 ht]
    exact Γ.winding_selected lam (by simpa only [operatorPath_one] using hlam) hls
  · intro lam hlam hls
    rw [← C.geometric_eq 1 ht]
    exact Γ.winding_complement lam (by simpa only [operatorPath_one] using hlam) hls

/-- The selected spectral subspace at the source endpoint. -/
noncomputable def sourceSelectedSpectralSubspace
    (C : SpectralContinuationWitness A V s) : Submodule ℂ H :=
  boundedSelfAdjointSpectralSubspace A
    C.sourceSeparatingContour.selfAdjoint s
    C.sourceSeparatingContour.measurable_selected

/-- The selected spectral subspace at the target endpoint. -/
noncomputable def targetSelectedSpectralSubspace
    (C : SpectralContinuationWitness A V s) : Submodule ℂ H :=
  boundedSelfAdjointSpectralSubspace (A + V)
    C.targetSeparatingContour.selfAdjoint s
    C.targetSeparatingContour.measurable_selected

/-- The selected spectral projection at the source endpoint: the Riesz operator of `A`
around the witness's common contour.

The twin of `sourceSelectedSpectralSubspace`, and the operator whose subspace that is.  It
takes the *witness's* contour rather than `sourceSeparatingContour.geometric`; the two agree
by `geometric_eq`, and using the common one keeps the source and target endpoints visibly the
same integral around the same curve. -/
noncomputable def sourceSelectedProjection
    (C : SpectralContinuationWitness A V s) : H →L[ℂ] H :=
  fixedContourRieszOperator C.contour A

/-- The selected spectral projection at the target endpoint. -/
noncomputable def targetSelectedProjection
    (C : SpectralContinuationWitness A V s) : H →L[ℂ] H :=
  fixedContourRieszOperator C.contour (A + V)

/-- The source selected spectral subspace is orthogonally complemented. -/
noncomputable instance sourceSelectedSpectralSubspace_hasOrthogonalProjection
    (C : SpectralContinuationWitness A V s) :
    C.sourceSelectedSpectralSubspace.HasOrthogonalProjection := by
  unfold sourceSelectedSpectralSubspace
  infer_instance

/-- The target selected spectral subspace is orthogonally complemented. -/
noncomputable instance targetSelectedSpectralSubspace_hasOrthogonalProjection
    (C : SpectralContinuationWitness A V s) :
    C.targetSelectedSpectralSubspace.HasOrthogonalProjection := by
  unfold targetSelectedSpectralSubspace
  infer_instance

omit [CompleteSpace H] in
/-- The source endpoint witness retains the common geometric contour. -/
theorem sourceSeparatingContour_geometric
    (C : SpectralContinuationWitness A V s) :
    C.sourceSeparatingContour.geometric = C.contour := by
  rfl

omit [CompleteSpace H] in
/-- The target endpoint witness retains the common geometric contour. -/
theorem targetSeparatingContour_geometric
    (C : SpectralContinuationWitness A V s) :
    C.targetSeparatingContour.geometric = C.contour := by
  rfl

/-- The selected source and target spectral subspaces are unitarily
transported along the affine path.

All contour integration and spectral-calculus identification is hidden behind
`SpectralContinuationWitness`; the conclusion is stated only through the
canonical orthogonal projections onto the endpoint spectral subspaces. -/
theorem exists_unitary_transport_selectedSpectralSubspaces
    (C : SpectralContinuationWitness A V s) :
    ∃ W : H →L[ℂ] H,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧
      W ∘L C.sourceSelectedSpectralSubspace.starProjection =
        C.targetSelectedSpectralSubspace.starProjection ∘L W := by
  obtain ⟨W, hWunitary, hWintertwines⟩ :=
    exists_unitary_transport_of_spectralSeparatingContour_operatorPath
      C.contour A V s C.separating C.geometric_eq
      C.margin C.margin_pos C.spectrum_separated
  have hsource :
      fixedContourRieszOperator C.contour (operatorPath A V 0) =
        C.sourceSelectedSpectralSubspace.starProjection := by
    rw [← C.sourceSeparatingContour_geometric]
    simpa only [sourceSelectedSpectralSubspace] using
      fixedContourRieszOperator_operatorPath_zero_eq_starProjection
        A V C.sourceSeparatingContour
  have htarget :
      fixedContourRieszOperator C.contour (operatorPath A V 1) =
        C.targetSelectedSpectralSubspace.starProjection := by
    rw [← C.targetSeparatingContour_geometric]
    simpa only [targetSelectedSpectralSubspace] using
      fixedContourRieszOperator_operatorPath_one_eq_starProjection
        A V C.targetSeparatingContour
  rw [hsource, htarget] at hWintertwines
  exact ⟨W, hWunitary, hWintertwines⟩

end SpectralContinuationWitness

end SpectralContinuation

end DavisKahanExt
end TauCeti
