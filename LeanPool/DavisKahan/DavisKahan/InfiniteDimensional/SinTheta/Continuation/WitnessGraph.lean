/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.Theorem
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SelectedReduction

/-! # Witness Graph -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Canonical graph of a spectral-continuation witness

The compatibility bridge now identifies every pathwise contour Riesz operator
with the genuine selected spectral projection.  This leaf packages that fact
through `SpectralContinuationWitness`, removes the older explicit
identification argument, and constructs the unique contractive angular graph
of the selected endpoint.

The final theorem records that this graph reduces the perturbed operator.  No
block-coordinate Riccati claim is made here; that requires a separate bridge
from the ambient source spectral subspace to the direct-sum block model.
-/

namespace TauCeti
namespace DavisKahanExt

open TauCeti.DavisKahanExt

open DavisKahan

open Set
open scoped InnerProductSpace unitInterval

universe v

section WitnessSelectedGraph

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

namespace SpectralContinuationWitness

/-- The common contour of a continuation witness is pointwise the genuine
selected spectral projection along the affine path. -/
theorem fixedContourRieszOperator_eq_selectedSpectralProjection
    (C : SpectralContinuationWitness A V s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    fixedContourRieszOperator C.contour (operatorPath A V t) =
      boundedSelfAdjointSpectralProjection (operatorPath A V t)
        (C.separating t ht).selfAdjoint s
        C.sourceSeparatingContour.measurable_selected := by
  rw [← C.geometric_eq t ht]
  simpa only using
    (C.separating t ht).fixedContourRieszOperator_eq_boundedSelfAdjointSpectralProjection

/-- The explicit contour coefficient of a continuation witness controls the
quarter-angle of its endpoint selected spectral subspaces. -/
theorem selectedSpectralSubspaces_isQuarterAcute_of_contour_bound
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    IsQuarterAcute C.sourceSelectedSpectralSubspace
      C.targetSelectedSpectralSubspace := by
  let hself : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (operatorPath A V t).IsSymmetric :=
    fun t ht => (C.separating t ht).selfAdjoint
  let hs : MeasurableSet s := C.sourceSeparatingContour.measurable_selected
  have hidentify : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      fixedContourRieszOperator C.contour (operatorPath A V t) =
        boundedSelfAdjointSpectralProjection (operatorPath A V t)
          (hself t ht) s hs := by
    intro t ht
    simpa only [hself, hs] using
      C.fixedContourRieszOperator_eq_selectedSpectralProjection t ht
  have hquarter :=
    boundedSelfAdjointSpectralSubspaces_endpoints_isQuarterAcute_of_contour_bound
      C.contour A V C.margin C.margin_pos s hs
      C.sourceSeparatingContour.selfAdjoint
      C.targetSeparatingContour.selfAdjoint hself
      C.spectrum_separated hidentify hsmall
  simpa only [sourceSelectedSpectralSubspace,
    targetSelectedSpectralSubspace, hs] using hquarter

/-- A quantitatively small continuation witness has a unique contractive
angular graph representation of its selected endpoint. -/
theorem existsUnique_selectedEndpointAngularOperator
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    ∃! X : H →L[ℂ] H,
      IsAngularOperator C.sourceSelectedSpectralSubspace X ∧
      graphSubspace C.sourceSelectedSpectralSubspace X =
        C.targetSelectedSpectralSubspace ∧
      ‖X‖ < 1 := by
  exact existsUnique_contractiveAngularOperator_of_isQuarterAcute
    C.sourceSelectedSpectralSubspace C.targetSelectedSpectralSubspace
    (C.selectedSpectralSubspaces_isQuarterAcute_of_contour_bound hsmall)

/-- The canonical contractive angular operator selected by a continuation
witness. -/
noncomputable def selectedEndpointAngularOperator
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) : H →L[ℂ] H :=
  Classical.choose (C.existsUnique_selectedEndpointAngularOperator hsmall)

/-- The witness-selected endpoint operator is angular over the source selected
spectral subspace. -/
theorem selectedEndpointAngularOperator_isAngularOperator
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    IsAngularOperator C.sourceSelectedSpectralSubspace
      (C.selectedEndpointAngularOperator hsmall) :=
  (Classical.choose_spec
    (C.existsUnique_selectedEndpointAngularOperator hsmall)).1.1

/-- The graph of the witness-selected endpoint operator is exactly the target
selected spectral subspace. -/
theorem graphSubspace_selectedEndpointAngularOperator
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    graphSubspace C.sourceSelectedSpectralSubspace
        (C.selectedEndpointAngularOperator hsmall) =
      C.targetSelectedSpectralSubspace :=
  (Classical.choose_spec
    (C.existsUnique_selectedEndpointAngularOperator hsmall)).1.2.1

/-- The witness-selected endpoint angular operator is strictly contractive. -/
theorem norm_selectedEndpointAngularOperator_lt_one
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    ‖C.selectedEndpointAngularOperator hsmall‖ < 1 :=
  (Classical.choose_spec
    (C.existsUnique_selectedEndpointAngularOperator hsmall)).1.2.2

/-- Any contractive angular operator with the selected endpoint graph is the
canonical witness-selected operator. -/
theorem eq_selectedEndpointAngularOperator
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2)
    (X : H →L[ℂ] H)
    (hX : IsAngularOperator C.sourceSelectedSpectralSubspace X)
    (hgraph : graphSubspace C.sourceSelectedSpectralSubspace X =
      C.targetSelectedSpectralSubspace)
    (hcontractive : ‖X‖ < 1) :
    X = C.selectedEndpointAngularOperator hsmall :=
  (Classical.choose_spec
    (C.existsUnique_selectedEndpointAngularOperator hsmall)).2 X
      ⟨hX, hgraph, hcontractive⟩

/-- The graph selected by a quantitatively small continuation witness reduces
the perturbed bounded self-adjoint operator. -/
theorem selectedEndpointAngularOperator_graph_reduces
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    ContinuousLinearMap.Reduces (A + V)
      (graphSubspace C.sourceSelectedSpectralSubspace
        (C.selectedEndpointAngularOperator hsmall)) := by
  rw [C.graphSubspace_selectedEndpointAngularOperator hsmall]
  unfold targetSelectedSpectralSubspace
  exact boundedSelfAdjointSpectralSubspace_reduces
    (A + V) C.targetSeparatingContour.selfAdjoint s
    C.targetSeparatingContour.measurable_selected

end SpectralContinuationWitness

end WitnessSelectedGraph

end DavisKahanExt
end TauCeti
namespace TauCeti
namespace DavisKahan
namespace SinTheta
namespace Continuation

open TauCeti.DavisKahanExt

open DavisKahan

open scoped InnerProductSpace Topology



variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The selected Riesz projector of a common-contour witness is norm-continuous
along the affine path. -/
theorem spectralSubspace_path_continuous
    {A V : H →L[ℂ] H} {s : Set ℝ}
    (C : SpectralContinuationWitness A V s) :
    ContinuousOn
      (fun t : ℝ => fixedContourRieszOperator C.contour (operatorPath A V t))
      (Set.Icc 0 1) :=
  continuousOn_fixedContourRieszOperator_operatorPath
    C.contour A V (Set.Icc 0 1) C.margin C.margin_pos
    (fun t ht => (C.separating t ht).selfAdjoint) C.spectrum_separated

/-- A quantitatively small selected branch is acute; the stronger conclusion
provided by the continuation layer is quarter-acuteness. -/
theorem sinTwoTheta_acute_of_small_perturbation
    {A V : H →L[ℂ] H} {s : Set ℝ}
    (C : SpectralContinuationWitness A V s)
    (hsmall : selectedBranchProjectionLipschitzConstant
      C.contour V C.margin < Real.sqrt 2 / 2) :
    IsUniformlyAcute C.sourceSelectedSpectralSubspace C.targetSelectedSpectralSubspace :=
  isUniformlyAcute_of_isQuarterAcute _ _
    (C.selectedSpectralSubspaces_isQuarterAcute_of_contour_bound hsmall)


end Continuation
end SinTheta
end DavisKahan
end TauCeti
