/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.MaximalDomainTransport
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.GraphClosedness
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.CompactGraphEmbedding
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.FreeBeamAnalyticFoundation
import Mathlib.Tactic

/-!
# Assembly of the paper-facing free-beam analytic foundation

The existing `SobolevTraceFoundation` is expressed entirely in ambient
submodules.  The natural construction, however, starts with a graph Hilbert
space carrying continuous trace maps.  This file proves that the structural
parts of the paper-facing interface follow automatically from a
`FourthOrderTraceModel`, dense embedding, and graph-norm lower bound.

After this reduction, the remaining genuinely analytic obligations are Green
symmetry, self-adjointness, compactness, affine-kernel identification,
root localization, and ODE-to-spectrum identification.
-/

open Set
open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Analytic

noncomputable section

open Abstract
open FreeBeam

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Remaining completion data after the graph-space and trace-kernel
constructions have been automated. -/
structure BeamFoundationCompletionData where
  /-- The abstract fourth-order trace model underlying the beam realization. -/
  traceModel : Abstract.FourthOrderTraceModel (𝕜 := ℂ) (H := H) (V := V)
  free_dense : DenseRange traceModel.freeEmbed
  /-- The positive lower bound controlling the norm by the free graph map. -/
  graphConstant : ℝ
  graphConstant_pos : 0 < graphConstant
  graph_lower_bound : ∀ x : traceModel.freeSubspace,
    graphConstant * ‖x‖ ≤ ‖traceModel.freeGraphMap x‖
  green_identity : ∀ x y : traceModel.freeAmbientDomain,
    ⟪traceModel.freeFourthAmbient x, (y : H)⟫_ℂ =
      ⟪(x : H), traceModel.freeFourthAmbient y⟫_ℂ
  selfAdjoint :
    _root_.IsSelfAdjoint (traceModel.toPartialMapOfGraphNorm free_dense
      graphConstant_pos graph_lower_bound)
  graph_compact :
    Abstract.SequentiallyCompactGraphEmbedding
      (traceModel.toPartialMapOfGraphNorm free_dense
        graphConstant_pos graph_lower_bound)
  /-- An isometric identification of the affine kernel with complex two-dimensional Euclidean
  space. -/
  affineKernelEquiv :
    EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℂ]
      partialMapKernel
        (traceModel.toPartialMapOfGraphNorm free_dense
          graphConstant_pos graph_lower_bound)
  /-- Localization and minimality data for the first positive characteristic root. -/
  rootLocalization : PositiveRootLocalization
  /-- The first positive spectral value, equal to the fourth power of the localized root. -/
  firstPositiveSpectralValue : ℝ
  firstPositiveSpectralValue_eq :
    firstPositiveSpectralValue = rootLocalization.firstPositiveRoot ^ 4
  spectrum_nonnegative :
    TauCeti.LinearPMap.realSpectrum (traceModel.toPartialMapOfGraphNorm
      free_dense graphConstant_pos graph_lower_bound) ⊆ Set.Ici 0
  positive_spectrum_characterization : ∀ lambda : ℝ,
    lambda ∈ TauCeti.LinearPMap.realSpectrum
      (traceModel.toPartialMapOfGraphNorm free_dense
        graphConstant_pos graph_lower_bound) →
    0 < lambda →
    ∃ beta : ℝ, 0 < beta ∧ characteristic beta = 0 ∧ lambda = beta ^ 4

namespace BeamFoundationCompletionData

/-- Closed graph used by the assembled operator. -/
theorem closed_freeGraph
    (D : BeamFoundationCompletionData (H := H) (V := V)) :
    IsClosed (Set.range fun x : D.traceModel.freeAmbientDomain =>
      ((x : H), D.traceModel.freeFourthAmbient x)) :=
  D.traceModel.isClosed_ambientGraph_of_graphNorm_bound
    D.graphConstant_pos D.graph_lower_bound

omit [CompleteSpace V] in
/-- Density of the assembled free domain. -/
theorem dense_freeDomain
    (D : BeamFoundationCompletionData (H := H) (V := V)) :
    Dense (D.traceModel.freeAmbientDomain : Set H) :=
  D.traceModel.dense_freeAmbientDomain D.free_dense

/-- The trace-space completion data constructs the exact paper-facing analytic
foundation. -/
noncomputable def toSobolevTraceFoundation
    (D : BeamFoundationCompletionData (H := H) (V := V)) :
    FreeBeam.SobolevTraceFoundation (H := H) where
  maximalDomain := D.traceModel.maximalAmbientDomain
  freeDomain := D.traceModel.freeAmbientDomain
  free_le_maximal := D.traceModel.freeAmbientDomain_le_maximalAmbientDomain
  maximalFourth := D.traceModel.maximalFourthAmbient
  freeFourth := D.traceModel.freeFourthAmbient
  freeFourth_agrees := D.traceModel.freeFourthAmbient_agrees
  traceSecondLeft := D.traceModel.traceSecondLeftAmbient
  traceThirdLeft := D.traceModel.traceThirdLeftAmbient
  traceSecondRight := D.traceModel.traceSecondRightAmbient
  traceThirdRight := D.traceModel.traceThirdRightAmbient
  mem_freeDomain_iff := D.traceModel.mem_freeAmbientDomain_iff_traces
  dense_freeDomain := D.dense_freeDomain
  closed_freeGraph := D.closed_freeGraph
  green_identity := D.green_identity
  selfAdjoint := by
    simpa [Abstract.FourthOrderTraceModel.toPartialMapOfGraphNorm,
      Abstract.FourthOrderTraceModel.toPartialMap] using D.selfAdjoint
  graph_compact := by
    intro x hx
    apply D.graph_compact x
    rcases hx with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    change ‖(x n : H)‖ ^ 2 +
      ‖D.traceModel.freeFourthAmbient (x n)‖ ^ 2 ≤ C
    simpa only [Abstract.FourthOrderTraceModel.freeFourthAmbient_inverse] using hC n
  affineKernelEquiv := by
    simpa [Abstract.FourthOrderTraceModel.toPartialMapOfGraphNorm,
      Abstract.FourthOrderTraceModel.toPartialMap] using D.affineKernelEquiv
  rootLocalization := D.rootLocalization
  firstPositiveSpectralValue := D.firstPositiveSpectralValue
  firstPositiveSpectralValue_eq := D.firstPositiveSpectralValue_eq
  spectrum_nonnegative := by
    simpa [Abstract.FourthOrderTraceModel.toPartialMapOfGraphNorm,
      Abstract.FourthOrderTraceModel.toPartialMap] using D.spectrum_nonnegative
  positive_spectrum_characterization := by
    intro lambda hlambda hpositive
    apply D.positive_spectrum_characterization lambda
    · simpa [Abstract.FourthOrderTraceModel.toPartialMapOfGraphNorm,
        Abstract.FourthOrderTraceModel.toPartialMap] using hlambda
    · exact hpositive

/-- The assembled first positive spectral value exceeds `500`. -/
theorem firstPositiveSpectralValue_gt_five_hundred
    (D : BeamFoundationCompletionData (H := H) (V := V)) :
    500 < D.firstPositiveSpectralValue := by
  exact D.toSobolevTraceFoundation.firstPositiveSpectralValue_gt_five_hundred

end BeamFoundationCompletionData

end

end Analytic
end FreeBeam
end DavisKahan
end TauCeti
