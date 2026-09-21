/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.Polish
import LeanPool.MarkovProcess.MarkovProcess.Continuity.GlobalDyadicFloorModification
import LeanPool.MarkovProcess.MarkovProcess.Continuity.DenseTimeContinuousSupport

/-!
# Kolmogorov support for dense-time trajectory kernels

This file applies the global dyadic-floor modification to the coordinate process of a
dense-time trajectory kernel.  A parameterwise Kolmogorov moment condition implies that the
dense-time law is supported on restrictions of continuous paths.

No measurability of the totalized modification as a path-valued map, PDE increment estimate,
Markov property of the resulting paths, or Hunt-process assertion is made here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha]

/-- A parameterwise Kolmogorov moment estimate for the canonical coordinate process implies
almost-sure support of every dense-time trajectory law on restrictions of continuous paths.
The constants and exponents may depend on the kernel parameter. -/
theorem IsSupportedOnContinuousPaths.of_isKolmogorovCoordinate
    (kappa : Kernel beta (DenseTime → alpha)) [IsMarkovKernel kappa]
    (hK : ∀ b, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r) (kappa b) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p) :
    IsSupportedOnContinuousPaths kappa := by
  apply IsSupportedOnContinuousPaths.of_continuousModification kappa
  intro b
  obtain ⟨p, q, gamma, M, hcoord, hgamma, hgammaq⟩ := hK b
  let X : DenseTime → (DenseTime → alpha) → alpha := fun r omega ↦ omega r
  refine ⟨fun t omega ↦ continuousGlobalDyadicFloorLimit X omega t, ?_, ?_⟩
  · intro omega
    exact continuous_continuousGlobalDyadicFloorLimit X omega
  · intro r
    simpa only [X, DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply] using
      IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit
        hcoord hgamma hgammaq r

section ContinuousPathKernel

/-- Under the coordinate Kolmogorov estimate, transporting to continuous paths and restricting
back to dense time recovers the original trajectory kernel.  The path-space transport uses only
the already established measurable extension map. -/
theorem map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
    (kappa : Kernel beta (DenseTime → alpha)) [IsMarkovKernel kappa]
    (default : ContinuousPath alpha)
    (hK : ∀ b, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r) (kappa b) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p) :
    (toContinuousPathKernel kappa default).map ContinuousPath.denseRestriction = kappa := by
  exact IsSupportedOnContinuousPaths.map_denseRestriction kappa
    (IsSupportedOnContinuousPaths.of_isKolmogorovCoordinate kappa hK) default

end ContinuousPathKernel

end Kernel
end
end MarkovProcess
