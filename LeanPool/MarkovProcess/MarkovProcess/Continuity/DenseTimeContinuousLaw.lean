/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Continuity.DenseTimeContinuousExtension
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Transporting dense-time laws to continuous paths

This file transports a kernel on dense-time trajectories to ordinary continuous paths under an
explicit support-on-the-continuous-range hypothesis. It does not prove that support hypothesis.
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory Set

namespace MarkovProcess

section

namespace Kernel

variable {β alpha : Type*} [MeasurableSpace β] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [T2Space alpha]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- A dense-time kernel is almost surely supported on restrictions of continuous paths. -/
def IsSupportedOnContinuousPaths (κ : Kernel β (DenseTime → alpha)) : Prop :=
  ∀ x, ∀ᵐ path ∂κ x, path ∈ Set.range (ContinuousPath.denseRestriction (alpha := alpha))

/-- Transport a dense-time kernel to continuous paths by the measurable extension map. -/
def toContinuousPathKernel (κ : Kernel β (DenseTime → alpha))
    (default : ContinuousPath alpha) : Kernel β (ContinuousPath alpha) :=
  Kernel.mapOfMeasurable κ (ContinuousPath.continuousExtension default)
    (ContinuousPath.measurable_continuousExtension default)

/-- The continuous-path transport agrees with the ordinary kernel map. -/
theorem toContinuousPathKernel_eq_map (κ : Kernel β (DenseTime → alpha))
    (default : ContinuousPath alpha) :
    toContinuousPathKernel κ default =
      κ.map (ContinuousPath.continuousExtension default) :=
  Kernel.mapOfMeasurable_eq_map _
    (ContinuousPath.measurable_continuousExtension default)

/-- A Markov dense-time kernel transports to a Markov continuous-path kernel. -/
theorem isMarkovKernel_toContinuousPathKernel (κ : Kernel β (DenseTime → alpha))
    [IsMarkovKernel κ] (default : ContinuousPath alpha) :
    IsMarkovKernel (toContinuousPathKernel κ default) := by
  rw [toContinuousPathKernel_eq_map]
  exact Kernel.IsMarkovKernel.map _
    (ContinuousPath.measurable_continuousExtension default)

/-- Under the support hypothesis, the transported kernel is independent of the arbitrary
off-range default path. -/
theorem IsSupportedOnContinuousPaths.toContinuousPathKernel_eq
    (κ : Kernel β (DenseTime → alpha)) (hκ : IsSupportedOnContinuousPaths κ)
    (default₁ default₂ : ContinuousPath alpha) :
    toContinuousPathKernel κ default₁ = toContinuousPathKernel κ default₂ := by
  rw [toContinuousPathKernel_eq_map, toContinuousPathKernel_eq_map]
  ext x s hs
  rw [Kernel.map_apply' _ (ContinuousPath.measurable_continuousExtension default₁) x hs,
    Kernel.map_apply' _ (ContinuousPath.measurable_continuousExtension default₂) x hs]
  have hfun : ContinuousPath.continuousExtension default₁ =ᵐ[κ x]
      ContinuousPath.continuousExtension default₂ :=
    (hκ x).mono fun path hpath ↦ by
      obtain ⟨omega, rfl⟩ := hpath
      rw [ContinuousPath.continuousExtension_denseRestriction,
        ContinuousPath.continuousExtension_denseRestriction]
  exact measure_congr (hfun.preimage s)

/-- On the continuous restriction range, extension followed by restriction is the identity. -/
theorem IsSupportedOnContinuousPaths.map_denseRestriction
    (κ : Kernel β (DenseTime → alpha)) (hκ : IsSupportedOnContinuousPaths κ)
    (default : ContinuousPath alpha) :
    (toContinuousPathKernel κ default).map ContinuousPath.denseRestriction = κ := by
  rw [toContinuousPathKernel_eq_map, ← Kernel.map_comp_right]
  · ext x s hs
    rw [Kernel.map_apply' _
      ((ContinuousPath.measurable_denseRestriction).comp
        (ContinuousPath.measurable_continuousExtension default)) x hs]
    have hfun :
        ContinuousPath.denseRestriction ∘ ContinuousPath.continuousExtension default
          =ᵐ[κ x] id :=
      (hκ x).mono fun path hpath ↦
        ContinuousPath.denseRestriction_continuousExtension_of_mem_range default hpath
    simpa only [Set.preimage_id] using measure_congr (hfun.preimage s)
  · exact ContinuousPath.measurable_continuousExtension default
  · exact ContinuousPath.measurable_denseRestriction

end Kernel
end
end MarkovProcess

end PortComputability
