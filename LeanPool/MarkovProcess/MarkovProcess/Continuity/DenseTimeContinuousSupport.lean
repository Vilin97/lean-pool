/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Continuity.DenseTimeContinuousLaw


/-!
# Continuous support from a continuous modification

This file turns a continuous-time modification of the coordinate process of a dense-time law
into almost-sure support on restrictions of continuous paths. The only measure-theoretic step is
the simultaneous choice of all dense-time modification identities, which is valid because
`DenseTime` is countable.

The continuous modification itself is not constructed here: it is the Kolmogorov--Chentsov
argument of `Continuity/GlobalDyadicFloorModification.lean`, applied to dense-time trajectory
kernels in `Continuity/KolmogorovDenseTimeContinuousSupport.lean`.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory Set

namespace MarkovProcess

section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha]

/-- A continuous-time modification of every coordinate law implies that the original dense-time
law is almost surely the restriction of a continuous path. The modification may depend on the
kernel parameter `b`; no measurable choice of modifications in `b` is required for this
pointwise support conclusion. -/
theorem IsSupportedOnContinuousPaths.of_continuousModification
    (kappa : Kernel beta (DenseTime → alpha))
    (hmod : ∀ b, ∃ Y : NNReal → (DenseTime → alpha) → alpha,
      (∀ omega, Continuous (fun t ↦ Y t omega)) ∧
        ∀ q, (fun omega : DenseTime → alpha ↦ omega q) =ᵐ[kappa b]
          Y (DenseTime.castOrderEmbedding q)) :
    IsSupportedOnContinuousPaths kappa := by
  intro b
  obtain ⟨Y, hYcont, hYmod⟩ := hmod b
  have hmod_all : ∀ᵐ omega ∂kappa b, ∀ q,
      omega q = Y (DenseTime.castOrderEmbedding q) omega :=
    ae_all_iff.2 hYmod
  filter_upwards [hmod_all] with omega homega
  let path : ContinuousPath alpha :=
    ⟨fun t ↦ Y t omega, hYcont omega⟩
  refine ⟨path, ?_⟩
  funext q
  exact (homega q).symm

end Kernel
end
end MarkovProcess

end PortComputability
