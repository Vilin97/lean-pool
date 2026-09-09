/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters

/-!
# Binding the primitive carrier transport to the actual cycle parameters

The geometry and support proofs live below the stage controls in
`ActualCarrierTransportBase`.  This module identifies them with the literal
canonical parameter record without adding a solved-field assumption.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualCarrierTransport

open Set Function
open CorrectionInitialization CorrectionInitialization.ActualPrimary

export ActualCarrierTransportBase
  (Point Parameter Plane Index associatedPoint parameterDomain Ordered
   associatedPoint_mem_domain slowMap slowMap_eq slowMap_continuous
   slowCore slowCore_closed referenceLength referenceLength_pos clock clock_pos
   spatialLabel referenceGeometry gap geometry reference_refine
   sourceRegion sourceRegion_closed domain_log_band carrier_band_distance
   ordered_of_carrier carrier_empty_of_not_ordered coordinates_clock native_coordinates
   mem_sourceRegion labelCarrier_iff_sourceRegion activeSlowCore activeSlowCore_closed
   canonicalSourceRegion canonicalSourceRegion_closed labelCarrier_iff_canonicalSourceRegion
   cutoff cutoff_eq_native reference_outer_injective geometry_outer_injective)

variable {B N0 : ℕ}

@[simp] theorem domain_eq :
    ActualCarrierTransportBase.domain = ActualInitialization.geometry.domain := rfl

@[simp] theorem labelCarrier_eq (l : Index B N0) (n : ℕ) :
    ActualCarrierTransportBase.labelCarrier l n = ActualInitialization.labelCarrier l n := rfl

theorem canonical_geometry (l : Index B N0) (n : ℕ) :
    (ActualParticularStageControls.canonicalParameters (l.2,l.1)).geometry n =
      geometry l n := rfl

theorem canonical_length (l : Index B N0) (n : ℕ) :
    (ActualParticularStageControls.canonicalParameters (l.2,l.1)).length n =
      referenceLength l / clock l n := rfl

theorem canonical_cutoff (l : Index B N0) (n : ℕ) :
    (ActualParticularStageControls.canonicalParameters (l.2,l.1)).cutoff n =
      ActualGaussianCoverage.nativeCutoff slots.radius (referenceLength l)
        slots.radius_pos (referenceLength_pos l) (clock l n) :=
  ActualCarrierTransportBase.cutoff_eq_native l n

theorem fixed_geometry (l : Index B N0) (n : ℕ) :
    ((ActualCycleParameters.fixedParameters B N0).particular l).geometry n =
      geometry l n := rfl

theorem fixed_length (l : Index B N0) (n : ℕ) :
    ((ActualCycleParameters.fixedParameters B N0).particular l).length n =
      referenceLength l / clock l n := rfl

theorem fixed_cutoff (l : Index B N0) (n : ℕ) :
    ((ActualCycleParameters.fixedParameters B N0).particular l).cutoff n =
      ActualGaussianCoverage.nativeCutoff slots.radius (referenceLength l)
        slots.radius_pos (referenceLength_pos l) (clock l n) :=
  canonical_cutoff l n

end NavierStokes.ActualCarrierTransport
