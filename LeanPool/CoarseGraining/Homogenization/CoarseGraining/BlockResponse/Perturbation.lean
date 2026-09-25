/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.Integrand
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.PairHalfScalar
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.VolumeAverage
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.BlockEnergyFirstVariation
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.ResponseJMuAdjoint

/-!
# BlockResponse perturbation, first-variation, and witness identities
(aggregate re-export)

Previously a 2169-line monolithic module; now split along thematic
boundaries into the five files imported above. Shim for backward compatibility.
-/

@[expose] public section
