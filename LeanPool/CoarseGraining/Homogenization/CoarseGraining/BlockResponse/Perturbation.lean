/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.Integrand
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.PairHalfScalar
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.VolumeAverage
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.BlockEnergyFirstVariation
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.ResponseJMuAdjoint

/-!
# BlockResponse perturbation, first-variation, and witness identities
(aggregate re-export)

Previously a 2169-line monolithic module; now split along thematic
boundaries into the five files imported above. Shim for backward compatibility.
-/
