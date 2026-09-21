/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.FinalWrappers
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicQuantitativeCutoff
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicCoefficientBounds
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicScalarControls
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicGradientControls
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicCanonicalGradient
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal

/-!
# From single-cube Caccioppoli to the radius raw estimate

Compatibility wrapper for the single-cube-to-raw subdirectory.  The development
now lives in `Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.*`.
-/
