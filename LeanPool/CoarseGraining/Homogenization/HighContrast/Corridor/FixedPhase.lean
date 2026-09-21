/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.CarrierObservable
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.ClampedObservable
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.CorePatchEnergy
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.CutoffData
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.EfronSteinAE
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.EfronSteinPhase
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.MeasurableObservable
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.PerCoreEnergy
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.Recombination
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.Resample
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.Variance
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.VarianceFinal

/-! Supporting modules for Coarse-graining theory for elliptic equations. -/
