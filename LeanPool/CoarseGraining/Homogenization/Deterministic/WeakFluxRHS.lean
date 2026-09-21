/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AveragedStepping
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergy
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergyAveraged
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergyPoincare
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.FullStepping
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.FluxStepping
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.GlobalAbsorbed
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.GlobalIteration
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.NeumannCorrector
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge

/-!
# Weak flux estimates with right-hand side

Compatibility wrapper for the Section 3.2.3 RHS weak-flux development.
-/
