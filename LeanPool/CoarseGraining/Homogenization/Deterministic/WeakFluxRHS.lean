/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AveragedStepping
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergy
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergyAveraged
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergyPoincare
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.FullStepping
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.FluxStepping
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.GlobalAbsorbed
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.GlobalIteration
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.NeumannCorrector
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge

/-!
# Weak flux estimates with right-hand side

Compatibility wrapper for the Section 3.2.3 RHS weak-flux development.
-/

@[expose] public section
