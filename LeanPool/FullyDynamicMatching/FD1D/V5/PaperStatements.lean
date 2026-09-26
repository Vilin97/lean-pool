/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.V5.Main
public import LeanPool.FullyDynamicMatching.FD1D.V5.StatementModel

/-!
# Palomar endpoint for optimal fully dynamic matching

This module instantiates the compact paper-facing stochastic model with the
hierarchical V5 selector and transfers the proved continuous-process bounds.
-/

@[expose] public section

namespace FD1D.V5.Palomar

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory Topology unitInterval

/-- The measurable hierarchical selector used by the V5 formalization. -/
def hierarchicalPolicy (m : ℕ) (hm : 1 ≤ m) : OnlinePolicy m where
  select s u :=
    FD1D.V5.spatialSelectedLabel
      (FD1D.V5.treeDepth m) (FD1D.V5.parameterA m : ℝ)
      (FD1D.SupplyConfiguration.canonicalFallback (by omega)) s u
  selectMeasurable := by
    exact FD1D.V5.spatialSelectedLabel_measurable
      (FD1D.V5.treeDepth m) (FD1D.V5.parameterA m : ℝ)
      (FD1D.SupplyConfiguration.canonicalFallback (by omega))
  stepMeasurable := by
    simpa only [FD1D.V5.spatialStep] using
      (FD1D.V5.spatialStep_measurable
        (FD1D.V5.treeDepth m) (FD1D.V5.parameterA m : ℝ)
        (FD1D.SupplyConfiguration.canonicalFallback (by omega)))

private theorem trajectoryFromState_hierarchicalPolicy_eq
    {m : ℕ} (hm : 1 ≤ m) (s₀ : Inventory m) :
    trajectoryFromState (hierarchicalPolicy m hm) s₀ =
      FD1D.V5.ContinuousProcess.trajectoryLawFromState
        (L := FD1D.V5.treeDepth m) s₀
        (FD1D.V5.parameterA m : ℝ)
        (FD1D.SupplyConfiguration.canonicalFallback (by omega)) := by
  rfl

private theorem uniformTrajectory_hierarchicalPolicy_eq
    {m : ℕ} (hm : 1 ≤ m) :
    uniformTrajectory (hierarchicalPolicy m hm) =
      FD1D.V5.ContinuousProcess.trajectoryLaw
        (L := FD1D.V5.treeDepth m) (m := m)
        (FD1D.V5.parameterA m : ℝ)
        (FD1D.SupplyConfiguration.canonicalFallback (by omega)) := by
  rfl

private theorem processCost_hierarchicalPolicy_eq
    {m : ℕ} (hm : 1 ≤ m) (z : ProcessState m) :
    processCost (hierarchicalPolicy m hm) z =
      FD1D.V5.ContinuousProcess.processCost
        (FD1D.V5.treeDepth m) (FD1D.V5.parameterA m : ℝ)
        (FD1D.SupplyConfiguration.canonicalFallback (by omega)) z := by
  rfl

private theorem trajectoryRMSCostFromState_hierarchicalPolicy_eq
    {m : ℕ} (hm : 1 ≤ m) (s₀ : Inventory m) :
    trajectoryRMSCostFromState (hierarchicalPolicy m hm) s₀ =
      FD1D.V5.ContinuousProcess.trajectoryRMSCostFromState m hm s₀ := by
  funext t
  unfold trajectoryRMSCostFromState
    FD1D.V5.ContinuousProcess.trajectoryRMSCostFromState
    FD1D.V5.ContinuousProcess.trajectoryExpectedSquaredCostFromState
    FD1D.V5.ContinuousProcess.trajectoryExpectedSquaredCostFrom
  rw [trajectoryFromState_hierarchicalPolicy_eq hm s₀]
  apply congrArg Real.sqrt
  apply integral_congr_ae
  filter_upwards with path
  rw [FD1D.V5.ContinuousProcess.processSquaredCost_eq_sq]
  exact congrArg (fun x : ℝ => x ^ 2)
    (processCost_hierarchicalPolicy_eq hm (path t))

private def refreshSupplyOfInventory
    (L : ℕ) (initial : Inventory m) : FD1D.RefreshSupply L m where
  location j := initial j
  leaf _ := default
  location_mem_unit j := (initial j).property

private theorem initializedAverageCost_hierarchicalPolicy_eq
    {m N : ℕ} (hm : 1 ≤ m) (initial demand : Inventory m)
    (path : ℕ → ProcessState m) :
    initializedAverageCost
        (hierarchicalPolicy m hm) initial demand N path =
      FD1D.V5.ContinuousProcess.joinedTrajectoryAverageCost
        (refreshSupplyOfInventory (FD1D.V5.treeDepth m) initial)
        (fun j => (demand j : ℝ))
        (FD1D.V5.parameterA m : ℝ) (by omega) N path := by
  unfold initializedAverageCost
    FD1D.V5.ContinuousProcess.joinedTrajectoryAverageCost
  rw [FD1D.V5.ContinuousProcess.sum_joinedInitializationStepCost]
  congr 2

private theorem policyGuarantees
    {m : ℕ} (hm : 2 ≤ m) :
    PolicyGuarantees m (hierarchicalPolicy m (by omega)) where
  arbitraryInitialRMS := by
    intro s₀
    rw [trajectoryRMSCostFromState_hierarchicalPolicy_eq (by omega) s₀]
    simpa [universalConstant, FD1D.V5.universalConstant] using
      (FD1D.V5.limsup_trajectoryRMSCostFromState_le_log_succ hm s₀)
  initializedFiniteHorizon := by
    intro N hN initial demand
    rw [uniformTrajectory_hierarchicalPolicy_eq (by omega)]
    apply le_of_eq_of_le
      (integral_congr_ae
        (Filter.Eventually.of_forall fun path =>
          initializedAverageCost_hierarchicalPolicy_eq
            (by omega) initial demand path))
    simpa [universalConstant, FD1D.V5.universalConstant] using
      (FD1D.V5.finite_horizon_expected_joinedTrajectoryCost_le_log_succ
        hm hN
        (refreshSupplyOfInventory (FD1D.V5.treeDepth m) initial)
        (fun j => (demand j : ℝ))
        (fun j => (demand j).property))

/--
There is a measurable online policy whose RMS one-period cost from every fixed
initial inventory is eventually at most `C log(m+1)/m`, and whose expected
average cost after scheduled replacement is at most the same bound for every
`N >= 2m^2`.
-/
theorem optimalDynamicMatchingUpperBound :
    OptimalDynamicMatchingUpperBound where
  policy := by
    intro m hm
    exact ⟨hierarchicalPolicy m (by omega), policyGuarantees hm⟩

end

end FD1D.V5.Palomar
