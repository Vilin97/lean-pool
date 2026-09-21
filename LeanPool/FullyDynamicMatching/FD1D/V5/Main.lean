/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.JoinedTrajectory
import LeanPool.FullyDynamicMatching.FD1D.V5.Balanced
import LeanPool.FullyDynamicMatching.FD1D.V5.Complexity

/-!
# Manuscript-facing theorem for bundle v5

This module packages the explicit continuous-coordinate online process, its
exact finite count marginals, the two natural-log cost bounds in the main
theorem, the balanced-initial-law corollary, and the abstract resource
guarantees.
-/

namespace FD1D.V5

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-- One universal constant sufficient for both parts of the main theorem. -/
def universalConstant : ℝ :=
  72000 / Real.log 2

theorem universalConstant_pos :
    0 < universalConstant := by
  unfold universalConstant
  exact div_pos (by norm_num) (Real.log_pos (by norm_num))

/-- Natural-log form of manuscript part (i), from any fixed initial inventory. -/
theorem limsup_trajectoryRMSCostFromState_le_log_succ
    {m : ℕ} (hm : 2 ≤ m) (s0 : SpatialState m) :
    Filter.limsup
        (ContinuousProcess.trajectoryRMSCostFromState m (by omega) s0)
        atTop ≤
      universalConstant * Real.log ((m + 1 : ℕ) : ℝ) / (m : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog :
      0 ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 1 by omega))
  have ha := parameterA_cast_le_log_succ hm
  have hscaled :
      (17 / 2 : ℝ) * (parameterA m : ℝ) ≤
        universalConstant * Real.log ((m + 1 : ℕ) : ℝ) := by
    calc
      (17 / 2 : ℝ) * (parameterA m : ℝ) ≤
          (17 / 2 : ℝ) *
            ((8000 / Real.log 2) *
              Real.log ((m + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left ha (by norm_num)
      _ = (68000 / Real.log 2) *
          Real.log ((m + 1 : ℕ) : ℝ) := by ring
      _ ≤ (72000 / Real.log 2) *
          Real.log ((m + 1 : ℕ) : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by norm_num) hlogTwo.le) hlog
      _ = universalConstant *
          Real.log ((m + 1 : ℕ) : ℝ) := rfl
  calc
    Filter.limsup
        (ContinuousProcess.trajectoryRMSCostFromState m (by omega) s0)
        atTop ≤
      (17 / 2) * (parameterA m : ℝ) / (m : ℝ) :=
      ContinuousProcess.limsup_trajectoryRMSCostFromState_le
        (by omega) s0
    _ ≤ universalConstant * Real.log ((m + 1 : ℕ) : ℝ) / (m : ℝ) :=
      div_le_div_of_nonneg_right hscaled hmpos.le

/--
Natural-log form of manuscript part (ii).  The scheduled replacement phase
is joined pathwise to the same post-refresh trajectory.
-/
theorem finite_horizon_expected_joinedTrajectoryCost_le_log_succ
    {m N : ℕ} (hm : 2 ≤ m) (hN : 2 * m ^ 2 ≤ N)
    (initial : RefreshSupply (treeDepth m) m)
    (demand : Fin m → ℝ)
    (hdemand : ∀ j, demand j ∈ Set.Icc (0 : ℝ) 1) :
    (∫ path : ℕ → ContinuousProcess.ProcessState m,
        ContinuousProcess.joinedTrajectoryAverageCost initial demand
          (parameterA m : ℝ) (by omega) N path
          ∂ContinuousProcess.trajectoryLaw
            (L := treeDepth m) (m := m)
            (parameterA m : ℝ)
            (SupplyConfiguration.canonicalFallback (by omega))) ≤
      universalConstant * Real.log ((m + 1 : ℕ) : ℝ) / (m : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have ha := parameterA_cast_le_log_succ hm
  have hscaled :
      9 * (parameterA m : ℝ) ≤
        universalConstant * Real.log ((m + 1 : ℕ) : ℝ) := by
    calc
      9 * (parameterA m : ℝ) ≤
          9 * ((8000 / Real.log 2) *
            Real.log ((m + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left ha (by norm_num)
      _ = universalConstant *
          Real.log ((m + 1 : ℕ) : ℝ) := by
        unfold universalConstant
        ring
  exact
    (ContinuousProcess.finite_horizon_expected_joinedTrajectoryCost_le_nine
      (by omega) hN initial demand hdemand).trans
      (div_le_div_of_nonneg_right hscaled hmpos.le)

/--
All formal conclusions used by the v5 main theorem and balanced corollary.
The `countMarginal` field identifies the explicit continuous process with
the finite V5 count kernel at every time.
-/
structure FullFormalization (m : ℕ) (hm : 2 ≤ m) : Prop where
  countMarginal :
    ∀ (s0 : SpatialState m) (t : ℕ),
      Measure.map
          (fun path : ℕ → ContinuousProcess.ProcessState m =>
            spatialCount (treeDepth m) (path t).1)
          (ContinuousProcess.trajectoryLawFromState
            (L := treeDepth m) s0 (parameterA m : ℝ)
              (SupplyConfiguration.canonicalFallback (by omega))) =
        ((parameterizedKernel m (by omega)).iterate t
          (FiniteLaw.dirac
            (spatialCount (treeDepth m) s0))).toMeasure
  arbitraryInitialRMS :
    ∀ s0 : SpatialState m,
      Filter.limsup
          (ContinuousProcess.trajectoryRMSCostFromState m (by omega) s0)
          atTop ≤
        universalConstant * Real.log ((m + 1 : ℕ) : ℝ) / (m : ℝ)
  initializedFiniteHorizon :
    ∀ (N : ℕ), 2 * m ^ 2 ≤ N →
      ∀ (initial : RefreshSupply (treeDepth m) m)
        (demand : Fin m → ℝ),
        (∀ j, demand j ∈ Set.Icc (0 : ℝ) 1) →
          (∫ path : ℕ → ContinuousProcess.ProcessState m,
              ContinuousProcess.joinedTrajectoryAverageCost
                initial demand (parameterA m : ℝ) (by omega) N path
              ∂ContinuousProcess.trajectoryLaw
                (L := treeDepth m) (m := m)
                (parameterA m : ℝ)
                (SupplyConfiguration.canonicalFallback (by omega))) ≤
            universalConstant * Real.log ((m + 1 : ℕ) : ℝ) / (m : ℝ)
  balancedEveryHorizon :
    ∀ T : ℕ, 0 < T →
      Real.sqrt
          ((∑ t ∈ Finset.range T,
            ((parameterizedKernel m (by omega)).iterate t
              (Balanced.parameterizedLaw m)).expect
                (parameterizedSquaredCostEnvelope m)) / (T : ℝ)) ≤
        (2 + Real.sqrt (501 / 12)) *
          (parameterA m : ℝ) / (m : ℝ)
  resources : HierarchicalResourceGuarantees

/-- The explicit V5 online policy satisfies the complete packaged theorem. -/
theorem full_formalization
    {m : ℕ} (hm : 2 ≤ m) :
    FullFormalization m hm where
  countMarginal := by
    intro s0 t
    simpa [parameterizedKernel] using
      (ContinuousProcess.trajectoryLawFromState_count_marginal
        (L := treeDepth m) s0
        (parameterA m : ℝ) (parameterA_cast_pos (by omega))
        (by omega)
        (SupplyConfiguration.canonicalFallback (by omega)) t)
  arbitraryInitialRMS :=
    limsup_trajectoryRMSCostFromState_le_log_succ hm
  initializedFiniteHorizon := by
    intro N hN initial demand hdemand
    exact finite_horizon_expected_joinedTrajectoryCost_le_log_succ
      hm hN initial demand hdemand
  balancedEveryHorizon := by
    intro T hT
    exact Balanced.parameterizedLaw_average_rms_squaredCostEnvelope_le
      (by omega) hT
  resources := hierarchicalPolicy_resourceGuarantees

end

end FD1D.V5
