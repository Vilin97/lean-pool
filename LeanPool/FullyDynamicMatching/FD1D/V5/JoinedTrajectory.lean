/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.V5.TrajectoryBounds
public import LeanPool.FullyDynamicMatching.FD1D.Refresh

/-! # Joined Trajectory -/

@[expose] public section

namespace FD1D

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

namespace V5.ContinuousProcess

variable {L m : ℕ}

/-!
# Initialization joined to the continuous trajectory

The time-zero spatial coordinate of `trajectoryLaw` is the iid refreshed
inventory. We use that exact coordinate vector as the replenishment supply
for the first `m` scheduled matches. Thus initialization and the main policy
live on one path space, with a pathwise (not merely count-law) phase boundary.
-/

/-- A continuous coordinate state, viewed as the supply used by
initialization. -/
def coordinateRefreshSupply (L : ℕ) (s : SpatialState m) :
    RefreshSupply L m where
  location j := s j
  leaf := spatialLeaves L s
  location_mem_unit j := (s j).property

@[simp]
theorem coordinateRefreshSupply_location
    (L : ℕ) (s : SpatialState m) (j : Fin m) :
    (coordinateRefreshSupply L s).location j = s j :=
  rfl

@[simp]
theorem coordinateRefreshSupply_leaf
    (L : ℕ) (s : SpatialState m) :
    (coordinateRefreshSupply L s).leaf = spatialLeaves L s :=
  rfl

theorem refresh_coordinateRefreshSupply_location
    (initial : RefreshSupply L m) (s : SpatialState m) (j : Fin m) :
    (initial.refresh (coordinateRefreshSupply L s) m).location j = s j := by
  simp [RefreshSupply.refresh]

theorem refresh_coordinateRefreshSupply_leaf
    (initial : RefreshSupply L m) (s : SpatialState m) :
    (initial.refresh (coordinateRefreshSupply L s) m).leaf =
      spatialLeaves L s := by
  simp [RefreshSupply.refresh]

theorem refresh_coordinateRefreshSupply_countState
    (initial : RefreshSupply L m) (s : SpatialState m) :
    (initial.refresh (coordinateRefreshSupply L s) m).countState =
      spatialCount L s := by
  apply InventoryState.ext
  intro i
  simp [RefreshSupply.countState, spatialCount,
    SupplyConfiguration.countState, SupplyConfiguration.leafCount,
    assignmentState, assignmentCount,
    ]
  rfl

/-- The terminal initialized supply read from the same path used by the main policy. -/
def joinedInitializationTerminal
    (initial : RefreshSupply L m)
    (path : ℕ → ProcessState m) : RefreshSupply L m :=
  initial.refresh (coordinateRefreshSupply L (path 0).1) m

/-- Every terminal initialized coordinate is the corresponding time-zero path coordinate. -/
@[simp]
theorem joinedInitializationTerminal_location
    (initial : RefreshSupply L m)
    (path : ℕ → ProcessState m) (j : Fin m) :
    (joinedInitializationTerminal initial path).location j = (path 0).1 j := by
  exact refresh_coordinateRefreshSupply_location initial (path 0).1 j

/-- The terminal initialized leaf labels are the labels of the time-zero path coordinates. -/
@[simp]
theorem joinedInitializationTerminal_leaf
    (initial : RefreshSupply L m)
    (path : ℕ → ProcessState m) :
    (joinedInitializationTerminal initial path).leaf =
      spatialLeaves L (path 0).1 := by
  exact refresh_coordinateRefreshSupply_leaf initial (path 0).1

/-- The terminal initialized count is the time-zero count of the same path. -/
@[simp]
theorem joinedInitializationTerminal_countState
    (initial : RefreshSupply L m)
    (path : ℕ → ProcessState m) :
    (joinedInitializationTerminal initial path).countState =
      spatialCount L (path 0).1 := by
  exact refresh_coordinateRefreshSupply_countState initial (path 0).1

/-- The time-zero spatial vector on the trajectory has the iid continuous law. -/
theorem map_timeZeroSpatial_trajectoryLaw
    (a : ℝ) (fallback : Fin m) :
    Measure.map
        (fun path : ℕ → ProcessState m => (path 0).1)
        (trajectoryLaw (L := L) a fallback) =
      initialSpatialLaw m := by
  have hrewrite :
      Measure.map
          (fun path : ℕ → ProcessState m => (path 0).1)
          (trajectoryLaw (L := L) a fallback) =
        Measure.map Prod.fst
          (Measure.map (fun path : ℕ → ProcessState m => path 0)
            (trajectoryLaw (L := L) a fallback)) := by
    symm
    rw [Measure.map_map measurable_fst (measurable_pi_apply 0)]
    rfl
  rw [hrewrite, trajectoryLaw_marginal, processLaw_eq_product]
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  rfl

/-- On the joined path law, initialization terminates with the refreshed count law. -/
theorem map_joinedInitializationTerminal_countState
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (initial : RefreshSupply L m) :
    Measure.map
        (fun path : ℕ → ProcessState m =>
          (joinedInitializationTerminal initial path).countState)
        (trajectoryLaw (L := L) a fallback) =
      (refreshedLaw L m).toMeasure := by
  simpa using
    (trajectoryLaw_count_marginal
      (L := L) (m := m) a ha hm fallback 0)

/-- Cost of scheduled initialization match `j` on the joined path. -/
def joinedInitializationStepCost
    (initial : RefreshSupply L m) (demand : Fin m → ℝ)
    (path : ℕ → ProcessState m) (j : Fin m) : ℝ :=
  |demand j -
    (initial.refresh
      (coordinateRefreshSupply L (path 0).1) j.val).location j|

/-- The joined scheduled match removes the still-unrefreshed original label. -/
@[simp]
theorem joinedInitializationStepCost_eq
    (initial : RefreshSupply L m) (demand : Fin m → ℝ)
    (path : ℕ → ProcessState m) (j : Fin m) :
    joinedInitializationStepCost initial demand path j =
      |demand j - initial.location j| := by
  unfold joinedInitializationStepCost
  rw [RefreshSupply.refresh_current_location_is_original
    initial (coordinateRefreshSupply L (path 0).1) j.isLt]

/-- The joined path's initialization costs sum to the explicit initialization cost. -/
theorem sum_joinedInitializationStepCost
    (initial : RefreshSupply L m) (demand : Fin m → ℝ)
    (path : ℕ → ProcessState m) :
    ∑ j, joinedInitializationStepCost initial demand path j =
      initializationMatchingCost initial demand := by
  simp [initializationMatchingCost]

/-- A main-period path cost is integrable on the continuous trajectory law. -/
theorem pathProcessCost_integrable
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    Integrable
      (fun path : ℕ → ProcessState m =>
        processCost L a fallback (path t))
      (trajectoryLaw (L := L) a fallback) := by
  apply Integrable.of_bound
    ((processCost_measurable L a fallback).comp
      (measurable_pi_apply t)).aestronglyMeasurable 1
  filter_upwards with path
  change |processCost L a fallback (path t)| ≤ 1
  rw [abs_of_nonneg
    (processCost_nonneg L a fallback (path t))]
  exact processCost_le_one L a fallback (path t)

/--
The average cost of initialization followed by the main policy, as one random
variable on the single infinite continuous trajectory.
-/
def joinedTrajectoryAverageCost
    (initial : RefreshSupply L m) (demand : Fin m → ℝ)
    (a : ℝ) (hm : 0 < m) (N : ℕ)
    (path : ℕ → ProcessState m) : ℝ :=
  ((∑ j, joinedInitializationStepCost initial demand path j) +
      ∑ t ∈ Finset.range (N - m),
        processCost L a (SupplyConfiguration.canonicalFallback hm) (path t)) /
    (N : ℝ)

/-- The joined full-horizon path cost is integrable. -/
theorem joinedTrajectoryAverageCost_integrable
    (initial : RefreshSupply L m) (demand : Fin m → ℝ)
    (a : ℝ) (hm : 0 < m) (N : ℕ) :
    Integrable
      (joinedTrajectoryAverageCost initial demand a hm N)
      (trajectoryLaw (L := L) a
        (SupplyConfiguration.canonicalFallback hm)) := by
  have hinit :
      Integrable
        (fun _path : ℕ → ProcessState m =>
          initializationMatchingCost initial demand)
        (trajectoryLaw (L := L) a
          (SupplyConfiguration.canonicalFallback hm)) :=
    integrable_const _
  have hsum :
      Integrable
        (fun path : ℕ → ProcessState m =>
          ∑ t ∈ Finset.range (N - m),
            processCost L a (SupplyConfiguration.canonicalFallback hm)
              (path t))
        (trajectoryLaw (L := L) a
          (SupplyConfiguration.canonicalFallback hm)) := by
    apply integrable_finsetSum
    intro t ht
    exact pathProcessCost_integrable a
      (SupplyConfiguration.canonicalFallback hm) t
  refine ((hinit.add hsum).div_const (N : ℝ)).congr ?_
  filter_upwards with path
  change
    (initializationMatchingCost initial demand +
        ∑ t ∈ Finset.range (N - m),
          processCost L a (SupplyConfiguration.canonicalFallback hm)
            (path t)) / (N : ℝ) =
      joinedTrajectoryAverageCost initial demand a hm N path
  rw [joinedTrajectoryAverageCost, sum_joinedInitializationStepCost]

/--
The expectation of the one-path full-horizon cost is exactly initialization
cost plus the sum of the trajectory's one-period expected costs.
-/
theorem integral_joinedTrajectoryAverageCost
    (initial : RefreshSupply L m) (demand : Fin m → ℝ)
    (a : ℝ) (hm : 0 < m) (N : ℕ) :
    (∫ path : ℕ → ProcessState m,
        joinedTrajectoryAverageCost initial demand a hm N path
          ∂trajectoryLaw (L := L) a
            (SupplyConfiguration.canonicalFallback hm)) =
      (initializationMatchingCost initial demand +
          ∑ t ∈ Finset.range (N - m),
            trajectoryExpectedCost
              (L := L) (m := m) a hm
              (SupplyConfiguration.canonicalFallback hm) t) /
        (N : ℝ) := by
  let fallback : Fin m := SupplyConfiguration.canonicalFallback hm
  have hinit :
      Integrable
        (fun _path : ℕ → ProcessState m =>
          initializationMatchingCost initial demand)
        (trajectoryLaw (L := L) a fallback) :=
    integrable_const _
  have hcost (t : ℕ) :
      Integrable
        (fun path : ℕ → ProcessState m =>
          processCost L a fallback (path t))
        (trajectoryLaw (L := L) a fallback) :=
    pathProcessCost_integrable a fallback t
  have hsum :
      Integrable
        (fun path : ℕ → ProcessState m =>
          ∑ t ∈ Finset.range (N - m),
            processCost L a fallback (path t))
        (trajectoryLaw (L := L) a fallback) := by
    exact integrable_finsetSum (Finset.range (N - m))
      (fun t ht => hcost t)
  unfold joinedTrajectoryAverageCost
  simp only [sum_joinedInitializationStepCost]
  change
    (∫ path : ℕ → ProcessState m,
        (initializationMatchingCost initial demand +
            ∑ t ∈ Finset.range (N - m),
              processCost L a fallback (path t)) / (N : ℝ)
          ∂trajectoryLaw (L := L) a fallback) =
      (initializationMatchingCost initial demand +
          ∑ t ∈ Finset.range (N - m),
            trajectoryExpectedCost
              (L := L) (m := m) a hm fallback t) /
        (N : ℝ)
  rw [integral_div]
  rw [integral_add hinit hsum]
  rw [integral_finsetSum (Finset.range (N - m))
    (fun t ht => hcost t)]
  simp only [trajectoryExpectedCost]
  dsimp [fallback]
  simp

/-- Manuscript part (ii): scheduled replacement followed by the v5 policy
has average expected cost at most `9a/m` once `N ≥ 2m²`. -/
theorem finite_horizon_expected_joinedTrajectoryCost_le_nine
    {m N : ℕ} (hm : 1 ≤ m) (hN : 2 * m ^ 2 ≤ N)
    (initial : RefreshSupply (treeDepth m) m)
    (demand : Fin m → ℝ)
    (hdemand : ∀ j, demand j ∈ Set.Icc (0 : ℝ) 1) :
    (∫ path : ℕ → ProcessState m,
        joinedTrajectoryAverageCost initial demand
          (parameterA m : ℝ) (by omega) N path
          ∂trajectoryLaw
            (L := treeDepth m) (m := m)
            (parameterA m : ℝ)
            (SupplyConfiguration.canonicalFallback (by omega))) ≤
      9 * (parameterA m : ℝ) / (m : ℝ) := by
  rw [integral_joinedTrajectoryAverageCost]
  have hmpos : 0 < m := by omega
  have hmN : m ≤ N := by
    have hmm : m ≤ m ^ 2 := by nlinarith
    omega
  have hS : m ^ 2 ≤ N - m := by
    have hmm : m ≤ m ^ 2 := by nlinarith
    omega
  have havg := refreshed_average_expected_cost_le hm hS
  let costSum : ℝ :=
    ∑ t ∈ Finset.range (N - m),
      trajectoryExpectedCost
        (L := treeDepth m) (m := m) (parameterA m : ℝ) hmpos
        (SupplyConfiguration.canonicalFallback hmpos) t
  have hSpos : 0 < N - m := by
    have : 0 < m ^ 2 := pow_pos hmpos 2
    omega
  have hSreal : 0 < ((N - m : ℕ) : ℝ) := by
    exact_mod_cast hSpos
  have hsum :
      costSum ≤ ((N - m : ℕ) : ℝ) *
        ((17 / 2) * (parameterA m : ℝ) / (m : ℝ)) := by
    have h := (div_le_iff₀ hSreal).mp
      (by simpa [costSum] using havg)
    simpa [mul_comm] using h
  have hinit : initializationMatchingCost initial demand ≤ (m : ℝ) :=
    initializationMatchingCost_le_card initial demand hdemand
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le hmpos hmN)
  have hmreal : 0 < (m : ℝ) := by
    exact_mod_cast hmpos
  have haNat : 1 ≤ parameterA m := parameterA_pos hm
  have hareal : 1 ≤ (parameterA m : ℝ) := by
    exact_mod_cast haNat
  have hSleN : ((N - m : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sub_le N m
  have hNquad : 2 * (m : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hAS :
      (parameterA m : ℝ) * ((N - m : ℕ) : ℝ) ≤
        (parameterA m : ℝ) * (N : ℝ) := by
    gcongr
  have hquadA :
      (m : ℝ) ^ 2 ≤
        (1 / 2 : ℝ) * (parameterA m : ℝ) * (N : ℝ) := by
    have hhalf : (m : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * (N : ℝ) := by
      nlinarith
    have hnonneg : 0 ≤ (N : ℝ) := hNreal.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hareal) hnonneg]
  change
    (initializationMatchingCost initial demand + costSum) / (N : ℝ) ≤ _
  apply (div_le_iff₀ hNreal).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hmreal).2
  calc
    (initializationMatchingCost initial demand + costSum) * (m : ℝ) ≤
        ((m : ℝ) + ((N - m : ℕ) : ℝ) *
          ((17 / 2) * (parameterA m : ℝ) / (m : ℝ))) *
            (m : ℝ) := by
      gcongr
    _ ≤ 9 * (parameterA m : ℝ) * (N : ℝ) := by
      field_simp [hmreal.ne']
      nlinarith

end ContinuousProcess

end V5

end

end FD1D
