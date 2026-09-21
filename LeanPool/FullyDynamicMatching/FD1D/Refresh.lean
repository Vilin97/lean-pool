/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.FinalArithmetic

/-! # Refresh -/

namespace FD1D

noncomputable section

open scoped BigOperators

/-!
# Explicit initialization by labeled refresh

During the first `m` requests, label `k` is matched and replaced at step
`k < m`.  Labels below `k` have already been refreshed, while labels at or
above `k` still denote the original supply.  This makes it impossible for
the initialization schedule to delete a previously refreshed label.

`Spatial.lean` is deliberately not imported here: its current dependency on
the transport development is transient.  Exact coordinates are instead
parameterized by a unit-interval location rule.  The count projection and
its law are independent of that rule.
-/

/-- Replace exactly the labels whose indices are strictly below `k`. -/
def refreshAssignment {ι : Type*} {m : ℕ}
    (initial replenishment : Assignment ι m) (k : ℕ) :
    Assignment ι m :=
  fun j => if j.val < k then replenishment j else initial j

@[simp]
theorem refreshAssignment_zero {ι : Type*} {m : ℕ}
    (initial replenishment : Assignment ι m) :
    refreshAssignment initial replenishment 0 = initial := by
  funext j
  simp [refreshAssignment]

@[simp]
theorem refreshAssignment_at_card {ι : Type*} {m : ℕ}
    (initial replenishment : Assignment ι m) :
    refreshAssignment initial replenishment m = replenishment := by
  funext j
  simp [refreshAssignment, j.isLt]

theorem refreshAssignment_apply_of_lt {ι : Type*} {m k : ℕ}
    (initial replenishment : Assignment ι m) (j : Fin m)
    (hj : j.val < k) :
    refreshAssignment initial replenishment k j = replenishment j := by
  simp [refreshAssignment, hj]

theorem refreshAssignment_apply_of_le {ι : Type*} {m k : ℕ}
    (initial replenishment : Assignment ι m) (j : Fin m)
    (hj : k ≤ j.val) :
    refreshAssignment initial replenishment k j = initial j := by
  simp [refreshAssignment, Nat.not_lt.mpr hj]

/-- Immediately before step `k`, label `k` still denotes original supply. -/
theorem refreshAssignment_current_is_original {ι : Type*} {m k : ℕ}
    (initial replenishment : Assignment ι m) (hk : k < m) :
    refreshAssignment initial replenishment k ⟨k, hk⟩ =
      initial ⟨k, hk⟩ := by
  simp [refreshAssignment]

/-- Immediately after step `k`, label `k` denotes its replenishment. -/
theorem refreshAssignment_current_is_replenished {ι : Type*} {m k : ℕ}
    (initial replenishment : Assignment ι m) (hk : k < m) :
    refreshAssignment initial replenishment (k + 1) ⟨k, hk⟩ =
      replenishment ⟨k, hk⟩ := by
  simp [refreshAssignment]

/--
Advancing the schedule cannot alter a previously refreshed label.  Both
sides equal that label's prescribed replenishment.
-/
theorem refreshAssignment_preserves_refreshed {ι : Type*} {m k : ℕ}
    (initial replenishment : Assignment ι m) (j : Fin m)
    (hj : j.val < k) :
    refreshAssignment initial replenishment (k + 1) j =
      refreshAssignment initial replenishment k j := by
  rw [refreshAssignment_apply_of_lt initial replenishment j hj]
  exact refreshAssignment_apply_of_lt initial replenishment j (by omega)

/-- Advancing step `k` also leaves every label strictly above `k` alone. -/
theorem refreshAssignment_preserves_later {ι : Type*} {m k : ℕ}
    (initial replenishment : Assignment ι m) (j : Fin m)
    (hj : k < j.val) :
    refreshAssignment initial replenishment (k + 1) j =
      refreshAssignment initial replenishment k j := by
  rw [refreshAssignment_apply_of_le initial replenishment j (by omega)]
  exact (refreshAssignment_apply_of_le initial replenishment j hj.le).symm

/-- The leaf-count state after the first `k` labeled replacements. -/
def refreshState {L m : ℕ}
    (initial replenishment : DyadicAssignment L m) (k : ℕ) :
    InventoryState (DyadicNode L) m :=
  assignmentState (refreshAssignment initial replenishment k)

@[simp]
theorem refreshState_zero {L m : ℕ}
    (initial replenishment : DyadicAssignment L m) :
    refreshState initial replenishment 0 = assignmentState initial := by
  simp [refreshState]

/-- After all `m` replacements, the count state forgets the initial supply. -/
@[simp]
theorem refreshState_at_card {L m : ℕ}
    (initial replenishment : DyadicAssignment L m) :
    refreshState initial replenishment m =
      assignmentState replenishment := by
  simp [refreshState]

/--
An arbitrary labeled supply configuration at the resolution used by the
count chain.  No distributional assumption is imposed on the initial supply.
-/
structure RefreshSupply (L m : ℕ) where
  /-- Spatial coordinate of each labeled supply item. -/
  location : Fin m → ℝ
  /-- Dyadic leaf assigned to each labeled supply item. -/
  leaf : DyadicAssignment L m
  location_mem_unit :
    ∀ j, location j ∈ Set.Icc (0 : ℝ) 1

/--
Coordinates for every possible replenishment-leaf assignment.  This is the
coordinate-level parameter used while `Spatial.lean` is unavailable.
-/
structure ReplenishmentCoordinates (L m : ℕ) where
  /-- Replenishment coordinates associated with each dyadic assignment. -/
  location : DyadicAssignment L m → Fin m → ℝ
  location_mem_unit :
    ∀ ω j, location ω j ∈ Set.Icc (0 : ℝ) 1

namespace ReplenishmentCoordinates

/-- The realized labeled replenishment configuration for outcome `ω`. -/
def supply {L m : ℕ} (R : ReplenishmentCoordinates L m)
    (ω : DyadicAssignment L m) : RefreshSupply L m where
  location := R.location ω
  leaf := ω
  location_mem_unit := R.location_mem_unit ω

@[simp]
theorem supply_location {L m : ℕ} (R : ReplenishmentCoordinates L m)
    (ω : DyadicAssignment L m) (j : Fin m) :
    (R.supply ω).location j = R.location ω j :=
  rfl

@[simp]
theorem supply_leaf {L m : ℕ} (R : ReplenishmentCoordinates L m)
    (ω : DyadicAssignment L m) :
    (R.supply ω).leaf = ω :=
  rfl

end ReplenishmentCoordinates

namespace RefreshSupply

/-- Count projection of a labeled supply configuration. -/
def countState {L m : ℕ} (C : RefreshSupply L m) :
    InventoryState (DyadicNode L) m :=
  assignmentState C.leaf

/-- The labeled configuration after the first `k` replacements. -/
def refresh {L m : ℕ} (initial replenishment : RefreshSupply L m)
    (k : ℕ) : RefreshSupply L m where
  location :=
    refreshAssignment initial.location replenishment.location k
  leaf :=
    refreshAssignment initial.leaf replenishment.leaf k
  location_mem_unit := by
    intro j
    by_cases hj : j.val < k
    · simpa [refreshAssignment, hj] using
        replenishment.location_mem_unit j
    · simpa [refreshAssignment, hj] using
        initial.location_mem_unit j

@[simp]
theorem refresh_location {L m : ℕ}
    (initial replenishment : RefreshSupply L m) (k : ℕ) (j : Fin m) :
    (initial.refresh replenishment k).location j =
      refreshAssignment initial.location replenishment.location k j :=
  rfl

@[simp]
theorem refresh_leaf {L m : ℕ}
    (initial replenishment : RefreshSupply L m) (k : ℕ) :
    (initial.refresh replenishment k).leaf =
      refreshAssignment initial.leaf replenishment.leaf k :=
  rfl

@[simp]
theorem refresh_countState {L m : ℕ}
    (initial replenishment : RefreshSupply L m) (k : ℕ) :
    (initial.refresh replenishment k).countState =
      refreshState initial.leaf replenishment.leaf k :=
  rfl

/--
For every replenishment outcome, the terminal count state is exactly the
fiber-count state of that outcome.
-/
theorem refresh_countState_at_card {L m : ℕ}
    (initial : RefreshSupply L m) (R : ReplenishmentCoordinates L m)
    (ω : DyadicAssignment L m) :
    (initial.refresh (R.supply ω) m).countState =
      assignmentState ω := by
  simp

/--
At step `k`, the scheduled match removes original label `k`, not any label
that was replenished at an earlier step.
-/
theorem refresh_current_location_is_original {L m k : ℕ}
    (initial replenishment : RefreshSupply L m) (hk : k < m) :
    (initial.refresh replenishment k).location ⟨k, hk⟩ =
      initial.location ⟨k, hk⟩ := by
  exact refreshAssignment_current_is_original
    initial.location replenishment.location hk

end RefreshSupply

/--
The count-state law after `k` scheduled replacements, with all replenishment
leaf labels sampled jointly from the uniform law on assignments.
-/
def refreshCountLaw {L m : ℕ} (initial : RefreshSupply L m)
    (R : ReplenishmentCoordinates L m) (k : ℕ) :
    FiniteLaw (InventoryState (DyadicNode L) m) :=
  (FiniteLaw.uniform : FiniteLaw (DyadicAssignment L m)).map
    (fun ω => (initial.refresh (R.supply ω) k).countState)

/--
The explicit `m`-step schedule has exactly the iid refreshed count law,
independently of the arbitrary initial supply and coordinate rule.
-/
@[simp]
theorem refreshCountLaw_at_card {L m : ℕ}
    (initial : RefreshSupply L m)
    (R : ReplenishmentCoordinates L m) :
    refreshCountLaw initial R m = refreshedLaw L m := by
  simp [refreshCountLaw, refreshedLaw]

/-- Unit-interval points are at distance at most one. -/
theorem abs_sub_le_one_of_mem_unit {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |x - y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/--
Cost at initialization step `j`: match the request to label `j` in the
configuration just before that label is refreshed.
-/
def scheduledInitializationStepCost {L m : ℕ}
    (initial : RefreshSupply L m)
    (R : ReplenishmentCoordinates L m)
    (ω : DyadicAssignment L m)
    (demand : Fin m → ℝ) (j : Fin m) : ℝ :=
  |demand j -
    (initial.refresh (R.supply ω) j.val).location j|

/-- The scheduled step always matches the still-unrefreshed original label. -/
@[simp]
theorem scheduledInitializationStepCost_eq {L m : ℕ}
    (initial : RefreshSupply L m)
    (R : ReplenishmentCoordinates L m)
    (ω : DyadicAssignment L m)
    (demand : Fin m → ℝ) (j : Fin m) :
    scheduledInitializationStepCost initial R ω demand j =
      |demand j - initial.location j| := by
  simp [scheduledInitializationStepCost, RefreshSupply.refresh,
    refreshAssignment]

/-- The total cost of matching each initialization request to its old label. -/
def initializationMatchingCost {L m : ℕ}
    (initial : RefreshSupply L m) (demand : Fin m → ℝ) : ℝ :=
  ∑ j, |demand j - initial.location j|

/-- The pathwise schedule cost is independent of replenishment outcomes. -/
theorem sum_scheduledInitializationStepCost_eq {L m : ℕ}
    (initial : RefreshSupply L m)
    (R : ReplenishmentCoordinates L m)
    (ω : DyadicAssignment L m)
    (demand : Fin m → ℝ) :
    ∑ j, scheduledInitializationStepCost initial R ω demand j =
      initializationMatchingCost initial demand := by
  simp [initializationMatchingCost]

/-- Every initialization match has cost at most one. -/
theorem scheduledInitializationStepCost_le_one {L m : ℕ}
    (initial : RefreshSupply L m)
    (R : ReplenishmentCoordinates L m)
    (ω : DyadicAssignment L m)
    (demand : Fin m → ℝ)
    (hdemand : ∀ j, demand j ∈ Set.Icc (0 : ℝ) 1)
    (j : Fin m) :
    scheduledInitializationStepCost initial R ω demand j ≤ 1 := by
  rw [scheduledInitializationStepCost_eq]
  exact abs_sub_le_one_of_mem_unit
    (hdemand j) (initial.location_mem_unit j)

/-- The complete `m`-step initialization period costs at most `m`. -/
theorem initializationMatchingCost_le_card {L m : ℕ}
    (initial : RefreshSupply L m)
    (demand : Fin m → ℝ)
    (hdemand : ∀ j, demand j ∈ Set.Icc (0 : ℝ) 1) :
    initializationMatchingCost initial demand ≤ (m : ℝ) := by
  unfold initializationMatchingCost
  calc
    ∑ j, |demand j - initial.location j| ≤
        ∑ _j : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact abs_sub_le_one_of_mem_unit
        (hdemand j) (initial.location_mem_unit j)
    _ = (m : ℝ) := by simp

/--
The final finite-horizon wrapper.  Its first conclusion identifies the
explicit schedule's terminal count law with `refreshedLaw`; its second
conclusion invokes the main arithmetic theorem with the initialization bound
proved above, so neither fact remains a hypothesis.
-/
theorem finite_horizon_expected_cost_le_seven_after_refresh
    {m N : ℕ} (hm : 1 ≤ m) (hN : 2 * m ^ 2 ≤ N)
    (initial : RefreshSupply (treeDepth m) m)
    (R : ReplenishmentCoordinates (treeDepth m) m)
    (demand : Fin m → ℝ)
    (hdemand : ∀ j, demand j ∈ Set.Icc (0 : ℝ) 1)
    (cost : ℕ →
      InventoryState (DyadicNode (treeDepth m)) m → ℝ)
    (htransport :
      (∑ t ∈ Finset.range (N - m),
          (refreshedIterate m hm t).expect (cost t)) /
            ((N - m : ℕ) : ℝ) ≤
        1 / (leafCount m : ℝ) +
          (parameterA m : ℝ) / Real.sqrt 6 *
            Real.sqrt
              ((∑ t ∈ Finset.range (N - m),
                  (refreshedIterate m hm t).expect
                    (parameterizedHazardEnergy m)) /
                    ((N - m : ℕ) : ℝ) -
                1 / (m : ℝ) ^ 2)) :
    refreshCountLaw initial R m =
        refreshedLaw (treeDepth m) m ∧
      (initializationMatchingCost initial demand +
          ∑ t ∈ Finset.range (N - m),
            (refreshedIterate m hm t).expect (cost t)) / (N : ℝ) ≤
        7 * (parameterA m : ℝ) / (m : ℝ) := by
  constructor
  · exact refreshCountLaw_at_card initial R
  · exact finite_horizon_expected_cost_le_seven
      hm hN (initializationMatchingCost initial demand) cost
      (initializationMatchingCost_le_card initial demand hdemand)
      htransport

end

end FD1D
