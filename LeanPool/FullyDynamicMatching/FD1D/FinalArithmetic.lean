/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Bounds
import LeanPool.FullyDynamicMatching.FD1D.Parameters
import LeanPool.FullyDynamicMatching.FD1D.Arithmetic
import LeanPool.FullyDynamicMatching.FD1D.Initialization

/-!
# Final arithmetic for the chosen parameters

This file turns the concrete stationary and finite-time hazard estimates into
the advertised `6a/m` and `7a/m` bounds.  Transport enters only through an
equation-(3) inequality supplied as a hypothesis.
-/

namespace FD1D

noncomputable section

open scoped BigOperators

/-- The concrete hierarchical count kernel with the paper's parameter and
tree depth. -/
def parameterizedKernel (m : ℕ) (hm : 1 ≤ m) :
    FiniteKernel
      (InventoryState (DyadicNode (treeDepth m)) m) :=
  HierarchicalDynamics.kernel
    (L := treeDepth m) (parameterA m : ℝ)
    (parameterA_cast_pos hm) (by omega)

/-- Terminal hazard energy for the paper's parameter and tree depth. -/
def parameterizedHazardEnergy (m : ℕ)
    (x : InventoryState (DyadicNode (treeDepth m)) m) : ℝ :=
  HierarchicalDynamics.stateHazardEnergy
    (parameterA m : ℝ) x (treeDepth m)

/-- The count law at time `t` after iid uniform refreshing. -/
def refreshedIterate (m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    FiniteLaw
      (InventoryState (DyadicNode (treeDepth m)) m) :=
  (parameterizedKernel m hm).iterate t
    (refreshedLaw (treeDepth m) m)

/--
For the chosen parameters, stationary equation (3) implies the advertised
stationary `6a/m` bound.  All hazard and parameter hypotheses are discharged
internally.
-/
theorem stationary_expected_cost_le_six
    {m : ℕ} (hm : 1 ≤ m)
    (μ : FiniteLaw
      (InventoryState (DyadicNode (treeDepth m)) m))
    (cost :
      InventoryState (DyadicNode (treeDepth m)) m → ℝ)
    (hμ : (parameterizedKernel m hm).IsStationary μ)
    (htransport :
      μ.expect cost ≤
        1 / (leafCount m : ℝ) +
          (parameterA m : ℝ) / Real.sqrt 6 *
            Real.sqrt
              (μ.expect (parameterizedHazardEnergy m) -
                1 / (m : ℝ) ^ 2)) :
    μ.expect cost ≤
      6 * (parameterA m : ℝ) / (m : ℝ) := by
  have hmpos : 0 < m := by omega
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have ha : 0 < (parameterA m : ℝ) :=
    parameterA_cast_pos hm
  have hμ' :
      (HierarchicalDynamics.kernel
        (L := treeDepth m) (parameterA m : ℝ)
        ha hmpos).IsStationary μ := by
    simpa [parameterizedKernel] using hμ
  have hHazard :
      μ.expect (parameterizedHazardEnergy m) ≤
        206 / (3 * (m : ℝ) ^ 2) := by
    change
      μ.expect (fun x =>
        HierarchicalDynamics.stateHazardEnergy
          (parameterA m : ℝ) x (treeDepth m)) ≤
        206 / (3 * (m : ℝ) ^ 2)
    exact HierarchicalDynamics.stationary_expected_hazard_bound
      (L := treeDepth m) (m := m)
      (a := (parameterA m : ℝ))
      ha hmpos (parameterA_cast_ge_treeDepth hm) μ hμ'
  have hRootPoint :
      ∀ x : InventoryState (DyadicNode (treeDepth m)) m,
        1 / (m : ℝ) ^ 2 ≤ parameterizedHazardEnergy m x := by
    intro x
    simpa [parameterizedHazardEnergy] using
      (HierarchicalDynamics.stateHazardEnergy_root_le
        (L := treeDepth m) (m := m)
        (a := (parameterA m : ℝ)) ha x)
  have hRoot :
      1 / (m : ℝ) ^ 2 ≤
        μ.expect (parameterizedHazardEnergy m) := by
    calc
      1 / (m : ℝ) ^ 2 =
          μ.expect (fun _ => 1 / (m : ℝ) ^ 2) :=
        (μ.expect_const _).symm
      _ ≤ μ.expect (parameterizedHazardEnergy m) :=
        μ.expect_mono hRootPoint
  exact stationary_cost_le_six
    ha.le hmreal
    (one_div_leafCount_le_two_mul_parameterA_div hm)
    hRoot hHazard htransport

/--
For `T ≥ m²`, an averaged equation-(3)/Jensen estimate along the concrete
iterates from the refreshed law implies average expected cost at most `6a/m`.
-/
theorem finite_average_expected_cost_le_six
    {m T : ℕ} (hm : 1 ≤ m) (hT : m ^ 2 ≤ T)
    (cost : ℕ →
      InventoryState (DyadicNode (treeDepth m)) m → ℝ)
    (htransport :
      (∑ t ∈ Finset.range T,
          (refreshedIterate m hm t).expect (cost t)) / (T : ℝ) ≤
        1 / (leafCount m : ℝ) +
          (parameterA m : ℝ) / Real.sqrt 6 *
            Real.sqrt
              ((∑ t ∈ Finset.range T,
                  (refreshedIterate m hm t).expect
                    (parameterizedHazardEnergy m)) / (T : ℝ) -
                1 / (m : ℝ) ^ 2)) :
    (∑ t ∈ Finset.range T,
        (refreshedIterate m hm t).expect (cost t)) / (T : ℝ) ≤
      6 * (parameterA m : ℝ) / (m : ℝ) := by
  have hmpos : 0 < m := by omega
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hTpos : 0 < T := by
    have : 0 < m ^ 2 := pow_pos hmpos 2
    omega
  have hTreal : (m : ℝ) ^ 2 ≤ (T : ℝ) := by
    exact_mod_cast hT
  have hTrealPos : 0 < (T : ℝ) := by exact_mod_cast hTpos
  have ha : 0 < (parameterA m : ℝ) :=
    parameterA_cast_pos hm
  have hHazard :
      (∑ t ∈ Finset.range T,
          (refreshedIterate m hm t).expect
            (parameterizedHazardEnergy m)) / (T : ℝ) ≤
        206 / (3 * (m : ℝ) ^ 2) + 1 / (T : ℝ) := by
    change
      (∑ t ∈ Finset.range T,
          ((parameterizedKernel m hm).iterate t
            (refreshedLaw (treeDepth m) m)).expect
              (fun x =>
                HierarchicalDynamics.stateHazardEnergy
                  (parameterA m : ℝ) x (treeDepth m))) / (T : ℝ) ≤
        206 / (3 * (m : ℝ) ^ 2) + 1 / (T : ℝ)
    simpa [parameterizedKernel] using
      (HierarchicalDynamics.finite_average_expected_hazard_bound
        (L := treeDepth m) (m := m)
        (a := (parameterA m : ℝ))
        ha hmpos
        (parameterA_cast_ge_treeDepth hm)
        (two_hundred_mul_log_one_add_le_parameterA hm)
        (refreshedLaw (treeDepth m) m) T hTpos)
  have hRootPoint :
      ∀ x : InventoryState (DyadicNode (treeDepth m)) m,
        1 / (m : ℝ) ^ 2 ≤ parameterizedHazardEnergy m x := by
    intro x
    simpa [parameterizedHazardEnergy] using
      (HierarchicalDynamics.stateHazardEnergy_root_le
        (L := treeDepth m) (m := m)
        (a := (parameterA m : ℝ)) ha x)
  have hRootAt (t : ℕ) :
      1 / (m : ℝ) ^ 2 ≤
        (refreshedIterate m hm t).expect
          (parameterizedHazardEnergy m) := by
    calc
      1 / (m : ℝ) ^ 2 =
          (refreshedIterate m hm t).expect
            (fun _ => 1 / (m : ℝ) ^ 2) :=
        ((refreshedIterate m hm t).expect_const _).symm
      _ ≤ (refreshedIterate m hm t).expect
          (parameterizedHazardEnergy m) :=
        (refreshedIterate m hm t).expect_mono hRootPoint
  have hRootSum :
      ∑ t ∈ Finset.range T, (1 / (m : ℝ) ^ 2) ≤
        ∑ t ∈ Finset.range T,
          (refreshedIterate m hm t).expect
            (parameterizedHazardEnergy m) := by
    apply Finset.sum_le_sum
    intro t ht
    exact hRootAt t
  have hRoot :
      1 / (m : ℝ) ^ 2 ≤
        (∑ t ∈ Finset.range T,
            (refreshedIterate m hm t).expect
              (parameterizedHazardEnergy m)) / (T : ℝ) := by
    apply (le_div_iff₀ hTrealPos).2
    simpa [mul_comm] using hRootSum
  exact transient_cost_le_six
    (a := (parameterA m : ℝ))
    (m := (m : ℝ)) (T := (T : ℝ))
    (H :=
      (∑ t ∈ Finset.range T,
          (refreshedIterate m hm t).expect
            (parameterizedHazardEnergy m)) / (T : ℝ))
    (cell := 1 / (leafCount m : ℝ))
    (cost :=
      (∑ t ∈ Finset.range T,
          (refreshedIterate m hm t).expect (cost t)) / (T : ℝ))
    ha.le hmreal hTreal
    (one_div_leafCount_le_two_mul_parameterA_div hm)
    hRoot hHazard htransport

/--
For `N ≥ 2m²`, at most `m` initialization cost followed by the concrete main
policy bound gives total expected average cost at most `7a/m`.
-/
theorem finite_horizon_expected_cost_le_seven
    {m N : ℕ} (hm : 1 ≤ m) (hN : 2 * m ^ 2 ≤ N)
    (initializationCost : ℝ)
    (cost : ℕ →
      InventoryState (DyadicNode (treeDepth m)) m → ℝ)
    (hinitialization : initializationCost ≤ (m : ℝ))
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
    (initializationCost +
        ∑ t ∈ Finset.range (N - m),
          (refreshedIterate m hm t).expect (cost t)) / (N : ℝ) ≤
      7 * (parameterA m : ℝ) / (m : ℝ) := by
  have hmpos : 0 < m := by omega
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hMainHorizon : m ^ 2 ≤ N - m :=
    main_horizon_long_enough hm hN
  have hMainPos : 0 < N - m := by
    have : 0 < m ^ 2 := pow_pos hmpos 2
    omega
  have hMainRealPos : 0 < ((N - m : ℕ) : ℝ) := by
    exact_mod_cast hMainPos
  have hNpos : 0 < N := by omega
  have hNrealPos : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hmain :=
    finite_average_expected_cost_le_six
      hm hMainHorizon cost htransport
  let mainSum : ℝ :=
    ∑ t ∈ Finset.range (N - m),
      (refreshedIterate m hm t).expect (cost t)
  let rate : ℝ :=
    6 * (parameterA m : ℝ) / (m : ℝ)
  have hmainSum :
      mainSum ≤ rate * ((N - m : ℕ) : ℝ) := by
    exact (div_le_iff₀ hMainRealPos).mp hmain
  have hMainLeN : ((N - m : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sub_le N m
  have hrate : 0 ≤ rate := by
    dsimp [rate]
    positivity
  have hmainScaled : mainSum / (N : ℝ) ≤ rate := by
    apply (div_le_iff₀ hNrealPos).2
    calc
      mainSum ≤ rate * ((N - m : ℕ) : ℝ) := hmainSum
      _ ≤ rate * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hMainLeN hrate
  have hinitScaled :
      initializationCost / (N : ℝ) ≤
        (m : ℝ) / (N : ℝ) :=
    div_le_div_of_nonneg_right hinitialization hNrealPos.le
  have haOne : (1 : ℝ) ≤ (parameterA m : ℝ) := by
    exact_mod_cast parameterA_pos hm
  have hNsqNat : m ^ 2 ≤ N := by omega
  have hNsqReal : (m : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast hNsqNat
  have hfinal :
      (m : ℝ) / (N : ℝ) + rate ≤
        7 * (parameterA m : ℝ) / (m : ℝ) := by
    exact initialization_average_bound
      haOne hmreal hNsqReal (le_refl rate)
  change (initializationCost + mainSum) / (N : ℝ) ≤
    7 * (parameterA m : ℝ) / (m : ℝ)
  calc
    (initializationCost + mainSum) / (N : ℝ) =
        initializationCost / (N : ℝ) +
          mainSum / (N : ℝ) := by ring
    _ ≤ (m : ℝ) / (N : ℝ) + rate :=
      add_le_add hinitScaled hmainScaled
    _ ≤ 7 * (parameterA m : ℝ) / (m : ℝ) := hfinal

end

end FD1D
