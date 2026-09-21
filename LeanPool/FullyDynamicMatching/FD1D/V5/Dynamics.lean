/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Dynamics
import LeanPool.FullyDynamicMatching.FD1D.V5.TreePolicy

/-!
# Count dynamics for the v5 policy

This module instantiates the generic delete-then-arrive inventory kernel with
the v5 deletion masses and connects it to the harmonic potential with
regularizer `a / 2`.
-/

namespace FD1D.V5.Dynamics

noncomputable section

open scoped BigOperators

variable {L m : ℕ}

/-- Regard a fixed-total leaf-count vector as a coherent tree inventory. -/
abbrev aggregatedInventory
    (x : InventoryState (DyadicNode L) m) : AggregatedInventory L m :=
  FD1D.HierarchicalDynamics.aggregatedInventory x

theorem aggregatedInventory_leaf_count
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (aggregatedInventory x).count L w = x.1 w :=
  FD1D.HierarchicalDynamics.aggregatedInventory_leaf_count x w

theorem aggregatedInventory_count
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    (aggregatedInventory x).count d v =
      ∑ w ∈ leafBlock hdL v, x.1 w :=
  FD1D.HierarchicalDynamics.aggregatedInventory_count x hdL v

/-- The v5 leaf deletion probabilities. -/
def deletionRule (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    DeletionRule (DyadicNode L) m where
  prob x w :=
    TreePolicy.deletionMass (aggregatedInventory x) a L w
  nonneg x w :=
    TreePolicy.deletionMass_nonneg
      (aggregatedInventory x) ha hm le_rfl w
  empty x w hw :=
    TreePolicy.leaf_deletionMass_eq_zero_of_count_eq_zero
      (aggregatedInventory x) a w (by simpa using hw)
  occupied_pos x w hw :=
    TreePolicy.leaf_deletionMass_pos_of_count_pos
      (aggregatedInventory x) ha hm w (by simpa using hw)
  sum_prob x :=
    TreePolicy.sum_deletionMass
      (aggregatedInventory x) hm le_rfl

@[simp] theorem deletionRule_prob
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (deletionRule a ha hm).prob x w =
      TreePolicy.deletionMass (aggregatedInventory x) a L w :=
  rfl

/-- Delete according to the v5 rule and add an independent uniform leaf. -/
def kernel (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    FiniteKernel (InventoryState (DyadicNode L) m) :=
  (deletionRule a ha hm).kernel

@[simp] theorem kernel_apply
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x y : InventoryState (DyadicNode L) m) :
    kernel a ha hm x y =
      ∑ deleted, ∑ arrived,
        if InventoryState.move x deleted arrived = y then
          TreePolicy.deletionMass
              (aggregatedInventory x) a L deleted *
            (1 / Fintype.card (DyadicNode L) : ℝ)
        else 0 :=
  rfl

theorem kernel_move_pos
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {deleted arrived : DyadicNode L} (hdeleted : 0 < x.1 deleted) :
    0 < kernel a ha hm x
      (InventoryState.move x deleted arrived) :=
  (deletionRule a ha hm).kernel_move_pos x hdeleted

theorem kernel_irreducible
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (kernel (L := L) a ha hm).Irreducible :=
  FD1D.HierarchicalDynamics.deletionRule_kernel_irreducible
    (deletionRule a ha hm)

theorem kernel_hasPositiveLoops
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (kernel (L := L) a ha hm).HasPositiveLoops :=
  (deletionRule a ha hm).kernel_hasPositiveLoops

/-! ## Node marginals and count updates -/

/-- Probability that the deleted leaf lies below a given node. -/
def deletionMarginal
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) : ℝ :=
  ∑ w ∈ leafBlock hdL v, (deletionRule a ha hm).prob x w

theorem deletionMarginal_eq
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    deletionMarginal a ha hm x hdL v =
      TreePolicy.deletionMass (aggregatedInventory x) a d v := by
  let q : CoherentTreeLabel L ℝ :=
    { value := TreePolicy.deletionMass (aggregatedInventory x) a
      children := TreePolicy.deletionMass_children
        (aggregatedInventory x) a }
  simpa [deletionMarginal, deletionRule, q] using
    (FD1D.HierarchicalDynamics.coherent_eq_sum_leafBlock q hdL v).symm

theorem aggregatedInventory_move_count
    (x : InventoryState (DyadicNode L) m)
    {deleted arrived : DyadicNode L} (hdeleted : 0 < x.1 deleted)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    (aggregatedInventory
        (InventoryState.move x deleted arrived)).count d v =
      updateCount ((aggregatedInventory x).count d v)
        (FD1D.HierarchicalDynamics.inBlock
          (leafBlock hdL v) deleted)
        (FD1D.HierarchicalDynamics.inBlock
          (leafBlock hdL v) arrived) :=
  FD1D.HierarchicalDynamics.aggregatedInventory_move_count
    x hdeleted hdL v

theorem kernel_expectation_eq_delete_arrive
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    (f : InventoryState (DyadicNode L) m → ℝ) :
    ∑ y, kernel a ha hm x y * f y =
      ∑ deleted, ∑ arrived,
        (deletionRule a ha hm).prob x deleted *
          (1 / Fintype.card (DyadicNode L) : ℝ) *
            f (InventoryState.move x deleted arrived) := by
  rw [kernel]
  simp only [DeletionRule.kernel_apply]
  calc
    ∑ y, (∑ deleted, ∑ arrived,
          if InventoryState.move x deleted arrived = y then
            (deletionRule a ha hm).prob x deleted *
              (1 / Fintype.card (DyadicNode L) : ℝ)
          else 0) * f y =
        ∑ deleted, ∑ arrived, ∑ y,
          (if InventoryState.move x deleted arrived = y then
            (deletionRule a ha hm).prob x deleted *
              (1 / Fintype.card (DyadicNode L) : ℝ)
          else 0) * f y := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro deleted _
            rw [Finset.sum_comm]
    _ = ∑ deleted, ∑ arrived,
          (deletionRule a ha hm).prob x deleted *
            (1 / Fintype.card (DyadicNode L) : ℝ) *
              f (InventoryState.move x deleted arrived) := by
            apply Finset.sum_congr rfl
            intro deleted _
            apply Finset.sum_congr rfl
            intro arrived _
            simp

theorem kernel_expected_nodePotentialChange
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    ∑ y, kernel a ha hm x y *
        (harmonicPotential (a / 2)
            ((aggregatedInventory y).count d v) -
          harmonicPotential (a / 2)
            ((aggregatedInventory x).count d v)) =
      expectedNodePotentialChange (a / 2)
        ((aggregatedInventory x).count d v)
        (nodeMass d v)
        (TreePolicy.deletionMass
          (aggregatedInventory x) a d v) := by
  let S := leafBlock hdL v
  let deleteWeight : DyadicNode L → ℝ :=
    fun w => (deletionRule a ha hm).prob x w
  let arrivalWeight : DyadicNode L → ℝ :=
    fun _ => (1 / Fintype.card (DyadicNode L) : ℝ)
  let N := (aggregatedInventory x).count d v
  let q := TreePolicy.deletionMass (aggregatedInventory x) a d v
  let p := nodeMass d v
  let change : Bool → Bool → ℝ := fun deleted arrived =>
    harmonicPotential (a / 2) (updateCount N deleted arrived) -
      harmonicPotential (a / 2) N
  rw [kernel_expectation_eq_delete_arrive]
  have hrewrite (deleted arrived : DyadicNode L) :
      deleteWeight deleted * arrivalWeight arrived *
          (harmonicPotential (a / 2)
              ((aggregatedInventory
                (InventoryState.move x deleted arrived)).count d v) -
            harmonicPotential (a / 2) N) =
        deleteWeight deleted * arrivalWeight arrived *
          change
            (FD1D.HierarchicalDynamics.inBlock S deleted)
            (FD1D.HierarchicalDynamics.inBlock S arrived) := by
    by_cases hdeleted : 0 < x.1 deleted
    · rw [aggregatedInventory_move_count x hdeleted hdL v]
    · have hempty : x.1 deleted = 0 := by omega
      have hweight : deleteWeight deleted = 0 :=
        (deletionRule a ha hm).empty x deleted hempty
      simp [hweight]
  change
    (∑ deleted, ∑ arrived,
      deleteWeight deleted * arrivalWeight arrived *
        (harmonicPotential (a / 2)
            ((aggregatedInventory
              (InventoryState.move x deleted arrived)).count d v) -
          harmonicPotential (a / 2) N)) =
      expectedNodePotentialChange (a / 2) N p q
  simp_rw [hrewrite]
  apply Eq.trans
    (FD1D.HierarchicalDynamics.double_inBlock_partition
      deleteWeight arrivalWeight S S q p
      ((deletionRule a ha hm).sum_prob x)
      (by
        dsimp only [arrivalWeight]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard :
            (Fintype.card (DyadicNode L) : ℝ) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        field_simp)
      (by
        simpa [deleteWeight, S, q, deletionMarginal] using
          deletionMarginal_eq a ha hm x hdL v)
      (by
        simpa [arrivalWeight, S, p,
          FD1D.HierarchicalDynamics.arrivalMarginal] using
          FD1D.HierarchicalDynamics.arrivalMarginal_eq_nodeMass hdL v)
      change)
  rfl

/-! ## State observables and exact harmonic drift -/

/-- Aggregated inventory counts viewed as labels on every dyadic level. -/
def countLabel (x : InventoryState (DyadicNode L) m) :
    ∀ d, DyadicNode d → ℕ :=
  (aggregatedInventory x).count

/-- Deletion mass at every node of the aggregated inventory tree. -/
def deletionLabel (a : ℝ) (x : InventoryState (DyadicNode L) m) :
    ∀ d, DyadicNode d → ℝ :=
  TreePolicy.deletionMass (aggregatedInventory x) a

/-- Deletion rate at every node of the aggregated inventory tree. -/
def rateLabel (a : ℝ) (x : InventoryState (DyadicNode L) m) :
    ∀ d, DyadicNode d → ℝ :=
  TreePolicy.rate (aggregatedInventory x) a

/-- The manuscript potential `Φ`, whose harmonic shift is `a/2`. -/
def statePotential (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  globalHarmonicPotential L (a / 2) (countLabel x)

/-- The principal restoring term `D`. -/
def stateDrift (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  potentialDrift L (a / 2) (countLabel x) (deletionLabel a x)

/-- The exact curvature remainder `R`. -/
def stateRemainder (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  potentialRemainder L (a / 2) (countLabel x) (deletionLabel a x)

/-- Hazard energy of the state rate labels at the selected dyadic level. -/
def stateRateEnergy (a : ℝ)
    (x : InventoryState (DyadicNode L) m) (d : ℕ) : ℝ :=
  hazardEnergy (rateLabel a x) d

/-- Transport energy of the aggregated inventory state. -/
def stateTransportEnergy (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  TreePolicy.transportEnergy (aggregatedInventory x) a

theorem kernel_expected_globalPotentialChange
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    ∑ y, kernel a ha hm x y *
        (statePotential a y - statePotential a x) =
      expectedGlobalPotentialChange L (a / 2)
        (countLabel x) (deletionLabel a x) := by
  have hpoint (y : InventoryState (DyadicNode L) m) :
      statePotential a y - statePotential a x =
        ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
          (nodeMass (d + 1) v) ^ 2 *
            (harmonicPotential (a / 2)
                ((aggregatedInventory y).count (d + 1) v) -
              harmonicPotential (a / 2)
                ((aggregatedInventory x).count (d + 1) v)) := by
    unfold statePotential globalHarmonicPotential countLabel
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  simp_rw [hpoint, Finset.mul_sum]
  calc
    ∑ y, ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
        kernel a ha hm x y *
          ((nodeMass (d + 1) v) ^ 2 *
            (harmonicPotential (a / 2)
                ((aggregatedInventory y).count (d + 1) v) -
              harmonicPotential (a / 2)
                ((aggregatedInventory x).count (d + 1) v))) =
        ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
          (nodeMass (d + 1) v) ^ 2 *
            (∑ y, kernel a ha hm x y *
              (harmonicPotential (a / 2)
                  ((aggregatedInventory y).count (d + 1) v) -
                harmonicPotential (a / 2)
                  ((aggregatedInventory x).count (d + 1) v))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = expectedGlobalPotentialChange L (a / 2)
          (countLabel x) (deletionLabel a x) := by
      unfold expectedGlobalPotentialChange countLabel deletionLabel
      apply Finset.sum_congr rfl
      intro d hd
      have hdL : d < L := Finset.mem_range.mp hd
      apply Finset.sum_congr rfl
      intro v hv
      rw [kernel_expected_nodePotentialChange a ha hm x
        (show d + 1 ≤ L by omega) v]

theorem kernel_drift_eq_stateDrift_sub_stateRemainder
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    ∑ y, kernel a ha hm x y *
        (statePotential a y - statePotential a x) =
      stateDrift a x - stateRemainder a x := by
  rw [kernel_expected_globalPotentialChange a ha hm x]
  exact expectedGlobalPotentialChange_eq_drift_sub_remainder
    (by linarith : 0 < a / 2)
    (fun d v hzero => by
      change
        ((aggregatedInventory x).count d v : ℝ) *
          TreePolicy.rate (aggregatedInventory x) a d v = 0
      change (aggregatedInventory x).count d v = 0 at hzero
      rw [hzero]
      simp)

/-! ## Pointwise energy and remainder bounds -/

theorem countLabel_le_total_all
    (x : InventoryState (DyadicNode L) m)
    (d : ℕ) (v : DyadicNode d) :
    countLabel x d v ≤ m :=
  FD1D.HierarchicalDynamics.countLabel_le_total_all x d v

theorem deletionLabel_nonneg
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    0 ≤ deletionLabel a x d v :=
  TreePolicy.deletionMass_nonneg
    (aggregatedInventory x) ha hm hdL v

theorem deletionLabel_le_one
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    deletionLabel a x d v ≤ 1 := by
  rw [← TreePolicy.sum_deletionMass
    (aggregatedInventory x) hm hdL]
  exact Finset.single_le_sum
    (fun w _ =>
      TreePolicy.deletionMass_nonneg
        (aggregatedInventory x) ha hm hdL w)
    (Finset.mem_univ v)

theorem intervalMass_le_count_add_half_mul_rate
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    nodeMass d v ≤
      ((countLabel x d v : ℝ) + a / 2) * rateLabel a x d v :=
  TreePolicy.intervalMass_le_count_add_half_mul_rate
    (aggregatedInventory x) ha hm hdL v

theorem stateDrift_lower_bound
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    stateDrift a x ≥
      a / 1000 * stateRateEnergy a x L +
        stateTransportEnergy a x / (1000 * a) -
        501 * a / (1000 * (m : ℝ) ^ 2) := by
  exact TreePolicy.deterministic_aggregate_estimate
    (aggregatedInventory x) ha hm

theorem stateRateEnergy_step
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d < L) :
    stateRateEnergy a x d ≤ stateRateEnergy a x (d + 1) :=
  TreePolicy.rateEnergy_mono (aggregatedInventory x) ha hm hdL

theorem stateRateEnergy_mono_to_depth
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {i j : ℕ} (hij : i ≤ j) (hjL : j ≤ L) :
    stateRateEnergy a x i ≤ stateRateEnergy a x j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact (ih (by omega)).trans
        (stateRateEnergy_step a ha hm x (by omega))

theorem stateRemainder_nonneg
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    0 ≤ stateRemainder a x := by
  unfold stateRemainder potentialRemainder
  apply Finset.sum_nonneg
  intro d hd
  have hdL : d < L := Finset.mem_range.mp hd
  apply Finset.sum_nonneg
  intro v hv
  have hq := deletionLabel_le_one a ha hm x
    (show d + 1 ≤ L by omega) v
  have hp := nodeMass_nonneg (d + 1) v
  positivity

theorem stateRemainder_le_sum_rateEnergy
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    stateRemainder a x ≤
      ∑ d ∈ Finset.range L, stateRateEnergy a x (d + 1) := by
  unfold stateRemainder potentialRemainder stateRateEnergy
  apply Finset.sum_le_sum
  intro d hd
  have hdL : d < L := Finset.mem_range.mp hd
  simp only [hazardEnergy, weightedLevel]
  apply Finset.sum_le_sum
  intro v hv
  exact potentialRemainder_summand_le
    (nodeMass_nonneg (d + 1) v)
    (deletionLabel_nonneg a ha hm x (by omega) v)
    (deletionLabel_le_one a ha hm x (by omega) v)
    (by positivity)
    (intervalMass_le_count_add_half_mul_rate
      a ha hm x (by omega) v)

theorem sum_stateRateEnergy_le_depth_mul
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    (∑ d ∈ Finset.range L, stateRateEnergy a x (d + 1)) ≤
      (L : ℝ) * stateRateEnergy a x L := by
  calc
    (∑ d ∈ Finset.range L, stateRateEnergy a x (d + 1))
        ≤ ∑ _d ∈ Finset.range L, stateRateEnergy a x L := by
          apply Finset.sum_le_sum
          intro d hd
          have hdL : d < L := Finset.mem_range.mp hd
          exact stateRateEnergy_mono_to_depth a ha hm x
            (by omega) le_rfl
    _ = (L : ℝ) * stateRateEnergy a x L := by simp

theorem stateRemainder_bounds
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    0 ≤ stateRemainder a x ∧
      stateRemainder a x ≤
        ∑ d ∈ Finset.range L, stateRateEnergy a x (d + 1) ∧
      (∑ d ∈ Finset.range L, stateRateEnergy a x (d + 1)) ≤
        (L : ℝ) * stateRateEnergy a x L :=
  ⟨stateRemainder_nonneg a ha hm x,
    stateRemainder_le_sum_rateEnergy a ha hm x,
    sum_stateRateEnergy_le_depth_mul a ha hm x⟩

theorem statePotential_nonneg
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m) :
    0 ≤ statePotential a x :=
  globalHarmonicPotential_nonneg (by linarith : 0 < a / 2)

theorem statePotential_le_log_one_add_two_mul_div
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m) :
    statePotential a x ≤
      Real.log (1 + 2 * (m : ℝ) / a) := by
  have hbound := globalHarmonicPotential_le_log_one_add
    (L := L) (m := m) (a := a / 2)
    (by linarith : 0 < a / 2)
    (countLabel_le_total_all x)
  change globalHarmonicPotential L (a / 2) (countLabel x) ≤ _
  calc
    globalHarmonicPotential L (a / 2) (countLabel x) ≤
        Real.log (1 + (m : ℝ) / (a / 2)) := hbound
    _ = Real.log (1 + 2 * (m : ℝ) / a) := by
      congr 1
      field_simp [ha.ne']

end

end FD1D.V5.Dynamics
