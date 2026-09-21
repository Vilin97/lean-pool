/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Transport
import LeanPool.FullyDynamicMatching.FD1D.Dynamics
import LeanPool.FullyDynamicMatching.FD1D.Bounds
import LeanPool.FullyDynamicMatching.FD1D.Spatial

/-! # Concrete Transport -/

namespace FD1D

noncomputable section

open scoped BigOperators
open Set MeasureTheory

/-!
# Concrete transport for the hierarchical count chain

This module identifies the recursive dyadic mass used by the analytic
transport argument with the deletion probabilities of the concrete
hierarchical policy.
-/

namespace HierarchicalDynamics

variable {L m : ℕ}

/-- The deletion-mass tree below `v`, with `k` levels still to descend. -/
def stateDyadicMassAt (a : ℝ)
    (x : InventoryState (DyadicNode L) m) :
    (d k : ℕ) → DyadicNode d → DyadicMass k
  | d, 0, v => .leaf (deletionLabel a x d v)
  | d, k + 1, v =>
      .branch
        (stateDyadicMassAt a x (d + 1) k (leftChild v))
        (stateDyadicMassAt a x (d + 1) k (rightChild v))

/-- The complete depth-`L` deletion-mass tree of a count state. -/
def stateDyadicMass (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : DyadicMass L :=
  stateDyadicMassAt a x 0 L dyadicRoot

@[simp] theorem stateDyadicMassAt_zero
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    (d : ℕ) (v : DyadicNode d) :
    stateDyadicMassAt a x d 0 v =
      .leaf (deletionLabel a x d v) :=
  rfl

@[simp] theorem stateDyadicMassAt_succ
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    (d k : ℕ) (v : DyadicNode d) :
    stateDyadicMassAt a x d (k + 1) v =
      .branch
        (stateDyadicMassAt a x (d + 1) k (leftChild v))
        (stateDyadicMassAt a x (d + 1) k (rightChild v)) :=
  rfl

/-- Every concrete recursive subtree has its policy deletion mass as total. -/
theorem stateDyadicMassAt_total
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m)
    {d k : ℕ} (hdk : d + k ≤ L) (v : DyadicNode d) :
    (stateDyadicMassAt a x d k v).total =
      deletionLabel a x d v := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
      simp only [stateDyadicMassAt, DyadicMass.total]
      rw [ih (d := d + 1) (by omega) (leftChild v),
        ih (d := d + 1) (by omega) (rightChild v)]
      symm
      exact HierarchicalPolicy.deletionMass_children
        (aggregatedInventory x) ha d (by omega) v

theorem stateDyadicMassAt_allNonneg
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d k : ℕ} (hdk : d + k ≤ L) (v : DyadicNode d) :
    (stateDyadicMassAt a x d k v).allNonneg := by
  induction k generalizing d with
  | zero =>
      exact deletionLabel_nonneg a ha hm x (by omega) v
  | succ k ih =>
      exact ⟨ih (d := d + 1) (by omega) (leftChild v),
        ih (d := d + 1) (by omega) (rightChild v)⟩

/-- At remaining depth zero, the recursive leaf is the concrete deletion
probability of that leaf. -/
theorem stateDyadicMassAt_leaf_probability
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    stateDyadicMassAt a x L 0 w =
      .leaf ((deletionRule a ha hm).prob x w) := by
  rw [stateDyadicMassAt_zero, deletionRule_prob]
  rfl

@[simp] theorem stateDyadicMass_total
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    (stateDyadicMass a x).total = 1 := by
  rw [stateDyadicMass,
    stateDyadicMassAt_total a ha x (by omega)]
  exact HierarchicalPolicy.deletionMass_root
    (aggregatedInventory x) a hm

theorem stateDyadicMass_isProbability
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    (stateDyadicMass a x).IsProbability where
  nonneg :=
    stateDyadicMassAt_allNonneg a ha hm x (by omega) dyadicRoot
  total_eq_one := stateDyadicMass_total a ha hm x

/-- The root coefficient of every recursive subtree is the concrete policy
imbalance at the same node. -/
theorem stateDyadicMassAt_rootCoefficient
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m)
    {d k : ℕ} (hdk : d + (k + 1) ≤ L) (v : DyadicNode d) :
    (stateDyadicMassAt a x (d + 1) k (leftChild v)).total -
        (stateDyadicMassAt a x (d + 1) k (rightChild v)).total =
      HierarchicalPolicy.imbalance (aggregatedInventory x) a d v := by
  rw [stateDyadicMassAt_total a ha x (by omega),
    stateDyadicMassAt_total a ha x (by omega)]
  rfl

/-- Prefix a relative dyadic node by an absolute node. -/
private def appendDyadicNode {d r : ℕ}
    (v : DyadicNode d) (w : DyadicNode r) :
    DyadicNode (d + r) :=
  ⟨v.val * 2 ^ r + w.val, by
    rw [pow_add]
    calc
      v.val * 2 ^ r + w.val < (v.val + 1) * 2 ^ r := by
        rw [Nat.add_mul, one_mul]
        omega
      _ ≤ 2 ^ d * 2 ^ r :=
        Nat.mul_le_mul_right (2 ^ r) (Nat.succ_le_iff.mpr v.isLt)⟩

@[simp] private theorem appendDyadicNode_zero
    {d : ℕ} (v : DyadicNode d) :
    appendDyadicNode v (0 : DyadicNode 0) = v := by
  apply Fin.ext
  simp [appendDyadicNode]

private theorem appendDyadicNode_leftNode_heq
    {d k : ℕ} (v : DyadicNode d) (j : CompleteHaarNode k) :
    appendDyadicNode v (DyadicMass.leftNode j).2 ≍
      appendDyadicNode (leftChild v) j.2 := by
  apply (Fin.heq_ext_iff (by
    congr 1
    simp [DyadicMass.leftNode]
    omega)).2
  simp only [appendDyadicNode, DyadicMass.leftNode, leftChild_val]
  simp only [Fin.val_succ, pow_succ]
  ring

private theorem appendDyadicNode_rightNode_heq
    {d k : ℕ} (v : DyadicNode d) (j : CompleteHaarNode k) :
    appendDyadicNode v (DyadicMass.rightNode j).2 ≍
      appendDyadicNode (rightChild v) j.2 := by
  apply (Fin.heq_ext_iff (by
    congr 1
    simp [DyadicMass.rightNode]
    omega)).2
  simp only [appendDyadicNode, DyadicMass.rightNode, rightChild_val]
  simp only [Fin.val_succ, pow_succ]
  ring

private theorem appendDyadicNode_inl_heq
    {d k : ℕ} (v : DyadicNode d) (w : DyadicNode k) :
    appendDyadicNode v (dyadicLeafSumEquiv k (Sum.inl w)) ≍
      appendDyadicNode (leftChild v) w := by
  apply (Fin.heq_ext_iff (by
    congr 1
    omega)).2
  simp only [appendDyadicNode, dyadicLeafSumEquiv_inl_val,
    leftChild_val, pow_succ]
  ring

private theorem appendDyadicNode_inr_heq
    {d k : ℕ} (v : DyadicNode d) (w : DyadicNode k) :
    appendDyadicNode v (dyadicLeafSumEquiv k (Sum.inr w)) ≍
      appendDyadicNode (rightChild v) w := by
  apply (Fin.heq_ext_iff (by
    congr 1
    omega)).2
  simp only [appendDyadicNode, dyadicLeafSumEquiv_inr_val,
    rightChild_val, pow_succ]
  ring

private theorem deletionLabel_eq_of_depth_node_heq
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    {d e : ℕ} (hde : d = e)
    (v : DyadicNode d) (w : DyadicNode e) (hvw : v ≍ w) :
    deletionLabel a x d v = deletionLabel a x e w := by
  subst e
  rw [eq_of_heq hvw]

private theorem stateDyadicMassAt_leafMass
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    {d k : ℕ} (hdk : d + k ≤ L) (v : DyadicNode d)
    (w : DyadicNode k) :
    (stateDyadicMassAt a x d k v).leafMass w =
      deletionLabel a x (d + k) (appendDyadicNode v w) := by
  induction k generalizing d with
  | zero =>
      have hw : w = 0 := Fin.eq_zero w
      subst w
      simp [stateDyadicMassAt, DyadicMass.leafMass]
  | succ k ih =>
      obtain ⟨w | w, rfl⟩ := (dyadicLeafSumEquiv k).surjective w
      · rw [stateDyadicMassAt_succ, DyadicMass.leafMass_left,
          ih (d := d + 1) (by omega) (leftChild v) w]
        apply deletionLabel_eq_of_depth_node_heq
        · omega
        · exact (appendDyadicNode_inl_heq v w).symm
      · rw [stateDyadicMassAt_succ, DyadicMass.leafMass_right,
          ih (d := d + 1) (by omega) (rightChild v) w]
        apply deletionLabel_eq_of_depth_node_heq
        · omega
        · exact (appendDyadicNode_inr_heq v w).symm

/-- Every indexed leaf mass of the concrete dyadic tree is exactly the
probability assigned by the concrete deletion rule. -/
theorem stateDyadicMass_leafMass_eq_deletionRule
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (stateDyadicMass a x).leafMass w =
      (deletionRule a ha hm).prob x w := by
  rw [deletionRule_prob]
  rw [stateDyadicMass,
    stateDyadicMassAt_leafMass a x (by omega) dyadicRoot w]
  apply deletionLabel_eq_of_depth_node_heq
  · omega
  · apply (Fin.heq_ext_iff (by simp)).2
    simp [appendDyadicNode, dyadicRoot]

private theorem completeHaarNode_cases
    {k : ℕ} (i : CompleteHaarNode (k + 1)) :
    i = ⟨⟨0, Nat.zero_lt_succ k⟩, (0 : DyadicNode 0)⟩ ∨
      (∃ j : CompleteHaarNode k, i = DyadicMass.leftNode j) ∨
      ∃ j : CompleteHaarNode k, i = DyadicMass.rightNode j := by
  rcases i with ⟨⟨d, hd⟩, w⟩
  cases d with
  | zero =>
      left
      congr 1
      exact Fin.eq_zero w
  | succ r =>
      have hrk : r < k := by omega
      let depth : Fin k := ⟨r, hrk⟩
      by_cases hw : w.val < 2 ^ r
      · right
        left
        let u : Fin (2 ^ r) := ⟨w.val, hw⟩
        refine ⟨⟨depth, u⟩, ?_⟩
        apply Sigma.ext
        · apply Fin.ext
          simp [DyadicMass.leftNode, depth]
        · apply (Fin.heq_ext_iff
            (by simp [DyadicMass.leftNode, depth])).2
          rfl
      · right
        right
        have hwlt : w.val < 2 ^ (r + 1) := w.isLt
        have hpow : 2 ^ (r + 1) = 2 ^ r * 2 := by
          rw [pow_succ]
        have hu : w.val - 2 ^ r < 2 ^ r := by omega
        let u : Fin (2 ^ r) := ⟨w.val - 2 ^ r, hu⟩
        refine ⟨⟨depth, u⟩, ?_⟩
        apply Sigma.ext
        · apply Fin.ext
          simp [DyadicMass.rightNode, depth]
        · apply (Fin.heq_ext_iff
            (by simp [DyadicMass.rightNode, depth])).2
          dsimp [u, DyadicMass.rightNode, depth]
          omega

private theorem imbalance_eq_of_depth_node_heq
    (I : AggregatedInventory L m) (a : ℝ)
    {d e : ℕ} (hde : d = e)
    (v : DyadicNode d) (w : DyadicNode e) (hvw : v ≍ w) :
    HierarchicalPolicy.imbalance I a d v =
      HierarchicalPolicy.imbalance I a e w := by
  subst e
  rw [eq_of_heq hvw]

private theorem stateDyadicMassAt_nodeCoefficient
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m)
    {d k : ℕ} (hdk : d + k ≤ L) (v : DyadicNode d)
    (i : CompleteHaarNode k) :
    (stateDyadicMassAt a x d k v).nodeCoefficient i =
      HierarchicalPolicy.imbalance (aggregatedInventory x) a
        (d + i.1.val) (appendDyadicNode v i.2) := by
  induction k generalizing d with
  | zero => exact Fin.elim0 i.1
  | succ k ih =>
      rcases completeHaarNode_cases i with hi | hi | hi
      · subst i
        rw [stateDyadicMassAt_succ]
        simp only [DyadicMass.nodeCoefficient,
          DyadicMass.nodeChildMasses,
          Nat.add_zero, appendDyadicNode_zero]
        exact stateDyadicMassAt_rootCoefficient a ha x hdk v
      · rcases hi with ⟨j, rfl⟩
        rw [stateDyadicMassAt_succ,
          DyadicMass.nodeCoefficient_leftNode,
          ih (d := d + 1) (by omega) (leftChild v) j]
        apply imbalance_eq_of_depth_node_heq
        · simp [DyadicMass.leftNode]
          omega
        · exact (appendDyadicNode_leftNode_heq v j).symm
      · rcases hi with ⟨j, rfl⟩
        rw [stateDyadicMassAt_succ,
          DyadicMass.nodeCoefficient_rightNode,
          ih (d := d + 1) (by omega) (rightChild v) j]
        apply imbalance_eq_of_depth_node_heq
        · simp [DyadicMass.rightNode]
          omega
        · exact (appendDyadicNode_rightNode_heq v j).symm

/-- Every canonical Haar coefficient of the concrete mass tree is exactly
the policy imbalance at the same depth and node. -/
theorem stateDyadicMass_nodeCoefficient
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m)
    (i : CompleteHaarNode L) :
    (stateDyadicMass a x).nodeCoefficient i =
      HierarchicalPolicy.imbalance (aggregatedInventory x) a
        i.1.val i.2 := by
  rw [stateDyadicMass,
    stateDyadicMassAt_nodeCoefficient a ha x (by omega) dyadicRoot i]
  congr 2
  · omega
  · apply (Fin.heq_ext_iff (by simp)).2
    simp [appendDyadicNode, dyadicRoot]

/-- The recursive Haar series of the concrete policy is the canonical
complete-tree tent combination with the policy imbalances as coefficients. -/
theorem stateDyadicMass_haarSeries_eq
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (stateDyadicMass a x).haarSeries z =
      haarCombination (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
        (fun i : CompleteHaarNode L => HierarchicalPolicy.imbalance
          (aggregatedInventory x) a i.1.val i.2) z := by
  rw [(stateDyadicMass a x).haarSeries_eq_haarCombination hz.1 hz.2]
  apply congrFun
  congr 1
  funext i
  exact stateDyadicMass_nodeCoefficient a ha x i

/-- The concrete coefficient family in the canonical complete-tree index. -/
def stateHaarCoefficient (a : ℝ)
    (x : InventoryState (DyadicNode L) m)
    (i : CompleteHaarNode L) : ℝ :=
  HierarchicalPolicy.imbalance
    (aggregatedInventory x) a i.1.val i.2

/-- The monotone quantile policy associated with a concrete count state. -/
def stateQuantilePolicy
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    MonotoneQuantilePolicy (stateDyadicMass a x).piecewiseCDF :=
  (stateDyadicMass a x).quantilePolicy
    (stateDyadicMass_isProbability a ha hm x)

/-- Cost of the continuous quantile map before rounding to a cell endpoint. -/
def stateQuantileCost
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  (stateQuantilePolicy a ha hm x).quantileDistance

/-- Cost of the demand-driven selected cell endpoint. -/
def stateCellCost
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  (stateQuantilePolicy a ha hm x).expectedDistance

private theorem stateDiscrepancyArea_eq_haarArea
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    cdfTransportArea
        (fun z => (stateDyadicMass a x).piecewiseCDF z - z) =
      cdfTransportArea
        (haarCombination (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) (stateHaarCoefficient a x)) := by
  unfold cdfTransportArea
  apply setIntegral_congr_fun measurableSet_Icc
  intro z hz
  apply congrArg abs
  calc
    (stateDyadicMass a x).piecewiseCDF z - z =
        (stateDyadicMass a x).haarSeries z :=
      (stateDyadicMass a x).quantile_discrepancy_eq_haar
        (stateDyadicMass_isProbability a ha hm x) hz
    _ = haarCombination (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) (stateHaarCoefficient a x) z := by
      unfold stateHaarCoefficient
      exact stateDyadicMass_haarSeries_eq a ha x hz

/-- The continuous quantile cost is the CDF area of the canonical concrete
Haar combination. -/
theorem stateQuantileCost_eq_haarArea
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    stateQuantileCost a ha hm x =
      cdfTransportArea
        (haarCombination (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) (stateHaarCoefficient a x)) := by
  rw [stateQuantileCost,
    MonotoneQuantilePolicy.quantileDistance_eq_cdfTransportArea]
  exact stateDiscrepancyArea_eq_haarArea a ha hm x

/-- Pointwise transport-cost hypothesis used by equation (3). -/
theorem stateCellCost_pointwise
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    stateCellCost a ha hm x ≤ 1 / ((2 ^ L : ℕ) : ℝ) +
      cdfTransportArea
        (haarCombination (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) (stateHaarCoefficient a x)) := by
  calc
    stateCellCost a ha hm x ≤ 1 / ((2 ^ L : ℕ) : ℝ) +
        cdfTransportArea
          (fun z => (stateDyadicMass a x).piecewiseCDF z - z) := by
      exact (stateDyadicMass a x).quantile_cost_within_leaf
        (stateDyadicMass_isProbability a ha hm x)
    _ = _ := by
      rw [stateDiscrepancyArea_eq_haarArea a ha hm x]

/-- Spatial's actual occupied-point selector satisfies the same one-cell
pointwise hypothesis for the concrete hierarchical deletion rule. -/
theorem stateActualCost_pointwise
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (C : SupplyConfiguration L m) (fallback : Fin m) :
    C.expectedActualDistance (stateDyadicMass a C.countState) fallback ≤
      1 / ((2 ^ L : ℕ) : ℝ) +
        cdfTransportArea
          (haarCombination (haarNodeLeft (L := L))
            (haarNodeWidth (L := L))
            (stateHaarCoefficient a C.countState)) := by
  calc
    C.expectedActualDistance (stateDyadicMass a C.countState) fallback ≤
        dyadicCellWidth L +
          cdfTransportArea (fun z =>
            (stateDyadicMass a C.countState).piecewiseCDF z - z) := by
      exact C.expectedActualDistance_le_one_cell_of_deletionRule
        (stateDyadicMass a C.countState)
        (stateDyadicMass_isProbability a ha hm C.countState)
        (deletionRule a ha hm)
        (stateDyadicMass_leafMass_eq_deletionRule a ha hm C.countState)
        fallback
    _ = _ := by
      rw [stateDiscrepancyArea_eq_haarArea a ha hm C.countState]
      rfl

private theorem expected_internalWeightedSum_eq
    {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (b : Ω → ∀ d, DyadicNode d → ℝ) :
    (∑ i : CompleteHaarNode L,
        haarNodeWidth i *
          μ.expect (fun ω => (b ω i.1.val i.2) ^ 2)) =
      μ.expect (fun ω =>
        internalWeightedSum (fun d v => (b ω d v) ^ 2) L) := by
  rw [Fintype.sum_sigma]
  simp only [haarNodeWidth, one_div]
  change (∑ d : Fin L, ∑ v : DyadicNode d.val,
      ((2 ^ d.val : ℕ) : ℝ)⁻¹ *
        μ.expect (fun ω => (b ω d.val v) ^ 2)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun d => ∑ v : DyadicNode d,
      ((2 ^ d : ℕ) : ℝ)⁻¹ *
        μ.expect (fun ω => (b ω d v) ^ 2)) L]
  unfold FiniteLaw.expect internalWeightedSum weightedLevel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω hω
  apply Finset.sum_congr rfl
  intro v hv
  simp [nodeMass]
  ring

/-- Expected equation (2), derived pointwise from the concrete policy's
hazard-energy telescope.  The sample type may contain data besides the count
state, which is useful for time averages and spatial configurations. -/
theorem expected_equation_two
    {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω)
    (state : Ω → InventoryState (DyadicNode L) m)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (∑ i : CompleteHaarNode L,
        haarNodeWidth i * μ.expect (fun ω =>
          (stateHaarCoefficient a (state ω) i) ^ 2)) ≤
      2 * a ^ 2 *
        (μ.expect (fun ω => stateHazardEnergy a (state ω) L) -
          1 / (m : ℝ) ^ 2) := by
  calc
    (∑ i : CompleteHaarNode L,
        haarNodeWidth i * μ.expect (fun ω =>
          (stateHaarCoefficient a (state ω) i) ^ 2)) =
        μ.expect (fun ω => internalWeightedSum
          (fun d v => (HierarchicalPolicy.imbalance
            (aggregatedInventory (state ω)) a d v) ^ 2) L) := by
      simpa [stateHaarCoefficient] using
        expected_internalWeightedSum_eq μ
          (fun ω d v => HierarchicalPolicy.imbalance
            (aggregatedInventory (state ω)) a d v)
    _ ≤ μ.expect (fun ω => 2 * a ^ 2 *
          (stateHazardEnergy a (state ω) L -
            1 / (m : ℝ) ^ 2)) := by
      apply μ.expect_mono
      intro ω
      simpa [stateHazardEnergy, hazardLabel] using
        HierarchicalPolicy.hazard_energy_bound
          (aggregatedInventory (state ω)) ha hm
    _ = 2 * a ^ 2 *
        (μ.expect (fun ω => stateHazardEnergy a (state ω) L) -
          1 / (m : ℝ) ^ 2) := by
      rw [μ.expect_const_mul, μ.expect_sub, μ.expect_const]

theorem expected_hazard_gap_nonneg
    {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω)
    (state : Ω → InventoryState (DyadicNode L) m)
    (a : ℝ) (ha : 0 < a) :
    0 ≤ μ.expect (fun ω => stateHazardEnergy a (state ω) L) -
      1 / (m : ℝ) ^ 2 := by
  have h := μ.expect_mono
    (f := fun _ => 1 / (m : ℝ) ^ 2)
    (g := fun ω => stateHazardEnergy a (state ω) L)
    (fun ω => stateHazardEnergy_root_le a ha (state ω))
  rw [μ.expect_const] at h
  linarith

/--
Concrete equation (3) for an arbitrary finite sample space and state
projection.  Callers supply only the pointwise cost comparison and the
law-level separated-or-odd `hsym` condition; equation (2) is discharged
internally by `expected_equation_two`.
-/
theorem concrete_transport_equation_three
    {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω)
    (state : Ω → InventoryState (DyadicNode L) m)
    (cost : Ω → ℝ)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hcost : ∀ ω, cost ω ≤ 1 / ((2 ^ L : ℕ) : ℝ) +
      cdfTransportArea
        (haarCombination (haarNodeLeft (L := L))
          (haarNodeWidth (L := L))
          (stateHaarCoefficient a (state ω))))
    (hsym : ∀ i j : CompleteHaarNode L, i ≠ j →
      IntervalsSeparated (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) i j ∨
        μ.OddSymmetry (fun ω =>
          stateHaarCoefficient a (state ω) i *
            stateHaarCoefficient a (state ω) j)) :
    μ.expect cost ≤ 1 / ((2 ^ L : ℕ) : ℝ) +
      a / Real.sqrt 6 *
        Real.sqrt
          (μ.expect (fun ω => stateHazardEnergy a (state ω) L) -
            1 / (m : ℝ) ^ 2) := by
  let gap :=
    μ.expect (fun ω => stateHazardEnergy a (state ω) L) -
      1 / (m : ℝ) ^ 2
  exact transport_cost_equation_three
    μ (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
    (fun ω => stateHaarCoefficient a (state ω)) cost
    (((2 ^ L : ℕ) : ℝ)) a gap
    (by positivity) ha.le
    (expected_hazard_gap_nonneg μ state a ha)
    (fun i => haarNodeWidth_pos i)
    hcost hsym (expected_equation_two μ state a ha hm)

/-- Equation (3) specialized to the concrete selected-cell endpoint cost. -/
theorem expected_stateCellCost_equation_three
    {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω)
    (state : Ω → InventoryState (DyadicNode L) m)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (hsym : ∀ i j : CompleteHaarNode L, i ≠ j →
      IntervalsSeparated (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) i j ∨
        μ.OddSymmetry (fun ω =>
          stateHaarCoefficient a (state ω) i *
            stateHaarCoefficient a (state ω) j)) :
    μ.expect (fun ω => stateCellCost a ha hm (state ω)) ≤
      1 / ((2 ^ L : ℕ) : ℝ) +
        a / Real.sqrt 6 *
          Real.sqrt
            (μ.expect (fun ω => stateHazardEnergy a (state ω) L) -
              1 / (m : ℝ) ^ 2) := by
  apply concrete_transport_equation_three μ state
    (fun ω => stateCellCost a ha hm (state ω)) a ha hm
  · exact fun ω => stateCellCost_pointwise a ha hm (state ω)
  · exact hsym

end HierarchicalDynamics

end

end FD1D
