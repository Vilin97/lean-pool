/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.V5.Energy
public import LeanPool.FullyDynamicMatching.FD1D.V5.Symmetry
public import LeanPool.FullyDynamicMatching.FD1D.InvariantTransport
public import LeanPool.FullyDynamicMatching.FD1D.Initialization
public import LeanPool.FullyDynamicMatching.FD1D.Averaging
public import LeanPool.FullyDynamicMatching.FD1D.Spatial

/-!
# Quantile transport for the v5 policy

This module realizes the v5 leaf deletion probabilities as a recursive
dyadic mass, identifies its integrated Haar coefficients with the v5
deletion imbalances, and proves the exact invariant-law `L²` identity.
-/

@[expose] public section

namespace FD1D.V5.Transport

noncomputable section

open scoped BigOperators
open Set MeasureTheory

variable {L m : ℕ}

/-! ## The concrete v5 dyadic mass -/

/-- The v5 deletion-mass tree below `v`, with `k` levels left to descend. -/
def stateDyadicMassAt (a : ℝ)
    (x : InventoryState (DyadicNode L) m) :
    (d k : ℕ) → DyadicNode d → DyadicMass k
  | d, 0, v => .leaf (Dynamics.deletionLabel a x d v)
  | d, k + 1, v =>
      .branch
        (stateDyadicMassAt a x (d + 1) k (leftChild v))
        (stateDyadicMassAt a x (d + 1) k (rightChild v))

/-- The complete v5 deletion-mass tree. -/
def stateDyadicMass (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : DyadicMass L :=
  stateDyadicMassAt a x 0 L dyadicRoot

@[simp] theorem stateDyadicMassAt_zero
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    (d : ℕ) (v : DyadicNode d) :
    stateDyadicMassAt a x d 0 v =
      .leaf (Dynamics.deletionLabel a x d v) :=
  rfl

@[simp] theorem stateDyadicMassAt_succ
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    (d k : ℕ) (v : DyadicNode d) :
    stateDyadicMassAt a x d (k + 1) v =
      .branch
        (stateDyadicMassAt a x (d + 1) k (leftChild v))
        (stateDyadicMassAt a x (d + 1) k (rightChild v)) :=
  rfl

theorem stateDyadicMassAt_total
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    {d k : ℕ} (hdk : d + k ≤ L) (v : DyadicNode d) :
    (stateDyadicMassAt a x d k v).total =
      Dynamics.deletionLabel a x d v := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
      simp only [stateDyadicMassAt, DyadicMass.total]
      rw [ih (d := d + 1) (by omega) (leftChild v),
        ih (d := d + 1) (by omega) (rightChild v)]
      symm
      exact TreePolicy.deletionMass_children
        (Dynamics.aggregatedInventory x) a d (by omega) v

theorem stateDyadicMassAt_allNonneg
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d k : ℕ} (hdk : d + k ≤ L) (v : DyadicNode d) :
    (stateDyadicMassAt a x d k v).allNonneg := by
  induction k generalizing d with
  | zero =>
      exact Dynamics.deletionLabel_nonneg a ha hm x (by omega) v
  | succ k ih =>
      exact ⟨ih (d := d + 1) (by omega) (leftChild v),
        ih (d := d + 1) (by omega) (rightChild v)⟩

theorem stateDyadicMassAt_leaf_probability
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    stateDyadicMassAt a x L 0 w =
      .leaf ((Dynamics.deletionRule a ha hm).prob x w) := by
  rw [stateDyadicMassAt_zero, Dynamics.deletionRule_prob]
  rfl

@[simp] theorem stateDyadicMass_total
    (a : ℝ) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    (stateDyadicMass a x).total = 1 := by
  rw [stateDyadicMass, stateDyadicMassAt_total a x (by omega)]
  exact TreePolicy.deletionMass_root
    (Dynamics.aggregatedInventory x) a hm

theorem stateDyadicMass_isProbability
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    (stateDyadicMass a x).IsProbability where
  nonneg :=
    stateDyadicMassAt_allNonneg a ha hm x (by omega) dyadicRoot
  total_eq_one := stateDyadicMass_total a hm x

theorem stateDyadicMassAt_rootCoefficient
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    {d k : ℕ} (hdk : d + (k + 1) ≤ L) (v : DyadicNode d) :
    (stateDyadicMassAt a x (d + 1) k (leftChild v)).total -
        (stateDyadicMassAt a x (d + 1) k (rightChild v)).total =
      TreePolicy.imbalance (Dynamics.aggregatedInventory x) a d v := by
  rw [stateDyadicMassAt_total a x (by omega),
    stateDyadicMassAt_total a x (by omega)]
  rfl

/-! ## Canonical tree indexing -/

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
    Dynamics.deletionLabel a x d v =
      Dynamics.deletionLabel a x e w := by
  subst e
  rw [eq_of_heq hvw]

private theorem stateDyadicMassAt_leafMass
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    {d k : ℕ} (hdk : d + k ≤ L) (v : DyadicNode d)
    (w : DyadicNode k) :
    (stateDyadicMassAt a x d k v).leafMass w =
      Dynamics.deletionLabel a x (d + k)
        (appendDyadicNode v w) := by
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

theorem stateDyadicMass_leafMass_eq_deletionRule
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (stateDyadicMass a x).leafMass w =
      (Dynamics.deletionRule a ha hm).prob x w := by
  rw [Dynamics.deletionRule_prob]
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
    TreePolicy.imbalance I a d v =
      TreePolicy.imbalance I a e w := by
  subst e
  rw [eq_of_heq hvw]

private theorem stateDyadicMassAt_nodeCoefficient
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    {d k : ℕ} (hdk : d + k ≤ L) (v : DyadicNode d)
    (i : CompleteHaarNode k) :
    (stateDyadicMassAt a x d k v).nodeCoefficient i =
      TreePolicy.imbalance (Dynamics.aggregatedInventory x) a
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
        exact stateDyadicMassAt_rootCoefficient a x hdk v
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

theorem stateDyadicMass_nodeCoefficient
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    (i : CompleteHaarNode L) :
    (stateDyadicMass a x).nodeCoefficient i =
      TreePolicy.imbalance (Dynamics.aggregatedInventory x) a
        i.1.val i.2 := by
  rw [stateDyadicMass,
    stateDyadicMassAt_nodeCoefficient a x (by omega) dyadicRoot i]
  congr 2
  · omega
  · apply (Fin.heq_ext_iff (by simp)).2
    simp [appendDyadicNode, dyadicRoot]

/-- The canonical v5 integrated-Haar coefficient family. -/
def stateHaarCoefficient (a : ℝ)
    (x : InventoryState (DyadicNode L) m)
    (i : CompleteHaarNode L) : ℝ :=
  TreePolicy.imbalance
    (Dynamics.aggregatedInventory x) a i.1.val i.2

theorem stateDyadicMass_haarSeries_eq
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (stateDyadicMass a x).haarSeries z =
      haarCombination (haarNodeLeft (L := L))
        (haarNodeWidth (L := L))
        (stateHaarCoefficient a x) z := by
  rw [(stateDyadicMass a x).haarSeries_eq_haarCombination hz.1 hz.2]
  apply congrFun
  congr 1
  funext i
  exact stateDyadicMass_nodeCoefficient a x i

theorem stateDyadicMass_cdf_sub_id_eq
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (stateDyadicMass a x).piecewiseCDF z - z =
      haarCombination (haarNodeLeft (L := L))
        (haarNodeWidth (L := L))
        (stateHaarCoefficient a x) z := by
  calc
    (stateDyadicMass a x).piecewiseCDF z - z =
        (stateDyadicMass a x).haarSeries z :=
      (stateDyadicMass a x).quantile_discrepancy_eq_haar
        (stateDyadicMass_isProbability a ha hm x) hz
    _ = _ := stateDyadicMass_haarSeries_eq a x hz

/-! ## Symmetry and exact expected Haar energy -/

theorem haarCoefficient_swapNode
    (a : ℝ) (i : CompleteHaarNode L)
    (x : InventoryState (DyadicNode L) m) :
    stateHaarCoefficient a
        (FD1D.TreeSymmetry.inventorySwap i.1.isLt i.2 x) i =
      -stateHaarCoefficient a x i := by
  exact V5.TreeSymmetry.imbalance_swapNode_general
    i.1.isLt i.2 x a

theorem haarCoefficient_strictAncestor
    (a : ℝ) (i j : CompleteHaarNode L)
    (hji : j.1.val < i.1.val)
    (x : InventoryState (DyadicNode L) m) :
    stateHaarCoefficient a
        (FD1D.TreeSymmetry.inventorySwap i.1.isLt i.2 x) j =
      stateHaarCoefficient a x j := by
  exact V5.TreeSymmetry.imbalance_strictAncestor_general
    i.1.isLt i.2 x a hji j.2

theorem haar_crossTerm_symmetry_of_swapInvariant
    (a : ℝ)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hinv : ∀ (d : Fin L) (v : DyadicNode d.val),
      FiniteKernel.LawInvariant μ
        (FD1D.TreeSymmetry.inventorySwap d.isLt v)) :
    ∀ i j, i ≠ j →
      IntervalsSeparated (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) i j ∨
        μ.OddSymmetry (fun x =>
          stateHaarCoefficient a x i *
            stateHaarCoefficient a x j) := by
  apply completeHaar_crossTerm_symmetry_of_invariant_swaps
    μ (fun x i => stateHaarCoefficient a x i)
    (fun d v => FD1D.TreeSymmetry.inventorySwap d.isLt v) hinv
  · exact fun d v x => haarCoefficient_swapNode a ⟨d, v⟩ x
  · exact fun d v k w hkd x =>
      haarCoefficient_strictAncestor a ⟨d, v⟩ ⟨k, w⟩ hkd x

theorem stationary_haar_crossTerm_symmetry
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hμ : (Dynamics.kernel a ha hm).IsStationary μ) :
    ∀ i j, i ≠ j →
      IntervalsSeparated (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) i j ∨
        μ.OddSymmetry (fun x =>
          stateHaarCoefficient a x i *
            stateHaarCoefficient a x j) := by
  apply haar_crossTerm_symmetry_of_swapInvariant a μ
  intro d v
  exact V5.TreeSymmetry.stationary_lawInvariant
    d.isLt v a ha hm hμ

theorem iterate_lawInvariant_of_swapInvariant
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hinv : ∀ (d : Fin L) (v : DyadicNode d.val),
      FiniteKernel.LawInvariant μ
        (FD1D.TreeSymmetry.inventorySwap d.isLt v))
    (n : ℕ) :
    ∀ (d : Fin L) (v : DyadicNode d.val),
      FiniteKernel.LawInvariant
        ((Dynamics.kernel a ha hm).iterate n μ)
        (FD1D.TreeSymmetry.inventorySwap d.isLt v) := by
  intro d v
  exact FiniteKernel.iterate_lawInvariant
    (V5.TreeSymmetry.kernel_equivariant d.isLt v a ha hm)
    (hinv d v) n

theorem iterate_refreshedLaw_lawInvariant
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (n : ℕ) (d : Fin L) (v : DyadicNode d.val) :
    FiniteKernel.LawInvariant
      ((Dynamics.kernel a ha hm).iterate n (refreshedLaw L m))
      (FD1D.TreeSymmetry.inventorySwap d.isLt v) := by
  apply iterate_refreshedLaw_lawInvariant_of_compatible
    (Dynamics.kernel a ha hm)
    (FD1D.TreeSymmetry.leafSwap d.isLt v)
    (FD1D.TreeSymmetry.inventorySwap d.isLt v)
  · intro omega
    calc
      assignmentState
          (assignmentPerm (FD1D.TreeSymmetry.leafSwap d.isLt v) omega) =
          inventoryStatePerm (FD1D.TreeSymmetry.leafSwap d.isLt v)
            (assignmentState omega) :=
        assignmentState_perm (FD1D.TreeSymmetry.leafSwap d.isLt v) omega
      _ = FD1D.TreeSymmetry.inventorySwap d.isLt v
          (assignmentState omega) := by
        rw [FD1D.TreeSymmetry.inventorySwap,
          FD1D.TreeSymmetry.inventoryPerm_eq_inventoryStatePerm]
  · exact V5.TreeSymmetry.kernel_equivariant d.isLt v a ha hm

private theorem expected_internalWeightedSum_eq
    {Omega : Type*} [Fintype Omega]
    (μ : FiniteLaw Omega)
    (b : Omega → ∀ d, DyadicNode d → ℝ) :
    (∑ i : CompleteHaarNode L,
        haarNodeWidth i *
          μ.expect (fun omega => (b omega i.1.val i.2) ^ 2)) =
      μ.expect (fun omega =>
        internalWeightedSum (fun d v => (b omega d v) ^ 2) L) := by
  rw [Fintype.sum_sigma]
  simp only [haarNodeWidth, one_div]
  change (∑ d : Fin L, ∑ v : DyadicNode d.val,
      ((2 ^ d.val : ℕ) : ℝ)⁻¹ *
        μ.expect (fun omega => (b omega d.val v) ^ 2)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun d => ∑ v : DyadicNode d,
      ((2 ^ d : ℕ) : ℝ)⁻¹ *
        μ.expect (fun omega => (b omega d v) ^ 2)) L]
  unfold FiniteLaw.expect internalWeightedSum weightedLevel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega homega
  apply Finset.sum_congr rfl
  intro v hv
  simp [nodeMass]
  ring

/-- Cancellation and transport energy: `E ||F_Q-id||₂² = E G / 12`. -/
theorem expected_haarL2_eq_transportEnergy
    (a : ℝ)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hinv : ∀ (d : Fin L) (v : DyadicNode d.val),
      FiniteKernel.LawInvariant μ
        (FD1D.TreeSymmetry.inventorySwap d.isLt v)) :
    μ.expect (fun x =>
        haarL2 (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
          (stateHaarCoefficient a x)) =
      (1 / 12) * μ.expect (Dynamics.stateTransportEnergy a) := by
  rw [expected_haarL2 μ
    (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
    (fun x => stateHaarCoefficient a x)
    (fun i => haarNodeWidth_pos i)
    (haar_crossTerm_symmetry_of_swapInvariant a μ hinv)]
  congr 1
  change
    (∑ i : CompleteHaarNode L, haarNodeWidth i *
      μ.expect (fun x =>
        (TreePolicy.imbalance (Dynamics.aggregatedInventory x) a
          i.1.val i.2) ^ 2)) =
      μ.expect (Dynamics.stateTransportEnergy a)
  calc
    _ = μ.expect (fun x =>
        internalWeightedSum
          (fun d v =>
            (TreePolicy.imbalance
              (Dynamics.aggregatedInventory x) a d v) ^ 2) L) :=
      expected_internalWeightedSum_eq μ
        (fun x d v =>
          TreePolicy.imbalance (Dynamics.aggregatedInventory x) a d v)
    _ = μ.expect (Dynamics.stateTransportEnergy a) := by
      rfl

theorem stationary_expected_haarL2_eq_transportEnergy
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hμ : (Dynamics.kernel a ha hm).IsStationary μ) :
    μ.expect (fun x =>
        haarL2 (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
          (stateHaarCoefficient a x)) =
      (1 / 12) * μ.expect (Dynamics.stateTransportEnergy a) := by
  apply expected_haarL2_eq_transportEnergy a μ
  intro d v
  exact V5.TreeSymmetry.stationary_lawInvariant
    d.isLt v a ha hm hμ

/-! ## First-moment quantile cost -/

/-- Expected distance under the quantile policy of the state dyadic mass. -/
def stateCellCost
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  ((stateDyadicMass a x).quantilePolicy
    (stateDyadicMass_isProbability a ha hm x)).expectedDistance

theorem stateCellCost_pointwise
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    stateCellCost a ha hm x ≤
      1 / ((2 ^ L : ℕ) : ℝ) +
        cdfTransportArea
          (haarCombination (haarNodeLeft (L := L))
            (haarNodeWidth (L := L))
            (stateHaarCoefficient a x)) := by
  calc
    stateCellCost a ha hm x ≤
        1 / ((2 ^ L : ℕ) : ℝ) +
          cdfTransportArea (fun z =>
            (stateDyadicMass a x).piecewiseCDF z - z) := by
      exact (stateDyadicMass a x).quantile_cost_within_leaf
        (stateDyadicMass_isProbability a ha hm x)
    _ = _ := by
      congr 1
      unfold cdfTransportArea
      apply setIntegral_congr_fun measurableSet_Icc
      intro z hz
      change
        |(stateDyadicMass a x).piecewiseCDF z - z| =
          |haarCombination (haarNodeLeft (L := L))
            (haarNodeWidth (L := L))
            (stateHaarCoefficient a x) z|
      rw [stateDyadicMass_cdf_sub_id_eq a ha hm x hz]

theorem expected_stateCellCost_le
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hinv : ∀ (d : Fin L) (v : DyadicNode d.val),
      FiniteKernel.LawInvariant μ
        (FD1D.TreeSymmetry.inventorySwap d.isLt v)) :
    μ.expect (stateCellCost a ha hm) ≤
      1 / ((2 ^ L : ℕ) : ℝ) +
        Real.sqrt ((1 / 12) *
          μ.expect (Dynamics.stateTransportEnergy a)) := by
  calc
    μ.expect (stateCellCost a ha hm) ≤
        μ.expect (fun x =>
          1 / ((2 ^ L : ℕ) : ℝ) +
            cdfTransportArea
              (haarCombination (haarNodeLeft (L := L))
                (haarNodeWidth (L := L))
                (stateHaarCoefficient a x))) :=
      μ.expect_mono (stateCellCost_pointwise a ha hm)
    _ = 1 / ((2 ^ L : ℕ) : ℝ) +
        μ.expect (fun x =>
          cdfTransportArea
            (haarCombination (haarNodeLeft (L := L))
              (haarNodeWidth (L := L))
              (stateHaarCoefficient a x))) := by
      rw [μ.expect_add, μ.expect_const]
    _ ≤ 1 / ((2 ^ L : ℕ) : ℝ) +
        Real.sqrt
          (μ.expect (fun x =>
            haarL2 (haarNodeLeft (L := L))
              (haarNodeWidth (L := L))
              (stateHaarCoefficient a x))) := by
      gcongr
      exact expected_area_le_sqrt_l2 μ
        (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
        (fun x => stateHaarCoefficient a x)
        (fun i => haarNodeWidth_pos i)
    _ = _ := by
      rw [expected_haarL2_eq_transportEnergy a μ hinv]

end

end FD1D.V5.Transport
