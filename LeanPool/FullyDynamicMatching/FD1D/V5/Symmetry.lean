/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.V5.Dynamics
public import LeanPool.FullyDynamicMatching.FD1D.Symmetry

/-!
# Tree symmetry for the v5 policy

The underlying subtree permutations are policy-independent and live in
`FD1D.TreeSymmetry`. This module proves that the recursively propagated v5
rates and deletion masses are equivariant under those permutations.
-/

@[expose] public section

namespace FD1D.V5.TreeSymmetry

noncomputable section

open FD1D.TreeSymmetry
open LocalPolicy

variable {L m : ℕ}

private theorem aggregate_count_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    {r : ℕ} (hrn : r ≤ n) (w : DyadicNode ((d + 1) + r)) :
    (Dynamics.aggregatedInventory
        (inventoryPerm (subtreeSwap v n) x)).count
        ((d + 1) + r) (subtreeSwap v r w) =
      (Dynamics.aggregatedInventory x).count ((d + 1) + r) w := by
  simpa only [← FD1D.TreeSymmetry.stateAggregate_eq_aggregatedInventory] using
    FD1D.TreeSymmetry.stateAggregate_count_subtreeSwap v x hrn w

private theorem aggregate_count_aboveSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    {k : ℕ} (hkd : k ≤ d) (w : DyadicNode k) :
    (Dynamics.aggregatedInventory
        (inventoryPerm (subtreeSwap v n) x)).count k w =
      (Dynamics.aggregatedInventory x).count k w := by
  simpa only [← FD1D.TreeSymmetry.stateAggregate_eq_aggregatedInventory] using
    FD1D.TreeSymmetry.stateAggregate_count_aboveSwap v x hkd w

/-- Rates at every level weakly above the swapped node are unchanged. -/
theorem rate_aboveSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {k : ℕ} (hkd : k ≤ d) (w : DyadicNode k) :
    TreePolicy.rate
        (Dynamics.aggregatedInventory
          (inventoryPerm (subtreeSwap v n) x)) a k w =
      TreePolicy.rate (Dynamics.aggregatedInventory x) a k w := by
  induction k with
  | zero =>
      have hw : w = dyadicRoot := Fin.eq_zero w
      subst w
      rfl
  | succ k ih =>
      let z := (childrenEquiv k).symm w
      have hz : childrenEquiv k z = w :=
        (childrenEquiv k).apply_symm_apply w
      rw [← hz]
      rcases z with ⟨u, side⟩
      have hparent := ih (by omega) u
      have hleft :=
        aggregate_count_aboveSwap v x (k := k + 1)
          (by omega) (leftChild u)
      have hright :=
        aggregate_count_aboveSwap v x (k := k + 1)
          (by omega) (rightChild u)
      fin_cases side
      · change
          TreePolicy.rate
              (Dynamics.aggregatedInventory
                (inventoryPerm (subtreeSwap v n) x)) a
              (k + 1) (leftChild u) =
            TreePolicy.rate (Dynamics.aggregatedInventory x) a
              (k + 1) (leftChild u)
        rw [TreePolicy.rate_leftChild, TreePolicy.rate_leftChild,
          hparent, hleft, hright]
      · change
          TreePolicy.rate
              (Dynamics.aggregatedInventory
                (inventoryPerm (subtreeSwap v n) x)) a
              (k + 1) (rightChild u) =
            TreePolicy.rate (Dynamics.aggregatedInventory x) a
              (k + 1) (rightChild u)
        rw [TreePolicy.rate_rightChild, TreePolicy.rate_rightChild,
          hparent, hleft, hright]

/-- At the first level below `v`, rates follow the child swap. -/
theorem rate_subtreeSwap_zero
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) (w : DyadicNode (d + 1)) :
    TreePolicy.rate
        (Dynamics.aggregatedInventory
          (inventoryPerm (subtreeSwap v n) x)) a
        (d + 1) (subtreeSwap v 0 w) =
      TreePolicy.rate (Dynamics.aggregatedInventory x) a (d + 1) w := by
  let I' :=
    Dynamics.aggregatedInventory
      (inventoryPerm (subtreeSwap v n) x)
  let I := Dynamics.aggregatedInventory x
  let z := (childrenEquiv d).symm w
  have hz : childrenEquiv d z = w :=
    (childrenEquiv d).apply_symm_apply w
  rw [← hz]
  rcases z with ⟨u, side⟩
  have hparent :
      TreePolicy.rate I' a d u = TreePolicy.rate I a d u := by
    exact rate_aboveSwap v x a (le_refl d) u
  by_cases huv : u = v
  · subst u
    have hleft :=
      aggregate_count_subtreeSwap v x (r := 0) (by omega)
        (leftChild v)
    have hright :=
      aggregate_count_subtreeSwap v x (r := 0) (by omega)
        (rightChild v)
    have hleft' :
        I'.count (d + 1) (rightChild v) =
          I.count (d + 1) (leftChild v) := by
      simpa [I', I] using hleft
    have hright' :
        I'.count (d + 1) (leftChild v) =
          I.count (d + 1) (rightChild v) := by
      simpa [I', I] using hright
    fin_cases side
    · change
        TreePolicy.rate I' a (d + 1)
            (subtreeSwap v 0 (leftChild v)) =
          TreePolicy.rate I a (d + 1) (leftChild v)
      rw [subtreeSwap_zero_left]
      rw [TreePolicy.rate_rightChild, TreePolicy.rate_leftChild,
        hparent, hleft', hright']
      exact rateRight_swap a (TreePolicy.intervalMass d v)
        (TreePolicy.rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v))
    · change
        TreePolicy.rate I' a (d + 1)
            (subtreeSwap v 0 (rightChild v)) =
          TreePolicy.rate I a (d + 1) (rightChild v)
      rw [subtreeSwap_zero_right]
      rw [TreePolicy.rate_leftChild, TreePolicy.rate_rightChild,
        hparent, hleft', hright']
      exact rateLeft_swap a (TreePolicy.intervalMass d v)
        (TreePolicy.rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v))
  · have hll : leftChild u ≠ leftChild v := by
      intro h
      apply huv
      simpa using congrArg parent h
    have hlr : leftChild u ≠ rightChild v := by
      intro h
      apply huv
      simpa using congrArg parent h
    have hrl : rightChild u ≠ leftChild v := by
      intro h
      apply huv
      simpa using congrArg parent h
    have hrr : rightChild u ≠ rightChild v := by
      intro h
      apply huv
      simpa using congrArg parent h
    have hleft :=
      aggregate_count_subtreeSwap v x (r := 0) (by omega)
        (leftChild u)
    have hright :=
      aggregate_count_subtreeSwap v x (r := 0) (by omega)
        (rightChild u)
    rw [subtreeSwap_zero_of_ne v hll hlr] at hleft
    rw [subtreeSwap_zero_of_ne v hrl hrr] at hright
    have hleft' :
        I'.count (d + 1) (leftChild u) =
          I.count (d + 1) (leftChild u) := by
      simpa [I', I] using hleft
    have hright' :
        I'.count (d + 1) (rightChild u) =
          I.count (d + 1) (rightChild u) := by
      simpa [I', I] using hright
    fin_cases side
    · change
        TreePolicy.rate I' a (d + 1)
            (subtreeSwap v 0 (leftChild u)) =
          TreePolicy.rate I a (d + 1) (leftChild u)
      rw [subtreeSwap_zero_of_ne v hll hlr,
        TreePolicy.rate_leftChild, TreePolicy.rate_leftChild,
        hparent, hleft', hright']
    · change
        TreePolicy.rate I' a (d + 1)
            (subtreeSwap v 0 (rightChild u)) =
          TreePolicy.rate I a (d + 1) (rightChild u)
      rw [subtreeSwap_zero_of_ne v hrl hrr,
        TreePolicy.rate_rightChild, TreePolicy.rate_rightChild,
        hparent, hleft', hright']

/-- Rates at descendant nodes are transported by the subtree swap. -/
theorem rate_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {r : ℕ} (hrn : r ≤ n)
    (w : DyadicNode ((d + 1) + r)) :
    TreePolicy.rate
        (Dynamics.aggregatedInventory
          (inventoryPerm (subtreeSwap v n) x)) a
        ((d + 1) + r) (subtreeSwap v r w) =
      TreePolicy.rate (Dynamics.aggregatedInventory x) a
        ((d + 1) + r) w := by
  induction r with
  | zero =>
      exact rate_subtreeSwap_zero v x a w
  | succ r ih =>
      let z := (childrenEquiv ((d + 1) + r)).symm w
      have hz : childrenEquiv ((d + 1) + r) z = w :=
        (childrenEquiv ((d + 1) + r)).apply_symm_apply w
      rw [← hz]
      rcases z with ⟨u, side⟩
      have hparent := ih (by omega) u
      have hleft :=
        aggregate_count_subtreeSwap v x (r := r + 1)
          (by omega) (leftChild u)
      have hright :=
        aggregate_count_subtreeSwap v x (r := r + 1)
          (by omega) (rightChild u)
      have hleft' :
          (Dynamics.aggregatedInventory
              (inventoryPerm (subtreeSwap v n) x)).count
              (((d + 1) + r) + 1)
              (leftChild (subtreeSwap v r u)) =
            (Dynamics.aggregatedInventory x).count
              (((d + 1) + r) + 1) (leftChild u) := by
        rw [← subtreeSwap_succ_leftChild v u]
        exact hleft
      have hright' :
          (Dynamics.aggregatedInventory
              (inventoryPerm (subtreeSwap v n) x)).count
              (((d + 1) + r) + 1)
              (rightChild (subtreeSwap v r u)) =
            (Dynamics.aggregatedInventory x).count
              (((d + 1) + r) + 1) (rightChild u) := by
        rw [← subtreeSwap_succ_rightChild v u]
        exact hright
      fin_cases side
      · change
          TreePolicy.rate
              (Dynamics.aggregatedInventory
                (inventoryPerm (subtreeSwap v n) x)) a
              (((d + 1) + r) + 1)
              (subtreeSwap v (r + 1) (leftChild u)) =
            TreePolicy.rate (Dynamics.aggregatedInventory x) a
              (((d + 1) + r) + 1) (leftChild u)
        rw [subtreeSwap_succ_leftChild,
          TreePolicy.rate_leftChild, TreePolicy.rate_leftChild, hparent]
        rw [hleft', hright']
        simp [TreePolicy.intervalMass, nodeMass]
      · change
          TreePolicy.rate
              (Dynamics.aggregatedInventory
                (inventoryPerm (subtreeSwap v n) x)) a
              (((d + 1) + r) + 1)
              (subtreeSwap v (r + 1) (rightChild u)) =
            TreePolicy.rate (Dynamics.aggregatedInventory x) a
              (((d + 1) + r) + 1) (rightChild u)
        rw [subtreeSwap_succ_rightChild,
          TreePolicy.rate_rightChild, TreePolicy.rate_rightChild, hparent]
        rw [hleft', hright']
        simp [TreePolicy.intervalMass, nodeMass]

/-- Deletion masses at and above the swapped node are unchanged. -/
theorem deletionMass_aboveSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {k : ℕ} (hkd : k ≤ d) (w : DyadicNode k) :
    TreePolicy.deletionMass
        (Dynamics.aggregatedInventory
          (inventoryPerm (subtreeSwap v n) x)) a k w =
      TreePolicy.deletionMass
        (Dynamics.aggregatedInventory x) a k w := by
  unfold TreePolicy.deletionMass TreePolicy.inventory
  rw [aggregate_count_aboveSwap v x hkd w,
    rate_aboveSwap v x a hkd w]

/-- Deletion masses at descendants are transported by the subtree swap. -/
theorem deletionMass_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {r : ℕ} (hrn : r ≤ n)
    (w : DyadicNode ((d + 1) + r)) :
    TreePolicy.deletionMass
        (Dynamics.aggregatedInventory
          (inventoryPerm (subtreeSwap v n) x)) a
        ((d + 1) + r) (subtreeSwap v r w) =
      TreePolicy.deletionMass (Dynamics.aggregatedInventory x) a
        ((d + 1) + r) w := by
  unfold TreePolicy.deletionMass TreePolicy.inventory
  rw [aggregate_count_subtreeSwap v x hrn w,
    rate_subtreeSwap v x a hrn w]

/-- The fixed-label deletion imbalance at the swapped node changes sign. -/
theorem imbalance_swapNode
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) :
    TreePolicy.imbalance
        (Dynamics.aggregatedInventory
          (inventoryPerm (subtreeSwap v n) x)) a d v =
      -TreePolicy.imbalance (Dynamics.aggregatedInventory x) a d v := by
  have hleft :=
    deletionMass_subtreeSwap v x a (r := 0) (by omega)
      (leftChild v)
  have hright :=
    deletionMass_subtreeSwap v x a (r := 0) (by omega)
      (rightChild v)
  simp only [subtreeSwap_zero_left] at hleft
  simp only [subtreeSwap_zero_right] at hright
  unfold TreePolicy.imbalance
  rw [hleft, hright]
  ring

/-- A strict ancestor's deletion imbalance is unchanged. -/
theorem imbalance_strictAncestor
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {k : ℕ} (hkd : k < d) (w : DyadicNode k) :
    TreePolicy.imbalance
        (Dynamics.aggregatedInventory
          (inventoryPerm (subtreeSwap v n) x)) a k w =
      TreePolicy.imbalance (Dynamics.aggregatedInventory x) a k w := by
  unfold TreePolicy.imbalance
  rw [deletionMass_aboveSwap v x a (by omega) (leftChild w),
    deletionMass_aboveSwap v x a (by omega) (rightChild w)]

/-! ## Arbitrary-depth wrappers -/

theorem deletionMass_leafSwapWithGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    (w : DyadicNode L) :
    TreePolicy.deletionMass
        (Dynamics.aggregatedInventory
          (inventorySwapWithGap v r hlevel x)) a L
        (leafSwapWithGap v r hlevel w) =
      TreePolicy.deletionMass (Dynamics.aggregatedInventory x) a L w := by
  subst L
  exact deletionMass_subtreeSwap v x a le_rfl w

theorem imbalance_swapNodeWithGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (x : InventoryState (DyadicNode L) m) (a : ℝ) :
    TreePolicy.imbalance
        (Dynamics.aggregatedInventory
          (inventorySwapWithGap v r hlevel x)) a d v =
      -TreePolicy.imbalance (Dynamics.aggregatedInventory x) a d v := by
  subst L
  exact imbalance_swapNode v x a

theorem imbalance_strictAncestorWithGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    {k : ℕ} (hkd : k < d) (w : DyadicNode k) :
    TreePolicy.imbalance
        (Dynamics.aggregatedInventory
          (inventorySwapWithGap v r hlevel x)) a k w =
      TreePolicy.imbalance (Dynamics.aggregatedInventory x) a k w := by
  subst L
  exact imbalance_strictAncestor v x a hkd w

theorem deletionMass_leafSwap
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    (w : DyadicNode L) :
    TreePolicy.deletionMass
        (Dynamics.aggregatedInventory
          (inventorySwap hdL v x)) a L
        (leafSwap hdL v w) =
      TreePolicy.deletionMass (Dynamics.aggregatedInventory x) a L w :=
  deletionMass_leafSwapWithGap
    v (L - (d + 1)) (by omega) x a w

theorem imbalance_swapNode_general
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (a : ℝ) :
    TreePolicy.imbalance
        (Dynamics.aggregatedInventory (inventorySwap hdL v x)) a d v =
      -TreePolicy.imbalance (Dynamics.aggregatedInventory x) a d v :=
  imbalance_swapNodeWithGap
    v (L - (d + 1)) (by omega) x a

theorem imbalance_strictAncestor_general
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    {k : ℕ} (hkd : k < d) (w : DyadicNode k) :
    TreePolicy.imbalance
        (Dynamics.aggregatedInventory (inventorySwap hdL v x)) a k w =
      TreePolicy.imbalance (Dynamics.aggregatedInventory x) a k w :=
  imbalance_strictAncestorWithGap
    v (L - (d + 1)) (by omega) x a hkd w

/-! ## Kernel equivariance and invariant stationary laws -/

theorem deletionRule_prob_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (w : DyadicNode ((d + 1) + n)) :
    (Dynamics.deletionRule a ha hm).prob
        (inventoryPerm (subtreeSwap v n) x) (subtreeSwap v n w) =
      (Dynamics.deletionRule a ha hm).prob x w := by
  change
    TreePolicy.deletionMass
        (Dynamics.aggregatedInventory
          (inventoryPerm (subtreeSwap v n) x)) a ((d + 1) + n)
          (subtreeSwap v n w) =
      TreePolicy.deletionMass
        (Dynamics.aggregatedInventory x) a ((d + 1) + n) w
  exact deletionMass_subtreeSwap v x a le_rfl w

theorem kernel_equivariant_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (Dynamics.kernel
        (L := (d + 1) + n) (m := m) a ha hm).Equivariant
      (inventoryPerm (subtreeSwap v n)) := by
  exact FD1D.TreeSymmetry.deletionKernel_equivariant
    (Dynamics.deletionRule a ha hm)
    (subtreeSwap v n)
    (deletionRule_prob_subtreeSwap v a ha hm)

theorem kernel_equivariant_withGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (Dynamics.kernel (L := L) (m := m) a ha hm).Equivariant
      (inventorySwapWithGap v r hlevel) := by
  subst L
  exact kernel_equivariant_subtreeSwap v a ha hm

theorem kernel_equivariant
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (Dynamics.kernel (L := L) (m := m) a ha hm).Equivariant
      (inventorySwap hdL v) :=
  kernel_equivariant_withGap
    v (L - (d + 1)) (by omega) a ha hm

theorem stationary_lawInvariant
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    {μ : FiniteLaw (InventoryState (DyadicNode L) m)}
    (hμ : (Dynamics.kernel (L := L) (m := m) a ha hm).IsStationary μ) :
    FiniteKernel.LawInvariant μ (inventorySwap hdL v) :=
  FD1D.TreeSymmetry.stationary_lawInvariant_of_irreducible
    (Dynamics.kernel_irreducible a ha hm)
    (kernel_equivariant hdL v a ha hm) hμ

end

end FD1D.V5.TreeSymmetry
