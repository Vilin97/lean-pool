/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Dynamics

/-! # Symmetry -/

namespace FD1D

noncomputable section

open scoped BigOperators

/-!
# Local child-swap symmetries

A swap at a depth-`d` node exchanges its two child subtrees.  The
permutation is propagated to deeper levels by preserving every subsequent
left/right choice.  This file also lifts the permutations to inventory
states and records the equivariance of the hierarchical policy.
-/

namespace TreeSymmetry

/-- Lift a permutation of one tree level to the next level, preserving the
left/right choice below every permuted node. -/
def liftNodePerm {k : ℕ} (e : Equiv.Perm (DyadicNode k)) :
    Equiv.Perm (DyadicNode (k + 1)) :=
  (childrenEquiv k).symm.trans
    ((e.prodCongr (Equiv.refl (Fin 2))).trans (childrenEquiv k))

@[simp] theorem liftNodePerm_leftChild {k : ℕ}
    (e : Equiv.Perm (DyadicNode k)) (w : DyadicNode k) :
    liftNodePerm e (leftChild w) = leftChild (e w) := by
  simp [liftNodePerm, leftChild]

@[simp] theorem liftNodePerm_rightChild {k : ℕ}
    (e : Equiv.Perm (DyadicNode k)) (w : DyadicNode k) :
    liftNodePerm e (rightChild w) = rightChild (e w) := by
  simp [liftNodePerm, rightChild]

/-- The permutation at level `d+1+r` induced by swapping the children of
`v`. -/
def subtreeSwap {d : ℕ} (v : DyadicNode d) :
    (r : ℕ) → Equiv.Perm (DyadicNode ((d + 1) + r))
  | 0 => Equiv.swap (leftChild v) (rightChild v)
  | r + 1 => liftNodePerm (subtreeSwap v r)

@[simp] theorem subtreeSwap_zero_left {d : ℕ} (v : DyadicNode d) :
    subtreeSwap v 0 (leftChild v) = rightChild v :=
  Equiv.swap_apply_left _ _

@[simp] theorem subtreeSwap_zero_right {d : ℕ} (v : DyadicNode d) :
    subtreeSwap v 0 (rightChild v) = leftChild v :=
  Equiv.swap_apply_right _ _

theorem subtreeSwap_zero_of_ne {d : ℕ} (v : DyadicNode d)
    {w : DyadicNode (d + 1)}
    (hleft : w ≠ leftChild v) (hright : w ≠ rightChild v) :
    subtreeSwap v 0 w = w :=
  Equiv.swap_apply_of_ne_of_ne hleft hright

@[simp] theorem subtreeSwap_succ_leftChild {d r : ℕ}
    (v : DyadicNode d) (w : DyadicNode ((d + 1) + r)) :
    subtreeSwap v (r + 1) (leftChild w) =
      leftChild (subtreeSwap v r w) := by
  simp [subtreeSwap]

@[simp] theorem subtreeSwap_succ_rightChild {d r : ℕ}
    (v : DyadicNode d) (w : DyadicNode ((d + 1) + r)) :
    subtreeSwap v (r + 1) (rightChild w) =
      rightChild (subtreeSwap v r w) := by
  simp [subtreeSwap]

theorem liftNodePerm_involutive {k : ℕ}
    (e : Equiv.Perm (DyadicNode k))
    (he : ∀ w, e (e w) = w) :
    ∀ w, liftNodePerm e (liftNodePerm e w) = w := by
  intro w
  let z := (childrenEquiv k).symm w
  have hz : childrenEquiv k z = w :=
    (childrenEquiv k).apply_symm_apply w
  rw [← hz]
  rcases z with ⟨u, side⟩
  simp only [liftNodePerm, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.symm_apply_apply]
  change childrenEquiv k (e (e u), side) = childrenEquiv k (u, side)
  rw [he]

@[simp] theorem subtreeSwap_involutive {d r : ℕ}
    (v : DyadicNode d) (w : DyadicNode ((d + 1) + r)) :
    subtreeSwap v r (subtreeSwap v r w) = w := by
  induction r with
  | zero =>
      exact Equiv.swap_apply_self _ _ _
  | succ r ih =>
      exact liftNodePerm_involutive (subtreeSwap v r) ih w

theorem subtreeSwap_symm {d r : ℕ} (v : DyadicNode d) :
    (subtreeSwap v r).symm = subtreeSwap v r := by
  apply Equiv.ext
  intro w
  apply (subtreeSwap v r).injective
  simp

/-- The ancestor `r` levels above a node. -/
def ancestorNode {k : ℕ} : (r : ℕ) → DyadicNode (k + r) → DyadicNode k
  | 0, w => w
  | r + 1, w => ancestorNode r (parent w)

@[simp] theorem ancestorNode_zero {k : ℕ} (w : DyadicNode k) :
    ancestorNode 0 w = w :=
  rfl

@[simp] theorem ancestorNode_succ_leftChild {k r : ℕ}
    (w : DyadicNode (k + r)) :
    ancestorNode (r + 1) (leftChild w) = ancestorNode r w := by
  simp [ancestorNode]

@[simp] theorem ancestorNode_succ_rightChild {k r : ℕ}
    (w : DyadicNode (k + r)) :
    ancestorNode (r + 1) (rightChild w) = ancestorNode r w := by
  simp [ancestorNode]

/-- A node outside the two exchanged descendant blocks is fixed pointwise. -/
theorem subtreeSwap_fixed_of_ancestor_ne
    {d r : ℕ} (v : DyadicNode d)
    (w : DyadicNode ((d + 1) + r))
    (hleft : ancestorNode r w ≠ leftChild v)
    (hright : ancestorNode r w ≠ rightChild v) :
    subtreeSwap v r w = w := by
  induction r with
  | zero =>
      exact subtreeSwap_zero_of_ne v hleft hright
  | succ r ih =>
      let z := (childrenEquiv ((d + 1) + r)).symm w
      have hz : childrenEquiv ((d + 1) + r) z = w :=
        (childrenEquiv ((d + 1) + r)).apply_symm_apply w
      rw [← hz] at hleft hright ⊢
      rcases z with ⟨u, side⟩
      fin_cases side
      · change subtreeSwap v (r + 1) (leftChild u) = leftChild u
        change ancestorNode (r + 1) (leftChild u) ≠ leftChild v at hleft
        change ancestorNode (r + 1) (leftChild u) ≠ rightChild v at hright
        simp only [ancestorNode_succ_leftChild] at hleft hright
        rw [subtreeSwap_succ_leftChild, ih u hleft hright]
      · change subtreeSwap v (r + 1) (rightChild u) = rightChild u
        change ancestorNode (r + 1) (rightChild u) ≠ leftChild v at hleft
        change ancestorNode (r + 1) (rightChild u) ≠ rightChild v at hright
        simp only [ancestorNode_succ_rightChild] at hleft hright
        rw [subtreeSwap_succ_rightChild, ih u hleft hright]

theorem conjugate_involutive
    {α β : Type*} (c : α ≃ β) (e : Equiv.Perm α)
    (he : ∀ x, e (e x) = x) (y : β) :
    (c.symm.trans (e.trans c))
        ((c.symm.trans (e.trans c)) y) = y := by
  simp only [Equiv.trans_apply, c.symm_apply_apply]
  rw [he]
  simp

/-! ## Relabeling finite inventories -/

instance inventoryStateNonempty
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ} :
    Nonempty (InventoryState ι m) :=
  ⟨⟨fun i => if i = Classical.arbitrary ι then m else 0, by simp⟩⟩

/-- Push a fixed-total count vector forward along a permutation. -/
def inventoryPerm {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : Equiv.Perm ι) : Equiv.Perm (InventoryState ι m) where
  toFun x :=
    ⟨fun i => x.1 (e.symm i), by
      calc
        ∑ i, x.1 (e.symm i) = ∑ i, x.1 i :=
          Equiv.sum_comp e.symm x.1
        _ = m := x.2⟩
  invFun x :=
    ⟨fun i => x.1 (e i), by
      calc
        ∑ i, x.1 (e i) = ∑ i, x.1 i :=
          Equiv.sum_comp e x.1
        _ = m := x.2⟩
  left_inv x := by
    apply InventoryState.ext
    intro i
    simp
  right_inv x := by
    apply InventoryState.ext
    intro i
    simp

@[simp] theorem inventoryPerm_apply_count
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : Equiv.Perm ι) (x : InventoryState ι m) (i : ι) :
    (inventoryPerm e x).1 i = x.1 (e.symm i) :=
  rfl

theorem inventoryPerm_apply_image_count
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : Equiv.Perm ι) (x : InventoryState ι m) (i : ι) :
    (inventoryPerm e x).1 (e i) = x.1 i := by
  simp [inventoryPerm]

/-- Transport an explicitly iterated subtree swap to a named leaf depth. -/
def leafSwapWithGap {d L : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L) : Equiv.Perm (DyadicNode L) :=
  let c : DyadicNode ((d + 1) + r) ≃ DyadicNode L :=
    Equiv.cast (congrArg DyadicNode hlevel)
  c.symm.trans ((subtreeSwap v r).trans c)

/-- The involution of depth-`L` leaves induced by a child swap at `v`. -/
def leafSwap {d L : ℕ} (hdL : d < L) (v : DyadicNode d) :
    Equiv.Perm (DyadicNode L) :=
  leafSwapWithGap v (L - (d + 1)) (by omega)

/-- The child swap lifted to fixed-total leaf inventories. -/
def inventorySwap {d L m : ℕ} (hdL : d < L) (v : DyadicNode d) :
    Equiv.Perm (InventoryState (DyadicNode L) m) :=
  inventoryPerm (leafSwap hdL v)

/-- The lifted inventory swap with an explicit depth gap. -/
def inventorySwapWithGap {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L) :
    Equiv.Perm (InventoryState (DyadicNode L) m) :=
  inventoryPerm (leafSwapWithGap v r hlevel)

@[simp] theorem leafSwap_involutive {d L : ℕ} (hdL : d < L)
    (v : DyadicNode d) (w : DyadicNode L) :
    leafSwap hdL v (leafSwap hdL v w) = w := by
  unfold leafSwap
  unfold leafSwapWithGap
  exact conjugate_involutive _ _ (subtreeSwap_involutive v) w

theorem leafSwap_symm {d L : ℕ} (hdL : d < L) (v : DyadicNode d) :
    (leafSwap hdL v).symm = leafSwap hdL v := by
  apply Equiv.ext
  intro w
  apply (leafSwap hdL v).injective
  simp

@[simp] theorem leafSwapWithGap_rfl {d n : ℕ} (v : DyadicNode d) :
    leafSwapWithGap v n rfl = subtreeSwap v n := by
  rfl

@[simp] theorem inventorySwapWithGap_rfl {d n m : ℕ}
    (v : DyadicNode d) :
    (inventorySwapWithGap v n rfl :
      Equiv.Perm (InventoryState (DyadicNode ((d + 1) + n)) m)) =
        inventoryPerm (subtreeSwap v n) := by
  rfl

@[simp] theorem inventorySwap_apply_image_count
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (inventorySwap hdL v x).1 (leafSwap hdL v w) = x.1 w :=
  inventoryPerm_apply_image_count _ _ _

/-! ## Canonical aggregate counts under a swap -/

/-- Regard a fixed-total state as a leaf inventory. -/
def stateLeafInventory {L m : ℕ}
    (x : InventoryState (DyadicNode L) m) : LeafInventory L m where
  count := x.1
  total_count := x.2

/-- The canonical aggregate counts of a fixed-total state. -/
def stateAggregate {L m : ℕ}
    (x : InventoryState (DyadicNode L) m) : AggregatedInventory L m :=
  (stateLeafInventory x).aggregate

theorem stateAggregate_leaf_count {L m : ℕ}
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (stateAggregate x).count L w = x.1 w := by
  change ((stateLeafInventory x).aggregate).count L w = x.1 w
  rw [(stateLeafInventory x).aggregate.count_leaf]
  rfl

/-- The inventory consisting of one item at `w`. -/
def singletonInventoryState {L : ℕ} (w : DyadicNode L) :
    InventoryState (DyadicNode L) 1 where
  val z := if z = w then 1 else 0
  property := by simp

@[simp] theorem inventoryPerm_singleton
    {L : ℕ} (e : Equiv.Perm (DyadicNode L)) (w : DyadicNode L) :
    inventoryPerm e (singletonInventoryState w) =
      singletonInventoryState (e w) := by
  apply InventoryState.ext
  intro z
  simp [singletonInventoryState, inventoryPerm, Equiv.symm_apply_eq]

theorem stateAggregate_singleton_count
    {L k : ℕ} (w : DyadicNode L) (hkL : k ≤ L)
    (u : DyadicNode k) :
    (stateAggregate (singletonInventoryState w)).count k u =
      if w ∈ leafBlock hkL u then 1 else 0 := by
  simp [stateAggregate, stateLeafInventory, LeafInventory.aggregate,
    LeafInventory.nodeCount, hkL, singletonInventoryState]

/--
Below the swapped children, canonical aggregate counts are carried to the
corresponding node by `subtreeSwap`.
-/
theorem stateAggregate_count_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    {r : ℕ} (hrn : r ≤ n) (w : DyadicNode ((d + 1) + r)) :
    (stateAggregate (inventoryPerm (subtreeSwap v n) x)).count
        ((d + 1) + r) (subtreeSwap v r w) =
      (stateAggregate x).count ((d + 1) + r) w := by
  induction hgap : n - r using Nat.strong_induction_on generalizing r with
  | h gap ih =>
      by_cases hre : r = n
      · subst r
        simp
      · have hrlt : r < n := lt_of_le_of_ne hrn hre
        have hlevel :
            (d + 1) + r < (d + 1) + n := by omega
        rw [(stateAggregate
              (inventoryPerm (subtreeSwap v n) x)).count_children
              ((d + 1) + r) hlevel (subtreeSwap v r w)]
        rw [← subtreeSwap_succ_leftChild v w,
          ← subtreeSwap_succ_rightChild v w]
        have hgap' : n - (r + 1) < gap := by omega
        have ihleft :=
          ih (n - (r + 1)) hgap' (r := r + 1) (by omega)
            (leftChild w) rfl
        have ihrigh :=
          ih (n - (r + 1)) hgap' (r := r + 1) (by omega)
            (rightChild w) rfl
        erw [ihleft, ihrigh]
        exact
          ((stateAggregate x).count_children
            ((d + 1) + r) hlevel w).symm

/-- Counts at the level of the swapped node itself are unchanged. -/
theorem stateAggregate_count_swapLevel
    {d n m : ℕ} (v w : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m) :
    (stateAggregate (inventoryPerm (subtreeSwap v n) x)).count d w =
      (stateAggregate x).count d w := by
  let I' := stateAggregate (inventoryPerm (subtreeSwap v n) x)
  let I := stateAggregate x
  have hdL : d < (d + 1) + n := by omega
  rw [I'.count_children d hdL w, I.count_children d hdL w]
  by_cases hwv : w = v
  · subst w
    have hleft :=
      stateAggregate_count_subtreeSwap v x (r := 0) (by omega)
        (leftChild v)
    have hright :=
      stateAggregate_count_subtreeSwap v x (r := 0) (by omega)
        (rightChild v)
    have hleft' :
        I'.count (d + 1) (rightChild v) =
          I.count (d + 1) (leftChild v) := by
      simpa [I', I] using hleft
    have hright' :
        I'.count (d + 1) (leftChild v) =
          I.count (d + 1) (rightChild v) := by
      simpa [I', I] using hright
    rw [hleft', hright']
    omega
  · have hll : leftChild w ≠ leftChild v := by
      intro h
      apply hwv
      simpa using congrArg parent h
    have hlr : leftChild w ≠ rightChild v := by
      intro h
      apply hwv
      simpa using congrArg parent h
    have hrl : rightChild w ≠ leftChild v := by
      intro h
      apply hwv
      simpa using congrArg parent h
    have hrr : rightChild w ≠ rightChild v := by
      intro h
      apply hwv
      simpa using congrArg parent h
    have hleft :=
      stateAggregate_count_subtreeSwap v x (r := 0) (by omega)
        (leftChild w)
    have hright :=
      stateAggregate_count_subtreeSwap v x (r := 0) (by omega)
        (rightChild w)
    rw [subtreeSwap_zero_of_ne v hll hlr] at hleft
    rw [subtreeSwap_zero_of_ne v hrl hrr] at hright
    have hleft' :
        I'.count (d + 1) (leftChild w) =
          I.count (d + 1) (leftChild w) := by
      simpa [I', I] using hleft
    have hright' :
        I'.count (d + 1) (rightChild w) =
          I.count (d + 1) (rightChild w) := by
      simpa [I', I] using hright
    rw [hleft', hright']

/-- Every count at or above the swapped node's depth is unchanged. -/
theorem stateAggregate_count_aboveSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    {k : ℕ} (hkd : k ≤ d) (w : DyadicNode k) :
    (stateAggregate (inventoryPerm (subtreeSwap v n) x)).count k w =
      (stateAggregate x).count k w := by
  induction hgap : d - k using Nat.strong_induction_on generalizing k with
  | h gap ih =>
      by_cases hkeq : k = d
      · subst k
        exact stateAggregate_count_swapLevel v w x
      · have hklt : k < d := lt_of_le_of_ne hkd hkeq
        have hkL : k < (d + 1) + n := by omega
        rw [(stateAggregate
              (inventoryPerm (subtreeSwap v n) x)).count_children
              k hkL w,
            (stateAggregate x).count_children k hkL w]
        have hgap' : d - (k + 1) < gap := by omega
        rw [ih (d - (k + 1)) hgap' (k := k + 1) (by omega)
              (leftChild w) rfl,
            ih (d - (k + 1)) hgap' (k := k + 1) (by omega)
              (rightChild w) rfl]

/-! ## Action on descendant blocks -/

theorem mem_leafBlock_subtreeSwap_iff
    {d n s : ℕ} (v : DyadicNode d) (hsn : s ≤ n)
    (u : DyadicNode ((d + 1) + s))
    (w : DyadicNode ((d + 1) + n)) :
    subtreeSwap v n w ∈
        leafBlock (show (d + 1) + s ≤ (d + 1) + n by omega)
          (subtreeSwap v s u) ↔
      w ∈ leafBlock (show (d + 1) + s ≤ (d + 1) + n by omega) u := by
  have hcount :=
    stateAggregate_count_subtreeSwap v (singletonInventoryState w)
      hsn u
  rw [inventoryPerm_singleton] at hcount
  rw [stateAggregate_singleton_count
        (subtreeSwap v n w) (by omega) (subtreeSwap v s u),
      stateAggregate_singleton_count w (by omega) u] at hcount
  by_cases hleft :
      subtreeSwap v n w ∈
        leafBlock (show (d + 1) + s ≤ (d + 1) + n by omega)
          (subtreeSwap v s u) <;>
    by_cases hright :
      w ∈ leafBlock (show (d + 1) + s ≤ (d + 1) + n by omega) u <;>
    simp_all

theorem leafSwap_exchanges_leftBlock
    {d n : ℕ} (v : DyadicNode d)
    (w : DyadicNode ((d + 1) + n)) :
    subtreeSwap v n w ∈
        leafBlock (show d + 1 ≤ (d + 1) + n by omega) (rightChild v) ↔
      w ∈ leafBlock (show d + 1 ≤ (d + 1) + n by omega) (leftChild v) := by
  simpa using
    (mem_leafBlock_subtreeSwap_iff v (s := 0) (by omega)
      (leftChild v) w)

theorem leafSwap_exchanges_rightBlock
    {d n : ℕ} (v : DyadicNode d)
    (w : DyadicNode ((d + 1) + n)) :
    subtreeSwap v n w ∈
        leafBlock (show d + 1 ≤ (d + 1) + n by omega) (leftChild v) ↔
      w ∈ leafBlock (show d + 1 ≤ (d + 1) + n by omega) (rightChild v) := by
  simpa using
    (mem_leafBlock_subtreeSwap_iff v (s := 0) (by omega)
      (rightChild v) w)

theorem leafSwap_preserves_otherBlock
    {d n : ℕ} (v : DyadicNode d) (u : DyadicNode (d + 1))
    (hleft : u ≠ leftChild v) (hright : u ≠ rightChild v)
    (w : DyadicNode ((d + 1) + n)) :
    subtreeSwap v n w ∈
        leafBlock (show d + 1 ≤ (d + 1) + n by omega) u ↔
      w ∈ leafBlock (show d + 1 ≤ (d + 1) + n by omega) u := by
  simpa [subtreeSwap_zero_of_ne v hleft hright] using
    (mem_leafBlock_subtreeSwap_iff v (s := 0) (by omega) u w)

theorem leafSwapWithGap_exchanges_leftBlock
    {d L : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L) (w : DyadicNode L) :
    leafSwapWithGap v r hlevel w ∈
        leafBlock (show d + 1 ≤ L by omega) (rightChild v) ↔
      w ∈ leafBlock (show d + 1 ≤ L by omega) (leftChild v) := by
  subst L
  exact leafSwap_exchanges_leftBlock v w

theorem leafSwapWithGap_exchanges_rightBlock
    {d L : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L) (w : DyadicNode L) :
    leafSwapWithGap v r hlevel w ∈
        leafBlock (show d + 1 ≤ L by omega) (leftChild v) ↔
      w ∈ leafBlock (show d + 1 ≤ L by omega) (rightChild v) := by
  subst L
  exact leafSwap_exchanges_rightBlock v w

theorem leafSwapWithGap_preserves_otherBlock
    {d L : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (u : DyadicNode (d + 1))
    (hleft : u ≠ leftChild v) (hright : u ≠ rightChild v)
    (w : DyadicNode L) :
    leafSwapWithGap v r hlevel w ∈
        leafBlock (show d + 1 ≤ L by omega) u ↔
      w ∈ leafBlock (show d + 1 ≤ L by omega) u := by
  subst L
  exact leafSwap_preserves_otherBlock v u hleft hright w

theorem leafSwap_exchanges_leftBlock_general
    {d L : ℕ} (hdL : d < L) (v : DyadicNode d) (w : DyadicNode L) :
    leafSwap hdL v w ∈
        leafBlock (show d + 1 ≤ L by omega) (rightChild v) ↔
      w ∈ leafBlock (show d + 1 ≤ L by omega) (leftChild v) :=
  leafSwapWithGap_exchanges_leftBlock
    v (L - (d + 1)) (by omega) w

theorem leafSwap_exchanges_rightBlock_general
    {d L : ℕ} (hdL : d < L) (v : DyadicNode d) (w : DyadicNode L) :
    leafSwap hdL v w ∈
        leafBlock (show d + 1 ≤ L by omega) (leftChild v) ↔
      w ∈ leafBlock (show d + 1 ≤ L by omega) (rightChild v) :=
  leafSwapWithGap_exchanges_rightBlock
    v (L - (d + 1)) (by omega) w

theorem leafSwap_preserves_otherBlock_general
    {d L : ℕ} (hdL : d < L) (v : DyadicNode d)
    (u : DyadicNode (d + 1))
    (hleft : u ≠ leftChild v) (hright : u ≠ rightChild v)
    (w : DyadicNode L) :
    leafSwap hdL v w ∈ leafBlock (show d + 1 ≤ L by omega) u ↔
      w ∈ leafBlock (show d + 1 ≤ L by omega) u :=
  leafSwapWithGap_preserves_otherBlock
    v (L - (d + 1)) (by omega) u hleft hright w

/-! ## Equivariance of the hierarchical policy -/

open LocalHazard

theorem hL_swap_counts (a h : ℝ) (x y : ℕ) :
    hL a h y x = hR a h x y := by
  by_cases hxy : x + y = 0
  · have hyx : y + x = 0 := by omega
    simp [hL, hR, hxy, hyx]
  · have hyx : y + x ≠ 0 := by omega
    simp only [hL, hR, ite_eq_right hxy, ite_eq_right hyx]
    unfold D N
    ring

theorem hR_swap_counts (a h : ℝ) (x y : ℕ) :
    hR a h y x = hL a h x y := by
  by_cases hxy : x + y = 0
  · have hyx : y + x = 0 := by omega
    simp [hL, hR, hxy, hyx]
  · have hyx : y + x ≠ 0 := by omega
    simp only [hL, hR, ite_eq_right hxy, ite_eq_right hyx]
    unfold D N
    ring

/-- Hazards at every level weakly above the swapped node are unchanged. -/
theorem policy_hazard_aboveSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {k : ℕ} (hkd : k ≤ d) (w : DyadicNode k) :
    HierarchicalPolicy.hazard
        (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a k w =
      HierarchicalPolicy.hazard (stateAggregate x) a k w := by
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
        stateAggregate_count_aboveSwap v x (k := k + 1)
          (by omega) (leftChild u)
      have hright :=
        stateAggregate_count_aboveSwap v x (k := k + 1)
          (by omega) (rightChild u)
      fin_cases side
      · change
          HierarchicalPolicy.hazard
              (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a
              (k + 1) (leftChild u) =
            HierarchicalPolicy.hazard (stateAggregate x) a
              (k + 1) (leftChild u)
        rw [HierarchicalPolicy.hazard_leftChild,
          HierarchicalPolicy.hazard_leftChild, hparent, hleft, hright]
      · change
          HierarchicalPolicy.hazard
              (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a
              (k + 1) (rightChild u) =
            HierarchicalPolicy.hazard (stateAggregate x) a
              (k + 1) (rightChild u)
        rw [HierarchicalPolicy.hazard_rightChild,
          HierarchicalPolicy.hazard_rightChild, hparent, hleft, hright]

/-- At the first level below `v`, hazards follow the child swap. -/
theorem policy_hazard_subtreeSwap_zero
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) (w : DyadicNode (d + 1)) :
    HierarchicalPolicy.hazard
        (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a
        (d + 1) (subtreeSwap v 0 w) =
      HierarchicalPolicy.hazard (stateAggregate x) a (d + 1) w := by
  let I' := stateAggregate (inventoryPerm (subtreeSwap v n) x)
  let I := stateAggregate x
  let z := (childrenEquiv d).symm w
  have hz : childrenEquiv d z = w :=
    (childrenEquiv d).apply_symm_apply w
  rw [← hz]
  rcases z with ⟨u, side⟩
  have hparent :
      HierarchicalPolicy.hazard I' a d u =
        HierarchicalPolicy.hazard I a d u := by
    exact policy_hazard_aboveSwap v x a (le_refl d) u
  by_cases huv : u = v
  · subst u
    have hleft :=
      stateAggregate_count_subtreeSwap v x (r := 0) (by omega)
        (leftChild v)
    have hright :=
      stateAggregate_count_subtreeSwap v x (r := 0) (by omega)
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
        HierarchicalPolicy.hazard I' a (d + 1)
            (subtreeSwap v 0 (leftChild v)) =
          HierarchicalPolicy.hazard I a (d + 1) (leftChild v)
      rw [subtreeSwap_zero_left]
      rw [HierarchicalPolicy.hazard_rightChild,
        HierarchicalPolicy.hazard_leftChild, hparent, hleft', hright']
      exact hR_swap_counts a
        (HierarchicalPolicy.hazard I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v))
    · change
        HierarchicalPolicy.hazard I' a (d + 1)
            (subtreeSwap v 0 (rightChild v)) =
          HierarchicalPolicy.hazard I a (d + 1) (rightChild v)
      rw [subtreeSwap_zero_right]
      rw [HierarchicalPolicy.hazard_leftChild,
        HierarchicalPolicy.hazard_rightChild, hparent, hleft', hright']
      exact hL_swap_counts a
        (HierarchicalPolicy.hazard I a d v)
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
      stateAggregate_count_subtreeSwap v x (r := 0) (by omega)
        (leftChild u)
    have hright :=
      stateAggregate_count_subtreeSwap v x (r := 0) (by omega)
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
        HierarchicalPolicy.hazard I' a (d + 1)
            (subtreeSwap v 0 (leftChild u)) =
          HierarchicalPolicy.hazard I a (d + 1) (leftChild u)
      rw [subtreeSwap_zero_of_ne v hll hlr,
        HierarchicalPolicy.hazard_leftChild,
        HierarchicalPolicy.hazard_leftChild, hparent, hleft', hright']
    · change
        HierarchicalPolicy.hazard I' a (d + 1)
            (subtreeSwap v 0 (rightChild u)) =
          HierarchicalPolicy.hazard I a (d + 1) (rightChild u)
      rw [subtreeSwap_zero_of_ne v hrl hrr,
        HierarchicalPolicy.hazard_rightChild,
        HierarchicalPolicy.hazard_rightChild, hparent, hleft', hright']

/-- Hazards at every descendant node are transported by the tree swap. -/
theorem policy_hazard_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {r : ℕ} (hrn : r ≤ n)
    (w : DyadicNode ((d + 1) + r)) :
    HierarchicalPolicy.hazard
        (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a
        ((d + 1) + r) (subtreeSwap v r w) =
      HierarchicalPolicy.hazard (stateAggregate x) a
        ((d + 1) + r) w := by
  induction r with
  | zero =>
      exact policy_hazard_subtreeSwap_zero v x a w
  | succ r ih =>
      let z := (childrenEquiv ((d + 1) + r)).symm w
      have hz : childrenEquiv ((d + 1) + r) z = w :=
        (childrenEquiv ((d + 1) + r)).apply_symm_apply w
      rw [← hz]
      rcases z with ⟨u, side⟩
      have hparent := ih (by omega) u
      have hleft :=
        stateAggregate_count_subtreeSwap v x (r := r + 1)
          (by omega) (leftChild u)
      have hright :=
        stateAggregate_count_subtreeSwap v x (r := r + 1)
          (by omega) (rightChild u)
      have hleft' :
          (stateAggregate
              (inventoryPerm (subtreeSwap v n) x)).count
              (((d + 1) + r) + 1)
              (leftChild (subtreeSwap v r u)) =
            (stateAggregate x).count (((d + 1) + r) + 1)
              (leftChild u) := by
        rw [← subtreeSwap_succ_leftChild v u]
        exact hleft
      have hright' :
          (stateAggregate
              (inventoryPerm (subtreeSwap v n) x)).count
              (((d + 1) + r) + 1)
              (rightChild (subtreeSwap v r u)) =
            (stateAggregate x).count (((d + 1) + r) + 1)
              (rightChild u) := by
        rw [← subtreeSwap_succ_rightChild v u]
        exact hright
      fin_cases side
      · change
          HierarchicalPolicy.hazard
              (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a
              (((d + 1) + r) + 1)
              (subtreeSwap v (r + 1) (leftChild u)) =
            HierarchicalPolicy.hazard (stateAggregate x) a
              (((d + 1) + r) + 1) (leftChild u)
        rw [subtreeSwap_succ_leftChild,
          HierarchicalPolicy.hazard_leftChild,
          HierarchicalPolicy.hazard_leftChild, hparent]
        rw [hleft', hright']
      · change
          HierarchicalPolicy.hazard
              (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a
              (((d + 1) + r) + 1)
              (subtreeSwap v (r + 1) (rightChild u)) =
            HierarchicalPolicy.hazard (stateAggregate x) a
              (((d + 1) + r) + 1) (rightChild u)
        rw [subtreeSwap_succ_rightChild,
          HierarchicalPolicy.hazard_rightChild,
          HierarchicalPolicy.hazard_rightChild, hparent]
        rw [hleft', hright']

/-- Deletion masses at and above the swapped node are unchanged. -/
theorem policy_deletionMass_aboveSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {k : ℕ} (hkd : k ≤ d) (w : DyadicNode k) :
    HierarchicalPolicy.deletionMass
        (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a k w =
      HierarchicalPolicy.deletionMass (stateAggregate x) a k w := by
  unfold HierarchicalPolicy.deletionMass HierarchicalPolicy.inventory
  rw [stateAggregate_count_aboveSwap v x hkd w,
    policy_hazard_aboveSwap v x a hkd w]

/-- Deletion masses at descendant nodes are transported by the swap. -/
theorem policy_deletionMass_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {r : ℕ} (hrn : r ≤ n)
    (w : DyadicNode ((d + 1) + r)) :
    HierarchicalPolicy.deletionMass
        (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a
        ((d + 1) + r) (subtreeSwap v r w) =
      HierarchicalPolicy.deletionMass (stateAggregate x) a
        ((d + 1) + r) w := by
  unfold HierarchicalPolicy.deletionMass HierarchicalPolicy.inventory
  rw [stateAggregate_count_subtreeSwap v x hrn w,
    policy_hazard_subtreeSwap v x a hrn w]

/-- The Haar-type deletion coefficient at the swapped node changes sign. -/
theorem policy_imbalance_swapNode
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) :
    HierarchicalPolicy.imbalance
        (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a d v =
      -HierarchicalPolicy.imbalance (stateAggregate x) a d v := by
  have hleft :=
    policy_deletionMass_subtreeSwap v x a (r := 0) (by omega)
      (leftChild v)
  have hright :=
    policy_deletionMass_subtreeSwap v x a (r := 0) (by omega)
      (rightChild v)
  simp only [subtreeSwap_zero_left] at hleft
  simp only [subtreeSwap_zero_right] at hright
  unfold HierarchicalPolicy.imbalance
  rw [hleft, hright]
  ring

/-- A strict ancestor's deletion coefficient is unchanged. -/
theorem policy_imbalance_strictAncestor
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {k : ℕ} (hkd : k < d) (w : DyadicNode k) :
    HierarchicalPolicy.imbalance
        (stateAggregate (inventoryPerm (subtreeSwap v n) x)) a k w =
      HierarchicalPolicy.imbalance (stateAggregate x) a k w := by
  unfold HierarchicalPolicy.imbalance
  rw [policy_deletionMass_aboveSwap v x a (by omega) (leftChild w),
    policy_deletionMass_aboveSwap v x a (by omega) (rightChild w)]

/-! ## Arbitrary-depth wrappers -/

theorem stateAggregate_count_subtreeSwapWithGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (x : InventoryState (DyadicNode L) m)
    {s : ℕ} (hsr : s ≤ r) (w : DyadicNode ((d + 1) + s)) :
    (stateAggregate (inventorySwapWithGap v r hlevel x)).count
        ((d + 1) + s) (subtreeSwap v s w) =
      (stateAggregate x).count ((d + 1) + s) w := by
  subst L
  exact stateAggregate_count_subtreeSwap v x hsr w

theorem stateAggregate_count_leafSwapWithGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (stateAggregate (inventorySwapWithGap v r hlevel x)).count L
        (leafSwapWithGap v r hlevel w) =
      (stateAggregate x).count L w := by
  subst L
  exact stateAggregate_count_subtreeSwap v x le_rfl w

theorem stateAggregate_count_aboveSwapWithGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (x : InventoryState (DyadicNode L) m)
    {k : ℕ} (hkd : k ≤ d) (w : DyadicNode k) :
    (stateAggregate (inventorySwapWithGap v r hlevel x)).count k w =
      (stateAggregate x).count k w := by
  subst L
  exact stateAggregate_count_aboveSwap v x hkd w

theorem policy_deletionMass_subtreeSwapWithGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    {s : ℕ} (hsr : s ≤ r) (w : DyadicNode ((d + 1) + s)) :
    HierarchicalPolicy.deletionMass
        (stateAggregate (inventorySwapWithGap v r hlevel x)) a
        ((d + 1) + s) (subtreeSwap v s w) =
      HierarchicalPolicy.deletionMass (stateAggregate x) a
        ((d + 1) + s) w := by
  subst L
  exact policy_deletionMass_subtreeSwap v x a hsr w

theorem policy_deletionMass_leafSwapWithGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    (w : DyadicNode L) :
    HierarchicalPolicy.deletionMass
        (stateAggregate (inventorySwapWithGap v r hlevel x)) a L
        (leafSwapWithGap v r hlevel w) =
      HierarchicalPolicy.deletionMass (stateAggregate x) a L w := by
  subst L
  exact policy_deletionMass_subtreeSwap v x a le_rfl w

theorem policy_imbalance_swapNodeWithGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (x : InventoryState (DyadicNode L) m) (a : ℝ) :
    HierarchicalPolicy.imbalance
        (stateAggregate (inventorySwapWithGap v r hlevel x)) a d v =
      -HierarchicalPolicy.imbalance (stateAggregate x) a d v := by
  subst L
  exact policy_imbalance_swapNode v x a

theorem policy_imbalance_strictAncestorWithGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    {k : ℕ} (hkd : k < d) (w : DyadicNode k) :
    HierarchicalPolicy.imbalance
        (stateAggregate (inventorySwapWithGap v r hlevel x)) a k w =
      HierarchicalPolicy.imbalance (stateAggregate x) a k w := by
  subst L
  exact policy_imbalance_strictAncestor v x a hkd w

theorem stateAggregate_count_leafSwap
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (stateAggregate (inventorySwap hdL v x)).count L
        (leafSwap hdL v w) =
      (stateAggregate x).count L w :=
  stateAggregate_count_leafSwapWithGap v (L - (d + 1)) (by omega) x w

theorem policy_deletionMass_leafSwap
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    (w : DyadicNode L) :
    HierarchicalPolicy.deletionMass
        (stateAggregate (inventorySwap hdL v x)) a L
        (leafSwap hdL v w) =
      HierarchicalPolicy.deletionMass (stateAggregate x) a L w :=
  policy_deletionMass_leafSwapWithGap
    v (L - (d + 1)) (by omega) x a w

theorem policy_imbalance_swapNode_general
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (a : ℝ) :
    HierarchicalPolicy.imbalance
        (stateAggregate (inventorySwap hdL v x)) a d v =
      -HierarchicalPolicy.imbalance (stateAggregate x) a d v :=
  policy_imbalance_swapNodeWithGap
    v (L - (d + 1)) (by omega) x a

theorem policy_imbalance_strictAncestor_general
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    {k : ℕ} (hkd : k < d) (w : DyadicNode k) :
    HierarchicalPolicy.imbalance
        (stateAggregate (inventorySwap hdL v x)) a k w =
      HierarchicalPolicy.imbalance (stateAggregate x) a k w :=
  policy_imbalance_strictAncestorWithGap
    v (L - (d + 1)) (by omega) x a hkd w

/-! ## Generic move and kernel equivariance -/

theorem inventoryPerm_move
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : Equiv.Perm ι) (x : InventoryState ι m) (deleted arrived : ι) :
    inventoryPerm e (InventoryState.move x deleted arrived) =
      InventoryState.move (inventoryPerm e x) (e deleted) (e arrived) := by
  by_cases hd : 0 < x.1 deleted
  · have hd' : 0 < (inventoryPerm e x).1 (e deleted) := by simpa
    apply InventoryState.ext
    intro i
    let j := e.symm i
    have hij : e j = i := e.apply_symm_apply i
    rw [← hij, inventoryPerm_apply_image_count,
      InventoryState.move_apply_of_pos x hd,
      InventoryState.move_apply_of_pos (inventoryPerm e x) hd']
    simp
  · have hz : x.1 deleted = 0 := by omega
    have hz' : (inventoryPerm e x).1 (e deleted) = 0 := by simpa
    rw [InventoryState.move_empty x hz,
      InventoryState.move_empty (inventoryPerm e x) hz']

theorem deletionKernel_equivariant
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}
    (R : DeletionRule ι m) (e : Equiv.Perm ι)
    (hprob : ∀ x i, R.prob (inventoryPerm e x) (e i) = R.prob x i) :
    R.kernel.Equivariant (inventoryPerm e) := by
  intro x y
  simp only [DeletionRule.kernel_apply]
  rw [← Equiv.sum_comp e (fun deleted =>
    ∑ arrived,
      if InventoryState.move (inventoryPerm e x) deleted arrived =
          inventoryPerm e y then
        R.prob (inventoryPerm e x) deleted *
          (1 / Fintype.card ι : ℝ)
      else 0)]
  apply Finset.sum_congr rfl
  intro deleted _
  rw [← Equiv.sum_comp e (fun arrived =>
    if InventoryState.move (inventoryPerm e x) (e deleted) arrived =
        inventoryPerm e y then
      R.prob (inventoryPerm e x) (e deleted) *
        (1 / Fintype.card ι : ℝ)
    else 0)]
  apply Finset.sum_congr rfl
  intro arrived _
  rw [← inventoryPerm_move e x deleted arrived, hprob]
  simp

/-! ## The concrete hierarchical deletion kernel -/

@[simp] theorem stateAggregate_eq_aggregatedInventory
    {L m : ℕ} (x : InventoryState (DyadicNode L) m) :
    stateAggregate x = HierarchicalDynamics.aggregatedInventory x := by
  rfl

theorem concrete_aggregateCount_leafSwap
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (HierarchicalDynamics.aggregatedInventory
        (inventorySwap hdL v x)).count L (leafSwap hdL v w) =
      (HierarchicalDynamics.aggregatedInventory x).count L w := by
  simpa only [← stateAggregate_eq_aggregatedInventory] using
    stateAggregate_count_leafSwap hdL v x w

theorem concrete_deletionMass_leafSwap
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    (w : DyadicNode L) :
    HierarchicalPolicy.deletionMass
        (HierarchicalDynamics.aggregatedInventory
          (inventorySwap hdL v x)) a L (leafSwap hdL v w) =
      HierarchicalPolicy.deletionMass
        (HierarchicalDynamics.aggregatedInventory x) a L w := by
  simpa only [← stateAggregate_eq_aggregatedInventory] using
    policy_deletionMass_leafSwap hdL v x a w

theorem concrete_imbalance_swapNode
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (a : ℝ) :
    HierarchicalPolicy.imbalance
        (HierarchicalDynamics.aggregatedInventory
          (inventorySwap hdL v x)) a d v =
      -HierarchicalPolicy.imbalance
        (HierarchicalDynamics.aggregatedInventory x) a d v := by
  simpa only [← stateAggregate_eq_aggregatedInventory] using
    policy_imbalance_swapNode_general hdL v x a

theorem concrete_imbalance_strictAncestor
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (x : InventoryState (DyadicNode L) m) (a : ℝ)
    {k : ℕ} (hkd : k < d) (w : DyadicNode k) :
    HierarchicalPolicy.imbalance
        (HierarchicalDynamics.aggregatedInventory
          (inventorySwap hdL v x)) a k w =
      HierarchicalPolicy.imbalance
        (HierarchicalDynamics.aggregatedInventory x) a k w := by
  simpa only [← stateAggregate_eq_aggregatedInventory] using
    policy_imbalance_strictAncestor_general hdL v x a hkd w

theorem concrete_deletionRule_prob_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (w : DyadicNode ((d + 1) + n)) :
    (HierarchicalDynamics.deletionRule a ha hm).prob
        (inventoryPerm (subtreeSwap v n) x) (subtreeSwap v n w) =
      (HierarchicalDynamics.deletionRule a ha hm).prob x w := by
  change
    HierarchicalPolicy.deletionMass
        (HierarchicalDynamics.aggregatedInventory
          (inventoryPerm (subtreeSwap v n) x)) a ((d + 1) + n)
          (subtreeSwap v n w) =
      HierarchicalPolicy.deletionMass
        (HierarchicalDynamics.aggregatedInventory x) a ((d + 1) + n) w
  simpa only [← stateAggregate_eq_aggregatedInventory] using
    policy_deletionMass_subtreeSwap v x a le_rfl w

theorem concrete_kernel_equivariant_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (HierarchicalDynamics.kernel
        (L := (d + 1) + n) (m := m) a ha hm).Equivariant
      (inventoryPerm (subtreeSwap v n)) := by
  exact deletionKernel_equivariant
    (HierarchicalDynamics.deletionRule a ha hm)
    (subtreeSwap v n)
    (concrete_deletionRule_prob_subtreeSwap v a ha hm)

theorem concrete_kernel_equivariant_withGap
    {d L m : ℕ} (v : DyadicNode d) (r : ℕ)
    (hlevel : (d + 1) + r = L)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (HierarchicalDynamics.kernel (L := L) (m := m) a ha hm).Equivariant
      (inventorySwapWithGap v r hlevel) := by
  subst L
  exact concrete_kernel_equivariant_subtreeSwap v a ha hm

theorem concrete_kernel_equivariant
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (HierarchicalDynamics.kernel (L := L) (m := m) a ha hm).Equivariant
      (inventorySwap hdL v) :=
  concrete_kernel_equivariant_withGap
    v (L - (d + 1)) (by omega) a ha hm

/-! ## Invariant stationary laws for a single permutation -/

/-- Push a finite law forward along a permutation, in pointwise form. -/
def permuteLaw {α : Type*} [Fintype α] 
    (e : Equiv.Perm α) (μ : FiniteLaw α) : FiniteLaw α where
  mass x := μ.mass (e.symm x)
  mass_nonneg x := μ.mass_nonneg _
  sum_mass := by
    calc
      ∑ x, μ.mass (e.symm x) = ∑ x, μ.mass x :=
        Equiv.sum_comp e.symm μ.mass
      _ = 1 := μ.sum_mass

@[simp] theorem permuteLaw_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (μ : FiniteLaw α) (x : α) :
    (permuteLaw e μ).mass x = μ.mass (e.symm x) :=
  rfl

theorem permuteLaw_stationary
    {α : Type*} [Fintype α] [DecidableEq α]
    {K : FiniteKernel α} {μ : FiniteLaw α} {e : Equiv.Perm α}
    (hK : K.Equivariant e) (hμ : K.IsStationary μ) :
    K.IsStationary (permuteLaw e μ) := by
  apply FiniteLaw.ext
  intro y
  simp only [FiniteKernel.mass_step, permuteLaw_mass]
  rw [← Equiv.sum_comp e (fun x => μ.mass (e.symm x) * K x y)]
  simp only [e.symm_apply_apply]
  have hKy (x : α) : K (e x) y = K x (e.symm y) := by
    simpa using hK x (e.symm y)
  simp_rw [hKy]
  rw [← FiniteKernel.mass_step, hμ]

theorem stationary_lawInvariant_of_irreducible
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {K : FiniteKernel α} {μ : FiniteLaw α} {e : Equiv.Perm α}
    (hirr : K.Irreducible) (hK : K.Equivariant e)
    (hμ : K.IsStationary μ) :
    FiniteKernel.LawInvariant μ e := by
  have heq : permuteLaw e μ = μ :=
    FiniteKernel.stationary_unique hirr
      (permuteLaw_stationary hK hμ) hμ
  intro x
  have hx := congrArg (fun ν : FiniteLaw α => ν.mass (e x)) heq
  simpa using hx.symm

theorem concrete_stationary_lawInvariant
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    {μ : FiniteLaw (InventoryState (DyadicNode L) m)}
    (hirr :
      (HierarchicalDynamics.kernel (L := L) (m := m) a ha hm).Irreducible)
    (hμ :
      (HierarchicalDynamics.kernel (L := L) (m := m) a ha hm).IsStationary μ) :
    FiniteKernel.LawInvariant μ (inventorySwap hdL v) :=
  stationary_lawInvariant_of_irreducible hirr
    (concrete_kernel_equivariant hdL v a ha hm) hμ

end TreeSymmetry

end

end FD1D
