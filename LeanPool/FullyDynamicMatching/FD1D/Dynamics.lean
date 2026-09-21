/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Markov
import LeanPool.FullyDynamicMatching.FD1D.Policy
import LeanPool.FullyDynamicMatching.FD1D.Potential
import LeanPool.FullyDynamicMatching.FD1D.PotentialBounds

/-! # Dynamics -/

namespace FD1D

noncomputable section

/-!
# Concrete hierarchical inventory dynamics

This module instantiates the finite inventory chain with the hierarchical
deletion masses.  It also connects the actual delete-then-arrive kernel to
the harmonic-potential drift identity.
-/

open scoped BigOperators

namespace HierarchicalDynamics

variable {L m : ℕ}

/-- Regard a fixed-total count vector as a leaf inventory. -/
def leafInventory (x : InventoryState (DyadicNode L) m) :
    LeafInventory L m where
  count := x.1
  total_count := x.2

/-- Canonical coherent counts associated with a count-chain state. -/
def aggregatedInventory (x : InventoryState (DyadicNode L) m) :
    AggregatedInventory L m :=
  (leafInventory x).aggregate

@[simp] theorem leafInventory_count
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (leafInventory x).count w = x.1 w :=
  rfl

@[simp] theorem aggregatedInventory_leaf_count
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (aggregatedInventory x).count L w = x.1 w := by
  change ((leafInventory x).aggregate).count L w = x.1 w
  rw [(leafInventory x).aggregate.count_leaf]
  rfl

theorem aggregatedInventory_count
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    (aggregatedInventory x).count d v =
      ∑ w ∈ leafBlock hdL v, x.1 w := by
  simp [aggregatedInventory, LeafInventory.aggregate,
    LeafInventory.nodeCount, leafInventory, hdL]

/-- Leaf deletion probabilities prescribed by the hierarchical policy. -/
def deletionRule (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    DeletionRule (DyadicNode L) m where
  prob x w :=
    HierarchicalPolicy.deletionMass (aggregatedInventory x) a L w
  nonneg x w :=
    HierarchicalPolicy.leaf_deletionMass_nonneg
      (aggregatedInventory x) ha hm w
  empty x w hw :=
    HierarchicalPolicy.leaf_deletionMass_eq_zero_of_count_eq_zero
      (aggregatedInventory x) a w (by simpa using hw)
  occupied_pos x w hw := by
    rw [HierarchicalPolicy.deletionMass_eq_count_mul_hazard]
    exact mul_pos (by
      rw [aggregatedInventory_leaf_count]
      exact_mod_cast hw)
      (HierarchicalPolicy.hazard_pos
        (aggregatedInventory x) ha hm L le_rfl w)
  sum_prob x :=
    HierarchicalPolicy.sum_leaf_deletionMass
      (aggregatedInventory x) ha hm

@[simp] theorem deletionRule_prob
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) (w : DyadicNode L) :
    (deletionRule a ha hm).prob x w =
      HierarchicalPolicy.deletionMass (aggregatedInventory x) a L w :=
  rfl

/-- Delete according to the hierarchical rule, then add a uniform leaf. -/
def kernel (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    FiniteKernel (InventoryState (DyadicNode L) m) :=
  (deletionRule a ha hm).kernel

@[simp] theorem kernel_apply
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x y : InventoryState (DyadicNode L) m) :
    kernel a ha hm x y =
      ∑ deleted, ∑ arrived,
        if InventoryState.move x deleted arrived = y then
          HierarchicalPolicy.deletionMass
              (aggregatedInventory x) a L deleted *
            (1 / Fintype.card (DyadicNode L) : ℝ)
        else 0 :=
  rfl

/-! ## Constructive irreducibility of fixed-total inventory dynamics -/

/-- Total target deficit of one fixed-total inventory relative to another. -/
def inventoryDeficit
    {ι : Type*} [Fintype ι] {m : ℕ}
    (x y : InventoryState ι m) : ℕ :=
  ∑ i, (y.1 i - x.1 i)

theorem inventoryDeficit_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (x y : InventoryState ι m) :
    inventoryDeficit x y = 0 ↔ x = y := by
  constructor
  · intro hzero
    have hpoint :
        ∀ i : ι, y.1 i - x.1 i = 0 := by
      rw [inventoryDeficit,
        Finset.sum_eq_zero_iff_of_nonneg
          (fun _ _ => Nat.zero_le _)] at hzero
      exact fun i => hzero i (Finset.mem_univ i)
    have hyx : ∀ i : ι, y.1 i ≤ x.1 i :=
      fun i => Nat.sub_eq_zero_iff_le.mp (hpoint i)
    apply InventoryState.ext
    have hsum : (∑ i, y.1 i) = ∑ i, x.1 i := by
      rw [x.2, y.2]
    have hall :=
      (Finset.sum_eq_sum_iff_of_le
        (s := Finset.univ)
        (fun i _ => hyx i)).mp hsum
    intro i
    exact (hall i (Finset.mem_univ i)).symm
  · rintro rfl
    simp [inventoryDeficit]

private theorem exists_deficit_and_excess
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (x y : InventoryState ι m) (hxy : x ≠ y) :
    ∃ arrived deleted : ι,
      x.1 arrived < y.1 arrived ∧ y.1 deleted < x.1 deleted := by
  have hdeficit : inventoryDeficit x y ≠ 0 := by
    exact fun hzero =>
      hxy ((inventoryDeficit_eq_zero_iff x y).mp hzero)
  have hexists :
      ∃ arrived : ι, y.1 arrived - x.1 arrived ≠ 0 := by
    by_contra h
    push Not at h
    apply hdeficit
    unfold inventoryDeficit
    simp [h]
  obtain ⟨arrived, harrived⟩ := hexists
  have harrivedlt : x.1 arrived < y.1 arrived := by
    omega
  have hexcess : ∃ deleted : ι, y.1 deleted < x.1 deleted := by
    by_contra h
    push Not at h
    have hsumlt :
        (∑ i, x.1 i) < ∑ i, y.1 i :=
      Finset.sum_lt_sum
        (fun i _ => h i)
        ⟨arrived, Finset.mem_univ arrived, harrivedlt⟩
    rw [x.2, y.2] at hsumlt
    omega
  obtain ⟨deleted, hdeleted⟩ := hexcess
  exact ⟨arrived, deleted, harrivedlt, hdeleted⟩

theorem inventoryDeficit_move_lt
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (x y : InventoryState ι m) {deleted arrived : ι}
    (harrived : x.1 arrived < y.1 arrived)
    (hdeleted : y.1 deleted < x.1 deleted) :
    inventoryDeficit (InventoryState.move x deleted arrived) y <
      inventoryDeficit x y := by
  have hdeletedPos : 0 < x.1 deleted := by omega
  have hne : arrived ≠ deleted := by
    intro h
    subst deleted
    omega
  let deficit : ι → ℕ := fun i => y.1 i - x.1 i
  have hfun :
      (fun i =>
        y.1 i - (InventoryState.move x deleted arrived).1 i) =
        Function.update deficit arrived (deficit arrived - 1) := by
    funext i
    rw [InventoryState.move_apply_of_pos x hdeletedPos]
    by_cases hia : i = arrived
    · subst i
      simp [deficit, hne]
      omega
    · by_cases hid : i = deleted
      · subst i
        have hda : deleted ≠ arrived := Ne.symm hne
        simp [deficit, hda]
        omega
      · simp [deficit, hia, hid]
  unfold inventoryDeficit
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ arrived)]
  have hsplit :=
    Finset.sum_erase_add Finset.univ deficit (Finset.mem_univ arrived)
  have hpos : 0 < deficit arrived := by
    dsimp [deficit]
    omega
  simp only [Finset.sdiff_singleton_eq_erase]
  change
    deficit arrived - 1 +
        ∑ x ∈ Finset.univ.erase arrived, deficit x <
      ∑ i, deficit i
  omega

/--
Every fixed-total inventory is reachable from every other one under any
deletion rule that is strictly positive on occupied coordinates.
-/
theorem deletionRule_kernel_irreducible
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}
    (R : DeletionRule ι m) :
    R.kernel.Irreducible := by
  intro x y
  induction hdef : inventoryDeficit x y using
      Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hxy : x = y
      · subst y
        exact R.kernel.reaches_refl x
      · obtain ⟨arrived, deleted, harrived, hdeleted⟩ :=
          exists_deficit_and_excess x y hxy
        let z := InventoryState.move x deleted arrived
        have hstep : R.kernel.Reaches x z :=
          R.kernel.reaches_of_pos
            (R.kernel_move_pos x (by omega))
        have hdecrease : inventoryDeficit z y < n := by
          rw [← hdef]
          exact inventoryDeficit_move_lt x y harrived hdeleted
        exact R.kernel.reaches_trans hstep
          (ih (inventoryDeficit z y) hdecrease z rfl)

theorem kernel_move_pos
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {deleted arrived : DyadicNode L} (hdeleted : 0 < x.1 deleted) :
    0 < kernel a ha hm x
      (InventoryState.move x deleted arrived) :=
  (deletionRule a ha hm).kernel_move_pos x hdeleted

/-- The hierarchical fixed-total count chain is irreducible. -/
theorem kernel_irreducible
    (a : ℝ) (ha : 0 < a) (hm : 0 < m) :
    (kernel (L := L) a ha hm).Irreducible :=
  deletionRule_kernel_irreducible (deletionRule a ha hm)

private theorem leafBlock_self (v : DyadicNode L) :
    leafBlock (le_refl L) v = {v} := by
  ext w
  rw [mem_leafBlock_interval, Finset.mem_singleton]
  simp only [Nat.sub_self, pow_zero, mul_one]
  constructor
  · intro hw
    apply Fin.ext
    omega
  · rintro rfl
    omega

/--
A coherent tree label equals the sum of its leaf labels over the corresponding
descendant block.
-/
theorem coherent_eq_sum_leafBlock
    {A : Type*} [AddCommMonoid A]
    (q : CoherentTreeLabel L A)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    q.value d v = ∑ w ∈ leafBlock hdL v, q.value L w := by
  induction hgap : L - d using Nat.strong_induction_on generalizing d with
  | h k ih =>
      by_cases hd : d = L
      · subst d
        rw [leafBlock_self]
        simp
      · have hlt : d < L := lt_of_le_of_ne hdL hd
        have hgap' : L - (d + 1) < k := by omega
        rw [q.children d hlt v, leafBlock_children hlt v]
        rw [Finset.sum_union
          (leafBlock_disjoint (show d + 1 ≤ L by omega)
            (leftChild_ne_rightChild v))]
        rw [ih (L - (d + 1)) hgap' (d := d + 1)
              (Nat.succ_le_iff.mpr hlt) (leftChild v) rfl,
            ih (L - (d + 1)) hgap' (d := d + 1)
              (Nat.succ_le_iff.mpr hlt) (rightChild v) rfl]

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
      HierarchicalPolicy.deletionMass
        (aggregatedInventory x) a d v := by
  let q : CoherentTreeLabel L ℝ :=
    { value :=
        HierarchicalPolicy.deletionMass (aggregatedInventory x) a
      children :=
        HierarchicalPolicy.deletionMass_children
          (aggregatedInventory x) ha }
  simpa [deletionMarginal, deletionRule, q] using
    (coherent_eq_sum_leafBlock q hdL v).symm

/-- Probability that a uniform arriving leaf lies below a given node. -/
def arrivalMarginal {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) : ℝ :=
  ∑ _w ∈ leafBlock hdL v,
    (1 / Fintype.card (DyadicNode L) : ℝ)

theorem arrivalMarginal_eq_nodeMass
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    arrivalMarginal hdL v = nodeMass d v := by
  rw [arrivalMarginal, Finset.sum_const, nsmul_eq_mul, card_leafBlock]
  simp only [Fintype.card_fin]
  norm_num [nodeMass]
  have hpow :
      (2 : ℝ) ^ L = (2 : ℝ) ^ d * (2 : ℝ) ^ (L - d) := by
    rw [← pow_add, Nat.add_sub_of_le hdL]
  rw [hpow]
  field_simp

/-! ## Counts under an actual leaf move -/

private theorem sum_update_add_one
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (j : ι) :
    ∑ i ∈ S, Function.update f j (f j + 1) i =
      (∑ i ∈ S, f i) + if j ∈ S then 1 else 0 := by
  by_cases hj : j ∈ S
  · rw [Finset.sum_update_of_mem hj]
    have hsplit := Finset.sum_erase_add S f hj
    simp only [Finset.sdiff_singleton_eq_erase, if_pos hj]
    omega
  · rw [if_neg hj]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := by
      intro hij
      exact hj (hij ▸ hi)
    simp [hij]

private theorem sum_update_sub_one
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (j : ι) (hjpos : 0 < f j) :
    ∑ i ∈ S, Function.update f j (f j - 1) i =
      (∑ i ∈ S, f i) - if j ∈ S then 1 else 0 := by
  by_cases hj : j ∈ S
  · rw [Finset.sum_update_of_mem hj]
    have hsplit := Finset.sum_erase_add S f hj
    simp only [Finset.sdiff_singleton_eq_erase, if_pos hj]
    omega
  · rw [if_neg hj, Nat.sub_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := by
      intro hij
      exact hj (hij ▸ hi)
    simp [hij]

/-- Boolean membership in a finite block. -/
def inBlock {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) : Bool :=
  decide (i ∈ S)

@[simp] theorem inBlock_eq_true
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {i : ι} :
    inBlock S i = true ↔ i ∈ S := by
  simp [inBlock]

@[simp] theorem inBlock_eq_false
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {i : ι} :
    inBlock S i = false ↔ i ∉ S := by
  simp [inBlock]

/--
The count in any finite block after an occupied deletion and an arrival is
the four-case `updateCount` used by the potential calculation.
-/
theorem sum_move_eq_updateCount
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (x : InventoryState ι m) (S : Finset ι)
    {deleted arrived : ι} (hdeleted : 0 < x.1 deleted) :
    ∑ i ∈ S, (InventoryState.move x deleted arrived).1 i =
      updateCount (∑ i ∈ S, x.1 i)
        (inBlock S deleted) (inBlock S arrived) := by
  rw [InventoryState.move, dif_pos hdeleted]
  let removed := Function.update x.1 deleted (x.1 deleted - 1)
  change
    (∑ i ∈ S, Function.update removed arrived (removed arrived + 1) i) =
      updateCount (∑ i ∈ S, x.1 i)
        (inBlock S deleted) (inBlock S arrived)
  rw [sum_update_add_one S removed arrived]
  have hremoved := sum_update_sub_one S x.1 deleted hdeleted
  change (∑ i ∈ S, removed i) =
    (∑ i ∈ S, x.1 i) - if deleted ∈ S then 1 else 0 at hremoved
  rw [hremoved]
  by_cases hdS : deleted ∈ S <;>
    by_cases haS : arrived ∈ S <;>
    simp [inBlock, hdS, haS, updateCount]
  have hsumpos : 0 < ∑ i ∈ S, x.1 i := by
    exact lt_of_lt_of_le hdeleted
      (Finset.single_le_sum
        (s := S) (f := x.1) (fun _ _ => Nat.zero_le _) hdS)
  omega

/-- Concrete aggregated count update at every node. -/
theorem aggregatedInventory_move_count
    (x : InventoryState (DyadicNode L) m)
    {deleted arrived : DyadicNode L} (hdeleted : 0 < x.1 deleted)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    (aggregatedInventory (InventoryState.move x deleted arrived)).count d v =
      updateCount ((aggregatedInventory x).count d v)
        (inBlock (leafBlock hdL v) deleted)
        (inBlock (leafBlock hdL v) arrived) := by
  rw [aggregatedInventory_count _ hdL,
    aggregatedInventory_count _ hdL]
  exact sum_move_eq_updateCount x (leafBlock hdL v) hdeleted

/-! ## Finite weighted membership partitions -/

private theorem weighted_inBlock_partition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℝ) (S : Finset ι) (q : ℝ)
    (hsum : ∑ i, weight i = 1)
    (hq : ∑ i ∈ S, weight i = q)
    (f : Bool → ℝ) :
    ∑ i, weight i * f (inBlock S i) =
      q * f true + (1 - q) * f false := by
  have hpartition :=
    Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun i => i ∈ S) weight
  have hout :
      ∑ i ∈ Finset.univ with i ∉ S, weight i = 1 - q := by
    have hin :
        ∑ i ∈ Finset.univ with i ∈ S, weight i = q := by
      simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using hq
    linarith
  calc
    ∑ i, weight i * f (inBlock S i) =
        (∑ i ∈ Finset.univ with i ∈ S,
            weight i * f (inBlock S i)) +
          ∑ i ∈ Finset.univ with i ∉ S,
            weight i * f (inBlock S i) := by
              rw [Finset.sum_filter_add_sum_filter_not]
    _ = (∑ i ∈ S, weight i) * f true +
          (∑ i ∈ Finset.univ with i ∉ S, weight i) * f false := by
            congr 1
            · rw [Finset.filter_mem_eq_inter, Finset.univ_inter,
                Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              simp [inBlock, hi]
            · rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              have hiS : i ∉ S := (Finset.mem_filter.mp hi).2
              simp [inBlock, hiS]
    _ = q * f true + (1 - q) * f false := by rw [hq, hout]

theorem double_inBlock_partition
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (deleteWeight : ι → ℝ) (arrivalWeight : κ → ℝ)
    (deleteSet : Finset ι) (arrivalSet : Finset κ)
    (q p : ℝ)
    (hdeleteSum : ∑ i, deleteWeight i = 1)
    (harrivalSum : ∑ j, arrivalWeight j = 1)
    (hq : ∑ i ∈ deleteSet, deleteWeight i = q)
    (hp : ∑ j ∈ arrivalSet, arrivalWeight j = p)
    (f : Bool → Bool → ℝ) :
    (∑ i, ∑ j,
        deleteWeight i * arrivalWeight j *
          f (inBlock deleteSet i) (inBlock arrivalSet j)) =
      ∑ deleted : Bool, ∑ arrived : Bool,
        bernoulliMass q deleted * bernoulliMass p arrived *
          f deleted arrived := by
  have hinner (i : ι) :
      (∑ j, deleteWeight i * arrivalWeight j *
          f (inBlock deleteSet i) (inBlock arrivalSet j)) =
        deleteWeight i *
          (p * f (inBlock deleteSet i) true +
            (1 - p) * f (inBlock deleteSet i) false) := by
    calc
      (∑ j, deleteWeight i * arrivalWeight j *
          f (inBlock deleteSet i) (inBlock arrivalSet j)) =
          deleteWeight i * ∑ j,
            arrivalWeight j *
              f (inBlock deleteSet i) (inBlock arrivalSet j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = deleteWeight i *
          (p * f (inBlock deleteSet i) true +
            (1 - p) * f (inBlock deleteSet i) false) := by
            rw [weighted_inBlock_partition arrivalWeight arrivalSet
              p harrivalSum hp]
  simp_rw [hinner]
  rw [weighted_inBlock_partition deleteWeight deleteSet q
    hdeleteSum hq
    (fun deleted =>
      p * f deleted true + (1 - p) * f deleted false)]
  simp [bernoulliMass]
  ring

/-! ## Expectations under the concrete kernel -/

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
        (harmonicPotential a
            ((aggregatedInventory y).count d v) -
          harmonicPotential a
            ((aggregatedInventory x).count d v)) =
      expectedNodePotentialChange a
        ((aggregatedInventory x).count d v)
        (nodeMass d v)
        (HierarchicalPolicy.deletionMass
          (aggregatedInventory x) a d v) := by
  let S := leafBlock hdL v
  let deleteWeight : DyadicNode L → ℝ :=
    fun w => (deletionRule a ha hm).prob x w
  let arrivalWeight : DyadicNode L → ℝ :=
    fun _ => (1 / Fintype.card (DyadicNode L) : ℝ)
  let N := (aggregatedInventory x).count d v
  let q :=
    HierarchicalPolicy.deletionMass (aggregatedInventory x) a d v
  let p := nodeMass d v
  let change : Bool → Bool → ℝ := fun deleted arrived =>
    harmonicPotential a (updateCount N deleted arrived) -
      harmonicPotential a N
  rw [kernel_expectation_eq_delete_arrive]
  have hrewrite (deleted arrived : DyadicNode L) :
      deleteWeight deleted * arrivalWeight arrived *
          (harmonicPotential a
              ((aggregatedInventory
                (InventoryState.move x deleted arrived)).count d v) -
            harmonicPotential a N) =
        deleteWeight deleted * arrivalWeight arrived *
          change (inBlock S deleted) (inBlock S arrived) := by
    by_cases hdeleted : 0 < x.1 deleted
    · rw [aggregatedInventory_move_count x hdeleted hdL v]
    · have hempty : x.1 deleted = 0 := by omega
      have hweight : deleteWeight deleted = 0 :=
        (deletionRule a ha hm).empty x deleted hempty
      simp [hweight]
  change
    (∑ deleted, ∑ arrived,
      deleteWeight deleted * arrivalWeight arrived *
        (harmonicPotential a
            ((aggregatedInventory
              (InventoryState.move x deleted arrived)).count d v) -
          harmonicPotential a N)) =
      expectedNodePotentialChange a N p q
  simp_rw [hrewrite]
  apply Eq.trans
    (double_inBlock_partition deleteWeight arrivalWeight S S q p
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
        simpa [arrivalWeight, S, p, arrivalMarginal] using
          arrivalMarginal_eq_nodeMass hdL v)
      change)
  rfl

/-! ## Global state observables and exact kernel drift -/

/-- Coherent natural count label of a count-chain state. -/
def countLabel (x : InventoryState (DyadicNode L) m) :
    ∀ d, DyadicNode d → ℕ :=
  (aggregatedInventory x).count

/-- Hierarchical deletion mass at every tree node. -/
def deletionLabel (a : ℝ) (x : InventoryState (DyadicNode L) m) :
    ∀ d, DyadicNode d → ℝ :=
  HierarchicalPolicy.deletionMass (aggregatedInventory x) a

/-- Extended policy hazard at every tree node. -/
def hazardLabel (a : ℝ) (x : InventoryState (DyadicNode L) m) :
    ∀ d, DyadicNode d → ℝ :=
  HierarchicalPolicy.hazard (aggregatedInventory x) a

/-- Global harmonic potential of a count-chain state. -/
def statePotential (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  globalHarmonicPotential L a (countLabel x)

/-- Bellman drift quantity `D` of a count-chain state. -/
def stateDrift (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  potentialDrift L a (countLabel x) (deletionLabel a x)

/-- Harmonic drift remainder `R` of a count-chain state. -/
def stateRemainder (a : ℝ)
    (x : InventoryState (DyadicNode L) m) : ℝ :=
  potentialRemainder L a (countLabel x) (deletionLabel a x)

/-- Hazard energy at one level in a count-chain state. -/
def stateHazardEnergy (a : ℝ)
    (x : InventoryState (DyadicNode L) m) (d : ℕ) : ℝ :=
  hazardEnergy (hazardLabel a x) d

theorem kernel_expected_globalPotentialChange
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    ∑ y, kernel a ha hm x y *
        (statePotential a y - statePotential a x) =
      expectedGlobalPotentialChange L a
        (countLabel x) (deletionLabel a x) := by
  have hpoint (y : InventoryState (DyadicNode L) m) :
      statePotential a y - statePotential a x =
        ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
          (nodeMass (d + 1) v) ^ 2 *
            (harmonicPotential a
                ((aggregatedInventory y).count (d + 1) v) -
              harmonicPotential a
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
            (harmonicPotential a
                ((aggregatedInventory y).count (d + 1) v) -
              harmonicPotential a
                ((aggregatedInventory x).count (d + 1) v))) =
        ∑ d ∈ Finset.range L, ∑ v : DyadicNode (d + 1),
          (nodeMass (d + 1) v) ^ 2 *
            (∑ y, kernel a ha hm x y *
              (harmonicPotential a
                  ((aggregatedInventory y).count (d + 1) v) -
                harmonicPotential a
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
    _ = expectedGlobalPotentialChange L a
          (countLabel x) (deletionLabel a x) := by
      unfold expectedGlobalPotentialChange countLabel deletionLabel
      apply Finset.sum_congr rfl
      intro d hd
      have hdL : d < L := Finset.mem_range.mp hd
      apply Finset.sum_congr rfl
      intro v hv
      rw [kernel_expected_nodePotentialChange a ha hm x
        (show d + 1 ≤ L by omega) v]

/--
The conditional drift of the actual count-chain kernel is exactly the
policy's `D - R`.
-/
theorem kernel_drift_eq_stateDrift_sub_stateRemainder
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    ∑ y, kernel a ha hm x y *
        (statePotential a y - statePotential a x) =
      stateDrift a x - stateRemainder a x := by
  rw [kernel_expected_globalPotentialChange a ha hm x]
  exact expectedGlobalPotentialChange_eq_drift_sub_remainder ha
    (fun d v hzero => by
      change
        ((aggregatedInventory x).count d v : ℝ) *
          HierarchicalPolicy.hazard (aggregatedInventory x) a d v = 0
      change (aggregatedInventory x).count d v = 0 at hzero
      rw [hzero]
      simp)

/--
Expanded form of the concrete one-step identity, exposing the generic
`potentialDrift` and `potentialRemainder` definitions directly.
-/
theorem kernel_drift_eq_potentialDrift_sub_potentialRemainder
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    ∑ y, kernel a ha hm x y *
        (statePotential a y - statePotential a x) =
      potentialDrift L a (countLabel x) (deletionLabel a x) -
        potentialRemainder L a (countLabel x) (deletionLabel a x) := by
  simpa [stateDrift, stateRemainder] using
    kernel_drift_eq_stateDrift_sub_stateRemainder a ha hm x

/-! ## Per-state bounds used by stationarity and finite-time telescoping -/

theorem countLabel_le_total
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    countLabel x d v ≤ m := by
  have hsum := (aggregatedInventory x).level_count_eq hdL
  have hle := Finset.single_le_sum
    (fun w _ => Nat.zero_le ((aggregatedInventory x).count d w))
    (Finset.mem_univ v)
  change (aggregatedInventory x).count d v ≤ m
  omega

theorem countLabel_le_total_all
    (x : InventoryState (DyadicNode L) m)
    (d : ℕ) (v : DyadicNode d) :
    countLabel x d v ≤ m := by
  by_cases hdL : d ≤ L
  · exact countLabel_le_total x hdL v
  · change (aggregatedInventory x).count d v ≤ m
    simp [aggregatedInventory, LeafInventory.aggregate, hdL]

theorem deletionLabel_nonneg
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    0 ≤ deletionLabel a x d v :=
  HierarchicalPolicy.deletionMass_nonneg
    (aggregatedInventory x) ha hm hdL v

theorem deletionLabel_le_one
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    deletionLabel a x d v ≤ 1 := by
  rw [← HierarchicalPolicy.sum_deletionMass
    (aggregatedInventory x) ha hm hdL]
  exact Finset.single_le_sum
    (fun w _ =>
      HierarchicalPolicy.deletionMass_nonneg
        (aggregatedInventory x) ha hm hdL w)
    (Finset.mem_univ v)

theorem deletionLabel_eq_zero_of_count_eq_zero
    (a : ℝ) (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (v : DyadicNode d)
    (hzero : countLabel x d v = 0) :
    deletionLabel a x d v = 0 := by
  change
    ((aggregatedInventory x).count d v : ℝ) *
      HierarchicalPolicy.hazard (aggregatedInventory x) a d v = 0
  change (aggregatedInventory x).count d v = 0 at hzero
  rw [hzero]
  simp

theorem intervalMass_le_count_add_a_mul_hazard
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    nodeMass d v ≤
      ((countLabel x d v : ℝ) + a) * hazardLabel a x d v :=
  HierarchicalPolicy.intervalMass_le_regularized_count_mul_hazard
    (aggregatedInventory x) ha hm hdL v

theorem stateDrift_lower_bound
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    stateDrift a x ≥
      a * (stateHazardEnergy a x L / 100 -
        103 / (300 * (m : ℝ) ^ 2)) := by
  exact HierarchicalPolicy.deterministic_bellman_bound
    (aggregatedInventory x) ha hm

theorem stateHazardEnergy_step
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m)
    {d : ℕ} (hdL : d < L) :
    stateHazardEnergy a x d ≤ stateHazardEnergy a x (d + 1) := by
  let I := aggregatedInventory x
  let h := HierarchicalPolicy.hazard I a
  have hlocal (v : DyadicNode d) :
      0 ≤ childAverage (fun d v => (h d v) ^ 2) d v -
        (h d v) ^ 2 := by
    have hineq :=
      HierarchicalPolicy.local_hazard_inequality I ha d hdL v
    have hcoef : 0 < 2 * a ^ 2 := by positivity
    have :
        0 ≤ 2 * a ^ 2 *
          (childAverage (fun d v => (h d v) ^ 2) d v -
            (h d v) ^ 2) :=
      (sq_nonneg (HierarchicalPolicy.imbalance I a d v)).trans hineq
    exact (mul_nonneg_iff_of_pos_left hcoef).mp this
  change hazardEnergy h d ≤ hazardEnergy h (d + 1)
  have hsum :
      0 ≤ ∑ v, nodeMass d v *
        (childAverage (fun d v => (h d v) ^ 2) d v -
          (h d v) ^ 2) := by
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg (nodeMass_nonneg d v) (hlocal v)
  rw [weighted_local_sum] at hsum
  simpa [hazardEnergy] using hsum

theorem stateHazardEnergy_mono_to_depth
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m)
    {i j : ℕ} (hij : i ≤ j) (hjL : j ≤ L) :
    stateHazardEnergy a x i ≤ stateHazardEnergy a x j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      exact (ih (by omega)).trans
        (stateHazardEnergy_step a ha x (by omega))

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
  have hq :=
    deletionLabel_le_one a ha hm x
      (show d + 1 ≤ L by omega) v
  have hp := nodeMass_nonneg (d + 1) v
  positivity

theorem stateRemainder_le_sum_hazardEnergy
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    stateRemainder a x ≤
      ∑ d ∈ Finset.range L, stateHazardEnergy a x (d + 1) := by
  unfold stateRemainder potentialRemainder stateHazardEnergy
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
    (intervalMass_le_count_add_a_mul_hazard
      a ha hm x (by omega) v)

theorem sum_stateHazardEnergy_le_depth_mul
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m) :
    (∑ d ∈ Finset.range L, stateHazardEnergy a x (d + 1)) ≤
      (L : ℝ) * stateHazardEnergy a x L := by
  calc
    (∑ d ∈ Finset.range L, stateHazardEnergy a x (d + 1))
        ≤ ∑ _d ∈ Finset.range L, stateHazardEnergy a x L := by
          apply Finset.sum_le_sum
          intro d hd
          have hdL : d < L := Finset.mem_range.mp hd
          exact stateHazardEnergy_mono_to_depth a ha x
            (by omega) le_rfl
    _ = (L : ℝ) * stateHazardEnergy a x L := by simp

theorem stateRemainder_bounds
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (x : InventoryState (DyadicNode L) m) :
    0 ≤ stateRemainder a x ∧
      stateRemainder a x ≤
        ∑ d ∈ Finset.range L, stateHazardEnergy a x (d + 1) ∧
      (∑ d ∈ Finset.range L, stateHazardEnergy a x (d + 1)) ≤
        (L : ℝ) * stateHazardEnergy a x L :=
  ⟨stateRemainder_nonneg a ha hm x,
    stateRemainder_le_sum_hazardEnergy a ha hm x,
    sum_stateHazardEnergy_le_depth_mul a ha x⟩

theorem statePotential_nonneg
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m) :
    0 ≤ statePotential a x :=
  globalHarmonicPotential_nonneg ha

theorem statePotential_le_log_one_add
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m) :
    statePotential a x ≤ Real.log (1 + (m : ℝ) / a) := by
  exact globalHarmonicPotential_le_log_one_add ha
    (countLabel_le_total_all x)

theorem statePotential_bounds
    (a : ℝ) (ha : 0 < a)
    (x : InventoryState (DyadicNode L) m) :
    0 ≤ statePotential a x ∧
      statePotential a x ≤ Real.log (1 + (m : ℝ) / a) :=
  ⟨statePotential_nonneg a ha x,
    statePotential_le_log_one_add a ha x⟩

end HierarchicalDynamics

end

end FD1D
