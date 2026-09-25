/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.Basic

/-! # Tree -/

@[expose] public section

namespace FD1D

noncomputable section

/-!
# Complete dyadic trees

Nodes at depth `d` are numbered from left to right by `Fin (2 ^ d)`.
The module supplies the finite-tree bookkeeping used by the hazard and
Bellman arguments. All global estimates are consequences of explicit local
hypotheses; no policy-specific algebra is hidden here.
-/

/-- Nodes of the complete dyadic tree at depth `d`. -/
abbrev DyadicNode (d : ℕ) := Fin (2 ^ d)

/-- The unique node at depth zero. -/
def dyadicRoot : DyadicNode 0 := 0

/-- Splitting a level into the two children of every node. -/
def childrenEquiv (d : ℕ) : DyadicNode d × Fin 2 ≃ DyadicNode (d + 1) :=
  finProdFinEquiv.trans (finCongr (by simp [pow_succ]))

/-- The left child of a dyadic node. -/
def leftChild {d : ℕ} (v : DyadicNode d) : DyadicNode (d + 1) :=
  childrenEquiv d (v, 0)

/-- The right child of a dyadic node. -/
def rightChild {d : ℕ} (v : DyadicNode d) : DyadicNode (d + 1) :=
  childrenEquiv d (v, 1)

@[simp] theorem leftChild_val {d : ℕ} (v : DyadicNode d) :
    (leftChild v).val = 2 * v.val := by
  simp [leftChild, childrenEquiv, finProdFinEquiv]

@[simp] theorem rightChild_val {d : ℕ} (v : DyadicNode d) :
    (rightChild v).val = 2 * v.val + 1 := by
  simp [rightChild, childrenEquiv, finProdFinEquiv]
  omega

/-- The parent of a nonroot node. -/
def parent {d : ℕ} (v : DyadicNode (d + 1)) : DyadicNode d :=
  (childrenEquiv d).symm v |>.1

@[simp] theorem parent_leftChild {d : ℕ} (v : DyadicNode d) :
    parent (leftChild v) = v := by
  simp [parent, leftChild]

@[simp] theorem parent_rightChild {d : ℕ} (v : DyadicNode d) :
    parent (rightChild v) = v := by
  simp [parent, rightChild]

theorem leftChild_ne_rightChild {d : ℕ} (v : DyadicNode d) :
    leftChild v ≠ rightChild v := by
  intro h
  have hs := congrArg (fun x => x.2.val) ((childrenEquiv d).injective h)
  norm_num at hs

/--
Every node at level `d+1` occurs exactly once as a left or right child.
This is the basic child-partition identity for finite sums.
-/
theorem sum_children {M : Type*} [AddCommMonoid M] (d : ℕ)
    (f : DyadicNode (d + 1) → M) :
    ∑ w, f w = ∑ v, (f (leftChild v) + f (rightChild v)) := by
  calc
    ∑ w, f w = ∑ x : DyadicNode d × Fin 2, f (childrenEquiv d x) := by
      symm
      exact (childrenEquiv d).sum_comp f
    _ = ∑ v, ∑ side : Fin 2, f (childrenEquiv d (v, side)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ v, (f (leftChild v) + f (rightChild v)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Fin.sum_univ_two]
      rfl

/--
At levels `d ≤ L`, a leaf is uniquely a pair consisting of a depth-`d`
ancestor and an offset in that ancestor's consecutive leaf block.
-/
def descendantsEquiv {d L : ℕ} (hdL : d ≤ L) :
    DyadicNode d × Fin (2 ^ (L - d)) ≃ DyadicNode L :=
  finProdFinEquiv.trans (finCongr (by
    calc
      2 ^ d * 2 ^ (L - d) = 2 ^ (d + (L - d)) := by
        rw [pow_add]
      _ = 2 ^ L := by rw [Nat.add_sub_of_le hdL]))

/-- The leaf with offset `j` in the block below `v`. -/
def descendantLeaf {d L : ℕ} (hdL : d ≤ L) (v : DyadicNode d)
    (j : Fin (2 ^ (L - d))) : DyadicNode L :=
  descendantsEquiv hdL (v, j)

/-- Descendant blocks are consecutive in the left-to-right leaf numbering. -/
theorem descendantLeaf_val {d L : ℕ} (hdL : d ≤ L) (v : DyadicNode d)
    (j : Fin (2 ^ (L - d))) :
    (descendantLeaf hdL v j).val = v.val * 2 ^ (L - d) + j.val := by
  simp [descendantLeaf, descendantsEquiv, finProdFinEquiv]
  ac_rfl

/-- The embedding of offsets into the leaf block below one node. -/
def descendantEmbedding {d L : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    Fin (2 ^ (L - d)) ↪ DyadicNode L where
  toFun := descendantLeaf hdL v
  inj' := by
    intro i j hij
    have hp := (descendantsEquiv hdL).injective hij
    exact congrArg Prod.snd hp

/-- The consecutive block of depth-`L` leaves below `v`. -/
def leafBlock {d L : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    Finset (DyadicNode L) :=
  Finset.univ.map (descendantEmbedding hdL v)

@[simp] theorem card_leafBlock {d L : ℕ} (hdL : d ≤ L)
    (v : DyadicNode d) :
    (leafBlock hdL v).card = 2 ^ (L - d) := by
  simp [leafBlock]

theorem mem_leafBlock_iff {d L : ℕ} (hdL : d ≤ L)
    (v : DyadicNode d) (w : DyadicNode L) :
    w ∈ leafBlock hdL v ↔
      ∃ j : Fin (2 ^ (L - d)), descendantLeaf hdL v j = w := by
  rw [leafBlock, Finset.mem_map]
  simp only [Finset.mem_univ, true_and]
  change (∃ j, descendantLeaf hdL v j = w) ↔ _
  rfl

/-- Membership in a descendant block, expressed as a half-open index interval. -/
theorem mem_leafBlock_interval {d L : ℕ} (hdL : d ≤ L)
    (v : DyadicNode d) (w : DyadicNode L) :
    w ∈ leafBlock hdL v ↔
      v.val * 2 ^ (L - d) ≤ w.val ∧
        w.val < (v.val + 1) * 2 ^ (L - d) := by
  rw [mem_leafBlock_iff]
  constructor
  · rintro ⟨j, rfl⟩
    rw [descendantLeaf_val]
    constructor
    · omega
    · have := j.isLt
      simp [Nat.add_mul]
  · intro hw
    simp only [Nat.add_mul, one_mul] at hw
    have hk : 0 < 2 ^ (L - d) := Nat.two_pow_pos _
    let j : Fin (2 ^ (L - d)) :=
      ⟨w.val - v.val * 2 ^ (L - d), by omega⟩
    refine ⟨j, Fin.ext ?_⟩
    rw [descendantLeaf_val]
    dsimp [j]
    omega

/-- Distinct nodes at one level have disjoint descendant leaf blocks. -/
theorem leafBlock_disjoint {d L : ℕ} (hdL : d ≤ L)
    {v w : DyadicNode d} (hvw : v ≠ w) :
    Disjoint (leafBlock hdL v) (leafBlock hdL w) := by
  rw [Finset.disjoint_left]
  intro z hzv hzw
  rw [mem_leafBlock_iff] at hzv hzw
  obtain ⟨i, hi⟩ := hzv
  obtain ⟨j, hj⟩ := hzw
  have hp : (v, i) = (w, j) := by
    apply (descendantsEquiv hdL).injective
    exact hi.trans hj.symm
  exact hvw (congrArg Prod.fst hp)

/-- Every leaf belongs to a unique block at every shallower level. -/
theorem existsUnique_leafBlock {d L : ℕ} (hdL : d ≤ L)
    (w : DyadicNode L) :
    ∃! v : DyadicNode d, w ∈ leafBlock hdL v := by
  let x := (descendantsEquiv hdL).symm w
  refine ⟨x.1, ?_, ?_⟩
  · change w ∈ leafBlock hdL x.1
    rw [mem_leafBlock_iff]
    exact ⟨x.2, (descendantsEquiv hdL).apply_symm_apply w⟩
  · intro v hv
    rw [mem_leafBlock_iff] at hv
    obtain ⟨j, hj⟩ := hv
    have hp : (v, j) = x := by
      have hj' : descendantsEquiv hdL (v, j) = w := hj
      have hx : descendantsEquiv hdL x = w := by
        simp [x]
      apply (descendantsEquiv hdL).injective
      exact hj'.trans hx.symm
    exact congrArg Prod.fst hp

/-- A parent's leaf block is the disjoint union of its children's blocks. -/
theorem leafBlock_children {d L : ℕ} (hdL : d < L)
    (v : DyadicNode d) :
    leafBlock (Nat.le_of_lt hdL) v =
      leafBlock (show d + 1 ≤ L by omega) (leftChild v) ∪
        leafBlock (show d + 1 ≤ L by omega) (rightChild v) := by
  ext w
  rw [Finset.mem_union]
  rw [mem_leafBlock_interval, mem_leafBlock_interval, mem_leafBlock_interval]
  have hsub : L - d = (L - (d + 1)) + 1 := by omega
  rw [hsub, pow_succ]
  simp [Nat.add_mul]
  ring_nf
  omega

/-- Interval mass of every node at depth `d`. -/
def nodeMass (d : ℕ) (_ : DyadicNode d) : ℝ :=
  ((2 : ℝ) ^ d)⁻¹

theorem nodeMass_pos (d : ℕ) (v : DyadicNode d) :
    0 < nodeMass d v := by
  simp [nodeMass]

theorem nodeMass_nonneg (d : ℕ) (v : DyadicNode d) :
    0 ≤ nodeMass d v :=
  (nodeMass_pos d v).le

@[simp] theorem nodeMass_root :
    nodeMass 0 dyadicRoot = 1 := by
  simp [nodeMass]

/-- Each child has half its parent's interval mass. -/
theorem nodeMass_child {d : ℕ} (v : DyadicNode d) (side : Fin 2) :
    nodeMass (d + 1) (childrenEquiv d (v, side)) = nodeMass d v / 2 := by
  simp [nodeMass, pow_succ]
  ring

@[simp] theorem nodeMass_leftChild {d : ℕ} (v : DyadicNode d) :
    nodeMass (d + 1) (leftChild v) = nodeMass d v / 2 :=
  nodeMass_child v 0

@[simp] theorem nodeMass_rightChild {d : ℕ} (v : DyadicNode d) :
    nodeMass (d + 1) (rightChild v) = nodeMass d v / 2 :=
  nodeMass_child v 1

/-- Node masses at every complete level sum to one. -/
theorem sum_nodeMass (d : ℕ) :
    ∑ v : DyadicNode d, nodeMass d v = 1 := by
  simp [nodeMass]

/-! ## Inventory and coherent labels -/

/-- A leaf inventory vector with a prescribed total inventory `m`. -/
structure LeafInventory (L m : ℕ) where
  /-- Number of inventory items in each leaf of the dyadic tree. -/
  count : DyadicNode L → ℕ
  total_count : ∑ v, count v = m

/--
Aggregated counts at every level. The explicit child equation states exactly
that each internal count is the sum of the inventory in its two child blocks.
-/
structure AggregatedInventory (L m : ℕ) where
  /-- Inventory at the finest dyadic level. -/
  leaf : LeafInventory L m
  /-- Aggregated inventory count at each dyadic level and node. -/
  count : ∀ d, DyadicNode d → ℕ
  count_leaf : count L = leaf.count
  count_children : ∀ d, d < L → ∀ v,
    count d v = count (d + 1) (leftChild v) +
      count (d + 1) (rightChild v)
  count_root : count 0 dyadicRoot = m

namespace LeafInventory

/-- Concrete aggregate of a leaf inventory over one descendant block. -/
def nodeCount {L m d : ℕ} (I : LeafInventory L m) (hdL : d ≤ L)
    (v : DyadicNode d) : ℕ :=
  ∑ w ∈ leafBlock hdL v, I.count w

@[simp] theorem nodeCount_leaf {L m : ℕ} (I : LeafInventory L m)
    (v : DyadicNode L) :
    I.nodeCount le_rfl v = I.count v := by
  have hblock : leafBlock (le_refl L) v = {v} := by
    ext w
    rw [mem_leafBlock_interval, Finset.mem_singleton]
    simp only [Nat.sub_self, pow_zero, mul_one]
    constructor
    · intro hw
      apply Fin.ext
      omega
    · rintro rfl
      omega
  simp [nodeCount, hblock]

@[simp] theorem nodeCount_root {L m : ℕ} (I : LeafInventory L m) :
    I.nodeCount (Nat.zero_le L) dyadicRoot = m := by
  have hblock : leafBlock (Nat.zero_le L) dyadicRoot = Finset.univ := by
    ext w
    rw [mem_leafBlock_interval]
    simp [dyadicRoot, w.isLt]
  simpa [nodeCount, hblock] using I.total_count

/-- Aggregated inventory counts satisfy the parent/children count identity. -/
theorem nodeCount_children {L m d : ℕ} (I : LeafInventory L m)
    (hdL : d < L) (v : DyadicNode d) :
    I.nodeCount (Nat.le_of_lt hdL) v =
      I.nodeCount (Nat.succ_le_iff.mpr hdL) (leftChild v) +
        I.nodeCount (Nat.succ_le_iff.mpr hdL) (rightChild v) := by
  rw [nodeCount, leafBlock_children hdL v]
  exact Finset.sum_union
    (leafBlock_disjoint (show d + 1 ≤ L by omega)
      (leftChild_ne_rightChild v))

/-- Every fixed-total leaf vector has canonical coherent aggregate counts. -/
def aggregate {L m : ℕ} (I : LeafInventory L m) :
    AggregatedInventory L m where
  leaf := I
  count d v := if hdL : d ≤ L then I.nodeCount hdL v else 0
  count_leaf := by
    funext v
    simp
  count_children d hdL v := by
    simp only [dite_eq_left (Nat.le_of_lt hdL),
      dite_eq_left (Nat.succ_le_iff.mpr hdL)]
    exact I.nodeCount_children hdL v
  count_root := by
    simp

end LeafInventory

/--
An abstract additive tree labeling. It is useful for `q`, inventory counts,
or any other quantity whose parent is the sum of its children.
-/
structure CoherentTreeLabel (L : ℕ) (A : Type*) [AddCommMonoid A] where
  /-- Node labels whose parent value is the sum of its child values. -/
  value : ∀ d, DyadicNode d → A
  children : ∀ d, d < L → ∀ v,
    value d v = value (d + 1) (leftChild v) +
      value (d + 1) (rightChild v)

/-- Sum of a depth-indexed label over one complete level. -/
def levelSum {A : Type*} [AddCommMonoid A]
    (f : ∀ d, DyadicNode d → A) (d : ℕ) : A :=
  ∑ v, f d v

theorem levelSum_succ {A : Type*} [AddCommMonoid A]
    (f : ∀ d, DyadicNode d → A) (d : ℕ) :
    levelSum f (d + 1) =
      ∑ v, (f (d + 1) (leftChild v) + f (d + 1) (rightChild v)) := by
  exact sum_children d (f (d + 1))

theorem CoherentTreeLabel.levelSum_eq_root
    {L : ℕ} {A : Type*} [AddCommMonoid A]
    (f : CoherentTreeLabel L A) {d : ℕ} (hdL : d ≤ L) :
    levelSum f.value d = f.value 0 dyadicRoot := by
  induction d with
  | zero =>
      exact Fin.sum_univ_one (f.value 0)
  | succ d ih =>
      rw [levelSum_succ]
      simp_rw [← f.children d (by omega)]
      exact ih (by omega)

theorem AggregatedInventory.level_count_eq
    {L m : ℕ} (I : AggregatedInventory L m) {d : ℕ} (hdL : d ≤ L) :
    ∑ v, I.count d v = m := by
  let f : CoherentTreeLabel L ℕ :=
    { value := I.count
      children := I.count_children }
  rw [show (∑ v, I.count d v) = levelSum f.value d by rfl]
  rw [f.levelSum_eq_root hdL]
  exact I.count_root

theorem AggregatedInventory.leaf_count_eq_total
    {L m : ℕ} (I : AggregatedInventory L m) :
    ∑ v, I.count L v = m :=
  I.level_count_eq le_rfl

/-! ## Weighted telescopes -/

/-- Mass-weighted sum of a real label over one complete level. -/
def weightedLevel (f : ∀ d, DyadicNode d → ℝ) (d : ℕ) : ℝ :=
  ∑ v, nodeMass d v * f d v

@[simp] theorem weightedLevel_zero (f : ∀ d, DyadicNode d → ℝ) :
    weightedLevel f 0 = f 0 dyadicRoot := by
  unfold weightedLevel
  change (∑ v : Fin 1, nodeMass 0 v * f 0 v) = f 0 dyadicRoot
  rw [Fin.sum_univ_one]
  simp [nodeMass, dyadicRoot]

/-- Arithmetic mean of a real label over the two children of `v`. -/
def childAverage (f : ∀ d, DyadicNode d → ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  (f (d + 1) (leftChild v) + f (d + 1) (rightChild v)) / 2

/-- A child average weighted at the parent equals the next weighted level. -/
theorem weighted_childAverage_sum
    (f : ∀ d, DyadicNode d → ℝ) (d : ℕ) :
    ∑ v, nodeMass d v * childAverage f d v = weightedLevel f (d + 1) := by
  rw [weightedLevel, sum_children]
  apply Finset.sum_congr rfl
  intro v _
  simp only [childAverage, nodeMass_leftChild, nodeMass_rightChild]
  ring

theorem weighted_local_sum
    (f : ∀ d, DyadicNode d → ℝ) (d : ℕ) :
    ∑ v, nodeMass d v * (childAverage f d v - f d v) =
      weightedLevel f (d + 1) - weightedLevel f d := by
  rw [show (∑ v, nodeMass d v * (childAverage f d v - f d v)) =
      (∑ v, nodeMass d v * childAverage f d v) -
        ∑ v, nodeMass d v * f d v by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _
      ring]
  rw [weighted_childAverage_sum]
  rfl

/-- Generic mass-weighted telescope over all internal nodes. -/
theorem weighted_tree_telescope
    (f : ∀ d, DyadicNode d → ℝ) (L : ℕ) :
    ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v * (childAverage f d v - f d v) =
      weightedLevel f L - f 0 dyadicRoot := by
  simp_rw [weighted_local_sum]
  rw [Finset.sum_range_sub]
  rw [weightedLevel_zero]

/-- Sum of a mass-weighted label over all nonroot levels through `L`. -/
def nonrootWeightedSum (f : ∀ d, DyadicNode d → ℝ) (L : ℕ) : ℝ :=
  ∑ d ∈ Finset.range L, weightedLevel f (d + 1)

/-- Sum of a mass-weighted label over all internal levels before `L`. -/
def internalWeightedSum (f : ∀ d, DyadicNode d → ℝ) (L : ℕ) : ℝ :=
  ∑ d ∈ Finset.range L, weightedLevel f d

/-- The hazard energy `H_d = ∑_{depth(v)=d} p_v h_v²`. -/
def hazardEnergy (h : ∀ d, DyadicNode d → ℝ) (d : ℕ) : ℝ :=
  weightedLevel (fun d v => (h d v) ^ 2) d

theorem hazardEnergy_root (h : ∀ d, DyadicNode d → ℝ) :
    hazardEnergy h 0 = (h 0 dyadicRoot) ^ 2 := by
  exact weightedLevel_zero (fun d v => (h d v) ^ 2)

/-- Exact hazard-energy telescope behind equations (1) and (2). -/
theorem hazard_energy_telescope
    (h : ∀ d, DyadicNode d → ℝ) (L : ℕ) :
    ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2) =
      hazardEnergy h L - hazardEnergy h 0 := by
  rw [hazardEnergy_root]
  exact weighted_tree_telescope (fun d v => (h d v) ^ 2) L

/--
Summing the local hazard inequality gives equation (2), before substituting
the root value `h_root = 1/m`.
-/
theorem hazard_energy_bound
    (L : ℕ) (a : ℝ)
    (h b : ∀ d, DyadicNode d → ℝ)
    (hlocal : ∀ d, d < L → ∀ v,
      (b d v) ^ 2 ≤ 2 * a ^ 2 *
        (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2)) :
    internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
      2 * a ^ 2 * (hazardEnergy h L - hazardEnergy h 0) := by
  have hs :
      internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
        ∑ d ∈ Finset.range L,
          ∑ v, nodeMass d v * (2 * a ^ 2 *
            (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2)) := by
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left
      (hlocal d (Finset.mem_range.mp hd) v) (nodeMass_nonneg d v)
  calc
    internalWeightedSum (fun d v => (b d v) ^ 2) L
        ≤ _ := hs
    _ = 2 * a ^ 2 *
        (∑ d ∈ Finset.range L,
          ∑ v, nodeMass d v *
            (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2)) := by
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = 2 * a ^ 2 * (hazardEnergy h L - hazardEnergy h 0) := by
      rw [hazard_energy_telescope]

/--
Equation (2) directly from equation (1), with the latter stated in its
displayed divided form.
-/
theorem hazard_energy_bound_from_local
    (L : ℕ) {a : ℝ}
    (h b : ∀ d, DyadicNode d → ℝ) (ha : a ≠ 0)
    (hlocal : ∀ d, d < L → ∀ v,
      (b d v) ^ 2 / (2 * a ^ 2) ≤
        childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2) :
    internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
      2 * a ^ 2 * (hazardEnergy h L - hazardEnergy h 0) := by
  apply hazard_energy_bound L a h b
  intro d hdL v
  have hden : 0 < 2 * a ^ 2 := by positivity
  simpa [mul_comm] using (div_le_iff₀ hden).mp (hlocal d hdL v)

/-- Equation (2) with `H₀ = m⁻²`. -/
theorem hazard_energy_bound_of_root
    (L : ℕ) {a m : ℝ} (h b : ∀ d, DyadicNode d → ℝ)
    (hm : m ≠ 0) (hroot : h 0 dyadicRoot = 1 / m)
    (hlocal : ∀ d, d < L → ∀ v,
      (b d v) ^ 2 ≤ 2 * a ^ 2 *
        (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2)) :
    internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
      2 * a ^ 2 * (hazardEnergy h L - 1 / m ^ 2) := by
  have hbound := hazard_energy_bound L a h b hlocal
  have hH0 : hazardEnergy h 0 = 1 / m ^ 2 := by
    rw [hazardEnergy_root, hroot]
    field_simp
  rwa [hH0] at hbound

/-! ## Bellman telescope and deterministic estimate -/

/--
The exact generic Bellman telescope. `c` is the child cost (`t Z` in the
paper), while `B` is any node potential.
-/
theorem bellman_tree_telescope
    (c B : ∀ d, DyadicNode d → ℝ) (L : ℕ) :
    ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (childAverage c d v + childAverage B d v - B d v) =
      nonrootWeightedSum c L + weightedLevel B L - B 0 dyadicRoot := by
  have hlevel : ∀ d,
      (∑ v, nodeMass d v *
        (childAverage c d v + childAverage B d v - B d v)) =
        weightedLevel c (d + 1) +
          (weightedLevel B (d + 1) - weightedLevel B d) := by
    intro d
    rw [show (∑ v, nodeMass d v *
        (childAverage c d v + childAverage B d v - B d v)) =
        (∑ v, nodeMass d v * childAverage c d v) +
        ∑ v, nodeMass d v * (childAverage B d v - B d v) by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v _
          ring]
    rw [weighted_childAverage_sum, weighted_local_sum]
  simp_rw [hlevel]
  rw [Finset.sum_add_distrib, Finset.sum_range_sub]
  rw [weightedLevel_zero]
  simp only [nonrootWeightedSum]
  ring

/--
Global form of the local Bellman inequality (7). This is the telescope used
immediately before equation (9).
-/
theorem bellman_global_bound
    (L : ℕ) (h t Z B : ∀ d, DyadicNode d → ℝ)
    (hlocal : ∀ d, d < L → ∀ v,
      childAverage (fun d v => t d v * Z d v) d v +
          childAverage B d v - B d v ≥
        (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2) / 100) :
    nonrootWeightedSum (fun d v => t d v * Z d v) L ≥
      (hazardEnergy h L - hazardEnergy h 0) / 100 +
        B 0 dyadicRoot - weightedLevel B L := by
  have hs :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => t d v * Z d v) d v +
            childAverage B d v - B d v))) ≥
      ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => (h d v) ^ 2) d v -
            (h d v) ^ 2) / 100) := by
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left
      (hlocal d (Finset.mem_range.mp hd) v) (nodeMass_nonneg d v)
  rw [bellman_tree_telescope] at hs
  have henergy := hazard_energy_telescope h L
  rw [← henergy]
  have hdiv :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (childAverage (fun d v => (h d v) ^ 2) d v -
            (h d v) ^ 2)) / 100 =
        ∑ d ∈ Finset.range L,
          ∑ v, nodeMass d v *
            ((childAverage (fun d v => (h d v) ^ 2) d v -
              (h d v) ^ 2) / 100) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v _
    ring
  calc
    (∑ d ∈ Finset.range L,
      ∑ v, nodeMass d v *
        (childAverage (fun d v => (h d v) ^ 2) d v -
          (h d v) ^ 2)) / 100 +
        B 0 dyadicRoot - weightedLevel B L
        = (∑ d ∈ Finset.range L,
            ∑ v, nodeMass d v *
              ((childAverage (fun d v => (h d v) ^ 2) d v -
                (h d v) ^ 2) / 100)) +
            B 0 dyadicRoot - weightedLevel B L := by
              rw [hdiv]
    _ ≤ nonrootWeightedSum (fun d v => t d v * Z d v) L := by
      linarith

/-- The drift quantity `D` from equation (9). -/
def bellmanDrift
    (L : ℕ) (a : ℝ)
    (N q : ∀ d, DyadicNode d → ℝ) : ℝ :=
  ∑ d ∈ Finset.range L,
    ∑ v : DyadicNode (d + 1),
      (nodeMass (d + 1) v) ^ 2 *
        (nodeMass (d + 1) v - q (d + 1) v) /
          (N (d + 1) v + a)

theorem bellman_cost_eq_drift_div
    (L : ℕ) (a : ℝ)
    (N q t Z : ∀ d, DyadicNode d → ℝ)
    (ht : ∀ d v, t d v = (nodeMass d v - q d v) / a)
    (hZ : ∀ d v, Z d v = nodeMass d v / (N d v + a)) :
    nonrootWeightedSum (fun d v => t d v * Z d v) L =
      bellmanDrift L a N q / a := by
  simp_rw [nonrootWeightedSum, weightedLevel, bellmanDrift, ht, hZ,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro v _
  ring

/--
The deterministic Bellman estimate (9). The hypotheses are exactly the
local certificate (7), the definitions of `t` and `Z`, and the terminal/root
sign bounds proved in the paper.
-/
theorem deterministic_bellman_bound
    (L : ℕ) {a m : ℝ} (N q h t Z B : ∀ d, DyadicNode d → ℝ)
    (ha : 0 < a) (hm : 0 < m)
    (ht : ∀ d v, t d v = (nodeMass d v - q d v) / a)
    (hZ : ∀ d v, Z d v = nodeMass d v / (N d v + a))
    (hroot : h 0 dyadicRoot = 1 / m)
    (hlocal : ∀ d, d < L → ∀ v,
      childAverage (fun d v => t d v * Z d v) d v +
          childAverage B d v - B d v ≥
        (childAverage (fun d v => (h d v) ^ 2) d v -
          (h d v) ^ 2) / 100)
    (hleaf : ∀ v : DyadicNode L, B L v ≤ 0)
    (hBroot : -(1 / (3 * m ^ 2)) ≤ B 0 dyadicRoot) :
    bellmanDrift L a N q ≥
      a * (hazardEnergy h L / 100 - 103 / (300 * m ^ 2)) := by
  have hglobal := bellman_global_bound L h t Z B hlocal
  rw [bellman_cost_eq_drift_div L a N q t Z ht hZ] at hglobal
  have hleafsum : weightedLevel B L ≤ 0 := by
    apply Finset.sum_nonpos
    intro v _
    exact mul_nonpos_of_nonneg_of_nonpos (nodeMass_nonneg L v) (hleaf v)
  have hH0 : hazardEnergy h 0 = 1 / m ^ 2 := by
    rw [hazardEnergy_root, hroot]
    field_simp
  rw [hH0] at hglobal
  have hlower :
      hazardEnergy h L / 100 - 103 / (300 * m ^ 2) ≤
        bellmanDrift L a N q / a := by
    have hpre :
        (hazardEnergy h L - 1 / m ^ 2) / 100 -
            1 / (3 * m ^ 2) ≤ bellmanDrift L a N q / a := by
      linarith
    have heq :
        (hazardEnergy h L - 1 / m ^ 2) / 100 -
            1 / (3 * m ^ 2) =
          hazardEnergy h L / 100 - 103 / (300 * m ^ 2) := by
      field_simp
      ring
    rwa [← heq]
  have := (le_div_iff₀ ha).mp hlower
  nlinarith

/-! ## Squared masses -/

/-- Squared interval masses on level `d` sum to `2⁻ᵈ`. -/
theorem sum_nodeMass_sq (d : ℕ) :
    ∑ v : DyadicNode d, (nodeMass d v) ^ 2 = ((2 : ℝ) ^ d)⁻¹ := by
  simp [nodeMass]
  field_simp

/-- Sum of `p_v²` over every nonroot node through depth `L`. -/
def nonrootMassSqSum (L : ℕ) : ℝ :=
  ∑ d ∈ Finset.range L,
    ∑ v : DyadicNode (d + 1), (nodeMass (d + 1) v) ^ 2

/-- `∑_{v ≠ root} p_v² = 1 - 1/n` for `n = 2^L`. -/
theorem sum_nonroot_nodeMass_sq (L : ℕ) :
    nonrootMassSqSum L = 1 - 1 / (2 ^ L : ℝ) := by
  induction L with
  | zero =>
      simp [nonrootMassSqSum]
  | succ L ih =>
      rw [nonrootMassSqSum, Finset.sum_range_succ, sum_nodeMass_sq]
      rw [show (∑ d ∈ Finset.range L,
          ∑ v : DyadicNode (d + 1), (nodeMass (d + 1) v) ^ 2) =
          nonrootMassSqSum L by rfl, ih]
      simp only [pow_succ]
      field_simp
      ring

end

end FD1D
