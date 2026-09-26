/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.Hazard
public import LeanPool.FullyDynamicMatching.FD1D.Tree
public import LeanPool.FullyDynamicMatching.FD1D.Bellman

/-! # Policy -/

@[expose] public section

namespace FD1D

noncomputable section

/-!
# The hierarchical deletion policy

This module assembles the local two-child formulas into labels on a complete
dyadic tree. Counts come from a coherent `AggregatedInventory`; hazards are
defined recursively from the root, and all other policy quantities are then
derived from the counts and hazards.
-/

namespace HierarchicalPolicy

open LocalHazard

variable {L m : ℕ}

/-- Select the appropriate extended child hazard. -/
def childHazard (a h : ℝ) (x y : ℕ) (side : Fin 2) : ℝ :=
  if side = 0 then hL a h x y else hR a h x y

/-- The recursively propagated extended hazard, rooted at `1 / m`. -/
def hazard (I : AggregatedInventory L m) (a : ℝ) :
    ∀ d, DyadicNode d → ℝ
  | 0, _ => 1 / (m : ℝ)
  | d + 1, w =>
      let z := (childrenEquiv d).symm w
      childHazard a (hazard I a d z.1)
        (I.count (d + 1) (leftChild z.1))
        (I.count (d + 1) (rightChild z.1)) z.2

/-- Inventory counts, coerced to reals. -/
def inventory (I : AggregatedInventory L m) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  I.count d v

/-- Conditional left-child deletion probability at an internal node. -/
def splitLeft (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  dL a (I.count (d + 1) (leftChild v))
    (I.count (d + 1) (rightChild v))

/-- Conditional right-child deletion probability at an internal node. -/
def splitRight (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  dR a (I.count (d + 1) (leftChild v))
    (I.count (d + 1) (rightChild v))

/-- Deletion mass `q_v = N_v h_v`. -/
def deletionMass (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  inventory I d v * hazard I a d v

/-- Interval mass `p_v`. -/
def intervalMass (d : ℕ) (v : DyadicNode d) : ℝ :=
  nodeMass d v

/-- Discrepancy `t_v = (p_v - q_v) / a`. -/
def discrepancy (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  (intervalMass d v - deletionMass I a d v) / a

/-- Reciprocal regularized count `Z_v = p_v / (N_v + a)`. -/
def regularizedMass (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  intervalMass d v / (inventory I d v + a)

/-- The normalized Bellman coordinate `y_v = Z_v / h_v`. -/
def bellmanY (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  regularizedMass I a d v / hazard I a d v

/-- The scalar weight in the Bellman function. -/
def bellmanWeight (y : ℝ) : ℝ := FD1D.d y

/-- The Bellman function from equation (6). -/
def bellmanFunction (h t y : ℝ) : ℝ := FD1D.B h t y

/-- The Bellman value attached to a policy node. -/
def bellmanValue (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  bellmanFunction (hazard I a d v) (discrepancy I a d v)
    (bellmanY I a d v)

@[simp] theorem hazard_root (I : AggregatedInventory L m) (a : ℝ) :
    hazard I a 0 dyadicRoot = 1 / (m : ℝ) :=
  rfl

@[simp] theorem hazard_leftChild (I : AggregatedInventory L m) (a : ℝ)
    (d : ℕ) (v : DyadicNode d) :
    hazard I a (d + 1) (leftChild v) =
      hL a (hazard I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  simp [hazard, childHazard, leftChild]

@[simp] theorem hazard_rightChild (I : AggregatedInventory L m) (a : ℝ)
    (d : ℕ) (v : DyadicNode d) :
    hazard I a (d + 1) (rightChild v) =
      hR a (hazard I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  simp [hazard, childHazard, rightChild, show (1 : Fin 2) ≠ 0 by decide]

@[simp] theorem intervalMass_root :
    intervalMass 0 dyadicRoot = 1 := by
  simp [intervalMass]

@[simp] theorem intervalMass_leftChild (d : ℕ) (v : DyadicNode d) :
    intervalMass (d + 1) (leftChild v) = intervalMass d v / 2 := by
  simp [intervalMass]

@[simp] theorem intervalMass_rightChild (d : ℕ) (v : DyadicNode d) :
    intervalMass (d + 1) (rightChild v) = intervalMass d v / 2 := by
  simp [intervalMass]

theorem inventory_children (I : AggregatedInventory L m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    inventory I d v =
      inventory I (d + 1) (leftChild v) +
        inventory I (d + 1) (rightChild v) := by
  unfold inventory
  exact_mod_cast I.count_children d hdL v

theorem split_add (I : AggregatedInventory L m) {a : ℝ} (ha : 0 < a)
    (d : ℕ) (v : DyadicNode d) :
    splitLeft I a d v + splitRight I a d v = 1 := by
  exact dL_add_dR ha

theorem hazard_pos (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    ∀ d, d ≤ L → ∀ v, 0 < hazard I a d v := by
  intro d
  induction d with
  | zero =>
      intro _ v
      simp [hazard, Nat.cast_pos.mpr hm]
  | succ d ih =>
      intro hdL w
      let z := (childrenEquiv d).symm w
      have hz : childrenEquiv d z = w := (childrenEquiv d).apply_symm_apply w
      have hp : 0 < hazard I a d z.1 := ih (by omega) z.1
      rw [← hz]
      rcases z with ⟨v, side⟩
      fin_cases side
      · change 0 < hazard I a (d + 1) (leftChild v)
        rw [hazard_leftChild]
        exact hL_pos ha hp
      · change 0 < hazard I a (d + 1) (rightChild v)
        rw [hazard_rightChild]
        exact hR_pos ha hp

theorem deletionMass_eq_count_mul_hazard
    (I : AggregatedInventory L m) (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    deletionMass I a d v =
      (I.count d v : ℝ) * hazard I a d v :=
  rfl

theorem deletionMass_leftChild (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (d : ℕ) (hdL : d < L)
    (v : DyadicNode d) :
    deletionMass I a (d + 1) (leftChild v) =
      deletionMass I a d v * splitLeft I a d v := by
  let x := I.count (d + 1) (leftChild v)
  let y := I.count (d + 1) (rightChild v)
  have hcount : I.count d v = x + y := I.count_children d hdL v
  have hq :
      deletionMass I a d v =
        N x y * hazard I a d v := by
    simp only [deletionMass, inventory, hcount, N]
    norm_num
  simpa [deletionMass, inventory, splitLeft, x, y] using
    (q_mul_dL_eq_count_mul_hL (a := a) ha hq).symm

theorem deletionMass_rightChild (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (d : ℕ) (hdL : d < L)
    (v : DyadicNode d) :
    deletionMass I a (d + 1) (rightChild v) =
      deletionMass I a d v * splitRight I a d v := by
  let x := I.count (d + 1) (leftChild v)
  let y := I.count (d + 1) (rightChild v)
  have hcount : I.count d v = x + y := I.count_children d hdL v
  have hq :
      deletionMass I a d v =
        N x y * hazard I a d v := by
    simp only [deletionMass, inventory, hcount, N]
    norm_num
  simpa [deletionMass, inventory, splitRight, x, y] using
    (q_mul_dR_eq_count_mul_hR (a := a) ha hq).symm

theorem deletionMass_children (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (d : ℕ) (hdL : d < L)
    (v : DyadicNode d) :
    deletionMass I a d v =
      deletionMass I a (d + 1) (leftChild v) +
        deletionMass I a (d + 1) (rightChild v) := by
  rw [deletionMass_leftChild I ha d hdL v,
    deletionMass_rightChild I ha d hdL v, ← mul_add, split_add I ha]
  ring

theorem deletionMass_root (I : AggregatedInventory L m) (a : ℝ)
    (hm : 0 < m) :
    deletionMass I a 0 dyadicRoot = 1 := by
  simp [deletionMass, inventory, I.count_root, hazard, ne_of_gt hm]

theorem deletionMass_nonneg (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    0 ≤ deletionMass I a d v := by
  exact mul_nonneg (Nat.cast_nonneg _) (hazard_pos I ha hm d hdL v).le

/-- At every complete level, the deletion masses form a probability vector. -/
theorem sum_deletionMass (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) :
    ∑ v, deletionMass I a d v = 1 := by
  let q : CoherentTreeLabel L ℝ :=
    { value := deletionMass I a
      children := deletionMass_children I ha }
  rw [show (∑ v, deletionMass I a d v) = levelSum q.value d by rfl]
  rw [q.levelSum_eq_root hdL]
  exact deletionMass_root I a hm

theorem leaf_deletionMass_nonneg (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (hm : 0 < m) (v : DyadicNode L) :
    0 ≤ deletionMass I a L v :=
  deletionMass_nonneg I ha hm le_rfl v

theorem sum_leaf_deletionMass (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (hm : 0 < m) :
    ∑ v : DyadicNode L, deletionMass I a L v = 1 :=
  sum_deletionMass I ha hm le_rfl

theorem leaf_deletionMass_eq_zero_of_count_eq_zero
    (I : AggregatedInventory L m) (a : ℝ) (v : DyadicNode L)
    (hv : I.count L v = 0) :
    deletionMass I a L v = 0 := by
  simp [deletionMass, inventory, hv]

theorem discrepancy_eq (I : AggregatedInventory L m) (a : ℝ)
    (d : ℕ) (v : DyadicNode d) :
    discrepancy I a d v =
      (nodeMass d v - deletionMass I a d v) / a :=
  rfl

theorem regularizedMass_eq (I : AggregatedInventory L m) (a : ℝ)
    (d : ℕ) (v : DyadicNode d) :
    regularizedMass I a d v =
      nodeMass d v / (inventory I d v + a) :=
  rfl

theorem discrepancy_root (I : AggregatedInventory L m) {a : ℝ}
    (_ha : 0 < a) (hm : 0 < m) :
    discrepancy I a 0 dyadicRoot = 0 := by
  rw [discrepancy_eq, deletionMass_root I a hm]
  simp only [nodeMass_root]
  simp

private theorem parent_local_data
    (I : AggregatedInventory L m) {a : ℝ} (_ha : 0 < a)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    let x := I.count (d + 1) (leftChild v)
    let y := I.count (d + 1) (rightChild v)
    inventory I d v = N x y ∧
      deletionMass I a d v = q (hazard I a d v) x y := by
  dsimp
  have hc := I.count_children d hdL v
  constructor <;> simp [inventory, deletionMass, N, q, hc]

theorem discrepancy_eq_local (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (d : ℕ) (hdL : d < L)
    (v : DyadicNode d) :
    discrepancy I a d v =
      t a (intervalMass d v) (hazard I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  rw [discrepancy]
  have hp := parent_local_data I ha d hdL v
  simp only at hp
  rw [hp.2]
  rfl

theorem discrepancy_leftChild (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (d : ℕ) (hdL : d < L)
    (v : DyadicNode d) :
    discrepancy I a (d + 1) (leftChild v) =
      tL a (intervalMass d v) (hazard I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  rw [discrepancy, intervalMass_leftChild,
    deletionMass_leftChild I ha d hdL v]
  have hp := parent_local_data I ha d hdL v
  simp only at hp
  rw [hp.2]
  rfl

theorem discrepancy_rightChild (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (d : ℕ) (hdL : d < L)
    (v : DyadicNode d) :
    discrepancy I a (d + 1) (rightChild v) =
      tR a (intervalMass d v) (hazard I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  rw [discrepancy, intervalMass_rightChild,
    deletionMass_rightChild I ha d hdL v]
  have hp := parent_local_data I ha d hdL v
  simp only at hp
  rw [hp.2]
  rfl

/-- The invariant `t_v / h_v ≤ 1/2`, propagated from the root. -/
theorem discrepancy_div_hazard_le_half
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    ∀ d, d ≤ L → ∀ v,
      discrepancy I a d v / hazard I a d v ≤ 1 / 2 := by
  intro d
  induction d with
  | zero =>
      intro _ v
      have hv : v = dyadicRoot := Fin.eq_zero v
      subst v
      rw [discrepancy_root I ha hm]
      simp
  | succ d ih =>
      intro hdL w
      let z := (childrenEquiv d).symm w
      have hz : childrenEquiv d z = w := (childrenEquiv d).apply_symm_apply w
      have hd : d < L := by omega
      have hparent : 0 < hazard I a d z.1 :=
        hazard_pos I ha hm d (by omega) z.1
      have hinv := ih (by omega) z.1
      rw [discrepancy_eq_local I ha d hd z.1] at hinv
      rw [← hz]
      rcases z with ⟨v, side⟩
      fin_cases side
      · change
          discrepancy I a (d + 1) (leftChild v) /
              hazard I a (d + 1) (leftChild v) ≤ 1 / 2
        rw [discrepancy_leftChild I ha d hd v, hazard_leftChild]
        exact
          (t_div_h_le_half_left (a := a)
            (p := intervalMass d v) (h := hazard I a d v)
            (x := I.count (d + 1) (leftChild v))
            (y := I.count (d + 1) (rightChild v)) ha hparent hinv)
      · change
          discrepancy I a (d + 1) (rightChild v) /
              hazard I a (d + 1) (rightChild v) ≤ 1 / 2
        rw [discrepancy_rightChild I ha d hd v, hazard_rightChild]
        exact
          (t_div_h_le_half_right (a := a)
            (p := intervalMass d v) (h := hazard I a d v)
            (x := I.count (d + 1) (leftChild v))
            (y := I.count (d + 1) (rightChild v)) ha hparent hinv)

/-- Equation (5), now available at every policy node. -/
theorem intervalMass_le_regularized_count_mul_hazard
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) {d : ℕ} (hdL : d ≤ L)
    (v : DyadicNode d) :
    intervalMass d v ≤
      (inventory I d v + a) * hazard I a d v := by
  have hh := hazard_pos I ha hm d hdL v
  have ht := discrepancy_div_hazard_le_half I ha hm d hdL v
  have ht' : discrepancy I a d v ≤ hazard I a d v / 2 := by
    have := (div_le_iff₀ hh).mp ht
    linarith
  rw [discrepancy] at ht'
  have := (div_le_iff₀ ha).mp ht'
  simp only [deletionMass, inventory] at this
  have hN : (0 : ℝ) ≤ (I.count d v : ℝ) := Nat.cast_nonneg _
  have hah : 0 ≤ a * hazard I a d v := mul_nonneg ha.le hh.le
  change intervalMass d v ≤
    ((I.count d v : ℝ) + a) * hazard I a d v
  nlinarith

theorem bellmanY_nonneg (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    0 ≤ bellmanY I a d v := by
  have hh := (hazard_pos I ha hm d hdL v).le
  have hden : 0 < inventory I d v + a := by
    dsimp [inventory]
    positivity
  exact div_nonneg (div_nonneg (nodeMass_nonneg d v) hden.le) hh

theorem bellmanY_le_one (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    bellmanY I a d v ≤ 1 := by
  have hh := hazard_pos I ha hm d hdL v
  have hden : 0 < inventory I d v + a := by
    dsimp [inventory]
    positivity
  rw [bellmanY, regularizedMass]
  apply (div_le_iff₀ hh).2
  apply (div_le_iff₀ hden).2
  simpa [mul_comm] using
    intervalMass_le_regularized_count_mul_hazard I ha hm hdL v

theorem discrepancy_div_hazard_le_bellmanY
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    discrepancy I a d v / hazard I a d v ≤ bellmanY I a d v := by
  have hh := hazard_pos I ha hm d hdL v
  have hden : 0 < inventory I d v + a := by
    dsimp [inventory]
    positivity
  have hbase :
      discrepancy I a d v ≤ regularizedMass I a d v := by
    rw [regularizedMass, discrepancy, deletionMass]
    apply (div_le_div_iff₀ ha hden).2
    have hmajor :=
      intervalMass_le_regularized_count_mul_hazard I ha hm hdL v
    have hN : 0 ≤ inventory I d v := Nat.cast_nonneg _
    nlinarith
  exact div_le_div_of_nonneg_right hbase hh.le

/-- The signed imbalance at an internal node. -/
def imbalance (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  deletionMass I a (d + 1) (leftChild v) -
    deletionMass I a (d + 1) (rightChild v)

theorem imbalance_eq_local (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (d : ℕ) (hdL : d < L)
    (v : DyadicNode d) :
    imbalance I a d v =
      b a (hazard I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  rw [imbalance, deletionMass_leftChild I ha d hdL v,
    deletionMass_rightChild I ha d hdL v]
  have hp := parent_local_data I ha d hdL v
  simp only at hp
  rw [hp.2]
  rfl

/-- The local inequality whose tree sum is the hazard-energy bound. -/
theorem local_hazard_inequality
    (I : AggregatedInventory L m) {a : ℝ} (ha : 0 < a)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    (imbalance I a d v) ^ 2 ≤
      2 * a ^ 2 *
        (childAverage (fun d v => (hazard I a d v) ^ 2) d v -
          (hazard I a d v) ^ 2) := by
  have hlocal :=
    hazardIncrement_ge
      (h := hazard I a d v)
      (x := I.count (d + 1) (leftChild v))
      (y := I.count (d + 1) (rightChild v)) ha
  rw [imbalance_eq_local I ha d hdL v]
  unfold childAverage
  simp only [hazard_leftChild, hazard_rightChild]
  simpa [mul_comm] using
    (div_le_iff₀ (by positivity : 0 < 2 * a ^ 2)).mp hlocal

theorem hazard_energy_bound
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    internalWeightedSum (fun d v => (imbalance I a d v) ^ 2) L ≤
      2 * a ^ 2 *
        (FD1D.hazardEnergy (hazard I a) L - 1 / (m : ℝ) ^ 2) := by
  exact hazard_energy_bound_of_root L (hazard I a) (imbalance I a)
    (mod_cast (ne_of_gt hm)) (hazard_root I a)
    (local_hazard_inequality I ha)

/--
The one isolated interface to the polynomial Bellman certificate. A module
importing both this policy and `FD1D.Bellman` can prove this proposition from
`FD1D.local_bellman_inequality`; no certificate algebra is duplicated here.
-/
def LocalBellmanHypothesis (I : AggregatedInventory L m) (a : ℝ) : Prop :=
  ∀ d, d < L → ∀ v,
    childAverage
          (fun d v => discrepancy I a d v * regularizedMass I a d v) d v +
        childAverage (bellmanValue I a) d v - bellmanValue I a d v ≥
      (childAverage (fun d v => (hazard I a d v) ^ 2) d v -
        (hazard I a d v) ^ 2) / 100

private theorem child_denominator_left
    {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    2 * ((x : ℝ) + a) * hL a h x y =
      h * N x y + 2 * a * (h + V a h x y) := by
  by_cases hxy : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    simp [hL, hR, V, N]
  · rw [V_eq ha]
    simp only [hL, ite_eq_right hxy]
    field_simp [D_ne_zero ha hxy]
    unfold D N
    ring

private theorem child_denominator_right
    {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    2 * ((y : ℝ) + a) * hR a h x y =
      h * N x y + 2 * a * (h + V a h x y) := by
  by_cases hxy : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    simp [hL, hR, V, N]
  · rw [V_eq ha]
    simp only [hR, ite_eq_right hxy]
    field_simp [D_ne_zero ha hxy]
    unfold D N
    ring

private theorem childY_left_normalized
    {a h p : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    (p / 2 / ((x : ℝ) + a)) / hL a h x y =
      (N x y / a + ((p - N x y * h) / a) / h) /
        (N x y / a + 2 + 2 * (V a h x y / h)) := by
  have hV : 0 ≤ V a h x y := V_nonneg ha hh.le
  have hC :
      0 < h * N x y + 2 * a * (h + V a h x y) := by
    have hN := N_nonneg x y
    have hah : 0 < 2 * a * h := by positivity
    nlinarith [mul_nonneg hh.le hN, mul_nonneg ha.le hV]
  have hxa : 0 < (x : ℝ) + a := count_add_a_pos ha x
  have hhL : 0 < hL a h x y := hL_pos ha hh
  calc
    (p / 2 / ((x : ℝ) + a)) / hL a h x y =
        p / (2 * ((x : ℝ) + a) * hL a h x y) := by
      field_simp [hxa.ne', hhL.ne']
    _ = p / (h * N x y + 2 * a * (h + V a h x y)) := by
      rw [child_denominator_left ha]
    _ = (N x y / a + ((p - N x y * h) / a) / h) /
        (N x y / a + 2 + 2 * (V a h x y / h)) := by
      have hnum :
          N x y / a + ((p - N x y * h) / a) / h =
            p / (a * h) := by
        field_simp [ha.ne', hh.ne']
        ring
      have hden :
          N x y / a + 2 + 2 * (V a h x y / h) =
            (h * N x y + 2 * a * (h + V a h x y)) / (a * h) := by
        field_simp [ha.ne', hh.ne']
        ring
      rw [hnum, hden]
      field_simp [ha.ne', hh.ne', hC.ne']

private theorem childY_right_normalized
    {a h p : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    (p / 2 / ((y : ℝ) + a)) / hR a h x y =
      (N x y / a + ((p - N x y * h) / a) / h) /
        (N x y / a + 2 + 2 * (V a h x y / h)) := by
  have hV : 0 ≤ V a h x y := V_nonneg ha hh.le
  have hC :
      0 < h * N x y + 2 * a * (h + V a h x y) := by
    have hN := N_nonneg x y
    have hah : 0 < 2 * a * h := by positivity
    nlinarith [mul_nonneg hh.le hN, mul_nonneg ha.le hV]
  have hya : 0 < (y : ℝ) + a := count_add_a_pos ha y
  have hhR : 0 < hR a h x y := hR_pos ha hh
  calc
    (p / 2 / ((y : ℝ) + a)) / hR a h x y =
        p / (2 * ((y : ℝ) + a) * hR a h x y) := by
      field_simp [hya.ne', hhR.ne']
    _ = p / (h * N x y + 2 * a * (h + V a h x y)) := by
      rw [child_denominator_right ha]
    _ = (N x y / a + ((p - N x y * h) / a) / h) /
        (N x y / a + 2 + 2 * (V a h x y / h)) := by
      have hnum :
          N x y / a + ((p - N x y * h) / a) / h =
            p / (a * h) := by
        field_simp [ha.ne', hh.ne']
        ring
      have hden :
          N x y / a + 2 + 2 * (V a h x y / h) =
            (h * N x y + 2 * a * (h + V a h x y)) / (a * h) := by
        field_simp [ha.ne', hh.ne']
        ring
      rw [hnum, hden]
      field_simp [ha.ne', hh.ne', hC.ne']

/-!
This is the only proof tied to `FD1D.Bellman`. It converts the concrete
policy labels into the normalized coordinates of the polynomial certificate.
-/
theorem localBellmanHypothesis
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    LocalBellmanHypothesis I a := by
  intro d hdL v
  let x := I.count (d + 1) (leftChild v)
  let y := I.count (d + 1) (rightChild v)
  let h := hazard I a d v
  let p := intervalMass d v
  let tt := discrepancy I a d v
  let s := inventory I d v / a
  let r := tt / h
  let vv := V a h x y / h
  let ww := w a h x y / h
  have hh : 0 < h := hazard_pos I ha hm d (by omega) v
  have hN : 0 ≤ inventory I d v := Nat.cast_nonneg _
  have hcount : inventory I d v = N x y :=
    (parent_local_data I ha d hdL v).1
  have hs : 0 ≤ s := div_nonneg hN ha.le
  have hrUpper : r ≤ 1 / 2 :=
    discrepancy_div_hazard_le_half I ha hm d (by omega) v
  have hp : 0 < p := nodeMass_pos d v
  have htt :
      tt = (p - inventory I d v * h) / a := by
    rfl
  have hrLower : -s < r := by
    dsimp only [r, s]
    rw [htt]
    field_simp [ha.ne', hh.ne']
    nlinarith
  have hV0 : 0 ≤ V a h x y := V_nonneg ha hh.le
  have hv0 : 0 ≤ vv := div_nonneg hV0 hh.le
  have hvUpper : vv ≤ s / 2 := by
    calc
      vv ≤ N x y / (2 * a) :=
        V_div_h_le (x := x) (y := y) ha hh
      _ = s / 2 := by
        dsimp only [s]
        rw [hcount]
        ring
  have hwSq : ww ^ 2 = normalizedW s vv := by
    dsimp only [ww, vv, s]
    rw [hcount, normalizedW, div_pow, w_sq_eq ha]
    field_simp [ha.ne', hh.ne', N_add_two_mul_a_ne_zero ha x y]
  have htNorm : tt = h * r := by
    dsimp only [r]
    field_simp [hh.ne']
  have hy :
      bellmanY I a d v = (s + r) / (s + 1) := by
    rw [bellmanY, regularizedMass]
    dsimp only [r, s]
    rw [htt]
    dsimp only [p, h]
    field_simp [ha.ne',
      (hazard_pos I ha hm d (by omega) v).ne']
    ring
  have hhL :
      hazard I a (d + 1) (leftChild v) =
        h * (1 + vv + ww) := by
    rw [hazard_leftChild, hL_eq_h_add_V_add_w]
    dsimp only [vv, ww]
    field_simp [hh.ne']
    ring
  have hhR :
      hazard I a (d + 1) (rightChild v) =
        h * (1 + vv - ww) := by
    rw [hazard_rightChild, hR_eq_h_add_V_sub_w]
    dsimp only [vv, ww]
    field_simp [hh.ne']
    ring
  have htL :
      discrepancy I a (d + 1) (leftChild v) =
        h * (r / 2 + ww) := by
    rw [discrepancy_leftChild I ha d hdL v, tL_eq ha]
    rw [← discrepancy_eq_local I ha d hdL v]
    dsimp only [r, ww, tt]
    field_simp [hh.ne']
    ring
  have htR :
      discrepancy I a (d + 1) (rightChild v) =
        h * (r / 2 - ww) := by
    rw [discrepancy_rightChild I ha d hdL v, tR_eq ha]
    rw [← discrepancy_eq_local I ha d hdL v]
    dsimp only [r, ww, tt]
    field_simp [hh.ne']
    ring
  have hyL :
      bellmanY I a (d + 1) (leftChild v) =
        (s + r) / (s + 2 + 2 * vv) := by
    rw [bellmanY, regularizedMass, inventory, hazard_leftChild,
      intervalMass_leftChild]
    change
      (p / 2 / ((x : ℝ) + a)) / hL a h x y =
        (s + r) / (s + 2 + 2 * vv)
    dsimp only [r, s, vv]
    rw [htt, hcount]
    exact childY_left_normalized ha hh
  have hyR :
      bellmanY I a (d + 1) (rightChild v) =
        (s + r) / (s + 2 + 2 * vv) := by
    rw [bellmanY, regularizedMass, inventory, hazard_rightChild,
      intervalMass_rightChild]
    change
      (p / 2 / ((y : ℝ) + a)) / hR a h x y =
        (s + r) / (s + 2 + 2 * vv)
    dsimp only [r, s, vv]
    rw [htt, hcount]
    exact childY_right_normalized ha hh
  have hZL :
      regularizedMass I a (d + 1) (leftChild v) =
        bellmanY I a (d + 1) (leftChild v) *
          hazard I a (d + 1) (leftChild v) := by
    rw [bellmanY]
    exact (div_mul_cancel₀ _
      (hazard_pos I ha hm (d + 1) (by omega) (leftChild v)).ne').symm
  have hZR :
      regularizedMass I a (d + 1) (rightChild v) =
        bellmanY I a (d + 1) (rightChild v) *
          hazard I a (d + 1) (rightChild v) := by
    rw [bellmanY]
    exact (div_mul_cancel₀ _
      (hazard_pos I ha hm (d + 1) (by omega) (rightChild v)).ne').symm
  have hlocal := FD1D.local_bellman_inequality
    hs hrLower hrUpper hv0 hvUpper hwSq htNorm hy hhL hhR htL htR
    hyL hyR hZL hZR
  dsimp only [h, tt] at hlocal
  simpa [childAverage, bellmanValue, bellmanFunction,
    FD1D.B, FD1D.d, ge_iff_le, div_eq_mul_inv, mul_comm] using hlocal

theorem bellmanValue_leaf_nonpos
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) (v : DyadicNode L) :
    bellmanValue I a L v ≤ 0 := by
  let h := hazard I a L v
  let r := discrepancy I a L v / h
  have hh : 0 ≤ h := (hazard_pos I ha hm L le_rfl v).le
  have hr : r ≤ 1 / 2 :=
    discrepancy_div_hazard_le_half I ha hm L le_rfl v
  have hy0 := bellmanY_nonneg I ha hm le_rfl v
  have hy1 := bellmanY_le_one I ha hm le_rfl v
  have hry :=
    discrepancy_div_hazard_le_bellmanY I ha hm le_rfl v
  have ht : discrepancy I a L v = h * r := by
    dsimp [r, h]
    field_simp [(hazard_pos I ha hm L le_rfl v).ne']
  rw [bellmanValue, ht]
  exact FD1D.bellman_nonpositive hh hr hy0 hy1 hry

theorem bellmanValue_root_lower
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    -(1 / (3 * (m : ℝ) ^ 2)) ≤ bellmanValue I a 0 dyadicRoot := by
  rw [bellmanValue, discrepancy_root I ha hm, hazard_root]
  have h := FD1D.bellman_root_bound
    (h := 1 / (m : ℝ))
    (bellmanY_nonneg I ha hm (Nat.zero_le L) dyadicRoot)
    (bellmanY_le_one I ha hm (Nat.zero_le L) dyadicRoot)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have heq :
      -(1 / (3 * (m : ℝ) ^ 2)) = -((1 / (m : ℝ)) ^ 2) / 3 := by
    field_simp [hm0]
  rw [heq]
  exact h

/-- Equation (9) specialized to the concrete hierarchical policy. -/
theorem deterministic_bellman_bound
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    FD1D.bellmanDrift L a (inventory I) (deletionMass I a) ≥
      a * (FD1D.hazardEnergy (hazard I a) L / 100 -
        103 / (300 * (m : ℝ) ^ 2)) := by
  exact FD1D.deterministic_bellman_bound L
    (inventory I) (deletionMass I a) (hazard I a)
    (discrepancy I a) (regularizedMass I a) (bellmanValue I a)
    ha (mod_cast hm) (discrepancy_eq I a) (regularizedMass_eq I a)
    (hazard_root I a) (localBellmanHypothesis I ha hm)
    (bellmanValue_leaf_nonpos I ha hm)
    (bellmanValue_root_lower I ha hm)

end HierarchicalPolicy

end

end FD1D
