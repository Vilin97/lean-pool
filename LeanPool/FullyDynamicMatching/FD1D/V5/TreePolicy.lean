/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.V5.LocalBellman

/-!
# The v5 hierarchical tree policy

This module propagates the local three-cap rule through a complete dyadic
tree. It proves the invariant domain, rate-energy monotonicity, the lifted
local Bellman inequality, and the deterministic aggregate estimate.
-/

@[expose] public section

namespace FD1D.V5.TreePolicy

noncomputable section

open LocalPolicy

variable {L m : ℕ}

/-- Select the left or right rate of the local rule for one dyadic child. -/
def childRate (a p h : ℝ) (x y : ℕ) (side : Fin 2) : ℝ :=
  if side = 0 then rateLeft a p h x y else rateRight a p h x y

/-- Recursively propagated analytic rate, rooted at `1/m`. -/
def rate (I : AggregatedInventory L m) (a : ℝ) :
    ∀ d, DyadicNode d → ℝ
  | 0, _ => 1 / (m : ℝ)
  | d + 1, w =>
      let z := (childrenEquiv d).symm w
      childRate a (nodeMass d z.1) (rate I a d z.1)
        (I.count (d + 1) (leftChild z.1))
        (I.count (d + 1) (rightChild z.1)) z.2

/-- Inventory count coerced to `ℝ`. -/
def inventory (I : AggregatedInventory L m) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  I.count d v

/-- Node interval mass. -/
def intervalMass (d : ℕ) (v : DyadicNode d) : ℝ :=
  nodeMass d v

/-- Deletion mass `q_v = N_v h_v`. -/
def deletionMass (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  inventory I d v * rate I a d v

/-- Discrepancy `t_v = (p_v-q_v)/a`. -/
def discrepancy (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  (intervalMass d v - deletionMass I a d v) / a

/-- Regularized mass `Z_v = p_v/(N_v+a/2)`. -/
def regularizedMass (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  intervalMass d v / (inventory I d v + a / 2)

/-- Quadratic Bellman correction at a node. -/
def bellmanValue (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  bellman (rate I a d v) (discrepancy I a d v)
    (regularizedMass I a d v)

/-- Fixed-spatial-label child deletion imbalance. -/
def imbalance (I : AggregatedInventory L m) (a : ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  deletionMass I a (d + 1) (leftChild v) -
    deletionMass I a (d + 1) (rightChild v)

@[simp] theorem rate_root (I : AggregatedInventory L m) (a : ℝ) :
    rate I a 0 dyadicRoot = 1 / (m : ℝ) :=
  rfl

@[simp] theorem rate_leftChild (I : AggregatedInventory L m) (a : ℝ)
    (d : ℕ) (v : DyadicNode d) :
    rate I a (d + 1) (leftChild v) =
      rateLeft a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  simp [rate, childRate, leftChild, intervalMass]

@[simp] theorem rate_rightChild (I : AggregatedInventory L m) (a : ℝ)
    (d : ℕ) (v : DyadicNode d) :
    rate I a (d + 1) (rightChild v) =
      rateRight a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  simp [rate, childRate, rightChild, intervalMass,
    show (1 : Fin 2) ≠ 0 by decide]

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

theorem deletionMass_leftChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    deletionMass I a (d + 1) (leftChild v) =
      massLeft a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  rw [deletionMass, inventory, rate_leftChild]
  exact (massLeft_eq_count_mul_rateLeft _ _ _ _ _).symm

theorem deletionMass_rightChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    deletionMass I a (d + 1) (rightChild v) =
      massRight a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  rw [deletionMass, inventory, rate_rightChild]
  exact (massRight_eq_count_mul_rateRight _ _ _ _ _).symm

theorem deletionMass_children (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    deletionMass I a d v =
      deletionMass I a (d + 1) (leftChild v) +
        deletionMass I a (d + 1) (rightChild v) := by
  rw [deletionMass_leftChild, deletionMass_rightChild,
    massLeft_add_massRight]
  unfold deletionMass parentMass inventory LocalPolicy.inventory
  rw [I.count_children d hdL v]
  norm_num

theorem deletionMass_root (I : AggregatedInventory L m) (a : ℝ)
    (hm : 0 < m) :
    deletionMass I a 0 dyadicRoot = 1 := by
  simp [deletionMass, inventory, I.count_root, rate, ne_of_gt hm]

theorem discrepancy_root (I : AggregatedInventory L m) {a : ℝ}
    (_ha : 0 < a) (hm : 0 < m) :
    discrepancy I a 0 dyadicRoot = 0 := by
  simp [discrepancy, deletionMass_root I a hm]

private theorem parent_local_data
    (I : AggregatedInventory L m) (a : ℝ)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    let x := I.count (d + 1) (leftChild v)
    let y := I.count (d + 1) (rightChild v)
    inventory I d v = LocalPolicy.inventory x y ∧
      deletionMass I a d v =
        parentMass (rate I a d v) x y := by
  dsimp
  have hc := I.count_children d hdL v
  constructor <;>
    simp [inventory, deletionMass, parentMass, LocalPolicy.inventory, hc]

theorem discrepancy_eq_local (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    discrepancy I a d v =
      LocalPolicy.discrepancy a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  unfold discrepancy LocalPolicy.discrepancy
  rw [(parent_local_data I a d hdL v).2]

theorem regularizedMass_eq_local (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    regularizedMass I a d v =
      LocalPolicy.regularizedMass a (intervalMass d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  unfold regularizedMass LocalPolicy.regularizedMass
  rw [(parent_local_data I a d hdL v).1]

theorem discrepancy_leftChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    discrepancy I a (d + 1) (leftChild v) =
      discrepancyLeft a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  rw [discrepancy, intervalMass_leftChild, deletionMass_leftChild]
  rfl

theorem discrepancy_rightChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    discrepancy I a (d + 1) (rightChild v) =
      discrepancyRight a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  rw [discrepancy, intervalMass_rightChild, deletionMass_rightChild]
  rfl

theorem regularizedMass_leftChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    regularizedMass I a (d + 1) (leftChild v) =
      regularizedMassLeft a (intervalMass d v)
        (I.count (d + 1) (leftChild v))
         := by
  simp [regularizedMass, regularizedMassLeft, inventory]

theorem regularizedMass_rightChild (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    regularizedMass I a (d + 1) (rightChild v) =
      regularizedMassRight a (intervalMass d v)
        (I.count (d + 1) (rightChild v)) := by
  simp [regularizedMass, regularizedMassRight, inventory]

/-! ## Invariant domain and feasibility -/

theorem node_invariants
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    ∀ d, d ≤ L → ∀ v,
      0 < rate I a d v ∧
        discrepancy I a d v ≤ rate I a d v / 2 ∧
        regularizedMass I a d v ≤ rate I a d v := by
  intro d
  induction d with
  | zero =>
      intro _ v
      have hv : v = dyadicRoot := Fin.eq_zero v
      subst v
      have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
      have hrate : 0 < rate I a 0 dyadicRoot := by
        rw [rate_root]
        exact one_div_pos.mpr hmR
      have hdisc : discrepancy I a 0 dyadicRoot ≤
          rate I a 0 dyadicRoot / 2 := by
        rw [discrepancy_root I ha hm]
        positivity
      have hreg :
          regularizedMass I a 0 dyadicRoot ≤
            rate I a 0 dyadicRoot := by
        unfold regularizedMass inventory intervalMass
        rw [I.count_root]
        simp only [nodeMass_root, rate_root]
        apply one_div_le_one_div_of_le hmR
        have : 0 ≤ a / 2 := by positivity
        linarith
      exact ⟨hrate, hdisc, hreg⟩
  | succ d ih =>
      intro hdL w
      let z := (childrenEquiv d).symm w
      have hz : childrenEquiv d z = w :=
        (childrenEquiv d).apply_symm_apply w
      have hd : d < L := by omega
      have hp := ih (by omega) z.1
      let x := I.count (d + 1) (leftChild z.1)
      let y := I.count (d + 1) (rightChild z.1)
      have htLocal :
          LocalPolicy.discrepancy a (intervalMass d z.1)
              (rate I a d z.1) x y ≤
            rate I a d z.1 / 2 := by
        dsimp [x, y]
        rw [← discrepancy_eq_local I a d hd z.1]
        exact hp.2.1
      have hchildren :=
        LocalPolicy.child_invariants ha (nodeMass_pos d z.1)
          hp.1 htLocal
      have hZLpos :
          0 < regularizedMassLeft a (intervalMass d z.1) x := by
        unfold regularizedMassLeft
        exact div_pos (div_pos (nodeMass_pos d z.1) (by norm_num))
          (by positivity)
      have hZRpos :
          0 < regularizedMassRight a (intervalMass d z.1) y := by
        unfold regularizedMassRight
        exact div_pos (div_pos (nodeMass_pos d z.1) (by norm_num))
          (by positivity)
      rw [← hz]
      rcases z with ⟨v, side⟩
      fin_cases side
      · change
          0 < rate I a (d + 1) (leftChild v) ∧
            discrepancy I a (d + 1) (leftChild v) ≤
              rate I a (d + 1) (leftChild v) / 2 ∧
            regularizedMass I a (d + 1) (leftChild v) ≤
              rate I a (d + 1) (leftChild v)
        rw [rate_leftChild, discrepancy_leftChild,
          regularizedMass_leftChild]
        exact ⟨hZLpos.trans_le hchildren.2.1,
          hchildren.1, hchildren.2.1⟩
      · change
          0 < rate I a (d + 1) (rightChild v) ∧
            discrepancy I a (d + 1) (rightChild v) ≤
              rate I a (d + 1) (rightChild v) / 2 ∧
            regularizedMass I a (d + 1) (rightChild v) ≤
              rate I a (d + 1) (rightChild v)
        rw [rate_rightChild, discrepancy_rightChild,
          regularizedMass_rightChild]
        exact ⟨hZRpos.trans_le hchildren.2.2.2,
          hchildren.2.2.1, hchildren.2.2.2⟩

theorem rate_pos (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    0 < rate I a d v :=
  (node_invariants I ha hm d hdL v).1

theorem discrepancy_le_half (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    discrepancy I a d v ≤ rate I a d v / 2 :=
  (node_invariants I ha hm d hdL v).2.1

theorem regularizedMass_le_rate
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    regularizedMass I a d v ≤ rate I a d v :=
  (node_invariants I ha hm d hdL v).2.2

theorem intervalMass_le_count_add_half_mul_rate
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    intervalMass d v ≤
      (inventory I d v + a / 2) * rate I a d v := by
  have hden : 0 < inventory I d v + a / 2 := by
    unfold inventory
    positivity
  have hreg := regularizedMass_le_rate I ha hm hdL v
  unfold regularizedMass at hreg
  simpa [mul_comm] using (div_le_iff₀ hden).mp hreg

theorem deletionMass_nonneg (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    0 ≤ deletionMass I a d v := by
  exact mul_nonneg (Nat.cast_nonneg _)
    (rate_pos I ha hm hdL v).le

theorem sum_deletionMass (I : AggregatedInventory L m)
    {a : ℝ} (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) :
    ∑ v, deletionMass I a d v = 1 := by
  let q : CoherentTreeLabel L ℝ :=
    { value := deletionMass I a
      children := deletionMass_children I a }
  rw [show (∑ v, deletionMass I a d v) = levelSum q.value d by rfl]
  rw [q.levelSum_eq_root hdL]
  exact deletionMass_root I a hm

theorem leaf_deletionMass_eq_zero_of_count_eq_zero
    (I : AggregatedInventory L m) (a : ℝ) (v : DyadicNode L)
    (hv : I.count L v = 0) :
    deletionMass I a L v = 0 := by
  simp [deletionMass, inventory, hv]

theorem leaf_deletionMass_pos_of_count_pos
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) (v : DyadicNode L)
    (hv : 0 < I.count L v) :
    0 < deletionMass I a L v := by
  unfold deletionMass inventory
  exact mul_pos (by exact_mod_cast hv) (rate_pos I ha hm le_rfl v)

theorem regularizedMass_pos
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (d : ℕ) (v : DyadicNode d) :
    0 < regularizedMass I a d v := by
  unfold regularizedMass intervalMass inventory
  exact div_pos (nodeMass_pos d v) (by positivity)

theorem bellmanValue_nonpos
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    bellmanValue I a d v ≤ 0 := by
  unfold bellmanValue
  exact bellman_nonpos (regularizedMass_pos I ha d v).le
    (discrepancy_le_half I ha hm hdL v)

/-! ## Rate-energy monotonicity -/

theorem local_rate_average_ge
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    rate I a d v ≤
      childAverage (rate I a) d v := by
  have hp : 0 < intervalMass d v := nodeMass_pos d v
  have hh := rate_pos I ha hm (by omega) v
  have ht := discrepancy_le_half I ha hm (by omega) v
  rw [discrepancy_eq_local I a d hdL v] at ht
  have hlocal :=
    LocalPolicy.child_rate_average_ge ht
  unfold childAverage
  rw [rate_leftChild, rate_rightChild]
  exact hlocal

theorem local_rate_energy_nonneg
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    0 ≤ childAverage (fun d v => rate I a d v ^ 2) d v -
      rate I a d v ^ 2 := by
  let hL := rate I a (d + 1) (leftChild v)
  let hR := rate I a (d + 1) (rightChild v)
  let hP := rate I a d v
  let avg := (hL + hR) / 2
  have havg : hP ≤ avg := by
    simpa [hP, avg, hL, hR, childAverage] using
      local_rate_average_ge I ha hm d hdL v
  have hp : 0 < hP := rate_pos I ha hm (by omega) v
  have havg0 : 0 ≤ avg := hp.le.trans havg
  have hJensen :
      avg ^ 2 ≤ (hL ^ 2 + hR ^ 2) / 2 := by
    dsimp [avg]
    nlinarith [sq_nonneg (hL - hR)]
  have hmono : hP ^ 2 ≤ avg ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr havg)
      (add_nonneg havg0 hp.le)]
  unfold childAverage
  dsimp [hL, hR, hP] at *
  linarith

theorem rateEnergy_mono
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d < L) :
    hazardEnergy (rate I a) d ≤ hazardEnergy (rate I a) (d + 1) := by
  have hsum :
      0 ≤ ∑ v, nodeMass d v *
        (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2) := by
    apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (nodeMass_nonneg d v)
      (local_rate_energy_nonneg I ha hm d hdL v)
  rw [weighted_local_sum] at hsum
  exact sub_nonneg.mp (by simpa [hazardEnergy] using hsum)

theorem rateEnergy_root (I : AggregatedInventory L m) (a : ℝ)
    (hm : 0 < m) :
    hazardEnergy (rate I a) 0 = 1 / (m : ℝ) ^ 2 := by
  rw [hazardEnergy_root, rate_root]
  field_simp

/-! ## Lifted Bellman inequality -/

theorem imbalance_eq_local (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    imbalance I a d v =
      bias a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  unfold imbalance
  rw [deletionMass_leftChild, deletionMass_rightChild]
  exact (bias_eq_massLeft_sub_massRight _ _ _ _ _).symm

theorem local_bellman_inequality
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    childAverage
          (fun d v => discrepancy I a d v *
            regularizedMass I a d v) d v +
        childAverage (bellmanValue I a) d v -
        bellmanValue I a d v ≥
      (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2 +
          imbalance I a d v ^ 2 / a ^ 2) / 1000 := by
  let x := I.count (d + 1) (leftChild v)
  let y := I.count (d + 1) (rightChild v)
  have hh := rate_pos I ha hm (by omega) v
  have ht := discrepancy_le_half I ha hm (by omega) v
  rw [discrepancy_eq_local I a d hdL v] at ht
  have hlocal :=
    LocalBellman.local_bellman_inequality ha
      (nodeMass_pos d v) hh ht
  unfold LocalBellman.localResidual LocalBellman.localEnergy at hlocal
  have hdiscL :
      discrepancyLeft a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        discrepancy I a (d + 1) (leftChild v) :=
    (discrepancy_leftChild I a d v).symm
  have hdiscR :
      discrepancyRight a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        discrepancy I a (d + 1) (rightChild v) :=
    (discrepancy_rightChild I a d v).symm
  have hZL :
      regularizedMassLeft a (nodeMass d v)
          (I.count (d + 1) (leftChild v))
           =
        regularizedMass I a (d + 1) (leftChild v) :=
    (regularizedMass_leftChild I a d v).symm
  have hZR :
      regularizedMassRight a (nodeMass d v)
          (I.count (d + 1) (rightChild v)) =
        regularizedMass I a (d + 1) (rightChild v) :=
    (regularizedMass_rightChild I a d v).symm
  have hrateL :
      rateLeft a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        rate I a (d + 1) (leftChild v) :=
    (rate_leftChild I a d v).symm
  have hrateR :
      rateRight a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        rate I a (d + 1) (rightChild v) :=
    (rate_rightChild I a d v).symm
  have hdiscP :
      LocalPolicy.discrepancy a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        discrepancy I a d v :=
    (discrepancy_eq_local I a d hdL v).symm
  have hZP :
      LocalPolicy.regularizedMass a (nodeMass d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        regularizedMass I a d v :=
    (regularizedMass_eq_local I a d hdL v).symm
  have hb :
      bias a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        imbalance I a d v :=
    (imbalance_eq_local I a d v).symm
  rw [hdiscL, hdiscR, hZL, hZR, hrateL, hrateR,
    hdiscP, hZP, hb] at hlocal
  unfold childAverage bellmanValue
  ring_nf at hlocal ⊢
  exact hlocal

/-- The local certificate with its two energy terms separated. -/
theorem local_bellman_inequality_separated
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    childAverage
          (fun d v => discrepancy I a d v *
            regularizedMass I a d v) d v +
        childAverage (bellmanValue I a) d v -
        bellmanValue I a d v ≥
      (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2) / 1000 +
        imbalance I a d v ^ 2 / (1000 * a ^ 2) := by
  have hlocal := local_bellman_inequality I ha hm d hdL v
  calc
    (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2) / 1000 +
        imbalance I a d v ^ 2 / (1000 * a ^ 2) =
      (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2 +
          imbalance I a d v ^ 2 / a ^ 2) / 1000 := by
            field_simp [ha.ne']
    _ ≤ _ := hlocal

/-! ## Deterministic aggregate estimate -/

/-- The transport energy `G = ∑_{v internal} p_v b_v²`. -/
def transportEnergy (I : AggregatedInventory L m) (a : ℝ) : ℝ :=
  internalWeightedSum (fun d v => imbalance I a d v ^ 2) L

/-- The restoring term in the drift of the harmonic inventory potential. -/
def restoringDrift (I : AggregatedInventory L m) (a : ℝ) : ℝ :=
  bellmanDrift L (a / 2) (inventory I) (deletionMass I a)

/-- The restoring drift is `a` times the nonroot weighted `t Z` sum. -/
theorem restoringDrift_div
    (I : AggregatedInventory L m) {a : ℝ} (ha : 0 < a) :
    restoringDrift I a / a =
      nonrootWeightedSum
        (fun d v => discrepancy I a d v * regularizedMass I a d v) L := by
  unfold restoringDrift bellmanDrift nonrootWeightedSum weightedLevel
  unfold discrepancy regularizedMass intervalMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v hv
  field_simp [ha.ne']

theorem bellmanValue_root_eq
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    bellmanValue I a 0 dyadicRoot =
      -1 / (2 * (m : ℝ) * ((m : ℝ) + a / 2)) := by
  rw [bellmanValue, discrepancy_root I ha hm, rate_root]
  simp only [bellman, zero_sub, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true]
  unfold regularizedMass intervalMass inventory
  rw [I.count_root]
  simp only [nodeMass_root]
  field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne']
  ring

theorem bellmanValue_root_lower
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    -(1 / (2 * (m : ℝ) ^ 2)) ≤
      bellmanValue I a 0 dyadicRoot := by
  rw [bellmanValue_root_eq I ha hm]
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsmall :
      2 * (m : ℝ) ^ 2 ≤ 2 * (m : ℝ) * ((m : ℝ) + a / 2) := by
    nlinarith [mul_pos hmR ha]
  have hrecip :
      1 / (2 * (m : ℝ) * ((m : ℝ) + a / 2)) ≤
        1 / (2 * (m : ℝ) ^ 2) := by
    exact one_div_le_one_div_of_le (by positivity) hsmall
  simpa only [neg_div] using neg_le_neg hrecip

/--
The deterministic aggregate estimate from Proposition 4.3 of the manuscript:
`D ≥ a H_L / 1000 + G / (1000 a) - 501 a / (1000 m²)`.
-/
theorem deterministic_aggregate_estimate
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    restoringDrift I a ≥
      a / 1000 * hazardEnergy (rate I a) L +
        transportEnergy I a / (1000 * a) -
        501 * a / (1000 * (m : ℝ) ^ 2) := by
  have hsum :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => rate I a d v ^ 2) d v -
              rate I a d v ^ 2) / 1000 +
            imbalance I a d v ^ 2 / (1000 * a ^ 2))) ≤
      ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (childAverage
              (fun d v => discrepancy I a d v *
                regularizedMass I a d v) d v +
            childAverage (bellmanValue I a) d v -
            bellmanValue I a d v) := by
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left
      (local_bellman_inequality_separated I ha hm d
        (Finset.mem_range.mp hd) v)
      (nodeMass_nonneg d v)
  have hrate :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => rate I a d v ^ 2) d v -
            rate I a d v ^ 2) / 1000)) =
        (hazardEnergy (rate I a) L -
          hazardEnergy (rate I a) 0) / 1000 := by
    calc
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => rate I a d v ^ 2) d v -
            rate I a d v ^ 2) / 1000)) =
          (∑ d ∈ Finset.range L,
            ∑ v, nodeMass d v *
              (childAverage (fun d v => rate I a d v ^ 2) d v -
                rate I a d v ^ 2)) / 1000 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = _ := by rw [hazard_energy_telescope]
  have himbalance :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (imbalance I a d v ^ 2 / (1000 * a ^ 2))) =
        transportEnergy I a / (1000 * a ^ 2) := by
    unfold transportEnergy internalWeightedSum weightedLevel
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  have hright :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => rate I a d v ^ 2) d v -
              rate I a d v ^ 2) / 1000 +
            imbalance I a d v ^ 2 / (1000 * a ^ 2))) =
        (hazardEnergy (rate I a) L -
            hazardEnergy (rate I a) 0) / 1000 +
          transportEnergy I a / (1000 * a ^ 2) := by
    rw [show
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => rate I a d v ^ 2) d v -
              rate I a d v ^ 2) / 1000 +
            imbalance I a d v ^ 2 / (1000 * a ^ 2))) =
        (∑ d ∈ Finset.range L,
          ∑ v, nodeMass d v *
            ((childAverage (fun d v => rate I a d v ^ 2) d v -
              rate I a d v ^ 2) / 1000)) +
        ∑ d ∈ Finset.range L,
          ∑ v, nodeMass d v *
            (imbalance I a d v ^ 2 / (1000 * a ^ 2)) by
      simp only [mul_add, Finset.sum_add_distrib]]
    rw [hrate, himbalance]
  rw [hright, bellman_tree_telescope] at hsum
  rw [← restoringDrift_div I ha] at hsum
  have hleaf : weightedLevel (bellmanValue I a) L ≤ 0 := by
    apply Finset.sum_nonpos
    intro v hv
    exact mul_nonpos_of_nonneg_of_nonpos
      (nodeMass_nonneg L v)
      (bellmanValue_nonpos I ha hm le_rfl v)
  have hroot :=
    bellmanValue_root_lower I ha hm
  have hH0 :
      hazardEnergy (rate I a) 0 = 1 / (m : ℝ) ^ 2 :=
    rateEnergy_root I a hm
  rw [hH0] at hsum
  have hnegroot :
      -bellmanValue I a 0 dyadicRoot ≤
        1 / (2 * (m : ℝ) ^ 2) := by
    simpa only [neg_neg] using neg_le_neg hroot
  have hsumUpper :
      (hazardEnergy (rate I a) L - 1 / (m : ℝ) ^ 2) / 1000 +
          transportEnergy I a / (1000 * a ^ 2) ≤
        restoringDrift I a / a + 1 / (2 * (m : ℝ) ^ 2) := by
    calc
      (hazardEnergy (rate I a) L - 1 / (m : ℝ) ^ 2) / 1000 +
            transportEnergy I a / (1000 * a ^ 2) ≤
          restoringDrift I a / a +
              weightedLevel (bellmanValue I a) L -
              bellmanValue I a 0 dyadicRoot := hsum
      _ = restoringDrift I a / a +
            weightedLevel (bellmanValue I a) L +
            (-bellmanValue I a 0 dyadicRoot) := by ring
      _ ≤ restoringDrift I a / a + 0 +
            1 / (2 * (m : ℝ) ^ 2) :=
        add_le_add
          (add_le_add (le_refl (restoringDrift I a / a)) hleaf)
          hnegroot
      _ = restoringDrift I a / a +
            1 / (2 * (m : ℝ) ^ 2) := by ring
  have hminus :
      ((hazardEnergy (rate I a) L - 1 / (m : ℝ) ^ 2) / 1000 +
          transportEnergy I a / (1000 * a ^ 2)) -
          1 / (2 * (m : ℝ) ^ 2) ≤
        restoringDrift I a / a :=
    (sub_le_iff_le_add).2 hsumUpper
  have hpre :
      hazardEnergy (rate I a) L / 1000 +
          transportEnergy I a / (1000 * a ^ 2) -
          501 / (1000 * (m : ℝ) ^ 2) ≤
        restoringDrift I a / a := by
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    convert hminus using 1;
      field_simp [hmR]; ring
  have hscaled := (le_div_iff₀ ha).mp hpre
  calc
    a / 1000 * hazardEnergy (rate I a) L +
          transportEnergy I a / (1000 * a) -
          501 * a / (1000 * (m : ℝ) ^ 2) =
        (hazardEnergy (rate I a) L / 1000 +
          transportEnergy I a / (1000 * a ^ 2) -
          501 / (1000 * (m : ℝ) ^ 2)) * a := by
            field_simp [ha.ne']
    _ ≤ restoringDrift I a := hscaled

end

end FD1D.V5.TreePolicy
