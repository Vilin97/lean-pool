/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Analysis.Convex.Integral
public import LeanPool.FullyDynamicMatching.FD1D.Basic

/-! # Transport -/

@[expose] public section

namespace FD1D

noncomputable section

open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral

/-!
# Dyadic Haar transport on the unit interval

This file isolates the analytic part of Section 2. A `DyadicMass L` is a
binary tree with exactly `2^L` leaf masses. Its recursive CDF is the CDF of
the measure which spreads every leaf mass uniformly over its dyadic cell.

The second half of the file proves the finite-family Haar calculation. Tree
symmetry is expressed by mass-preserving child-swap equivalences on the
finite state space. This is exactly the property used to kill a nested
cross term; disjoint tents vanish pointwise.
-/

/-- A complete binary tree of `2^L` real leaf masses. -/
inductive DyadicMass : ℕ → Type
  | leaf (mass : ℝ) : DyadicMass 0
  | branch {L : ℕ} (left right : DyadicMass L) : DyadicMass (L + 1)

namespace DyadicMass

/-- Total mass below the root. -/
def total : {L : ℕ} → DyadicMass L → ℝ
  | 0, leaf m => m
  | _ + 1, branch l r => total l + total r

/-- Leaf masses, in their left-to-right spatial order. -/
def leaves : {L : ℕ} → DyadicMass L → List ℝ
  | 0, leaf m => [m]
  | _ + 1, branch l r => leaves l ++ leaves r

@[simp] theorem length_leaves {L : ℕ} (q : DyadicMass L) :
    q.leaves.length = 2 ^ L := by
  induction q with
  | leaf => simp [leaves]
  | @branch L l r ihl ihr =>
      simp [leaves, ihl, ihr, pow_succ]
      omega

/--
Build the complete dyadic mass tree from its left-to-right vector of
`2^L` leaf masses.
-/
def ofLeafVector : (L : ℕ) → (Fin (2 ^ L) → ℝ) → DyadicMass L
  | 0, f => .leaf (f 0)
  | L + 1, f =>
      let e : Fin (2 ^ L + 2 ^ L) ≃ Fin (2 ^ (L + 1)) :=
        finCongr (by rw [pow_succ]; omega)
      .branch
        (ofLeafVector L (fun i => f (e (Fin.castAdd _ i))))
        (ofLeafVector L (fun i => f (e (Fin.natAdd _ i))))

@[simp] theorem total_ofLeafVector (L : ℕ) (f : Fin (2 ^ L) → ℝ) :
    (ofLeafVector L f).total = ∑ i, f i := by
  induction L with
  | zero =>
      simp [ofLeafVector, total]
  | succ L ih =>
      simp only [ofLeafVector, total]
      rw [ih, ih]
      let e : Fin (2 ^ L + 2 ^ L) ≃ Fin (2 ^ (L + 1)) :=
        finCongr (by rw [pow_succ]; omega)
      rw [← e.sum_comp f]
      exact (Fin.sum_univ_add (fun i => f (e i))).symm

/-- Every leaf mass is nonnegative. -/
def allNonneg : {L : ℕ} → DyadicMass L → Prop
  | 0, leaf m => 0 ≤ m
  | _ + 1, branch l r => allNonneg l ∧ allNonneg r

theorem allNonneg_ofLeafVector (L : ℕ) (f : Fin (2 ^ L) → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (ofLeafVector L f).allNonneg := by
  induction L with
  | zero =>
      simpa [ofLeafVector, allNonneg] using hf 0
  | succ L ih =>
      simp only [ofLeafVector, allNonneg]
      constructor
      · apply ih
        intro i
        exact hf _
      · apply ih
        intro i
        exact hf _

theorem total_nonneg {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg) :
    0 ≤ q.total := by
  induction q with
  | leaf => exact hq
  | branch l r ihl ihr =>
      exact add_nonneg (ihl hq.1) (ihr hq.2)

/-- The hypotheses saying that the `2^L` leaf masses form a probability vector. -/
structure IsProbability {L : ℕ} (q : DyadicMass L) : Prop where
  nonneg : q.allNonneg
  total_eq_one : q.total = 1

theorem isProbability_ofLeafVector (L : ℕ) (f : Fin (2 ^ L) → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hsum : ∑ i, f i = 1) :
    (ofLeafVector L f).IsProbability where
  nonneg := allNonneg_ofLeafVector L f hf
  total_eq_one := by simpa using hsum

/--
The explicit piecewise-linear CDF. Outside `[0,1]` this is merely a
piecewise-linear extension; all CDF statements below are restricted to the
unit interval.
-/
def piecewiseCDF : {L : ℕ} → DyadicMass L → ℝ → ℝ
  | 0, leaf m => fun z => m * z
  | _ + 1, branch l r => fun z =>
      if z ≤ 1 / 2 then piecewiseCDF l (2 * z)
      else total l + piecewiseCDF r (2 * z - 1)

@[simp] theorem piecewiseCDF_zero {L : ℕ} (q : DyadicMass L) :
    q.piecewiseCDF 0 = 0 := by
  induction q with
  | leaf => simp [piecewiseCDF]
  | branch l r ihl ihr => simp [piecewiseCDF, ihl]

@[simp] theorem piecewiseCDF_one {L : ℕ} (q : DyadicMass L) :
    q.piecewiseCDF 1 = q.total := by
  induction q with
  | leaf => simp [piecewiseCDF, total]
  | branch l r ihl ihr => norm_num [piecewiseCDF, total, ihr]

theorem piecewiseCDF_nonneg {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ q.piecewiseCDF z := by
  induction q generalizing z with
  | leaf m =>
      simp only [piecewiseCDF]
      exact mul_nonneg hq hz0
  | @branch L l r ihl ihr =>
      simp only [piecewiseCDF]
      by_cases hz : z ≤ 1 / 2
      · rw [ite_eq_left hz]
        exact ihl hq.1 (by linarith) (by linarith)
      · rw [ite_eq_right hz]
        exact add_nonneg (total_nonneg l hq.1)
          (ihr hq.2 (by linarith) (by linarith))

theorem piecewiseCDF_le_total {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.piecewiseCDF z ≤ q.total := by
  induction q generalizing z with
  | leaf m =>
      simp only [piecewiseCDF, total]
      have := mul_nonneg hq (sub_nonneg.mpr hz1)
      nlinarith
  | @branch L l r ihl ihr =>
      simp only [piecewiseCDF]
      by_cases hz : z ≤ 1 / 2
      · rw [ite_eq_left hz]
        have hle := ihl hq.1 (z := 2 * z) (by linarith) (by linarith)
        have hr := total_nonneg r hq.2
        simp only [total]
        linarith
      · rw [ite_eq_right hz]
        have hle := ihr hq.2 (z := 2 * z - 1) (by linarith) (by linarith)
        simp only [total]
        linarith

/-- Nonnegative leaf masses make the explicit CDF monotone on `[0,1]`. -/
theorem piecewiseCDF_monotoneOn {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg) :
    MonotoneOn q.piecewiseCDF (Icc 0 1) := by
  induction q with
  | leaf m =>
      intro x hx y hy hxy
      simp only [piecewiseCDF]
      exact mul_le_mul_of_nonneg_left hxy hq
  | @branch L l r ihl ihr =>
      intro x hx y hy hxy
      simp only [piecewiseCDF]
      by_cases hxhalf : x ≤ 1 / 2
      · rw [ite_eq_left hxhalf]
        by_cases hyhalf : y ≤ 1 / 2
        · rw [ite_eq_left hyhalf]
          exact ihl hq.1 (a := 2 * x) (b := 2 * y)
            ⟨by linarith [hx.1], by linarith⟩
            ⟨by linarith [hy.1], by linarith⟩ (by linarith)
        · rw [ite_eq_right hyhalf]
          have hleft := piecewiseCDF_le_total l hq.1
            (z := 2 * x) (by linarith [hx.1]) (by linarith)
          have hright := piecewiseCDF_nonneg r hq.2
            (z := 2 * y - 1) (by linarith) (by linarith [hy.2])
          linarith
      · have hyhalf : ¬y ≤ 1 / 2 := by linarith
        rw [ite_eq_right hxhalf, ite_eq_right hyhalf]
        simpa [add_comm] using add_le_add_left (ihr hq.2
          (a := 2 * x - 1) (b := 2 * y - 1)
          ⟨by linarith, by linarith [hx.2]⟩
          ⟨by linarith, by linarith [hy.2]⟩ (by linarith)) l.total

/--
The explicit generalized inverse in mass coordinates. Its input ranges
from `0` to `q.total`; at a branch the interval is split at the left mass.
-/
def quantile : {L : ℕ} → DyadicMass L → ℝ → ℝ
  | 0, leaf m => fun u => u / m
  | _ + 1, branch l r => fun u =>
      if u ≤ l.total then l.quantile u / 2
      else (1 + r.quantile (u - l.total)) / 2

/--
The actual selected-leaf policy. It returns the left endpoint of the leaf
whose cumulative-mass interval contains `u`.
-/
def selectedLeaf : {L : ℕ} → DyadicMass L → ℝ → ℝ
  | 0, leaf _ => fun _ => 0
  | _ + 1, branch l r => fun u =>
      if u ≤ l.total then l.selectedLeaf u / 2
      else (1 + r.selectedLeaf (u - l.total)) / 2

theorem piecewiseCDF_measurable {L : ℕ} (q : DyadicMass L) :
    Measurable q.piecewiseCDF := by
  induction q with
  | leaf =>
      exact measurable_const.mul measurable_id
  | @branch L l r ihl ihr =>
      apply Measurable.ite (measurableSet_le measurable_id measurable_const)
      · exact ihl.comp (measurable_const.mul measurable_id)
      · exact measurable_const.add
          (ihr.comp ((measurable_const.mul measurable_id).sub measurable_const))

theorem quantile_measurable {L : ℕ} (q : DyadicMass L) :
    Measurable q.quantile := by
  induction q with
  | leaf =>
      exact measurable_id.div_const _
  | @branch L l r ihl ihr =>
      apply Measurable.ite (measurableSet_le measurable_id measurable_const)
      · exact ihl.div_const _
      · exact (measurable_const.add
          (ihr.comp (measurable_id.sub measurable_const))).div_const _

theorem selectedLeaf_measurable {L : ℕ} (q : DyadicMass L) :
    Measurable q.selectedLeaf := by
  induction q with
  | leaf =>
      exact measurable_const
  | @branch L l r ihl ihr =>
      apply Measurable.ite (measurableSet_le measurable_id measurable_const)
      · exact ihl.div_const _
      · exact (measurable_const.add
          (ihr.comp (measurable_id.sub measurable_const))).div_const _

/-- The explicit generalized inverse takes mass coordinates into `[0,1]`. -/
theorem quantile_mem_unit {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total) :
    q.quantile u ∈ Icc (0 : ℝ) 1 := by
  induction q generalizing u with
  | leaf m =>
      simp only [quantile]
      by_cases hm : m = 0
      · subst m
        have hu : u = 0 := by simpa [total] using le_antisymm hu1 hu0
        simp [hu]
      · have hmpos : 0 < m := lt_of_le_of_ne hq (Ne.symm hm)
        constructor
        · exact div_nonneg hu0 hmpos.le
        · exact (div_le_one hmpos).2 (by simpa [total] using hu1)
  | @branch L l r ihl ihr =>
      simp only [quantile]
      by_cases hu : u ≤ l.total
      · rw [ite_eq_left hu]
        have hlocal := ihl hq.1 hu0 hu
        constructor <;> linarith [hlocal.1, hlocal.2]
      · rw [ite_eq_right hu]
        have hulocal : 0 ≤ u - l.total := by linarith
        have hurlocal : u - l.total ≤ r.total := by
          rw [total] at hu1
          linarith
        have hlocal := ihr hq.2 hulocal hurlocal
        constructor <;> linarith [hlocal.1, hlocal.2]

/-- The selected point is an endpoint in the unit interval. -/
theorem selectedLeaf_mem_unit {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total) :
    q.selectedLeaf u ∈ Icc (0 : ℝ) 1 := by
  induction q generalizing u with
  | leaf =>
      simp [selectedLeaf]
  | @branch L l r ihl ihr =>
      simp only [selectedLeaf]
      by_cases hu : u ≤ l.total
      · rw [ite_eq_left hu]
        have hlocal := ihl hq.1 hu0 hu
        constructor <;> linarith [hlocal.1, hlocal.2]
      · rw [ite_eq_right hu]
        have hulocal : 0 ≤ u - l.total := by linarith
        have hurlocal : u - l.total ≤ r.total := by
          rw [total] at hu1
          linarith
        have hlocal := ihr hq.2 hulocal hurlocal
        constructor <;> linarith [hlocal.1, hlocal.2]

/-- Positive mass coordinates have a strictly positive generalized inverse. -/
theorem quantile_pos {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ q.total) :
    0 < q.quantile u := by
  induction q generalizing u with
  | leaf m =>
      simp only [quantile]
      have hm : 0 < m := lt_of_lt_of_le hu0 (by simpa [total] using hu1)
      exact div_pos hu0 hm
  | @branch L l r ihl ihr =>
      simp only [quantile]
      by_cases hu : u ≤ l.total
      · rw [ite_eq_left hu]
        exact div_pos (ihl hq.1 hu0 hu) (by norm_num)
      · rw [ite_eq_right hu]
        have hlocal : 0 ≤ r.quantile (u - l.total) :=
          (r.quantile_mem_unit hq.2 (by linarith)
            (by
              rw [total] at hu1
              linarith)).1
        linarith

/--
Generalized-inverse relation for the explicit recursive map. This includes
zero-mass leaves and therefore does not require strict positivity.
-/
theorem quantile_le_iff {L : ℕ} (q : DyadicMass L) (hq : q.allNonneg)
    {u z : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.quantile u ≤ z ↔ u ≤ q.piecewiseCDF z := by
  induction q generalizing u z with
  | leaf m =>
      simp only [quantile, piecewiseCDF]
      by_cases hm : m = 0
      · subst m
        have hu : u = 0 := by simpa [total] using le_antisymm hu1 hu0
        simp [hu, hz0]
      · have hmpos : 0 < m := lt_of_le_of_ne hq (Ne.symm hm)
        rw [div_le_iff₀ hmpos]
        ring_nf
  | @branch L l r ihl ihr =>
      simp only [quantile, piecewiseCDF]
      by_cases hz : z ≤ 1 / 2
      · rw [ite_eq_left hz]
        have h2z0 : 0 ≤ 2 * z := by linarith
        have h2z1 : 2 * z ≤ 1 := by linarith
        by_cases hu : u ≤ l.total
        · rw [ite_eq_left hu]
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
          simpa [mul_comm] using ihl hq.1 hu0 hu h2z0 h2z1
        · rw [ite_eq_right hu]
          have hqr := quantile_mem_unit r hq.2
            (u := u - l.total) (by linarith)
            (by
              rw [total] at hu1
              linarith)
          have hqrpos := quantile_pos r hq.2 (u := u - l.total)
            (by linarith) (by
              rw [total] at hu1
              linarith)
          have hleft := piecewiseCDF_le_total l hq.1 h2z0 h2z1
          constructor
          · intro h
            exfalso
            linarith
          · intro h
            exfalso
            exact hu (h.trans hleft)
      · rw [ite_eq_right hz]
        have h2z0 : 0 ≤ 2 * z - 1 := by linarith
        have h2z1 : 2 * z - 1 ≤ 1 := by linarith
        by_cases hu : u ≤ l.total
        · rw [ite_eq_left hu]
          have hql := quantile_mem_unit l hq.1 hu0 hu
          have hright := piecewiseCDF_nonneg r hq.2 h2z0 h2z1
          constructor
          · intro _
            linarith
          · intro _
            linarith [hql.2]
        · rw [ite_eq_right hu]
          have hulocal : 0 ≤ u - l.total := by linarith
          have hurlocal : u - l.total ≤ r.total := by
            rw [total] at hu1
            linarith
          have hiff := ihr hq.2 hulocal hurlocal h2z0 h2z1
          constructor
          · intro h
            have hqle : r.quantile (u - l.total) ≤ 2 * z - 1 := by
              linarith
            have := hiff.mp hqle
            linarith
          · intro h
            have hlocal : u - l.total ≤ r.piecewiseCDF (2 * z - 1) := by
              linarith
            have := hiff.mpr hlocal
            linarith

/--
The selected leaf endpoint and the continuous quantile lie in the same
depth-`L` dyadic cell.
-/
theorem selectedLeaf_sub_quantile_le {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ q.total) :
    |q.selectedLeaf u - q.quantile u| ≤ 1 / ((2 ^ L : ℕ) : ℝ) := by
  induction q generalizing u with
  | leaf m =>
      have hqu := (leaf m).quantile_mem_unit hq hu0 hu1
      simp only [selectedLeaf]
      rw [abs_of_nonpos (by simpa using hqu.1)]
      norm_num
      linarith [hqu.2]
  | @branch L l r ihl ihr =>
      simp only [selectedLeaf, quantile]
      by_cases hu : u ≤ l.total
      · rw [ite_eq_left hu, ite_eq_left hu]
        have h := ihl hq.1 hu0 hu
        rw [show l.selectedLeaf u / 2 - l.quantile u / 2 =
          (l.selectedLeaf u - l.quantile u) / 2 by ring]
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [pow_succ]
        norm_num at h ⊢
        nlinarith
      · rw [ite_eq_right hu, ite_eq_right hu]
        have hulocal : 0 ≤ u - l.total := by linarith
        have hurlocal : u - l.total ≤ r.total := by
          rw [total] at hu1
          linarith
        have h := ihr hq.2 hulocal hurlocal
        rw [show (1 + r.selectedLeaf (u - l.total)) / 2 -
            (1 + r.quantile (u - l.total)) / 2 =
          (r.selectedLeaf (u - l.total) -
            r.quantile (u - l.total)) / 2 by ring]
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [pow_succ]
        norm_num at h ⊢
        nlinarith

/-- The height-`1/2` tent on the unit interval, in local coordinates. -/
def unitTent (z : ℝ) : ℝ :=
  if z ≤ 1 / 2 then z else 1 - z

/--
The integrated Haar series, written recursively. At a branch it adds the
root imbalance and then evaluates the unique child series whose support
contains `z`.
-/
def haarSeries : {L : ℕ} → DyadicMass L → ℝ → ℝ
  | 0, leaf _ => fun _ => 0
  | _ + 1, branch l r => fun z =>
      (total l - total r) * unitTent z +
        if z ≤ 1 / 2 then haarSeries l (2 * z)
        else haarSeries r (2 * z - 1)

/-- Pointwise integrated Haar expansion of the explicit piecewise-linear CDF. -/
theorem cdf_sub_linear_eq_haar {L : ℕ} (q : DyadicMass L)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.piecewiseCDF z - q.total * z = q.haarSeries z := by
  induction q generalizing z with
  | leaf m => simp [piecewiseCDF, total, haarSeries]
  | @branch L l r ihl ihr =>
      by_cases hz : z ≤ 1 / 2
      · have h2z0 : 0 ≤ 2 * z := by linarith
        have h2z1 : 2 * z ≤ 1 := by linarith
        rw [piecewiseCDF, haarSeries]
        simp only [hz, ite_eq_left]
        rw [← ihl h2z0 h2z1]
        rw [unitTent, ite_eq_left hz]
        simp only [total]
        ring
      · have h2z0 : 0 ≤ 2 * z - 1 := by linarith
        have h2z1 : 2 * z - 1 ≤ 1 := by linarith
        rw [piecewiseCDF, haarSeries]
        simp only [hz]
        rw [← ihr h2z0 h2z1]
        rw [unitTent, ite_eq_right hz]
        simp only [total, ite_false]
        ring

end DyadicMass

/-! ## Dyadic tents and their elementary integrals -/

/--
The height-`1/2` tent on `[l,l+p]`. Splitting into `Icc` and `Ioc` makes
the two affine pieces disjoint without changing any Lebesgue integral.
-/
def dyadicTent (l p z : ℝ) : ℝ :=
  (Icc l (l + p / 2)).indicator (fun x => (x - l) / p) z +
    (Ioc (l + p / 2) (l + p)).indicator (fun x => (l + p - x) / p) z

theorem dyadicTent_eq_zero_of_not_mem {l p z : ℝ} (hp : 0 ≤ p)
    (hz : z ∉ Icc l (l + p)) :
    dyadicTent l p z = 0 := by
  have hzL : z ∉ Icc l (l + p / 2) := by
    intro h
    apply hz
    constructor <;> linarith [h.1, h.2]
  have hzR : z ∉ Ioc (l + p / 2) (l + p) := by
    intro h
    apply hz
    constructor <;> linarith [h.1, h.2]
  simp [dyadicTent, hzL, hzR]

/-- A nonzero tent value lies in the interior of its supporting interval. -/
theorem dyadicTent_ne_zero_mem_Ioo {l p z : ℝ} (hp : 0 < p)
    (hz : dyadicTent l p z ≠ 0) :
    z ∈ Ioo l (l + p) := by
  have hmem : z ∈ Icc l (l + p) := by
    by_contra hout
    exact hz (dyadicTent_eq_zero_of_not_mem hp.le hout)
  have hneL : z ≠ l := by
    intro heq
    subst z
    have hL : l ∈ Icc l (l + p / 2) := by constructor <;> linarith
    have hR : l ∉ Ioc (l + p / 2) (l + p) := by
      intro h
      linarith [h.1]
    simp [dyadicTent, hL, hR] at hz
  have hneR : z ≠ l + p := by
    intro heq
    subst z
    have hL : l + p ∉ Icc l (l + p / 2) := by
      intro h
      linarith [h.2]
    have hR : l + p ∈ Ioc (l + p / 2) (l + p) := by
      constructor <;> linarith
    simp [dyadicTent, hL, hR] at hz
  exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hneL), lt_of_le_of_ne hmem.2 hneR⟩

private theorem left_sq_integral (l p : ℝ) (hp : 0 < p) :
    (∫ z in l..l + p / 2, ((z - l) / p) ^ 2) = p / 24 := by
  have hpow : IntervalIntegrable (fun z : ℝ => z ^ 2) volume l (l + p / 2) :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun z : ℝ => 2 * l * z) volume l (l + p / 2) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ => l ^ 2) volume l (l + p / 2) :=
    continuous_const.intervalIntegrable _ _
  rw [show (fun z : ℝ => ((z - l) / p) ^ 2) =
      fun z => ((z ^ 2 - 2 * l * z) + l ^ 2) / p ^ 2 by
    funext z
    ring]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_add (hpow.sub hlin) hconst]
  rw [intervalIntegral.integral_sub hpow hlin]
  rw [integral_pow]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_id]
  rw [intervalIntegral.integral_const]
  field_simp
  ring

private theorem right_sq_integral (l p : ℝ) (hp : 0 < p) :
    (∫ z in l + p / 2..l + p, ((l + p - z) / p) ^ 2) = p / 24 := by
  have hpow : IntervalIntegrable (fun z : ℝ => z ^ 2) volume (l + p / 2) (l + p) :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun z : ℝ => 2 * (l + p) * z)
      volume (l + p / 2) (l + p) :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ => (l + p) ^ 2)
      volume (l + p / 2) (l + p) :=
    continuous_const.intervalIntegrable _ _
  rw [show (fun z : ℝ => ((l + p - z) / p) ^ 2) =
      fun z => ((z ^ 2 - 2 * (l + p) * z) + (l + p) ^ 2) / p ^ 2 by
    funext z
    ring]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_add (hpow.sub hlin) hconst]
  rw [intervalIntegral.integral_sub hpow hlin]
  rw [integral_pow]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_id]
  rw [intervalIntegral.integral_const]
  field_simp
  ring

private theorem dyadicTent_sq_pointwise (l p z : ℝ) :
    dyadicTent l p z ^ 2 =
      (Icc l (l + p / 2)).indicator (fun x => ((x - l) / p) ^ 2) z +
      (Ioc (l + p / 2) (l + p)).indicator (fun x => ((l + p - x) / p) ^ 2) z := by
  by_cases hL : z ∈ Icc l (l + p / 2)
  · have hR : z ∉ Ioc (l + p / 2) (l + p) := by
      intro h
      linarith [hL.2, h.1]
    simp [dyadicTent, hL, hR]
  · by_cases hR : z ∈ Ioc (l + p / 2) (l + p)
    · simp [dyadicTent, hL, hR]
    · simp [dyadicTent, hL, hR]

/-- The exact tent normalization used in Section 2: `∫ tau_v² = p_v/12`. -/
theorem dyadicTent_sq_integral (l p : ℝ) (hp : 0 < p) :
    (∫ z, dyadicTent l p z ^ 2) = p / 12 := by
  have hleft : IntegrableOn (fun z : ℝ => ((z - l) / p) ^ 2)
      (Icc l (l + p / 2)) :=
    ((continuous_id.sub continuous_const).div_const p |>.pow 2).integrableOn_Icc
  have hright : IntegrableOn (fun z : ℝ => ((l + p - z) / p) ^ 2)
      (Ioc (l + p / 2) (l + p)) :=
    ((continuous_const.sub continuous_id).div_const p |>.pow 2).integrableOn_Ioc
  rw [show (fun z : ℝ => dyadicTent l p z ^ 2) = fun z =>
      (Icc l (l + p / 2)).indicator (fun x => ((x - l) / p) ^ 2) z +
      (Ioc (l + p / 2) (l + p)).indicator
        (fun x => ((l + p - x) / p) ^ 2) z by
    funext z
    exact dyadicTent_sq_pointwise l p z]
  rw [MeasureTheory.integral_add (hleft.integrable_indicator measurableSet_Icc)
    (hright.integrable_indicator measurableSet_Ioc)]
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : l ≤ l + p / 2)]
  rw [← intervalIntegral.integral_of_le (by linarith : l + p / 2 ≤ l + p)]
  rw [left_sq_integral l p hp, right_sq_integral l p hp]
  ring

/-- Tents with separated interiors have zero pointwise product. -/
theorem dyadicTent_mul_eq_zero_of_separated {l₁ p₁ l₂ p₂ z : ℝ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hsep : l₁ + p₁ ≤ l₂ ∨ l₂ + p₂ ≤ l₁) :
    dyadicTent l₁ p₁ z * dyadicTent l₂ p₂ z = 0 := by
  by_cases h1 : dyadicTent l₁ p₁ z = 0
  · simp [h1]
  by_cases h2 : dyadicTent l₂ p₂ z = 0
  · simp [h2]
  have hm1 := dyadicTent_ne_zero_mem_Ioo hp₁ h1
  have hm2 := dyadicTent_ne_zero_mem_Ioo hp₂ h2
  rcases hsep with hsep | hsep
  · exfalso
    linarith [hm1.2, hm2.1]
  · exfalso
    linarith [hm2.2, hm1.1]

theorem dyadicTent_stronglyMeasurable (l p : ℝ) :
    StronglyMeasurable (dyadicTent l p) := by
  exact (((continuous_id.sub continuous_const).div_const p).stronglyMeasurable.indicator
      measurableSet_Icc).add
    (((continuous_const.sub continuous_id).div_const p).stronglyMeasurable.indicator
      measurableSet_Ioc)

theorem dyadicTent_integrable (l p : ℝ) :
    Integrable (dyadicTent l p) := by
  apply Integrable.add
  · exact ((continuous_id.sub continuous_const).div_const p).integrableOn_Icc
      |>.integrable_indicator measurableSet_Icc
  · exact ((continuous_const.sub continuous_id).div_const p).integrableOn_Ioc
      |>.integrable_indicator measurableSet_Ioc

theorem abs_dyadicTent_le_half (l p z : ℝ) (hp : 0 < p) :
    |dyadicTent l p z| ≤ 1 / 2 := by
  by_cases hL : z ∈ Icc l (l + p / 2)
  · have hR : z ∉ Ioc (l + p / 2) (l + p) := by
      intro h
      linarith [hL.2, h.1]
    rw [dyadicTent]
    simp only [Set.indicator_of_mem hL, Set.indicator_of_notMem hR, add_zero]
    rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hL.1) hp.le)]
    exact (div_le_iff₀ hp).2 (by linarith [hL.2])
  · by_cases hR : z ∈ Ioc (l + p / 2) (l + p)
    · rw [dyadicTent]
      simp only [Set.indicator_of_notMem hL, Set.indicator_of_mem hR, zero_add]
      rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hR.2) hp.le)]
      exact (div_le_iff₀ hp).2 (by linarith [hR.1])
    · simp [dyadicTent, hL, hR]

theorem dyadicTent_mul_integrable (l₁ p₁ l₂ p₂ : ℝ) (hp₁ : 0 < p₁) :
    Integrable (fun z => dyadicTent l₁ p₁ z * dyadicTent l₂ p₂ z) := by
  apply (dyadicTent_integrable l₂ p₂).bdd_mul
  · exact (dyadicTent_stronglyMeasurable l₁ p₁).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using abs_dyadicTent_le_half l₁ p₁ z hp₁

/-! ## Flattening the recursive Haar series -/

/-- One internal-node term in the integrated Haar expansion. -/
structure HaarTerm where
  /-- Left endpoint of the dyadic interval supporting the Haar term. -/
  left : ℝ
  /-- Width of the interval supporting the Haar term. -/
  width : ℝ
  /-- Coefficient multiplying the integrated Haar tent. -/
  coeff : ℝ

namespace HaarTerm

/-- Pointwise value of one geometric integrated Haar term. -/
def value (t : HaarTerm) (z : ℝ) : ℝ :=
  t.coeff * dyadicTent t.left t.width z

end HaarTerm

/-- Pointwise value of a finite list of integrated Haar terms. -/
def haarTermSum (ts : List HaarTerm) (z : ℝ) : ℝ :=
  (ts.map (fun t => t.value z)).sum

@[simp] theorem haarTermSum_nil (z : ℝ) :
    haarTermSum [] z = 0 := rfl

@[simp] theorem haarTermSum_cons (t : HaarTerm) (ts : List HaarTerm) (z : ℝ) :
    haarTermSum (t :: ts) z = t.value z + haarTermSum ts z := by
  simp [haarTermSum]

@[simp] theorem haarTermSum_append (s t : List HaarTerm) (z : ℝ) :
    haarTermSum (s ++ t) z = haarTermSum s z + haarTermSum t z := by
  simp [haarTermSum]

/--
List every internal node, placing the root on `[a,a+p]` and recursively
placing the two child lists on its two halves. The coefficient at each
node is exactly its left-subtree mass minus its right-subtree mass.
-/
def DyadicMass.haarTermsAt :
    {L : ℕ} → ℝ → ℝ → DyadicMass L → List HaarTerm
  | 0, _, _, .leaf _ => []
  | _ + 1, a, p, .branch l r =>
      ⟨a, p, l.total - r.total⟩ ::
        (haarTermsAt a (p / 2) l ++
          haarTermsAt (a + p / 2) (p / 2) r)

/-- The internal-node Haar terms in their geometric locations in `[0,1]`. -/
def DyadicMass.haarTerms {L : ℕ} (q : DyadicMass L) : List HaarTerm :=
  q.haarTermsAt 0 1

@[simp] theorem DyadicMass.length_haarTermsAt
    {L : ℕ} (q : DyadicMass L) (a p : ℝ) :
    (q.haarTermsAt a p).length = 2 ^ L - 1 := by
  induction q generalizing a p with
  | leaf => simp [haarTermsAt]
  | @branch L l r ihl ihr =>
      have hpow : 0 < 2 ^ L := Nat.two_pow_pos L
      simp [haarTermsAt, ihl, ihr, pow_succ]
      omega

@[simp] theorem DyadicMass.length_haarTerms
    {L : ℕ} (q : DyadicMass L) :
    q.haarTerms.length = 2 ^ L - 1 := by
  simp [haarTerms]

theorem DyadicMass.haarTermsAt_width_pos
    {L : ℕ} (q : DyadicMass L) {a p : ℝ} (hp : 0 < p)
    {t : HaarTerm} (ht : t ∈ q.haarTermsAt a p) :
    0 < t.width := by
  induction q generalizing a p with
  | leaf =>
      simp [haarTermsAt] at ht
  | @branch L l r ihl ihr =>
      simp only [haarTermsAt, List.mem_cons, List.mem_append] at ht
      rcases ht with rfl | ht | ht
      · exact hp
      · exact ihl (by positivity) ht
      · exact ihr (by positivity) ht

theorem DyadicMass.haarTerms_width_pos
    {L : ℕ} (q : DyadicMass L) {t : HaarTerm} (ht : t ∈ q.haarTerms) :
    0 < t.width := by
  exact q.haarTermsAt_width_pos (by norm_num) ht

private theorem dyadicTent_eq_zero_of_not_mem_Ioo {l p z : ℝ}
    (hp : 0 < p) (hz : z ∉ Ioo l (l + p)) :
    dyadicTent l p z = 0 := by
  by_contra h
  exact hz (dyadicTent_ne_zero_mem_Ioo hp h)

private theorem dyadicTent_eq_unitTent_affine {a p z : ℝ}
    (hp : 0 < p) (hz0 : a ≤ z) (hz1 : z ≤ a + p) :
    dyadicTent a p z = DyadicMass.unitTent ((z - a) / p) := by
  by_cases hz : z ≤ a + p / 2
  · have hmem : z ∈ Icc a (a + p / 2) := ⟨hz0, hz⟩
    have hnot : z ∉ Ioc (a + p / 2) (a + p) := by
      intro h
      linarith [h.1]
    have hhalf : (z - a) / p ≤ 1 / 2 := by
      apply (div_le_iff₀ hp).2
      linarith
    rw [DyadicMass.unitTent, ite_eq_left hhalf]
    simp [dyadicTent, hmem, hnot]
  · have hnot : z ∉ Icc a (a + p / 2) := by
      intro h
      exact hz h.2
    have hmem : z ∈ Ioc (a + p / 2) (a + p) :=
      ⟨lt_of_not_ge hz, hz1⟩
    have hhalf : ¬(z - a) / p ≤ 1 / 2 := by
      intro h
      have := (div_le_iff₀ hp).1 h
      linarith
    simp only [dyadicTent, Set.indicator_of_notMem hnot,
      Set.indicator_of_mem hmem, zero_add, DyadicMass.unitTent,
      ite_eq_right hhalf]
    field_simp
    ring

private theorem DyadicMass.haarTermSum_haarTermsAt_eq_zero_of_outside
    {L : ℕ} (q : DyadicMass L) {a p z : ℝ} (hp : 0 < p)
    (hz : z ≤ a ∨ a + p ≤ z) :
    haarTermSum (q.haarTermsAt a p) z = 0 := by
  induction q generalizing a p with
  | leaf =>
      simp [haarTermsAt]
  | @branch L l r ihl ihr =>
      have hp2 : 0 < p / 2 := by positivity
      have hroot : dyadicTent a p z = 0 := by
        apply dyadicTent_eq_zero_of_not_mem_Ioo hp
        intro h
        rcases hz with hz | hz <;> linarith [h.1, h.2]
      have hleft : haarTermSum (l.haarTermsAt a (p / 2)) z = 0 := by
        apply ihl hp2
        rcases hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr (by linarith)
      have hright :
          haarTermSum (r.haarTermsAt (a + p / 2) (p / 2)) z = 0 := by
        apply ihr hp2
        rcases hz with hz | hz
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      simp [haarTermsAt, HaarTerm.value, hroot, hleft, hright]

/--
The recursive integrated Haar series is the sum of every internal-node
coefficient times its geometric tent, on any positive ambient interval.
-/
theorem DyadicMass.haarSeries_eq_haarTermSumAt
    {L : ℕ} (q : DyadicMass L) {a p z : ℝ}
    (hp : 0 < p) (hz0 : a ≤ z) (hz1 : z ≤ a + p) :
    q.haarSeries ((z - a) / p) =
      haarTermSum (q.haarTermsAt a p) z := by
  induction q generalizing a p z with
  | leaf =>
      simp [haarSeries, haarTermsAt]
  | @branch L l r ihl ihr =>
      have hp2 : 0 < p / 2 := by positivity
      have hroot :
          dyadicTent a p z = DyadicMass.unitTent ((z - a) / p) :=
        dyadicTent_eq_unitTent_affine hp hz0 hz1
      by_cases hz : z ≤ a + p / 2
      · have hhalf : (z - a) / p ≤ 1 / 2 := by
          apply (div_le_iff₀ hp).2
          linarith
        have hcoord : 2 * ((z - a) / p) = (z - a) / (p / 2) := by
          field_simp
        have hactive :
            l.haarSeries (2 * ((z - a) / p)) =
              haarTermSum (l.haarTermsAt a (p / 2)) z := by
          rw [hcoord]
          exact ihl hp2 hz0 hz
        have hinactive :
            haarTermSum (r.haarTermsAt (a + p / 2) (p / 2)) z = 0 :=
          r.haarTermSum_haarTermsAt_eq_zero_of_outside hp2 (Or.inl hz)
        rw [DyadicMass.haarSeries]
        simp only [hhalf, ite_eq_left]
        rw [hactive]
        simp [haarTermsAt, HaarTerm.value, hroot, hinactive]
      · have hhalf : ¬(z - a) / p ≤ 1 / 2 := by
          intro h
          have := (div_le_iff₀ hp).1 h
          linarith
        have hzmid : a + p / 2 ≤ z := le_of_not_ge hz
        have hcoord :
            2 * ((z - a) / p) - 1 =
              (z - (a + p / 2)) / (p / 2) := by
          field_simp
          ring
        have hactive :
            r.haarSeries (2 * ((z - a) / p) - 1) =
              haarTermSum
                (r.haarTermsAt (a + p / 2) (p / 2)) z := by
          rw [hcoord]
          apply ihr hp2 hzmid
          linarith
        have hinactive :
            haarTermSum (l.haarTermsAt a (p / 2)) z = 0 :=
          l.haarTermSum_haarTermsAt_eq_zero_of_outside hp2
            (Or.inr hzmid)
        rw [DyadicMass.haarSeries]
        simp only [hhalf]
        rw [hactive]
        simp [haarTermsAt, HaarTerm.value, hroot, hinactive]

/-- Pointwise finite internal-node expansion on `[0,1]`. -/
theorem DyadicMass.haarSeries_eq_haarTermSum
    {L : ℕ} (q : DyadicMass L) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.haarSeries z = haarTermSum q.haarTerms z := by
  simpa [DyadicMass.haarTerms] using
    q.haarSeries_eq_haarTermSumAt (a := 0) (p := 1) (z := z)
      (by norm_num) hz0 (by simpa using hz1)

/-! ## Geometric support and nesting vocabulary -/

/-- Internal nodes of a depth-`L` complete binary tree. -/
abbrev CompleteHaarNode (L : ℕ) := Σ d : Fin L, Fin (2 ^ d.val)

/-- Left endpoint of the dyadic interval indexed by a complete Haar node. -/
def haarNodeLeft {L : ℕ} (v : CompleteHaarNode L) : ℝ :=
  (v.2.val : ℝ) / (2 ^ v.1.val : ℕ)

/-- Width of the dyadic interval indexed by a complete Haar node. -/
def haarNodeWidth {L : ℕ} (v : CompleteHaarNode L) : ℝ :=
  1 / (2 ^ v.1.val : ℕ)

/-- Integrated Haar tent on the interval indexed by the node. -/
def haarNodeTent {L : ℕ} (v : CompleteHaarNode L) : ℝ → ℝ :=
  dyadicTent (haarNodeLeft v) (haarNodeWidth v)

theorem haarNodeWidth_pos {L : ℕ} (v : CompleteHaarNode L) :
    0 < haarNodeWidth v := by
  simp [haarNodeWidth]

/-- Geometric nesting of two dyadic node supports. -/
def HaarSupportNested {L : ℕ} (v w : CompleteHaarNode L) : Prop :=
  Icc (haarNodeLeft v) (haarNodeLeft v + haarNodeWidth v) ⊆
    Icc (haarNodeLeft w) (haarNodeLeft w + haarNodeWidth w)

theorem haarNodeTent_eq_zero_outside {L : ℕ} (v : CompleteHaarNode L) {z : ℝ}
    (hz : z ∉ Icc (haarNodeLeft v) (haarNodeLeft v + haarNodeWidth v)) :
    haarNodeTent v z = 0 :=
  dyadicTent_eq_zero_of_not_mem (haarNodeWidth_pos v).le hz

theorem HaarSupportNested.trans {L : ℕ} {u v w : CompleteHaarNode L}
    (huv : HaarSupportNested u v) (hvw : HaarSupportNested v w) :
    HaarSupportNested u w :=
  fun _ hz => hvw (huv hz)

/-! ## Canonical complete-tree indexing -/

namespace DyadicMass

/--
The masses of the two children of an internal node `v = ⟨d,k⟩`.
At positive depth, `k` selects the appropriate half-tree recursively.
-/
def nodeChildMasses : {L : ℕ} → DyadicMass L → CompleteHaarNode L → ℝ × ℝ
  | 0, .leaf _, v => Fin.elim0 v.1
  | _ + 1, .branch l r, ⟨⟨0, _⟩, _⟩ => (l.total, r.total)
  | L + 1, .branch l r, ⟨⟨d + 1, hd⟩, v⟩ =>
      let d' : Fin L := ⟨d, Nat.lt_of_succ_lt_succ hd⟩
      let w : Fin (2 ^ d + 2 ^ d) :=
        Fin.cast (by rw [pow_succ]; omega) v
      Fin.addCases
        (fun vl => nodeChildMasses l ⟨d', vl⟩)
        (fun vr => nodeChildMasses r ⟨d', vr⟩) w

/-- The Haar coefficient at a node is its left-child mass minus its right-child mass. -/
def nodeCoefficient {L : ℕ} (q : DyadicMass L) (v : CompleteHaarNode L) : ℝ :=
  (q.nodeChildMasses v).1 - (q.nodeChildMasses v).2

theorem nodeCoefficient_eq_childMass_sub {L : ℕ} (q : DyadicMass L)
    (v : CompleteHaarNode L) :
    q.nodeCoefficient v =
      (q.nodeChildMasses v).1 - (q.nodeChildMasses v).2 :=
  rfl

@[simp] theorem nodeChildMasses_root {L : ℕ} (l r : DyadicMass L) :
    (branch l r).nodeChildMasses
      ⟨0, 0⟩ = (l.total, r.total) :=
  rfl

@[simp] theorem nodeCoefficient_root {L : ℕ} (l r : DyadicMass L) :
    (branch l r).nodeCoefficient
      ⟨0, 0⟩ = l.total - r.total :=
  rfl

/-- Embed a node into the left half-tree one level below a new root. -/
def leftNode {L : ℕ} (v : CompleteHaarNode L) : CompleteHaarNode (L + 1) :=
  ⟨v.1.succ, ⟨v.2.val, by
    change v.2.val < 2 ^ (v.1.val + 1)
    rw [pow_succ]
    omega⟩⟩

/-- Embed a node into the right half-tree one level below a new root. -/
def rightNode {L : ℕ} (v : CompleteHaarNode L) : CompleteHaarNode (L + 1) :=
  ⟨v.1.succ, ⟨2 ^ v.1.val + v.2.val, by
    change 2 ^ v.1.val + v.2.val < 2 ^ (v.1.val + 1)
    rw [pow_succ]
    omega⟩⟩

/-- Identification of the two child index blocks with the next dyadic level. -/
def childFinEquiv (d : ℕ) : Fin (2 ^ d + 2 ^ d) ≃ Fin (2 ^ (d + 1)) :=
  finCongr (by rw [pow_succ]; omega)

theorem succNode_castAdd_eq_leftNode {L : ℕ} (d : Fin L)
    (v : Fin (2 ^ d.val)) :
    (⟨d.succ, childFinEquiv d.val (Fin.castAdd (2 ^ d.val) v)⟩ :
      CompleteHaarNode (L + 1)) = leftNode ⟨d, v⟩ := by
  rfl

theorem succNode_natAdd_eq_rightNode {L : ℕ} (d : Fin L)
    (v : Fin (2 ^ d.val)) :
    (⟨d.succ, childFinEquiv d.val (Fin.natAdd (2 ^ d.val) v)⟩ :
      CompleteHaarNode (L + 1)) = rightNode ⟨d, v⟩ := by
  rfl

@[simp] theorem haarNodeLeft_leftNode {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeLeft (leftNode v) = haarNodeLeft v / 2 := by
  simp [haarNodeLeft, leftNode, pow_succ]
  ring

@[simp] theorem haarNodeWidth_leftNode {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeWidth (leftNode v) = haarNodeWidth v / 2 := by
  simp [haarNodeWidth, leftNode, pow_succ]
  ring

@[simp] theorem haarNodeLeft_rightNode {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeLeft (rightNode v) = 1 / 2 + haarNodeLeft v / 2 := by
  simp [haarNodeLeft, rightNode, pow_succ]
  field_simp

@[simp] theorem haarNodeWidth_rightNode {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeWidth (rightNode v) = haarNodeWidth v / 2 := by
  simp [haarNodeWidth, rightNode, pow_succ]
  ring

@[simp] theorem nodeChildMasses_leftNode {L : ℕ} (l r : DyadicMass L)
    (v : CompleteHaarNode L) :
    (branch l r).nodeChildMasses (leftNode v) = l.nodeChildMasses v := by
  rcases v with ⟨⟨d, hd⟩, v⟩
  simp [leftNode, nodeChildMasses, Fin.addCases]

@[simp] theorem nodeChildMasses_rightNode {L : ℕ} (l r : DyadicMass L)
    (v : CompleteHaarNode L) :
    (branch l r).nodeChildMasses (rightNode v) = r.nodeChildMasses v := by
  rcases v with ⟨⟨d, hd⟩, v⟩
  simp [rightNode, nodeChildMasses, Fin.addCases]

@[simp] theorem nodeCoefficient_leftNode {L : ℕ} (l r : DyadicMass L)
    (v : CompleteHaarNode L) :
    (branch l r).nodeCoefficient (leftNode v) = l.nodeCoefficient v := by
  simp [nodeCoefficient]

@[simp] theorem nodeCoefficient_rightNode {L : ℕ} (l r : DyadicMass L)
    (v : CompleteHaarNode L) :
    (branch l r).nodeCoefficient (rightNode v) = r.nodeCoefficient v := by
  simp [nodeCoefficient]

end DyadicMass

/-! ## Finite tree symmetry and cancellation of cross terms -/

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- A finite law is invariant under a state-space equivalence. -/
def InvariantUnder (μ : FiniteLaw Ω) (e : Ω ≃ Ω) : Prop :=
  ∀ ω, μ.mass (e ω) = μ.mass ω

/--
An observable has an odd symmetry if a mass-preserving child swap changes
its sign. A local tree automorphism supplies precisely such an equivalence
for an ancestor-descendant coefficient product.
-/
def OddSymmetry (μ : FiniteLaw Ω) (f : Ω → ℝ) : Prop :=
  ∃ e : Ω ≃ Ω, InvariantUnder μ e ∧ ∀ ω, f (e ω) = -f ω

theorem expect_comp_equiv (μ : FiniteLaw Ω) (e : Ω ≃ Ω)
    (he : InvariantUnder μ e) (f : Ω → ℝ) :
    μ.expect (fun ω => f (e ω)) = μ.expect f := by
  rw [expect, expect]
  calc
    ∑ ω, μ.mass ω * f (e ω) = ∑ ω, μ.mass (e ω) * f (e ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [he]
    _ = ∑ ω, μ.mass ω * f ω := by
      exact e.sum_comp (fun ω => μ.mass ω * f ω)

/-- A mass-preserving sign flip forces expectation zero. -/
theorem expect_eq_zero_of_oddSymmetry (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hodd : OddSymmetry μ f) :
    μ.expect f = 0 := by
  rcases hodd with ⟨e, he, hflip⟩
  have hneg : μ.expect f = -μ.expect f := by
    calc
      μ.expect f = μ.expect (fun ω => f (e ω)) :=
        (expect_comp_equiv μ e he f).symm
      _ = -μ.expect f := by
        simp_rw [hflip]
        simp [expect]
  linarith

end FiniteLaw

/-- The interiors of two tent supports are disjoint (endpoints may coincide). -/
def IntervalsSeparated {ι : Type*} (l p : ι → ℝ) (i j : ι) : Prop :=
  l i + p i ≤ l j ∨ l j + p j ≤ l i

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

/-- A finite integrated Haar expansion. -/
def haarCombination (l p : ι → ℝ) (b : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ i, b i * dyadicTent (l i) (p i) z

namespace DyadicMass

theorem branch_succ_fiber {L : ℕ} (l r : DyadicMass L) (d : Fin L)
    (z : ℝ) :
    (∑ y : Fin (2 ^ d.succ.val),
      (branch l r).nodeCoefficient ⟨d.succ, y⟩ *
        dyadicTent (haarNodeLeft ⟨d.succ, y⟩)
          (haarNodeWidth ⟨d.succ, y⟩) z) =
      (∑ y : Fin (2 ^ d.val),
        l.nodeCoefficient ⟨d, y⟩ *
          dyadicTent (haarNodeLeft (leftNode ⟨d, y⟩))
            (haarNodeWidth (leftNode ⟨d, y⟩)) z) +
      ∑ y : Fin (2 ^ d.val),
        r.nodeCoefficient ⟨d, y⟩ *
          dyadicTent (haarNodeLeft (rightNode ⟨d, y⟩))
            (haarNodeWidth (rightNode ⟨d, y⟩)) z := by
  let e := childFinEquiv d.val
  change (∑ y : Fin (2 ^ (d.val + 1)),
    (branch l r).nodeCoefficient ⟨d.succ, y⟩ *
      dyadicTent (haarNodeLeft ⟨d.succ, y⟩)
        (haarNodeWidth ⟨d.succ, y⟩) z) = _
  rw [← e.sum_comp]
  rw [Fin.sum_univ_add]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro y _
    rw [succNode_castAdd_eq_leftNode]
    simp
  · apply Finset.sum_congr rfl
    intro y _
    rw [succNode_natAdd_eq_rightNode]
    simp

theorem dyadicTent_scale_left (l p z : ℝ) (hp : p ≠ 0) :
    dyadicTent (l / 2) (p / 2) z = dyadicTent l p (2 * z) := by
  have hL : z ∈ Icc (l / 2) (l / 2 + (p / 2) / 2) ↔
      2 * z ∈ Icc l (l + p / 2) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hR : z ∈ Ioc (l / 2 + (p / 2) / 2) (l / 2 + p / 2) ↔
      2 * z ∈ Ioc (l + p / 2) (l + p) := by
    simp only [mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases hzL : z ∈ Icc (l / 2) (l / 2 + (p / 2) / 2)
  · have h2zL := hL.mp hzL
    have hzR : z ∉ Ioc (l / 2 + (p / 2) / 2) (l / 2 + p / 2) := by
      intro h
      linarith [hzL.2, h.1]
    have h2zR : 2 * z ∉ Ioc (l + p / 2) (l + p) := hR.not.mp hzR
    rw [dyadicTent, dyadicTent, indicator_of_mem hzL,
      indicator_of_notMem hzR, indicator_of_mem h2zL,
      indicator_of_notMem h2zR]
    field_simp [hp]
  · have h2zL : 2 * z ∉ Icc l (l + p / 2) := hL.not.mp hzL
    by_cases hzR : z ∈ Ioc (l / 2 + (p / 2) / 2) (l / 2 + p / 2)
    · have h2zR := hR.mp hzR
      rw [dyadicTent, dyadicTent, indicator_of_notMem hzL,
        indicator_of_mem hzR, indicator_of_notMem h2zL,
        indicator_of_mem h2zR]
      field_simp [hp]
    · have h2zR : 2 * z ∉ Ioc (l + p / 2) (l + p) := hR.not.mp hzR
      rw [dyadicTent, dyadicTent, indicator_of_notMem hzL,
        indicator_of_notMem hzR, indicator_of_notMem h2zL,
        indicator_of_notMem h2zR]

theorem dyadicTent_scale_right (l p z : ℝ) (hp : p ≠ 0) :
    dyadicTent (1 / 2 + l / 2) (p / 2) z =
      dyadicTent l p (2 * z - 1) := by
  have hL : z ∈ Icc (1 / 2 + l / 2)
      (1 / 2 + l / 2 + (p / 2) / 2) ↔
      2 * z - 1 ∈ Icc l (l + p / 2) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hR : z ∈ Ioc (1 / 2 + l / 2 + (p / 2) / 2)
      (1 / 2 + l / 2 + p / 2) ↔
      2 * z - 1 ∈ Ioc (l + p / 2) (l + p) := by
    simp only [mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases hzL : z ∈ Icc (1 / 2 + l / 2)
      (1 / 2 + l / 2 + (p / 2) / 2)
  · have h2zL := hL.mp hzL
    have hzR : z ∉ Ioc (1 / 2 + l / 2 + (p / 2) / 2)
        (1 / 2 + l / 2 + p / 2) := by
      intro h
      linarith [hzL.2, h.1]
    have h2zR : 2 * z - 1 ∉ Ioc (l + p / 2) (l + p) := hR.not.mp hzR
    rw [dyadicTent, dyadicTent, indicator_of_mem hzL,
      indicator_of_notMem hzR, indicator_of_mem h2zL,
      indicator_of_notMem h2zR]
    field_simp [hp]
    ring
  · have h2zL : 2 * z - 1 ∉ Icc l (l + p / 2) := hL.not.mp hzL
    by_cases hzR : z ∈ Ioc (1 / 2 + l / 2 + (p / 2) / 2)
        (1 / 2 + l / 2 + p / 2)
    · have h2zR := hR.mp hzR
      rw [dyadicTent, dyadicTent, indicator_of_notMem hzL,
        indicator_of_mem hzR, indicator_of_notMem h2zL,
        indicator_of_mem h2zR]
      field_simp [hp]
      ring
    · have h2zR : 2 * z - 1 ∉ Ioc (l + p / 2) (l + p) := hR.not.mp hzR
      rw [dyadicTent, dyadicTent, indicator_of_notMem hzL,
        indicator_of_notMem hzR, indicator_of_notMem h2zL,
        indicator_of_notMem h2zR]

theorem haarCombination_leftNode {L : ℕ} (b : CompleteHaarNode L → ℝ)
    (z : ℝ) :
    (∑ v : CompleteHaarNode L, b v *
      dyadicTent (haarNodeLeft (leftNode v)) (haarNodeWidth (leftNode v)) z) =
      haarCombination haarNodeLeft haarNodeWidth b (2 * z) := by
  unfold haarCombination
  apply Finset.sum_congr rfl
  intro v _
  rw [haarNodeLeft_leftNode, haarNodeWidth_leftNode,
    dyadicTent_scale_left _ _ _ (haarNodeWidth_pos v).ne']

theorem haarCombination_rightNode {L : ℕ} (b : CompleteHaarNode L → ℝ)
    (z : ℝ) :
    (∑ v : CompleteHaarNode L, b v *
      dyadicTent (haarNodeLeft (rightNode v)) (haarNodeWidth (rightNode v)) z) =
      haarCombination haarNodeLeft haarNodeWidth b (2 * z - 1) := by
  unfold haarCombination
  apply Finset.sum_congr rfl
  intro v _
  rw [haarNodeLeft_rightNode, haarNodeWidth_rightNode,
    dyadicTent_scale_right _ _ _ (haarNodeWidth_pos v).ne']

theorem haarNodeLeft_nonneg {L : ℕ} (v : CompleteHaarNode L) :
    0 ≤ haarNodeLeft v := by
  unfold haarNodeLeft
  positivity

theorem haarNodeRight_le_one {L : ℕ} (v : CompleteHaarNode L) :
    haarNodeLeft v + haarNodeWidth v ≤ 1 := by
  unfold haarNodeLeft haarNodeWidth
  have hp : (0 : ℝ) < (2 ^ v.1.val : ℕ) := by positivity
  rw [← add_div]
  apply (div_le_one hp).2
  norm_cast
  omega

theorem haarCombination_eq_zero_of_outside {L : ℕ}
    (b : CompleteHaarNode L → ℝ) {z : ℝ} (hz : z ≤ 0 ∨ 1 ≤ z) :
    haarCombination haarNodeLeft haarNodeWidth b z = 0 := by
  unfold haarCombination
  apply Finset.sum_eq_zero
  intro v _
  suffices dyadicTent (haarNodeLeft v) (haarNodeWidth v) z = 0 by
    simp [this]
  by_contra h
  have hm := dyadicTent_ne_zero_mem_Ioo (haarNodeWidth_pos v) h
  rcases hz with hz | hz
  · linarith [hm.1, haarNodeLeft_nonneg v]
  · linarith [hm.2, haarNodeRight_le_one v]

theorem branch_root_fiber {L : ℕ} (l r : DyadicMass L) (z : ℝ) :
    (∑ y : Fin (2 ^ (0 : Fin (L + 1)).val),
      (branch l r).nodeCoefficient ⟨(0 : Fin (L + 1)), y⟩ *
        dyadicTent (haarNodeLeft ⟨(0 : Fin (L + 1)), y⟩)
          (haarNodeWidth ⟨(0 : Fin (L + 1)), y⟩) z) =
      (l.total - r.total) * dyadicTent 0 1 z := by
  classical
  let e : Fin 1 ≃ Fin (2 ^ (0 : Fin (L + 1)).val) :=
    finCongr (by norm_num)
  rw [← e.sum_comp, Fin.sum_univ_one]
  have he : e 0 = 0 := by
    apply Fin.ext
    norm_num [e]
  rw [he, nodeCoefficient_root]
  norm_num [haarNodeLeft, haarNodeWidth]

/--
The recursive Haar series is exactly the canonical finite sum over all
internal nodes `⟨d,k⟩` of the complete depth-`L` tree.
-/
theorem haarSeries_eq_haarCombination {L : ℕ} (q : DyadicMass L) {z : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.haarSeries z =
      haarCombination haarNodeLeft haarNodeWidth q.nodeCoefficient z := by
  induction q generalizing z with
  | leaf =>
      simp [haarSeries, haarCombination]
  | @branch L l r ihl ihr =>
      unfold haarCombination
      rw [Fintype.sum_sigma, Fin.sum_univ_succ]
      simp_rw [branch_succ_fiber]
      rw [Finset.sum_add_distrib]
      rw [← Fintype.sum_sigma (fun v : CompleteHaarNode L =>
        l.nodeCoefficient v * dyadicTent (haarNodeLeft (leftNode v))
          (haarNodeWidth (leftNode v)) z)]
      rw [← Fintype.sum_sigma (fun v : CompleteHaarNode L =>
        r.nodeCoefficient v * dyadicTent (haarNodeLeft (rightNode v))
          (haarNodeWidth (rightNode v)) z)]
      rw [haarCombination_leftNode, haarCombination_rightNode]
      have htent : dyadicTent 0 1 z = unitTent z := by
        simpa using dyadicTent_eq_unitTent_affine
          (a := 0) (p := 1) (z := z) (by norm_num) hz0 (by simpa using hz1)
      rw [branch_root_fiber]
      rw [htent]
      simp only [haarSeries]
      by_cases hz : z ≤ 1 / 2
      · rw [ite_eq_left hz, ihl (by linarith) (by linarith)]
        rw [haarCombination_eq_zero_of_outside r.nodeCoefficient
          (Or.inl (by linarith : 2 * z - 1 ≤ 0))]
        ring
      · rw [ite_eq_right hz, ihr (by linarith) (by linarith)]
        rw [haarCombination_eq_zero_of_outside l.nodeCoefficient
          (Or.inr (by linarith : 1 ≤ 2 * z))]
        ring

/-- The canonical node sum is the CDF deviation on the unit interval. -/
theorem cdf_sub_linear_eq_haarCombination {L : ℕ} (q : DyadicMass L)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    q.piecewiseCDF z - q.total * z =
      haarCombination haarNodeLeft haarNodeWidth q.nodeCoefficient z := by
  rw [q.cdf_sub_linear_eq_haar hz0 hz1,
    q.haarSeries_eq_haarCombination hz0 hz1]

end DyadicMass

/-- Squared `L²` norm of a finite integrated Haar expansion. -/
def haarL2 (l p : ι → ℝ) (b : ι → ℝ) : ℝ :=
  ∫ z, haarCombination l p b z ^ 2

theorem haarL2_eq_gram (l p b : ι → ℝ) (hp : ∀ i, 0 < p i) :
    haarL2 l p b =
      ∑ i, ∑ j, (b i * b j) *
        ∫ z, dyadicTent (l i) (p i) z * dyadicTent (l j) (p j) z := by
  unfold haarL2 haarCombination
  rw [show (fun z : ℝ => (∑ i, b i * dyadicTent (l i) (p i) z) ^ 2) =
      fun z => ∑ i, ∑ j, (b i * b j) *
        (dyadicTent (l i) (p i) z * dyadicTent (l j) (p j) z) by
    funext z
    simp only [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [MeasureTheory.integral_const_mul]
    · intro j _
      exact (dyadicTent_mul_integrable _ _ _ _ (hp i)).const_mul _
  · intro i _
    exact MeasureTheory.integrable_finsetSum _ fun j _ =>
      (dyadicTent_mul_integrable _ _ _ _ (hp i)).const_mul _

private theorem expect_double_sum (μ : FiniteLaw Ω) (b : Ω → ι → ℝ)
    (G : ι → ι → ℝ) :
    μ.expect (fun ω => ∑ i, ∑ j, (b ω i * b ω j) * G i j) =
      ∑ i, ∑ j, G i j * μ.expect (fun ω => b ω i * b ω j) := by
  rw [FiniteLaw.expect]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [FiniteLaw.expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/--
Expected Parseval identity for integrated Haar functions. For unequal
nodes, either their interiors are disjoint or a tree child swap makes the
coefficient product odd. Thus every cross term vanishes.
-/
theorem expected_haarL2 (μ : FiniteLaw Ω) (l p : ι → ℝ)
    (b : Ω → ι → ℝ) (hp : ∀ i, 0 < p i)
    (hsym : ∀ i j, i ≠ j → IntervalsSeparated l p i j ∨
      μ.OddSymmetry (fun ω => b ω i * b ω j)) :
    μ.expect (fun ω => haarL2 l p (b ω)) =
      (1 / 12) * ∑ i, p i * μ.expect (fun ω => (b ω i) ^ 2) := by
  simp_rw [haarL2_eq_gram l p _ hp]
  rw [expect_double_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [show (fun ω => b ω i * b ω i) = fun ω => (b ω i) ^ 2 by
      funext
      ring]
    rw [show (fun z => dyadicTent (l i) (p i) z * dyadicTent (l i) (p i) z) =
      fun z => dyadicTent (l i) (p i) z ^ 2 by
      funext
      ring]
    rw [dyadicTent_sq_integral _ _ (hp i)]
    ring
  · intro j _ hji
    have hij : i ≠ j := Ne.symm hji
    rcases hsym i j hij with hsep | hodd
    · have hzero : (fun z => dyadicTent (l i) (p i) z *
          dyadicTent (l j) (p j) z) = fun _ => 0 := by
        funext z
        exact dyadicTent_mul_eq_zero_of_separated (hp i) (hp j) hsep
      rw [hzero]
      simp
    · rw [μ.expect_eq_zero_of_oddSymmetry _ hodd]
      simp
  · simp

/-! ## Quantile/CDF cost and Cauchy--Schwarz -/

/--
The elementary one-dimensional monotone-transport cost: the area between
the source and target CDFs. This representation avoids introducing a
separate Wasserstein API.
-/
def cdfTransportArea (f : ℝ → ℝ) : ℝ :=
  ∫ z in Icc (0 : ℝ) 1, |f z|

private def leStep (a b : ℝ) : ℝ :=
  if a ≤ b then 1 else 0

private theorem integral_abs_leStep_right
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ z in Icc (0 : ℝ) 1, |leStep a z - leStep b z|) = |a - b| := by
  rcases le_total a b with hab | hba
  · have heq : EqOn
        (fun z : ℝ => |leStep a z - leStep b z|)
        ((Ico a b).indicator (fun _ : ℝ => 1)) (Icc (0 : ℝ) 1) := by
      intro z _
      by_cases haz : a ≤ z
      · by_cases hbz : b ≤ z
        · have hnot : z ∉ Ico a b := fun h => (not_lt_of_ge hbz) h.2
          simp [leStep, haz, hbz, hnot]
        · have hmem : z ∈ Ico a b := ⟨haz, lt_of_not_ge hbz⟩
          simp [leStep, haz, hbz, hmem]
      · have hbz : ¬b ≤ z := fun hbz => haz (hab.trans hbz)
        have hnot : z ∉ Ico a b := fun h => haz h.1
        simp [leStep, haz, hbz, hnot]
    rw [setIntegral_congr_fun measurableSet_Icc heq]
    rw [setIntegral_indicator measurableSet_Ico]
    have hinter : Icc (0 : ℝ) 1 ∩ Ico a b = Ico a b := by
      apply inter_eq_right.mpr
      intro z hz
      exact ⟨ha.1.trans hz.1, hz.2.le.trans hb.2⟩
    rw [hinter]
    simp [Real.volume_Ico, measureReal_def, hab,
      abs_of_nonpos (sub_nonpos.mpr hab)]
  · have heq : EqOn
        (fun z : ℝ => |leStep a z - leStep b z|)
        ((Ico b a).indicator (fun _ : ℝ => 1)) (Icc (0 : ℝ) 1) := by
      intro z _
      by_cases hbz : b ≤ z
      · by_cases haz : a ≤ z
        · have hnot : z ∉ Ico b a := fun h => (not_lt_of_ge haz) h.2
          simp [leStep, haz, hbz, hnot]
        · have hmem : z ∈ Ico b a := ⟨hbz, lt_of_not_ge haz⟩
          simp [leStep, haz, hbz, hmem]
      · have haz : ¬a ≤ z := fun haz => hbz (hba.trans haz)
        have hnot : z ∉ Ico b a := fun h => hbz h.1
        simp [leStep, haz, hbz, hnot]
    rw [setIntegral_congr_fun measurableSet_Icc heq]
    rw [setIntegral_indicator measurableSet_Ico]
    have hinter : Icc (0 : ℝ) 1 ∩ Ico b a = Ico b a := by
      apply inter_eq_right.mpr
      intro z hz
      exact ⟨hb.1.trans hz.1, hz.2.le.trans ha.2⟩
    rw [hinter]
    simp [Real.volume_Ico, measureReal_def, hba,
      abs_of_nonneg (sub_nonneg.mpr hba)]

private theorem integral_abs_leStep_left
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ z in Icc (0 : ℝ) 1, |leStep z a - leStep z b|) = |a - b| := by
  rcases le_total a b with hab | hba
  · have heq : EqOn
        (fun z : ℝ => |leStep z a - leStep z b|)
        ((Ioc a b).indicator (fun _ : ℝ => 1)) (Icc (0 : ℝ) 1) := by
      intro z _
      by_cases hza : z ≤ a
      · have hzb : z ≤ b := hza.trans hab
        have hnot : z ∉ Ioc a b := fun h => (not_lt_of_ge hza) h.1
        simp [leStep, hza, hzb, hnot]
      · by_cases hzb : z ≤ b
        · have hmem : z ∈ Ioc a b := ⟨lt_of_not_ge hza, hzb⟩
          simp [leStep, hza, hzb, hmem]
        · have hnot : z ∉ Ioc a b := fun h => hzb h.2
          simp [leStep, hza, hzb, hnot]
    rw [setIntegral_congr_fun measurableSet_Icc heq]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hinter : Icc (0 : ℝ) 1 ∩ Ioc a b = Ioc a b := by
      apply inter_eq_right.mpr
      intro z hz
      exact ⟨ha.1.trans hz.1.le, hz.2.trans hb.2⟩
    rw [hinter]
    simp [Real.volume_Ioc, measureReal_def, hab,
      abs_of_nonpos (sub_nonpos.mpr hab)]
  · have heq : EqOn
        (fun z : ℝ => |leStep z a - leStep z b|)
        ((Ioc b a).indicator (fun _ : ℝ => 1)) (Icc (0 : ℝ) 1) := by
      intro z _
      by_cases hzb : z ≤ b
      · have hza : z ≤ a := hzb.trans hba
        have hnot : z ∉ Ioc b a := fun h => (not_lt_of_ge hzb) h.1
        simp [leStep, hza, hzb, hnot]
      · by_cases hza : z ≤ a
        · have hmem : z ∈ Ioc b a := ⟨lt_of_not_ge hzb, hza⟩
          simp [leStep, hza, hzb, hmem]
        · have hnot : z ∉ Ioc b a := fun h => hza h.2
          simp [leStep, hza, hzb, hnot]
    rw [setIntegral_congr_fun measurableSet_Icc heq]
    rw [setIntegral_indicator measurableSet_Ioc]
    have hinter : Icc (0 : ℝ) 1 ∩ Ioc b a = Ioc b a := by
      apply inter_eq_right.mpr
      intro z hz
      exact ⟨hb.1.trans hz.1.le, hz.2.trans ha.2⟩
    rw [hinter]
    simp [Real.volume_Ioc, measureReal_def, hba,
      abs_of_nonneg (sub_nonneg.mpr hba)]

/--
The one-dimensional quantile/CDF identity, proved directly by expressing
absolute displacement as an integral of threshold disagreements and
swapping the two unit-interval integrals.
-/
theorem integral_abs_quantile_sub_id_eq_integral_abs_cdf_sub_id
    {F T : ℝ → ℝ}
    (_hF : Measurable F) (hT : Measurable T)
    (hF01 : MapsTo F (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hT01 : MapsTo T (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgc : ∀ u ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1,
      T u ≤ z ↔ u ≤ F z) :
    (∫ u in Icc (0 : ℝ) 1, |T u - u|) =
      ∫ z in Icc (0 : ℝ) 1, |F z - z| := by
  let k : ℝ → ℝ → ℝ := fun u z => |leStep (T u) z - leStep u z|
  have hk_meas : Measurable (Function.uncurry k) := by
    have h₁ : Measurable (fun p : ℝ × ℝ => leStep (T p.1) p.2) := by
      apply Measurable.ite
      · exact measurableSet_le (hT.comp measurable_fst) measurable_snd
      · exact measurable_const
      · exact measurable_const
    have h₂ : Measurable (fun p : ℝ × ℝ => leStep p.1 p.2) := by
      apply Measurable.ite
      · exact measurableSet_le measurable_fst measurable_snd
      · exact measurable_const
      · exact measurable_const
    exact (h₁.sub h₂).abs
  have hk_on : IntegrableOn (Function.uncurry k)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) := by
    apply Measure.integrableOn_of_bounded
      (by
        rw [Measure.prod_prod]
        norm_num [Real.volume_Icc])
      hk_meas.aestronglyMeasurable (M := 1)
    filter_upwards with p
    change ‖|leStep (T p.1) p.2 - leStep p.1 p.2|‖ ≤ 1
    rw [Real.norm_eq_abs, abs_abs]
    unfold leStep
    split_ifs <;> norm_num
  have hk : Integrable (Function.uncurry k)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod
        (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hk_on
  calc
    (∫ u in Icc (0 : ℝ) 1, |T u - u|)
        = ∫ u in Icc (0 : ℝ) 1, ∫ z in Icc (0 : ℝ) 1, k u z := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro u hu
          exact (integral_abs_leStep_right (hT01 hu) hu).symm
    _ = ∫ z in Icc (0 : ℝ) 1, ∫ u in Icc (0 : ℝ) 1, k u z :=
      integral_integral_swap hk
    _ = ∫ z in Icc (0 : ℝ) 1, |F z - z| := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro z hz
      change (∫ u in Icc (0 : ℝ) 1, k u z) = |F z - z|
      rw [← integral_abs_leStep_left (hF01 hz) hz]
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hu
      dsimp only [k]
      unfold leStep
      rw [if_congr (hgc u hu z hz)] <;> rfl

/-- An actual quantile map together with an actual selected point. -/
structure MonotoneQuantilePolicy (F : ℝ → ℝ) where
  monotoneCDF : MonotoneOn F (Icc 0 1)
  cdf_measurable : Measurable F
  cdf_mapsTo : MapsTo F (Icc 0 1) (Icc 0 1)
  /-- Measurable generalized inverse of the cumulative distribution function. -/
  quantileMap : ℝ → ℝ
  quantile_measurable : Measurable quantileMap
  quantile_mapsTo : MapsTo quantileMap (Icc 0 1) (Icc 0 1)
  generalizedInverse : ∀ u ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) 1,
    quantileMap u ≤ z ↔ u ≤ F z
  /-- Measurable selected location approximating the quantile map. -/
  selectedPoint : ℝ → ℝ
  selected_measurable : Measurable selectedPoint
  selected_mapsTo : MapsTo selectedPoint (Icc 0 1) (Icc 0 1)
  /-- Uniform upper bound for the distance from a selected location to its quantile. -/
  withinError : ℝ
  withinError_nonneg : 0 ≤ withinError
  selected_close : ∀ u ∈ Icc (0 : ℝ) 1,
    |selectedPoint u - quantileMap u| ≤ withinError

namespace MonotoneQuantilePolicy

/-- Actual cost of the selected-point policy against a uniform request. -/
def expectedDistance {F : ℝ → ℝ} (P : MonotoneQuantilePolicy F) : ℝ :=
  ∫ u in Icc (0 : ℝ) 1, |P.selectedPoint u - u|

/-- Cost of the continuous generalized inverse before leaf rounding. -/
def quantileDistance {F : ℝ → ℝ} (P : MonotoneQuantilePolicy F) : ℝ :=
  ∫ u in Icc (0 : ℝ) 1, |P.quantileMap u - u|

theorem quantileDistance_eq_cdfTransportArea {F : ℝ → ℝ}
    (P : MonotoneQuantilePolicy F) :
    P.quantileDistance = cdfTransportArea (fun z => F z - z) := by
  exact integral_abs_quantile_sub_id_eq_integral_abs_cdf_sub_id
    P.cdf_measurable P.quantile_measurable P.cdf_mapsTo P.quantile_mapsTo
    P.generalizedInverse

private theorem selectedDistance_integrable {F : ℝ → ℝ}
    (P : MonotoneQuantilePolicy F) :
    IntegrableOn (fun u => |P.selectedPoint u - u|) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    (P.selected_measurable.sub measurable_id).abs.aestronglyMeasurable (M := 1)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  change ‖|P.selectedPoint u - u|‖ ≤ 1
  rw [Real.norm_eq_abs, abs_abs]
  have hs := P.selected_mapsTo hu
  exact abs_le.2 ⟨by linarith [hs.1, hu.2], by linarith [hs.2, hu.1]⟩

private theorem quantileDistance_integrable {F : ℝ → ℝ}
    (P : MonotoneQuantilePolicy F) :
    IntegrableOn (fun u => |P.quantileMap u - u|) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    (P.quantile_measurable.sub measurable_id).abs.aestronglyMeasurable (M := 1)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  change ‖|P.quantileMap u - u|‖ ≤ 1
  rw [Real.norm_eq_abs, abs_abs]
  have hq := P.quantile_mapsTo hu
  exact abs_le.2 ⟨by linarith [hq.1, hu.2], by linarith [hq.2, hu.1]⟩

theorem expectedDistance_le {F : ℝ → ℝ} (P : MonotoneQuantilePolicy F)
    : P.expectedDistance ≤ P.withinError +
      cdfTransportArea (fun z => F z - z) := by
  have hrhs : IntegrableOn
      (fun u => P.withinError + |P.quantileMap u - u|) (Icc (0 : ℝ) 1) :=
    (integrableOn_const (C := P.withinError)
      (by simp [Real.volume_Icc])).add P.quantileDistance_integrable
  calc
    P.expectedDistance ≤
        ∫ u in Icc (0 : ℝ) 1, P.withinError + |P.quantileMap u - u| := by
      apply setIntegral_mono_on P.selectedDistance_integrable hrhs measurableSet_Icc
      intro u hu
      calc
        |P.selectedPoint u - u| ≤
            |P.selectedPoint u - P.quantileMap u| +
              |P.quantileMap u - u| := abs_sub_le _ _ _
        _ ≤ P.withinError + |P.quantileMap u - u| :=
          by linarith [P.selected_close u hu]
    _ = P.withinError + P.quantileDistance := by
      rw [MeasureTheory.integral_add
        (integrableOn_const (C := P.withinError)
          (by simp [Real.volume_Icc]))
        P.quantileDistance_integrable]
      simp [quantileDistance]
    _ = P.withinError + cdfTransportArea (fun z => F z - z) := by
      rw [P.quantileDistance_eq_cdfTransportArea]

end MonotoneQuantilePolicy

/-- The explicit dyadic CDF, inverse, and leaf endpoint form an actual policy. -/
def DyadicMass.quantilePolicy {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) :
    MonotoneQuantilePolicy q.piecewiseCDF where
  monotoneCDF := q.piecewiseCDF_monotoneOn hq.nonneg
  cdf_measurable := q.piecewiseCDF_measurable
  cdf_mapsTo := fun z hz => ⟨q.piecewiseCDF_nonneg hq.nonneg hz.1 hz.2,
    by simpa [hq.total_eq_one] using q.piecewiseCDF_le_total hq.nonneg hz.1 hz.2⟩
  quantileMap := q.quantile
  quantile_measurable := q.quantile_measurable
  quantile_mapsTo := fun u hu => q.quantile_mem_unit hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2)
  generalizedInverse := fun u hu z hz => q.quantile_le_iff hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2) hz.1 hz.2
  selectedPoint := q.selectedLeaf
  selected_measurable := q.selectedLeaf_measurable
  selected_mapsTo := fun u hu => q.selectedLeaf_mem_unit hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2)
  withinError := 1 / ((2 ^ L : ℕ) : ℝ)
  withinError_nonneg := by positivity
  selected_close := fun u hu => q.selectedLeaf_sub_quantile_le hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2)

theorem DyadicMass.exists_monotoneQuantilePolicy {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) :
    ∃ P : MonotoneQuantilePolicy q.piecewiseCDF,
      P.withinError = 1 / ((2 ^ L : ℕ) : ℝ) :=
  ⟨q.quantilePolicy hq, rfl⟩

/--
The actual selected-leaf endpoint has cost at most the exact quantile cost
plus one depth-`L` cell width.
-/
theorem DyadicMass.quantile_cost_within_leaf {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) :
    (q.quantilePolicy hq).expectedDistance ≤ 1 / ((2 ^ L : ℕ) : ℝ) +
      cdfTransportArea (fun z => q.piecewiseCDF z - z) := by
  exact (q.quantilePolicy hq).expectedDistance_le

/--
For probability leaf masses, the CDF discrepancy used by the quantile
policy is exactly the recursively defined integrated Haar series.
-/
theorem DyadicMass.quantile_discrepancy_eq_haar {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    q.piecewiseCDF z - z = q.haarSeries z := by
  simpa [hq.total_eq_one] using q.cdf_sub_linear_eq_haar hz.1 hz.2

theorem haarCombination_integrable (l p b : ι → ℝ) :
    Integrable (haarCombination l p b) := by
  unfold haarCombination
  exact integrable_finsetSum _ fun i _ =>
    (dyadicTent_integrable (l i) (p i)).const_mul _

theorem haarCombination_sq_integrable (l p b : ι → ℝ) (hp : ∀ i, 0 < p i) :
    Integrable (fun z => haarCombination l p b z ^ 2) := by
  rw [show (fun z : ℝ => haarCombination l p b z ^ 2) =
      fun z => ∑ i, ∑ j, (b i * b j) *
        (dyadicTent (l i) (p i) z * dyadicTent (l j) (p j) z) by
    funext z
    unfold haarCombination
    simp only [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring]
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ =>
      (dyadicTent_mul_integrable _ _ _ _ (hp i)).const_mul _

theorem cdfTransportArea_nonneg (f : ℝ → ℝ) :
    0 ≤ cdfTransportArea f :=
  integral_nonneg fun _ => abs_nonneg _

/-- Cauchy--Schwarz on the unit interval, proved by Jensen for `x ↦ x²`. -/
theorem integral_abs_sq_le_integral_sq {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1))
    (hfsq : IntegrableOn (fun z => f z ^ 2) (Icc 0 1)) :
    cdfTransportArea f ^ 2 ≤ ∫ z in Icc (0 : ℝ) 1, f z ^ 2 := by
  let ν : Measure ℝ := volume.restrict (Icc 0 1)
  let : IsProbabilityMeasure ν := ⟨by
    simp [ν, Real.volume_Icc]⟩
  have habs : Integrable (fun z => |f z|) ν := hf.norm
  have habssq : Integrable (fun z => |f z| ^ 2) ν := by
    simpa [ν, IntegrableOn, sq_abs] using hfsq
  have hj := (Even.convexOn_pow (even_iff_two_dvd.mpr (by norm_num : 2 ∣ 2)) :
      ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2)).map_integral_le
      (continuous_pow 2).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      habs habssq
  simpa [ν, cdfTransportArea, Function.comp_def] using hj

theorem cdfTransportArea_sq_le_haarL2 (l p b : ι → ℝ) (hp : ∀ i, 0 < p i) :
    cdfTransportArea (haarCombination l p b) ^ 2 ≤ haarL2 l p b := by
  have hsq := haarCombination_sq_integrable l p b hp
  calc
    cdfTransportArea (haarCombination l p b) ^ 2
        ≤ ∫ z in Icc (0 : ℝ) 1, haarCombination l p b z ^ 2 :=
      integral_abs_sq_le_integral_sq
        (haarCombination_integrable l p b).integrableOn hsq.integrableOn
    _ ≤ ∫ z, haarCombination l p b z ^ 2 := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun z => sq_nonneg (haarCombination l p b z)) hsq
    _ = haarL2 l p b := rfl

namespace FiniteLaw

/-- Weighted Cauchy--Schwarz for the project's finite-law expectation. -/
theorem expect_sq_le_expect_sq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.expect f ^ 2 ≤ μ.expect (fun ω => f ω ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => Real.sqrt (μ.mass ω))
    (fun ω => Real.sqrt (μ.mass ω) * f ω)
  have hleft : (∑ ω, Real.sqrt (μ.mass ω) *
      (Real.sqrt (μ.mass ω) * f ω)) = μ.expect f := by
    rw [expect]
    apply Finset.sum_congr rfl
    intro ω _
    rw [← mul_assoc, Real.mul_self_sqrt (μ.mass_nonneg ω)]
  have hmass : (∑ ω, Real.sqrt (μ.mass ω) ^ 2) = 1 := by
    calc
      (∑ ω, Real.sqrt (μ.mass ω) ^ 2) = ∑ ω, μ.mass ω := by
        apply Finset.sum_congr rfl
        intro ω _
        exact Real.sq_sqrt (μ.mass_nonneg ω)
      _ = 1 := μ.sum_mass
  have hright : (∑ ω, (Real.sqrt (μ.mass ω) * f ω) ^ 2) =
      μ.expect (fun ω => f ω ^ 2) := by
    rw [expect]
    apply Finset.sum_congr rfl
    intro ω _
    rw [mul_pow, Real.sq_sqrt (μ.mass_nonneg ω)]
  rw [hleft, hmass, hright, one_mul] at hcs
  exact hcs

theorem expect_le_sqrt_expect_sq (μ : FiniteLaw Ω) (f g : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hg : ∀ ω, 0 ≤ g ω)
    (hfg : ∀ ω, f ω ^ 2 ≤ g ω) :
    μ.expect f ≤ Real.sqrt (μ.expect g) := by
  have hef : 0 ≤ μ.expect f := μ.expect_nonneg hf
  have heg : 0 ≤ μ.expect g := μ.expect_nonneg hg
  rw [Real.le_sqrt hef heg]
  calc
    μ.expect f ^ 2 ≤ μ.expect (fun ω => f ω ^ 2) :=
      μ.expect_sq_le_expect_sq f
    _ ≤ μ.expect g := μ.expect_mono hfg

end FiniteLaw

/-- CDF-area transport followed by Cauchy--Schwarz in space and in state. -/
theorem expected_area_le_sqrt_l2 (μ : FiniteLaw Ω) (l p : ι → ℝ)
    (b : Ω → ι → ℝ) (hp : ∀ i, 0 < p i) :
    μ.expect (fun ω => cdfTransportArea (haarCombination l p (b ω))) ≤
      Real.sqrt (μ.expect (fun ω => haarL2 l p (b ω))) := by
  apply μ.expect_le_sqrt_expect_sq
  · exact fun _ => cdfTransportArea_nonneg _
  · exact fun _ => integral_nonneg fun _ => sq_nonneg _
  · exact fun ω => cdfTransportArea_sq_le_haarL2 l p (b ω) hp

/-!
`gap` below is the abstract hazard telescope
`E[H_L] - m⁻²`. The hypothesis `htelescope` is equation (2):
`Σ p_v E[b_v²] ≤ 2 a² gap`.
-/

/--
Equation (3), with the exact constant. `hcost` is the conditional monotone
quantile bound plus the deterministic within-cell error `1/n`.
-/
theorem transport_cost_equation_three
    (μ : FiniteLaw Ω) (l p : ι → ℝ) (b : Ω → ι → ℝ)
    (cost : Ω → ℝ) (n a gap : ℝ)
    (_hn : 0 < n) (ha : 0 ≤ a) (hgap : 0 ≤ gap)
    (hp : ∀ i, 0 < p i)
    (hcost : ∀ ω, cost ω ≤ 1 / n +
      cdfTransportArea (haarCombination l p (b ω)))
    (hsym : ∀ i j, i ≠ j → IntervalsSeparated l p i j ∨
      μ.OddSymmetry (fun ω => b ω i * b ω j))
    (htelescope : ∑ i, p i * μ.expect (fun ω => (b ω i) ^ 2) ≤
      2 * a ^ 2 * gap) :
    μ.expect cost ≤ 1 / n + a / Real.sqrt 6 * Real.sqrt gap := by
  have hcostExpect : μ.expect cost ≤ 1 / n +
      μ.expect (fun ω => cdfTransportArea (haarCombination l p (b ω))) := by
    calc
      μ.expect cost ≤ μ.expect (fun ω => 1 / n +
          cdfTransportArea (haarCombination l p (b ω))) :=
        μ.expect_mono hcost
      _ = 1 / n + μ.expect (fun ω =>
          cdfTransportArea (haarCombination l p (b ω))) := by
        rw [FiniteLaw.expect, FiniteLaw.expect]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        rw [μ.sum_mass, one_mul]
  have harea := expected_area_le_sqrt_l2 μ l p b hp
  have hhaar := expected_haarL2 μ l p b hp hsym
  have hl2 : μ.expect (fun ω => haarL2 l p (b ω)) ≤ a ^ 2 * gap / 6 := by
    rw [hhaar]
    nlinarith
  have hsqrt6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hcoef_nonneg : 0 ≤ a / Real.sqrt 6 * Real.sqrt gap := by positivity
  have hcoef_sq :
      (a / Real.sqrt 6 * Real.sqrt gap) ^ 2 = a ^ 2 * gap / 6 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
      Real.sq_sqrt hgap]
    ring
  have hsqrtBound : Real.sqrt (μ.expect (fun ω => haarL2 l p (b ω))) ≤
      a / Real.sqrt 6 * Real.sqrt gap := by
    rw [Real.sqrt_le_iff]
    exact ⟨hcoef_nonneg, hcoef_sq ▸ hl2⟩
  linarith

end

end FD1D
