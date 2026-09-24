/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Euclidean Hardy--Littlewood maximal function

This module defines the uncentred maximal function on `Vec3` and proves its
weak `(1,1)` estimate by the metric Vitali covering theorem.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter


noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

abbrev hardyLittlewoodMetricBall (c : Vec3) (r : ℝ) : Set Vec3 := Metric.ball c r

/-- The uncentred Hardy--Littlewood maximal function on `Vec3`. -/
def maximalFunction (f : Vec3 → ℝ≥0∞) (z : Vec3) : ℝ≥0∞ :=
  ⨆ c : Vec3, ⨆ r : ℝ,
    (hardyLittlewoodMetricBall c r).indicator
      (fun _ ↦ ⨍⁻ y in hardyLittlewoodMetricBall c r, f y ∂volume) z

private lemma volume_metricBall (x : Vec3) {r : ℝ} (hr : 0 < r) :
    volume (hardyLittlewoodMetricBall x r) = ENNReal.ofReal ((2 * r) ^ 3) := by
  rw [MeasureTheory.volume_pi_ball x hr]
  simp only [Real.volume_ball, Finset.prod_const]
  norm_num [Fintype.card_fin]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  have hmul : ENNReal.ofReal 2 * ENNReal.ofReal r = ENNReal.ofReal (2 * r) :=
    (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [h2, hmul, ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * r) 3]

theorem volume_metricBall_eq {x : Vec3} {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball x r) = ENNReal.ofReal ((2 * r) ^ 3) := by
  exact volume_metricBall x hr

private lemma volume_metricBall_five_mul_le {x : Vec3} {r : ℝ} (hr : 0 < r) :
    volume (hardyLittlewoodMetricBall x (5 * r)) ≤
      ENNReal.ofReal (5 ^ 3) * volume (hardyLittlewoodMetricBall x r) := by
  rw [volume_metricBall x (by linarith only [hr]), volume_metricBall x hr]
  calc
    ENNReal.ofReal ((2 * (5 * r)) ^ 3) =
        ENNReal.ofReal (5 ^ 3 * (2 * r) ^ 3) := by
      congr 1
      ring
    _ = ENNReal.ofReal (5 ^ 3) * ENNReal.ofReal ((2 * r) ^ 3) :=
      ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (5 ^ 3) * ENNReal.ofReal ((2 * r) ^ 3) := le_rfl

theorem maximalFunction_average_le {f : Vec3 → ℝ≥0∞}
    {c z : Vec3} {r : ℝ} (hz : z ∈ hardyLittlewoodMetricBall c r) :
    ⨍⁻ y in hardyLittlewoodMetricBall c r, f y ∂volume ≤ maximalFunction f z := by
  apply le_iSup₂_of_le c r
  simp only [indicator_of_mem hz]
  exact le_rfl

theorem lowerSemicontinuous_maximalFunction (f : Vec3 → ℝ≥0∞) :
    LowerSemicontinuous (maximalFunction f) := by
  intro z s hzs
  obtain ⟨c, r, h⟩ := exists_lt_of_lt_ciSup₂' hzs
  have hz : z ∈ hardyLittlewoodMetricBall c r :=
    mem_of_indicator_ne_zero (h.trans_le' bot_le |>.ne.symm)
  rw [indicator_of_mem hz] at h
  apply eventually_of_mem
  · exact Metric.isOpen_ball.mem_nhds hz
  · intro y hy
    apply LT.lt.trans_le _ (le_iSup₂ c r)
    rwa [indicator_of_mem hy]

theorem measurable_maximalFunction (f : Vec3 → ℝ≥0∞) :
    Measurable (maximalFunction f) :=
  (lowerSemicontinuous_maximalFunction f).measurable

private lemma metricBall_measurable (c : Vec3) (r : ℝ) :
    MeasurableSet (hardyLittlewoodMetricBall c r) :=
  Metric.isOpen_ball.measurableSet

private lemma metricBall_nonempty {c : Vec3} {r : ℝ} (hr : 0 < r) :
    (hardyLittlewoodMetricBall c r).Nonempty :=
  Metric.nonempty_ball.mpr hr

private lemma maximalAverage_condition_of_mem
    {f : Vec3 → ℝ≥0∞} {l : ℝ≥0∞}
    {c : Vec3} {r : ℝ} (hr : 0 < r)
    (havg : l < ⨍⁻ y in hardyLittlewoodMetricBall c r, f y ∂volume) :
    l * volume (hardyLittlewoodMetricBall c r) ≤
      ∫⁻ y in hardyLittlewoodMetricBall c r, f y := by
  rw [setLAverage_eq] at havg
  have hvol0 : volume (hardyLittlewoodMetricBall c r) ≠ 0 := by
    rw [volume_metricBall c hr]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hvoltop : volume (hardyLittlewoodMetricBall c r) ≠ ∞ := by
    rw [volume_metricBall c hr]
    exact ENNReal.ofReal_ne_top
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hvol0) (Or.inl hvoltop)).mp
  exact havg.le

private theorem measure_biUnion_le_lintegral
    (T : Set (Vec3 × ℝ)) (l : ℝ≥0∞) (f : Vec3 → ℝ≥0∞)
    (hpos : ∀ i ∈ T, 0 < i.2)
    (hbounded : ∃ R : ℝ, ∀ i ∈ T, i.2 ≤ R)
    (hcondition : ∀ i ∈ T,
      l * volume (hardyLittlewoodMetricBall i.1 i.2) ≤
        ∫⁻ y in hardyLittlewoodMetricBall i.1 i.2, f y) :
    l * volume (⋃ i ∈ T, hardyLittlewoodMetricBall i.1 i.2) ≤
      ENNReal.ofReal (5 ^ 3) * ∫⁻ y, f y := by
  obtain ⟨R, hR⟩ := hbounded
  obtain ⟨u, huT, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      T (fun i : Vec3 × ℝ ↦ i.1) (fun i ↦ i.2) R hR 5 (by norm_num)
  have hu_countable : u.Countable := hdisj.countable_of_isOpen
      (fun i hi ↦ Metric.isOpen_ball)
      (fun i hi ↦ metricBall_nonempty (hpos i (huT hi)))
  haveI : Countable u := hu_countable.to_subtype
  let enlarged : Vec3 × ℝ → Set Vec3 :=
    fun i ↦ hardyLittlewoodMetricBall i.1 (5 * i.2)
  have hcover_union :
      (⋃ i ∈ T, hardyLittlewoodMetricBall i.1 i.2) ⊆ ⋃ i ∈ u, enlarged i := by
    intro z hz
    rcases mem_iUnion₂.mp hz with ⟨i, hiT, hzi⟩
    obtain ⟨j, hju, hsubset⟩ := hcover i hiT
    apply mem_iUnion₂.mpr ⟨j, hju, ?_⟩
    exact hsubset hzi
  have henlarged_measure (i : u) :
      volume (enlarged i) ≤
        ENNReal.ofReal (5 ^ 3) * volume (hardyLittlewoodMetricBall i.1.1 i.1.2) := by
    exact volume_metricBall_five_mul_le (hpos i (huT i.property))
  have hdisj_subtype : Pairwise (Function.onFun Disjoint
      (fun i : u ↦ hardyLittlewoodMetricBall i.1.1 i.1.2)) := by
    intro i j hij
    exact hdisj i.property j.property (Subtype.coe_ne_coe.mpr hij)
  have hsum_integral :
      (∑' i : u, ∫⁻ y in hardyLittlewoodMetricBall i.1.1 i.1.2, f y) ≤ ∫⁻ y, f y := by
    calc
      (∑' i : u, ∫⁻ y in hardyLittlewoodMetricBall i.1.1 i.1.2, f y) =
          ∫⁻ y in ⋃ i : u, hardyLittlewoodMetricBall i.1.1 i.1.2, f y := by
            symm
            apply lintegral_iUnion
            · exact fun i ↦ metricBall_measurable i.1.1 i.1.2
            · exact hdisj_subtype
      _ ≤ ∫⁻ y, f y := by
        gcongr
        exact MeasureTheory.Measure.restrict_le_self
  calc
    l * volume (⋃ i ∈ T, hardyLittlewoodMetricBall i.1 i.2) ≤
        l * volume (⋃ i ∈ u, enlarged i) := by
      gcongr
    _ ≤ l * ∑' i : u, volume (enlarged i) := by
      gcongr
      exact measure_biUnion_le volume hu_countable enlarged
    _ ≤ l * ∑' i : u,
        ENNReal.ofReal (5 ^ 3) * volume (hardyLittlewoodMetricBall i.1.1 i.1.2) := by
      gcongr with i
      exact henlarged_measure i
    _ = ENNReal.ofReal (5 ^ 3) *
        ∑' i : u, l * volume (hardyLittlewoodMetricBall i.1.1 i.1.2) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ ENNReal.ofReal (5 ^ 3) *
        ∑' i : u, ∫⁻ y in hardyLittlewoodMetricBall i.1.1 i.1.2, f y := by
      gcongr with i
      exact hcondition i.1 (huT i.2)
    _ ≤ ENNReal.ofReal (5 ^ 3) * ∫⁻ y, f y := by
      gcongr

def maximalLevelBalls (f : Vec3 → ℝ≥0∞)
    (l : ℝ≥0∞) (n : ℕ) : Set (Vec3 × ℝ) :=
  {i | 0 < i.2 ∧ i.2 ≤ (n : ℝ) ∧
    l < ⨍⁻ y in hardyLittlewoodMetricBall i.1 i.2, f y ∂volume}

/-- The weak `(1,1)` estimate for the Euclidean maximal function. -/
theorem measure_maximalFunction_lt_le
    (f : Vec3 → ℝ≥0∞) {l : ℝ≥0∞} (hl : 0 < l) :
    volume {z | l < maximalFunction f z} ≤
      (ENNReal.ofReal (5 ^ 3) / l) * ∫⁻ y, f y := by
  by_cases hltop : l = ∞
  · simp [hltop]
  have hlevel :
      {z | l < maximalFunction f z} =
        ⋃ n, ⋃ i ∈ maximalLevelBalls f l n, hardyLittlewoodMetricBall i.1 i.2 := by
    ext z
    constructor
    · intro hz
      change l < maximalFunction f z at hz
      obtain ⟨c, r, h⟩ := exists_lt_of_lt_ciSup₂' hz
      have hzball : z ∈ hardyLittlewoodMetricBall c r :=
        mem_of_indicator_ne_zero (h.trans_le' bot_le |>.ne.symm)
      rw [indicator_of_mem hzball] at h
      have hr : 0 < r := by
        exact (Metric.nonempty_ball.mp ⟨z, hzball⟩)
      obtain ⟨n, hn⟩ := exists_nat_ge r
      refine mem_iUnion.mpr ⟨n, mem_iUnion₂.mpr ⟨(c, r), ?_, hzball⟩⟩
      exact ⟨hr, hn, h⟩
    · intro hz
      rcases mem_iUnion.mp hz with ⟨n, hz⟩
      rcases mem_iUnion₂.mp hz with ⟨i, hi, hzi⟩
      exact lt_of_lt_of_le hi.2.2 (maximalFunction_average_le hzi)
  have hmono : Monotone (fun n : ℕ ↦
      ⋃ i ∈ maximalLevelBalls f l n, hardyLittlewoodMetricBall i.1 i.2) := by
    intro m n hmn z hz
    rcases mem_iUnion₂.mp hz with ⟨i, hi, hzi⟩
    refine mem_iUnion₂.mpr ⟨i, ?_, hzi⟩
    exact ⟨hi.1, hi.2.1.trans (by exact_mod_cast hmn), hi.2.2⟩
  have hlevel_bound (n : ℕ) :
      l * volume (⋃ i ∈ maximalLevelBalls f l n,
        hardyLittlewoodMetricBall i.1 i.2) ≤ ENNReal.ofReal (5 ^ 3) * ∫⁻ y, f y := by
    apply measure_biUnion_le_lintegral
    · intro i hi
      exact hi.1
    · exact ⟨(n : ℝ), fun i hi ↦ hi.2.1⟩
    · intro i hi
      exact maximalAverage_condition_of_mem hi.1 hi.2.2
  have hrewrite :
      (ENNReal.ofReal (5 ^ 3) / l) * ∫⁻ y, f y =
        (ENNReal.ofReal (5 ^ 3) * ∫⁻ y, f y) / l := by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    ac_rfl
  rw [hrewrite]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hl.ne') (Or.inl hltop)).2
  rw [hlevel, hmono.measure_iUnion, ENNReal.iSup_mul]
  exact iSup_le (fun n ↦ by simpa [mul_comm] using hlevel_bound n)

end CKN.Foundation.Euclidean
