/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Doubling
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Average

/-!
# The parabolic Hardy--Littlewood maximal function

This file defines the uncentred maximal function using the genuine parabolic
metric from `Basic`.  The weak estimate is proved by the Vitali covering
theorem.  The covering argument follows the general metric-measure argument in
`Carleson/ToMathlib/HardyLittlewood.lean` from the Carleson project, released
under Apache 2.0.
-/

public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter


noncomputable section

namespace CKN.Foundation.Parabolic

/-- Parabolic metric-ball family used by the maximal operator. -/
abbrev hardyLittlewoodParabolicMetricBall (z : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r

/-- Uncentered Hardy–Littlewood maximal function over parabolic balls. -/
@[expose]
def parabolicMaximalFunction (f : ParabolicPoint → ℝ≥0∞) (z : ParabolicPoint) : ℝ≥0∞ :=
  ⨆ c : ParabolicPoint, ⨆ r : ℝ,
    (hardyLittlewoodParabolicMetricBall c r).indicator
      (fun _ ↦ ⨍⁻ y in hardyLittlewoodParabolicMetricBall c r, f y ∂volume) z

theorem parabolicMaximalFunction_average_le {f : ParabolicPoint → ℝ≥0∞}
    {c z : ParabolicPoint} {r : ℝ} (hz : z ∈ hardyLittlewoodParabolicMetricBall c r) :
    ⨍⁻ y in hardyLittlewoodParabolicMetricBall c r, f y ∂volume ≤ parabolicMaximalFunction f z := by
  apply le_iSup₂_of_le c r
  simp only [indicator_of_mem hz]
  exact le_rfl

theorem lowerSemicontinuous_parabolicMaximalFunction (f : ParabolicPoint → ℝ≥0∞) :
    LowerSemicontinuous (parabolicMaximalFunction f) := by
  intro z s hzs
  obtain ⟨c, r, h⟩ := exists_lt_of_lt_ciSup₂' hzs
  have hz : z ∈ hardyLittlewoodParabolicMetricBall c r :=
    mem_of_indicator_ne_zero (h.trans_le' bot_le |>.ne.symm)
  rw [indicator_of_mem hz] at h
  apply eventually_of_mem
  · exact Metric.isOpen_ball.mem_nhds hz
  · intro y hy
    apply LT.lt.trans_le _ (le_iSup₂ c r)
    rwa [indicator_of_mem hy]

theorem measurable_parabolicMaximalFunction (f : ParabolicPoint → ℝ≥0∞) :
    Measurable (parabolicMaximalFunction f) :=
  (lowerSemicontinuous_parabolicMaximalFunction f).measurable

private lemma parabolicMetricBall_measurable (c : ParabolicPoint) (r : ℝ) :
    MeasurableSet (hardyLittlewoodParabolicMetricBall c r) :=
  Metric.isOpen_ball.measurableSet

private lemma parabolicMetricBall_nonempty {c : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    (hardyLittlewoodParabolicMetricBall c r).Nonempty :=
  Metric.nonempty_ball.mpr hr

private lemma parabolicAverage_condition_of_mem
    {f : ParabolicPoint → ℝ≥0∞} {l : ℝ≥0∞}
    {c : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (havg : l < ⨍⁻ y in hardyLittlewoodParabolicMetricBall c r, f y ∂volume) :
    l * volume (hardyLittlewoodParabolicMetricBall c r) ≤
      ∫⁻ y in hardyLittlewoodParabolicMetricBall c r, f y := by
  rw [setLAverage_eq] at havg
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (volume_parabolicBall_pos hr).ne')
    (Or.inl (volume_parabolicBall_lt_top hr).ne)).mp
  exact havg.le

private theorem measure_biUnion_le_lintegral
    (T : Set (ParabolicPoint × ℝ)) (l : ℝ≥0∞) (f : ParabolicPoint → ℝ≥0∞)
    (hpos : ∀ i ∈ T, 0 < i.2)
    (hbounded : ∃ R : ℝ, ∀ i ∈ T, i.2 ≤ R)
    (hcondition : ∀ i ∈ T,
      l * volume (hardyLittlewoodParabolicMetricBall i.1 i.2) ≤
        ∫⁻ y in hardyLittlewoodParabolicMetricBall i.1 i.2, f y) :
    l * volume (⋃ i ∈ T, hardyLittlewoodParabolicMetricBall i.1 i.2) ≤
      ENNReal.ofReal (10 ^ 5) * ∫⁻ y, f y := by
  obtain ⟨R, hR⟩ := hbounded
  obtain ⟨u, huT, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      T (fun i : ParabolicPoint × ℝ ↦ i.1) (fun i ↦ i.2) R hR 5 (by norm_num)
  have hu_countable : u.Countable := hdisj.countable_of_isOpen
      (fun i hi ↦ Metric.isOpen_ball)
      (fun i hi ↦ parabolicMetricBall_nonempty (hpos i (huT hi)))
  have : Countable u := hu_countable.to_subtype
  let enlarged : ParabolicPoint × ℝ → Set ParabolicPoint :=
    fun i ↦ hardyLittlewoodParabolicMetricBall i.1 (5 * i.2)
  have hcover_union :
      (⋃ i ∈ T, hardyLittlewoodParabolicMetricBall i.1 i.2) ⊆ ⋃ i ∈ u, enlarged i := by
    intro z hz
    rcases mem_iUnion₂.mp hz with ⟨i, hiT, hzi⟩
    obtain ⟨j, hju, hsubset⟩ := hcover i hiT
    apply mem_iUnion₂.mpr ⟨j, hju, ?_⟩
    exact hsubset hzi
  have henlarged_measure (i : u) :
      volume (enlarged i) ≤
        ENNReal.ofReal (10 ^ 5) * volume (hardyLittlewoodParabolicMetricBall i.1.1 i.1.2) := by
    exact volume_parabolicBall_five_mul_le (hpos i (huT i.property))
  have hdisj_subtype : Pairwise (Function.onFun Disjoint
      (fun i : u ↦ hardyLittlewoodParabolicMetricBall i.1.1 i.1.2)) := by
    intro i j hij
    exact hdisj i.property j.property (Subtype.coe_ne_coe.mpr hij)
  have hsum_integral :
      (∑' i : u, ∫⁻ y in hardyLittlewoodParabolicMetricBall i.1.1 i.1.2, f y) ≤ ∫⁻ y, f y := by
    calc
      (∑' i : u, ∫⁻ y in hardyLittlewoodParabolicMetricBall i.1.1 i.1.2, f y) =
          ∫⁻ y in ⋃ i : u, hardyLittlewoodParabolicMetricBall i.1.1 i.1.2, f y := by
            symm
            apply lintegral_iUnion
            · exact fun i ↦ parabolicMetricBall_measurable i.1.1 i.1.2
            · exact hdisj_subtype
      _ ≤ ∫⁻ y, f y := by
        gcongr
        exact Measure.restrict_le_self
  calc
    l * volume (⋃ i ∈ T, hardyLittlewoodParabolicMetricBall i.1 i.2) ≤
        l * volume (⋃ i ∈ u, enlarged i) := by
      gcongr
    _ ≤ l * ∑' i : u, volume (enlarged i) := by
      gcongr
      exact measure_biUnion_le volume hu_countable enlarged
    _ ≤ l * ∑' i : u,
        ENNReal.ofReal (10 ^ 5) * volume (hardyLittlewoodParabolicMetricBall i.1.1 i.1.2) := by
      gcongr with i
      exact henlarged_measure i
    _ = ENNReal.ofReal (10 ^ 5) *
        ∑' i : u, l * volume (hardyLittlewoodParabolicMetricBall i.1.1 i.1.2) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ ENNReal.ofReal (10 ^ 5) *
        ∑' i : u, ∫⁻ y in hardyLittlewoodParabolicMetricBall i.1.1 i.1.2, f y := by
      gcongr with i
      exact hcondition i.1 (huT i.2)
    _ ≤ ENNReal.ofReal (10 ^ 5) * ∫⁻ y, f y := by
      gcongr

/-- Parabolic balls of bounded positive radius with average above a chosen level. -/
def parabolicMaximalLevelBalls (f : ParabolicPoint → ℝ≥0∞)
    (l : ℝ≥0∞) (n : ℕ) : Set (ParabolicPoint × ℝ) :=
  {i | 0 < i.2 ∧ i.2 ≤ (n : ℝ) ∧
    l < ⨍⁻ y in hardyLittlewoodParabolicMetricBall i.1 i.2, f y ∂volume}

theorem measure_parabolicMaximalFunction_lt_le
    (f : ParabolicPoint → ℝ≥0∞) {l : ℝ≥0∞} (hl : 0 < l) :
    volume {z | l < parabolicMaximalFunction f z} ≤
      (ENNReal.ofReal (10 ^ 5) / l) * ∫⁻ y, f y := by
  by_cases hltop : l = ∞
  · simp [hltop]
  have hlevel :
      {z | l < parabolicMaximalFunction f z} =
        ⋃ n, ⋃ i ∈ parabolicMaximalLevelBalls f l n,
          hardyLittlewoodParabolicMetricBall i.1 i.2 := by
    ext z
    constructor
    · intro hz
      change l < parabolicMaximalFunction f z at hz
      obtain ⟨c, r, h⟩ := exists_lt_of_lt_ciSup₂' hz
      have hzball : z ∈ hardyLittlewoodParabolicMetricBall c r :=
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
      exact lt_of_lt_of_le hi.2.2 (parabolicMaximalFunction_average_le hzi)
  have hmono : Monotone (fun n : ℕ ↦
      ⋃ i ∈ parabolicMaximalLevelBalls f l n, hardyLittlewoodParabolicMetricBall i.1 i.2) := by
    intro m n hmn z hz
    rcases mem_iUnion₂.mp hz with ⟨i, hi, hzi⟩
    refine mem_iUnion₂.mpr ⟨i, ?_, hzi⟩
    exact ⟨hi.1, hi.2.1.trans (by exact_mod_cast hmn), hi.2.2⟩
  have hlevel_bound (n : ℕ) :
      l * volume (⋃ i ∈ parabolicMaximalLevelBalls f l n,
        hardyLittlewoodParabolicMetricBall i.1 i.2) ≤ ENNReal.ofReal (10 ^ 5) * ∫⁻ y, f y := by
    apply measure_biUnion_le_lintegral
    · intro i hi
      exact (hi.1)
    · exact ⟨(n : ℝ), fun i hi ↦ hi.2.1⟩
    · intro i hi
      exact parabolicAverage_condition_of_mem hi.1 hi.2.2
  have hrewrite :
      (ENNReal.ofReal (10 ^ 5) / l) * ∫⁻ y, f y =
        (ENNReal.ofReal (10 ^ 5) * ∫⁻ y, f y) / l := by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    ac_rfl
  rw [hrewrite]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hl.ne') (Or.inl hltop)).2
  rw [hlevel, hmono.measure_iUnion, ENNReal.iSup_mul]
  exact iSup_le (fun n ↦ by simpa [mul_comm] using hlevel_bound n)

end CKN.Foundation.Parabolic
