/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import Mathlib.MeasureTheory.Measure.Doubling
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Doubling geometry for parabolic volume

The parabolic metric has homogeneous dimension five.  The lemmas below record
the corresponding scaling of the spatial balls and parabolic cylinders, then
use the cylinder/metric-ball comparison from `Basic` to provide the doubling
instance required by metric covering arguments.
-/

public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric


noncomputable section

namespace CKN.Foundation.Parabolic

/-- Linear spatial dilation used in the parabolic doubling calculation. -/
def doublingVec3ScaleLinear (a : ℝ) : Vec3 →ₗ[ℝ] Vec3 :=
  a • LinearMap.id

private lemma vec3ScaleLinear_apply (a : ℝ) (v : Vec3) :
    doublingVec3ScaleLinear a v = a • v := by
  rfl

private lemma vec3ScaleLinear_det (a : ℝ) :
    LinearMap.det (doublingVec3ScaleLinear a) = a ^ 3 := by
  simp [doublingVec3ScaleLinear, LinearMap.det_smul, LinearMap.det_id]

lemma volume_vec3Ball_scale {a r : ℝ} (ha : 0 < a) :
    volume (vec3Ball 0 (a * r)) = ENNReal.ofReal (a ^ 3) * volume (vec3Ball 0 r) := by
  let f := doublingVec3ScaleLinear a⁻¹
  have hdet : LinearMap.det f ≠ 0 := by
    rw [show f = doublingVec3ScaleLinear a⁻¹ by rfl, vec3ScaleLinear_det]
    exact pow_ne_zero 3 (inv_ne_zero ha.ne')
  have hpre : (f : Vec3 → Vec3) ⁻¹' vec3Ball 0 r = vec3Ball 0 (a * r) := by
    ext y
    change vec3EuclideanNorm (f y - 0) < r ↔ vec3EuclideanNorm (y - 0) < a * r
    rw [sub_zero, sub_zero, vec3ScaleLinear_apply, vec3EuclideanNorm_smul,
      abs_of_pos (inv_pos.mpr ha)]
    constructor
    · intro h
      calc
        vec3EuclideanNorm y = a * (a⁻¹ * vec3EuclideanNorm y) := by
          field_simp [ha.ne']
        _ < a * r := mul_lt_mul_of_pos_left h ha
    · intro h
      have h' := mul_lt_mul_of_pos_left h (inv_pos.mpr ha)
      calc
        a⁻¹ * vec3EuclideanNorm y < a⁻¹ * (a * r) := h'
        _ = r := by field_simp [ha.ne']
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi (f := f) hdet
  have hmeasure := congrArg (fun μ : Measure Vec3 => μ (vec3Ball 0 r)) hmap
  rw [Measure.map_apply (f.continuous_of_finiteDimensional.measurable)
    (vec3Ball_measurable 0 r), hpre, Measure.smul_apply] at hmeasure
  rw [vec3ScaleLinear_det] at hmeasure
  have ha3 : 0 < a ^ 3 := pow_pos ha 3
  simpa [f, abs_of_pos (inv_pos.mpr ha), abs_of_pos ha, inv_pow, ha.ne',
    ENNReal.ofReal_inv_of_pos ha3, ENNReal.ofReal_pow ha.le] using hmeasure

lemma volume_parabolicCylinder_radius_scale {x : Vec3} {t r a : ℝ} (ha : 0 < a) :
    volume (parabolicCylinder x t (a * r)) =
      ENNReal.ofReal (a ^ 5) * volume (parabolicCylinder x t r) := by
  rw [volume_parabolicCylinder, volume_parabolicCylinder,
    volume_vec3Ball x (a * r), volume_vec3Ball x r, volume_vec3Ball_scale ha, mul_pow,
    ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ 2)]
  calc
    _ = (ENNReal.ofReal (a ^ 3) * ENNReal.ofReal (a ^ 2)) *
        (volume (vec3Ball 0 r) * ENNReal.ofReal (r ^ 2)) := by ring
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ 3), ← pow_add]

lemma volume_parabolicCylinder_time (x : Vec3) (t₁ t₂ r : ℝ) :
    volume (parabolicCylinder x t₁ r) = volume (parabolicCylinder x t₂ r) := by
  rw [volume_parabolicCylinder, volume_parabolicCylinder]

lemma closedBall_subset_parabolicCylinder {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace (x, t) r ⊆
      parabolicCylinder x (t + 8 * r ^ 2) (4 * r) := by
  have hclosed : @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace (x, t) r ⊆
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace (x, t) (2 * r) :=
    Metric.closedBall_subset_ball (by linarith only [hr])
  have hball := metricBall_subset_parabolicCylinder (x := x) (t := t + 8 * r ^ 2)
      (r := 4 * r) (by positivity)
  have hcenter : (x, t + 8 * r ^ 2 - (4 * r) ^ 2 / 2) = (x, t) := by
    congr 1
    ring
  have hradius : (4 * r) / 2 = 2 * r := by ring
  rw [hcenter, hradius] at hball
  exact hclosed.trans hball

lemma parabolicCylinder_subset_closedBall {x : Vec3} {t r : ℝ} (hr : 0 < r) :
    parabolicCylinder x (t + r ^ 2 / 2) r ⊆
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace (x, t) r := by
  have hcyl := parabolicCylinder_subset_metricBall (x := x) (t := t + r ^ 2 / 2) hr
  have hcenter : (x, t + r ^ 2 / 2 - r ^ 2 / 2) = (x, t) := by
    congr 1
    ring
  rw [hcenter] at hcyl
  exact hcyl.trans Metric.ball_subset_closedBall

lemma volume_parabolicBall_five_mul_le {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    (volume : Measure ParabolicPoint)
        (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z (5 * r)) ≤
      ENNReal.ofReal (10 ^ 5) *
        volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r) := by
  have hupper :
      (volume : Measure ParabolicPoint)
          (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z (5 * r)) ≤
        volume (parabolicCylinder z.1 (z.2 + (10 * r) ^ 2 / 2) (10 * r)) := by
    have hball := metricBall_subset_parabolicCylinder (x := z.1)
      (t := z.2 + (10 * r) ^ 2 / 2) (r := 10 * r) (by positivity)
    have hcenter :
        (z.1, z.2 + (10 * r) ^ 2 / 2 - (10 * r) ^ 2 / 2) = z := by
      congr 1
      ring
    have hradius : (10 * r) / 2 = 5 * r := by ring
    rw [hcenter, hradius] at hball
    exact measure_mono hball
  have hlower :
      volume (parabolicCylinder z.1 (z.2 + r ^ 2 / 2) r) ≤
        (volume : Measure ParabolicPoint)
          (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r) := by
    have hcyl := parabolicCylinder_subset_metricBall (x := z.1)
      (t := z.2 + r ^ 2 / 2) hr
    have hcenter : (z.1, z.2 + r ^ 2 / 2 - r ^ 2 / 2) = z := by
      congr 1
      ring
    rw [hcenter] at hcyl
    exact measure_mono hcyl
  have hscale := volume_parabolicCylinder_radius_scale
    (x := z.1) (t := z.2 + (10 * r) ^ 2 / 2) (r := r) (a := 10) (by norm_num)
  have htime := volume_parabolicCylinder_time z.1
    (z.2 + (10 * r) ^ 2 / 2) (z.2 + r ^ 2 / 2) r
  calc
    (volume : Measure ParabolicPoint)
          (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z (5 * r)) ≤
        volume (parabolicCylinder z.1 (z.2 + (10 * r) ^ 2 / 2) (10 * r)) := hupper
    _ = ENNReal.ofReal (10 ^ 5) *
        volume (parabolicCylinder z.1 (z.2 + (10 * r) ^ 2 / 2) r) := hscale
    _ = ENNReal.ofReal (10 ^ 5) *
        volume (parabolicCylinder z.1 (z.2 + r ^ 2 / 2) r) := by rw [htime]
    _ ≤ ENNReal.ofReal (10 ^ 5) *
        volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r) := by
      gcongr
    _ = ENNReal.ofReal (10 ^ 5) *
        volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r) := rfl

lemma volume_parabolicBall_two_mul_le {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    (volume : Measure ParabolicPoint)
        (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z (2 * r)) ≤
      ENNReal.ofReal (10 ^ 5) *
        volume (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r) := by
  have hsubset :
      @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z (2 * r) ⊆
        @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z (5 * r) := by
    exact Metric.ball_subset_ball (by linarith only [hr])
  exact (measure_mono hsubset).trans (volume_parabolicBall_five_mul_le hr)

lemma volume_parabolicBall_pos {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    0 < (volume : Measure ParabolicPoint)
      (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r) := by
  have hcyl := parabolicCylinder_subset_metricBall (x := z.1)
    (t := z.2 + r ^ 2 / 2) hr
  have hcenter : (z.1, z.2 + r ^ 2 / 2 - r ^ 2 / 2) = z := by
    congr 1
    ring
  rw [hcenter] at hcyl
  exact (Integration.volume_parabolicCylinder_pos hr).trans_le (measure_mono hcyl)

lemma volume_parabolicBall_lt_top {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    (volume : Measure ParabolicPoint)
        (@Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r) < ∞ := by
  have hball := metricBall_subset_parabolicCylinder (x := z.1)
    (t := z.2 + (2 * r) ^ 2 / 2) (r := 2 * r) (by positivity)
  have hcenter :
      (z.1, z.2 + (2 * r) ^ 2 / 2 - (2 * r) ^ 2 / 2) = z := by
    congr 1
    ring
  have hradius : (2 * r) / 2 = r := by ring
  rw [hcenter, hradius] at hball
  apply (measure_mono hball).trans_lt
  exact Integration.volume_parabolicCylinder_lt_top

instance parabolicVolumeIsUnifLocDoublingMeasure :
    IsUnifLocDoublingMeasure (volume : Measure ParabolicPoint) where
  exists_measure_closedBall_le_mul'' := by
    refine ⟨(8 ^ 5 : ℝ≥0), ?_⟩
    filter_upwards [eventually_mem_nhdsWithin] with r hr
    have hr' : 0 < r := by exact mem_Ioi.mp hr
    intro z
    have hset : parabolicCylinder z.1 (z.2 + 8 * (2 * r) ^ 2) (4 * (2 * r)) ⊆
        parabolicCylinder z.1 (z.2 + 8 * (2 * r) ^ 2) (8 * r) := by
      rw [show 4 * (2 * r) = 8 * r by ring]
    have hupper :
        (volume : Measure ParabolicPoint)
            (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r)) ≤
          volume (parabolicCylinder z.1 (z.2 + 8 * (2 * r) ^ 2) (8 * r)) :=
      measure_mono ((closedBall_subset_parabolicCylinder
        (x := z.1) (t := z.2) (r := 2 * r) (by positivity)).trans hset)
    have hlower :
        volume (parabolicCylinder z.1 (z.2 + r ^ 2 / 2) r) ≤
          (volume : Measure ParabolicPoint)
            (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :=
      measure_mono (parabolicCylinder_subset_closedBall
        (x := z.1) (t := z.2) (r := r) hr')
    have hscale := volume_parabolicCylinder_radius_scale
      (x := z.1) (t := z.2 + 8 * (2 * r) ^ 2) (r := r) (a := 8) (by norm_num)
    have htime := volume_parabolicCylinder_time z.1
      (z.2 + 8 * (2 * r) ^ 2) (z.2 + r ^ 2 / 2) r
    calc
      (volume : Measure ParabolicPoint)
          (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (2 * r)) ≤
          volume (parabolicCylinder z.1 (z.2 + 8 * (2 * r) ^ 2) (8 * r)) := hupper
      _ = ENNReal.ofReal (8 ^ 5) *
          volume (parabolicCylinder z.1 (z.2 + 8 * (2 * r) ^ 2) r) := hscale
      _ = ENNReal.ofReal (8 ^ 5) *
          volume (parabolicCylinder z.1 (z.2 + r ^ 2 / 2) r) := by rw [htime]
      _ ≤ ENNReal.ofReal (8 ^ 5) *
          volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) :=
        by gcongr
      _ = (↑(8 ^ 5 : ℝ≥0) : ℝ≥0∞) *
          volume (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) := by norm_num

end CKN.Foundation.Parabolic
