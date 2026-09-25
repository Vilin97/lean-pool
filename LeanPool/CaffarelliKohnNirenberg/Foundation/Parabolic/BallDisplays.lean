/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The parabolic ball and its volume

This file records the literal displays of `paper/ckn.tex` that describe the
open parabolic ball `𝔅_r(z)` of the metric `dpar` (equation
`eq:parabolic-ball` and Lemma `lem:parabolic-metric`):

* `𝔅_r(z) = B_r(x) × (t - r², t + r²)` for `z = (x, t)`;
* `C_r(z) ⊆ 𝔅_r(z)` and `𝔅_r(z) ⊆ C_{2r}(x, t + r²)`, where `C_r(z)` is the
  parabolic cylinder `B_r(x) × (t - r², t]`;
* `|𝔅_r(z)| = (8π/3) r⁵`.

The spatial ball `vec3Ball x r` uses the Euclidean norm on `Fin 3 → ℝ`
(`vec3EuclideanNorm`), so its volume is computed by transporting Mathlib's
volume of the Euclidean ball in `EuclideanSpace ℝ (Fin 3)` along the
measure-preserving equivalence `WithLp.toLp 2`.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric


noncomputable section

namespace CKN.Foundation.Parabolic

/-- Equation `eq:parabolic-ball`: the open `parabolicDist`-ball of radius `r`
about `z = (x, t)` is the product of the Euclidean ball `vec3Ball x r` with the
open time interval `(t - r², t + r²)`. -/
theorem metricBall_eq_parabolicBall (z : ParabolicPoint) (r : ℝ) :
    Metric.ball z r = vec3Ball z.1 r ×ˢ Ioo (z.2 - r ^ 2) (z.2 + r ^ 2) := by
  ext p
  change dist p z < r ↔
    vec3EuclideanNorm (p.1 - z.1) < r ∧ (z.2 - r ^ 2 < p.2 ∧ p.2 < z.2 + r ^ 2)
  rw [dist_eq_parabolicDist]
  change max (vec3EuclideanNorm (p.1 - z.1)) (Real.sqrt |p.2 - z.2|) < r ↔
    vec3EuclideanNorm (p.1 - z.1) < r ∧ (z.2 - r ^ 2 < p.2 ∧ p.2 < z.2 + r ^ 2)
  rcases le_or_gt r 0 with hr | hr
  · constructor
    · intro h
      exact absurd h (not_lt.mpr <| calc
        r ≤ 0 := hr
        _ ≤ vec3EuclideanNorm (p.1 - z.1) := vec3EuclideanNorm_nonneg _
        _ ≤ max (vec3EuclideanNorm (p.1 - z.1)) (Real.sqrt |p.2 - z.2|) := le_max_left _ _)
    · rintro ⟨hspace, -⟩
      exact absurd hspace (not_lt.mpr (le_trans hr (vec3EuclideanNorm_nonneg _)))
  · rw [max_lt_iff, Real.sqrt_lt' hr, abs_lt]
    constructor
    · rintro ⟨hspace, hlo, hhi⟩
      exact ⟨hspace, by linarith only [hlo], by linarith only [hhi]⟩
    · rintro ⟨hspace, hlo, hhi⟩
      exact ⟨hspace, by linarith only [hlo], by linarith only [hhi]⟩

/-- Lemma `lem:parabolic-metric`: the parabolic cylinder `C_r(z)` is contained
in the open ball `𝔅_r(z)` of the same center and radius.  Every point of the
cylinder with time coordinate exactly `t` lies in the open time interval
`(t - r², t + r²)` because `r > 0`. -/
theorem parabolicCylinder_subset_metricBall_sameCenter (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) : parabolicCylinder z.1 z.2 r ⊆ Metric.ball z r := by
  intro p hp
  rw [metricBall_eq_parabolicBall]
  change vec3EuclideanNorm (p.1 - z.1) < r ∧ (z.2 - r ^ 2 < p.2 ∧ p.2 ≤ z.2) at hp
  change p.1 ∈ vec3Ball z.1 r ∧ p.2 ∈ Ioo (z.2 - r ^ 2) (z.2 + r ^ 2)
  exact ⟨hp.1, hp.2.1,
    lt_of_le_of_lt hp.2.2 (lt_add_of_pos_right _ (sq_pos_of_pos hr))⟩

/-- Lemma `lem:parabolic-metric`: the open parabolic ball `𝔅_r(z)` is contained
in the cylinder of radius `2r` based at `(x, t + r²)`, i.e.
`𝔅_r(z) ⊆ C_{2r}(x, t + r²)`. -/
theorem metricBall_subset_parabolicCylinder_doubled (z : ParabolicPoint) {r : ℝ}
    (hr : 0 < r) :
    Metric.ball z r ⊆ parabolicCylinder z.1 (z.2 + r ^ 2) (2 * r) := by
  intro p hp
  rw [metricBall_eq_parabolicBall] at hp
  change vec3EuclideanNorm (p.1 - z.1) < r ∧ (z.2 - r ^ 2 < p.2 ∧ p.2 < z.2 + r ^ 2)
    at hp
  change vec3EuclideanNorm (p.1 - z.1) < 2 * r ∧
    ((z.2 + r ^ 2) - (2 * r) ^ 2 < p.2 ∧ p.2 ≤ z.2 + r ^ 2)
  exact ⟨lt_of_lt_of_le hp.1 (by linarith only [hr]),
    by linarith only [hp.2.1, sq_pos_of_pos hr], le_of_lt hp.2.2⟩

/-- The volume of the open Euclidean ball of radius `r` centred at the origin
of `Vec3 = Fin 3 → ℝ`, namely `(4π/3) r³`.  The Euclidean norm on `Fin 3 → ℝ`
is the `L²` norm, so this is Mathlib's `EuclideanSpace.volume_ball_fin_three`,
transported along the measure-preserving equivalence `WithLp.toLp 2`. -/
lemma volume_vec3Ball_zero (r : ℝ) :
    volume (vec3Ball (0 : Vec3) r) =
      ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [show vec3Ball (0 : Vec3) r =
      (fun y : Vec3 => WithLp.toLp 2 y) ⁻¹'
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r) from by
    ext y
    simp only [mem_vec3Ball, mem_preimage, mem_ball, dist_zero_right, sub_zero,
      vec3EuclideanNorm_eq_l2]]
  rw [(PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    measurableSet_ball.nullMeasurableSet]
  exact EuclideanSpace.volume_ball_fin_three (0 : EuclideanSpace ℝ (Fin 3)) r

/-- The volume of the open Euclidean ball of radius `r` centred at any point of
`Vec3`, namely `(4π/3) r³`; this is `volume_vec3Ball_zero` together with
translation invariance of Lebesgue measure. -/
lemma volume_vec3Ball_eq (x : Vec3) (r : ℝ) :
    volume (vec3Ball x r) =
      ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [volume_vec3Ball, volume_vec3Ball_zero]

/-- The volume of the parabolic ball: `|𝔅_r(z)| = (8π/3) r⁵`, the product of
the spatial ball volume `(4π/3) r³` and the time interval length `2r²`. -/
theorem volume_metricBall (z : ParabolicPoint) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball z r) = ENNReal.ofReal (8 * Real.pi / 3 * r ^ 5) := by
  rw [metricBall_eq_parabolicBall]
  change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
      (vec3Ball z.1 r ×ˢ Ioo (z.2 - r ^ 2) (z.2 + r ^ 2)) =
    ENNReal.ofReal (8 * Real.pi / 3 * r ^ 5)
  rw [Measure.prod_prod, volume_vec3Ball_eq, Real.volume_Ioo,
    show (z.2 + r ^ 2) - (z.2 - r ^ 2) = 2 * r ^ 2 by ring]
  rw [← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end CKN.Foundation.Parabolic
