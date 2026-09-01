/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Geometry.FiniteProjection

/-!
# Uniform locality of prepared roots

The roots of a positive-degree prepared polynomial converge uniformly to the
distinguished point as the base tends to the origin.  This is the locality
bridge which allows ambient germ identities to be applied simultaneously to
every root of a nearby specialized fiber.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- Every root of a nearby prepared fiber lies in any prescribed neighborhood
of the ambient origin. -/
theorem eventually_appendLast_mem_of_preparedValue_eq_zero
    {n d : ℕ} (hd : 0 < d)
    (a : Fin d → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    {V : Set (ComplexEuclidean (n + 1))}
    (hV : V ∈ 𝓝 (0 : ComplexEuclidean (n + 1))) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n), ∀ w : ℂ,
      preparedValue a z w = 0 → appendLastCLE n (z, w) ∈ V := by
  have happendTendsto : Tendsto (appendLastCLE n)
      (𝓝 (0 : ComplexEuclidean n × ℂ))
      (𝓝 (0 : ComplexEuclidean (n + 1))) := by
    have h : Tendsto (appendLastCLE n)
      (𝓝 (0 : ComplexEuclidean n × ℂ))
      (𝓝 (appendLastCLE n (0 : ComplexEuclidean n × ℂ))) :=
      (appendLastCLE n).continuous.continuousAt
    simpa only [map_zero] using h
  have hpre : (appendLastCLE n) ⁻¹' V ∈
      𝓝 (0 : ComplexEuclidean n × ℂ) :=
    happendTendsto hV
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let r : ℝ := ε / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrε : r < ε := by
    dsimp [r]
    linarith
  have hcoeff :
      ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n), ∀ i,
        ‖a i z‖ < r ^ (d - (i : ℕ)) / (2 * (d : ℝ)) := by
    apply Filter.eventually_all.mpr
    intro i
    have hbound : ‖a i (0 : ComplexEuclidean n)‖ <
        r ^ (d - (i : ℕ)) / (2 * (d : ℝ)) := by
      rw [ha0 i, norm_zero]
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    exact (ha i).continuousAt.norm.eventually_lt continuousAt_const hbound
  have hbase : Metric.ball (0 : ComplexEuclidean n) r ∈ 𝓝 0 :=
    Metric.ball_mem_nhds _ hr
  filter_upwards [hcoeff, hbase] with z hzcoeff hzbase
  intro w hw
  have hwbound : ‖w‖ < r :=
    norm_lt_of_monic_sum_eq_zero_of_coeff_bound hd hr
      (fun i ↦ a i z) w hzcoeff hw
  apply hεsub
  have hzbound : ‖z‖ < r := by
    simpa [Metric.mem_ball, dist_zero_right] using hzbase
  have hpair : dist (z, w) (0 : ComplexEuclidean n × ℂ) < ε := by
    simpa [Prod.dist_eq, dist_zero_right, Prod.norm_def] using
      (max_lt (hzbound.trans hrε) (hwbound.trans hrε))
  exact Metric.mem_ball.mpr hpair

/-- Predicate form of `eventually_appendLast_mem_of_preparedValue_eq_zero`:
an ambient property which holds near the origin holds simultaneously at all
roots of every sufficiently nearby prepared fiber. -/
theorem eventually_on_all_prepared_roots
    {n d : ℕ} (hd : 0 < d)
    (a : Fin d → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    {R : ComplexEuclidean (n + 1) → Prop}
    (hR : ∀ᶠ x in 𝓝 (0 : ComplexEuclidean (n + 1)), R x) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n), ∀ w : ℂ,
      preparedValue a z w = 0 → R (appendLastCLE n (z, w)) := by
  exact eventually_appendLast_mem_of_preparedValue_eq_zero
    hd a ha ha0 hR

end

end LocalComplexGeometry
