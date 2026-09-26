/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.SeparateAnalytic.MeanValue

/-!
# Hartogs' lemma for powers of holomorphic norms

Under a common upper bound, pointwise eventual bounds for positive powers of holomorphic norms
become uniform on a neighborhood of each point. The exponents may vary with the sequence, so the
result applies to roots of Taylor coefficients. The domain is a closed ball in a
finite-dimensional complex normed space carrying an additive Haar volume, such as a finite
complex coordinate space.

The proof combines dominated convergence for the positive excess above the limiting bound with
the ball submean inequality. A ball centered at a nearby point fits inside a fixed ball;
nonnegativity bounds its integral by the fixed integral.

## Main results

`eventually_norm_rpow_lt_on_ball` is Hartogs' lemma: a pointwise eventual bound on positive
powers of holomorphic norms becomes uniform on a neighborhood of each point.
`exists_radius_area_bound` produces a nearby ball of controlled volume.
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- On a compact set, a uniformly bounded-above sequence of continuous functions with pointwise
eventual upper bound `A` has the corresponding integral upper bound. -/
theorem eventually_integral_lt_of_pointwise_eventually_le
    {K : Set E} {u : ℕ → E → ℝ} {A B ε : ℝ} (hK : IsCompact K)
    (hu : ∀ n, ContinuousOn (u n) K) (hB : ∀ n, ∀ z ∈ K, u n z ≤ B)
    (hlim : ∀ z ∈ K, ∀ δ > 0, ∀ᶠ n in atTop, u n z ≤ A + δ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∫ z in K, u n z < volume.real K * A + ε := by
  let v := fun n z => max (u n z - A) 0
  have hv (n : ℕ) : ContinuousOn (v n) K := ((hu n).sub continuousOn_const).sup continuousOn_const
  have ht (z : E) (hz : z ∈ K) : Tendsto (fun n => v n z) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact .of_forall fun n => ha.trans_le (le_max_right _ _)
    · intro b hb
      filter_upwards [hlim z hz (b / 2) (by positivity)] with n hn
      exact max_lt (by linarith) hb
  have hdom := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict K) (fun _ => max (B - A) 0)
    (fun n => ((hv n).integrableOn_compact hK).aestronglyMeasurable)
    (integrableOn_const hK.measure_lt_top.ne)
    (fun n => (ae_restrict_mem hK.measurableSet).mono fun z hz => by
      change |max (u n z - A) 0| ≤ max (B - A) 0
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le_max (sub_le_sub_right (hB n z hz) A) le_rfl)
    ((ae_restrict_mem hK.measurableSet).mono fun z hz => ht z hz)
  simp only [integral_zero] at hdom
  filter_upwards [hdom.eventually (gt_mem_nhds hε)] with n hn
  have hi : (∫ z in K, u n z - A) ≤ ∫ z in K, v n z :=
    setIntegral_mono_on (((hu n).sub continuousOn_const).integrableOn_compact hK)
      ((hv n).integrableOn_compact hK) hK.measurableSet (fun z _ => le_max_left _ _)
  rw [integral_sub ((hu n).integrableOn_compact hK) (integrableOn_const hK.measure_lt_top.ne),
    integral_const] at hi
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at hi
  change (∫ z in K, u n z) - volume.real K * A ≤ ∫ z in K, v n z at hi
  linarith

/-- The Haar volume of a closed ball scales with the real dimension. -/
private theorem real_volume_closedBall (c : E) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (closedBall c R) =
      R ^ Module.finrank ℝ E * volume.real (ball (0 : E) 1) :=
  Measure.addHaar_real_closedBall volume c hR

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- A slightly smaller ball retains enough volume to absorb an arbitrarily small increase in an
average bound. -/
private theorem exists_radius_area_bound {R A ε v : ℝ} (d : ℕ) (hR : 0 < R)
    (hv : 0 < v) (hε : 0 < ε) :
    ∃ r ∈ Ioo 0 R, R ^ d * v * (A + ε / 2) < r ^ d * v * (A + ε) := by
  have hcont : Continuous (fun r : ℝ => r ^ d * v * (A + ε)) := by fun_prop
  have hstrict : R ^ d * v * (A + ε / 2) < R ^ d * v * (A + ε) := by
    have hp : 0 < R ^ d * v := mul_pos (pow_pos hR d) hv
    nlinarith
  have hnhds := (isOpen_lt continuous_const hcont).mem_nhds hstrict
  exact nonempty_of_mem (inter_mem (Ioo_mem_nhdsLT hR) (nhdsWithin_le_nhds hnhds))

/-- **Hartogs' lemma for holomorphic norms.** A pointwise eventual bound on
positive powers of holomorphic norms, under a common upper bound on a closed
ball, becomes uniform on a neighborhood of its center. The powers may vary. -/
theorem eventually_norm_rpow_lt_on_ball
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℕ → E → F} {p : ℕ → ℝ} {c : E} {R A B ε : ℝ}
    (hR : 0 < R) (hp : ∀ n, 0 < p n)
    (hf : ∀ n, AnalyticOnNhd ℂ (f n) (closedBall c R))
    (hB : ∀ n, ∀ z ∈ closedBall c R, ‖f n z‖ ^ p n ≤ B)
    (hlim : ∀ z ∈ closedBall c R, ∀ δ > 0,
      ∀ᶠ n in atTop, ‖f n z‖ ^ p n ≤ A + δ) (hε : 0 < ε) :
    ∃ r > 0, ∀ᶠ n in atTop, ∀ z ∈ ball c r, ‖f n z‖ ^ p n < A + ε := by
  have hunit : 0 < volume.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : E) one_pos).ne' measure_ball_lt_top.ne
  obtain ⟨s, ⟨hs, hsR⟩, harea⟩ :=
    exists_radius_area_bound (A := A) (Module.finrank ℝ E) hR hunit hε
  have hvol : 0 < volume.real (closedBall c R) := by
    rw [real_volume_closedBall c hR.le]
    positivity
  have hint := eventually_integral_lt_of_pointwise_eventually_le (isCompact_closedBall c R)
    (fun n => (hf n).continuousOn.norm.rpow_const (fun _ _ => Or.inr (hp n).le)) hB hlim
    (mul_pos hvol (half_pos hε))
  refine ⟨R - s, sub_pos.mpr hsR, ?_⟩
  filter_upwards [hint] with n hn z hz
  have hsub : closedBall z s ⊆ closedBall c R :=
    closedBall_subset_closedBall' (by have := mem_ball.mp hz; linarith)
  have hmean := volume_mul_norm_rpow_le_integral_closedBall (E := E) (hp n) ((hf n).mono hsub)
  have hmono : (∫ w in closedBall z s, ‖f n w‖ ^ p n) ≤
      ∫ w in closedBall c R, ‖f n w‖ ^ p n :=
    setIntegral_mono_set
      (((hf n).continuousOn.norm.rpow_const (fun _ _ => Or.inr (hp n).le)).integrableOn_compact
        (isCompact_closedBall c R))
      (.of_forall fun w => Real.rpow_nonneg (norm_nonneg _) _) hsub.eventuallySubset
  rw [real_volume_closedBall z hs.le] at hmean
  rw [real_volume_closedBall c hR.le] at hn
  have hbound : s ^ Module.finrank ℝ E * volume.real (ball (0 : E) 1) * (‖f n z‖ ^ p n) <
      s ^ Module.finrank ℝ E * volume.real (ball (0 : E) 1) * (A + ε) :=
    (hmean.trans hmono).trans_lt (hn.trans_le (by nlinarith only [harea]))
  exact (mul_lt_mul_iff_right₀
    (mul_pos (pow_pos hs _) hunit)).mp hbound

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
