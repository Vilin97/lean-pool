/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MildWordEquation

@[expose] public section

/-! Exact restart identities for the genuine cylinder heat and Bochner Duhamel integrals. -/

noncomputable section

namespace EulerHeatRestart

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerSobolevHeatGenerator
  EulerDuhamelDifferentiation EulerVolterraConvolution
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Actual viscous heat obeys the semigroup law at nonnegative physical times. -/
theorem heatFlow_semigroup {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (u : SobolevSpace period q) :
    heatFlow period q ν s (heatFlow period q ν t u) = heatFlow period q ν (s+t) u := by
  unfold heatFlow
  rw [heatOperator_semigroup]
  apply congrArg (fun v : ℝ≥0 => heatOperator period q v u)
  rw [mul_add, Real.toNNReal_add (by positivity : 0 ≤ 2*ν*s) (by positivity : 0 ≤ 2*ν*t)]


/-- Heat propagates the earlier Duhamel history exactly to a later time. -/
theorem heatFlow_duhamel_history {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    heatFlow period q ν (t-a) (duhamel period ν T hT f a) =
      ∫ s in (0 : ℝ)..a, heatFlow period q ν (t-s) (extendPath T hT f s) := by
  unfold duhamel
  rw [← (heatFlow period q ν (t-a)).intervalIntegral_comp_comm
    ((shiftedHeat_continuous period ν T hT f a).intervalIntegrable 0 a)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with s hs
  rw [uIoc_of_le ha] at hs
  have hh := heatFlow_semigroup period ν hν (t-a) (a-s) (sub_nonneg.mpr hat) (sub_nonneg.mpr hs.2)
    (extendPath T hT f s)
  simpa only [sub_add_sub_cancel] using hh

/-- The actual Bochner Duhamel integral splits into propagated history and forcing after the restart time. -/
theorem duhamel_restart {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    duhamel period ν T hT f t = heatFlow period q ν (t-a) (duhamel period ν T hT f a) +
      ∫ s in a..t, heatFlow period q ν (t-s) (extendPath T hT f s) := by
  rw [heatFlow_duhamel_history period ν hν T hT f a t ha hat]
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((shiftedHeat_continuous period ν T hT f t).intervalIntegrable (μ := volume) 0 a)
    ((shiftedHeat_continuous period ν T hT f t).intervalIntegrable (μ := volume) a t)).symm

/-- The full genuine inhomogeneous heat solution restarts from its attained state. -/
theorem inhomogeneous_heat_restart {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (u₀ : SobolevSpace period q)
    (a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    heatFlow period q ν t u₀ + duhamel period ν T hT f t =
      heatFlow period q ν (t-a) (heatFlow period q ν a u₀ + duhamel period ν T hT f a) +
        ∫ s in a..t, heatFlow period q ν (t-s) (extendPath T hT f s) := by
  rw [map_add, heatFlow_semigroup period ν hν (t-a) a (sub_nonneg.mpr hat) ha,
    sub_add_cancel, duhamel_restart period ν hν T hT f a t ha hat, add_assoc]

/-- The old-history and new-source identity written in elapsed time after the restart. -/
theorem duhamel_restart_shifted {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    duhamel period ν T hT f (a+t) = heatFlow period q ν t (duhamel period ν T hT f a) +
      ∫ r in (0 : ℝ)..t, heatFlow period q ν (t-r) (extendPath T hT f (a+r)) := by
  have hh := duhamel_restart period ν hν T hT f a (a+t) ha (by linarith)
  rw [add_sub_cancel_left] at hh
  rw [hh]
  congr 1
  have hi := intervalIntegral.integral_comp_add_left
    (fun s => heatFlow period q ν (a+t-s) (extendPath T hT f s)) a (a := 0) (b := t)
  simp only [add_zero] at hi
  have he : (fun r => heatFlow period q ν (a+t-(a+r)) (extendPath T hT f (a+r))) =
      fun r => heatFlow period q ν (t-r) (extendPath T hT f (a+r)) := by
    funext r
    congr 2
    ring
  rw [he] at hi
  exact hi.symm

end EulerHeatRestart
