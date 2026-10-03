/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.IsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.PeriodicSmooth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Integral formulation of a characterized flow trajectory. -/

@[expose] public section

open Homogenization
open MeasureTheory
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

/-- A trajectory of a smooth-field global flow satisfies its integral equation
on every oriented finite interval. -/
theorem flow_eq_initial_add_intervalIntegral
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (x : Vec 2) (s t : ℝ) :
    X t x s = x + ∫ r in s..t, b r (X r x s) := by
  let γ : ℝ → Vec 2 := fun r => X r x s
  let f' : ℝ → Vec 2 := fun r => b r (X r x s)
  have hγ : Continuous γ := by
    exact continuous_iff_continuousAt.mpr fun r => (hX.2 x s r).continuousAt
  have hf' : Continuous f' := by
    exact hb.smooth.continuous.comp (continuous_id.prodMk hγ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := s) (b := t) (fun r _ => hX.2 x s r) (hf'.intervalIntegrable s t)
  have hsub : (∫ r in s..t, b r (X r x s)) = X t x s - x := by
    simpa [f', γ, hX.1] using hFTC
  calc
    X t x s = x + (X t x s - x) := by abel
    _ = x + ∫ r in s..t, b r (X r x s) := by rw [← hsub]

end AVenhance.Infra.Flow
