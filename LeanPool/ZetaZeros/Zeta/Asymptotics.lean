/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Defs

/-!
# Elementary asymptotic consequences of Riemann--von Mangoldt

This file turns the epsilon-form external input into the filter form used by the final proportion
argument and records the eventual positivity needed to divide by the zero count.
-/

@[expose] public section

namespace ZetaZeros

open Filter Topology

/-- The main scale in the Riemann--von Mangoldt and pair-correlation formulae. -/
noncomputable def zeroScale (T : ℝ) : ℝ := T / (2 * Real.pi) * Real.log T

/-- The Riemann--von Mangoldt scale is positive at all sufficiently large heights. -/
theorem zeroScale_pos_eventually : ∀ᶠ T in atTop, 0 < zeroScale T := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  exact mul_pos (div_pos hT0 (mul_pos (by norm_num) Real.pi_pos)) hlog

/-- Epsilon-form Riemann--von Mangoldt is convergence of the normalized count to one. -/
theorem RiemannVonMangoldt.tendsto (hRvM : RiemannVonMangoldt) :
    Tendsto (fun T : ℝ => (zeroCount T : ℝ) / zeroScale T) atTop (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hRvM ε hε
  filter_upwards [eventually_ge_atTop T₀] with T hT
  simpa only [zeroScale, Real.dist_eq] using hT₀ T hT

/-- Riemann--von Mangoldt in particular makes the zero count positive eventually. -/
theorem RiemannVonMangoldt.zeroCount_pos_eventually (hRvM : RiemannVonMangoldt) :
    ∀ᶠ T in atTop, 0 < (zeroCount T : ℝ) := by
  obtain ⟨T₀, hT₀⟩ := hRvM (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop T₀, zeroScale_pos_eventually] with T hT hscale
  have hratio : 0 < (zeroCount T : ℝ) / zeroScale T := by
    have habs := hT₀ T hT
    rw [abs_lt] at habs
    dsimp [zeroScale] at habs ⊢
    linarith
  rcases (div_pos_iff.mp hratio) with h | h
  · exact h.1
  · exact (not_lt_of_ge (le_of_lt hscale) h.2).elim

end ZetaZeros
