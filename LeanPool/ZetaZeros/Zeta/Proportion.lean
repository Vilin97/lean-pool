/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Zeta.Asymptotics

/-!
# The final asymptotic passage

Once the zero count and kernel energy have their required normalized limits, the two finite-height
inequalities turn into the claimed eventual proportion bounds.
-/

@[expose] public section

namespace ZetaZeros

open Filter Topology

/-- Dividing two quantities normalized by the same eventually non-zero scale preserves their
quotient limit. -/
theorem tendsto_ratio_of_tendsto_div_scale
    (N S scale : ℝ → ℝ) (C : ℝ)
    (hN : Tendsto (fun T => N T / scale T) atTop (nhds 1))
    (hS : Tendsto (fun T => S T / scale T) atTop (nhds C))
    (hscale : ∀ᶠ T in atTop, scale T ≠ 0) :
    Tendsto (fun T => S T / N T) atTop (nhds C) := by
  have hdiv := hS.div hN (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun T => S T / N T) =ᶠ[atTop]
      (fun T => (S T / scale T) / (N T / scale T)) := by
    filter_upwards [hscale] with T hs
    field_simp
  simpa only [div_one] using hdiv.congr' heq.symm

/-- The simple-real lower bound gives the eventual simple-zero proportion once the kernel energy
per zero tends to `C`. -/
theorem eventually_simple_proportion
    (N A S : ℝ → ℝ) (C ε : ℝ) (hε : 0 < ε)
    (hNpos : ∀ᶠ T in atTop, 0 < N T)
    (hS : Tendsto (fun T => S T / N T) atTop (nhds C))
    (hbound : ∀ᶠ T in atTop, 2 * N T - S T ≤ A T) :
    ∀ᶠ T in atTop, 2 - C - ε < A T / N T := by
  have hlt : ∀ᶠ T in atTop, S T / N T < C + ε :=
    (tendsto_order.1 hS).2 _ (by linarith)
  filter_upwards [hNpos, hlt, hbound] with T hNT hST hAT
  rw [lt_div_iff₀ hNT]
  have hSN : S T < (C + ε) * N T := (div_lt_iff₀ hNT).mp hST
  nlinarith

/-- The distinct-element lower bound gives the eventual distinct-zero proportion once the kernel
energy per zero tends to `C`. -/
theorem eventually_distinct_proportion
    (N A S : ℝ → ℝ) (C ε : ℝ) (hε : 0 < ε)
    (hNpos : ∀ᶠ T in atTop, 0 < N T)
    (hS : Tendsto (fun T => S T / N T) atTop (nhds C))
    (hbound : ∀ᶠ T in atTop, 3 / 2 * N T - S T / 2 ≤ A T) :
    ∀ᶠ T in atTop, 3 / 2 - C / 2 - ε < A T / N T := by
  have hlt : ∀ᶠ T in atTop, S T / N T < C + 2 * ε :=
    (tendsto_order.1 hS).2 _ (by linarith)
  filter_upwards [hNpos, hlt, hbound] with T hNT hST hAT
  rw [lt_div_iff₀ hNT]
  have hSN : S T < (C + 2 * ε) * N T := (div_lt_iff₀ hNT).mp hST
  nlinarith

end ZetaZeros
