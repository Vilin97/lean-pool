/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.Decay

/-!
# Pressure Gradient Decay

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section

namespace CKN.Core.Step4

/-! The rate-three exponent bookkeeping for the pressure-gradient decay. -/

def pressureGradientSourceExponent (κ : ℝ) : ℝ := 5 - 6 / κ

theorem pressureGradientSourceExponent_eq
    {κ : ℝ} :
    pressureGradientSourceExponent κ = 5 - 6 / κ := by
  rfl

theorem pressureGradientSourceExponent_nonneg
    {κ : ℝ} (hκ : 6 / 5 ≤ κ) :
    0 ≤ pressureGradientSourceExponent κ := by
  unfold pressureGradientSourceExponent
  have hκ0 : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  have hineq : 6 ≤ 5 * κ := by
    linarith only [hκ]
  have hdiv : 6 / κ ≤ 5 := (div_le_iff₀ hκ0).2 hineq
  linarith only [hdiv]

theorem pressureGradientSourceExponent_lt_three
    {κ : ℝ} (hκ : 0 < κ) (hκ3 : κ < 3) :
    pressureGradientSourceExponent κ < 3 := by
  unfold pressureGradientSourceExponent
  have hdiv : 2 < 6 / κ := by
    rw [lt_div_iff₀ hκ]
    linarith only [hκ3]
  linarith only [hdiv]

theorem pressureGradientSourceExponent_routeA :
    pressureGradientSourceExponent (25 / 11 : ℝ) = 59 / 25 := by
  unfold pressureGradientSourceExponent
  norm_num

theorem pressureGradientSourceExponent_endgame :
    pressureGradientSourceExponent (25 / 9 : ℝ) = 71 / 25 := by
  unfold pressureGradientSourceExponent
  norm_num

theorem pressureGradientRateThree_admissible :
    0 ≤ pressureGradientSourceExponent (25 / 11 : ℝ) ∧
      pressureGradientSourceExponent (25 / 11 : ℝ) < 3 ∧
      0 ≤ pressureGradientSourceExponent (25 / 9 : ℝ) ∧
      pressureGradientSourceExponent (25 / 9 : ℝ) < 3 := by
  rw [pressureGradientSourceExponent_routeA,
    pressureGradientSourceExponent_endgame]
  norm_num

/-! The scalar estimate used after the spatial harmonic estimate has been
    integrated in time.  The source term is intentionally left abstract here;
    the solution-level theorem supplies it from the one-scale estimate. -/

theorem pressure_gradient_two_scale_decay_from_components
    {Φ V : ℝ → ℝ} {C₃ ρ r : ℝ}
    (hC₃ : 0 ≤ C₃) (hρ : 0 < ρ) (hr : 0 < r) (hrr : r ≤ ρ / 8)
    (hΦ : 0 ≤ Φ ρ)
    (hdecomp : Φ r ≤ V r + Φ (r / 2))
    (hpart : V r ≤ C₃ * (r / ρ) ^ (3 : ℕ) * V ρ)
    (hharm : Φ (r / 2) ≤ C₃ * (r / ρ) ^ (3 : ℕ) *
      (Φ ρ + V ρ)) :
    Φ r ≤ 2 * C₃ * (r / ρ) ^ (3 : ℕ) * (Φ ρ + V ρ) := by
  exact pressure_gradient_two_scale_decay hC₃ hρ hr hrr hΦ hdecomp hpart hharm

/-! A geometric-scale form of the standard decay iteration.  This is the
    exact discrete form used by the Morrey wrapper. -/

theorem pressure_gradient_geometric_decay
    {θ σ A B : ℝ} {a : ℕ → ℝ}
    (hθ : 0 ≤ θ) (hσ : 0 ≤ σ) (hθσ : θ < σ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ha : 0 ≤ a 0) (haA : a 0 ≤ A)
    (hrec : ∀ n, a (n + 1) ≤ θ * a n + B * σ ^ n) :
    ∀ n, a n ≤ (A + B / (σ - θ)) * σ ^ n := by
  exact geometric_decay_iteration hθ hσ hθσ hA hB ha haA hrec

end CKN.Core.Step4
