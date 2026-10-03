/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Chebyshev level bound and the recursion assembly

Two purely analytic helpers used by the generic De Giorgi core
(`Stampacchia/DeGiorgiCore.lean`):

* `real_chebyshev_level`: the real-valued Chebyshev/Markov inequality
  `ε · (μ S)^{1/p} ≤ ‖h‖_{L^p}` whenever `S ⊆ {ε ≤ h}` and `‖h‖_{L^p} < ∞`.
* `sq_level_recursion_of_le`: the elementary squaring/superadditivity step turning
  `ε · |A_l|^{1/p} ≤ R` into `ε² · |A_l|^{2/p} ≤ R²`, combined with the
  subadditivity `(a+b)^{γ} ≤ a^{γ} + b^{γ}` for the two-copy volume.

Both are proved at default heartbeats, no `sorry`.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- **Real Chebyshev level bound.**  If `S ⊆ {x | ε ≤ h x}` with `ε ≥ 0` and
`‖h‖_{L^p(μ)} < ∞`, then
`ε · (μ S)^{1/p} ≤ ‖h‖_{L^p(μ)}` in real numbers. -/
theorem real_chebyshev_level {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ⊤)
    {h : α → ℝ} (hmeas : AEStronglyMeasurable h μ)
    (hfin : eLpNorm h p μ ≠ ⊤)
    {ε : ℝ} (hε : 0 ≤ ε) {S : Set α}
    (hSsub : ∀ x ∈ S, ε ≤ h x) :
    ε * (μ S).toReal ^ (1 / p.toReal) ≤ (eLpNorm h p μ).toReal := by
  set q : ℝ := p.toReal with hq_def
  have hq : 0 < q := ENNReal.toReal_pos hp0 hptop
  -- The ENNReal Chebyshev inequality.
  have hstep := mul_meas_ge_le_pow_eLpNorm' μ hp0 hptop (f := h) (ENNReal.ofReal ε)
  have hSsub' : S ⊆ {x | ENNReal.ofReal ε ≤ ‖h x‖ₑ} := by
    intro x hx
    have hεx : ε ≤ h x := hSsub x hx
    have henorm : ‖h x‖ₑ = ENNReal.ofReal (h x) := Real.enorm_eq_ofReal (le_trans hε hεx)
    rw [Set.mem_ofPred_eq, henorm]
    exact ENNReal.ofReal_le_ofReal hεx
  have hcombined :
      (ENNReal.ofReal ε) ^ q * μ S ≤ eLpNorm h p μ ^ q := by
    refine le_trans ?_ hstep
    exact mul_le_mul_right (measure_mono hSsub') _
  -- Move to reals.
  have hNfin : eLpNorm h p μ ^ q ≠ ⊤ := by
    simpa using ENNReal.rpow_ne_top_of_nonneg hq.le hfin
  have htoReal := ENNReal.toReal_mono hNfin hcombined
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hε] at htoReal
  -- `htoReal : ε ^ q * (μ S).toReal ≤ (eLpNorm h p μ).toReal ^ q`
  set m : ℝ := (μ S).toReal with hm_def
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set N : ℝ := (eLpNorm h p μ).toReal with hN_def
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  -- Raise both sides to the power `1/q`.
  have hLHSnn : 0 ≤ ε ^ q * m := mul_nonneg (Real.rpow_nonneg hε _) hm0
  have hmono := Real.rpow_le_rpow hLHSnn htoReal (le_of_lt (by positivity : (0:ℝ) < 1 / q))
  rw [Real.mul_rpow (Real.rpow_nonneg hε _) hm0] at hmono
  rw [← Real.rpow_mul hε, ← Real.rpow_mul hN0, mul_one_div, div_self hq.ne',
    Real.rpow_one, Real.rpow_one] at hmono
  exact hmono

/-- **Squaring step of the level recursion.**  From the two per-copy Chebyshev
bounds `ε · (vol S₁)^{1/p} ≤ N₁`, `ε · (vol S₂)^{1/p} ≤ N₂` and a bound
`N₁ + N₂ ≤ R`, together with `0 ≤ ε` and `0 < 1/p ≤ 1`, we obtain
`ε² · (vol S₁ + vol S₂)^{2/p} ≤ R²`. -/
theorem sq_level_recursion_of_le
    {ε r a b N₁ N₂ R : ℝ} (hε : 0 ≤ ε)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hN₁ : ε * a ^ r ≤ N₁) (hN₂ : ε * b ^ r ≤ N₂)
    (hsum : N₁ + N₂ ≤ R) (hR : 0 ≤ R) :
    ε ^ 2 * (a + b) ^ (2 * r) ≤ R ^ 2 := by
  -- Superadditivity of `t ↦ t^r`.
  have hsuper : (a + b) ^ r ≤ a ^ r + b ^ r := Real.rpow_add_le_add_rpow ha hb hr0 hr1
  have hlow : ε * (a + b) ^ r ≤ R := by
    calc ε * (a + b) ^ r ≤ ε * (a ^ r + b ^ r) := by
            exact mul_le_mul_of_nonneg_left hsuper hε
      _ = ε * a ^ r + ε * b ^ r := by ring
      _ ≤ N₁ + N₂ := add_le_add hN₁ hN₂
      _ ≤ R := hsum
  have hAB0 : 0 ≤ (a + b) ^ r := Real.rpow_nonneg (add_nonneg ha hb) _
  have hlow0 : 0 ≤ ε * (a + b) ^ r := mul_nonneg hε hAB0
  have hsq := mul_le_mul hlow hlow hlow0 hR
  have hAB2 : (a + b) ^ (2 * r) = (a + b) ^ r * (a + b) ^ r := by
    rw [show (2 * r) = r + r by ring,
      Real.rpow_add_of_nonneg (add_nonneg ha hb) hr0 hr0]
  calc ε ^ 2 * (a + b) ^ (2 * r)
      = (ε * (a + b) ^ r) * (ε * (a + b) ^ r) := by rw [hAB2]; ring
    _ ≤ R * R := hsq
    _ = R ^ 2 := by ring

end Homogenization
