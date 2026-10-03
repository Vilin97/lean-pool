/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSource
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsCentered
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredAnalyticInputs

/-! # Composed analyticity of the slow factors: assembly

Feeds the word bounds of `Q`, `A`, `Y'` (`TermCenteredAnalyticJets`), the temperature jets and the
flow jets (`TermCenteredAnalyticInputs`) and smoothness/periodicity (`TermCenteredAnalyticSmooth`)
to `slowFactorChoice2/3_composed_bounds`, and weakens the resulting radius and amplitude to the
normalised ones `ρ / c₂`, `c₁ κ S ρ⁻²`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4
    AVenhance.Infra.Section5.RelativeError

/-- `HasCoordinateAnalyticL2Bounds` is monotone in the amplitude and anti-monotone in the radius. -/
theorem sdc_hasCoordinate_mono {f : Vec 2 → ℂ} {Cf Cf' r r' : ℝ}
    (h : Infra.Ergodic.HasCoordinateAnalyticL2Bounds f Cf r) (hCf : 0 ≤ Cf) (hC : Cf ≤ Cf')
    (hr' : 0 < r') (hr : r' ≤ r) : Infra.Ergodic.HasCoordinateAnalyticL2Bounds f Cf' r' := by
  intro i n
  refine (h i n).trans ?_
  have hpow : r' ^ n ≤ r ^ n := pow_le_pow_left₀ hr'.le hr n
  have hpos : 0 < r' ^ n := pow_pos hr' n
  have hnum : Cf * (n.factorial : ℝ) ≤ Cf' * (n.factorial : ℝ) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  calc Cf * (n.factorial : ℝ) / r ^ n ≤ Cf * (n.factorial : ℝ) / r' ^ n :=
        div_le_div_of_nonneg_left (by positivity) hpos hpow
    _ ≤ Cf' * (n.factorial : ℝ) / r' ^ n := div_le_div_of_nonneg_right hnum hpos.le

/-- Abstract-real radius arithmetic. -/
theorem sdc_radius_ge {ε ρ K A₁ : ℝ} (hρ : 0 < ρ) (hρε : ρ ≤ ε) (hK : 1 ≤ K) (hA₁ : 1 ≤ A₁) :
    ρ / (2 * 2 ^ 14 * 33 * K * A₁) ≤
      (16 * (A₁ / ρ))⁻¹ / ((2 * 2 ^ 14 / ε) * ((16 * (A₁ / ρ))⁻¹ + 2 * (K * ε))) := by
  have he : 0 < ε := hρ.trans_le hρε
  have hK0 : 0 < K := by linarith
  have hA0 : 0 < A₁ := by linarith
  set u : ℝ := (16 * (A₁ / ρ))⁻¹ with hu
  have hu0 : 0 < u := by positivity
  have hρu : ρ = 16 * A₁ * u := by
    rw [hu]; field_simp
  have hden : 0 < (2 * 2 ^ 14 / ε) * (u + 2 * (K * ε)) := by positivity
  have hc2 : 0 < 2 * 2 ^ 14 * 33 * K * A₁ := by positivity
  rw [div_le_div_iff₀ hc2 hden]
  have h1 : ρ * ((2 * 2 ^ 14 / ε) * (u + 2 * (K * ε))) =
      2 ^ 15 * (ρ / ε) * u + 2 ^ 16 * K * ρ := by
    field_simp
  have h2 : ρ / ε ≤ 1 := (div_le_one he).2 hρε
  have h3 : 2 ^ 15 * (ρ / ε) * u ≤ 2 ^ 15 * u := by
    have := mul_le_mul_of_nonneg_right h2 hu0.le
    nlinarith
  have hKA : 1 ≤ K * A₁ := one_le_mul_of_one_le_of_one_le hK hA₁
  have h4 := mul_nonneg hu0.le (sub_nonneg.2 hKA)
  rw [h1]
  have h5 : 2 ^ 16 * K * ρ = 2 ^ 20 * (K * A₁) * u := by rw [hρu]; ring
  rw [h5]
  nlinarith

end AVenhance.Infra.Section5.Contracts
end
