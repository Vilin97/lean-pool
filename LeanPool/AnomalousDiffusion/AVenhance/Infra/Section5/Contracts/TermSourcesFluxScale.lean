/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsScales
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzScale

/-! # Abstract-real scale arithmetic for the flux source contracts

Pure real lemmas combining the scale package `left_to_show_scales` with the pointwise flux bounds
(source `e.monster.est.7`, `.10`, `.11`).  The key facts are

* `κ_m + a_m ε_m² ≤ (1 + √K) √κ_m √κ_{m-1}` (the source's `κ_m + a_m ε_m² ≲ √(κ_m κ_{m-1})`);
* `ε_m (a_m ε_m²/κ_m) ε_{m-1}^{-(1+γ/2)} ≤ 2π K² ε_{m-1}^δ`. -/

@[expose] public section

open Real

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance

/-- `κ + a ε² ≤ (1 + √K) √κ √κ'`. -/
theorem sa_mu_le {a ε κ κp K : ℝ} (ha : 0 ≤ a) (hκ : 0 < κ) (hκκp : κ ≤ κp) (hK : 0 ≤ K)
    (h : a ^ 2 * ε ^ 4 / κ ≤ K * κp) :
    κ + a * ε ^ 2 ≤ (1 + Real.sqrt K) * Real.sqrt κ * Real.sqrt κp := by
  have hκp : 0 ≤ κp := hκ.le.trans hκκp
  have hcs := RelativeError.corr_mul_sqrt_le (ε := ε) ha hκ hK hκp h
  have hsm : Real.sqrt κ ≤ Real.sqrt κp := Real.sqrt_le_sqrt hκκp
  have hsq : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ.le
  have hid : κ + a * ε ^ 2 = Real.sqrt κ * (Real.sqrt κ + a * ε ^ 2 / κ * Real.sqrt κ) := by
    have hdiv : a * ε ^ 2 / κ * κ = a * ε ^ 2 := div_mul_cancel₀ _ hκ.ne'
    calc κ + a * ε ^ 2 = κ + a * ε ^ 2 / κ * κ := by rw [hdiv]
      _ = Real.sqrt κ * Real.sqrt κ + a * ε ^ 2 / κ * (Real.sqrt κ * Real.sqrt κ) := by
          rw [hsq]
      _ = _ := by ring
  rw [hid]
  have hs0 : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg _
  calc Real.sqrt κ * (Real.sqrt κ + a * ε ^ 2 / κ * Real.sqrt κ)
      ≤ Real.sqrt κ * (Real.sqrt κp + Real.sqrt K * Real.sqrt κp) :=
        mul_le_mul_of_nonneg_left (add_le_add hsm hcs) hs0
    _ = _ := by ring

/-- `ε_m c ρ⁻¹ ≤ 2π K² ε^δ` for `c = a ε_m²/κ_m`. -/
theorem sa_chi_ratio {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) {K e em c : ℝ} (hK : 1 ≤ K)
    (he : 0 < e) (he1 : e ≤ 1) (hem : 0 < em) (hc0 : 0 ≤ c) (hc : c ≤ K * em ^ (-gamma β))
    (hemK : em ≤ K * e ^ q β) :
    em * c * (e ^ (1 + gamma β / 2))⁻¹ ≤ 2 * Real.pi * K ^ 2 * e ^ delta β := by
  have h := Integration.ansatz_scale_bound hβ hβ' hK he he1 hem hc0 hc hemK
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [← Real.rpow_neg he.le]
  have h2 : em * c * e ^ (-(1 + gamma β / 2)) =
      2 * Real.pi * (c * em / (2 * Real.pi) * e ^ (-(1 + gamma β / 2))) := by
    field_simp
  rw [h2, mul_assoc (2 * Real.pi)]
  exact mul_le_mul_of_nonneg_left h hpi.le

/-- Final arithmetic for `twistie3`. -/
theorem sa_twistie3_arith {μ e sT sp sm A B K : ℝ} (hμ : μ ≤ (1 + Real.sqrt K) * sm * sp)
    (hsT : 0 ≤ sT) (he : 0 ≤ e) (hsm : 0 ≤ sm) (hT : sp * sT ≤ A * B) :
    6 * (μ * e) * sT ≤ 6 * (1 + Real.sqrt K) * A * e * sm * B := by
  have hK1 : 0 ≤ 1 + Real.sqrt K := by positivity
  have h1 : μ * sT ≤ (1 + Real.sqrt K) * sm * (A * B) :=
    calc μ * sT ≤ (1 + Real.sqrt K) * sm * sp * sT := mul_le_mul_of_nonneg_right hμ hsT
      _ = (1 + Real.sqrt K) * sm * (sp * sT) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
  calc 6 * (μ * e) * sT = 6 * e * (μ * sT) := by ring
    _ ≤ 6 * e * ((1 + Real.sqrt K) * sm * (A * B)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- Final arithmetic for `normie2`. -/
theorem sa_normie2_arith {μ sH sp sm CH E B K : ℝ} (hμ : μ ≤ (1 + Real.sqrt K) * sm * sp)
    (hsH : 0 ≤ sH) (hsm : 0 ≤ sm) (hH : sp * sH ≤ CH * E * B) :
    3 * μ * sH ≤ 3 * (1 + Real.sqrt K) * sm * (CH * E * B) := by
  have hK1 : 0 ≤ 1 + Real.sqrt K := by positivity
  have h1 : μ * sH ≤ (1 + Real.sqrt K) * sm * (CH * E * B) :=
    calc μ * sH ≤ (1 + Real.sqrt K) * sm * sp * sH := mul_le_mul_of_nonneg_right hμ hsH
      _ = (1 + Real.sqrt K) * sm * (sp * sH) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (by positivity)
  calc 3 * μ * sH = 3 * (μ * sH) := by ring
    _ ≤ 3 * ((1 + Real.sqrt K) * sm * (CH * E * B)) := by gcongr
    _ = _ := by ring

/-- Final arithmetic for `normie1`. -/
theorem sa_normie1_arith {μ cχ D ρ sT s0 s1 sp sm A B K e : ℝ} (hK : 1 ≤ K) (he : 0 ≤ e) (hμ0 : 0
    ≤ μ) (hc0 : 0 ≤ cχ) (hρ : 0 < ρ) (hsp : 0 < sp)
    (hsm : 0 ≤ sm) (hD : D ≤ 2 ^ 16 * ρ⁻¹)
    (hsT : 0 ≤ sT) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1)
    (hμ : μ ≤ (1 + Real.sqrt K) * sm * sp)
    (hcρ : cχ * ρ⁻¹ ≤ 2 * Real.pi * K ^ 2 * e)
    (hT : sp * sT ≤ A * B) (h0 : sp * s0 ≤ A * (A / ρ) * B)
    (h1 : sp * s1 ≤ A * (A / ρ) * B) :
    40 * (2 * (μ * cχ) * D) * sT + 10 * (2 * (μ * cχ)) * s0 + 10 * (2 * (μ * cχ)) * s1 ≤
      ((80 * 2 ^ 16 * A + 40 * A ^ 2) * ((1 + Real.sqrt K) * (2 * Real.pi * K ^ 2))) * e * sm * B
          := by
  have hK1 : 0 ≤ 1 + Real.sqrt K := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  set Z := (1 + Real.sqrt K) * sm * (2 * Real.pi * K ^ 2 * e) with hZ
  have hZ0 : 0 ≤ Z := by
    have : 0 ≤ K := by linarith
    positivity
  set Y := μ * cχ * ρ⁻¹ with hY
  have hρi : 0 < ρ⁻¹ := inv_pos.2 hρ
  have hY0 : 0 ≤ Y := by positivity
  have hYle : Y ≤ sp * Z := by
    calc Y = μ * (cχ * ρ⁻¹) := by rw [hY]; ring
      _ ≤ ((1 + Real.sqrt K) * sm * sp) * (2 * Real.pi * K ^ 2 * e) :=
          mul_le_mul hμ hcρ (by positivity) (by positivity)
      _ = sp * Z := by rw [hZ]; ring
  -- first-order term
  have hT1 : Y * sT ≤ Z * (A * B) :=
    calc Y * sT ≤ sp * Z * sT := mul_le_mul_of_nonneg_right hYle hsT
      _ = Z * (sp * sT) := by ring
      _ ≤ Z * (A * B) := mul_le_mul_of_nonneg_left hT hZ0
  have hD1 : 2 * (μ * cχ) * D ≤ 2 * (2 ^ 16 * Y) := by
    calc 2 * (μ * cχ) * D ≤ 2 * (μ * cχ) * (2 ^ 16 * ρ⁻¹) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ = 2 * (2 ^ 16 * Y) := by rw [hY]; ring
  have hfirst : 40 * (2 * (μ * cχ) * D) * sT ≤ 80 * 2 ^ 16 * (Z * (A * B)) := by
    calc 40 * (2 * (μ * cχ) * D) * sT ≤ 40 * (2 * (2 ^ 16 * Y)) * sT := by gcongr
      _ = 80 * 2 ^ 16 * (Y * sT) := by ring
      _ ≤ _ := by gcongr
  -- second-order terms
  have hH : ∀ s : ℝ, 0 ≤ s → sp * s ≤ A * (A / ρ) * B →
      10 * (2 * (μ * cχ)) * s ≤ 20 * (Z * (A * A * B)) := by
    intro s hs hss
    have hμc : μ * cχ = Y * ρ := by rw [hY]; field_simp
    calc 10 * (2 * (μ * cχ)) * s = 20 * (Y * ρ * s) := by rw [hμc]; ring
      _ ≤ 20 * (sp * Z * ρ * s) := by gcongr
      _ = 20 * (Z * ρ * (sp * s)) := by ring
      _ ≤ 20 * (Z * ρ * (A * (A / ρ) * B)) := by gcongr
      _ = 20 * (Z * (A * A * B)) := by field_simp
  have e0 := hH s0 hs0 h0
  have e1 := hH s1 hs1 h1
  have hZe : Z * B = (1 + Real.sqrt K) * (2 * Real.pi * K ^ 2) * e * sm * B := by
    rw [hZ]; ring
  calc _ ≤ 80 * 2 ^ 16 * (Z * (A * B)) + 20 * (Z * (A * A * B)) + 20 * (Z * (A * A * B)) := by
        linarith
    _ = (80 * 2 ^ 16 * A + 40 * A ^ 2) * (Z * B) := by ring
    _ = _ := by rw [hZe]; ring

end AVenhance.Infra.Section5.Contracts
end
