/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesPhysicalBudgetScales

/-! # Iterates Inflated Radius Scale

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

/-- The exponent budget gamma >= 4 delta keeps the inflated analytic
frequency below R/F times the chosen norm frequency. -/
theorem iterate_inflated_radius_ratio {e γ δ L F R : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hL : 0 < L) (hFpos : 0 < F)
    (hR : 0 ≤ R) (hγδ : 4 * δ ≤ γ)
    (hF : F = e ^ (1 + γ / 2) * L) :
    ((R / e) / e ^ (2 * δ)) / L ≤ R / F := by
  have hp : 0 < e ^ (2 * δ) := Real.rpow_pos_of_pos he _
  have hx : e ^ (γ / 2 - 2 * δ) * (e * e ^ (2 * δ)) = e ^ (1 + γ / 2) := by
    calc
      _ = e ^ (γ / 2 - 2 * δ) * (e ^ (1 : ℝ) * e ^ (2 * δ)) := by rw [Real.rpow_one]
      _ = e ^ ((γ / 2 - 2 * δ) + (1 + 2 * δ)) := by rw [← Real.rpow_add he, ← Real.rpow_add he]
      _ = _ := by congr 1; ring
  have hpow : e ^ (γ / 2 - 2 * δ) ≤ 1 :=
    Real.rpow_le_one he.le he1 (by linarith only [hγδ])
  have heq : (((R / e) / e ^ (2 * δ)) / L) * F = R * e ^ (γ / 2 - 2 * δ) := by
    rw [hF, ← hx]
    field_simp
  have hb := mul_le_mul_of_nonneg_left hpow hR
  apply (le_div_iff₀ hFpos).mpr
  rw [heq]
  simpa only [mul_one] using hb

/-- One uniform numerical choice of the l.V constant supplies both radius
conditions after inflation. -/
theorem iterate_inflated_radius_geometric_conditions {r rvel L R F C₀ : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hrvel : 0 ≤ rvel) (_hR : 0 ≤ R)
    (hC₀ : 0 < C₀) (hF : C₀ ≤ F) (hlarge : 4 * R ≤ C₀)
    (hscale : r / L ≤ R / F) (hvel : rvel ≤ r) :
    2 * (r / L) ^ 2 ≤ 1 / 2 ∧ 2 * (rvel / L) ^ 2 ≤ 1 / 4 := by
  have hFp : 0 < F := hC₀.trans_le hF
  have hR4 : R / F ≤ 1 / 4 := (div_le_iff₀ hFp).mpr (by linarith only [hlarge, hF])
  have hr4 := hscale.trans hR4
  have hv4 := (div_le_div_of_nonneg_right hvel hL.le).trans hr4
  have hr0 : 0 ≤ r / L := div_nonneg hr hL.le
  have hv0 : 0 ≤ rvel / L := div_nonneg hrvel hL.le
  constructor <;> nlinarith only [hr4, hv4, hr0, hv0]

end AVenhance.Infra.Section4
