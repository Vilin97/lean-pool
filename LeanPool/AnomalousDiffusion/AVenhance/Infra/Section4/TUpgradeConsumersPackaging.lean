/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TUpgradeConsumersScalarFinal

/-! # TUpgrade Consumers Packaging

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

/-- Source smallness persists when the universal budget constant is enlarged. -/
theorem iterate_smallness_of_budget_enlargement {e d D : ℝ}
    (hd : 0 < d) (hdD : d ≤ D) (h : e ≤ (4 * D ^ 3)⁻¹) :
    e ≤ (4 * d ^ 3)⁻¹ := by
  have hD : 0 < D := hd.trans_le hdD
  have hp : 4 * d ^ 3 ≤ 4 * D ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hdD 3) (by norm_num)
  exact h.trans ((inv_le_inv₀ (by positivity) (by positivity)).mpr hp)

/-- Normalize the source frequency to the length scale in the downstream statements. -/
theorem iterate_source_frequency_eq {e : ℝ} (he : 0 < e) (γ D : ℝ) :
    D * e ^ (-1 - γ / 2) = D / e ^ (1 + γ / 2) := by
  have hexp : -1 - γ / 2 = -(1 + γ / 2) := by ring
  rw [hexp, Real.rpow_neg he.le]
  rfl

/-- First-gradient shape of `section_four_ansatz_bound.hTjet` from the exact
positive-temperature jet carrier. -/
theorem iterate_ansatz_Tjet_of_positive_jets {β : ℝ} {e A : ℝ}
    {θ₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (he : 0 < e)
    (h : Infra.Section5.RelativeError.PositiveTemperatureJets A (e ^ (1 + gamma β / 2))
      (Real.sqrt (l2NormSq θ₀)) u) :
    ∀ i : Fin 2, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => spaceGrad (u s) x i)) ≤
      A ^ 2 * Real.sqrt (l2NormSq θ₀) * e ^ (-(1 + gamma β / 2)) := by
  intro i s hs
  have hb := h 1 (fun _ => i) (by norm_num) s hs
  have heq : (fun x => iteratedFDeriv ℝ 1 (u s) x (fun _ => basisVec i)) =
      (fun x => spaceGrad (u s) x i) := by
    funext x
    simp only [iteratedFDeriv_one_apply]
    rfl
  rw [heq] at hb
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, pow_one] at hb
  rw [Real.rpow_neg he.le]
  convert hb using 1
  ring

end AVenhance.Infra.Section4
