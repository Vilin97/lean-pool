/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyTransfer
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools

/-! # Time assembly for the `twistie1` source contract

Abstract measure-theoretic step: if the slices of the negative norm are dominated by
`72 (P₁ √G(t) + P₂)` with `G(t) ≤ ∑_w c_w ‖V_w(t)‖²` (`t ∈ (0,1)`) for fields `V_w` continuous on
`[0,1] × ℝ²`, then the time negative norm is at most
`72 √2 (P₁ √(∑_w c_w ‖V_w‖²_{L²((0,1)×𝕋²)}) + P₂)`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem se_time_assembly {H : ℝ → ENNReal} {G : ℝ → ℝ} (V : List (Fin 2) → ℝ → Vec 2 → Vec 2)
    (cw : List (Fin 2) → ℝ) {P₁ P₂ : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hcw : ∀ w ∈ scWords2, 0 ≤ cw w)
    (hV : ∀ w ∈ scWords2, ∀ i : Fin 2, ContinuousOn (fun p : ℝ × Vec 2 => V w p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    (hG0 : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ G t)
    (hH : ∀ t ∈ Set.Ioo (0 : ℝ) 1, H t ≤ ENNReal.ofReal (72 * (P₁ * Real.sqrt (G t) + P₂)))
    (hGle : ∀ t ∈ Set.Ioo (0 : ℝ) 1, G t ≤ ∑ w ∈ scWords2, cw w * gradNormSq (V w t)) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1, H t ^ 2) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (72 * Real.sqrt 2 *
        (P₁ * Real.sqrt (∑ w ∈ scWords2, cw w * spaceTimeGradNormSq (V w)) + P₂)) := by
  set a : ℝ := 2 * 72 ^ 2 * P₁ ^ 2 with ha
  set Q : ℝ := 2 * 72 ^ 2 * P₂ ^ 2 with hQ
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  set c' : List (Fin 2) → ℝ := fun w => a * cw w with hc'
  have hc'0 : ∀ w ∈ scWords2, 0 ≤ c' w := fun w hw => mul_nonneg ha0 (hcw w hw)
  have hslice : ∀ t ∈ Set.Ioo (0 : ℝ) 1, H t ^ 2 ≤
      ENNReal.ofReal (∑ w ∈ scWords2, c' w * gradNormSq (V w t)) + ENNReal.ofReal Q := by
    intro t ht
    have hY0 : 0 ≤ 72 * (P₁ * Real.sqrt (G t) + P₂) := by
      have := Real.sqrt_nonneg (G t); positivity
    have h1 : H t ^ 2 ≤ ENNReal.ofReal ((72 * (P₁ * Real.sqrt (G t) + P₂)) ^ 2) := by
      rw [ENNReal.ofReal_pow hY0]
      exact pow_le_pow_left' (hH t ht) 2
    refine h1.trans ?_
    rw [← ENNReal.ofReal_add (Finset.sum_nonneg fun w hw =>
      mul_nonneg (hc'0 w hw) (sc_gradNormSq_nonneg _)) hQ0]
    apply ENNReal.ofReal_le_ofReal
    have hs : Real.sqrt (G t) ^ 2 = G t := Real.sq_sqrt (hG0 t ht)
    have hsum : ∑ w ∈ scWords2, c' w * gradNormSq (V w t) =
        a * ∑ w ∈ scWords2, cw w * gradNormSq (V w t) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by rw [hc']; ring
    rw [hsum]
    have hGa : a * G t ≤ a * ∑ w ∈ scWords2, cw w * gradNormSq (V w t) :=
      mul_le_mul_of_nonneg_left (hGle t ht) ha0
    have : (72 * (P₁ * Real.sqrt (G t) + P₂)) ^ 2 ≤ a * G t + Q := by
      have e : (P₁ * Real.sqrt (G t) + P₂) ^ 2 ≤ 2 * (P₁ * Real.sqrt (G t)) ^ 2 + 2 * P₂ ^ 2 := by
        nlinarith [sq_nonneg (P₁ * Real.sqrt (G t) - P₂)]
      calc (72 * (P₁ * Real.sqrt (G t) + P₂)) ^ 2 = 72 ^ 2 * (P₁ * Real.sqrt (G t) + P₂) ^ 2 := by
            ring
        _ ≤ 72 ^ 2 * (2 * (P₁ * Real.sqrt (G t)) ^ 2 + 2 * P₂ ^ 2) :=
            mul_le_mul_of_nonneg_left e (by positivity)
        _ = a * G t + Q := by
            rw [ha, hQ, mul_pow, hs]; ring
    linarith
  have hlin : ∫⁻ t in Set.Ioo (0 : ℝ) 1, H t ^ 2 ≤
      ENNReal.ofReal (∑ w ∈ scWords2, c' w * spaceTimeGradNormSq (V w) + Q) := by
    calc ∫⁻ t in Set.Ioo (0 : ℝ) 1, H t ^ 2
        ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, (ENNReal.ofReal (∑ w ∈ scWords2, c' w *
            gradNormSq (V w t)) + ENNReal.ofReal Q) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          exact hslice t ht
      _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (∑ w ∈ scWords2, c' w *
            gradNormSq (V w t))) + ENNReal.ofReal Q := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
          simp
      _ ≤ ENNReal.ofReal (∑ w ∈ scWords2, c' w * spaceTimeGradNormSq (V w)) +
            ENNReal.ofReal Q := by
          gcongr
          exact sc_lintegral_le_of_slices scWords2 hc'0 hV (f := fun t => ENNReal.ofReal
            (∑ w ∈ scWords2, c' w * gradNormSq (V w t))) (fun t _ => le_rfl)
      _ = _ := by
          rw [← ENNReal.ofReal_add (Finset.sum_nonneg fun w hw =>
            mul_nonneg (hc'0 w hw) (sc_spaceTimeGradNormSq_nonneg _)) hQ0]
  set U : ℝ := ∑ w ∈ scWords2, cw w * spaceTimeGradNormSq (V w) with hU
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun w hw =>
    mul_nonneg (hcw w hw) (sc_spaceTimeGradNormSq_nonneg _)
  have hUa : ∑ w ∈ scWords2, c' w * spaceTimeGradNormSq (V w) = a * U := by
    rw [hU, Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by rw [hc']; ring
  rw [hUa] at hlin
  calc _ ≤ (ENNReal.ofReal (a * U + Q)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hlin (by norm_num)
    _ = ENNReal.ofReal ((a * U + Q) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.sqrt_eq_rpow]
        apply Real.sqrt_le_iff.2
        refine ⟨by positivity, ?_⟩
        have hsU := Real.sq_sqrt hU0
        have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        have hsq : (72 * Real.sqrt 2 * (P₁ * Real.sqrt U + P₂)) ^ 2 =
            72 ^ 2 * 2 * (P₁ ^ 2 * U + 2 * P₁ * P₂ * Real.sqrt U + P₂ ^ 2) := by
          have : (72 * Real.sqrt 2 * (P₁ * Real.sqrt U + P₂)) ^ 2 =
              72 ^ 2 * Real.sqrt 2 ^ 2 * ((P₁ * Real.sqrt U) ^ 2 + 2 * (P₁ * Real.sqrt U) * P₂ +
                P₂ ^ 2) := by ring
          rw [this, hs2, mul_pow, hsU]; ring
        rw [hsq, ha, hQ]
        have hcross : 0 ≤ 2 * P₁ * P₂ * Real.sqrt U := by positivity
        nlinarith [hcross]

end AVenhance.Infra.Section5.Contracts
end
