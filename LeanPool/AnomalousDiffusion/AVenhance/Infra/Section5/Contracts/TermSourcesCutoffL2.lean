/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46FluxEstimate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs

/-! # `L²_{t,x}` transfer for the `cutoff1` source contract

From a slicewise bound `‖F(t)‖²_{L²} ≤ c² ‖∇T(t)‖²_{L²}` (`t ∈ (0,1)`) to the left side of
`Cutoff1SourceContract`, in terms of the space-time gradient norm of `T`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem TermSourcesCutoffL2.sb_gradNormSq_nonneg (F : Vec 2 → Vec 2) : 0 ≤ gradNormSq F := by
  unfold gradNormSq
  refine integral_nonneg fun x => ?_
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  change 0 ≤ F x 0 * F x 0 + F x 1 * F x 1
  nlinarith [mul_self_nonneg (F x 0), mul_self_nonneg (F x 1)]

theorem sb_l2_timeL2_le {F T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      l2NormSq (F t) ≤ c ^ 2 * gradNormSq (fun x => spaceGrad (T t) x)) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (l2NormSq (F t))) ^ 2) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal ((2 * Real.pi)⁻¹ * c) *
      ENNReal.ofReal (Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (T t) x))) := by
  set k : ℝ := (2 * Real.pi)⁻¹ * c with hk
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (l2NormSq (F t))) ^ 2 ≤
        ENNReal.ofReal k ^ 2 *
          (ENNReal.ofReal (Real.sqrt (gradNormSq (fun x => spaceGrad (T t) x))) ^ 2) := by
    intro t ht
    rw [← mul_pow, ← ENNReal.ofReal_mul hk0]
    refine ENNReal.pow_le_pow_left (ENNReal.ofReal_le_ofReal ?_)
    calc (2 * Real.pi)⁻¹ * Real.sqrt (l2NormSq (F t))
        ≤ (2 * Real.pi)⁻¹ * Real.sqrt (c ^ 2 * gradNormSq (fun x => spaceGrad (T t) x)) := by
          gcongr
          exact h t ht
      _ = k * Real.sqrt (gradNormSq (fun x => spaceGrad (T t) x)) := by
          rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc, hk]; ring
  have hlin : (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.sqrt (l2NormSq (F t))) ^ 2) ≤
      ENNReal.ofReal k ^ 2 * ∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (gradNormSq (fun x => spaceGrad (T t) x))) ^ 2 := by
    calc _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal k ^ 2 *
          (ENNReal.ofReal (Real.sqrt (gradNormSq (fun x => spaceGrad (T t) x))) ^ 2) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          exact hpt t ht
      _ = _ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hR := r46TimeL2_gradient_eq_spaceTime T hT
  unfold r46TimeL2 at hR
  calc _ ≤ (ENNReal.ofReal k ^ 2 * ∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (gradNormSq (fun x => spaceGrad (T t) x))) ^ 2) ^
          (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hlin (by norm_num)
    _ = ENNReal.ofReal k * (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt (gradNormSq (fun x => spaceGrad (T t) x))) ^ 2) ^
          (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ = _ := by rw [hR]

end AVenhance.Infra.Section5.Contracts
end
