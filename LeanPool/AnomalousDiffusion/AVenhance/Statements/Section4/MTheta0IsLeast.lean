/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.IsStreamSeq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelContinuous
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamVelLipschitz
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.KappaAt
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermittedInterval
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.PermissibleSet
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.ChiM
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.Flux
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.TimeAvgMat
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.GradMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceLap
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsWeakSolutionGrad
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.Ingredients
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatXiML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.HatZetaML
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.XiMK
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Ingredients.ZetaMK
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.LIdxConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.MTheta0

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- The set defining `m_{θ₀}` is nonempty (`ε_m → 0`), so `mTheta0` is its least element, not the
junk value `0` of `sInf ∅`. -/
theorem mTheta0_isLeast {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) {Λ : ℕ} (hΛ : 2 ^ 7 ≤ Λ)
    {R : ℝ} (hR : 0 < R) :
    IsLeast {m : ℕ | 2 ≤ m ∧ epsilon β Λ (m - 1) ^ (1 + gamma β / 2) ≤ R} (mTheta0 β Λ R) := by
  have hne : {m : ℕ | 2 ≤ m ∧ epsilon β Λ (m - 1) ^ (1 + gamma β / 2) ≤ R}.Nonempty := by
    have hq : 1 < q β := AVenhance.Infra.Ingredients.one_lt_q hβ hβ'
    have hγ : 0 ≤ gamma β := by
      unfold gamma
      have : 0 < q β + 1 := by linarith
      have : 0 ≤ (q β - 1) * β := by nlinarith
      positivity
    have hΛ1 : (Λ : ℝ)⁻¹ < 1 := by
      have : (1 : ℝ) < Λ := by
        have : (2 : ℝ) ^ 7 ≤ Λ := by exact_mod_cast hΛ
        linarith
      exact inv_lt_one_of_one_lt₀ this
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hR hΛ1
    refine ⟨N + 2, by omega, ?_⟩
    have hε := AVenhance.Infra.Ingredients.epsilon_le_lambda_pow (β := β) (Λ := Λ)
      (m := N + 2 - 1) hβ hβ' hΛ
    have hΛpos : (0 : ℝ) < Λ := by
      have : (2 : ℝ) ^ 7 ≤ Λ := by exact_mod_cast hΛ
      linarith
    have hε0 : 0 ≤ epsilon β Λ (N + 2 - 1) := by
      unfold epsilon
      split_ifs
      · norm_num
      · positivity
    have hpow : (Λ : ℝ) ^ (-((N + 2 - 1 : ℕ) : ℝ)) ≤ (Λ : ℝ)⁻¹ ^ N := by
      have h1 : (Λ : ℝ) ^ (-((N + 2 - 1 : ℕ) : ℝ)) = ((Λ : ℝ)⁻¹) ^ (N + 1) := by
        rw [show N + 2 - 1 = N + 1 from rfl, Real.rpow_neg hΛpos.le, Real.rpow_natCast, inv_pow]
      rw [h1]
      exact pow_le_pow_of_le_one (inv_nonneg.mpr hΛpos.le) hΛ1.le (Nat.le_succ N)
    have hε1 : epsilon β Λ (N + 2 - 1) ≤ 1 := by
      refine hε.trans (hpow.trans ?_)
      exact pow_le_one₀ (inv_nonneg.mpr hΛpos.le) hΛ1.le
    have hεR : epsilon β Λ (N + 2 - 1) ≤ R := hε.trans (hpow.trans hN.le)
    rcases hε0.eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith)]
      exact hR.le
    · calc epsilon β Λ (N + 2 - 1) ^ (1 + gamma β / 2)
          ≤ epsilon β Λ (N + 2 - 1) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hpos hε1 (by linarith)
        _ ≤ R := by rw [Real.rpow_one]; exact hεR
  exact ⟨Nat.sInf_mem hne, fun m hm => Nat.sInf_le hm⟩

end AVenhance
