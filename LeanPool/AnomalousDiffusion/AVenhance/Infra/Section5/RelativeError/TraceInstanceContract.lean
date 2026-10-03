/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceInstanceFrozen
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceInstanceInterface
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MStar

/-! # Uniform producer -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Section4
open AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Integration

/-- Uniform AV-parameter positive trace. The recursion constants, and hence
`Ctr`, are selected from `l_recurse β C₀` before the `Ingredients` instance.
The gate and later-scale hypothesis match the step-down part (ii) consumers. -/
theorem e44_initialTrace_contract (β C₀ : ℝ) :
    ∃ Ctr L : ℝ, 1 ≤ Ctr ∧ OnA8Instances β C₀ L
      (fun I _Φ _hΦ κ M R θ₀ m _θm θprev _T =>
        (6 : ℝ) / 5 ≤ β →
        epsilon β I.Λ (m - 1) ^ (1 + gamma β / 2 - delta β) ≤ R →
        e44PositiveTraceInput β I κ M m θ₀ θprev Ctr) := by
  obtain ⟨c, C, hc, hcC, hrec⟩ := AVenhance.l_recurse β C₀
  let Ctr := e44FrozenTraceConstant β c
  refine ⟨Ctr, C, ?_, ?_⟩
  · dsimp [Ctr, e44FrozenTraceConstant, e44TraceCombinationConstant]
    exact le_max_left _ _
  · intro I hCzeta hCxi hChat hCcut Φ hΦ κ hpermissible M hM hPerm R hR
      θ₀ hθ₀smooth hθ₀periodic hmean hanalytic m hm0 hmM θm θprev T
      hθm hθprev hT _hgate hLater
    have hm : 2 ≤ m := by
      exact (mTheta0_spec I.one_lt_beta I.beta_lt I.two_pow_seven_le hR).1.trans hm0
    have hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
        barNorm n (2 ^ 8 * (epsilon β I.Λ j)⁻¹) (Φ j t) ≤
          ENNReal.ofReal (2 ^ 5 * a β I.Λ j * epsilon β I.Λ j ^ 2 *
            (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)) := by
      obtain ⟨_, _, hstream⟩ := AVenhance.stream_regularity β
      intro j hj t n hn
      exact (hstream I Φ hΦ j hj t).2.1 n hn
    have hA5 := (hrec I hCzeta hCxi hChat κ hpermissible M hM hPerm).1
    have hε : 0 < epsilon β I.Λ (m - 1) :=
      Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hε1 : epsilon β I.Λ (m - 1) ≤ 1 :=
      Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hA5at := hA5 (m - 1) (by omega) (by omega)
    have hκupper : I.kappaSeq κ M (m - 1) ≤
        C * epsilon β I.Λ (m - 1) ^ (β + gamma β) := by
      have hid := theta_kappa_power_identity (β := β) (Λ := I.Λ)
        (m := m - 1) hε
      calc
        I.kappaSeq κ M (m - 1) ≤
            C * (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^
              (2 + gamma β)) := by
                simpa [Ingredients.kappaSeq] using hA5at.2
        _ = C * epsilon β I.Λ (m - 1) ^ (β + gamma β) := by rw [hid]
    have hβγ : 1 ≤ β + gamma β := by
      have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
      linarith
    have hεpower : epsilon β I.Λ (m - 1) ^ (β + gamma β) ≤
        epsilon β I.Λ (m - 1) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1 hβγ
    have hCpos : 0 < C := lt_trans hc hcC
    have hΛbase : 0 < (I.Λ : ℝ) := lt_of_lt_of_le hCpos hCcut
    have hΛone : 1 ≤ (I.Λ : ℝ) := by
      exact_mod_cast le_trans (by norm_num : 1 ≤ 2 ^ 7) I.two_pow_seven_le
    have hεLambda := Infra.Ingredients.epsilon_le_lambda_pow
      I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
    have hm1 : 1 ≤ m - 1 := by omega
    have hexponent : -((m - 1 : ℕ) : ℝ) ≤ -1 := by
      have hm1real : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hm1
      linarith
    have hεsmall : epsilon β I.Λ (m - 1) ≤ (I.Λ : ℝ)⁻¹ := by
      calc
        epsilon β I.Λ (m - 1) ≤ (I.Λ : ℝ) ^ (-((m - 1 : ℕ) : ℝ)) := hεLambda
        _ ≤ (I.Λ : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hΛone hexponent
        _ = (I.Λ : ℝ)⁻¹ := by rw [Real.rpow_neg_one]
    have hκ1 : I.kappaSeq κ M (m - 1) ≤ 1 := by
      calc
        I.kappaSeq κ M (m - 1) ≤ C * epsilon β I.Λ (m - 1) :=
          hκupper.trans (mul_le_mul_of_nonneg_left hεpower hCpos.le)
        _ ≤ C * (I.Λ : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hεsmall hCpos.le
        _ ≤ (I.Λ : ℝ) * (I.Λ : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hCcut (inv_nonneg.mpr hΛbase.le)
        _ = 1 := by field_simp
    have hmean' : ∫ x in unitCube, θ₀ x = 0 := by
      simpa [MeanZeroOn] using hmean
    have htrace := e44_initialTrace_of_explicit_A3_A5 I hΦ hm hmM c C hc hcC
      hA3 hA5 hθprev hanalytic hmean' hκ1 hLater
    intro w hw
    exact htrace.2 w hw

end AVenhance.Infra.Section5.RelativeError

end
