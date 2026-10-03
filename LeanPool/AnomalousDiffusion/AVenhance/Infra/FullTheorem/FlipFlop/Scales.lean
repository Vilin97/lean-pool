/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.FlipFlop.Abstract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaPrimeScaling
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.Parameters
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Scalars

/-! # Scale comparison for the flip-flop

`|log (ε_{n+1}^{β-γ} / ε_n^{β+γ})| ≤ 2 (β-γ) K_s ε_n` for `n ≥ 1`, where
`K_s = max 10 (supergeoConstant β)`; and the identity `a_n² ε_n⁴ = ε_n^{2β}`. -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.FlipFlop

open AVenhance

/-- The constant of the two-sided supergeometric comparison. -/
def ksConst (β : ℝ) : ℝ := max 10 (Infra.Ingredients.supergeoConstant β)

theorem ksConst_ge_ten (β : ℝ) : 10 ≤ ksConst β := le_max_left _ _

theorem beta_sub_gamma_pos {β : ℝ} (hβ : 1 < β) (hβ' : β < 4 / 3) : 0 < β - gamma β := by
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ hβ'
  have hs : β - gamma β = 2 * β / (q β + 1) := by
    unfold gamma
    field_simp [ne_of_gt (by linarith : 0 < q β + 1)]
    ring
  rw [hs]
  have : 0 < q β + 1 := by linarith
  positivity

theorem log_eps_ratio {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {n : ℕ} (hn : 1 ≤ n) (hsmall : 2 * ksConst β * epsilon β Λ n ≤ 1) :
    |Real.log (epsilon β Λ (n + 1) ^ (β - gamma β) / epsilon β Λ n ^ (β + gamma β))| ≤
      2 * (β - gamma β) * ksConst β * epsilon β Λ n := by
  have he : 0 < epsilon β Λ n := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hE : 0 < epsilon β Λ (n + 1) := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hqe : 0 < epsilon β Λ n ^ q β := Real.rpow_pos_of_pos he _
  obtain ⟨h1, h2⟩ := Infra.Ingredients.epsilon_supergeo hβ hβ' hΛ hn
  have hS : 0 ≤ Infra.Ingredients.supergeoConstant β := by
    have : 0 ≤ q β := (Infra.Ingredients.one_lt_q hβ hβ').le.trans' (by norm_num)
    unfold Infra.Ingredients.supergeoConstant
    positivity
  have hKs : Infra.Ingredients.supergeoConstant β ≤ ksConst β := le_max_right _ _
  have hK10 := ksConst_ge_ten β
  have hp := beta_sub_gamma_pos hβ hβ'
  set e := epsilon β Λ n
  set E := epsilon β Λ (n + 1)
  set x := E / e ^ q β - 1 with hx
  have hxlo : -(ksConst β * e) ≤ x := by
    have : (1 - 10 * e) ≤ E / e ^ q β := (le_div_iff₀ hqe).2 h1
    nlinarith
  have hxhi : x ≤ ksConst β * e := by
    have : E / e ^ q β ≤ 1 + Infra.Ingredients.supergeoConstant β * e :=
      (div_le_iff₀ hqe).2 h2
    nlinarith
  have hxabs : |x| ≤ ksConst β * e := abs_le.2 ⟨hxlo, hxhi⟩
  have hhalf : |x| ≤ 1 / 2 := by nlinarith
  have hratio : E ^ (β - gamma β) / e ^ (β + gamma β) = (1 + x) ^ (β - gamma β) := by
    have h1x : 1 + x = E / e ^ q β := by rw [hx]; ring
    rw [h1x, Real.div_rpow hE.le hqe.le, ← Real.rpow_mul he.le,
      Section3.q_gamma_balance hβ hβ']
  rw [hratio, Real.log_rpow (by linarith [(abs_le.1 hhalf).1])]
  rw [abs_mul, abs_of_pos hp]
  have := abs_log_one_add_le hhalf
  calc (β - gamma β) * |Real.log (1 + x)| ≤ (β - gamma β) * (2 * |x|) :=
        mul_le_mul_of_nonneg_left this hp.le
    _ ≤ (β - gamma β) * (2 * (ksConst β * e)) := by gcongr
    _ = _ := by ring

/-- `a_n² ε_n⁴ = ε_n^{2β}`. -/
theorem a_sq_mul_eps_four {β : ℝ} {Λ : ℕ} (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    (n : ℕ) : a β Λ n ^ 2 * epsilon β Λ n ^ 4 = epsilon β Λ n ^ (2 * β) := by
  have he : 0 < epsilon β Λ n := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  unfold a
  rw [← Real.rpow_natCast, ← Real.rpow_mul he.le, ← Real.rpow_natCast (epsilon β Λ n) 4,
    ← Real.rpow_add he]
  congr 1
  push_cast
  ring

end AVenhance.Infra.FullTheorem.FlipFlop
