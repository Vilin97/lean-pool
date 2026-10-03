/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaAtPrimeBootstrap
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaPrimeScaling
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Numeric.Exponents
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Scalars

/-! One-sided permitted-interval bounds at the top scale. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

theorem LRecurseTop.top_exponent_gap {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) :
    2 * delta β ≤ q β * (2 - β + gamma β) -
      (2 - β + 4 * delta β) := by
  let r := q β
  have hr : 1 < r := Infra.Ingredients.one_lt_q hβ hβ'
  have hden : 0 < 4 * r - 1 := by linarith
  have hden' : 0 < r + 1 := by linarith
  have hβr : β = 4 * r / (4 * r - 1) := by
    dsimp [r]
    rw [Infra.Ingredients.q_eq_beta_div_four_sub_one hβ]
    field_simp [ne_of_gt (sub_pos.mpr hβ)]
    ring
  have hγr : gamma β = 4 * r * (r - 1) /
      ((4 * r - 1) * (r + 1)) := by
    unfold gamma
    rw [show q β = r by rfl, hβr]
    field_simp [ne_of_gt hden, ne_of_gt hden']
  have hδr : delta β = (r - 1) ^ 2 /
      (4 * (r + 1) * (4 * r - 1)) :=
    Infra.Ingredients.delta_eq_q_fraction hβ hβ'
  have hidentity :
      q β * (2 - β + gamma β) - (2 - β + 4 * delta β) -
          2 * delta β =
        (r - 1) * (32 * r ^ 2 + 2 * r - 2) /
          (4 * (r + 1) * (4 * r - 1)) := by
    rw [show q β = r by rfl, hγr, hδr, hβr]
    field_simp [ne_of_gt hden, ne_of_gt hden',
      (show (0 : ℝ) < r * 4 - 1 by linarith only [hr]).ne']
    ring_nf
  have hpoly : 0 < 32 * r ^ 2 + 2 * r - 2 := by
    have hr2 : 1 < r ^ 2 := one_lt_pow₀ hr (by norm_num)
    linarith only [hr, hr2]
  have hnonneg : 0 ≤
      (r - 1) * (32 * r ^ 2 + 2 * r - 2) /
        (4 * (r + 1) * (4 * r - 1)) := by
    positivity
  linarith [hidentity, hnonneg]

/-- The one-sided facts at the terminal index. The coefficient depends
only on β. The ratio estimate includes the exceptional case `M = 1`. -/
theorem l_recurse_top {β : ℝ} {Λ M : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpermitted : κ ∈ permittedInterval β Λ M) (hM : 1 ≤ M) :
    (1 / 2 : ℝ) * a β Λ M * epsilon β Λ M ^ (2 + gamma β) ≤ κ ∧
      epsilon β Λ M ^ 2 / (κ * tau β Λ M) ≤
        kappaPrimeEndpointExpratConstant β *
          epsilon β Λ (M - 1) ^ (2 * delta β) := by
  let e := epsilon β Λ M
  let ep := epsilon β Λ (M - 1)
  let p := β - gamma β
  let θ := 2 - β + gamma β
  let s := 2 - β + 4 * delta β
  let A := 1 + Infra.Ingredients.supergeoConstant β / 128
  have he : 0 < e := by dsimp [e]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have heOne : e ≤ 1 := by
    dsimp [e]
    exact Infra.Construction.epsilon_le_one hβ hβ' hΛ
  have hep : 0 < ep := by dsimp [ep]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hepOne : ep ≤ 1 := by
    dsimp [ep]
    exact Infra.Construction.epsilon_le_one hβ hβ' hΛ
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ hβ'
  have hp : 0 < p := by
    dsimp [p]
    have hbal := q_gamma_balance hβ hβ'
    have hmul : (β - gamma β) * (q β + 1) = 2 * β := by
      calc
        (β - gamma β) * (q β + 1) =
            q β * (β - gamma β) + (β - gamma β) := by ring
        _ = (β + gamma β) + (β - gamma β) := by rw [hbal]
        _ = 2 * β := by ring
    have hden : 0 < q β + 1 := by linarith
    have hExp : β - gamma β = 2 * β / (q β + 1) := by
      calc
        β - gamma β = ((β - gamma β) * (q β + 1)) / (q β + 1) := by
          field_simp [ne_of_gt hden]
        _ = 2 * β / (q β + 1) := by rw [hmul]
    rw [hExp]
    positivity
  have htheta : 0 < θ := by
    dsimp [θ]
    linarith only [hβ', hγ]
  have hS : 0 ≤ Infra.Ingredients.supergeoConstant β := by
    dsimp [Infra.Ingredients.supergeoConstant]
    positivity
  have hA : 1 ≤ A := by
    dsimp [A]
    linarith only [hS]
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hperLo : (1 / 2 : ℝ) * e ^ p ≤ κ := by
    have hper := Set.mem_Icc.mp hpermitted
    have hmul : (β - gamma β) * (q β + 1) = 2 * β := by
      have hbal := q_gamma_balance hβ hβ'
      calc
        (β - gamma β) * (q β + 1) =
            q β * (β - gamma β) + (β - gamma β) := by ring
        _ = (β + gamma β) + (β - gamma β) := by rw [hbal]
        _ = 2 * β := by ring
    have hden : 0 < q β + 1 := by linarith
    have hExp : β - gamma β = 2 * β / (q β + 1) := by
      calc
        β - gamma β = ((β - gamma β) * (q β + 1)) / (q β + 1) := by
          field_simp [ne_of_gt hden]
        _ = 2 * β / (q β + 1) := by rw [hmul]
    simpa [e, p, permittedInterval, hExp] using hper.1
  have hscale : a β Λ M * e ^ (2 + gamma β) =
      e ^ (β + gamma β) := by
    calc
      a β Λ M * e ^ (2 + gamma β) =
          e ^ (β - 2) * e ^ (2 + gamma β) := by rfl
      _ = e ^ ((β - 2) + (2 + gamma β)) := by
        rw [← Real.rpow_add he]
      _ = e ^ (β + gamma β) := by congr 1; ring
  have hpowLower : e ^ (β + gamma β) ≤ e ^ p := by
    dsimp [p]
    exact Real.rpow_le_rpow_of_exponent_ge he heOne (by linarith only [hγ])
  have hlower : (1 / 2 : ℝ) * a β Λ M * e ^ (2 + gamma β) ≤ κ := by
    calc
      (1 / 2 : ℝ) * a β Λ M * e ^ (2 + gamma β) =
          (1 / 2 : ℝ) * (a β Λ M * e ^ (2 + gamma β)) := by ring
      _ = (1 / 2 : ℝ) * e ^ (β + gamma β) := by rw [hscale]
      _ ≤ (1 / 2 : ℝ) * e ^ p :=
        mul_le_mul_of_nonneg_left hpowLower (by norm_num)
      _ ≤ κ := hperLo
  have htime := Infra.Ingredients.tau_bounds hβ hβ' hΛ hM
  have htimeLo : (2 : ℝ) ^ (-33 : ℤ) * ep ^ s ≤ tau β Λ M := by
    simpa [ep, s, show M - 1 + 1 = M by omega] using htime.1
  have hκτ : (1 / 2 : ℝ) * e ^ p *
      ((2 : ℝ) ^ (-33 : ℤ) * ep ^ s) ≤ κ * tau β Λ M :=
    mul_le_mul hperLo htimeLo (by positivity) hκ.le
  have hdenLo : 0 < (1 / 2 : ℝ) * e ^ p *
      ((2 : ℝ) ^ (-33 : ℤ) * ep ^ s) := by positivity
  have hquot := div_le_div_of_nonneg_left (by positivity : 0 ≤ e ^ 2)
    hdenLo hκτ
  have hdenEq :
      ((1 / 2 : ℝ) * e ^ p) * ((2 : ℝ) ^ (-33 : ℤ) * ep ^ s) =
        ((1 / 2 : ℝ) * (2 : ℝ) ^ (-33 : ℤ)) * (e ^ p * ep ^ s) := by ring
  have hE : 0 < e ^ p := Real.rpow_pos_of_pos he _
  have hF : 0 < ep ^ s := Real.rpow_pos_of_pos hep _
  have hnormalize : e ^ 2 /
      (((1 / 2 : ℝ) * (2 : ℝ) ^ (-33 : ℤ)) * (e ^ p * ep ^ s)) =
        (2 : ℝ) ^ (34 : ℕ) * (e ^ θ / ep ^ s) := by
    have hpow : e ^ 2 = e ^ p * e ^ θ := by
      have hnat : e ^ (2 : ℕ) = e ^ (2 : ℝ) := (Real.rpow_natCast e 2).symm
      rw [hnat]
      have hexp : (2 : ℝ) = p + θ := by dsimp [p, θ]; ring
      rw [hexp, Real.rpow_add he]
    field_simp [ne_of_gt hE, ne_of_gt hF]
    rw [hpow]
  have hquot' : e ^ 2 / (κ * tau β Λ M) ≤
      e ^ 2 /
        (((1 / 2 : ℝ) * (2 : ℝ) ^ (-33 : ℤ)) * (e ^ p * ep ^ s)) := by
    rw [hdenEq] at hquot
    exact hquot
  have hratioBase : e ^ 2 / (κ * tau β Λ M) ≤
      (2 : ℝ) ^ (34 : ℕ) * (e ^ θ / ep ^ s) := by
    calc
      e ^ 2 / (κ * tau β Λ M) ≤
          e ^ 2 /
            (((1 / 2 : ℝ) * (2 : ℝ) ^ (-33 : ℤ)) * (e ^ p * ep ^ s)) := hquot'
      _ = (2 : ℝ) ^ (34 : ℕ) * (e ^ θ / ep ^ s) := hnormalize
  have heScale : e ≤ A * ep ^ q β := by
    by_cases hM2 : 2 ≤ M
    · have hscale := Infra.Ingredients.epsilon_supergeo hβ hβ' hΛ
        (m := M - 1) (by omega : 1 ≤ M - 1)
      have hnext : M - 1 + 1 = M := by omega
      rw [hnext] at hscale
      have hepSmall : ep ≤ 1 / 128 := by
        dsimp [ep]
        have hε := Infra.Ingredients.epsilon_le_lambda_pow hβ hβ' hΛ
          (m := M - 1)
        have hΛ128 : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
        have hn : 1 ≤ M - 1 := by omega
        have hmReal : (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hn
        have hexp : -((M - 1 : ℕ) : ℝ) ≤ (-1 : ℝ) := by linarith
        have hΛone : (1 : ℝ) ≤ (Λ : ℝ) := by
          exact_mod_cast (show 1 ≤ Λ by omega)
        have hpow : (Λ : ℝ) ^ (-((M - 1 : ℕ) : ℝ)) ≤
            (Λ : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hΛone hexp
        have hinv : (Λ : ℝ) ^ (-1 : ℝ) ≤ (128 : ℝ) ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one, Real.rpow_neg_one]
          simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hΛ128
        have hle := hε.trans (hpow.trans hinv)
        have h128 : (128 : ℝ) ^ (-1 : ℝ) = 1 / 128 := by norm_num
        exact hle.trans_eq h128
      have hfactor : 1 + Infra.Ingredients.supergeoConstant β * ep ≤ A := by
        dsimp [A]
        linarith only [mul_le_mul_of_nonneg_left hepSmall hS]
      have hsuper := hscale.2
      dsimp [e, ep]
      calc
        epsilon β Λ M ≤
            (1 + Infra.Ingredients.supergeoConstant β *
              epsilon β Λ (M - 1)) * epsilon β Λ (M - 1) ^ q β := hsuper
        _ ≤ A * epsilon β Λ (M - 1) ^ q β :=
          mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hep.le _)
    · have hM1 : M = 1 := by omega
      subst M
      have heOne' : epsilon β Λ 1 ≤ 1 :=
        Infra.Construction.epsilon_le_one hβ hβ' hΛ
      have hep0 : epsilon β Λ (1 - 1) = 1 := by simp [epsilon]
      have hep0' : ep = 1 := by simpa [ep] using hep0
      rw [hep0']
      simpa [e, Real.one_rpow] using le_trans heOne' hA
  have hpowA : e ^ θ ≤ A ^ θ * ep ^ (q β * θ) := by
    have hpowMon := Real.rpow_le_rpow he.le heScale htheta.le
    have hmul : (A * ep ^ q β) ^ θ = A ^ θ * ep ^ (q β * θ) := by
      rw [Real.mul_rpow hApos.le (Real.rpow_nonneg hep.le _), Real.rpow_mul hep.le]
    simpa [hmul] using hpowMon
  have hgap := LRecurseTop.top_exponent_gap hβ hβ'
  have hepPow : ep ^ (q β * θ) / ep ^ s ≤ ep ^ (2 * delta β) := by
    have hdiv : ep ^ (q β * θ) / ep ^ s = ep ^ (q β * θ - s) := by
      rw [← Real.rpow_sub hep]
    rw [hdiv]
    exact Real.rpow_le_rpow_of_exponent_ge hep hepOne hgap
  have hscaleStep1 :
      (2 : ℝ) ^ (34 : ℕ) * (e ^ θ / ep ^ s) ≤
        (2 : ℝ) ^ (34 : ℕ) *
          (A ^ θ * ep ^ (q β * θ) / ep ^ s) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact div_le_div_of_nonneg_right hpowA (Real.rpow_nonneg hep.le _)
  have hAterm : 0 ≤ A ^ θ := Real.rpow_nonneg hApos.le _
  have hscaleStep2 : A ^ θ * ep ^ (q β * θ) / ep ^ s ≤
      A ^ θ * ep ^ (2 * delta β) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hepPow hAterm
  have hscaleStep3 :
      (2 : ℝ) ^ (34 : ℕ) *
          (A ^ θ * ep ^ (q β * θ) / ep ^ s) ≤
        kappaPrimeEndpointExpratConstant β * ep ^ (2 * delta β) := by
    calc
      (2 : ℝ) ^ (34 : ℕ) *
          (A ^ θ * ep ^ (q β * θ) / ep ^ s) ≤
          (2 : ℝ) ^ (34 : ℕ) * (A ^ θ * ep ^ (2 * delta β)) :=
        mul_le_mul_of_nonneg_left hscaleStep2 (by positivity)
      _ = kappaPrimeEndpointExpratConstant β * ep ^ (2 * delta β) := by
        simp [kappaPrimeEndpointExpratConstant, A, θ, mul_assoc]
  have hexprat := hratioBase.trans (hscaleStep1.trans hscaleStep3)
  exact ⟨by simpa [e] using hlower, by simpa [e, ep] using hexprat⟩

end AVenhance.Infra.Section3

end
