/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaPrimeExprat
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.OneStepAveragingUnconditional
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaPrimeComparison
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.EpsilonConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleBounds

/-! Bootstrap estimates comparing the diffusivity recursion with κ′.

The top endpoint is treated directly from the permitted interval.  Interior
steps use the corrected κ′ exprat estimate and the unconditional averaging
bound. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

/-- The top permitted value also has a small exprat ratio, with the `2δ` exponent. -/
def kappaPrimeEndpointExpratConstant (β : ℝ) : ℝ :=
  2 ^ (34 : ℕ) *
    (1 + Infra.Ingredients.supergeoConstant β / 128) ^ (2 - β + gamma β)

theorem KappaAtPrimeBootstrap.endpoint_exponent_gap {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) :
    2 * delta β ≤ q β * (2 - β + gamma β) - (2 - β + 4 * delta β) := by
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
      (4 * (r + 1) * (4 * r - 1)) := by
    rw [Infra.Ingredients.delta_eq_q_fraction hβ hβ']
  have hidentity :
      q β * (2 - β + gamma β) - (2 - β + 4 * delta β) - 2 * delta β =
        (r - 1) * (32 * r ^ 2 + 2 * r - 2) /
          (4 * (r + 1) * (4 * r - 1)) := by
    rw [show q β = r by rfl, hγr, hδr, hβr]
    field_simp [ne_of_gt hden, ne_of_gt hden',
      show r * 4 - 1 ≠ 0 by nlinarith]
    ring_nf
  have hpoly : 0 < 32 * r ^ 2 + 2 * r - 2 := by
    nlinarith [sq_nonneg r]
  have hnonneg : 0 ≤
      (r - 1) * (32 * r ^ 2 + 2 * r - 2) /
        (4 * (r + 1) * (4 * r - 1)) := by
    positivity
  linarith [hidentity, hnonneg]

/-- The terminal ratio `ε_M²/(κ τ_M)` is controlled directly by the
permitted interval and the `M−1` time scale, with the one-sided exponent
`2δ`. -/
theorem kappaPrimeAt_terminal_exprat_upper {β : ℝ} {Λ M : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpermitted : κ ∈ permittedInterval β Λ M) (hM : 2 ≤ M) :
    epsilon β Λ M ^ 2 / (κ * tau β Λ M) ≤
      kappaPrimeEndpointExpratConstant β *
        epsilon β Λ (M - 1) ^ (2 * delta β) := by
  let e := epsilon β Λ M
  let ep := epsilon β Λ (M - 1)
  let p := 2 - β + gamma β
  let A := 1 + Infra.Ingredients.supergeoConstant β / 128
  have he : 0 < e := by dsimp [e]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hep : 0 < ep := by dsimp [ep]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hepSmall : ep ≤ 1 / 128 := by
    dsimp [ep]
    have hε := Infra.Ingredients.epsilon_le_lambda_pow hβ hβ' hΛ
      (m := M - 1)
    have hΛ : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
    have hn : 1 ≤ M - 1 := by omega
    have hmReal : (1 : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hn
    have hexp : -((M - 1 : ℕ) : ℝ) ≤ (-1 : ℝ) := by linarith
    have hΛone : (1 : ℝ) ≤ (Λ : ℝ) := by
      exact_mod_cast (show 1 ≤ Λ by omega)
    have hpow : (Λ : ℝ) ^ (-((M - 1 : ℕ) : ℝ)) ≤ (Λ : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hΛone hexp
    have hinv : (Λ : ℝ) ^ (-1 : ℝ) ≤ (128 : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, Real.rpow_neg_one]
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hΛ
    have hle := hε.trans (hpow.trans hinv)
    have h128 : (128 : ℝ) ^ (-1 : ℝ) = 1 / 128 := by norm_num
    exact hle.trans_eq h128
  have hp : 0 < p := by
    dsimp [p]
    have hγ := Infra.Ingredients.gamma_pos hβ hβ'
    linarith
  have hscale := Infra.Ingredients.epsilon_supergeo hβ hβ' hΛ
    (m := M - 1) (by omega : 1 ≤ M - 1)
  have heScale : e ≤ A * ep ^ q β := by
    have hnext : M - 1 + 1 = M := by omega
    rw [hnext] at hscale
    have hS : 0 ≤ Infra.Ingredients.supergeoConstant β := by
      dsimp [Infra.Ingredients.supergeoConstant]
      have hq : 0 < q β := lt_trans (by norm_num) (Infra.Ingredients.one_lt_q hβ hβ')
      positivity
    have hfactor : 1 + Infra.Ingredients.supergeoConstant β * ep ≤ A := by
      dsimp [A]
      nlinarith [mul_le_mul_of_nonneg_left hepSmall hS]
    dsimp [e, ep]
    calc
      epsilon β Λ M ≤
          (1 + Infra.Ingredients.supergeoConstant β *
            epsilon β Λ (M - 1)) *
              epsilon β Λ (M - 1) ^ q β := hscale.2
      _ ≤ A * epsilon β Λ (M - 1) ^ q β :=
        mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hep.le _)
  have htime := Infra.Ingredients.tau_bounds hβ hβ' hΛ
    (by omega : 1 ≤ M)
  have htimeLo : (2 : ℝ) ^ (-33 : ℤ) * ep ^
      (2 - β + 4 * delta β) ≤ tau β Λ M := by
    simpa [ep, show M - 1 + 1 = M by omega] using htime.1
  have hbetaExp : 2 * β / (q β + 1) = β - gamma β := by
    unfold gamma
    field_simp [ne_of_gt (by linarith [Infra.Ingredients.one_lt_q hβ hβ'] : 0 < q β + 1)]
    ring
  have hperLo : (1 / 2 : ℝ) * e ^ (β - gamma β) ≤ κ := by
    have hper := Set.mem_Icc.mp hpermitted
    have h := hper.1
    simpa [e, permittedInterval, hbetaExp] using h
  have hκbound : (1 / 2 : ℝ) * e ^ (β - gamma β) ≤ κ := hperLo
  have hratioBase :
      e ^ 2 / (κ * tau β Λ M) ≤
        (2 : ℝ) ^ (34 : ℕ) *
          (e ^ p / ep ^ (2 - β + 4 * delta β)) := by
    have hκτ : (1 / 2 : ℝ) * e ^ (β - gamma β) *
        ((2 : ℝ) ^ (-33 : ℤ) * ep ^ (2 - β + 4 * delta β)) ≤
        κ * tau β Λ M :=
      mul_le_mul hκbound htimeLo (by positivity) hκ.le
    have hnum : 0 ≤ e ^ 2 := by positivity
    have hdenLo : 0 <
        (1 / 2 : ℝ) * e ^ (β - gamma β) *
          ((2 : ℝ) ^ (-33 : ℤ) * ep ^ (2 - β + 4 * delta β)) := by
      positivity
    have hquot := div_le_div_of_nonneg_left hnum hdenLo hκτ
    have hpow : e ^ (2 : ℕ) / e ^ (β - gamma β) = e ^ p := by
      have hnat : e ^ (2 : ℕ) = e ^ (2 : ℝ) := (Real.rpow_natCast e 2).symm
      rw [hnat, ← Real.rpow_sub he]
      congr 1
      dsimp [p]
      ring
    have hdenEq :
        ((1 / 2 : ℝ) * e ^ (β - gamma β)) *
            ((2 : ℝ) ^ (-33 : ℤ) * ep ^ (2 - β + 4 * delta β)) =
          ((1 / 2 : ℝ) * (2 : ℝ) ^ (-33 : ℤ)) *
            (e ^ (β - gamma β) * ep ^ (2 - β + 4 * delta β)) := by ring
    have hE : 0 < e ^ (β - gamma β) := Real.rpow_pos_of_pos he _
    have hF : 0 < ep ^ (2 - β + 4 * delta β) := Real.rpow_pos_of_pos hep _
    have hnormalize : e ^ 2 /
        (((1 / 2 : ℝ) * (2 : ℝ) ^ (-33 : ℤ)) *
          (e ^ (β - gamma β) * ep ^ (2 - β + 4 * delta β))) =
        (2 : ℝ) ^ (34 : ℕ) *
          (e ^ 2 / e ^ (β - gamma β)) /
            ep ^ (2 - β + 4 * delta β) := by
      field_simp [ne_of_gt hE, ne_of_gt hF]
    have hquot' : e ^ 2 / (κ * tau β Λ M) ≤
        e ^ 2 /
          (((1 / 2 : ℝ) * (2 : ℝ) ^ (-33 : ℤ)) *
            (e ^ (β - gamma β) * ep ^ (2 - β + 4 * delta β))) := by
      rw [hdenEq] at hquot
      exact hquot
    calc
      e ^ 2 / (κ * tau β Λ M) ≤
          e ^ 2 /
            (((1 / 2 : ℝ) * (2 : ℝ) ^ (-33 : ℤ)) *
              (e ^ (β - gamma β) * ep ^ (2 - β + 4 * delta β))) := hquot'
      _ = (2 : ℝ) ^ (34 : ℕ) *
          (e ^ 2 / e ^ (β - gamma β)) /
            ep ^ (2 - β + 4 * delta β) := hnormalize
      _ = (2 : ℝ) ^ (34 : ℕ) *
          ((e ^ 2 / e ^ (β - gamma β)) /
            ep ^ (2 - β + 4 * delta β)) := by ring
      _ = (2 : ℝ) ^ (34 : ℕ) *
          (e ^ p / ep ^ (2 - β + 4 * delta β)) := by
        rw [hpow]
  have hApos : 0 < A := by
    have hq : 0 < q β := lt_trans (by norm_num) (Infra.Ingredients.one_lt_q hβ hβ')
    have hS : 0 ≤ Infra.Ingredients.supergeoConstant β := by
      dsimp [Infra.Ingredients.supergeoConstant]
      positivity
    dsimp [A]
    positivity
  have hpowA : e ^ p ≤ A ^ p * ep ^ (q β * p) := by
    have hpowMon := Real.rpow_le_rpow he.le heScale hp.le
    have hmul : (A * ep ^ q β) ^ p = A ^ p * ep ^ (q β * p) := by
      rw [Real.mul_rpow hApos.le (Real.rpow_nonneg hep.le _), Real.rpow_mul hep.le]
    simpa [hmul] using hpowMon
  have hgap := KappaAtPrimeBootstrap.endpoint_exponent_gap hβ hβ'
  have hepPow : ep ^ (q β * p) / ep ^ (2 - β + 4 * delta β) ≤
      ep ^ (2 * delta β) := by
    have hdiv : ep ^ (q β * p) / ep ^ (2 - β + 4 * delta β) =
        ep ^ (q β * p - (2 - β + 4 * delta β)) := by
      rw [← Real.rpow_sub hep]
    have hepOne : ep ≤ 1 := le_trans hepSmall (by norm_num)
    rw [hdiv]
    exact Real.rpow_le_rpow_of_exponent_ge hep hepOne hgap
  have hscaleStep1 :
      (2 : ℝ) ^ (34 : ℕ) *
          (e ^ p / ep ^ (2 - β + 4 * delta β)) ≤
        (2 : ℝ) ^ (34 : ℕ) *
          (A ^ p * ep ^ (q β * p) /
            ep ^ (2 - β + 4 * delta β)) :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hpowA (Real.rpow_nonneg hep.le _))
      (by positivity)
  have hAterm : 0 ≤ A ^ p := Real.rpow_nonneg hApos.le _
  have hscaleStep2Local : A ^ p * ep ^ (q β * p) /
      ep ^ (2 - β + 4 * delta β) ≤ A ^ p * ep ^ (2 * delta β) := by
    calc
      A ^ p * ep ^ (q β * p) / ep ^ (2 - β + 4 * delta β) =
          A ^ p * (ep ^ (q β * p) / ep ^ (2 - β + 4 * delta β)) := by
            rw [mul_div_assoc]
      _ ≤ A ^ p * ep ^ (2 * delta β) := mul_le_mul_of_nonneg_left hepPow hAterm
  have hscaleStep2 :
      (2 : ℝ) ^ (34 : ℕ) *
          (A ^ p * ep ^ (q β * p) /
            ep ^ (2 - β + 4 * delta β)) ≤
        (2 : ℝ) ^ (34 : ℕ) * (A ^ p * ep ^ (2 * delta β)) :=
    mul_le_mul_of_nonneg_left hscaleStep2Local (by positivity)
  have hresult : e ^ 2 / (κ * tau β Λ M) ≤
      (2 : ℝ) ^ (34 : ℕ) * (A ^ p * ep ^ (2 * delta β)) :=
    hratioBase.trans (hscaleStep1.trans hscaleStep2)
  simpa [e, ep, kappaPrimeEndpointExpratConstant, A, p, mul_assoc] using hresult

/-- The uniform upper constant for the interior κ′ exprat estimate. -/
def kappaPrimeExpratUpperConstant (β : ℝ) : ℝ :=
  (1 + Infra.Ingredients.supergeoConstant β / 128) ^
      (2 - β - gamma β) /
    ((9 / 80 / kappaPrimeUniformConstant β) * (2 : ℝ) ^ (-33 : ℤ))

/-- One constant covers the interior κ′ exprat estimate and the direct
permitted-interval estimate at its terminal scale. -/
def kappaPrimeExpratGlobalUpperConstant (β : ℝ) : ℝ :=
  max (kappaPrimeExpratUpperConstant β)
    (kappaPrimeEndpointExpratConstant β)

theorem kappaPrimeExpratUpperConstant_pos {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 < kappaPrimeExpratUpperConstant β := by
  have hU : 0 < kappaPrimeUniformConstant β :=
    kappaPrimeUniformConstant_pos hβ hβ'
  have hbase : 0 < 1 + Infra.Ingredients.supergeoConstant β / 128 := by
    have hq : 0 < q β := lt_trans (by norm_num) (Infra.Ingredients.one_lt_q hβ hβ')
    dsimp [Infra.Ingredients.supergeoConstant]
    positivity
  unfold kappaPrimeExpratUpperConstant
  exact div_pos (Real.rpow_pos_of_pos hbase _)
    (mul_pos (div_pos (by norm_num) hU) (zpow_pos (by norm_num) _))

theorem KappaAtPrimeBootstrap.kappaPrimeExpratGlobalUpperConstant_pos {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 < kappaPrimeExpratGlobalUpperConstant β := by
  have hinner : 0 < kappaPrimeExpratUpperConstant β :=
    kappaPrimeExpratUpperConstant_pos hβ hβ'
  have hend : 0 < kappaPrimeEndpointExpratConstant β := by
    have hq : 0 < q β := lt_trans (by norm_num) (Infra.Ingredients.one_lt_q hβ hβ')
    have hS : 0 ≤ Infra.Ingredients.supergeoConstant β := by
      dsimp [Infra.Ingredients.supergeoConstant]
      positivity
    have hbase : 0 < 1 + Infra.Ingredients.supergeoConstant β / 128 := by positivity
    unfold kappaPrimeEndpointExpratConstant
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos hbase _)
  unfold kappaPrimeExpratGlobalUpperConstant
  exact lt_of_lt_of_le hinner (le_max_left _ _)

/-- The κ′ exprat ratio, including the terminal scale, is bounded by one
β-only constant times `ε_{m−1}^δ`. -/
theorem kappaPrimeAt_exprat_global_upper {β : ℝ} {Λ M : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpermitted : κ ∈ permittedInterval β Λ M)
    {m : ℕ} (hm : 2 ≤ m) (hmM : m ≤ M) :
    epsilon β Λ m ^ 2 /
        (kappaPrimeAt β Λ κ m (M - m) * tau β Λ m) ≤
      kappaPrimeExpratGlobalUpperConstant β *
        epsilon β Λ (m - 1) ^ delta β := by
  by_cases hlt : m < M
  · have hbase := (kappaPrimeAt_exprat_bounds hβ hβ' hΛ hκ hpermitted hm hlt).2
    have heprev : 0 < epsilon β Λ (m - 1) :=
      Infra.Cutoff.epsilon_pos hβ hβ' hΛ
    have heprevOne : epsilon β Λ (m - 1) ≤ 1 :=
      Infra.Construction.epsilon_le_one hβ hβ' hΛ
    have hδ := Infra.Ingredients.delta_pos hβ hβ'
    have hpow : epsilon β Λ (m - 1) ^ (4 * delta β) ≤
        epsilon β Λ (m - 1) ^ delta β :=
      Real.rpow_le_rpow_of_exponent_ge heprev heprevOne (by nlinarith)
    have hchi :
        (let U := kappaPrimeUniformConstant β
         let chi := (1 + Infra.Ingredients.supergeoConstant β / 128) ^
            (2 - β - gamma β) /
          ((9 / 80 / U) * (2 : ℝ) ^ (-33 : ℤ));
         epsilon β Λ m ^ 2 /
           (kappaPrimeAt β Λ κ m (M - m) * tau β Λ m) ≤
             chi * epsilon β Λ (m - 1) ^ (4 * delta β)) := hbase
    dsimp only at hchi
    have hχeq : (1 + Infra.Ingredients.supergeoConstant β / 128) ^
        (2 - β - gamma β) /
        ((9 / 80 / kappaPrimeUniformConstant β) * (2 : ℝ) ^ (-33 : ℤ)) =
          kappaPrimeExpratUpperConstant β := rfl
    have hchi' :
        epsilon β Λ m ^ 2 /
          (kappaPrimeAt β Λ κ m (M - m) * tau β Λ m) ≤
        kappaPrimeExpratUpperConstant β *
          epsilon β Λ (m - 1) ^ (4 * delta β) := by
      simpa [kappaPrimeExpratUpperConstant] using hchi
    calc
      epsilon β Λ m ^ 2 /
          (kappaPrimeAt β Λ κ m (M - m) * tau β Λ m) ≤
        kappaPrimeExpratUpperConstant β *
          epsilon β Λ (m - 1) ^ (4 * delta β) := hchi'
      _ ≤ kappaPrimeExpratUpperConstant β *
          epsilon β Λ (m - 1) ^ delta β :=
            mul_le_mul_of_nonneg_left hpow
              (le_of_lt (kappaPrimeExpratUpperConstant_pos hβ hβ'))
      _ ≤ kappaPrimeExpratGlobalUpperConstant β *
          epsilon β Λ (m - 1) ^ delta β := by
            exact mul_le_mul_of_nonneg_right
              (le_max_left _ _) (Real.rpow_nonneg (le_of_lt heprev) _)
  · have hEq : m = M := by omega
    subst M
    have hterminal := kappaPrimeAt_terminal_exprat_upper hβ hβ' hΛ hκ hpermitted
      (by omega : 2 ≤ m)
    have hterminal' : epsilon β Λ m ^ 2 /
        (kappaPrimeAt β Λ κ m (m - m) * tau β Λ m) ≤
          kappaPrimeEndpointExpratConstant β *
            epsilon β Λ (m - 1) ^ (2 * delta β) := by
      simpa [kappaPrimeAt] using hterminal
    have heprev : 0 < epsilon β Λ (m - 1) :=
      Infra.Cutoff.epsilon_pos hβ hβ' hΛ
    have heprevOne : epsilon β Λ (m - 1) ≤ 1 :=
      Infra.Construction.epsilon_le_one hβ hβ' hΛ
    have hδ := Infra.Ingredients.delta_pos hβ hβ'
    have hpow : epsilon β Λ (m - 1) ^ (2 * delta β) ≤
        epsilon β Λ (m - 1) ^ delta β :=
      Real.rpow_le_rpow_of_exponent_ge heprev heprevOne (by nlinarith)
    have hconst : 0 ≤ kappaPrimeEndpointExpratConstant β := by
      have hq : 0 < q β := lt_trans (by norm_num) (Infra.Ingredients.one_lt_q hβ hβ')
      have hS : 0 ≤ Infra.Ingredients.supergeoConstant β := by
        dsimp [Infra.Ingredients.supergeoConstant]
        positivity
      have hbase : 0 < 1 + Infra.Ingredients.supergeoConstant β / 128 := by
        positivity
      unfold kappaPrimeEndpointExpratConstant
      exact mul_nonneg (by positivity) (Real.rpow_nonneg hbase.le _)
    calc
      epsilon β Λ m ^ 2 /
          (kappaPrimeAt β Λ κ m (m - m) * tau β Λ m) ≤
          kappaPrimeEndpointExpratConstant β *
            epsilon β Λ (m - 1) ^ (2 * delta β) := hterminal'
      _ ≤ kappaPrimeEndpointExpratConstant β *
          epsilon β Λ (m - 1) ^ delta β :=
        mul_le_mul_of_nonneg_left hpow hconst
      _ ≤ kappaPrimeExpratGlobalUpperConstant β *
          epsilon β Λ (m - 1) ^ delta β :=
        mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (le_of_lt (Infra.Cutoff.epsilon_pos hβ hβ' hΛ)) _)

/-- The elementary coarse comparison for one enhancement step.  It is used
only when the finite-scale ratio is too large for the averaging estimate. -/
theorem KappaAtPrimeBootstrap.coarse_recurrence_ratio_step {u v B D w R : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hB : 0 < B)
    (hD : D = (40 / 9 : ℝ) * B)
    (hcurrent : max (u / v) (v / u) ≤ R)
    (hlo : u ≤ w) (hhi : w ≤ u + D / u) :
    max (w / (v + B / v)) ((v + B / v) / w) ≤
      R * (1 + (40 / 9 : ℝ) * (B / v ^ 2)) := by
  have hw : 0 < w := lt_of_lt_of_le hu hlo
  have hy : 0 < v + B / v := by positivity
  have hratioPos : 0 < u / v := div_pos hu hv
  have hratioInvPos : 0 < v / u := div_pos hv hu
  have hratioLo : u / v ≤ max (u / v) (v / u) := le_max_left _ _
  have hratioInvLo : v / u ≤ max (u / v) (v / u) := le_max_right _ _
  have hratio : 0 ≤ max (u / v) (v / u) := le_trans hratioPos.le hratioLo
  have ht : 0 ≤ B / v ^ 2 := by positivity
  have hDpos : 0 ≤ D := by rw [hD]; positivity
  have hupper : w / (v + B / v) ≤
      max (u / v) (v / u) * (1 + (40 / 9 : ℝ) * (B / v ^ 2)) := by
    have hxupper : w / (v + B / v) ≤ (u + D / u) / v := by
      have hyv : v ≤ v + B / v := le_add_of_nonneg_right (by positivity)
      calc
        w / (v + B / v) ≤ w / v :=
          div_le_div_of_nonneg_left hw.le hv hyv
        _ ≤ (u + D / u) / v := div_le_div_of_nonneg_right hhi hv.le
    have hbound : (u + D / u) / v ≤
        max (u / v) (v / u) * (1 + (40 / 9 : ℝ) * (B / v ^ 2)) := by
      rw [hD]
      have hmul : (40 / 9 : ℝ) * (B / (u * v)) =
          (40 / 9 : ℝ) * (B / v ^ 2) * (v / u) := by
        field_simp [ne_of_gt hu, ne_of_gt hv]
      have heq : (u + ((40 / 9 : ℝ) * B) / u) / v =
          u / v + (40 / 9 : ℝ) * (B / (u * v)) := by
        field_simp [ne_of_gt hu, ne_of_gt hv]
      rw [heq, hmul]
      calc
        u / v + (40 / 9 : ℝ) * (B / v ^ 2) * (v / u) ≤
            max (u / v) (v / u) +
              (40 / 9 : ℝ) * (B / v ^ 2) * max (u / v) (v / u) := by
                exact add_le_add hratioLo
                  (mul_le_mul_of_nonneg_left hratioInvLo (by positivity))
        _ = max (u / v) (v / u) *
            (1 + (40 / 9 : ℝ) * (B / v ^ 2)) := by ring
    exact hxupper.trans hbound
  have hlower : (v + B / v) / w ≤
      max (u / v) (v / u) * (1 + (40 / 9 : ℝ) * (B / v ^ 2)) := by
    have hxy : (v + B / v) / w ≤ (v + B / v) / u :=
      div_le_div_of_nonneg_left (by positivity) hu hlo
    have heq : (v + B / v) / u = v / u + (B / v ^ 2) * (v / u) := by
      field_simp [ne_of_gt hu, ne_of_gt hv]
    calc
      (v + B / v) / w ≤ (v + B / v) / u := hxy
      _ = v / u + (B / v ^ 2) * (v / u) := heq
      _ ≤
          max (u / v) (v / u) +
            (40 / 9 : ℝ) * (B / v ^ 2) * max (u / v) (v / u) := by
              have hmul : (B / v ^ 2) * (v / u) ≤
                  (40 / 9 : ℝ) * (B / v ^ 2) * max (u / v) (v / u) := by
                have hcoef : 1 ≤ (40 / 9 : ℝ) := by norm_num
                calc
                  (B / v ^ 2) * (v / u) ≤
                      (B / v ^ 2) * max (u / v) (v / u) :=
                    mul_le_mul_of_nonneg_left hratioInvLo ht
                  _ ≤ (40 / 9 : ℝ) * (B / v ^ 2) *
                      max (u / v) (v / u) := by
                    rw [mul_assoc]
                    exact le_mul_of_one_le_left (mul_nonneg ht hratio) hcoef
              exact add_le_add hratioInvLo hmul
      _ = max (u / v) (v / u) *
          (1 + (40 / 9 : ℝ) * (B / v ^ 2)) := by ring
  exact (max_le_iff.mpr ⟨hupper, hlower⟩).trans
    (mul_le_mul_of_nonneg_right hcurrent (by positivity))

/-- The scale error is dominated by a fixed geometric sequence. -/
theorem epsilon_delta_le_geometric {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (n : ℕ) :
    epsilon β Λ n ^ delta β ≤ ((128 : ℝ) ^ (-delta β)) ^ n := by
  have hε := Infra.Ingredients.epsilon_le_lambda_pow hβ hβ' hΛ (m := n)
  have hΛ128 : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  have hexp : -(n : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg n)
  have hbase : (Λ : ℝ) ^ (-(n : ℝ)) ≤ (128 : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hΛ128 hexp
  have hεδ : 0 < delta β := Infra.Ingredients.delta_pos hβ hβ'
  have heps : 0 < epsilon β Λ n :=
    Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hpower := Real.rpow_le_rpow heps.le (hε.trans hbase) hεδ.le
  have hrewrite : ((128 : ℝ) ^ (-(n : ℝ))) ^ delta β =
      ((128 : ℝ) ^ (-delta β)) ^ n := by
    calc
      ((128 : ℝ) ^ (-(n : ℝ))) ^ delta β =
          (128 : ℝ) ^ ((-(n : ℝ)) * delta β) :=
        (Real.rpow_mul (by norm_num) (-(n : ℝ)) (delta β)).symm
      _ = (128 : ℝ) ^ ((-delta β) * (n : ℝ)) := by congr 1; ring
      _ = ((128 : ℝ) ^ (-delta β)) ^ (n : ℝ) :=
        Real.rpow_mul (by norm_num) (-delta β) (n : ℝ)
      _ = ((128 : ℝ) ^ (-delta β)) ^ n := by rw [Real.rpow_natCast]
  exact hpower.trans_eq hrewrite

/-- The geometric tail used to keep all high-scale recurrence comparisons
inside the factor-two bootstrap. -/
def kappaAtBootstrapTail (β E : ℝ) (n : ℕ) : ℝ :=
  E * ((128 : ℝ) ^ (-delta β)) ^ n /
    (1 - (128 : ℝ) ^ (-delta β))

/-- One recurrence step splits off the first term of the geometric tail. -/
theorem kappaAtBootstrapTail_succ {β E : ℝ} (n : ℕ)
    (hden : 1 - (128 : ℝ) ^ (-delta β) ≠ 0) :
    kappaAtBootstrapTail β E n =
      E * ((128 : ℝ) ^ (-delta β)) ^ n +
        kappaAtBootstrapTail β E (n + 1) := by
  unfold kappaAtBootstrapTail
  rw [pow_succ]
  field_simp [hden]
  ring

/-- A finite cutoff can make the high-scale geometric tail as small as needed. -/
theorem exists_kappaAtBootstrap_cutoff {β E : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hE : 0 < E) :
    ∃ N : ℕ, 1 ≤ N ∧
      kappaAtBootstrapTail β E N ≤ 1 / 2 := by
  let r := (128 : ℝ) ^ (-delta β)
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ hβ'
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by linarith)
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < (1 - r) / (2 * E) by positivity) hr1
  refine ⟨n + 1, by omega, ?_⟩
  have hrle : r ≤ 1 := hr1.le
  have hpow : r ^ (n + 1) ≤ r ^ n := by
    rw [pow_succ]
    calc
      r ^ n * r ≤ r ^ n * 1 := mul_le_mul_of_nonneg_left hrle (pow_nonneg hr0.le n)
      _ = r ^ n := mul_one _
  have hmul : E * r ^ n < (1 - r) / 2 := by
    calc
      E * r ^ n < E * ((1 - r) / (2 * E)) :=
        mul_lt_mul_of_pos_left hn hE
      _ = (1 - r) / 2 := by field_simp [ne_of_gt hE]
  have hmul' : E * r ^ (n + 1) ≤ (1 - r) / 2 := by
    calc
      E * r ^ (n + 1) ≤ E * r ^ n := mul_le_mul_of_nonneg_left hpow hE.le
      _ ≤ (1 - r) / 2 := hmul.le
  have hfinal : E * r ^ (n + 1) / (1 - r) ≤ 1 / 2 :=
    (div_le_iff₀ hden).2 (by linarith only [hmul'])
  simpa [kappaAtBootstrapTail, r] using hfinal

/-- The one-step error coefficient when the current actual/prime ratio is
bounded by `R`. -/
def kappaAtBootstrapErrorCoefficient (β C₀ R : ℝ) : ℝ :=
  (80 / 9) * lAmtOneStepConstant β C₀ *
    (R * kappaPrimeExpratGlobalUpperConstant β + 1)

/-- A bad-step threshold determined by the current comparison bound. -/
def KappaAtPrimeBootstrap.kappaAtBootstrapThreshold (β C₀ R : ℝ) : ℝ :=
  1 / (2 * kappaAtBootstrapErrorCoefficient β C₀ R)

/-- A lower bound for the next epsilon scale whenever a step is too coarse for
the relative averaging estimate. -/
def KappaAtPrimeBootstrap.kappaAtBootstrapBadEpsilonFloor (β C₀ R : ℝ) : ℝ :=
  (1 / 2) *
    KappaAtPrimeBootstrap.kappaAtBootstrapThreshold β C₀ R ^ (q β / delta β)

/-- The prime increment ratio is uniformly bounded on a bad low-scale step. -/
def KappaAtPrimeBootstrap.kappaAtBootstrapBadIncrementCap (β C₀ R : ℝ) : ℝ :=
  max (9 / 20 : ℝ)
    ((80 / 9) * kappaPrimeUniformConstant β ^ 2 *
      KappaAtPrimeBootstrap.kappaAtBootstrapBadEpsilonFloor β C₀ R ^ (-2 * gamma β))

/-- The worst multiplicative loss of one low-scale step at ratio bound `R`. -/
def kappaAtBootstrapStepFactor (β C₀ R : ℝ) : ℝ :=
  max 2 (1 + (40 / 9 : ℝ) *
    KappaAtPrimeBootstrap.kappaAtBootstrapBadIncrementCap β C₀ R)

/-- Finite iteration of the coarse low-scale step factors. -/
def kappaAtBootstrapIteratedBound (β C₀ : ℝ) : ℕ → ℝ
  | 0 => 2
  | n + 1 => kappaAtBootstrapIteratedBound β C₀ n *
      kappaAtBootstrapStepFactor β C₀ (kappaAtBootstrapIteratedBound β C₀ n)

theorem kappaAtBootstrapErrorCoefficient_pos {β C₀ R : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hC₀ : 0 ≤ C₀) (hR : 1 ≤ R) :
    0 < kappaAtBootstrapErrorCoefficient β C₀ R := by
  have hL : 0 < lAmtOneStepConstant β C₀ := by
    unfold lAmtOneStepConstant
    have hN : 0 ≤ (Nstar β : ℝ) := by positivity
    have hfac : 0 ≤ (Nstar β).factorial := by positivity
    positivity
  have hQ : 0 < kappaPrimeExpratGlobalUpperConstant β :=
    KappaAtPrimeBootstrap.kappaPrimeExpratGlobalUpperConstant_pos hβ hβ'
  unfold kappaAtBootstrapErrorCoefficient
  positivity

theorem KappaAtPrimeBootstrap.kappaAtBootstrapThreshold_pos {β C₀ R : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hC₀ : 0 ≤ C₀) (hR : 1 ≤ R) :
    0 < KappaAtPrimeBootstrap.kappaAtBootstrapThreshold β C₀ R := by
  unfold KappaAtPrimeBootstrap.kappaAtBootstrapThreshold
  exact div_pos (by norm_num) (mul_pos (by norm_num)
    (kappaAtBootstrapErrorCoefficient_pos hβ hβ' hC₀ hR))

theorem KappaAtPrimeBootstrap.kappaAtBootstrapErrorCoefficient_ge_one {β C₀ R : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hC₀ : 0 ≤ C₀) (hR : 1 ≤ R) :
    1 ≤ kappaAtBootstrapErrorCoefficient β C₀ R := by
  have hL : 2 ≤ lAmtOneStepConstant β C₀ := by
    have hN : 0 ≤ (Nstar β : ℝ) := by positivity
    have hterm1 : 0 ≤ (Nstar β : ℝ) * C₀ := mul_nonneg hN hC₀
    have hterm2 : 0 ≤ 4 * Real.pi ^ 2 * C₀ * Nstar β *
        2 ^ Nstar β := by positivity
    have hterm3 : 0 ≤ 2 * Nstar β * C₀ * ((Nstar β).factorial : ℝ) *
        2 ^ Nstar β * 2 ^ Nstar β * C₀ ^ 2 * 8 ^ Nstar β := by positivity
    unfold lAmtOneStepConstant
    linarith
  have hQ : 0 < kappaPrimeExpratGlobalUpperConstant β :=
    KappaAtPrimeBootstrap.kappaPrimeExpratGlobalUpperConstant_pos hβ hβ'
  unfold kappaAtBootstrapErrorCoefficient
  have hterm : 1 ≤ R * kappaPrimeExpratGlobalUpperConstant β + 1 := by
    have hmul : 0 ≤ R * kappaPrimeExpratGlobalUpperConstant β := by positivity
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hL (by norm_num : (0 : ℝ) ≤ 80 / 9)]

theorem KappaAtPrimeBootstrap.kappaAtBootstrapStepFactor_ge_two {β C₀ R : ℝ} :
    2 ≤ kappaAtBootstrapStepFactor β C₀ R := by
  unfold kappaAtBootstrapStepFactor
  exact le_max_left _ _

theorem KappaAtPrimeBootstrap.epsilon_le_one_over_128_local {β : ℝ} {Λ n : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    (hn : 1 ≤ n) : epsilon β Λ n ≤ (1 / 128 : ℝ) := by
  have he := Infra.Ingredients.epsilon_le_lambda_pow hβ hβ' hΛ (m := n)
  have hΛ128 : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  have hexp : -(n : ℝ) ≤ -1 := by exact_mod_cast (show -(n : ℤ) ≤ -1 by omega)
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 128) hexp
  have hpow' : (Λ : ℝ) ^ (-(n : ℝ)) ≤ (128 : ℝ) ^ (-1 : ℝ) := by
    calc
      (Λ : ℝ) ^ (-(n : ℝ)) ≤ (128 : ℝ) ^ (-(n : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hΛ128
          (neg_nonpos.mpr (Nat.cast_nonneg n))
      _ ≤ (128 : ℝ) ^ (-1 : ℝ) := hpow
  have hinv : (128 : ℝ) ^ (-1 : ℝ) = 1 / 128 := by norm_num
  exact he.trans (hpow'.trans_eq hinv)

/-- Every exceptional low-scale step has a β- and `C₀`-uniform lower bound
on its next epsilon scale. -/
theorem KappaAtPrimeBootstrap.epsilon_next_lower_of_bad_threshold {β : ℝ} {Λ j : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    (hj : 2 ≤ j) {t : ℝ} (ht : 0 < t)
    (hbad : t < epsilon β Λ (j - 1) ^ delta β) :
    (1 / 2 : ℝ) * t ^ (q β / delta β) ≤ epsilon β Λ j := by
  let e := epsilon β Λ (j - 1)
  have he : 0 < e := by dsimp [e]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have heSmall : e ≤ 1 / 128 := by
    dsimp [e]
    exact KappaAtPrimeBootstrap.epsilon_le_one_over_128_local hβ hβ' hΛ (by omega)
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos hβ hβ'
  have hq : 0 < q β := lt_trans (by norm_num) (Infra.Ingredients.one_lt_q hβ hβ')
  have hexp : 0 < q β / delta β := div_pos hq hδ
  have hpow : t ^ (q β / delta β) ≤ (e ^ delta β) ^ (q β / delta β) :=
    Real.rpow_le_rpow ht.le hbad.le hexp.le
  have hpowEq : (e ^ delta β) ^ (q β / delta β) = e ^ q β := by
    rw [← Real.rpow_mul he.le]
    congr 1
    field_simp [ne_of_gt hδ]
  have hsuper := Infra.Ingredients.epsilon_supergeo hβ hβ' hΛ
    (m := j - 1) (by omega : 1 ≤ j - 1)
  have hfactor : (1 / 2 : ℝ) ≤ 1 - 10 * e := by
    linarith only [heSmall]
  calc
    (1 / 2 : ℝ) * t ^ (q β / delta β) ≤
        (1 / 2 : ℝ) * e ^ q β :=
      mul_le_mul_of_nonneg_left (hpow.trans_eq hpowEq) (by norm_num)
    _ ≤ (1 - 10 * e) * e ^ q β :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg he.le _)
    _ ≤ epsilon β Λ j := by
      have hnext := hsuper.1
      have hidx : j - 1 + 1 = j := by omega
      simpa [e, hidx] using hnext

/-- On an interior scale, the normalized κ′ lower bound controls its relative
enhancement increment. -/
theorem KappaAtPrimeBootstrap.kappaPrime_increment_ratio_internal_upper {β : ℝ} {Λ M j : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpermitted : κ ∈ permittedInterval β Λ M)
    (hj : 1 ≤ j) (hjM : j < M) :
    ((9 / 80 : ℝ) * (a β Λ j ^ 2 * epsilon β Λ j ^ 4)) /
        (kappaPrimeAt β Λ κ j (M - j)) ^ 2 ≤
      (80 / 9 : ℝ) * kappaPrimeUniformConstant β ^ 2 *
        epsilon β Λ j ^ (-2 * gamma β) := by
  let e := epsilon β Λ j
  let aa := a β Λ j
  let U := kappaPrimeUniformConstant β
  let v := kappaPrimeAt β Λ κ j (M - j)
  let c := 9 / 80 / U
  have he : 0 < e := by dsimp [e]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have ha : 0 < aa := by dsimp [aa]; exact Infra.Cutoff.a_pos hβ hβ' hΛ
  have hU : 0 < U := kappaPrimeUniformConstant_pos hβ hβ'
  have hc : 0 < c := by dsimp [c]; positivity
  have hv : 0 < v := by
    dsimp [v]
    exact kappaPrimeAt_pos hβ hβ' hΛ hκ j (M - j)
  have hscale := (kappaPrimeAt_uniform_bounds hβ hβ' hΛ hκ hpermitted
    hj hjM).1
  have hscale' : c * (aa * e ^ (2 + gamma β)) ≤ v := by
    simpa [c, aa, e, v] using hscale
  have hscaleNonneg : 0 ≤ c * (aa * e ^ (2 + gamma β)) := by positivity
  have hsq : (c * (aa * e ^ (2 + gamma β))) ^ 2 ≤ v ^ 2 :=
    (sq_le_sq₀ hscaleNonneg (le_of_lt hv)).2 hscale'
  have hden : 0 < (c * (aa * e ^ (2 + gamma β))) ^ 2 := by positivity
  have hquot :
      ((9 / 80 : ℝ) * (aa ^ 2 * e ^ 4)) / v ^ 2 ≤
        ((9 / 80 : ℝ) * (aa ^ 2 * e ^ 4)) /
          (c * (aa * e ^ (2 + gamma β))) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) hden hsq
  have hcancel :
      ((9 / 80 : ℝ) * (aa ^ 2 * e ^ 4)) /
          (c * (aa * e ^ (2 + gamma β))) ^ 2 =
        (80 / 9 : ℝ) * U ^ 2 * e ^ (-2 * gamma β) := by
    have hpow : (e ^ (2 + gamma β)) ^ 2 = e ^ (2 * (2 + gamma β)) := by
      calc
        (e ^ (2 + gamma β)) ^ 2 = (e ^ (2 + gamma β)) ^ (2 : ℝ) := by
          exact (Real.rpow_natCast (e ^ (2 + gamma β)) 2).symm
        _ = e ^ ((2 + gamma β) * 2) :=
          (Real.rpow_mul he.le (2 + gamma β) 2).symm
        _ = e ^ (2 * (2 + gamma β)) := by congr 1; ring
    have hpow' : e ^ (2 * (2 + gamma β)) = e ^ (4 + 2 * gamma β) := by
      congr 1
      ring
    have hdenEq :
        (c * (aa * e ^ (2 + gamma β))) ^ 2 =
          c ^ 2 * aa ^ 2 * e ^ (4 + 2 * gamma β) := by
      rw [mul_pow, mul_pow, hpow, hpow']
      ring
    have hratio : e ^ 4 / e ^ (4 + 2 * gamma β) = e ^ (-2 * gamma β) := by
      have hnat : e ^ 4 = e ^ (4 : ℝ) := (Real.rpow_natCast e 4).symm
      rw [hnat, ← Real.rpow_sub he]
      have hexp : (4 : ℝ) - (4 + 2 * gamma β) = -2 * gamma β := by ring
      rw [hexp]
    rw [hdenEq]
    calc
      ((9 / 80 : ℝ) * (aa ^ 2 * e ^ 4)) /
          (c ^ 2 * aa ^ 2 * e ^ (4 + 2 * gamma β)) =
        ((9 / 80 : ℝ) / c ^ 2) *
          (e ^ 4 / e ^ (4 + 2 * gamma β)) := by
            field_simp [ne_of_gt hc, ne_of_gt ha, ne_of_gt he]
      _ = (80 / 9 : ℝ) * U ^ 2 * e ^ (-2 * gamma β) := by
        rw [hratio]
        dsimp [c]
        field_simp [ne_of_gt hU]
  calc
    ((9 / 80 : ℝ) * (a β Λ j ^ 2 * epsilon β Λ j ^ 4)) /
        (kappaPrimeAt β Λ κ j (M - j)) ^ 2 =
        ((9 / 80 : ℝ) * (aa ^ 2 * e ^ 4)) / v ^ 2 := by rfl
    _ ≤ _ := hquot
    _ = _ := hcancel

theorem KappaAtPrimeBootstrap.kappaPrime_increment_ratio_terminal_upper {β : ℝ} {Λ M : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpermitted : κ ∈ permittedInterval β Λ M) :
    ((9 / 80 : ℝ) * (a β Λ M ^ 2 * epsilon β Λ M ^ 4)) / κ ^ 2 ≤
      9 / 20 := by
  let e := epsilon β Λ M
  have he : 0 < e := by dsimp [e]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have heOne : e ≤ 1 := by
    dsimp [e]
    exact Infra.Construction.epsilon_le_one hβ hβ' hΛ
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have hbetaExp : 2 * β / (q β + 1) = β - gamma β := by
    unfold gamma
    have hq : 0 < q β + 1 := by linarith [Infra.Ingredients.one_lt_q hβ hβ']
    field_simp [ne_of_gt hq]
    ring
  have hperLo : (1 / 2 : ℝ) * e ^ (β - gamma β) ≤ κ := by
    have hper := Set.mem_Icc.mp hpermitted
    simpa [e, permittedInterval, hbetaExp] using hper.1
  have haeq : a β Λ M ^ 2 * e ^ 4 = e ^ (2 * β) := by
    have hpow : (e ^ (β - 2)) ^ 2 = e ^ (2 * (β - 2)) := by
      calc
        (e ^ (β - 2)) ^ 2 = (e ^ (β - 2)) ^ (2 : ℝ) :=
          (Real.rpow_natCast (e ^ (β - 2)) 2).symm
        _ = e ^ ((β - 2) * 2) := (Real.rpow_mul he.le (β - 2) 2).symm
        _ = e ^ (2 * (β - 2)) := by congr 1; ring
    calc
      a β Λ M ^ 2 * e ^ 4 = (e ^ (β - 2)) ^ 2 * e ^ 4 := by rfl
      _ = e ^ (2 * (β - 2)) * e ^ 4 := by rw [hpow]
      _ = e ^ (2 * (β - 2) + 4) := by
        rw [← Real.rpow_natCast e 4]
        exact (Real.rpow_add he (2 * (β - 2)) 4).symm
      _ = e ^ (2 * β) := by congr 1; ring
  have hdenLo : (1 / 2 : ℝ) ^ 2 * (e ^ (β - gamma β)) ^ 2 ≤ κ ^ 2 := by
    have hsquare := (sq_le_sq₀ (by positivity) hκ.le).2 hperLo
    exact (le_of_eq (by ring)).trans hsquare
  have hpowden : (e ^ (β - gamma β)) ^ 2 = e ^ (2 * (β - gamma β)) := by
    calc
      (e ^ (β - gamma β)) ^ 2 = (e ^ (β - gamma β)) ^ (2 : ℝ) :=
        (Real.rpow_natCast (e ^ (β - gamma β)) 2).symm
      _ = e ^ ((β - gamma β) * 2) :=
        (Real.rpow_mul he.le (β - gamma β) 2).symm
      _ = e ^ (2 * (β - gamma β)) := by congr 1; ring
  have hratio : e ^ (2 * β) / ((1 / 2 : ℝ) ^ 2 *
      e ^ (2 * (β - gamma β))) = 4 * e ^ (2 * gamma β) := by
    have hcombine : e ^ (2 * (β - gamma β)) * e ^ (2 * gamma β) =
        e ^ (2 * β) := by
      calc
        e ^ (2 * (β - gamma β)) * e ^ (2 * gamma β) =
            e ^ (2 * (β - gamma β) + 2 * gamma β) :=
          (Real.rpow_add he _ _).symm
        _ = e ^ (2 * β) := by congr 1; ring
    have hcombine : e ^ (2 * (β - gamma β)) * e ^ (2 * gamma β) =
        e ^ (2 * β) := by
      calc
        e ^ (2 * (β - gamma β)) * e ^ (2 * gamma β) =
            e ^ (2 * (β - gamma β) + 2 * gamma β) :=
          (Real.rpow_add he _ _).symm
        _ = e ^ (2 * β) := by congr 1; ring
    field_simp [ne_of_gt he]
    calc
      2 ^ 2 * e ^ (2 * β) = 4 * e ^ (2 * β) := by norm_num
      _ = 4 * (e ^ (2 * (β - gamma β)) * e ^ (2 * gamma β)) := by
        rw [← hcombine]
      _ = e ^ (2 * (β - gamma β)) * 4 * e ^ (2 * gamma β) := by ring
  have hquot : ((9 / 80 : ℝ) * e ^ (2 * β)) / κ ^ 2 ≤
      ((9 / 80 : ℝ) * e ^ (2 * β)) /
        ((1 / 2 : ℝ) ^ 2 * (e ^ (β - gamma β)) ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hdenLo
  have hresult : ((9 / 80 : ℝ) * e ^ (2 * β)) /
      ((1 / 2 : ℝ) ^ 2 * (e ^ (β - gamma β)) ^ 2) ≤ 9 / 20 := by
    rw [hpowden]
    calc
      ((9 / 80 : ℝ) * e ^ (2 * β)) /
          ((1 / 2 : ℝ) ^ 2 * e ^ (2 * (β - gamma β))) =
        (9 / 80 : ℝ) *
          (e ^ (2 * β) / ((1 / 2 : ℝ) ^ 2 * e ^ (2 * (β - gamma β)))) := by ring
      _ = (9 / 80 : ℝ) * (4 * e ^ (2 * gamma β)) := by rw [hratio]
      _ ≤ 9 / 20 := by
        have hpowle : e ^ (2 * gamma β) ≤ 1 :=
          Real.rpow_le_one he.le heOne (by positivity)
        linarith only [hpowle]
  calc
    ((9 / 80 : ℝ) * (a β Λ M ^ 2 * e ^ 4)) / κ ^ 2 =
        ((9 / 80 : ℝ) * e ^ (2 * β)) / κ ^ 2 := by rw [haeq]
    _ ≤ _ := hquot
    _ ≤ _ := hresult

private theorem kappaAtBootstrap_one_step_branch1 :
  ∀ {β C₀ : ℝ} (I : Ingredients β), I.Czeta ≤ C₀ → I.Chat ≤ C₀ → ∀ {κ : ℝ}, (0 : ℝ) < κ → ∀ {M j
    : ℕ}, κ ∈ permittedInterval β I.Λ M → (2 : ℕ) ≤ j → j ≤ M → ∀ {R : ℝ}, (1 : ℝ) ≤ R → (0 : ℝ)
    ≤ C₀ →
  let u : ℝ := I.kappaAt κ j (M - j);
  let v : ℝ := kappaPrimeAt β I.Λ κ j (M - j);
  let e : ℝ := epsilon β I.Λ (j - (1 : ℕ)) ^ delta β;
  let A : ℝ := a β I.Λ j ^ (2 : ℕ) * epsilon β I.Λ j ^ (4 : ℕ);
  let B : ℝ := (9 / 80 : ℝ) * A;
  let _ : ℝ := kappaAtBootstrapErrorCoefficient β C₀ R * e;
  (0 : ℝ) < u → (0 : ℝ) < v → (0 : ℝ) < A → (0 : ℝ) < B → (0 : ℝ) < epsilon β I.Λ (j - (1 : ℕ))
    → (0 : ℝ) < kappaPrimeExpratGlobalUpperConstant β → (0 : ℝ) <
    kappaAtBootstrapErrorCoefficient β C₀ R → (0 : ℝ) < tau β I.Λ j → v / u ≤ R → u / v ≤ R → (1
    : ℝ) / R ≤ u / v → e ≤ KappaAtPrimeBootstrap.kappaAtBootstrapThreshold β C₀ R → max
    (I.KhomScalar (I.kappaAt κ j (M - j)) j / (kappaPrimeAt β I.Λ κ j (M - j) + (9 / 80 : ℝ) *
    (a β I.Λ j ^ (2 : ℕ) * epsilon β I.Λ j ^ (4 : ℕ)) / kappaPrimeAt β I.Λ κ j (M - j)))
    ((kappaPrimeAt β I.Λ κ j (M - j) + (9 / 80 : ℝ) * (a β I.Λ j ^ (2 : ℕ) * epsilon β I.Λ j ^
    (4 : ℕ)) / kappaPrimeAt β I.Λ κ j (M - j)) / I.KhomScalar (I.kappaAt κ j (M - j)) j) ≤ R *
    kappaAtBootstrapStepFactor β C₀ R
    := by
  intro β C₀ I hCz hCh κ hκ M j hpermitted hj hjM R hR hC₀ u v e A B η hu hv hA hB he hQ hE htime
      hratioInv hratioHi hratioLo hgood
  have hηle : η ≤ 1 / 2 := by
    dsimp [η]
    calc
      kappaAtBootstrapErrorCoefficient β C₀ R * e ≤
          kappaAtBootstrapErrorCoefficient β C₀ R *
            KappaAtPrimeBootstrap.kappaAtBootstrapThreshold β C₀ R :=
        mul_le_mul_of_nonneg_left hgood hE.le
      _ = 1 / 2 := by
        unfold KappaAtPrimeBootstrap.kappaAtBootstrapThreshold
        field_simp [ne_of_gt hE]
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η < 1 := by linarith
  have hqprime := kappaPrimeAt_exprat_global_upper I.one_lt_beta I.beta_lt
    I.two_pow_seven_le hκ hpermitted hj hjM
  have hqActualEq : epsilon β I.Λ j ^ 2 / (u * tau β I.Λ j) =
      (epsilon β I.Λ j ^ 2 / (v * tau β I.Λ j)) * (v / u) := by
    field_simp [ne_of_gt hu, ne_of_gt hv, ne_of_gt htime]
  have hqActual : epsilon β I.Λ j ^ 2 / (u * tau β I.Λ j) ≤
      (R * kappaPrimeExpratGlobalUpperConstant β) * e := by
    rw [hqActualEq]
    calc
      (epsilon β I.Λ j ^ 2 / (v * tau β I.Λ j)) * (v / u) ≤
          (kappaPrimeExpratGlobalUpperConstant β * e) * (v / u) :=
        mul_le_mul_of_nonneg_right hqprime (by positivity)
      _ ≤ (kappaPrimeExpratGlobalUpperConstant β * e) * R :=
        mul_le_mul_of_nonneg_left hratioInv (by positivity)
      _ = (R * kappaPrimeExpratGlobalUpperConstant β) * e := by ring
  let S := A / u
  have hS : 0 < S := by dsimp [S]; exact div_pos hA hu
  have havg0 := KhomScalar_one_step_error_unconditional I hCz hCh
    (m := j) (by omega) hu
  have havg : |I.KhomScalar u j - (u + B / u)| ≤
      lAmtOneStepConstant β C₀ * S *
        (epsilon β I.Λ j ^ 2 / (u * tau β I.Λ j) + e) := by
    have h := havg0
    dsimp only at h
    have htarget : u + (9 / 80 : ℝ) * S = u + B / u := by
      dsimp [S, B, A]
      ring
    rw [htarget] at h
    exact h
  have hrelative : |I.KhomScalar u j - (u + B / u)| ≤ η * (B / u) := by
    calc
      |I.KhomScalar u j - (u + B / u)| ≤
          lAmtOneStepConstant β C₀ * S *
            (epsilon β I.Λ j ^ 2 / (u * tau β I.Λ j) + e) := havg
      _ ≤ lAmtOneStepConstant β C₀ * S *
            ((R * kappaPrimeExpratGlobalUpperConstant β + 1) * e) := by
        apply mul_le_mul_of_nonneg_left
        · calc
            epsilon β I.Λ j ^ 2 / (u * tau β I.Λ j) + e ≤
                (R * kappaPrimeExpratGlobalUpperConstant β) * e + e :=
              add_le_add hqActual le_rfl
            _ = (R * kappaPrimeExpratGlobalUpperConstant β + 1) * e := by ring
        · have hL : 0 ≤ lAmtOneStepConstant β C₀ := by
            unfold lAmtOneStepConstant
            positivity
          exact mul_nonneg hL hS.le
      _ = η * (B / u) := by
        dsimp [η, S, B, A, kappaAtBootstrapErrorCoefficient]
        ring
  have hstep := positive_recurrence_ratio_step hu hv hB hη0 hη1
    (by linarith : 0 < R) hratioLo hratioHi hratioInv hrelative
  have hstepHi :
      max (I.KhomScalar u j / (v + B / v))
        ((v + B / v) / I.KhomScalar u j) ≤ 2 * R := by
    have hden : 0 < 1 - η := by linarith
    have hprod : R / (1 - η) ≤ 2 * R := by
      apply (div_le_iff₀ hden).2
      have hetaR : 2 * R * η ≤ R := by
        have hmul := mul_le_mul_of_nonneg_left hηle
          (by positivity : 0 ≤ 2 * R)
        linarith only [hmul]
      linarith only [hetaR]
    exact hstep.trans hprod
  have hfactor : 2 ≤ kappaAtBootstrapStepFactor β C₀ R :=
    KappaAtPrimeBootstrap.kappaAtBootstrapStepFactor_ge_two
  have hfinal :
      max (I.KhomScalar u j / (v + B / v))
        ((v + B / v) / I.KhomScalar u j) ≤
    R * kappaAtBootstrapStepFactor β C₀ R := by
    have hfactor' : 2 * R ≤
        R * kappaAtBootstrapStepFactor β C₀ R := by
      calc
        2 * R = R * 2 := by ring
        _ ≤ R * kappaAtBootstrapStepFactor β C₀ R :=
          mul_le_mul_of_nonneg_left hfactor (by linarith : 0 ≤ R)
    exact hstepHi.trans hfactor'
  simpa [u, v, B] using hfinal

/-- A comparison step is controlled either by the averaging estimate with a
small relative error or by the crude two-sided flux bound. -/
theorem kappaAtBootstrap_one_step {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {κ : ℝ} (hκ : 0 < κ) {M j : ℕ}
    (hpermitted : κ ∈ permittedInterval β I.Λ M)
    (hj : 2 ≤ j) (hjM : j ≤ M) {R : ℝ} (hR : 1 ≤ R)
    (hcurrent : max
      (I.kappaAt κ j (M - j) /
        kappaPrimeAt β I.Λ κ j (M - j))
      (kappaPrimeAt β I.Λ κ j (M - j) /
        I.kappaAt κ j (M - j)) ≤ R) :
    max
      (I.KhomScalar (I.kappaAt κ j (M - j)) j /
        (kappaPrimeAt β I.Λ κ j (M - j) +
          (9 / 80 : ℝ) * (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4) /
            kappaPrimeAt β I.Λ κ j (M - j)))
      ((kappaPrimeAt β I.Λ κ j (M - j) +
          (9 / 80 : ℝ) * (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4) /
            kappaPrimeAt β I.Λ κ j (M - j)) /
        I.KhomScalar (I.kappaAt κ j (M - j)) j) ≤
    R * kappaAtBootstrapStepFactor β C₀ R := by
  have hC₀ : 0 ≤ C₀ := le_trans (by linarith [I.one_le_Czeta]) hCz
  let u := I.kappaAt κ j (M - j)
  let v := kappaPrimeAt β I.Λ κ j (M - j)
  let e := epsilon β I.Λ (j - 1) ^ delta β
  let A := a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4
  let B := (9 / 80 : ℝ) * A
  let η := kappaAtBootstrapErrorCoefficient β C₀ R * e
  have hu : 0 < u := by dsimp [u]; exact kappaAt_pos I hκ j (M - j)
  have hv : 0 < v := by
    dsimp [v]
    exact kappaPrimeAt_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
      hκ j (M - j)
  have hA : 0 < A := by
    dsimp [A]
    have ha := Infra.Cutoff.a_pos (m := j) I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have he := Infra.Cutoff.epsilon_pos (m := j) I.one_lt_beta I.beta_lt I.two_pow_seven_le
    positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have he : 0 < epsilon β I.Λ (j - 1) := by
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hepow : 0 < e := by dsimp [e]; positivity
  have hQ : 0 < kappaPrimeExpratGlobalUpperConstant β :=
    KappaAtPrimeBootstrap.kappaPrimeExpratGlobalUpperConstant_pos I.one_lt_beta I.beta_lt
  have hE : 0 < kappaAtBootstrapErrorCoefficient β C₀ R :=
    kappaAtBootstrapErrorCoefficient_pos I.one_lt_beta I.beta_lt hC₀ hR
  have htime : 0 < tau β I.Λ j := I.tau_pos' j
  have hratioInv : v / u ≤ R := (max_le_iff.mp hcurrent).2
  have hratioHi : u / v ≤ R := (max_le_iff.mp hcurrent).1
  have hratioLo : 1 / R ≤ u / v := by
    have h := one_div_le_one_div_of_le (div_pos hv hu) hratioInv
    calc
      1 / R ≤ 1 / (v / u) := h
      _ = u / v := by field_simp [ne_of_gt hu, ne_of_gt hv]
  have hthresholdPos : 0 < KappaAtPrimeBootstrap.kappaAtBootstrapThreshold β C₀ R :=
    KappaAtPrimeBootstrap.kappaAtBootstrapThreshold_pos I.one_lt_beta I.beta_lt
      (le_trans (by linarith [I.one_le_Czeta]) hCz) hR
  by_cases hgood : e ≤ KappaAtPrimeBootstrap.kappaAtBootstrapThreshold β C₀ R
  · exact @kappaAtBootstrap_one_step_branch1 β C₀ I hCz hCh κ hκ M j hpermitted hj hjM R hR hC₀ hu
      hv hA hB he hQ hE htime hratioInv hratioHi hratioLo hgood
  · have hbad : KappaAtPrimeBootstrap.kappaAtBootstrapThreshold β C₀ R < e := lt_of_not_ge hgood
    have hfloor : KappaAtPrimeBootstrap.kappaAtBootstrapBadEpsilonFloor β C₀ R ≤
        epsilon β I.Λ j := by
      dsimp [KappaAtPrimeBootstrap.kappaAtBootstrapBadEpsilonFloor, e] at hbad ⊢
      exact KappaAtPrimeBootstrap.epsilon_next_lower_of_bad_threshold I.one_lt_beta I.beta_lt
        I.two_pow_seven_le hj hthresholdPos hbad
    have htv : B / v ^ 2 ≤ KappaAtPrimeBootstrap.kappaAtBootstrapBadIncrementCap β C₀ R := by
      by_cases hjEq : j = M
      · subst M
        have hvEq : v = κ := by simp [v, kappaPrimeAt]
        rw [hvEq]
        have hterminal := KappaAtPrimeBootstrap.kappaPrime_increment_ratio_terminal_upper
          I.one_lt_beta I.beta_lt I.two_pow_seven_le hκ hpermitted
        have heq : B / κ ^ 2 =
            ((9 / 80 : ℝ) *
              (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4)) / κ ^ 2 := by
          rfl
        rw [heq]
        dsimp [KappaAtPrimeBootstrap.kappaAtBootstrapBadIncrementCap]
        exact (le_trans hterminal (le_max_left _ _))
      · have hjM' : j < M := by omega
        have hint := KappaAtPrimeBootstrap.kappaPrime_increment_ratio_internal_upper I.one_lt_beta
          I.beta_lt I.two_pow_seven_le hκ hpermitted (by omega) hjM'
        have hepsilonFloorPos : 0 < KappaAtPrimeBootstrap.kappaAtBootstrapBadEpsilonFloor β C₀ R
            := by
          unfold KappaAtPrimeBootstrap.kappaAtBootstrapBadEpsilonFloor
          exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hthresholdPos _)
        have hgammaNeg : -2 * gamma β ≤ 0 := by
          have hγ := Infra.Ingredients.gamma_pos I.one_lt_beta I.beta_lt
          linarith
        have hpow : epsilon β I.Λ j ^ (-2 * gamma β) ≤
            KappaAtPrimeBootstrap.kappaAtBootstrapBadEpsilonFloor β C₀ R ^ (-2 * gamma β) :=
          Real.rpow_le_rpow_of_nonpos hepsilonFloorPos hfloor hgammaNeg
        have hint' : B / v ^ 2 ≤
            (80 / 9 : ℝ) * kappaPrimeUniformConstant β ^ 2 *
              epsilon β I.Λ j ^ (-2 * gamma β) := by
          simpa [B, A] using hint
        have hcoef : 0 ≤ (80 / 9 : ℝ) *
            kappaPrimeUniformConstant β ^ 2 := by positivity
        have hfinal := calc
          B / v ^ 2 ≤ (80 / 9 : ℝ) * kappaPrimeUniformConstant β ^ 2 *
              epsilon β I.Λ j ^ (-2 * gamma β) := hint'
          _ ≤ (80 / 9 : ℝ) * kappaPrimeUniformConstant β ^ 2 *
              KappaAtPrimeBootstrap.kappaAtBootstrapBadEpsilonFloor β C₀ R ^ (-2 * gamma β) :=
            mul_le_mul_of_nonneg_left hpow hcoef
        dsimp [KappaAtPrimeBootstrap.kappaAtBootstrapBadIncrementCap]
        exact le_max_of_le_right hfinal
    have hD : A / 2 = (40 / 9 : ℝ) * B := by dsimp [B]; ring
    have hlow := khomScalar_ge_input I (m := j) (by omega) u hu
    have hhigh := khomScalar_le_input_add_amplitude I (m := j) (by omega) u hu
    have hupper : I.KhomScalar u j ≤ u + (A / 2) / u := by
      calc
        I.KhomScalar u j ≤ u + A / (2 * u) := by simpa [A] using hhigh
        _ = u + (A / 2) / u := by ring
    have hcoarse := KappaAtPrimeBootstrap.coarse_recurrence_ratio_step hu hv hB hD hcurrent
      hlow hupper
    have hfinal :
        max (I.KhomScalar u j / (v + B / v))
          ((v + B / v) / I.KhomScalar u j) ≤
        R * kappaAtBootstrapStepFactor β C₀ R := by
      have hfactor : 1 + (40 / 9 : ℝ) * (B / v ^ 2) ≤
          kappaAtBootstrapStepFactor β C₀ R := by
        unfold kappaAtBootstrapStepFactor
        calc
          1 + (40 / 9 : ℝ) * (B / v ^ 2) ≤
              1 + (40 / 9 : ℝ) *
                KappaAtPrimeBootstrap.kappaAtBootstrapBadIncrementCap β C₀ R :=
            add_le_add_right (mul_le_mul_of_nonneg_left htv
              (by norm_num : (0 : ℝ) ≤ 40 / 9)) 1
          _ ≤ max 2 (1 + (40 / 9 : ℝ) *
              KappaAtPrimeBootstrap.kappaAtBootstrapBadIncrementCap β C₀ R) := le_max_right _ _
      exact hcoarse.trans
        (mul_le_mul_of_nonneg_left hfactor
          (le_trans (by norm_num : (0 : ℝ) ≤ 1) hR))
    simpa [u, v, B] using hfinal

/-- Good-step comparison with the actual, summable relative error retained. -/
theorem kappaAtBootstrap_averaged_step {β C₀ : ℝ}
    (I : Ingredients β) (hCz : I.Czeta ≤ C₀) (hCh : I.Chat ≤ C₀)
    {κ : ℝ} (hκ : 0 < κ) {M j : ℕ}
    (hpermitted : κ ∈ permittedInterval β I.Λ M)
    (hj : 2 ≤ j) (hjM : j ≤ M) {R : ℝ} (hR : 1 ≤ R)
    (hcurrent : max
      (I.kappaAt κ j (M - j) /
        kappaPrimeAt β I.Λ κ j (M - j))
      (kappaPrimeAt β I.Λ κ j (M - j) /
        I.kappaAt κ j (M - j)) ≤ R)
    (hηsmall : kappaAtBootstrapErrorCoefficient β C₀ R *
      epsilon β I.Λ (j - 1) ^ delta β < 1) :
    let η := kappaAtBootstrapErrorCoefficient β C₀ R *
      epsilon β I.Λ (j - 1) ^ delta β
    max
      (I.KhomScalar (I.kappaAt κ j (M - j)) j /
        (kappaPrimeAt β I.Λ κ j (M - j) +
          (9 / 80 : ℝ) * (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4) /
            kappaPrimeAt β I.Λ κ j (M - j)))
      ((kappaPrimeAt β I.Λ κ j (M - j) +
          (9 / 80 : ℝ) * (a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4) /
            kappaPrimeAt β I.Λ κ j (M - j)) /
        I.KhomScalar (I.kappaAt κ j (M - j)) j) ≤
      R / (1 - η) := by
  dsimp only
  let u := I.kappaAt κ j (M - j)
  let v := kappaPrimeAt β I.Λ κ j (M - j)
  let e := epsilon β I.Λ (j - 1) ^ delta β
  let A := a β I.Λ j ^ 2 * epsilon β I.Λ j ^ 4
  let B := (9 / 80 : ℝ) * A
  let η := kappaAtBootstrapErrorCoefficient β C₀ R * e
  have hC₀ : 0 ≤ C₀ := le_trans (by linarith [I.one_le_Czeta]) hCz
  have hu : 0 < u := by dsimp [u]; exact kappaAt_pos I hκ j (M - j)
  have hv : 0 < v := by
    dsimp [v]
    exact kappaPrimeAt_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
      hκ j (M - j)
  have hA : 0 < A := by
    dsimp [A]
    have ha := Infra.Cutoff.a_pos (m := j) I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have he := Infra.Cutoff.epsilon_pos (m := j) I.one_lt_beta I.beta_lt I.two_pow_seven_le
    positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have he : 0 < epsilon β I.Λ (j - 1) := by
    exact Infra.Cutoff.epsilon_pos (m := j - 1)
      I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hepow : 0 < e := by dsimp [e]; positivity
  have hQ : 0 < kappaPrimeExpratGlobalUpperConstant β :=
    KappaAtPrimeBootstrap.kappaPrimeExpratGlobalUpperConstant_pos I.one_lt_beta I.beta_lt
  have hE : 0 < kappaAtBootstrapErrorCoefficient β C₀ R :=
    kappaAtBootstrapErrorCoefficient_pos I.one_lt_beta I.beta_lt hC₀ hR
  have htime : 0 < tau β I.Λ j := I.tau_pos' j
  have hcurrentInv : v / u ≤ R := (max_le_iff.mp hcurrent).2
  have hcurrentHi : u / v ≤ R := (max_le_iff.mp hcurrent).1
  have hcurrentLo : 1 / R ≤ u / v := by
    have h := one_div_le_one_div_of_le (div_pos hv hu) hcurrentInv
    calc
      1 / R ≤ 1 / (v / u) := h
      _ = u / v := by field_simp [ne_of_gt hu, ne_of_gt hv]
  have hqprime := kappaPrimeAt_exprat_global_upper I.one_lt_beta I.beta_lt
    I.two_pow_seven_le hκ hpermitted hj hjM
  have hqActualEq : epsilon β I.Λ j ^ 2 / (u * tau β I.Λ j) =
      (epsilon β I.Λ j ^ 2 / (v * tau β I.Λ j)) * (v / u) := by
    field_simp [ne_of_gt hu, ne_of_gt hv, ne_of_gt htime]
  have hqActual : epsilon β I.Λ j ^ 2 / (u * tau β I.Λ j) ≤
      (R * kappaPrimeExpratGlobalUpperConstant β) * e := by
    rw [hqActualEq]
    calc
      (epsilon β I.Λ j ^ 2 / (v * tau β I.Λ j)) * (v / u) ≤
          (kappaPrimeExpratGlobalUpperConstant β * e) * (v / u) :=
        mul_le_mul_of_nonneg_right hqprime (by positivity)
      _ ≤ (kappaPrimeExpratGlobalUpperConstant β * e) * R :=
        mul_le_mul_of_nonneg_left hcurrentInv (by positivity)
      _ = (R * kappaPrimeExpratGlobalUpperConstant β) * e := by ring
  let S := A / u
  have hS : 0 < S := by dsimp [S]; exact div_pos hA hu
  have havg0 := KhomScalar_one_step_error_unconditional I hCz hCh
    (m := j) (by omega) hu
  have havg : |I.KhomScalar u j - (u + B / u)| ≤
      lAmtOneStepConstant β C₀ * S *
        (epsilon β I.Λ j ^ 2 / (u * tau β I.Λ j) + e) := by
    have h := havg0
    dsimp only at h
    have htarget : u + (9 / 80 : ℝ) * S = u + B / u := by
      dsimp [S, B, A]
      ring
    rw [htarget] at h
    exact h
  have hrelative : |I.KhomScalar u j - (u + B / u)| ≤ η * (B / u) := by
    calc
      |I.KhomScalar u j - (u + B / u)| ≤
          lAmtOneStepConstant β C₀ * S *
            (epsilon β I.Λ j ^ 2 / (u * tau β I.Λ j) + e) := havg
      _ ≤ lAmtOneStepConstant β C₀ * S *
            ((R * kappaPrimeExpratGlobalUpperConstant β + 1) * e) := by
        apply mul_le_mul_of_nonneg_left
        · calc
            epsilon β I.Λ j ^ 2 / (u * tau β I.Λ j) + e ≤
                (R * kappaPrimeExpratGlobalUpperConstant β) * e + e :=
              add_le_add hqActual le_rfl
            _ = (R * kappaPrimeExpratGlobalUpperConstant β + 1) * e := by ring
        · have hL : 0 ≤ lAmtOneStepConstant β C₀ := by
            unfold lAmtOneStepConstant
            positivity
          exact mul_nonneg hL hS.le
      _ = η * (B / u) := by
        dsimp [η, S, B, A, kappaAtBootstrapErrorCoefficient]
        ring
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η < 1 := by simpa [η, e] using hηsmall
  have hstep := positive_recurrence_ratio_step hu hv hB hη0 hη1
    (by linarith : 0 < R) hcurrentLo hcurrentHi hcurrentInv hrelative
  have hκrec :
      max (I.KhomScalar u j / (v + B / v))
        ((v + B / v) / I.KhomScalar u j) ≤ R / (1 - η) := hstep
  simpa [u, v, B] using hκrec

theorem kappaAtBootstrap_errorCoefficient_mono {β C₀ R S : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hC₀ : 0 ≤ C₀)
    (hRS : R ≤ S) :
    kappaAtBootstrapErrorCoefficient β C₀ R ≤
      kappaAtBootstrapErrorCoefficient β C₀ S := by
  have hL : 0 ≤ lAmtOneStepConstant β C₀ := by
    unfold lAmtOneStepConstant
    positivity
  have hQ : 0 ≤ kappaPrimeExpratGlobalUpperConstant β :=
    le_of_lt (KappaAtPrimeBootstrap.kappaPrimeExpratGlobalUpperConstant_pos hβ hβ')
  unfold kappaAtBootstrapErrorCoefficient
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa [add_comm] using add_le_add_right
    (mul_le_mul_of_nonneg_right hRS hQ) 1

theorem kappaAtBootstrapTail_nonneg {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) {E : ℝ} (hE : 0 ≤ E) (n : ℕ) :
    0 ≤ kappaAtBootstrapTail β E n := by
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  have hr : 0 < (128 : ℝ) ^ (-delta β) := by positivity
  have hrlt : (128 : ℝ) ^ (-delta β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold kappaAtBootstrapTail
  positivity

theorem kappaAtBootstrapTail_le_half_of_index {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) {E : ℝ} (hE : 0 < E)
    {N n : ℕ} (hN : kappaAtBootstrapTail β E N ≤ 1 / 2)
    (hn : N ≤ n) :
    kappaAtBootstrapTail β E n ≤ 1 / 2 := by
  let r := (128 : ℝ) ^ (-delta β)
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  have hr : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hnEq : n = N + (n - N) := by omega
  have hpow' : r ^ n ≤ r ^ N := by
    rw [hnEq, pow_add]
    have hpowTail : r ^ (n - N) ≤ 1 := pow_le_one₀ hr.le hrlt.le
    have hpow : r ^ N * r ^ (n - N) ≤ r ^ N * 1 :=
      mul_le_mul_of_nonneg_left hpowTail (pow_nonneg hr.le N)
    simpa using hpow
  have hnum : E * r ^ n ≤ E * r ^ N := mul_le_mul_of_nonneg_left hpow' hE.le
  have hden : 0 < 1 - r := sub_pos.mpr hrlt
  have htail : kappaAtBootstrapTail β E n ≤ kappaAtBootstrapTail β E N := by
    unfold kappaAtBootstrapTail
    exact div_le_div_of_nonneg_right hnum hden.le
  exact htail.trans hN

theorem kappaAtBootstrapTail_step_bound {β η : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) {E : ℝ} (hE : 0 < E)
    {m : ℕ} (hmTail : kappaAtBootstrapTail β E m ≤ 1 / 2)
    (hη0 : 0 ≤ η)
    (hη : η ≤ E * ((128 : ℝ) ^ (-delta β)) ^ m) :
    (1 - kappaAtBootstrapTail β E (m + 1))⁻¹ / (1 - η) ≤
      (1 - kappaAtBootstrapTail β E m)⁻¹ := by
  let a₀ := kappaAtBootstrapTail β E (m + 1)
  let b₀ := E * ((128 : ℝ) ^ (-delta β)) ^ m
  have hδ := Infra.Ingredients.delta_pos hβ hβ'
  have hr : 0 < (128 : ℝ) ^ (-delta β) := by positivity
  have hrlt : (128 : ℝ) ^ (-delta β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - (128 : ℝ) ^ (-delta β) := sub_pos.mpr hrlt
  have ha₀ : 0 ≤ a₀ := by
    dsimp [a₀]
    exact kappaAtBootstrapTail_nonneg hβ hβ' hE.le _
  have hb₀ : 0 ≤ b₀ := by dsimp [b₀]; positivity
  have hsplit : kappaAtBootstrapTail β E m = b₀ + a₀ := by
    dsimp [a₀, b₀]
    rw [kappaAtBootstrapTail_succ m (ne_of_gt hden)]
  have hηle : η ≤ b₀ := hη
  have hηsmall : η ≤ 1 / 2 := by
    calc
      η ≤ kappaAtBootstrapTail β E m := hηle.trans (by rw [hsplit]; linarith)
      _ ≤ 1 / 2 := hmTail
  have hdenA : 0 < 1 - a₀ := by
    have hsplitLe : b₀ + a₀ ≤ 1 / 2 := by rw [← hsplit]; exact hmTail
    have ha₀le : a₀ ≤ 1 / 2 := by linarith [hsplitLe, hb₀]
    linarith
  have hdenEta : 0 < 1 - η := by linarith
  have hdenM : 0 < 1 - kappaAtBootstrapTail β E m := by linarith [hmTail]
  have hprod : 1 - kappaAtBootstrapTail β E m ≤ (1 - a₀) * (1 - η) := by
    rw [hsplit]
    have hmul : 0 ≤ a₀ * η := mul_nonneg ha₀ hη0
    linarith only [hηle, hmul]
  have hinv : ((1 - a₀) * (1 - η))⁻¹ ≤
      (1 - kappaAtBootstrapTail β E m)⁻¹ :=
    by simpa [one_div] using (one_div_le_one_div_of_le hdenM hprod)
  have hdivEq : (1 - a₀)⁻¹ / (1 - η) =
      ((1 - a₀) * (1 - η))⁻¹ := by
    field_simp [ne_of_gt hdenA, ne_of_gt hdenEta]
  simpa [a₀, hdivEq] using hinv

theorem kappaAtBootstrapIteratedBound_ge_two {β C₀ : ℝ} (n : ℕ) :
    2 ≤ kappaAtBootstrapIteratedBound β C₀ n := by
  induction n with
  | zero => simp [kappaAtBootstrapIteratedBound]
  | succ n ih =>
      rw [kappaAtBootstrapIteratedBound]
      have hf := KappaAtPrimeBootstrap.kappaAtBootstrapStepFactor_ge_two
        (β := β) (C₀ := C₀) (R := kappaAtBootstrapIteratedBound β C₀ n)
      nlinarith [ih, hf]

theorem kappaAtBootstrapIteratedBound_pos {β C₀ : ℝ} (n : ℕ) :
    0 < kappaAtBootstrapIteratedBound β C₀ n :=
  lt_of_lt_of_le (by norm_num) (kappaAtBootstrapIteratedBound_ge_two n)

theorem kappaAtBootstrapIteratedBound_mono {β C₀ : ℝ} {k n : ℕ}
    (hk : k ≤ n) :
    kappaAtBootstrapIteratedBound β C₀ k ≤
      kappaAtBootstrapIteratedBound β C₀ n := by
  induction n generalizing k with
  | zero => simp_all
  | succ n ih =>
      by_cases hkn : k ≤ n
      · have hstep : kappaAtBootstrapIteratedBound β C₀ n ≤
            kappaAtBootstrapIteratedBound β C₀ (n + 1) := by
          rw [kappaAtBootstrapIteratedBound]
          have hf := KappaAtPrimeBootstrap.kappaAtBootstrapStepFactor_ge_two
            (β := β) (C₀ := C₀) (R := kappaAtBootstrapIteratedBound β C₀ n)
          have hpos := kappaAtBootstrapIteratedBound_pos (β := β) (C₀ := C₀) n
          nlinarith
        exact (ih hkn).trans hstep
      · have hkEq : k = n + 1 := by omega
        simp [hkEq]

end AVenhance.Infra.Section3

end
