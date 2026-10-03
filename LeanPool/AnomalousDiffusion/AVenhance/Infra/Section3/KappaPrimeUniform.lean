/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.KappaPrimeScaling

/-! Uniform scale-normalized bounds for the auxiliary diffusivity chain. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

theorem KappaPrimeUniform.epsilon_le_128_rpow_neg {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    epsilon β Λ m ≤ (128 : ℝ) ^ (-(m : ℝ)) := by
  have hε := Infra.Ingredients.epsilon_le_lambda_pow hβ hβ' hΛ (m := m)
  have hΛ128 : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  have hexp : -(m : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg m)
  exact hε.trans (Real.rpow_le_rpow_of_nonpos (by norm_num) hΛ128 hexp)

theorem KappaPrimeUniform.finite_geometric_sum_le {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) ≤ 1 / (1 - r) := by
  have hrne : r ≠ 1 := ne_of_lt hr1
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  have hgeom : (∑ i ∈ Finset.range n, r ^ i) = (1 - r ^ n) / (1 - r) := by
    rw [geom_sum_eq hrne]
    field_simp [hrne, ne_of_gt hden]
    ring
  rw [hgeom, div_le_div_iff₀ hden hden]
  have hpow : 0 ≤ r ^ n := pow_nonneg hr0 n
  nlinarith

theorem KappaPrimeUniform.rpow_neg_nat_eq_inv_pow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ (-(n : ℝ)) = (x⁻¹) ^ n := by
  calc
    x ^ (-(n : ℝ)) = (x ^ (n : ℝ))⁻¹ := by rw [Real.rpow_neg hx.le]
    _ = (x ^ n)⁻¹ := by rw [Real.rpow_natCast]
    _ = (x⁻¹) ^ n := by rw [inv_pow]

theorem KappaPrimeUniform.rpow_neg_nat_mul_eq_pow {x p : ℝ} (hx : 0 < x)
    (n : ℕ) :
    x ^ (-(n : ℝ) * p) = (x ^ (-p)) ^ n := by
  calc
    x ^ (-(n : ℝ) * p) = x ^ ((-p) * (n : ℝ)) := by congr 1; ring
    _ = (x ^ (-p)) ^ (n : ℝ) := by rw [← Real.rpow_mul hx.le]
    _ = (x ^ (-p)) ^ n := by rw [Real.rpow_natCast]

/-- The β-dependent linear error coefficient for one normalized scale ratio. -/
def kappaPrimeRatioError (β : ℝ) : ℝ :=
  2 * Infra.Ingredients.supergeoConstant β +
    Infra.Ingredients.supergeoConstant β ^ 2 / 128

/-- Uniform bound immediately below the permitted terminal scale. -/
def kappaPrimeEndpointConstant (β : ℝ) : ℝ :=
  max ((1 + kappaPrimeRatioError β / 128) * (2 + 2 * (9 / 80)))
    ((1 + 50 / 128) * (2 * (9 / 80)))

/-- A β-only bound for every reciprocal-symmetric normalized κ′ value. -/
def kappaPrimeUniformConstant (β : ℝ) : ℝ :=
  kappaPrimeEndpointConstant β * Real.exp
    (max (kappaPrimeRatioError β) 50 * (128 / 127) +
      1 / (1 - (128 : ℝ) ^ (-2 * gamma β)))

theorem KappaPrimeUniform.kappaPrimeNormalized_terminal_bounds {β : ℝ} {Λ M : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (_hκ : 0 < κ)
    (hpermitted : κ ∈ AVenhance.permittedInterval β Λ M) :
    (1 / 2) * epsilon β Λ M ^ (-2 * gamma β) ≤
        kappaPrimeNormalized β Λ κ M 0 ∧
      kappaPrimeNormalized β Λ κ M 0 ≤
        2 * epsilon β Λ M ^ (-2 * gamma β) := by
  let e := epsilon β Λ M
  let z := kappaPrimeNormalized β Λ κ M 0
  have he : 0 < e := by
    dsimp [e]
    exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hq : 1 < q β := Infra.Ingredients.one_lt_q hβ hβ'
  have hqden : 0 < q β + 1 := by linarith
  have hbal : q β * (β - gamma β) = β + gamma β :=
    q_gamma_balance hβ hβ'
  have hmul : (β - gamma β) * (q β + 1) = 2 * β := by
    calc
      (β - gamma β) * (q β + 1) =
          q β * (β - gamma β) + (β - gamma β) := by ring
      _ = (β + gamma β) + (β - gamma β) := by rw [hbal]
      _ = 2 * β := by ring
  have hExp : β - gamma β = 2 * β / (q β + 1) := by
    calc
      β - gamma β = ((β - gamma β) * (q β + 1)) / (q β + 1) := by
        field_simp [ne_of_gt hqden]
      _ = 2 * β / (q β + 1) := by rw [hmul]
  have hper := Set.mem_Icc.mp hpermitted
  have hperLo : 1 / 2 * e ^ (2 * β / (q β + 1)) ≤ κ := by
    simpa [e, AVenhance.permittedInterval] using hper.1
  have hperHi : κ ≤ 2 * e ^ (2 * β / (q β + 1)) := by
    simpa [e, AVenhance.permittedInterval] using hper.2
  rw [← hExp] at hperLo hperHi
  have hratio : e ^ (β - gamma β) / e ^ (β + gamma β) =
      e ^ (-2 * gamma β) := by
    rw [← Real.rpow_sub he]
    congr 1
    ring
  have hlo : (1 / 2) * e ^ (-2 * gamma β) ≤ z := by
    have hquot : (1 / 2 * e ^ (β - gamma β)) /
        e ^ (β + gamma β) ≤ κ / e ^ (β + gamma β) :=
      div_le_div_of_nonneg_right hperLo (Real.rpow_nonneg he.le _)
    have hquotEq : (1 / 2 * e ^ (β - gamma β)) /
        e ^ (β + gamma β) = (1 / 2) * e ^ (-2 * gamma β) := by
      rw [← hratio]
      ring
    rw [hquotEq] at hquot
    dsimp [z, kappaPrimeNormalized]
    exact hquot
  have hhi : z ≤ 2 * e ^ (-2 * gamma β) := by
    have hquot : κ / e ^ (β + gamma β) ≤
        (2 * e ^ (β - gamma β)) / e ^ (β + gamma β) :=
      div_le_div_of_nonneg_right hperHi (Real.rpow_nonneg he.le _)
    have hquotEq : (2 * e ^ (β - gamma β)) /
        e ^ (β + gamma β) = 2 * e ^ (-2 * gamma β) := by
      rw [← hratio]
      ring
    rw [hquotEq] at hquot
    dsimp [z, kappaPrimeNormalized]
    exact hquot
  exact ⟨hlo, hhi⟩

/-- The last normalized recurrence step cancels the scale-dependent size of
the permitted terminal value. -/
theorem KappaPrimeUniform.kappaPrimeNormalizedSize_endpoint_bound {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpermitted : κ ∈ AVenhance.permittedInterval β Λ (m + 1))
    (hm : 1 ≤ m) :
    kappaPrimeNormalizedSize β Λ κ m 1 ≤ kappaPrimeEndpointConstant β := by
  let e := epsilon β Λ (m + 1)
  let z := kappaPrimeNormalized β Λ κ (m + 1) 0
  let u := e ^ (2 * gamma β)
  let R := (epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
    (β - gamma β)
  let c : ℝ := 9 / 80
  let T := u * z + c / z
  have he : 0 < e := by dsimp [e]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have hterminal := KappaPrimeUniform.kappaPrimeNormalized_terminal_bounds hβ hβ' hΛ hκ hpermitted
  have hzlo : (1 / 2) * e ^ (-2 * gamma β) ≤ z := by
    simpa [e, z] using hterminal.1
  have hzhi : z ≤ 2 * e ^ (-2 * gamma β) := by
    simpa [e, z] using hterminal.2
  have hzpos : 0 < z := kappaPrimeNormalized_pos hβ hβ' hΛ hκ (m + 1) 0
  have hcancel : e ^ (2 * gamma β) * e ^ (-2 * gamma β) = 1 := by
    rw [← Real.rpow_add he]
    simp
  have huzlo : 1 / 2 ≤ u * z := by
    dsimp [u]
    calc
      (1 / 2) = (1 / 2) *
          (e ^ (2 * gamma β) * e ^ (-2 * gamma β)) := by rw [hcancel]; ring
      _ = e ^ (2 * gamma β) * (1 / 2 * e ^ (-2 * gamma β)) := by ring
      _ ≤ e ^ (2 * gamma β) * z :=
        mul_le_mul_of_nonneg_left hzlo (by positivity)
      _ = u * z := by rfl
  have huzhi : u * z ≤ 2 := by
    dsimp [u]
    calc
      e ^ (2 * gamma β) * z ≤
          e ^ (2 * gamma β) * (2 * e ^ (-2 * gamma β)) :=
        mul_le_mul_of_nonneg_left hzhi (by positivity)
      _ = 2 := by
        calc
          e ^ (2 * gamma β) * (2 * e ^ (-2 * gamma β)) =
              2 * (e ^ (2 * gamma β) * e ^ (-2 * gamma β)) := by ring
          _ = 2 := by rw [hcancel]; ring
  have heOne : e ≤ 1 := by
    have hepow := KappaPrimeUniform.epsilon_le_128_rpow_neg hβ hβ' hΛ (m := m + 1)
    have h128 : 1 ≤ (128 : ℝ) := by norm_num
    have hexp : -((m + 1 : ℕ) : ℝ) ≤ 0 :=
      neg_nonpos.mpr (Nat.cast_nonneg (m + 1))
    exact le_trans hepow (Real.rpow_le_one_of_one_le_of_nonpos h128 hexp)
  have huOne : e ^ (2 * gamma β) ≤ 1 :=
    Real.rpow_le_one he.le heOne (by positivity)
  have hpowInv : 1 ≤ e ^ (-2 * gamma β) := by
    have hpos : 0 < e ^ (2 * gamma β) := Real.rpow_pos_of_pos he _
    have hinv : 1 ≤ (e ^ (2 * gamma β))⁻¹ := (one_le_inv₀ hpos).2 huOne
    simpa [Real.rpow_neg he.le] using hinv
  have hzHalf : 1 / 2 ≤ z := le_trans (by nlinarith [hpowInv]) hzlo
  have hc : 0 < c := by norm_num [c]
  have hcInv : c / z ≤ 2 * c := by
    apply (div_le_iff₀ hzpos).2
    dsimp [c]
    nlinarith [hzHalf]
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hTlo : 1 / 2 ≤ T := by
    dsimp [T]
    linarith [huzlo, div_nonneg hc.le hzpos.le]
  have hratio := kappaPrime_ratio_factor_bounds hβ hβ' hΛ hm
  have heMbound : epsilon β Λ m ≤ 1 / 128 := by
    have heps := KappaPrimeUniform.epsilon_le_128_rpow_neg hβ hβ' hΛ (m := m)
    have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hExp : -(m : ℝ) ≤ -1 := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 128) hExp
    have hInv : (128 : ℝ) ^ (-1 : ℝ) = 1 / 128 := by norm_num
    calc
      epsilon β Λ m ≤ 128 ^ (-(m : ℝ)) := heps
      _ ≤ 128 ^ (-1 : ℝ) := hpow
      _ = 1 / 128 := hInv
  have hA : 0 ≤ kappaPrimeRatioError β := by
    dsimp [kappaPrimeRatioError, Infra.Ingredients.supergeoConstant]
    have hq : 0 < q β := by linarith [Infra.Ingredients.one_lt_q hβ hβ']
    positivity
  have hRupper : R ≤ 1 + kappaPrimeRatioError β / 128 := by
    have h := hratio.1
    dsimp [R] at h ⊢
    have hmul := mul_le_mul_of_nonneg_left heMbound hA
    dsimp [kappaPrimeRatioError] at h hmul ⊢
    nlinarith
  have hRinvUpper : R⁻¹ ≤ 1 + 50 / 128 := by
    have h := hratio.2
    dsimp [R] at h ⊢
    nlinarith [mul_le_mul_of_nonneg_left heMbound (by norm_num : (0 : ℝ) ≤ 50)]
  have hRpos : 0 < R := by
    dsimp [R]
    apply Real.rpow_pos_of_pos
    exact div_pos (Infra.Cutoff.epsilon_pos hβ hβ' hΛ)
      (Real.rpow_pos_of_pos (Infra.Cutoff.epsilon_pos hβ hβ' hΛ) _)
  have hrec := kappaPrimeNormalized_step hβ hβ' hΛ hκ m 0
  have hcur : kappaPrimeNormalized β Λ κ m 1 = R * T := by
    simpa [R, T, u, z, c, e] using hrec
  have hcurUpper : R * T ≤
      (1 + kappaPrimeRatioError β / 128) * (2 + 2 * c) := by
    have hTupper : T ≤ 2 + 2 * c := by dsimp [T]; linarith [huzhi, hcInv]
    exact mul_le_mul hRupper hTupper (by positivity) (by positivity)
  have hrecipEq : c / (R * T) = R⁻¹ * (c / T) := by
    field_simp [ne_of_gt hRpos, ne_of_gt hTpos]
  have hrecipUpper : c / (R * T) ≤ (1 + 50 / 128) * (2 * c) := by
    rw [hrecipEq]
    have hcT : c / T ≤ 2 * c := by
      apply (div_le_iff₀ hTpos).2
      nlinarith [hTlo]
    exact mul_le_mul hRinvUpper hcT (by positivity) (by positivity)
  unfold kappaPrimeNormalizedSize
  rw [hcur]
  have hT : u * z + c / z = T := rfl
  change max (R * (u * z + c / z)) (c / (R * (u * z + c / z))) ≤ _
  rw [hT]
  dsimp [kappaPrimeEndpointConstant]
  exact max_le_max (by simpa [c] using hcurUpper) (by simpa [c] using hrecipUpper)

/-- Iterate the size recurrence for a chosen number of steps, leaving a
positive depth at the endpoint. -/
theorem KappaPrimeUniform.kappaPrimeNormalizedSize_chain_bound_to {β : ℝ} {Λ : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ) (m d r : ℕ) :
    kappaPrimeNormalizedSize β Λ κ m (d + r) ≤
      (∏ i ∈ Finset.range d,
        kappaPrimeNormalizedStepFactor β Λ (m + i)) *
        kappaPrimeNormalizedSize β Λ κ (m + d) r := by
  induction d generalizing m r with
  | zero => simp
  | succ d ih =>
      have hstep := kappaPrimeNormalizedSize_step hβ hβ' hΛ hκ m (d + r)
      have htail := ih (m + 1) r
      have hfactorNonneg : 0 ≤ kappaPrimeNormalizedStepFactor β Λ m := by
        have he : 0 < epsilon β Λ m := Infra.Cutoff.epsilon_pos hβ hβ' hΛ
        have hen : 0 < epsilon β Λ (m + 1) :=
          Infra.Cutoff.epsilon_pos hβ hβ' hΛ
        have hR : 0 < (epsilon β Λ (m + 1) /
            epsilon β Λ m ^ q β) ^ (β - gamma β) := by
          apply Real.rpow_pos_of_pos
          exact div_pos hen (Real.rpow_pos_of_pos he _)
        dsimp [kappaPrimeNormalizedStepFactor]
        exact mul_nonneg (le_trans hR.le (le_max_left _ _)) (by positivity)
      have hdepth : d + 1 + r = d + r + 1 := by omega
      calc
        kappaPrimeNormalizedSize β Λ κ m (d + 1 + r) ≤
            kappaPrimeNormalizedStepFactor β Λ m *
              kappaPrimeNormalizedSize β Λ κ (m + 1) (d + r) := by
          rw [hdepth]
          exact hstep
        _ ≤ kappaPrimeNormalizedStepFactor β Λ m *
              ((∏ i ∈ Finset.range d,
                kappaPrimeNormalizedStepFactor β Λ (m + 1 + i)) *
                kappaPrimeNormalizedSize β Λ κ (m + 1 + d) r) :=
          mul_le_mul_of_nonneg_left htail hfactorNonneg
        _ = (∏ i ∈ Finset.range (d + 1),
              kappaPrimeNormalizedStepFactor β Λ (m + i)) *
              kappaPrimeNormalizedSize β Λ κ (m + (d + 1)) r := by
          rw [Finset.prod_range_succ']
          have hprod :
              (∏ i ∈ Finset.range d,
                kappaPrimeNormalizedStepFactor β Λ (m + 1 + i)) =
              ∏ i ∈ Finset.range d,
                kappaPrimeNormalizedStepFactor β Λ (m + (i + 1)) := by
            apply Finset.prod_congr rfl
            intro i _
            congr 1
            omega
          have hidx : (m + 1) + d = m + (d + 1) := by omega
          rw [hprod, hidx]
          ring_nf

theorem KappaPrimeUniform.kappaPrimeNormalizedStepFactor_bound {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    (hm : 1 ≤ m) :
    kappaPrimeNormalizedStepFactor β Λ m ≤
      (1 + max (kappaPrimeRatioError β) 50 * epsilon β Λ m) *
        (1 + epsilon β Λ (m + 1) ^ (2 * gamma β)) := by
  let R := (epsilon β Λ (m + 1) / epsilon β Λ m ^ q β) ^
    (β - gamma β)
  let B := max (kappaPrimeRatioError β) 50
  have hratio := kappaPrime_ratio_factor_bounds hβ hβ' hΛ hm
  have he : 0 ≤ epsilon β Λ m :=
    (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le
  have hA : 0 ≤ kappaPrimeRatioError β := by
    dsimp [kappaPrimeRatioError, Infra.Ingredients.supergeoConstant]
    have hq : 0 < q β := by linarith [Infra.Ingredients.one_lt_q hβ hβ']
    positivity
  have hB_A : kappaPrimeRatioError β ≤ B := le_max_left _ _
  have hB_50 : 50 ≤ B := le_max_right _ _
  dsimp [kappaPrimeRatioError] at hB_A
  have hmax : max R R⁻¹ ≤ 1 + B * epsilon β Λ m := by
    apply max_le
    · have h := hratio.1
      exact h.trans (by
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hB_A he) 1)
    · have h := hratio.2
      exact h.trans (by
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hB_50 he) 1)
  dsimp [kappaPrimeNormalizedStepFactor, R]
  exact mul_le_mul_of_nonneg_right hmax
    (add_nonneg zero_le_one (Real.rpow_nonneg
      (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le _))

theorem KappaPrimeUniform.kappaPrimeNormalizedStepFactor_product_bound
    {β : ℝ} {Λ m d : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    (hm : 1 ≤ m) :
    (∏ i ∈ Finset.range d,
      kappaPrimeNormalizedStepFactor β Λ (m + i)) ≤
      Real.exp (max (kappaPrimeRatioError β) 50 * (128 / 127) +
        1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) := by
  let B := max (kappaPrimeRatioError β) 50
  let ρ := (128 : ℝ) ^ (-2 * gamma β)
  let r₀ : ℝ := 1 / 128
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hρlt : ρ < 1 := by
    dsimp [ρ]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith [hγ])
  have hr₀pos : 0 ≤ r₀ := by norm_num [r₀]
  have hr₀lt : r₀ < 1 := by norm_num [r₀]
  have hεpoint : ∀ i ∈ Finset.range d,
      epsilon β Λ (m + i) ≤ r₀ ^ i := by
    intro i hi
    have hε := KappaPrimeUniform.epsilon_le_128_rpow_neg hβ hβ' hΛ (m := m + i)
    have hindexNat : i ≤ m + i := by omega
    have hindex : (i : ℝ) ≤ ((m + i : ℕ) : ℝ) := by exact_mod_cast hindexNat
    have hexp : -((m + i : ℕ) : ℝ) ≤ -(i : ℝ) := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 128) hexp
    have hEq : (128 : ℝ) ^ (-(i : ℝ)) = r₀ ^ i := by
      dsimp [r₀]
      rw [KappaPrimeUniform.rpow_neg_nat_eq_inv_pow (by norm_num) i]
      norm_num
    exact hε.trans (hpow.trans_eq hEq)
  have hUpoint : ∀ i ∈ Finset.range d,
      epsilon β Λ (m + i + 1) ^ (2 * gamma β) ≤ ρ ^ i := by
    intro i hi
    let n := m + i + 1
    have hn : i ≤ n := by dsimp [n]; omega
    have hε := KappaPrimeUniform.epsilon_le_128_rpow_neg hβ hβ' hΛ (m := n)
    have hpowε : epsilon β Λ n ^ (2 * gamma β) ≤
        ((128 : ℝ) ^ (-(n : ℝ))) ^ (2 * gamma β) := by
      apply Real.rpow_le_rpow
      · exact (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le
      · exact hε
      · positivity
    have hnreal : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnexp : -(n : ℝ) * (2 * gamma β) ≤
        -(i : ℝ) * (2 * gamma β) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnreal) (le_of_lt hγ)]
    have hpowcmp := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 128) hnexp
    have hleft : ((128 : ℝ) ^ (-(n : ℝ))) ^ (2 * gamma β) =
        (128 : ℝ) ^ (-(n : ℝ) * (2 * gamma β)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 128)]
    have hright : ρ ^ i =
        (128 : ℝ) ^ (-(i : ℝ) * (2 * gamma β)) := by
      dsimp [ρ]
      rw [show -2 * gamma β = -(2 * gamma β) by ring]
      exact (KappaPrimeUniform.rpow_neg_nat_mul_eq_pow (x := 128)
        (p := 2 * gamma β) (by norm_num) i).symm
    calc
      epsilon β Λ n ^ (2 * gamma β) ≤
          ((128 : ℝ) ^ (-(n : ℝ))) ^ (2 * gamma β) := hpowε
      _ = (128 : ℝ) ^ (-(n : ℝ) * (2 * gamma β)) := hleft
      _ ≤ (128 : ℝ) ^ (-(i : ℝ) * (2 * gamma β)) := hpowcmp
      _ = ρ ^ i := hright.symm
  have hprodPoint : ∀ i ∈ Finset.range d,
      kappaPrimeNormalizedStepFactor β Λ (m + i) ≤
        (1 + B * epsilon β Λ (m + i)) *
          (1 + epsilon β Λ (m + i + 1) ^ (2 * gamma β)) := by
    intro i hi
    have hmi : 1 ≤ m + i := by omega
    simpa [B] using KappaPrimeUniform.kappaPrimeNormalizedStepFactor_bound hβ hβ' hΛ hmi
  have hfactorProd :
      Finset.prod (Finset.range d)
        (fun i => kappaPrimeNormalizedStepFactor β Λ (m + i)) ≤
      Finset.prod (Finset.range d) (fun i => 1 + B * epsilon β Λ (m + i)) *
        Finset.prod (Finset.range d)
          (fun i => 1 + epsilon β Λ (m + i + 1) ^ (2 * gamma β)) := by
    calc
      Finset.prod (Finset.range d)
          (fun i => kappaPrimeNormalizedStepFactor β Λ (m + i)) ≤
          Finset.prod (Finset.range d)
                (fun i => (1 + B * epsilon β Λ (m + i)) *
              (1 + epsilon β Λ (m + i + 1) ^ (2 * gamma β))) := by
                apply Finset.prod_le_prod₀
                · intro i hi
                  have he : 0 < epsilon β Λ (m + i) :=
                    Infra.Cutoff.epsilon_pos hβ hβ' hΛ
                  have hen : 0 < epsilon β Λ (m + i + 1) :=
                    Infra.Cutoff.epsilon_pos hβ hβ' hΛ
                  have hR : 0 <
                      (epsilon β Λ (m + i + 1) /
                        epsilon β Λ (m + i) ^ q β) ^ (β - gamma β) := by
                    apply Real.rpow_pos_of_pos
                    exact div_pos hen (Real.rpow_pos_of_pos he _)
                  dsimp [kappaPrimeNormalizedStepFactor]
                  exact mul_nonneg (le_trans hR.le (le_max_left _ _))
                    (by positivity)
                · exact hprodPoint
      _ = Finset.prod (Finset.range d)
            (fun i => 1 + B * epsilon β Λ (m + i)) *
          Finset.prod (Finset.range d)
            (fun i => 1 + epsilon β Λ (m + i + 1) ^ (2 * gamma β)) := by
              simpa using (Finset.prod_mul_distrib
                (s := Finset.range d)
                (f := fun i => 1 + B * epsilon β Λ (m + i))
                (g := fun i => 1 + epsilon β Λ (m + i + 1) ^ (2 * gamma β)))
  have hsumE :
      (∑ i ∈ Finset.range d, B * epsilon β Λ (m + i)) ≤ B * (128 / 127) := by
    calc
      (∑ i ∈ Finset.range d, B * epsilon β Λ (m + i)) ≤
          ∑ i ∈ Finset.range d, B * r₀ ^ i := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (hεpoint i hi) hB
      _ = B * (∑ i ∈ Finset.range d, r₀ ^ i) := by rw [Finset.mul_sum]
      _ ≤ B * (1 / (1 - r₀)) := by
            exact mul_le_mul_of_nonneg_left
              (KappaPrimeUniform.finite_geometric_sum_le hr₀pos hr₀lt d) hB
      _ = B * (128 / 127) := by norm_num [r₀]
  have hsumU :
      (∑ i ∈ Finset.range d,
        epsilon β Λ (m + i + 1) ^ (2 * gamma β)) ≤ 1 / (1 - ρ) := by
    calc
      (∑ i ∈ Finset.range d,
        epsilon β Λ (m + i + 1) ^ (2 * gamma β)) ≤
          ∑ i ∈ Finset.range d, ρ ^ i := by
            apply Finset.sum_le_sum
            exact hUpoint
      _ ≤ 1 / (1 - ρ) := KappaPrimeUniform.finite_geometric_sum_le hρpos.le hρlt d
  have hprodE :
      Finset.prod (Finset.range d) (fun i => 1 + B * epsilon β Λ (m + i)) ≤
        Real.exp (B * (128 / 127)) := by
    calc
      Finset.prod (Finset.range d) (fun i => 1 + B * epsilon β Λ (m + i)) ≤
          Real.exp (∑ i ∈ Finset.range d, B * epsilon β Λ (m + i)) :=
        Real.prod_one_add_le_exp_sum _ (by
          intro i
          exact mul_nonneg hB
            (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le)
      _ ≤ Real.exp (B * (128 / 127)) := Real.exp_le_exp.mpr hsumE
  have hprodU :
      Finset.prod (Finset.range d)
        (fun i => 1 + epsilon β Λ (m + i + 1) ^ (2 * gamma β)) ≤
        Real.exp (1 / (1 - ρ)) := by
    calc
      Finset.prod (Finset.range d)
          (fun i => 1 + epsilon β Λ (m + i + 1) ^ (2 * gamma β)) ≤
        Real.exp (∑ i ∈ Finset.range d,
            epsilon β Λ (m + i + 1) ^ (2 * gamma β)) :=
        Real.prod_one_add_le_exp_sum _ (by
          intro i
          exact Real.rpow_nonneg
            (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le _)
      _ ≤ Real.exp (1 / (1 - ρ)) := Real.exp_le_exp.mpr hsumU
  calc
    Finset.prod (Finset.range d)
        (fun i => kappaPrimeNormalizedStepFactor β Λ (m + i)) ≤
        Finset.prod (Finset.range d)
          (fun i => 1 + B * epsilon β Λ (m + i)) *
          Finset.prod (Finset.range d)
            (fun i => 1 + epsilon β Λ (m + i + 1) ^ (2 * gamma β)) := hfactorProd
    _ ≤ Real.exp (B * (128 / 127)) * Real.exp (1 / (1 - ρ)) := by
      apply mul_le_mul hprodE hprodU
      · exact Finset.prod_nonneg fun i hi =>
          add_nonneg zero_le_one (Real.rpow_nonneg
            (Infra.Cutoff.epsilon_pos hβ hβ' hΛ).le _)
      · exact Real.exp_nonneg _
    _ = Real.exp (B * (128 / 127) + 1 / (1 - ρ)) := by rw [← Real.exp_add]

/-- The reciprocal-symmetric normalized auxiliary chain has a uniform
β-dependent bound at every scale `1 ≤ m < M` with a permitted terminal value. -/
theorem kappaPrimeNormalizedSize_uniform_bound {β : ℝ} {Λ M : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpermitted : κ ∈ AVenhance.permittedInterval β Λ M)
    {m : ℕ} (hm : 1 ≤ m) (hmM : m < M) :
    kappaPrimeNormalizedSize β Λ κ m (M - m) ≤
      kappaPrimeUniformConstant β := by
  have hremNe : M - m ≠ 0 := by omega
  obtain ⟨d, hrem⟩ := Nat.exists_eq_succ_of_ne_zero hremNe
  let j := m + d
  have hM : j + 1 = M := by dsimp [j]; omega
  have hpermittedJ :
      κ ∈ AVenhance.permittedInterval β Λ (j + 1) := by
    simpa only [hM] using hpermitted
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hchain := KappaPrimeUniform.kappaPrimeNormalizedSize_chain_bound_to
    hβ hβ' hΛ hκ m d 1
  have hchain' :
      kappaPrimeNormalizedSize β Λ κ m (M - m) ≤
        (∏ i ∈ Finset.range d,
          kappaPrimeNormalizedStepFactor β Λ (m + i)) *
          kappaPrimeNormalizedSize β Λ κ j 1 := by
    simpa [hrem, j] using hchain
  have hprod := KappaPrimeUniform.kappaPrimeNormalizedStepFactor_product_bound
    (d := d) hβ hβ' hΛ hm
  have hend := KappaPrimeUniform.kappaPrimeNormalizedSize_endpoint_bound hβ hβ' hΛ hκ
    hpermittedJ hj
  have hendNonneg : 0 ≤ kappaPrimeNormalizedSize β Λ κ j 1 := by
    unfold kappaPrimeNormalizedSize
    exact le_max_of_le_left
      (kappaPrimeNormalized_pos hβ hβ' hΛ hκ j 1).le
  have hexpNonneg : 0 ≤ Real.exp
      (max (kappaPrimeRatioError β) 50 * (128 / 127) +
        1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) := Real.exp_nonneg _
  calc
    kappaPrimeNormalizedSize β Λ κ m (M - m) ≤
        (∏ i ∈ Finset.range d,
          kappaPrimeNormalizedStepFactor β Λ (m + i)) *
          kappaPrimeNormalizedSize β Λ κ j 1 := hchain'
    _ ≤ Real.exp
          (max (kappaPrimeRatioError β) 50 * (128 / 127) +
            1 / (1 - (128 : ℝ) ^ (-2 * gamma β))) *
          kappaPrimeEndpointConstant β := by
      exact mul_le_mul hprod hend hendNonneg hexpNonneg
    _ = kappaPrimeUniformConstant β := by
      dsimp [kappaPrimeUniformConstant]
      ring

/-- The auxiliary sequence satisfies two-sided uniform scale bounds on the
corrected range `1 ≤ m < M`. The scale is `a_m ε_m^(2+γ)`. -/
theorem kappaPrimeAt_uniform_bounds {β : ℝ} {Λ M : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ)
    {κ : ℝ} (hκ : 0 < κ)
    (hpermitted : κ ∈ AVenhance.permittedInterval β Λ M)
    {m : ℕ} (hm : 1 ≤ m) (hmM : m < M) :
    (9 / 80 / kappaPrimeUniformConstant β) *
        (a β Λ m * epsilon β Λ m ^ (2 + gamma β)) ≤
      kappaPrimeAt β Λ κ m (M - m) ∧
    kappaPrimeAt β Λ κ m (M - m) ≤
      kappaPrimeUniformConstant β *
        (a β Λ m * epsilon β Λ m ^ (2 + gamma β)) := by
  have hsize := kappaPrimeNormalizedSize_uniform_bound
    hβ hβ' hΛ hκ hpermitted hm hmM
  let z := kappaPrimeNormalized β Λ κ m (M - m)
  let e := epsilon β Λ m
  let U := kappaPrimeUniformConstant β
  have hzpos : 0 < z := by
    dsimp [z]
    exact kappaPrimeNormalized_pos hβ hβ' hΛ hκ m (M - m)
  have he : 0 < e := by dsimp [e]; exact Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hq : 0 < q β := by
    linarith [Infra.Ingredients.one_lt_q hβ hβ']
  have herr : 0 ≤ kappaPrimeRatioError β := by
    dsimp [kappaPrimeRatioError, Infra.Ingredients.supergeoConstant]
    positivity
  have hγ : 0 < gamma β := Infra.Ingredients.gamma_pos hβ hβ'
  have hρlt : (128 : ℝ) ^ (-2 * gamma β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith [hγ])
  have hden : 0 < 1 - (128 : ℝ) ^ (-2 * gamma β) := sub_pos.mpr hρlt
  have hendpointPos : 0 < kappaPrimeEndpointConstant β := by
    have hleft : 0 <
        (1 + kappaPrimeRatioError β / 128) * (2 + 2 * (9 / 80)) := by
      positivity
    exact lt_of_lt_of_le hleft (le_max_left _ _)
  have hUpos : 0 < U := by
    dsimp [U, kappaPrimeUniformConstant]
    exact mul_pos hendpointPos (Real.exp_pos _)
  have hzUpper : z ≤ U := by
    have h := le_trans (le_max_left z ((9 / 80) / z)) hsize
    simpa [z] using h
  have hzInvUpper : (9 / 80) / z ≤ U := by
    have h := le_trans (le_max_right z ((9 / 80) / z)) hsize
    simpa [z] using h
  have hzLower : 9 / 80 / U ≤ z := by
    apply (div_le_iff₀ hUpos).2
    have hmul : (9 : ℝ) / 80 ≤ U * z :=
      (div_le_iff₀ hzpos).1 hzInvUpper
    nlinarith [hmul]
  have hscaleEq :
      epsilon β Λ m ^ (β + gamma β) =
        a β Λ m * epsilon β Λ m ^ (2 + gamma β) := by
    change epsilon β Λ m ^ (β + gamma β) =
      epsilon β Λ m ^ (β - 2) * epsilon β Λ m ^ (2 + gamma β)
    rw [← Real.rpow_add he]
    congr 1
    ring
  have hκEq : kappaPrimeAt β Λ κ m (M - m) =
      z * e ^ (β + gamma β) := by
    dsimp [z, kappaPrimeNormalized, e]
    exact (div_mul_cancel₀ _
      (ne_of_gt (Real.rpow_pos_of_pos he (β + gamma β)))).symm
  constructor
  · rw [hκEq, ← hscaleEq]
    exact mul_le_mul_of_nonneg_right hzLower (Real.rpow_nonneg he.le _)
  · rw [hκEq, ← hscaleEq]
    exact mul_le_mul_of_nonneg_right hzUpper (Real.rpow_nonneg he.le _)

end AVenhance.Infra.Section3

end
