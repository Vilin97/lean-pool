/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaAnalyticInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaAnalyticRecursion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Scalars

/-! Radius bookkeeping for the analytic derivative induction. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section4

/-- Base scale in the temperature analyticity radius bound. -/
def thetaAnalyticRadiusBase (c : ℝ) : ℝ :=
  max (2 ^ 15 / Real.sqrt c) (2 ^ 9)

/-- Analytic radius bound combining the spatial scale and the initial radius. -/
def thetaAnalyticRadius (c e γ R : ℝ) : ℝ :=
  max (thetaAnalyticRadiusBase c * e ^ (-1 - γ / 2)) (2 / R)

theorem ThetaAnalyticScale.theta_a_epsilon_sq_div_kappa
    {β κ c : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (hc : 0 < c)
    (hκ : c * (AVenhance.a β I.Λ (m - 1) *
      AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β)) ≤ κ) :
    AVenhance.a β I.Λ (m - 1) *
        AVenhance.epsilon β I.Λ (m - 1) ^ 2 / κ ≤
      c⁻¹ * AVenhance.epsilon β I.Λ (m - 1) ^ (-AVenhance.gamma β) := by
  let e := AVenhance.epsilon β I.Λ (m - 1)
  have he : 0 < e := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hratio := theta_second_stream_derivative_over_kappa I hc (by simpa [e] using hκ)
  have ha : AVenhance.a β I.Λ (m - 1) = e ^ (β - 2) := by
    simp [e, AVenhance.a]
  have hratio' : e ^ (β - 2) / κ ≤
      c⁻¹ * e ^ (-2 - AVenhance.gamma β) := by
    simpa [e] using hratio
  have hmul := mul_le_mul_of_nonneg_left hratio'
    (by positivity : 0 ≤ e ^ 2)
  have hpow : e ^ 2 * e ^ (-2 - AVenhance.gamma β) =
      e ^ (-AVenhance.gamma β) := by
    rw [← Real.rpow_natCast e 2]
    rw [← Real.rpow_add he]
    congr 1
    ring
  calc
    AVenhance.a β I.Λ (m - 1) * e ^ 2 / κ =
        e ^ 2 * (e ^ (β - 2) / κ) := by rw [ha]; ring
    _ ≤ e ^ 2 * (c⁻¹ * e ^ (-2 - AVenhance.gamma β)) := hmul
    _ = c⁻¹ * (e ^ 2 * e ^ (-2 - AVenhance.gamma β)) := by ring
    _ = c⁻¹ * e ^ (-AVenhance.gamma β) := by rw [hpow]

theorem ThetaAnalyticScale.theta_stream_coeff_over_kappa_factorial
    {β κ c : ℝ} {m q : ℕ} (I : AVenhance.Ingredients β)
    (hc : 0 < c)
    (hκ : c * (AVenhance.a β I.Λ (m - 1) *
      AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β)) ≤ κ) :
    (thetaPotentialDerivativeCoefficient (m := m) I q / κ) /
        (q.factorial : ℝ) ≤
      (2 ^ 5 / c) * AVenhance.epsilon β I.Λ (m - 1) ^
        (-AVenhance.gamma β) *
          (2 ^ 8 / AVenhance.epsilon β I.Λ (m - 1)) ^ q := by
  let e := AVenhance.epsilon β I.Λ (m - 1)
  have he : 0 < e := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hAe := ThetaAnalyticScale.theta_a_epsilon_sq_div_kappa I hc (by simpa [e] using hκ)
  have hfac : (q.factorial : ℝ) ≠ 0 := by positivity
  have hcoeff : thetaPotentialDerivativeCoefficient (m := m) I q =
      2 ^ 5 * (AVenhance.a β I.Λ (m - 1) * e ^ 2) *
        (q.factorial : ℝ) * (2 ^ 8 / e) ^ q := by
    change 2 ^ 5 * AVenhance.a β I.Λ (m - 1) * e ^ 2 *
        (q.factorial : ℝ) * (2 ^ 8 * e⁻¹) ^ q = _
    rw [show (2 ^ 8 : ℝ) * e⁻¹ = (2 ^ 8 : ℝ) / e by rw [div_eq_mul_inv]]
    ring
  rw [hcoeff]
  have hfactor : 0 ≤ 2 ^ 5 * (q.factorial : ℝ) * (2 ^ 8 / e) ^ q := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hAe hfactor
  have hκpos : 0 < κ := by
    have hepow : 0 < e ^ (2 + AVenhance.gamma β) := Real.rpow_pos_of_pos he _
    have hap : 0 < AVenhance.a β I.Λ (m - 1) := by
      rw [AVenhance.a]
      exact Real.rpow_pos_of_pos he _
    exact lt_of_lt_of_le (mul_pos hc (mul_pos hap hepow)) hκ
  calc
    (2 ^ 5 * (AVenhance.a β I.Λ (m - 1) * e ^ 2) *
        (q.factorial : ℝ) * (2 ^ 8 / e) ^ q / κ) /
        (q.factorial : ℝ) =
      (2 ^ 5 * (2 ^ 8 / e) ^ q) *
        (AVenhance.a β I.Λ (m - 1) * e ^ 2 / κ) := by
          field_simp [hfac]
    _ ≤ (2 ^ 5 * (2 ^ 8 / e) ^ q) *
        (c⁻¹ * e ^ (-AVenhance.gamma β)) :=
          mul_le_mul_of_nonneg_left hAe (by positivity)
    _ = (2 ^ 5 / c) * e ^ (-AVenhance.gamma β) *
        (2 ^ 8 / e) ^ q := by
          rw [div_eq_mul_inv]
          ring

theorem ThetaAnalyticScale.theta_radius_ratio
    {e γ A L : ℝ} {q : ℕ}
    (he : 0 < e) (he1 : e ≤ 1) (hγ : 0 ≤ γ)
    (hA : 2 ^ 9 ≤ A) (hL : A * e ^ (-1 - γ / 2) ≤ L)
    (hq : 2 ≤ q) :
    e ^ (-γ) * (2 ^ 8 / (e * L)) ^ q ≤
      (2 ^ 8 / A) ^ 2 * (1 / 2 : ℝ) ^ (q - 2) := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hpowmul : e * e ^ (-1 - γ / 2) = e ^ (-γ / 2) := by
    calc
      e * e ^ (-1 - γ / 2) = e ^ (1 : ℝ) * e ^ (-1 - γ / 2) := by
        rw [Real.rpow_one]
      _ = e ^ (1 + (-1 - γ / 2)) := by rw [← Real.rpow_add he]
      _ = e ^ (-γ / 2) := by congr 1; ring
  have hLmul : A * e ^ (-γ / 2) ≤ e * L := by
    calc
      A * e ^ (-γ / 2) = A * (e * e ^ (-1 - γ / 2)) := by rw [hpowmul]
      _ = e * (A * e ^ (-1 - γ / 2)) := by ring
      _ ≤ e * L := mul_le_mul_of_nonneg_left hL he.le
  have hratio : 2 ^ 8 / (e * L) ≤ (2 ^ 8 / A) * e ^ (γ / 2) := by
    have hden : 0 < e * L := mul_pos he hLpos
    have hden' : 0 < A * e ^ (-γ / 2) := by positivity
    calc
      2 ^ 8 / (e * L) ≤ 2 ^ 8 / (A * e ^ (-γ / 2)) :=
        div_le_div_of_nonneg_left (by positivity) hden' hLmul
      _ = (2 ^ 8 / A) * e ^ (γ / 2) := by
        have hpowinv : e ^ (-(γ / 2)) * e ^ (γ / 2) = 1 := by
          calc
            e ^ (-(γ / 2)) * e ^ (γ / 2) =
                e ^ (-(γ / 2) + (γ / 2)) := by rw [← Real.rpow_add he]
            _ = e ^ 0 := by
              rw [show -(γ / 2) + γ / 2 = 0 by ring]
              simp
            _ = 1 := by simp
        field_simp [ne_of_gt hApos,
          ne_of_gt (Real.rpow_pos_of_pos he (γ / 2))]
        exact hpowinv.symm
  have hrbase : 0 ≤ 2 ^ 8 / A := by positivity
  have hrsmall : 2 ^ 8 / A ≤ 1 / 2 := by
    apply (div_le_iff₀ hApos).2
    nlinarith [hA]
  have hpow : e ^ (-γ) * (e ^ (γ / 2)) ^ q =
      e ^ (γ * ((q : ℝ) / 2 - 1)) := by
    rw [← Real.rpow_natCast (e ^ (γ / 2)) q, ← Real.rpow_mul he.le,
      ← Real.rpow_add he]
    congr 1
    ring
  have hexp : 0 ≤ γ * ((q : ℝ) / 2 - 1) := by
    apply mul_nonneg hγ
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hpowle : e ^ (γ * ((q : ℝ) / 2 - 1)) ≤ 1 :=
    Real.rpow_le_one he.le he1 hexp
  have hqsplit : q = 2 + (q - 2) := by omega
  have hbasepow : (2 ^ 8 / A) ^ q ≤
      (2 ^ 8 / A) ^ 2 * (1 / 2 : ℝ) ^ (q - 2) := by
    rw [hqsplit, pow_add]
    have hsub : 2 + (q - 2) - 2 = q - 2 := by omega
    rw [hsub]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hrbase hrsmall (q - 2))
      (pow_nonneg hrbase _)
  calc
    e ^ (-γ) * (2 ^ 8 / (e * L)) ^ q ≤
        e ^ (-γ) * ((2 ^ 8 / A) * e ^ (γ / 2)) ^ q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio q)
        (Real.rpow_nonneg he.le _)
    _ = (2 ^ 8 / A) ^ q *
          (e ^ (-γ) * (e ^ (γ / 2)) ^ q) := by ring
    _ ≤ (2 ^ 8 / A) ^ q := by
      have hnonneg : 0 ≤ (2 ^ 8 / A) ^ q := pow_nonneg hrbase _
      rw [hpow]
      nlinarith [hpowle, hnonneg]
    _ ≤ (2 ^ 8 / A) ^ 2 * (1 / 2 : ℝ) ^ (q - 2) := hbasepow

theorem ThetaAnalyticScale.theta_potential_two_eq
    {β : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (he : 0 < AVenhance.epsilon β I.Λ (m - 1)) :
    thetaPotentialDerivativeCoefficient (m := m) I 2 =
      2 ^ 22 * AVenhance.a β I.Λ (m - 1) := by
  rw [thetaPotentialDerivativeCoefficient]
  norm_num [Nat.factorial]
  field_simp [ne_of_gt he]
  ring

theorem ThetaAnalyticScale.theta_sqrt_potential_two_over_kappa
    {β κ c : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (hc : 0 < c)
    (hκ : c * (AVenhance.a β I.Λ (m - 1) *
      AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β)) ≤ κ) :
    Real.sqrt (thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) ≤
      (2 ^ 11 / Real.sqrt c) *
        AVenhance.epsilon β I.Λ (m - 1) ^ (-1 - AVenhance.gamma β / 2) := by
  let e := AVenhance.epsilon β I.Λ (m - 1)
  let γ := AVenhance.gamma β
  have he : 0 < e := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hM2 := ThetaAnalyticScale.theta_potential_two_eq I he
  have hratio := theta_second_stream_derivative_over_kappa I hc
    (by simpa [AVenhance.a, e] using hκ)
  have hsq : (e ^ (-1 - γ / 2)) ^ 2 = e ^ (-2 - γ) := by
    rw [← Real.rpow_natCast (e ^ (-1 - γ / 2)) 2, ← Real.rpow_mul he.le]
    congr 1
    ring
  have hconst : (2 ^ 11 / Real.sqrt c) ^ 2 = 2 ^ 22 / c := by
    rw [div_pow, Real.sq_sqrt hc.le]
    norm_num
  rw [hM2]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  have hmul := mul_le_mul_of_nonneg_left hratio
    (by norm_num : 0 ≤ (2 ^ 22 : ℝ))
  have htarget :
      (2 ^ 22 * AVenhance.a β I.Λ (m - 1)) / κ ≤
        (2 ^ 22 / c) * e ^ (-2 - γ) := by
    calc
      (2 ^ 22 * AVenhance.a β I.Λ (m - 1)) / κ =
          2 ^ 22 * (AVenhance.a β I.Λ (m - 1) / κ) := by ring
      _ ≤ (2 ^ 22 / c) * e ^ (-2 - γ) := by
        simpa [AVenhance.a, e, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  calc
    (2 ^ 22 * AVenhance.a β I.Λ (m - 1)) / κ ≤
        (2 ^ 22 / c) * e ^ (-2 - γ) := htarget
    _ = ((2 ^ 11 / Real.sqrt c) * e ^ (-1 - γ / 2)) ^ 2 := by
      rw [mul_pow, hconst, hsq]

theorem ThetaAnalyticScale.theta_q1_factorial_scale
    {β κ c R₀ : ℝ} {m n : ℕ} (I : AVenhance.Ingredients β)
    (hc : 0 < c) (hκ : c * (AVenhance.a β I.Λ (m - 1) *
      AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β)) ≤ κ)
    (hn : 1 ≤ n) :
    let e := AVenhance.epsilon β I.Λ (m - 1)
    let L := thetaAnalyticRadius c e (AVenhance.gamma β) R₀
    4 * Real.sqrt ((n : ℝ) *
        thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) *
        ((n - 1).factorial : ℝ) * L ^ (n - 1) ≤
      (1 / 4 : ℝ) * (n.factorial : ℝ) * L ^ n := by
  dsimp
  let e := AVenhance.epsilon β I.Λ (m - 1)
  let γ := AVenhance.gamma β
  let A := thetaAnalyticRadiusBase c
  let L := thetaAnalyticRadius c e γ R₀
  have he : 0 < e := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hA1 : 2 ^ 15 / Real.sqrt c ≤ A := by
    dsimp [A, thetaAnalyticRadiusBase]
    exact le_max_left _ _
  have hL1 : A * e ^ (-1 - γ / 2) ≤ L := by
    dsimp [L, thetaAnalyticRadius]
    exact le_max_left _ _
  have hApos : 0 < A := lt_of_lt_of_le (by positivity) hA1
  have hLpos : 0 < L := lt_of_lt_of_le
    (mul_pos hApos (Real.rpow_pos_of_pos he _)) hL1
  have hsqrtM := ThetaAnalyticScale.theta_sqrt_potential_two_over_kappa I hc hκ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrtN : Real.sqrt (n : ℝ) ≤ n := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [hncast]
  have hroot :
      Real.sqrt ((n : ℝ) *
          thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) ≤
        (n : ℝ) * (2 ^ 11 / Real.sqrt c) * e ^ (-1 - γ / 2) := by
    have hsplit :
        (n : ℝ) * thetaPotentialDerivativeCoefficient (m := m) I 2 / κ =
          (n : ℝ) *
            (thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) := by ring
    rw [hsplit, Real.sqrt_mul hnR.le]
    calc
      Real.sqrt (n : ℝ) *
          Real.sqrt (thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) ≤
        (n : ℝ) *
          ((2 ^ 11 / Real.sqrt c) * e ^ (-1 - γ / 2)) :=
            mul_le_mul hsqrtN hsqrtM (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hbase : 4 * (2 ^ 11 / Real.sqrt c) *
      e ^ (-1 - γ / 2) ≤ L / 4 := by
    have hrad : (2 ^ 15 / Real.sqrt c) *
        e ^ (-1 - γ / 2) ≤ L :=
      le_trans (mul_le_mul_of_nonneg_right hA1 (by positivity)) hL1
    calc
      4 * (2 ^ 11 / Real.sqrt c) * e ^ (-1 - γ / 2) =
          ((2 ^ 15 / Real.sqrt c) * e ^ (-1 - γ / 2)) / 4 := by ring
      _ ≤ L / 4 := div_le_div_of_nonneg_right hrad (by norm_num)
  have hfacNat' : n.factorial = n * (n - 1).factorial := by
    calc
      n.factorial = (n - 1 + 1).factorial := by rw [Nat.sub_add_cancel hn]
      _ = (n - 1 + 1) * (n - 1).factorial := Nat.factorial_succ _
      _ = n * (n - 1).factorial := by rw [Nat.sub_add_cancel hn]
  have hfac : (n : ℝ) * ((n - 1).factorial : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast hfacNat'.symm
  have hLpow : L ^ (n - 1) * L = L ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hnonneg : 0 ≤ (n.factorial : ℝ) * L ^ (n - 1) := by positivity
  calc
    4 * Real.sqrt ((n : ℝ) *
        thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) *
        ((n - 1).factorial : ℝ) * L ^ (n - 1) ≤
      4 * ((n : ℝ) * (2 ^ 11 / Real.sqrt c) *
        e ^ (-1 - γ / 2)) * ((n - 1).factorial : ℝ) * L ^ (n - 1) := by
          gcongr
    _ = ((n : ℝ) * ((n - 1).factorial : ℝ)) *
        (4 * (2 ^ 11 / Real.sqrt c) * e ^ (-1 - γ / 2)) *
          L ^ (n - 1) := by ring
    _ = (n.factorial : ℝ) *
        (4 * (2 ^ 11 / Real.sqrt c) * e ^ (-1 - γ / 2)) *
          L ^ (n - 1) := by rw [hfac]
    _ ≤ (n.factorial : ℝ) * (L / 4) * L ^ (n - 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbase (by positivity))
        (pow_nonneg hLpos.le _)
    _ = (1 / 4 : ℝ) * (n.factorial : ℝ) * L ^ n := by
      calc
        (n.factorial : ℝ) * (L / 4) * L ^ (n - 1) =
            (1 / 4 : ℝ) * (n.factorial : ℝ) *
              (L ^ (n - 1) * L) := by ring
        _ = _ := by rw [hLpow]

theorem ThetaAnalyticScale.theta_shifted_half_geometric_sum (n : ℕ) (hn : 1 ≤ n) :
    (∑ q ∈ Finset.range (n + 1),
      if 2 ≤ q then (1 / 2 : ℝ) ^ (q - 2) else 0) ≤ 2 := by
  have hsplit : n + 1 = 2 + (n - 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ q ∈ Finset.range 2,
      if 2 ≤ q then (1 / 2 : ℝ) ^ (q - 2) else 0) = 0 := by
    norm_num [Finset.sum_range_succ]
  rw [hfirst]
  have hrest :
      (∑ j ∈ Finset.range (n - 1),
        (if 2 ≤ 2 + j then (1 / 2 : ℝ) ^ (2 + j - 2) else 0)) =
      ∑ j ∈ Finset.range (n - 1), (1 / 2 : ℝ) ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp
  rw [hrest]
  have hgeom := AVenhance.Infra.Construction.sum_geometric_le
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) (n - 1)
  norm_num at hgeom ⊢
  exact hgeom.trans (by norm_num)

theorem ThetaAnalyticScale.theta_high_term_radius_bound
    {β κ c R₀ : ℝ} {m n q : ℕ} (I : AVenhance.Ingredients β)
    (hc : 0 < c)
    (hκ : c * (AVenhance.a β I.Λ (m - 1) *
      AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β)) ≤ κ)
    (hnq : 2 ≤ q) (hqle : q ≤ n)
    (hA : 2 ^ 9 ≤ thetaAnalyticRadiusBase c)
    (hL : thetaAnalyticRadiusBase c *
      AVenhance.epsilon β I.Λ (m - 1) ^
        (-1 - AVenhance.gamma β / 2) ≤
      thetaAnalyticRadius c (AVenhance.epsilon β I.Λ (m - 1))
        (AVenhance.gamma β) R₀) :
    let e := AVenhance.epsilon β I.Λ (m - 1)
    let γ := AVenhance.gamma β
    let A := thetaAnalyticRadiusBase c
    let L := thetaAnalyticRadius c e γ R₀
    4 * ((n.choose q : ℕ) : ℝ) *
        (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
        ((n - q).factorial : ℝ) * L ^ (n - q) ≤
      ((n.factorial : ℝ) * L ^ n) *
        ((2 ^ 7 / c) * (2 ^ 8 / A) ^ 2 * (1 / 2 : ℝ) ^ (q - 2)) := by
  dsimp
  let e := AVenhance.epsilon β I.Λ (m - 1)
  let γ := AVenhance.gamma β
  let A := thetaAnalyticRadiusBase c
  let L := thetaAnalyticRadius c e γ R₀
  have he : 0 < e := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : e ≤ 1 := AVenhance.Infra.Construction.epsilon_le_one
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hγ : 0 ≤ γ := (AVenhance.Infra.Ingredients.gamma_pos
    I.one_lt_beta I.beta_lt).le
  have hA' : 2 ^ 9 ≤ A := by simpa [A] using hA
  have hL' : A * e ^ (-1 - γ / 2) ≤ L := by simpa [A, L, e, γ] using hL
  have hLpos : 0 < L := by
    have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA'
    exact lt_of_lt_of_le (mul_pos hApos (Real.rpow_pos_of_pos he _)) hL'
  have hcoeff := ThetaAnalyticScale.theta_stream_coeff_over_kappa_factorial
    (I := I) (q := q) hc hκ
  have hcoeffL :
      ((thetaPotentialDerivativeCoefficient (m := m) I q / κ) /
          (q.factorial : ℝ)) / L ^ q ≤
        (2 ^ 5 / c) * e ^ (-γ) * (2 ^ 8 / (e * L)) ^ q := by
    have hLpowpos : 0 < L ^ q := by positivity
    calc
      ((thetaPotentialDerivativeCoefficient (m := m) I q / κ) /
          (q.factorial : ℝ)) / L ^ q ≤
        ((2 ^ 5 / c) * e ^ (-γ) * (2 ^ 8 / e) ^ q) / L ^ q :=
          div_le_div_of_nonneg_right hcoeff (by positivity)
      _ = (2 ^ 5 / c) * e ^ (-γ) * (2 ^ 8 / (e * L)) ^ q := by
        have hbase : (2 ^ 8 / e) / L = 2 ^ 8 / (e * L) := by
          field_simp [ne_of_gt he, ne_of_gt hLpos]
        have hpowdiv : (2 ^ 8 / e) ^ q / L ^ q =
            (2 ^ 8 / (e * L)) ^ q := by
          rw [← div_pow, hbase, div_pow]
        rw [mul_div_assoc, hpowdiv]
  have hrad := ThetaAnalyticScale.theta_radius_ratio he he1 hγ hA' hL' hnq
  have hscaled :
      4 * (((thetaPotentialDerivativeCoefficient (m := m) I q / κ) /
          (q.factorial : ℝ)) / L ^ q) ≤
        (2 ^ 7 / c) * (2 ^ 8 / A) ^ 2 * (1 / 2 : ℝ) ^ (q - 2) := by
    calc
      _ ≤ 4 * ((2 ^ 5 / c) * e ^ (-γ) *
          (2 ^ 8 / (e * L)) ^ q) :=
        mul_le_mul_of_nonneg_left hcoeffL (by norm_num)
      _ ≤ _ := by
        have hc0 : 0 ≤ 2 ^ 7 / c := by positivity
        have hratio' := mul_le_mul_of_nonneg_left hrad hc0
        convert hratio' using 1 <;> ring
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hqle
  have hchoose :
      ((n.choose q : ℕ) : ℝ) * (q.factorial : ℝ) *
        ((n - q).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast hchooseNat
  have hqfacpos : 0 < (q.factorial : ℝ) := by positivity
  have hfac :
      ((n.choose q : ℕ) : ℝ) * ((n - q).factorial : ℝ) =
        (n.factorial : ℝ) / (q.factorial : ℝ) := by
    apply (eq_div_iff (ne_of_gt hqfacpos)).2
    nlinarith [hchoose]
  have hpow : L ^ n = L ^ q * L ^ (n - q) := by
    calc
      L ^ n = L ^ (q + (n - q)) := by congr 1; omega
      _ = L ^ q * L ^ (n - q) := by rw [pow_add]
  have hcomb :
      ((n.choose q : ℕ) : ℝ) *
          (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
          ((n - q).factorial : ℝ) =
        ((n.factorial : ℝ) / (q.factorial : ℝ)) *
          (thetaPotentialDerivativeCoefficient (m := m) I q / κ) := by
    calc
      _ = (((n.choose q : ℕ) : ℝ) *
          ((n - q).factorial : ℝ)) *
          (thetaPotentialDerivativeCoefficient (m := m) I q / κ) := by ring
      _ = _ := by rw [hfac]
  have hident :
      4 * ((n.choose q : ℕ) : ℝ) *
          (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
          ((n - q).factorial : ℝ) * L ^ (n - q) =
        ((n.factorial : ℝ) * L ^ n) *
          (4 * (((thetaPotentialDerivativeCoefficient (m := m) I q / κ) /
            (q.factorial : ℝ)) / L ^ q)) := by
    calc
      _ = 4 * (((n.factorial : ℝ) / (q.factorial : ℝ)) *
          (thetaPotentialDerivativeCoefficient (m := m) I q / κ)) *
          L ^ (n - q) := by rw [← hcomb]; ring
      _ = _ := by
        field_simp [ne_of_gt hLpos, hqfacpos.ne']
        rw [hpow]
        ring
  have hDnonneg : 0 ≤ (n.factorial : ℝ) * L ^ n := by positivity
  calc
    4 * ((n.choose q : ℕ) : ℝ) *
        (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
        ((n - q).factorial : ℝ) * L ^ (n - q) =
      ((n.factorial : ℝ) * L ^ n) *
        (4 * (((thetaPotentialDerivativeCoefficient (m := m) I q / κ) /
          (q.factorial : ℝ)) / L ^ q)) := hident
    _ ≤ ((n.factorial : ℝ) * L ^ n) *
        ((2 ^ 7 / c) * (2 ^ 8 / A) ^ 2 * (1 / 2 : ℝ) ^ (q - 2)) :=
          mul_le_mul_of_nonneg_left hscaled hDnonneg

theorem ThetaAnalyticScale.theta_qhigh_factorial_scale
    {β κ c R₀ : ℝ} {m n : ℕ} (I : AVenhance.Ingredients β)
    (hc : 0 < c) (hκ : c * (AVenhance.a β I.Λ (m - 1) *
      AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β)) ≤ κ)
    (hn : 1 ≤ n) :
    let e := AVenhance.epsilon β I.Λ (m - 1)
    let L := thetaAnalyticRadius c e (AVenhance.gamma β) R₀
    4 * (∑ q ∈ Finset.range (n + 1),
      if 2 ≤ q then
        ((n.choose q : ℕ) : ℝ) *
          (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
            ((n - q).factorial : ℝ) * L ^ (n - q)
      else 0) ≤
      (1 / 4 : ℝ) * (n.factorial : ℝ) * L ^ n := by
  dsimp
  let e := AVenhance.epsilon β I.Λ (m - 1)
  let γ := AVenhance.gamma β
  let A := thetaAnalyticRadiusBase c
  let L := thetaAnalyticRadius c e γ R₀
  have hA1 : 2 ^ 15 / Real.sqrt c ≤ A := by
    dsimp [A, thetaAnalyticRadiusBase]
    exact le_max_left _ _
  have hA2 : 2 ^ 9 ≤ A := by
    dsimp [A, thetaAnalyticRadiusBase]
    exact le_max_right _ _
  have hL1 : A * e ^ (-1 - γ / 2) ≤ L := by
    dsimp [L, thetaAnalyticRadius]
    exact le_max_left _ _
  have hgeom := ThetaAnalyticScale.theta_shifted_half_geometric_sum n hn
  let K := (2 ^ 7 / c) * (2 ^ 8 / A) ^ 2
  have hKnonneg : 0 ≤ K := by positivity
  have hKsmall : K * 2 ≤ 1 / 4 := by
    have hc0 : 0 < c := hc
    have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
    have hApos : 0 < A := lt_of_lt_of_le (by positivity) hA1
    have hratio : 2 ^ 8 / A ≤ Real.sqrt c / 2 ^ 7 := by
      apply (div_le_iff₀ hApos).2
      have hmul := mul_le_mul_of_nonneg_right hA1 hsqrtc.le
      have hmul' : (2 : ℝ) ^ 15 ≤ A * Real.sqrt c := by
        field_simp [ne_of_gt hsqrtc] at hmul
        nlinarith [hmul]
      nlinarith [hmul']
    have hratioSq : (2 ^ 8 / A) ^ 2 ≤ c / (2 ^ 7) ^ 2 := by
      calc
        (2 ^ 8 / A) ^ 2 ≤ (Real.sqrt c / 2 ^ 7) ^ 2 :=
          by simpa [pow_two] using
            (mul_self_le_mul_self (by positivity) hratio)
        _ = c / (2 ^ 7) ^ 2 := by
          rw [div_pow, Real.sq_sqrt hc.le]
    dsimp [K]
    have hbound : (2 ^ 7 / c) * (c / (2 ^ 7) ^ 2) * 2 ≤ 1 / 4 := by
      field_simp [ne_of_gt hc0]
      norm_num
    calc
      (2 ^ 7 / c) * (2 ^ 8 / A) ^ 2 * 2 ≤
          (2 ^ 7 / c) * (c / (2 ^ 7) ^ 2) * 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratioSq (by positivity)) (by norm_num)
      _ ≤ 1 / 4 := hbound
  have htermSum :
      4 * (∑ q ∈ Finset.range (n + 1),
        if 2 ≤ q then
          ((n.choose q : ℕ) : ℝ) *
            (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
              ((n - q).factorial : ℝ) * L ^ (n - q)
        else 0) ≤
      ((n.factorial : ℝ) * L ^ n) *
        (K * (∑ q ∈ Finset.range (n + 1),
          if 2 ≤ q then (1 / 2 : ℝ) ^ (q - 2) else 0)) := by
    calc
      _ = ∑ q ∈ Finset.range (n + 1),
          if 2 ≤ q then
            4 * (((n.choose q : ℕ) : ℝ) *
              (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
                ((n - q).factorial : ℝ) * L ^ (n - q))
          else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            by_cases hq2 : 2 ≤ q <;> simp [hq2]
      _ ≤ ∑ q ∈ Finset.range (n + 1),
          if 2 ≤ q then
            ((n.factorial : ℝ) * L ^ n) *
              (K * (1 / 2 : ℝ) ^ (q - 2))
          else 0 := by
            apply Finset.sum_le_sum
            intro q hq
            by_cases hq2 : 2 ≤ q
            · have hqle : q ≤ n := by simp only [Finset.mem_range] at hq; omega
              have hbound := ThetaAnalyticScale.theta_high_term_radius_bound
                (I := I) (m := m) (n := n) (q := q) hc hκ hq2 hqle hA2 hL1
              simpa [hq2, K, mul_assoc, mul_left_comm, mul_comm] using hbound
            · simp [hq2]
      _ = ((n.factorial : ℝ) * L ^ n) *
          (K * (∑ q ∈ Finset.range (n + 1),
            if 2 ≤ q then (1 / 2 : ℝ) ^ (q - 2) else 0)) := by
            calc
              _ = ∑ q ∈ Finset.range (n + 1),
                  ((n.factorial : ℝ) * L ^ n) *
                    (K * (if 2 ≤ q then (1 / 2 : ℝ) ^ (q - 2) else 0)) := by
                      apply Finset.sum_congr rfl
                      intro q hq
                      by_cases hq2 : 2 ≤ q <;> simp [hq2]
              _ = ((n.factorial : ℝ) * L ^ n) *
                  ∑ q ∈ Finset.range (n + 1),
                    K * (if 2 ≤ q then (1 / 2 : ℝ) ^ (q - 2) else 0) := by
                      rw [← Finset.mul_sum]
              _ = ((n.factorial : ℝ) * L ^ n) *
                  (K * (∑ q ∈ Finset.range (n + 1),
                    if 2 ≤ q then (1 / 2 : ℝ) ^ (q - 2) else 0)) := by
                      rw [← Finset.mul_sum]
  have hLpos : 0 < L := by
    have he : 0 < e := AVenhance.Infra.Cutoff.epsilon_pos
      I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hApos : 0 < A := lt_of_lt_of_le (by positivity) hA1
    exact lt_of_lt_of_le
      (mul_pos hApos (Real.rpow_pos_of_pos he _)) hL1
  have hDnonneg : 0 ≤ (n.factorial : ℝ) * L ^ n := by positivity
  calc
    4 * (∑ q ∈ Finset.range (n + 1),
        if 2 ≤ q then
          ((n.choose q : ℕ) : ℝ) *
            (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
              ((n - q).factorial : ℝ) * L ^ (n - q)
        else 0) ≤
      ((n.factorial : ℝ) * L ^ n) *
        (K * (∑ q ∈ Finset.range (n + 1),
          if 2 ≤ q then (1 / 2 : ℝ) ^ (q - 2) else 0)) := htermSum
    _ ≤ ((n.factorial : ℝ) * L ^ n) * (K * 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hgeom hKnonneg) hDnonneg
    _ ≤ ((n.factorial : ℝ) * L ^ n) * (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hKsmall hDnonneg
    _ = (1 / 4 : ℝ) * (n.factorial : ℝ) * L ^ n := by ring

theorem theta_analytic_radius_scales_of_A5
    {β κ c R₀ : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (hc : 0 < c)
    (hκ : c * (AVenhance.a β I.Λ (m - 1) *
      AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β)) ≤ κ) :
    let e := AVenhance.epsilon β I.Λ (m - 1)
    let γ := AVenhance.gamma β
    let L := thetaAnalyticRadius c e γ R₀
    0 < κ ∧ 0 < L ∧ 2 / R₀ ≤ L ∧
      (∀ n : ℕ, 1 ≤ n →
        4 * Real.sqrt ((n : ℝ) *
            thetaPotentialDerivativeCoefficient (m := m) I 2 / κ) *
            ((n - 1).factorial : ℝ) * L ^ (n - 1) ≤
          (1 / 4 : ℝ) * (n.factorial : ℝ) * L ^ n) ∧
      (∀ n : ℕ, 1 ≤ n →
        4 * (∑ q ∈ Finset.range (n + 1),
          if 2 ≤ q then
            ((n.choose q : ℕ) : ℝ) *
              (thetaPotentialDerivativeCoefficient (m := m) I q / κ) *
                ((n - q).factorial : ℝ) * L ^ (n - q)
          else 0) ≤
          (1 / 4 : ℝ) * (n.factorial : ℝ) * L ^ n) := by
  dsimp
  let e := AVenhance.epsilon β I.Λ (m - 1)
  let γ := AVenhance.gamma β
  let L := thetaAnalyticRadius c e γ R₀
  have he : 0 < e := AVenhance.Infra.Cutoff.epsilon_pos
    I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hA5positive :
      0 < AVenhance.a β I.Λ (m - 1) *
        AVenhance.epsilon β I.Λ (m - 1) ^ (2 + AVenhance.gamma β) := by
    have ha : 0 < AVenhance.a β I.Λ (m - 1) := by
      rw [AVenhance.a]
      exact Real.rpow_pos_of_pos he _
    exact mul_pos ha (Real.rpow_pos_of_pos he _)
  have hκpos : 0 < κ :=
    lt_of_lt_of_le (mul_pos hc hA5positive) hκ
  have hLfirst : thetaAnalyticRadiusBase c *
      e ^ (-1 - γ / 2) ≤ L := by
    dsimp [L, thetaAnalyticRadius]
    exact le_max_left _ _
  have hLsecond : 2 / R₀ ≤ L := by
    dsimp [L, thetaAnalyticRadius]
    exact le_max_right _ _
  have hLpos : 0 < L := by
    have hApos : 0 < thetaAnalyticRadiusBase c := by
      exact lt_of_lt_of_le
        (by positivity : 0 < (2 : ℝ) ^ 15 / Real.sqrt c)
        (show (2 : ℝ) ^ 15 / Real.sqrt c ≤
          thetaAnalyticRadiusBase c by exact le_max_left _ _)
    exact lt_of_lt_of_le
      (mul_pos hApos (Real.rpow_pos_of_pos he _)) hLfirst
  refine ⟨hκpos, hLpos, hLsecond, ?_, ?_⟩
  · intro n hn
    simpa [e, L, γ] using
      (ThetaAnalyticScale.theta_q1_factorial_scale (I := I) (m := m) (n := n)
        (R₀ := R₀) hc hκ hn)
  · intro n hn
    simpa [e, L, γ] using
      (ThetaAnalyticScale.theta_qhigh_factorial_scale (I := I) (m := m) (n := n)
        (R₀ := R₀) hc hκ hn)

end AVenhance.Infra.Section4

end
