/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleBounds

/-! Decay and separation consequences of the length scales. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Ingredients

theorem EpsilonConsequences.qpow_ge_linear {q : ℝ} (hq : 1 < q) (m : ℕ) :
    1 + (m : ℝ) * (q - 1) ≤ q ^ m := by
  induction m with
  | zero => norm_num
  | succ n ih =>
      have hpow : 1 ≤ q ^ n := one_le_pow₀ (le_of_lt hq)
      have hstep : q - 1 ≤ q ^ n * (q - 1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hq.le) (sub_nonneg.mpr hpow)]
      calc
        1 + ((n + 1 : ℕ) : ℝ) * (q - 1) =
            (1 + (n : ℝ) * (q - 1)) + (q - 1) := by push_cast; ring
        _ ≤ q ^ n + (q - 1) := by nlinarith [ih]
        _ ≤ q ^ n + q ^ n * (q - 1) := by nlinarith [hstep]
        _ = q ^ (n + 1) := by rw [pow_succ]; ring

theorem EpsilonConsequences.epsilon_le_lambda_pow_aux {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    AVenhance.epsilon β Λ m ≤ (Λ : ℝ) ^ (-(m : ℝ)) := by
  by_cases hm : m = 0
  · simp [AVenhance.epsilon, hm]
  · have hq : 1 < AVenhance.q β := one_lt_q hβ hβ'
    have hexp : (m : ℝ) ≤ (AVenhance.q β) ^ m /
        (AVenhance.q β - 1) := by
      have hlin := EpsilonConsequences.qpow_ge_linear hq m
      apply (le_div_iff₀ (sub_pos.mpr hq)).2
      nlinarith
    have hbase : 1 ≤ (Λ : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 7) hΛ)
    let X := (Λ : ℝ) ^ ((AVenhance.q β) ^ m /
      (AVenhance.q β - 1))
    have hX : (Λ : ℝ) ^ (m : ℝ) ≤ X := by
      dsimp [X]
      have hle := Real.rpow_le_rpow_of_exponent_le hbase hexp
      simpa only [Real.rpow_natCast] using hle
    have hceil : (Λ : ℝ) ^ (m : ℝ) ≤ (⌈X⌉₊ : ℝ) :=
      hX.trans (Nat.le_ceil X)
    have hpos : 0 < (Λ : ℝ) ^ (m : ℝ) := by positivity
    have hceilpos : 0 < (⌈X⌉₊ : ℝ) := lt_of_lt_of_le hpos hceil
    have hinv : (⌈X⌉₊ : ℝ)⁻¹ ≤ ((Λ : ℝ) ^ (m : ℝ))⁻¹ :=
      (inv_le_inv₀ hceilpos hpos).2 hceil
    have hpowinv : ((Λ : ℝ) ^ (m : ℝ))⁻¹ = (Λ : ℝ) ^ (-(m : ℝ)) := by
      calc
        ((Λ : ℝ) ^ (m : ℝ))⁻¹ = ((Λ : ℝ) ^ m)⁻¹ := by rw [Real.rpow_natCast]
        _ = (Λ : ℝ) ^ (-(m : ℝ)) :=
          by
            simpa only [Real.rpow_natCast] using
              (Real.rpow_neg (x := (Λ : ℝ)) (by positivity) (m : ℝ)).symm
    simpa [AVenhance.epsilon, hm, X, hpowinv] using hinv

/-- Supergeometric base whose reciprocal determines the spatial scale. -/
def EpsilonConsequences.epsilonBase (β : ℝ) (Λ m : ℕ) : ℝ :=
  (Λ : ℝ) ^ ((AVenhance.q β) ^ m / (AVenhance.q β - 1))

theorem EpsilonConsequences.qpow_ge_q {q : ℝ} (hq : 1 < q) {m : ℕ} (hm : 1 ≤ m) :
    q ≤ q ^ m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [pow_succ]
  have hn : 1 ≤ q ^ n := one_le_pow₀ hq.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hq.le) (sub_nonneg.mpr hn)]

theorem EpsilonConsequences.log_lambda_ge_one {Λ : ℕ} (hΛ : 2 ^ 7 ≤ Λ) :
    1 ≤ Real.log (Λ : ℝ) := by
  apply (Real.le_log_iff_exp_le (by positivity : 0 < (Λ : ℝ))).2
  have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hthree : (3 : ℝ) ≤ (Λ : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 3 ≤ 2 ^ 7) hΛ)
  exact le_of_lt (lt_of_lt_of_le hexp hthree)

theorem EpsilonConsequences.epsilon_base_growth {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    EpsilonConsequences.epsilonBase β Λ (m + 1) ≥ (Λ : ℝ) * (EpsilonConsequences.epsilonBase β Λ m
        + 1) := by
  let q := AVenhance.q β
  let r := q - 1
  let L := Real.log (Λ : ℝ)
  let X := EpsilonConsequences.epsilonBase β Λ m
  have hq : 1 < q := by dsimp [q]; exact one_lt_q hβ hβ'
  have hr : 0 < r := by dsimp [r]; linarith
  have hL : 1 ≤ L := by dsimp [L]; exact EpsilonConsequences.log_lambda_ge_one hΛ
  have hΛpos : 0 < (Λ : ℝ) := by positivity
  have hΛbase : 1 ≤ (Λ : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 7) hΛ)
  have hqm : q ≤ q ^ m := by dsimp [q]; exact EpsilonConsequences.qpow_ge_q hq hm
  have hqpow : 1 ≤ q ^ m := by
    dsimp [q]
    exact one_le_pow₀ hq.le
  have hlog : 1 / r ≤ (q ^ m / r) * L := by
    have hmul : 1 ≤ q ^ m * L := by
      calc
        1 ≤ q ^ m := hqpow
        _ ≤ q ^ m * L := by
          simpa using mul_le_mul_of_nonneg_left hL
            (by positivity : 0 ≤ q ^ m)
    have hmulr : 1 * r ≤ (q ^ m * L) * r :=
      mul_le_mul_of_nonneg_right hmul hr.le
    have hdiv : 1 / r ≤ (q ^ m * L) / r :=
      (div_le_div_iff₀ hr hr).2 (by simpa using hmulr)
    calc
      1 / r ≤ (q ^ m * L) / r := hdiv
      _ = (q ^ m / r) * L := by ring
  have hXlarge : Real.exp (1 / r) ≤ X := by
    dsimp [X, EpsilonConsequences.epsilonBase]
    rw [Real.rpow_def_of_pos hΛpos]
    rw [Real.exp_le_exp]
    simpa [q, r, L, mul_comm] using hlog
  have hinvX : 1 / X ≤ r := by
    have hXpos : 0 < X := by dsimp [X, EpsilonConsequences.epsilonBase]; positivity
    have hexpLower : 1 + 1 / r ≤ Real.exp (1 / r) := by
      simpa [add_comm] using Real.add_one_le_exp (1 / r)
    have hsum : 1 + 1 / r ≤ X := hexpLower.trans hXlarge
    have hprod : r + 1 ≤ r * X := by
      have h := mul_le_mul_of_nonneg_right hsum hr.le
      have hleft : (1 + 1 / r) * r = r + 1 := by
        field_simp [ne_of_gt hr]
      rw [hleft] at h
      nlinarith [h]
    have hle : 1 ≤ r * X := by linarith
    simpa [one_div, mul_comm] using (div_le_iff₀ hXpos).2 hle
  have hpowr : (Λ : ℝ) ^ r = Real.exp (r * L) := by
    dsimp [L]
    rw [Real.rpow_def_of_pos hΛpos]
    congr 1
    ring
  have hLambdaR : 1 + r ≤ (Λ : ℝ) ^ r := by
    rw [hpowr]
    have hrl : r ≤ r * L := by
      simpa using mul_le_mul_of_nonneg_left hL hr.le
    linarith [Real.add_one_le_exp (r * L), hrl]
  have hfac : (Λ : ℝ) * (1 + 1 / X) ≤ (Λ : ℝ) ^ q := by
    have hqdecomp : q = 1 + r := by dsimp [r]; ring
    have hpowq : (Λ : ℝ) ^ q = (Λ : ℝ) * (Λ : ℝ) ^ r := by
      rw [hqdecomp, Real.rpow_add hΛpos]
      simp [Real.rpow_one]
    have hsum : 1 + 1 / X ≤ 1 + r := by linarith
    calc
      (Λ : ℝ) * (1 + 1 / X) ≤ (Λ : ℝ) * (1 + r) :=
        mul_le_mul_of_nonneg_left hsum hΛpos.le
      _ ≤ (Λ : ℝ) * (Λ : ℝ) ^ r :=
        mul_le_mul_of_nonneg_left hLambdaR hΛpos.le
      _ = (Λ : ℝ) ^ q := hpowq.symm
  have hfactor : (Λ : ℝ) ^ q ≤ (Λ : ℝ) ^ (q ^ m) :=
    Real.rpow_le_rpow_of_exponent_le hΛbase hqm
  have hExp : q ^ (m + 1) / r = q ^ m / r + q ^ m := by
    dsimp [r]
    rw [pow_succ]
    field_simp [ne_of_gt (sub_pos.mpr hq)]
    ring_nf
  have hgrowth : EpsilonConsequences.epsilonBase β Λ (m + 1) = X * (Λ : ℝ) ^ (q ^ m) := by
    change (Λ : ℝ) ^ (q ^ (m + 1) / r) = X * (Λ : ℝ) ^ (q ^ m)
    rw [hExp, Real.rpow_add hΛpos]
    dsimp [X, EpsilonConsequences.epsilonBase, q, r]
  rw [hgrowth]
  have hXpos : 0 < X := by dsimp [X, EpsilonConsequences.epsilonBase]; positivity
  calc
    X * (Λ : ℝ) ^ (q ^ m) ≥ X * (Λ : ℝ) ^ q :=
      mul_le_mul_of_nonneg_left hfactor hXpos.le
    _ ≥ (Λ : ℝ) * (X + 1) := by
      have h := mul_le_mul_of_nonneg_left hfac hXpos.le
      calc
        (Λ : ℝ) * (X + 1) = X * ((Λ : ℝ) * (1 + 1 / X)) := by
          field_simp [ne_of_gt hXpos]
        _ ≤ X * ((Λ : ℝ) ^ q) := h

theorem EpsilonConsequences.exp_le_one_add_mul_exp {x : ℝ} :
    Real.exp x ≤ 1 + x * Real.exp x := by
  have hneg : 1 - Real.exp (-x) ≤ x := by
    have h := Real.add_one_le_exp (-x)
    linarith
  have hid : Real.exp x * (1 - Real.exp (-x)) = Real.exp x - 1 := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    simp
  have hmul := mul_le_mul_of_nonneg_left hneg (Real.exp_nonneg x)
  rw [hid] at hmul
  linarith

/-- The β-dependent upper factor correcting the false uniform `10` in
`e.supergeo` (1077-1084). -/
def supergeoConstant (β : ℝ) : ℝ :=
  2 * AVenhance.q β * Real.exp (AVenhance.q β / 128)

/-- `e.supergeo` (1077-1084): the supergeometric scale comparison with the
upper error constant corrected. -/
theorem epsilon_supergeo {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) (hm : 1 ≤ m) :
    (1 - 10 * AVenhance.epsilon β Λ m) *
        AVenhance.epsilon β Λ m ^ (AVenhance.q β) ≤
      AVenhance.epsilon β Λ (m + 1) ∧
    AVenhance.epsilon β Λ (m + 1) ≤
      (1 + supergeoConstant β * AVenhance.epsilon β Λ m) *
        AVenhance.epsilon β Λ m ^ (AVenhance.q β) := by
  let q := AVenhance.q β
  let r := q - 1
  let X := EpsilonConsequences.epsilonBase β Λ m
  let Y := EpsilonConsequences.epsilonBase β Λ (m + 1)
  let c := (⌈X⌉₊ : ℝ)
  let d := (⌈Y⌉₊ : ℝ)
  have hq : 1 < q := by dsimp [q]; exact one_lt_q hβ hβ'
  have hqpos : 0 < q := by linarith
  have hr : 0 < r := by dsimp [r]; linarith
  have hΛpos : 0 < (Λ : ℝ) := by positivity
  have hΛbase : 1 ≤ (Λ : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 7) hΛ)
  have hΛ128 : (128 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  have hXpos : 0 < X := by dsimp [X, EpsilonConsequences.epsilonBase]; positivity
  have hYpos : 0 < Y := by dsimp [Y, EpsilonConsequences.epsilonBase]; positivity
  have hXge : (128 : ℝ) ≤ X := by
    have hexp : 1 ≤ q ^ m / r := by
      apply (le_div_iff₀ hr).2
      have hqm : q ≤ q ^ m := EpsilonConsequences.qpow_ge_q hq hm
      nlinarith [hq]
    have h := Real.rpow_le_rpow_of_exponent_le hΛbase hexp
    have hXdef : X = (Λ : ℝ) ^ (q ^ m / r) := by
      dsimp [X, EpsilonConsequences.epsilonBase, q, r]
    rw [hXdef]
    calc
      (128 : ℝ) ≤ (Λ : ℝ) := hΛ128
      _ = (Λ : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (Λ : ℝ) ^ (q ^ m / r) := h
  have hXone : 1 ≤ X := le_trans (by norm_num : (1 : ℝ) ≤ 128) hXge
  have hbaseGrowth := EpsilonConsequences.epsilon_base_growth hβ hβ' hΛ hm
  have hceilX : X ≤ c ∧ c < X + 1 := by
    constructor
    · dsimp [c]
      exact Nat.le_ceil X
    · dsimp [c]
      exact_mod_cast Nat.ceil_lt_add_one hXpos.le
  have hceilY : Y ≤ d ∧ d < Y + 1 := by
    constructor
    · dsimp [d]
      exact Nat.le_ceil Y
    · dsimp [d]
      exact_mod_cast Nat.ceil_lt_add_one hYpos.le
  have hcpos : 0 < c := lt_of_lt_of_le hXpos hceilX.1
  have hdpos : 0 < d := lt_of_lt_of_le hYpos hceilY.1
  have hYeq : Y = X ^ q := by
    have hExp : q ^ (m + 1) / (q - 1) =
        (q ^ m / (q - 1)) * q := by
      rw [pow_succ]
      field_simp [ne_of_gt hr]
    dsimp [Y, X, EpsilonConsequences.epsilonBase, q]
    rw [hExp, Real.rpow_mul hΛpos.le]
  have hc_le_Yplus : c ≤ Y + 1 := by
    have hXleY : X ≤ Y := by
      rw [hYeq]
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hXone hq.le)
    linarith [hceilX.2, hXleY]
  have hcPow : X ^ q ≤ c ^ q := Real.rpow_le_rpow hXpos.le hceilX.1 hqpos.le
  have hcoeff : 0 ≤ 1 - 1 / c := by
    have hcge1 : 1 ≤ c := le_trans hXone hceilX.1
    have hinv : 1 / c ≤ 1 := by
      apply (div_le_iff₀ hcpos).2
      simpa using hcge1
    linarith
  have hlowProd : (1 - 1 / c) * d ≤ c ^ q := by
    calc
      (1 - 1 / c) * d ≤ (1 - 1 / c) * (Y + 1) :=
        mul_le_mul_of_nonneg_left hceilY.2.le hcoeff
      _ ≤ Y := by
        have hcY := hc_le_Yplus
        field_simp [ne_of_gt hcpos]
        nlinarith [hcY]
      _ ≤ c ^ q := by rw [hYeq]; exact hcPow
  have hratioLowBase : 1 - 1 / c ≤ c ^ q / d :=
    (le_div_iff₀ hdpos).2 hlowProd
  have hratioUpBase : c ^ q / d ≤ 1 + supergeoConstant β / c := by
    have hYleD : X ^ q ≤ d := by rw [← hYeq]; exact hceilY.1
    have hceille : c ≤ X + 1 := hceilX.2.le
    have hbaseUpper : (1 + 1 / X) ≤ Real.exp (1 / X) := by
      simpa [add_comm] using Real.add_one_le_exp (1 / X)
    have hpowUpper : (X + 1) ^ q ≤ X ^ q * Real.exp (q / X) := by
      have hsum : X + 1 = X * (1 + 1 / X) := by
        field_simp [ne_of_gt hXpos]
      calc
        (X + 1) ^ q = X ^ q * (1 + 1 / X) ^ q := by
          rw [hsum, Real.mul_rpow hXpos.le (by positivity)]
        _ ≤ X ^ q * Real.exp (1 / X) ^ q := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) hbaseUpper hqpos.le)
            (by positivity)
        _ = X ^ q * Real.exp (q / X) := by
          congr 1
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          congr 1
          ring
    have hXbound : 1 / X ≤ (2 : ℝ) / c := by
      have hcX : c ≤ 2 * X := by linarith [hceilX.2, hXone]
      apply (div_le_div_iff₀ hXpos hcpos).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hqpos.le) (sub_nonneg.mpr hcX)]
    have hqdiv : q / X ≤ q / 128 := by
      apply (div_le_div_iff₀ hXpos (by norm_num : (0 : ℝ) < 128)).2
      exact mul_le_mul_of_nonneg_left hXge hqpos.le
    have hexpMono : Real.exp (q / X) ≤ Real.exp (q / 128) :=
      Real.exp_le_exp.mpr hqdiv
    have hexpBound : Real.exp (q / X) ≤ 1 + supergeoConstant β / c := by
      have hlin := EpsilonConsequences.exp_le_one_add_mul_exp (x := q / X)
      have hmul : (q / X) * Real.exp (q / X) ≤
          (2 * q / c) * Real.exp (q / 128) := by
        have hqX : q / X ≤ 2 * q / c := by
          apply (div_le_div_iff₀ hXpos hcpos).2
          nlinarith [mul_le_mul_of_nonneg_left hXbound hqpos.le]
        calc
          (q / X) * Real.exp (q / X) ≤
              (2 * q / c) * Real.exp (q / X) :=
            mul_le_mul_of_nonneg_right hqX (Real.exp_nonneg _)
          _ ≤ (2 * q / c) * Real.exp (q / 128) :=
            mul_le_mul_of_nonneg_left hexpMono (by positivity)
      have hC : (2 * q / c) * Real.exp (q / 128) =
          supergeoConstant β / c := by
        dsimp [supergeoConstant, q]
        ring
      calc
        Real.exp (q / X) ≤ 1 + (q / X) * Real.exp (q / X) := hlin
        _ ≤ 1 + (2 * q / c) * Real.exp (q / 128) := by linarith [hmul]
        _ = 1 + supergeoConstant β / c := by rw [hC]
    have hprod : c ^ q ≤ d * (1 + supergeoConstant β / c) := by
      calc
        c ^ q ≤ (X + 1) ^ q := Real.rpow_le_rpow hcpos.le hceille hqpos.le
        _ ≤ X ^ q * Real.exp (q / X) := hpowUpper
        _ ≤ d * Real.exp (q / X) :=
          mul_le_mul_of_nonneg_right hYleD (Real.exp_nonneg _)
        _ ≤ d * (1 + supergeoConstant β / c) :=
          mul_le_mul_of_nonneg_left hexpBound hdpos.le
    apply (div_le_iff₀ hdpos).2
    simpa [mul_comm] using hprod
  have hm0 : m ≠ 0 := by omega
  have heps : AVenhance.epsilon β Λ m = c⁻¹ := by
    simp [AVenhance.epsilon, hm0, c, X, EpsilonConsequences.epsilonBase]
  have henext : AVenhance.epsilon β Λ (m + 1) = d⁻¹ := by
    simp [AVenhance.epsilon, d, Y, EpsilonConsequences.epsilonBase]
  have hratio :
      AVenhance.epsilon β Λ (m + 1) /
        AVenhance.epsilon β Λ m ^ q = c ^ q / d := by
    rw [henext, heps, Real.inv_rpow hcpos.le]
    field_simp [ne_of_gt hdpos, ne_of_gt (Real.rpow_pos_of_pos hcpos q)]
  have hratioLower :
      1 - AVenhance.epsilon β Λ m ≤
        AVenhance.epsilon β Λ (m + 1) /
          AVenhance.epsilon β Λ m ^ q := by
    rw [hratio, heps]
    simpa [one_div] using hratioLowBase
  have hratioUpper :
      AVenhance.epsilon β Λ (m + 1) /
          AVenhance.epsilon β Λ m ^ q ≤
        1 + supergeoConstant β * AVenhance.epsilon β Λ m := by
    rw [hratio, heps]
    simpa [one_div, div_eq_mul_inv] using hratioUpBase
  have hepspos : 0 < AVenhance.epsilon β Λ m :=
    AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ
  have hpowpos : 0 < AVenhance.epsilon β Λ m ^ q :=
    Real.rpow_pos_of_pos hepspos q
  have hratioLower10 :
      1 - 10 * AVenhance.epsilon β Λ m ≤
        AVenhance.epsilon β Λ (m + 1) /
          AVenhance.epsilon β Λ m ^ q := by
    have hle : 1 - 10 * AVenhance.epsilon β Λ m ≤
        1 - AVenhance.epsilon β Λ m := by nlinarith [hepspos.le]
    exact le_trans hle hratioLower
  constructor
  · exact (le_div_iff₀ hpowpos).1 hratioLower10
  · exact (div_le_iff₀ hpowpos).1 hratioUpper

/-- `e.minsep` (1069-1073): `ε_m ≤ Λ⁻ᵐ`, hence `ε_m ≤ 2⁻⁷ᵐ`. -/
theorem epsilon_le_lambda_pow {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    AVenhance.epsilon β Λ m ≤ (Λ : ℝ) ^ (-(m : ℝ)) :=
  EpsilonConsequences.epsilon_le_lambda_pow_aux hβ hβ' hΛ

/-- `e.minsep` (1069-1073): successive length scales are separated
by at least the prescribed factor `Λ`. -/
theorem epsilon_minsep {β : ℝ} {Λ m : ℕ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) (hΛ : 2 ^ 7 ≤ Λ) :
    (Λ : ℝ) * AVenhance.epsilon β Λ (m + 1) ≤
      AVenhance.epsilon β Λ m := by
  by_cases hm : m = 0
  · subst m
    have heps := epsilon_le_lambda_pow hβ hβ' hΛ (m := 1)
    have hpow : (Λ : ℝ) ^ (-(1 : ℝ)) = (Λ : ℝ)⁻¹ := by
      rw [Real.rpow_neg_one]
    have hmul := mul_le_mul_of_nonneg_left
      (show AVenhance.epsilon β Λ 1 ≤ (Λ : ℝ)⁻¹ by simpa [hpow] using heps)
      (by positivity : 0 ≤ (Λ : ℝ))
    calc
      (Λ : ℝ) * AVenhance.epsilon β Λ 1 ≤ (Λ : ℝ) * (Λ : ℝ)⁻¹ := hmul
      _ = 1 := by field_simp [ne_of_gt (by positivity : 0 < (Λ : ℝ))]
  · let X := EpsilonConsequences.epsilonBase β Λ m
    let Y := EpsilonConsequences.epsilonBase β Λ (m + 1)
    let c := (⌈X⌉₊ : ℝ)
    let d := (⌈Y⌉₊ : ℝ)
    have hbase := EpsilonConsequences.epsilon_base_growth hβ hβ' hΛ (by omega : 1 ≤ m)
    have hXpos : 0 < X := by dsimp [X, EpsilonConsequences.epsilonBase]; positivity
    have hYpos : 0 < Y := by dsimp [Y, EpsilonConsequences.epsilonBase]; positivity
    have hcpos : 0 < c := by
      dsimp [c]
      exact_mod_cast Nat.ceil_pos.mpr hXpos
    have hdpos : 0 < d := by
      dsimp [d]
      exact_mod_cast Nat.ceil_pos.mpr hYpos
    have hc_lt : c < X + 1 := by
      dsimp [c]
      exact_mod_cast Nat.ceil_lt_add_one hXpos.le
    have hd_ge : Y ≤ d := by dsimp [d]; exact Nat.le_ceil Y
    have hΛpos : 0 < (Λ : ℝ) := by positivity
    have hceillt : (Λ : ℝ) * c < d := by
      calc
        (Λ : ℝ) * c < (Λ : ℝ) * (X + 1) :=
          mul_lt_mul_of_pos_left hc_lt hΛpos
        _ ≤ Y := by simpa [Nat.add_comm] using hbase
        _ ≤ d := hd_ge
    have hceil : (Λ : ℝ) * c ≤ d := hceillt.le
    have hquot : (Λ : ℝ) / d ≤ 1 / c :=
      (div_le_div_iff₀ hdpos hcpos).2 (by simpa using hceil)
    simpa [AVenhance.epsilon, hm, X, Y, c, d, EpsilonConsequences.epsilonBase, one_div,
      div_eq_mul_inv] using hquot

end AVenhance.Infra.Ingredients
