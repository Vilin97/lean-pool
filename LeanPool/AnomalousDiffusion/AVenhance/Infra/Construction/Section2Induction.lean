/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.ExplicitBarNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Scalars
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.TimeIncrement.FlowBounds

/-! The telescoping part of the Section 2 stream induction. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.Construction

/-- The first display of `p.SAMS.regularity`, isolated as an
explicit conditional input to the higher-order induction. -/
def StreamIncrementBounds {β : ℝ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ, ∀ n : ℕ,
    barNorm n (2 ^ 7 * (epsilon β I.Λ m)⁻¹) (Φ m t - Φ (m - 1) t) ≤
      ENNReal.ofReal (10 * epsilon β I.Λ m ^ β)

/-- Changing the radius multiplies the order-`n` seminorm by the `n`th power
of the radius ratio. -/
theorem barNorm_radius_change {n : ℕ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ n f) {R S : ℝ} (hR : 0 < R) (hS : 0 < S) :
    barNorm n S f = barNorm n R f * ENNReal.ofReal (R / S) ^ n := by
  rw [barNorm_eq_pointwise f n S hf, barNorm_eq_pointwise f n R hf]
  let a : ENNReal := ENNReal.ofReal R
  let b : ENNReal := ENNReal.ofReal S
  let q : ENNReal := ENNReal.ofReal (R / S)
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact (ENNReal.ofReal_pos.mpr hR).ne'
  have hatop : a ≠ ⊤ := by dsimp [a]; exact ENNReal.ofReal_ne_top
  have hb0 : b ≠ 0 := by
    dsimp [b]
    exact (ENNReal.ofReal_pos.mpr hS).ne'
  have hbtop : b ≠ ⊤ := by dsimp [b]; exact ENNReal.ofReal_ne_top
  have hq : q = a / b := by
    dsimp [q, a, b]
    exact ENNReal.ofReal_div_of_pos hS
  have hsingle : a⁻¹ * q = b⁻¹ := by
    rw [hq, div_eq_mul_inv]
    calc
      a⁻¹ * (a * b⁻¹) = (a⁻¹ * a) * b⁻¹ := by rw [mul_assoc]
      _ = b⁻¹ := by rw [ENNReal.inv_mul_cancel ha0 hatop, one_mul]
  have hfactor : a⁻¹ ^ n * q ^ n = b⁻¹ ^ n := by
    rw [← mul_pow, hsingle]
  let w : ENNReal := ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / n.factorial)
  let D : ENNReal := ⨆ J : Fin n → Fin 2, ⨆ x : Vec 2,
    ‖iteratedFDeriv ℝ n f x (fun j => basisVec (J j))‖ₑ
  change w * b⁻¹ ^ n * D = (w * a⁻¹ ^ n * D) * q ^ n
  rw [← hfactor]
  ac_rfl

theorem Section2Induction.stream_slice_sum_increments {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ) (t : ℝ) :
    Φ m t = ∑ j ∈ Finset.range m, (Φ (j + 1) t - Φ j t) := by
  induction m with
  | zero =>
      funext x
      simp [hseq.1]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [← ih]
      funext x
      simp

theorem Section2Induction.epsilon_gap_ratio {β : ℝ} {I : Ingredients β}
    (m j : ℕ) (hjm : j ≤ m) :
    epsilon β I.Λ m / epsilon β I.Λ j ≤
      (1 / 128 : ℝ) ^ (m - j) := by
  have hstep : ∀ k : ℕ,
      epsilon β I.Λ (k + 1) ≤ epsilon β I.Λ k / 128 := by
    intro k
    have hs := Ingredients.epsilon_minsep I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := k)
    have hΛ : (128 : ℝ) ≤ (I.Λ : ℝ) := by exact_mod_cast I.two_pow_seven_le
    have hp := mul_le_mul_of_nonneg_right hΛ
      (Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
        (m := k + 1)).le
    have hh : (128 : ℝ) * epsilon β I.Λ (k + 1) ≤ epsilon β I.Λ k :=
      le_trans hp hs
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 128)).2 (by nlinarith)
  have hiter : ∀ q, epsilon β I.Λ (j + q) ≤
      (1 / 128 : ℝ) ^ q * epsilon β I.Λ j := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        have hs := hstep (j + q)
        have hstep' : epsilon β I.Λ (j + q + 1) ≤
            (1 / 128 : ℝ) * epsilon β I.Λ (j + q) := by
          simpa [div_eq_mul_inv, mul_comm] using hs
        calc
          epsilon β I.Λ (j + (q + 1)) = epsilon β I.Λ (j + q + 1) := by rfl
          _ ≤ (1 / 128 : ℝ) * epsilon β I.Λ (j + q) := hstep'
          _ ≤ (1 / 128 : ℝ) * ((1 / 128 : ℝ) ^ q * epsilon β I.Λ j) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 128 : ℝ) ^ (q + 1) * epsilon β I.Λ j := by rw [pow_succ]; ac_rfl
  have hej : 0 < epsilon β I.Λ j :=
    Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hq := hiter (m - j)
  have hidx : j + (m - j) = m := by omega
  rw [hidx] at hq
  exact (div_le_iff₀ hej).2 hq

theorem Section2Induction.nat_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        n + 1 + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := by
          exact Nat.add_le_add_left (Nat.one_le_pow n 2 (by omega)) _
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

theorem Section2Induction.rpow_increment_scale_identity {a b β : ℝ}
    (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    a ^ β * (b / (2 * a)) ^ n =
      b ^ β * (2 : ℝ) ^ (-(n : ℝ)) * (b / a) ^ ((n : ℝ) - β) := by
  have hL : a ^ β * (b / (2 * a)) ^ n =
      a ^ β * (b ^ (n : ℝ) / (2 ^ (n : ℝ) * a ^ (n : ℝ))) := by
    rw [← Real.rpow_natCast (b / (2 * a)) n,
      Real.div_rpow hb.le (mul_nonneg (by norm_num) ha.le),
      Real.mul_rpow (by norm_num) ha.le, Real.rpow_natCast,
      Real.rpow_natCast, Real.rpow_natCast]
  rw [hL]
  have hratio : (b / a) ^ ((n : ℝ) - β) =
      (b ^ (n : ℝ) / b ^ β) / (a ^ (n : ℝ) / a ^ β) := by
    rw [Real.div_rpow hb.le ha.le, Real.rpow_sub hb (n : ℝ) β,
      Real.rpow_sub ha (n : ℝ) β]
  rw [hratio]
  have hpow2 : (2 : ℝ) ^ n * (2 : ℝ) ^ (-(n : ℝ)) = 1 := by
    rw [← Real.rpow_natCast (2 : ℝ) n,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_inv_cancel₀ (by positivity)
  have hpowA : 0 < a ^ (n : ℝ) := Real.rpow_pos_of_pos ha _
  have hpowB : 0 < b ^ β := Real.rpow_pos_of_pos hb _
  have hpowAB : 0 < a ^ β := Real.rpow_pos_of_pos ha _
  field_simp [ne_of_gt hpowA, ne_of_gt hpowB, ne_of_gt hpowAB]
  simp

theorem Section2Induction.epsilon_gap_power_bound {β : ℝ} {I : Ingredients β}
    {m j n : ℕ} (hjm : j ≤ m) (hn : 2 ≤ n) :
    (epsilon β I.Λ m / epsilon β I.Λ j) ^ ((n : ℝ) - β) ≤
      (1 / 2 : ℝ) ^ (m - j) := by
  have heJ := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := j)
  have heM := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hratio := Section2Induction.epsilon_gap_ratio (β := β) (I := I) m j hjm
  have hrpos : 0 < epsilon β I.Λ m / epsilon β I.Λ j := div_pos heM heJ
  have hbase : 0 < (1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hratio' : epsilon β I.Λ m / epsilon β I.Λ j ≤
      (1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ) := by
    simpa only [Real.rpow_natCast] using hratio
  have hratioPow := Real.rpow_le_rpow hrpos.le hratio'
    (by
      have hncast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hexpPos : 0 < (n : ℝ) - β := by linarith [I.beta_lt, hncast]
      exact hexpPos.le)
  have hexp : (2 : ℝ) / 3 ≤ (n : ℝ) - β := by
    have hβ : β < 4 / 3 := I.beta_lt
    have hcast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpowBaseLe : (1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ) ≤ 1 := by
    exact Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
  have hratioExp := Real.rpow_le_rpow_of_exponent_ge hbase hpowBaseLe hexp
  have hsmall : (1 / 128 : ℝ) ^ (2 / 3 : ℝ) ≤ 1 / 2 := by
    calc
      (1 / 128 : ℝ) ^ (2 / 3 : ℝ) =
          (2 : ℝ) ^ (-(14 / 3 : ℝ)) := by
        rw [show (1 / 128 : ℝ) = (2 : ℝ) ^ (-7 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hpowq : ((1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ)) ^ (2 / 3 : ℝ) =
      ((1 / 128 : ℝ) ^ (2 / 3 : ℝ)) ^ (m - j) := by
    have hx : 0 ≤ (1 / 128 : ℝ) := by norm_num
    calc
      ((1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ)) ^ (2 / 3 : ℝ) =
          (1 / 128 : ℝ) ^ (((m - j : ℕ) : ℝ) * (2 / 3 : ℝ)) :=
        (Real.rpow_mul hx _ _).symm
      _ = (1 / 128 : ℝ) ^ ((2 / 3 : ℝ) * ((m - j : ℕ) : ℝ)) := by
        congr 1
        ring
      _ = ((1 / 128 : ℝ) ^ (2 / 3 : ℝ)) ^ ((m - j : ℕ) : ℝ) :=
        Real.rpow_mul hx _ _
      _ = ((1 / 128 : ℝ) ^ (2 / 3 : ℝ)) ^ (m - j) := by
        rw [Real.rpow_natCast]
  have hpowHalf : ((1 / 128 : ℝ) ^ (2 / 3 : ℝ)) ^ (m - j) ≤
      (1 / 2 : ℝ) ^ (m - j) :=
    pow_le_pow_left₀ (by positivity) hsmall (m - j)
  have hnat : ((1 / 128 : ℝ) ^ ((m - j : ℕ) : ℝ)) ^ (2 / 3 : ℝ) ≤
      (1 / 2 : ℝ) ^ (m - j) := by
    rw [hpowq]
    exact hpowHalf
  exact hratioPow.trans (hratioExp.trans hnat)

theorem Section2Induction.rpow_two_neg_nat (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℝ)) = (1 / 2 : ℝ) ^ n := by
  calc
    (2 : ℝ) ^ (-(n : ℝ)) = ((2 : ℝ) ^ (n : ℝ))⁻¹ :=
      Real.rpow_neg (by norm_num) _
    _ = ((2 : ℝ) ^ n)⁻¹ := by rw [Real.rpow_natCast]
    _ = (1 / 2 : ℝ) ^ n := by
      simp [one_div]

theorem Section2Induction.epsilon_step_le_of_minsep {β : ℝ} {I : Ingredients β} (k : ℕ) :
    epsilon β I.Λ (k + 1) ≤ epsilon β I.Λ k := by
  have hs := Ingredients.epsilon_minsep I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := k)
  have hΛ : 1 ≤ (I.Λ : ℝ) := by
    have hseven := I.two_pow_seven_le
    have hnat : 1 ≤ I.Λ := by omega
    exact_mod_cast hnat
  have hm := mul_le_mul_of_nonneg_right hΛ
    (Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
      (m := k + 1)).le
  have hm' : epsilon β I.Λ (k + 1) ≤ (I.Λ : ℝ) * epsilon β I.Λ (k + 1) := by
    simpa using hm
  exact hm'.trans hs

theorem Section2Induction.stream_slice_contDiff {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (m : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) := by
  have hm := (streamSeq_isAdmissible hseq m).1
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => Function.uncurry (Φ m) (t, x))
  exact hm.comp hmap

theorem Section2Induction.stream_increment_bar_radius_bound
    {f : Vec 2 → ℝ} {n : ℕ} {R S K : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hR : 0 < R) (hS : 0 < S)
    (hK : 0 ≤ K) (hbar : barNorm n R f ≤ ENNReal.ofReal K) :
    barNorm n S f ≤ ENNReal.ofReal (K * (R / S) ^ n) := by
  rw [barNorm_radius_change (hf.of_le (by simp)) hR hS]
  have hratio : 0 ≤ R / S := (div_pos hR hS).le
  calc
    barNorm n R f * ENNReal.ofReal (R / S) ^ n ≤
        ENNReal.ofReal K * ENNReal.ofReal (R / S) ^ n :=
      mul_le_mul_of_nonneg_right hbar (by positivity)
    _ = ENNReal.ofReal (K * (R / S) ^ n) := by
      rw [← ENNReal.ofReal_pow hratio, ← ENNReal.ofReal_mul hK]

theorem Section2Induction.increment_scale_ratio {β : ℝ} {I : Ingredients β}
    {m j : ℕ} (hC : 0 < 11 + 768 / (β - 1)) :
    (2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) /
        ((11 + 768 / (β - 1)) * (epsilon β I.Λ m)⁻¹) =
      (2 : ℝ) ^ 7 * epsilon β I.Λ m /
        ((11 + 768 / (β - 1)) * epsilon β I.Λ (j + 1)) := by
  have hj : 0 < epsilon β I.Λ (j + 1) :=
    Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hm : 0 < epsilon β I.Λ m :=
    Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  field_simp [ne_of_gt hC, ne_of_gt hj, ne_of_gt hm]

theorem Section2Induction.high_increment_scale_ratio {β : ℝ} {I : Ingredients β}
    {m j : ℕ} :
    (2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) /
        (2 ^ 8 * (epsilon β I.Λ m)⁻¹) =
      epsilon β I.Λ m / (2 * epsilon β I.Λ (j + 1)) := by
  have hj : 0 < epsilon β I.Λ (j + 1) :=
    Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hm : 0 < epsilon β I.Λ m :=
    Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  field_simp [ne_of_gt hj, ne_of_gt hm]

/-- The sum of normalized increment bounds closes the high-order `e.phimbounds.subbed`
estimate. The only Section 2 induction input here is the first stream-regularity display. -/
theorem high_order_stream_bound_of_increment_bounds {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (hinc : StreamIncrementBounds I Φ) (m : ℕ) (t : ℝ)
    (n : ℕ) (hn : 2 ≤ n) :
    barNorm n (2 ^ 8 * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
      ENNReal.ofReal (2 ^ 5 * a β I.Λ m * epsilon β I.Λ m ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)) := by
  let em := epsilon β I.Λ m
  let R : ℝ := 2 ^ 8 * em⁻¹
  let d : ℕ → Vec 2 → ℝ := fun j => Φ (j + 1) t - Φ j t
  have hem : 0 < em := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hR : 0 < R := by dsimp [R, em]; positivity
  have hsumId := Section2Induction.stream_slice_sum_increments hseq m t
  have hfun : ∀ j ∈ Finset.range m, ContDiff ℝ n (d j) := by
    intro j _
    have hleft := Section2Induction.stream_slice_contDiff hseq (j + 1) t
    have hright := Section2Induction.stream_slice_contDiff hseq j t
    have hEq : d j = (fun x : Vec 2 => Φ (j + 1) t x - Φ j t x) := by
      funext x
      rfl
    rw [hEq]
    exact (hleft.sub hright).of_le (by simp)
  have hsum := barNorm_sum_le (Finset.range m) d n R hfun
  have hnonneg : 0 ≤ em ^ β := Real.rpow_nonneg hem.le _
  have hcoef : (20 : ℝ) * (1 / 2 : ℝ) ^ n ≤
      32 * (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3) := by
    have hNat := Section2Induction.nat_succ_le_two_pow n
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hNatReal : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hNat
    have hinv := one_div_le_one_div_of_le hden hNatReal
    have hhalf : (1 / 2 : ℝ) ^ n ≤ ((n : ℝ) + 1)⁻¹ := by
      simpa [one_div_pow] using hinv
    have hpoly : 20 * ((n : ℝ) + 1) ^ 2 ≤ 32 * ((n : ℝ) + 2) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) + 1), sq_nonneg ((n : ℝ) + 2)]
    calc
      20 * (1 / 2 : ℝ) ^ n ≤ 20 / ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
      _ ≤ 32 * (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3) := by
        apply (div_le_iff₀ hden).2
        field_simp [ne_of_gt hden]
        nlinarith [hpoly]
  rw [hsumId]
  calc
    barNorm n R (∑ j ∈ Finset.range m, d j) ≤
        ∑ j ∈ Finset.range m, barNorm n R (d j) := hsum
    _ ≤ ∑ j ∈ Finset.range m,
        ENNReal.ofReal (10 * epsilon β I.Λ (j + 1) ^ β *
          (epsilon β I.Λ m / (2 * epsilon β I.Λ (j + 1))) ^ n) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjlt : j < m := Finset.mem_range.mp hj
      have hjm : j + 1 ≤ m := by omega
      have he := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := j + 1)
      have hRj : 0 < 2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹ := by positivity
      have hrEq := Section2Induction.high_increment_scale_ratio (I := I) (m := m) (j := j)
      have hbar := hinc (j + 1) (by omega) t n
      have hbar' : barNorm n (2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) (d j) ≤
          ENNReal.ofReal (10 * epsilon β I.Λ (j + 1) ^ β) := by
        simpa [d] using hbar
      have hK : 0 ≤ 10 * epsilon β I.Λ (j + 1) ^ β := by positivity
      have hscaled := Section2Induction.stream_increment_bar_radius_bound
        (hf := (Section2Induction.stream_slice_contDiff hseq (j + 1) t).sub
          (Section2Induction.stream_slice_contDiff hseq j t)) hRj hR hK hbar'
      rw [hrEq] at hscaled
      change barNorm n R (fun x : Vec 2 => Φ (j + 1) t x - Φ j t x) ≤ _
      exact hscaled
    _ = ENNReal.ofReal (∑ j ∈ Finset.range m,
        (10 * epsilon β I.Λ (j + 1) ^ β *
          (epsilon β I.Λ m / (2 * epsilon β I.Λ (j + 1))) ^ n)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      intro j hj
      have heJ := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := j + 1)
      have heM := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := m)
      positivity
    _ ≤ ENNReal.ofReal (20 * em ^ β * (1 / 2 : ℝ) ^ n) := by
      apply ENNReal.ofReal_le_ofReal
      have hratio : ∀ j ∈ Finset.range m,
          epsilon β I.Λ (j + 1) ^ β *
              (em / (2 * epsilon β I.Λ (j + 1))) ^ n ≤
            em ^ β * (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ (m - 1 - j) := by
        intro j hj
        have hjlt : j < m := Finset.mem_range.mp hj
        have hjm : j + 1 ≤ m := by omega
        have heJ := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
          I.two_pow_seven_le (m := j + 1)
        have hscale := Section2Induction.rpow_increment_scale_identity (β := β) heJ hem n
        have hgap := Section2Induction.epsilon_gap_power_bound (I := I) (m := m) (j := j + 1)
          (n := n) hjm hn
        have hgapIdx : m - (j + 1) = m - 1 - j := by omega
        rw [hgapIdx] at hgap
        rw [hscale, Section2Induction.rpow_two_neg_nat]
        exact mul_le_mul_of_nonneg_left hgap (by positivity)
      have hsumTerms := Finset.sum_le_sum hratio
      have hreflect := Finset.sum_range_reflect
        (fun q : ℕ => (1 / 2 : ℝ) ^ q) m
      have hseries := (sum_geometric_le (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) < 1) m)
      have hweights : (∑ j ∈ Finset.range m,
          (1 / 2 : ℝ) ^ (m - 1 - j)) ≤ 2 := by
        rw [hreflect]
        norm_num at hseries ⊢
        exact hseries
      have hgeomWeighted :
          (∑ j ∈ Finset.range m,
            epsilon β I.Λ (j + 1) ^ β *
              (em / (2 * epsilon β I.Λ (j + 1))) ^ n) ≤
            em ^ β * (1 / 2 : ℝ) ^ n * 2 := by
        calc
          _ ≤ ∑ j ∈ Finset.range m,
              em ^ β * (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ (m - 1 - j) := hsumTerms
          _ = em ^ β * (1 / 2 : ℝ) ^ n *
              (∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ (m - 1 - j)) := by
                rw [Finset.mul_sum]
          _ ≤ em ^ β * (1 / 2 : ℝ) ^ n * 2 :=
              mul_le_mul_of_nonneg_left hweights (by positivity)
      have hrealSum :
          (∑ j ∈ Finset.range m,
            10 * epsilon β I.Λ (j + 1) ^ β *
              (em / (2 * epsilon β I.Λ (j + 1))) ^ n) ≤
            20 * em ^ β * (1 / 2 : ℝ) ^ n := by
        have hsumEq :
            (∑ j ∈ Finset.range m,
              10 * epsilon β I.Λ (j + 1) ^ β *
                (em / (2 * epsilon β I.Λ (j + 1))) ^ n) =
              ∑ j ∈ Finset.range m,
                10 * (epsilon β I.Λ (j + 1) ^ β *
                  (em / (2 * epsilon β I.Λ (j + 1))) ^ n) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        calc
          _ = ∑ j ∈ Finset.range m,
                10 * (epsilon β I.Λ (j + 1) ^ β *
                  (em / (2 * epsilon β I.Λ (j + 1))) ^ n) := hsumEq
          _ = 10 * (∑ j ∈ Finset.range m,
              epsilon β I.Λ (j + 1) ^ β *
                (em / (2 * epsilon β I.Λ (j + 1))) ^ n) := by
                  rw [Finset.mul_sum]
          _ ≤ 10 * (em ^ β * (1 / 2 : ℝ) ^ n * 2) :=
            mul_le_mul_of_nonneg_left hgeomWeighted (by norm_num)
          _ = 20 * em ^ β * (1 / 2 : ℝ) ^ n := by ring
      exact hrealSum
    _ ≤ ENNReal.ofReal (32 * em ^ β *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        20 * em ^ β * (1 / 2 : ℝ) ^ n =
            em ^ β * (20 * (1 / 2 : ℝ) ^ n) := by ring
        _ ≤ em ^ β * (32 * (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)) :=
          mul_le_mul_of_nonneg_left hcoef hnonneg
        _ = 32 * em ^ β * (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3) := by ring
    _ ≤ ENNReal.ofReal (2 ^ 5 * a β I.Λ m * epsilon β I.Λ m ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3)) := by
      apply ENNReal.ofReal_le_ofReal
      have haE : a β I.Λ m * em ^ 2 = em ^ β := by
        rw [a, ← Real.rpow_natCast em 2, ← Real.rpow_add hem]
        congr 1
        ring
      rw [show (2 : ℝ) ^ 5 = 32 by norm_num, ← haE]
      dsimp [em]
      ring_nf
      exact le_rfl

theorem Section2Induction.barNorm_stream_increment_sum_bound {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (hinc : StreamIncrementBounds I Φ) (m : ℕ) (t : ℝ) (n : ℕ)
    {S : ℝ} (hS : 0 < S) :
    barNorm n S (Φ m t) ≤ ENNReal.ofReal (∑ j ∈ Finset.range m,
      (10 * epsilon β I.Λ (j + 1) ^ β) *
        ((2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) / S) ^ n) := by
  let d : ℕ → Vec 2 → ℝ := fun j => Φ (j + 1) t - Φ j t
  have hsumId := Section2Induction.stream_slice_sum_increments hseq m t
  have hfun : ∀ j ∈ Finset.range m, ContDiff ℝ n (d j) := by
    intro j hj
    have hleft := Section2Induction.stream_slice_contDiff hseq (j + 1) t
    have hright := Section2Induction.stream_slice_contDiff hseq j t
    have hEq : d j = (fun x : Vec 2 => Φ (j + 1) t x - Φ j t x) := by
      funext x
      rfl
    rw [hEq]
    exact (hleft.sub hright).of_le (by simp)
  have hsum := barNorm_sum_le (Finset.range m) d n S hfun
  have hnonneg : ∀ j ∈ Finset.range m,
      0 ≤ 10 * epsilon β I.Λ (j + 1) ^ β *
        ((2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) / S) ^ n := by
    intro j hj
    have he := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := j + 1)
    positivity
  rw [hsumId]
  calc
    barNorm n S (∑ j ∈ Finset.range m, d j) ≤
        ∑ j ∈ Finset.range m, barNorm n S (d j) := hsum
    _ ≤ ∑ j ∈ Finset.range m,
        ENNReal.ofReal (10 * epsilon β I.Λ (j + 1) ^ β *
          ((2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) / S) ^ n) := by
      apply Finset.sum_le_sum
      intro j hj
      have he := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := j + 1)
      have hRj : 0 < 2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹ := by positivity
      have hbar := hinc (j + 1) (by omega) t n
      have hbar' : barNorm n (2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) (d j) ≤
          ENNReal.ofReal (10 * epsilon β I.Λ (j + 1) ^ β) := by
        simpa [d] using hbar
      have hK : 0 ≤ 10 * epsilon β I.Λ (j + 1) ^ β := by positivity
      have hscaled := Section2Induction.stream_increment_bar_radius_bound
        (hf := (Section2Induction.stream_slice_contDiff hseq (j + 1) t).sub
          (Section2Induction.stream_slice_contDiff hseq j t)) hRj hS hK hbar'
      have hEq : d j = (fun x : Vec 2 => Φ (j + 1) t x - Φ j t x) := by
        funext x
        rfl
      rw [hEq]
      exact hscaled
    _ = ENNReal.ofReal (∑ j ∈ Finset.range m,
        (10 * epsilon β I.Λ (j + 1) ^ β) *
          ((2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) / S) ^ n) := by
      rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]

/-- Zeroth and first order stream bounds obtained by summing the stream-regularity increment
scales. The constant is explicit and depends only on `β`. -/
theorem low_order_stream_bounds_of_increment_bounds {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (hinc : StreamIncrementBounds I Φ) (m : ℕ) (t : ℝ) :
    let C : ℝ := 11 + 768 / (β - 1)
    ∀ n : ℕ, n ≤ 1 →
      barNorm n (C * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
        ENNReal.ofReal (C * epsilon β I.Λ m ^ n) := by
  dsimp
  let C : ℝ := 11 + 768 / (β - 1)
  let em : ℝ := epsilon β I.Λ m
  have hβm1 : 0 < β - 1 := by linarith [I.one_lt_beta]
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by
    dsimp [C]
    have hnonneg : 0 ≤ 768 / (β - 1) := by positivity
    linarith
  have hem : 0 < em := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hS : 0 < C * em⁻¹ := by positivity
  have hpow0 :
      (∑ j ∈ Finset.range m,
        (10 * epsilon β I.Λ (j + 1) ^ β) *
          ((2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) / (C * em⁻¹)) ^ 0) =
        10 * (∑ j ∈ Finset.range m, epsilon β I.Λ (j + 1) ^ β) := by
    simp only [pow_zero, mul_one]
    rw [← Finset.mul_sum]
  have hsumBeta :
      (∑ j ∈ Finset.range m, epsilon β I.Λ (j + 1) ^ β) ≤
        ∑ j ∈ Finset.range (m + 1), epsilon β I.Λ j ^ β := by
    calc
      _ ≤ ∑ j ∈ Finset.range m, epsilon β I.Λ j ^ β := by
        apply Finset.sum_le_sum
        intro j hj
        have hstep := Section2Induction.epsilon_step_le_of_minsep (I := I) j
        exact Real.rpow_le_rpow
          (Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
          hstep (le_of_lt (by linarith [I.one_lt_beta]))
      _ ≤ ∑ j ∈ Finset.range (m + 1), epsilon β I.Λ j ^ β := by
        rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_right (Real.rpow_nonneg
          (Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _)
  have hzero : 10 * (∑ j ∈ Finset.range m, epsilon β I.Λ (j + 1) ^ β) ≤ 11 := by
    calc
      _ ≤ 10 * (∑ j ∈ Finset.range (m + 1), epsilon β I.Λ j ^ β) :=
        mul_le_mul_of_nonneg_left hsumBeta (by norm_num)
      _ ≤ 11 := telescoping_zero I.one_lt_beta I.beta_lt I.two_pow_seven_le m
  have hpow1 :
      (∑ j ∈ Finset.range m,
        (10 * epsilon β I.Λ (j + 1) ^ β) *
          ((2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) /
            (C * em⁻¹)) ^ 1) =
        (1280 / C) * em *
          (∑ j ∈ Finset.range m, epsilon β I.Λ (j + 1) ^ (β - 1)) := by
    have hterm : ∀ j ∈ Finset.range m,
        (10 * epsilon β I.Λ (j + 1) ^ β) *
            ((2 ^ 7 * (epsilon β I.Λ (j + 1))⁻¹) /
              (C * em⁻¹)) ^ 1 =
          (1280 / C) * em * epsilon β I.Λ (j + 1) ^ (β - 1) := by
      intro j hj
      have hr := Section2Induction.increment_scale_ratio (I := I) (m := m) (j := j) hC
      have he := Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := j + 1)
      have hbeta := epsilon_beta_div (E := epsilon β I.Λ (j + 1))
        (β := β) he
      rw [pow_one, hr]
      calc
        10 * epsilon β I.Λ (j + 1) ^ β *
            (2 ^ 7 * epsilon β I.Λ m /
              (C * epsilon β I.Λ (j + 1))) =
            (1280 / C) * em *
              (epsilon β I.Λ (j + 1) ^ β / epsilon β I.Λ (j + 1)) := by
                field_simp [ne_of_gt hC, ne_of_gt he]
                ring
        _ = (1280 / C) * em * epsilon β I.Λ (j + 1) ^ (β - 1) := by
          rw [hbeta]
    calc
      _ = ∑ j ∈ Finset.range m,
          (1280 / C) * em * epsilon β I.Λ (j + 1) ^ (β - 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm j hj
      _ = (1280 / C) * em *
          (∑ j ∈ Finset.range m, epsilon β I.Λ (j + 1) ^ (β - 1)) := by
            rw [Finset.mul_sum]
  have hsumBetaMinus :
      (∑ j ∈ Finset.range m, epsilon β I.Λ (j + 1) ^ (β - 1)) ≤
        3 / (5 * (β - 1)) := by
    have hshift :
        (∑ j ∈ Finset.range m, epsilon β I.Λ (j + 1) ^ (β - 1)) ≤
          ∑ j ∈ Finset.range (m + 1), epsilon β I.Λ j ^ (β - 1) := by
      calc
        _ ≤ ∑ j ∈ Finset.range m, epsilon β I.Λ j ^ (β - 1) := by
          apply Finset.sum_le_sum
          intro j hj
          exact Real.rpow_le_rpow
            (Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
            (Section2Induction.epsilon_step_le_of_minsep (I := I) j)
            (sub_nonneg.mpr (by linarith [I.one_lt_beta]))
        _ ≤ ∑ j ∈ Finset.range (m + 1), epsilon β I.Λ j ^ (β - 1) := by
          rw [Finset.sum_range_succ]
          exact le_add_of_nonneg_right (Real.rpow_nonneg
            (Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le _)
    have htel := telescoping_one I.one_lt_beta I.beta_lt
      I.two_pow_seven_le m
    have hmul : em * (5 *
        (∑ j ∈ Finset.range (m + 1), epsilon β I.Λ j ^ (β - 1))) ≤
        em * (3 / (β - 1)) := by
      have htel' : 5 * em *
          (∑ j ∈ Finset.range (m + 1), epsilon β I.Λ j ^ (β - 1)) ≤
          (3 / (β - 1)) * em := by
        simpa [em, mul_comm, mul_left_comm, mul_assoc] using htel
      nlinarith [htel']
    have hcancel := (mul_le_mul_iff_of_pos_left hem).mp hmul
    have hdiv :
        (∑ j ∈ Finset.range (m + 1), epsilon β I.Λ j ^ (β - 1)) ≤
          3 / (5 * (β - 1)) := by
      have hmulden := (le_div_iff₀ hβm1).mp hcancel
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 5 * (β - 1))).2
      nlinarith [hmulden]
    exact hshift.trans hdiv
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    have hbound := Section2Induction.barNorm_stream_increment_sum_bound hseq hinc m t 0 hS
    rw [hpow0] at hbound
    have hreal : 10 * (∑ j ∈ Finset.range m,
        epsilon β I.Λ (j + 1) ^ β) ≤ C := by
      have hCterm : 0 ≤ 768 / (β - 1) := by positivity
      dsimp [C]
      linarith [hzero, hCterm]
    have hfinal := hbound.trans (ENNReal.ofReal_le_ofReal hreal)
    simpa [C, em, pow_zero] using hfinal
  · have hn1 : n = 1 := by omega
    subst n
    have hbound := Section2Induction.barNorm_stream_increment_sum_bound hseq hinc m t 1 hS
    rw [hpow1] at hbound
    have hcoef : 1280 / C * (3 / (5 * (β - 1))) ≤ C := by
      have hCsmall : 768 / (β - 1) ≤ C := by dsimp [C]; linarith
      have hprod : 768 ≤ C * (β - 1) := (div_le_iff₀ hβm1).mp hCsmall
      have hfrac : 768 / (C * (β - 1)) ≤ 1 :=
        (div_le_iff₀ (mul_pos hC hβm1)).2 (by linarith)
      calc
        1280 / C * (3 / (5 * (β - 1))) = 768 / (C * (β - 1)) := by
          field_simp [ne_of_gt hC, ne_of_gt hβm1]
          norm_num
        _ ≤ 1 := hfrac
        _ ≤ C := hC1
    have hreal : (1280 / C) * em *
        (∑ j ∈ Finset.range m, epsilon β I.Λ (j + 1) ^ (β - 1)) ≤ C * em := by
      calc
        _ ≤ ((1280 / C) * em) * (3 / (5 * (β - 1))) := by
          exact mul_le_mul_of_nonneg_left hsumBetaMinus
            (mul_nonneg (by positivity) hem.le)
        _ ≤ C * em := by
          have hc := mul_le_mul_of_nonneg_right hcoef hem.le
          nlinarith [hc]
    have hfinal := hbound.trans (ENNReal.ofReal_le_ofReal hreal)
    simpa [C, em] using hfinal

/-- The full three-part stream-regularity spatial package follows from its first (increment)
display. This is the scale induction used in the existence of the stream sequence. -/
theorem stream_regularity_bounds_of_increment_bounds {β : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hinc : StreamIncrementBounds I Φ) :
    StreamRegularityBounds (11 + 768 / (β - 1)) I Φ := by
  let C : ℝ := 11 + 768 / (β - 1)
  change StreamRegularityBounds C I Φ
  intro m hm t
  refine ⟨?_, ?_, ?_⟩
  · exact hinc m hm t
  · intro n hn
    exact high_order_stream_bound_of_increment_bounds hseq hinc m t n hn
  · intro n hn
    simpa [C] using low_order_stream_bounds_of_increment_bounds hseq hinc m t n hn

end AVenhance.Infra.Construction
