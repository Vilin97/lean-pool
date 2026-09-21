/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# Integer binomial gap estimate

Blueprint node C02: with `2 ≤ d`, `2 ≤ q` and `8 * d ^ 2 ≤ r ≤ q`, writing
`T = r * (q - 1) - 1` and `U = q * (r - 1) + d * (q - 1)`, one has `T ≤ U`,
`U - T ≤ d * q`, and `r * Nat.choose (U + d) d ≤ (r + 4 * d ^ 2) * Nat.choose (T + d) d`.
For `1 ≤ k ≤ d` one also has `Nat.choose (T + k) k ≤ q ^ k * Nat.choose (r + k - 1) k`.
-/

namespace Nikodym.LowerBound

open Finset

/-- From `2 ≤ d` and `8 * d ^ 2 ≤ r` one has `1 ≤ r`. -/
private theorem one_le_r {d r : ℕ} (hd : 2 ≤ d) (hr : 8 * d ^ 2 ≤ r) : 1 ≤ r := by
  have hdpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
  exact (Nat.succ_le_of_lt (Nat.mul_pos (by decide : 0 < 8) (Nat.pow_pos hdpos))).trans hr

/-- `1 ≤ q - 1` from `2 ≤ q`. -/
private theorem one_le_q_sub_one {q : ℕ} (hq : 2 ≤ q) : 1 ≤ q - 1 :=
  Nat.le_sub_of_add_le (show 1 + 1 ≤ q from hq)

/-- `T + 1 = r * (q - 1)` when this difference is genuine. -/
private theorem T_add_one {q r : ℕ} (hq : 2 ≤ q) (hr1 : 1 ≤ r) :
    r * (q - 1) - 1 + 1 = r * (q - 1) :=
  Nat.sub_add_cancel (Nat.mul_le_mul hr1 (one_le_q_sub_one hq))

/-- Blueprint C02: if `0 ≤ x i` and `∑ x i ≤ 1 / 2`, then `∏ (1 + x i) ≤ 1 + 2 * ∑ x i`. -/
private theorem prod_one_add_le {ι : Type*} (s : Finset ι) (x : ι → ℚ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hs : ∑ i ∈ s, x i ≤ (1 / 2 : ℚ)) :
    ∏ i ∈ s, (1 + x i) ≤ 1 + 2 * ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hxa : 0 ≤ x a := hx a (mem_insert_self _ _)
    have hx' : ∀ i ∈ s, 0 ≤ x i := fun i hi ↦ hx i (mem_insert_of_mem hi)
    have hs' : ∑ i ∈ s, x i ≤ 1 / 2 := by
      rw [sum_insert ha] at hs
      exact (le_add_of_nonneg_left hxa).trans hs
    have ih' := ih hx' hs'
    set xa := x a
    set S := ∑ i ∈ s, x i
    have hS : 2 * S ≤ 1 := by linarith [hs']
    have hexp : (1 + xa) * (1 + 2 * S) = 1 + 2 * (S + xa) + (2 * S - 1) * xa := by ring
    rw [prod_insert ha, sum_insert ha]
    have hmul : (1 + xa) * ∏ i ∈ s, (1 + x i) ≤ (1 + xa) * (1 + 2 * S) :=
      mul_le_mul_of_nonneg_left ih' (add_nonneg zero_le_one hxa)
    have hdrop : 1 + 2 * (S + xa) + (2 * S - 1) * xa ≤ 1 + 2 * (S + xa) := by
      have ht : (2 * S - 1) * xa ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hS) hxa
      linarith
    have hcomm : 1 + 2 * (S + xa) = 1 + 2 * (xa + S) := by rw [add_comm S]
    exact (hmul.trans hexp.le).trans (hdrop.trans hcomm.le)

/-- Blueprint C02: `T ≤ U`. -/
theorem T_le_U {d q r : ℕ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hr : 8 * d ^ 2 ≤ r) :
    r * (q - 1) - 1 ≤ q * (r - 1) + d * (q - 1) := by
  have hr1 := one_le_r hd hr
  have hq1 : 1 ≤ q := (by decide : 1 ≤ 2).trans hq
  have hd1 : 1 ≤ d := (by decide : 1 ≤ 2).trans hd
  set q' := q - 1
  set r' := r - 1
  have hqeq : q = q' + 1 := (Nat.sub_add_cancel hq1).symm
  have hreq : r = r' + 1 := (Nat.sub_add_cancel hr1).symm
  rw [hqeq, hreq, Nat.sub_le_iff_le_add, Nat.add_one_mul, Nat.add_one_mul]
  -- `r' * q' + q' ≤ q' * r' + r' + d * q' + 1`
  rw [Nat.mul_comm r' q']
  have hqq : q' ≤ d * q' := Nat.le_mul_of_pos_left q' hd1
  omega

/-- Exact difference `U - T = (d - 1) * (q - 1) + r`. -/
private theorem U_sub_T_eq {d q r : ℕ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hr : 8 * d ^ 2 ≤ r) :
    q * (r - 1) + d * (q - 1) - (r * (q - 1) - 1) = (d - 1) * (q - 1) + r := by
  have hle := T_le_U hd hq hr
  have hr1 := one_le_r hd hr
  have hq1 : 1 ≤ q := (by decide : 1 ≤ 2).trans hq
  have hd1 : 1 ≤ d := (by decide : 1 ≤ 2).trans hd
  have hT : 1 ≤ r * (q - 1) := Nat.mul_le_mul hr1 (one_le_q_sub_one hq)
  refine Int.natCast_inj.mp ?_
  simp only [Nat.cast_sub hle, Nat.cast_sub hT, Nat.cast_sub hr1, Nat.cast_sub hq1,
    Nat.cast_sub hd1, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

/-- Blueprint C02: `U - T ≤ d * q`. -/
theorem U_sub_T_le {d q r : ℕ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hr : 8 * d ^ 2 ≤ r) (hrq : r ≤ q) :
    q * (r - 1) + d * (q - 1) - (r * (q - 1) - 1) ≤ d * q := by
  have hd1 : 1 ≤ d := (by decide : 1 ≤ 2).trans hd
  rw [U_sub_T_eq hd hq hr]
  calc
    (d - 1) * (q - 1) + r ≤ (d - 1) * q + r := Nat.add_le_add_right
      (Nat.mul_le_mul_left (d - 1) (Nat.sub_le q 1)) _
    _ ≤ (d - 1) * q + q := Nat.add_le_add_left hrq _
    _ = d * q := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hd1]

/-- Blueprint C02: `r * Nat.choose (U + d) d ≤ (r + 4 * d ^ 2) * Nat.choose (T + d) d`. -/
theorem r_mul_choose_le {d q r : ℕ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hr : 8 * d ^ 2 ≤ r)
    (hrq : r ≤ q) :
    r * ((q * (r - 1) + d * (q - 1) + d).choose d) ≤
      (r + 4 * d ^ 2) * ((r * (q - 1) - 1 + d).choose d) := by
  set T := r * (q - 1) - 1
  set U := q * (r - 1) + d * (q - 1)
  have hr1 := one_le_r hd hr
  have hTU : T ≤ U := T_le_U hd hq hr
  have hT1 : T + 1 = r * (q - 1) := T_add_one hq hr1
  have hUT_le : U - T ≤ d * q := U_sub_T_le hd hq hr hrq
  have hN :
      (U + d).choose d * ∏ i ∈ range d, (T + 1 + i) =
        (T + d).choose d * ∏ i ∈ range d, (U + 1 + i) := by
    simpa [Nat.ascFactorial_eq_prod_range] using
      calc
        (U + d).choose d * (T + 1).ascFactorial d
            = (U + d).choose d * (d.factorial * (T + d).choose d) := by
              rw [Nat.ascFactorial_eq_factorial_mul_choose]
          _ = (T + d).choose d * (d.factorial * (U + d).choose d) := by ring
          _ = (T + d).choose d * (U + 1).ascFactorial d := by
              rw [Nat.ascFactorial_eq_factorial_mul_choose]
  have hQ :
      ((U + d).choose d : ℚ) * ∏ i ∈ range d, ((T + 1 + i : ℕ) : ℚ) =
        ((T + d).choose d : ℚ) * ∏ i ∈ range d, ((U + 1 + i : ℕ) : ℚ) := by
    simpa [Nat.cast_mul, Nat.cast_prod] using congrArg (Nat.cast : ℕ → ℚ) hN
  have hprodT_ne : ∏ i ∈ range d, ((T + 1 + i : ℕ) : ℚ) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i _ ↦ Nat.cast_ne_zero.2 ?_
    exact (Nat.add_pos_left (Nat.succ_pos T) i).ne'
  have hchT_ne : ((T + d).choose d : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.choose_pos (Nat.le_add_left d T)).ne'
  have hratio :
      ((U + d).choose d : ℚ) / (T + d).choose d =
        ∏ i ∈ range d, ((U + 1 + i : ℕ) : ℚ) / (T + 1 + i : ℕ) := by
    rw [div_eq_iff hchT_ne, prod_div_distrib, div_mul_eq_mul_div, eq_div_iff hprodT_ne]
    convert hQ using 1
    ring
  let x : ℕ → ℚ := fun i ↦ ((U - T : ℕ) : ℚ) / (T + 1 + i : ℕ)
  have hx_eq : ∀ i ∈ range d, ((U + 1 + i : ℕ) : ℚ) / (T + 1 + i : ℕ) = 1 + x i := by
    intro i _
    have hne : ((T + 1 + i : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.add_pos_left (Nat.succ_pos T) i).ne'
    change _ = 1 + _ / _
    rw [one_add_div hne]
    congr 1
    exact_mod_cast (by omega : U + 1 + i = T + 1 + i + (U - T))
  have hx0 : ∀ i ∈ range d, 0 ≤ x i := fun i _ ↦
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hq1pos : 0 < q - 1 := Nat.lt_of_succ_le (one_le_q_sub_one hq)
  have hT1_pos : (0 : ℚ) < (T + 1 : ℕ) := Nat.cast_pos.2 (Nat.succ_pos T)
  have hr_pos : (0 : ℚ) < r := Nat.cast_pos.2 hr1
  have hx_le : ∀ i ∈ range d, x i ≤ (2 * d : ℚ) / r := by
    intro i _
    have hx1 : x i ≤ ((U - T : ℕ) : ℚ) / (T + 1 : ℕ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hT1_pos
        (Nat.cast_le.2 (Nat.le_add_right (T + 1) i))
    have hx2 : ((U - T : ℕ) : ℚ) / (T + 1 : ℕ) ≤ (d * q : ℚ) / (T + 1 : ℕ) := by
      gcongr
      exact_mod_cast hUT_le
    refine hx1.trans (hx2.trans ?_)
    rw [hT1, Nat.cast_mul]
    have hden : (0 : ℚ) < (r : ℚ) * ((q - 1 : ℕ) : ℚ) :=
      mul_pos hr_pos (Nat.cast_pos.2 hq1pos)
    rw [div_le_div_iff₀ hden hr_pos]
    set q1 := ((q - 1 : ℕ) : ℚ)
    set dq := (d : ℚ) * (q : ℚ)
    set dr := (d : ℚ) * (r : ℚ)
    have hq2n : q ≤ 2 * (q - 1) := by
      have hqeq : q = q - 1 + 1 :=
        (Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans hq)).symm
      rw [hqeq, two_mul]
      exact Nat.add_le_add_left (one_le_q_sub_one hq) (q - 1)
    have hq2 : (q : ℚ) ≤ 2 * q1 := by
      simpa [q1] using (Nat.cast_le (α := ℚ)).mpr hq2n
    have hdr : (0 : ℚ) ≤ dr := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc
      dq * (r : ℚ) = dr * (q : ℚ) := by unfold dq dr; ring
      _ ≤ dr * (2 * q1) := mul_le_mul_of_nonneg_left hq2 hdr
      _ = (2 * (d : ℚ)) * ((r : ℚ) * q1) := by unfold dr q1; ring
  have hsum : ∑ i ∈ range d, x i ≤ (2 * d ^ 2 : ℚ) / r := by
    calc
      ∑ i ∈ range d, x i ≤ ∑ i ∈ range d, (2 * d : ℚ) / r := sum_le_sum hx_le
      _ = d * ((2 * d : ℚ) / r) := by simp [sum_const, card_range]
      _ = (2 * d ^ 2 : ℚ) / r := by ring
  have hsum14 : ∑ i ∈ range d, x i ≤ (1 / 4 : ℚ) := by
    refine hsum.trans ?_
    rw [div_le_div_iff₀ hr_pos (by norm_num : (0 : ℚ) < 4)]
    calc
      (2 * (d : ℚ) ^ 2) * 4 = (8 * d ^ 2 : ℕ) := by push_cast; ring
      _ ≤ (r : ℚ) := Nat.cast_le.2 hr
      _ = (1 : ℚ) * r := by simp
  have hprod : ∏ i ∈ range d, (1 + x i) ≤ 1 + (4 * d ^ 2 : ℚ) / r := by
    have h12 : ∑ i ∈ range d, x i ≤ (1 / 2 : ℚ) := hsum14.trans (by norm_num)
    have hprod' := prod_one_add_le (range d) x hx0 h12
    have h2 : (0 : ℚ) ≤ 2 := by norm_num
    have hstep : 1 + 2 * ∑ i ∈ range d, x i ≤ 1 + 2 * ((2 * d ^ 2 : ℚ) / r) :=
      add_le_add (le_rfl : (1 : ℚ) ≤ 1) (mul_le_mul_of_nonneg_left hsum h2)
    have hring : 1 + 2 * ((2 * d ^ 2 : ℚ) / r) = 1 + (4 * d ^ 2 : ℚ) / r := by
      set a := (d ^ 2 : ℚ)
      set rr := (r : ℚ)
      ring
    exact hprod'.trans (hstep.trans hring.le)
  have hmain : (r : ℚ) * (U + d).choose d ≤
      (r + 4 * d ^ 2 : ℚ) * (T + d).choose d := by
    have hUP : ((U + d).choose d : ℚ) =
        (∏ i ∈ range d, (1 + x i)) * (T + d).choose d := by
      rw [← div_eq_iff hchT_ne, hratio, prod_congr rfl hx_eq]
    have hexp : (r : ℚ) * (1 + (4 * d ^ 2 : ℚ) / r) = r + 4 * d ^ 2 := by
      field_simp [hr_pos.ne']
    calc
      (r : ℚ) * (U + d).choose d
          = (r : ℚ) * ((∏ i ∈ range d, (1 + x i)) * (T + d).choose d) := by rw [hUP]
        _ = ((r : ℚ) * ∏ i ∈ range d, (1 + x i)) * (T + d).choose d := by
            rw [mul_assoc]
        _ ≤ ((r : ℚ) * (1 + (4 * d ^ 2 : ℚ) / r)) * (T + d).choose d :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hprod hr_pos.le) (Nat.cast_nonneg _)
        _ = (r + 4 * d ^ 2 : ℚ) * (T + d).choose d := by rw [hexp]
  exact_mod_cast hmain

/-- Blueprint C02: `Nat.choose (T + k) k ≤ q ^ k * Nat.choose (r + k - 1) k`. -/
theorem choose_T_le {d q r : ℕ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hr : 8 * d ^ 2 ≤ r)
    (_hrq : r ≤ q) {k : ℕ} (_hk : 1 ≤ k) (_hkd : k ≤ d) :
    (r * (q - 1) - 1 + k).choose k ≤ q ^ k * (r + k - 1).choose k := by
  set T := r * (q - 1) - 1
  have hr1 := one_le_r hd hr
  have hT1 : T + 1 = r * (q - 1) := T_add_one hq hr1
  have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
  have hfactor : ∀ i ∈ range k, T + 1 + i ≤ q * (r + i) := by
    intro i _
    rw [hT1]
    calc
      r * (q - 1) + i ≤ r * q + i :=
        Nat.add_le_add_right (Nat.mul_le_mul_left r (Nat.sub_le q 1)) _
      _ ≤ r * q + q * i := Nat.add_le_add_left (Nat.le_mul_of_pos_left i hqpos) _
      _ = q * (r + i) := by ring
  have hprod : ∏ i ∈ range k, (T + 1 + i) ≤ q ^ k * ∏ i ∈ range k, (r + i) := by
    calc
      ∏ i ∈ range k, (T + 1 + i) ≤ ∏ i ∈ range k, q * (r + i) := prod_le_prod' hfactor
      _ = (∏ i ∈ range k, q) * ∏ i ∈ range k, (r + i) := prod_mul_distrib
      _ = q ^ k * ∏ i ∈ range k, (r + i) := by simp [prod_const, card_range]
  have hL : (T + 1).ascFactorial k = k.factorial * (T + k).choose k :=
    Nat.ascFactorial_eq_factorial_mul_choose T k
  have hR : r.ascFactorial k = k.factorial * (r + k - 1).choose k :=
    Nat.ascFactorial_eq_factorial_mul_choose' r k
  have hasc : (T + 1).ascFactorial k ≤ q ^ k * r.ascFactorial k := by
    simpa [Nat.ascFactorial_eq_prod_range] using hprod
  have : k.factorial * (T + k).choose k ≤
      k.factorial * (q ^ k * (r + k - 1).choose k) := by
    rw [← hL]
    calc
      (T + 1).ascFactorial k ≤ q ^ k * r.ascFactorial k := hasc
      _ = q ^ k * (k.factorial * (r + k - 1).choose k) := by rw [hR]
      _ = k.factorial * (q ^ k * (r + k - 1).choose k) := by ring
  exact Nat.le_of_mul_le_mul_left this k.factorial_pos

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
