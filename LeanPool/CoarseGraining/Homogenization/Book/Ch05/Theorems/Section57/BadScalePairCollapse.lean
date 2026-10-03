/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScalePairTwoBranch
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentUnion
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleComponentBoundsTop

/-! # Bad Scale Pair Collapse -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Deterministic fixed-pair exponent collapse

This file contains the deterministic lower bounds on the raw tail parameters
from `BadScalePairTwoBranch`.  These are the first two manuscript-facing
collapses: the localized top range gives the `b*q` concentration scale, and the
crude bottom range gives the `t*q` discount scale.
-/

noncomputable section

private theorem rpow_three_mul_rpow_pow_nat_eq
    {x y : ℝ} {r : ℕ} :
    (3 : ℝ) ^ x * ((3 : ℝ) ^ y) ^ r =
      (3 : ℝ) ^ (x + y * (r : ℝ)) := by
  have hpow :
      ((3 : ℝ) ^ y) ^ r = (3 : ℝ) ^ (y * (r : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hpow]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]

/-- In the localized range with `q ≤ n`, the raw high-branch tail parameter
dominates the manuscript `b*q` scale, up to a summable geometric weight in
`m-q`. -/
theorem highTop_tailParameter_lower_bound
    {d : ℕ} [NeZero d]
    {K Cfluct θ a t α : ℝ} {q m n : ℕ}
    (hK : 0 < K) (hCfluct : 0 < Cfluct) (hθ : 0 < θ)
    (ha : 0 < a)
    (hαt : α < t) (hαb : α < (d : ℝ) / 2)
    (hαharm : α * (1 + ((d : ℝ) / 2) / a) < (d : ℝ) / 2)
    (hell : selectedBadPairScale K a t α q m n < n)
    (hqn : q ≤ n) (hnm : n < m) :
    let x : ℝ := α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let ell : ℕ := selectedBadPairScale K a t α q m n
    let b : ℝ := (d : ℝ) / 2
    let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
    let c : ℝ :=
      min (t - α)
        (min (b - α)
          (min ((t - α) * (1 + b / a))
            (b - α * (1 + b / a))))
    let highScale : ℝ :=
      Cfluct * (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
        θ ^ (2 : ℕ)
    let T : ℝ := (3 : ℝ) ^ (-x)
    let highLam : ℝ := T / (2 * K * highScale)
    let A : ℝ :=
      (3 : ℝ) ^ (b * (q : ℝ) - b * (L + 1)) /
        (2 * K * Cfluct * θ ^ (2 : ℕ))
    let ρ : ℝ := (3 : ℝ) ^ c
    A * ρ ^ (m - q) ≤ highLam := by
  intro x ell b L c highScale T highLam A ρ
  have hb_pos : 0 < b := by
    dsimp [b]
    have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hL_nonneg : 0 ≤ L := by
    have hden_pos : 0 < a * Real.log 3 := mul_pos ha hlog3_pos
    have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) :=
      Real.log_nonneg (le_max_right (2 * K) 1)
    dsimp [L]
    positivity
  have hℓn_le : ell ≤ n := le_of_lt hell
  have hnm_le : n ≤ m := le_of_lt hnm
  have hceil :
      (ell : ℝ) ≤ L + max (x / a) 0 + 1 := by
    simpa [x, ell, L] using
      selectedBadPairScale_cast_le_logOffset
        (K := K) (a := a) (t := t) (α := α)
        (q := q) (m := m) (n := n) ha
  have hexp_comp :
      b * ((n - ell : ℕ) : ℝ) - x ≥
        b * (q : ℝ) + c * ((m - q : ℕ) : ℝ) - b * (L + 1) := by
    have hraw :=
      highNatScaleExponent_lower_bound_of_ceil_q_le_n_sharp
        (a := a) (b := b) (t := t) (α := α) (L := L)
        (q := q) (m := m) (n := n) (ℓ := ell)
        ha hb_pos hαt hαb hαharm hL_nonneg
        hℓn_le hqn hnm_le
        (by simpa [x] using hceil)
    simpa [x, c] using hraw
  have hden_pos : 0 < 2 * K * Cfluct * θ ^ (2 : ℕ) := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hK) hCfluct)
      (pow_pos hθ 2)
  have hlam_eq :
      highLam =
        (3 : ℝ) ^ (b * ((n - ell : ℕ) : ℝ) - x) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
    let decay : ℝ :=
      (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ))
    have hdecay_pos : 0 < decay := by
      dsimp [decay]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
    have hquot :
        (3 : ℝ) ^ (-x) / decay =
          (3 : ℝ) ^ (b * ((n - ell : ℕ) : ℝ) - x) := by
      dsimp [decay, b]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring_nf
    dsimp [highLam, T, highScale]
    change
      (3 : ℝ) ^ (-x) /
          (2 * K * (Cfluct * decay * θ ^ (2 : ℕ))) =
        (3 : ℝ) ^ (b * ((n - ell : ℕ) : ℝ) - x) /
          (2 * K * Cfluct * θ ^ (2 : ℕ))
    calc
      (3 : ℝ) ^ (-x) /
          (2 * K * (Cfluct * decay * θ ^ (2 : ℕ)))
          =
        ((3 : ℝ) ^ (-x) / decay) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
            field_simp [hK.ne', hCfluct.ne', hθ.ne', hdecay_pos.ne']
      _ =
        (3 : ℝ) ^ (b * ((n - ell : ℕ) : ℝ) - x) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
            rw [hquot]
  have hpow_base :
      (3 : ℝ) ^ (b * (q : ℝ) + c * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
          (2 * K * Cfluct * θ ^ (2 : ℕ))
        =
      A * ρ ^ (m - q) := by
    dsimp [A, ρ]
    have hrpow :=
      rpow_three_mul_rpow_pow_nat_eq
        (x := b * (q : ℝ) - b * (L + 1))
        (y := c) (r := m - q)
    calc
      (3 : ℝ) ^ (b * (q : ℝ) + c * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
          (2 * K * Cfluct * θ ^ (2 : ℕ))
          =
        ((3 : ℝ) ^ (b * (q : ℝ) - b * (L + 1)) *
            ((3 : ℝ) ^ c) ^ (m - q)) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
            rw [hrpow]
            congr 1
            ring_nf
      _ =
        ((3 : ℝ) ^ (b * (q : ℝ) - b * (L + 1)) /
          (2 * K * Cfluct * θ ^ (2 : ℕ))) *
            ((3 : ℝ) ^ c) ^ (m - q) := by
            field_simp [hden_pos.ne']
  rw [hlam_eq, ← hpow_base]
  have hpow_le :
      (3 : ℝ) ^
          (b * (q : ℝ) + c * ((m - q : ℕ) : ℝ) - b * (L + 1)) ≤
        (3 : ℝ) ^ (b * ((n - ell : ℕ) : ℝ) - x) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp_comp
  exact div_le_div_of_nonneg_right hpow_le hden_pos.le

/-- In the crude bottom range, the raw crude tail parameter dominates the
manuscript `t*q` scale, up to a summable geometric weight in `m-q`. -/
theorem crudeBottom_tailParameter_lower_bound
    {K C θ a t α : ℝ} {q m n : ℕ}
    (hK : 0 < K) (hC : 0 < C) (hθ : 0 < θ)
    (ha : 0 < a) (ht : 0 < t) (hαt : α < t)
    (hnell : n ≤ selectedBadPairScale K a t α q m n)
    (hnq : n ≤ q) (hqm : q ≤ m) :
    let x : ℝ := α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
    let crudeScale : ℝ := K * (C * θ ^ (2 : ℕ))
    let T : ℝ := (3 : ℝ) ^ (-x)
    let crudeLam : ℝ := T / crudeScale
    let A : ℝ :=
      (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
        (K * C * θ ^ (2 : ℕ))
    let ρ : ℝ := (3 : ℝ) ^ (t - α)
    A * ρ ^ (m - q) ≤ crudeLam := by
  intro x L crudeScale T crudeLam A ρ
  let ell : ℕ := selectedBadPairScale K a t α q m n
  have hceil :
      (ell : ℝ) ≤ L + max (x / a) 0 + 1 := by
    simpa [x, ell, L] using
      selectedBadPairScale_cast_le_logOffset
        (K := K) (a := a) (t := t) (α := α)
        (q := q) (m := m) (n := n) ha
  have hn_bound : (n : ℝ) ≤ L + 1 := by
    exact
      n_le_logOffset_add_one_of_not_high_n_le_q
        (a := a) (t := t) (α := α) (L := L)
        (q := q) (m := m) (n := n) (ℓ := ell)
        ha ht hαt (by simpa [x] using hceil) hnell hnq hqm
  have hm_sub : m - n = (m - q) + (q - n) := by omega
  have hx_neg_eq :
      -x =
        (t - α) * ((m - q : ℕ) : ℝ) +
          t * ((q - n : ℕ) : ℝ) := by
    dsimp [x]
    rw [hm_sub]
    norm_num [Nat.cast_add]
    ring
  have hq_decomp :
      (q : ℝ) = (n : ℝ) + ((q - n : ℕ) : ℝ) := by
    have hnat : n + (q - n) = q := Nat.add_sub_of_le hnq
    exact_mod_cast hnat.symm
  have hexp_lower :
      t * (q : ℝ) - t * (L + 1) + (t - α) * ((m - q : ℕ) : ℝ) ≤ -x := by
    rw [hx_neg_eq, hq_decomp]
    have hn_mul : t * (n : ℝ) ≤ t * (L + 1) :=
      mul_le_mul_of_nonneg_left hn_bound ht.le
    nlinarith
  have hden_pos : 0 < K * C * θ ^ (2 : ℕ) := by
    exact mul_pos (mul_pos hK hC) (pow_pos hθ 2)
  have hlam_eq :
      crudeLam = (3 : ℝ) ^ (-x) / (K * C * θ ^ (2 : ℕ)) := by
    dsimp [crudeLam, T, crudeScale]
    ring
  have hpow_base :
      (3 : ℝ) ^
          (t * (q : ℝ) - t * (L + 1) +
            (t - α) * ((m - q : ℕ) : ℝ)) /
          (K * C * θ ^ (2 : ℕ))
        =
      A * ρ ^ (m - q) := by
    dsimp [A, ρ]
    have hrpow :=
      rpow_three_mul_rpow_pow_nat_eq
        (x := t * (q : ℝ) - t * (L + 1))
        (y := t - α) (r := m - q)
    calc
      (3 : ℝ) ^
          (t * (q : ℝ) - t * (L + 1) +
            (t - α) * ((m - q : ℕ) : ℝ)) /
          (K * C * θ ^ (2 : ℕ))
          =
        ((3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) *
            ((3 : ℝ) ^ (t - α)) ^ (m - q)) /
          (K * C * θ ^ (2 : ℕ)) := by
            rw [hrpow]
      _ =
        ((3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) /
          (K * C * θ ^ (2 : ℕ))) *
            ((3 : ℝ) ^ (t - α)) ^ (m - q) := by
            field_simp [hden_pos.ne']
  rw [hlam_eq, ← hpow_base]
  have hpow_le :
      (3 : ℝ) ^
          (t * (q : ℝ) - t * (L + 1) +
            (t - α) * ((m - q : ℕ) : ℝ)) ≤
        (3 : ℝ) ^ (-x) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp_lower
  exact div_le_div_of_nonneg_right hpow_le hden_pos.le

/-- In the mixed range `n <= q` where the localized scale is available, the
localized tail parameter has the exact interpolating exponent between the
concentration gain at scale `n` and the discount gain from `q - n`.  This is
kept separate from theorem-facing tails so that no weakened leading exponent is
exposed as a public endpoint. -/
theorem highBottom_tailParameter_interpolation_lower_bound
    {d : ℕ} [NeZero d]
    {K Cfluct θ a t α : ℝ} {q m n : ℕ}
    (hK : 0 < K) (hCfluct : 0 < Cfluct) (hθ : 0 < θ)
    (ha : 0 < a) (ht : 0 < t) (hαt : α < t)
    (hell : selectedBadPairScale K a t α q m n < n)
    (hnq : n ≤ q) (hqm : q ≤ m) :
    let x : ℝ := α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let ell : ℕ := selectedBadPairScale K a t α q m n
    let b : ℝ := (d : ℝ) / 2
    let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
    let highScale : ℝ :=
      Cfluct * (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
        θ ^ (2 : ℕ)
    let T : ℝ := (3 : ℝ) ^ (-x)
    let highLam : ℝ := T / (2 * K * highScale)
    let A : ℝ :=
      (3 : ℝ) ^
          (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
            (t - α) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
        (2 * K * Cfluct * θ ^ (2 : ℕ))
    A ≤ highLam := by
  intro x ell b L highScale T highLam A
  have hb_pos : 0 < b := by
    dsimp [b]
    have hd_pos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hx_div_nonpos :
      x / a ≤ 0 := by
    simpa [x] using
      highComplement_x_div_nonpos_of_n_le_q
        (a := a) (t := t) (α := α) (q := q) (m := m) (n := n)
        ha ht hαt hnq hqm
  have hceil :
      (ell : ℝ) ≤ L + max (x / a) 0 + 1 := by
    simpa [x, ell, L] using
      selectedBadPairScale_cast_le_logOffset
        (K := K) (a := a) (t := t) (α := α)
        (q := q) (m := m) (n := n) ha
  have hell_L : (ell : ℝ) ≤ L + 1 := by
    simpa [max_eq_right hx_div_nonpos] using hceil
  have hℓn_le : ell ≤ n := le_of_lt hell
  have hnell_cast :
      ((n - ell : ℕ) : ℝ) = (n : ℝ) - (ell : ℝ) := by
    exact_mod_cast (Nat.cast_sub hℓn_le :
      ((n - ell : ℕ) : ℝ) = (n : ℝ) - (ell : ℝ))
  have hm_sub : m - n = (m - q) + (q - n) := by omega
  have hx_neg_eq :
      -x =
        (t - α) * ((m - q : ℕ) : ℝ) +
          t * ((q - n : ℕ) : ℝ) := by
    dsimp [x]
    rw [hm_sub]
    norm_num [Nat.cast_add]
    ring
  have hq_decomp :
      (q : ℝ) = (n : ℝ) + ((q - n : ℕ) : ℝ) := by
    have hnat : n + (q - n) = q := Nat.add_sub_of_le hnq
    exact_mod_cast hnat.symm
  have hexp_lower :
      b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
            (t - α) * ((m - q : ℕ) : ℝ) - b * (L + 1) ≤
        b * ((n - ell : ℕ) : ℝ) - x := by
    rw [hnell_cast, hq_decomp]
    have hell_mul : b * (ell : ℝ) ≤ b * (L + 1) :=
      mul_le_mul_of_nonneg_left hell_L hb_pos.le
    nlinarith [hx_neg_eq]
  have hden_pos : 0 < 2 * K * Cfluct * θ ^ (2 : ℕ) := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hK) hCfluct)
      (pow_pos hθ 2)
  have hlam_eq :
      highLam =
        (3 : ℝ) ^ (b * ((n - ell : ℕ) : ℝ) - x) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
    let decay : ℝ :=
      (3 : ℝ) ^ ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ))
    have hdecay_pos : 0 < decay := by
      dsimp [decay]
      exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _
    have hquot :
        (3 : ℝ) ^ (-x) / decay =
          (3 : ℝ) ^ (b * ((n - ell : ℕ) : ℝ) - x) := by
      dsimp [decay, b]
      rw [div_eq_mul_inv]
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring_nf
    dsimp [highLam, T, highScale]
    change
      (3 : ℝ) ^ (-x) /
          (2 * K * (Cfluct * decay * θ ^ (2 : ℕ))) =
        (3 : ℝ) ^ (b * ((n - ell : ℕ) : ℝ) - x) /
          (2 * K * Cfluct * θ ^ (2 : ℕ))
    calc
      (3 : ℝ) ^ (-x) /
          (2 * K * (Cfluct * decay * θ ^ (2 : ℕ)))
          =
        ((3 : ℝ) ^ (-x) / decay) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
            field_simp [hK.ne', hCfluct.ne', hθ.ne', hdecay_pos.ne']
      _ =
        (3 : ℝ) ^ (b * ((n - ell : ℕ) : ℝ) - x) /
          (2 * K * Cfluct * θ ^ (2 : ℕ)) := by
            rw [hquot]
  rw [hlam_eq]
  have hpow_le :
      (3 : ℝ) ^
          (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
            (t - α) * ((m - q : ℕ) : ℝ) - b * (L + 1)) ≤
        (3 : ℝ) ^ (b * ((n - ell : ℕ) : ℝ) - x) :=
    Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp_lower
  exact div_le_div_of_nonneg_right hpow_le hden_pos.le

/-- In the bottom range `n <= q`, the crude tail parameter has the exact
discount exponent.  This lemma does not require the complementary condition
`n <= ell`; it is the crude half of the mixed-branch comparison. -/
theorem crudeBottom_tailParameter_discount_lower_bound
    {K C θ t α : ℝ} {q m n : ℕ}
    (hK : 0 < K) (hC : 0 < C) (hθ : 0 < θ)
    (hnq : n ≤ q) (hqm : q ≤ m) :
    let x : ℝ := α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let crudeScale : ℝ := K * (C * θ ^ (2 : ℕ))
    let T : ℝ := (3 : ℝ) ^ (-x)
    let crudeLam : ℝ := T / crudeScale
    let A : ℝ :=
      (3 : ℝ) ^
          (t * ((q - n : ℕ) : ℝ) +
            (t - α) * ((m - q : ℕ) : ℝ)) /
        (K * C * θ ^ (2 : ℕ))
    A ≤ crudeLam := by
  intro x crudeScale T crudeLam A
  have hm_sub : m - n = (m - q) + (q - n) := by omega
  have hx_neg_eq :
      -x =
        (t - α) * ((m - q : ℕ) : ℝ) +
          t * ((q - n : ℕ) : ℝ) := by
    dsimp [x]
    rw [hm_sub]
    norm_num [Nat.cast_add]
    ring
  have hden_pos : 0 < K * C * θ ^ (2 : ℕ) := by
    exact mul_pos (mul_pos hK hC) (pow_pos hθ 2)
  have hlam_eq :
      crudeLam = (3 : ℝ) ^ (-x) / (K * C * θ ^ (2 : ℕ)) := by
    dsimp [crudeLam, T, crudeScale]
    ring
  rw [hlam_eq]
  dsimp [A]
  have hpow_eq :
      (3 : ℝ) ^
          (t * ((q - n : ℕ) : ℝ) +
            (t - α) * ((m - q : ℕ) : ℝ)) =
        (3 : ℝ) ^ (-x) := by
    rw [hx_neg_eq]
    congr 1
    ring
  rw [hpow_eq]

/-- Direct localized estimate for the mixed bottom branch.

The conclusion keeps the exact interpolating exponent.  This is stronger than
the two-branch soft estimate when the localized branch is the better one, and
it is used later only before the final endpoint collapse. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_high
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry a : ℝ,
      0 < Cfluct ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let tau : ℝ := min σ 2
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        let highA : ℝ :=
          (3 : ℝ) ^
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → 0 < t → αbad < t →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          softPairTail pref highA tau := by
  obtain ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, hrawAll⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Centry, a, hCfluct, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n
  dsimp only
  intro hnm hqm ht hαt
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ell : ℕ := selectedBadPairScale K a t αbad q m n
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let tau : ℝ := min σ 2
  let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
  let highA : ℝ :=
    (3 : ℝ) ^
        (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
      (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
  by_cases hnq : n ≤ q
  · by_cases hell : selectedBadPairScale K a t αbad q m n < n
    · let highScale : ℝ :=
        Cfluct *
          (3 : ℝ) ^
            ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
          hΓ.thetaHat ^ (2 : ℕ)
      let T : ℝ := Real.rpow (3 : ℝ) (-x)
      let highLam : ℝ := T / (2 * K * highScale)
      have hK_pos : 0 < K := by
        simpa [K] using quenchedProbeEnvelopeConst_pos d
      have hHighLam : highA ≤ highLam := by
        simpa [K, x, ell, b, L, highScale, T, highLam, highA] using
          highBottom_tailParameter_interpolation_lower_bound
            (d := d) (K := K) (Cfluct := Cfluct)
            (θ := hΓ.thetaHat) (a := a) (t := t) (α := αbad)
            (q := q) (m := m) (n := n)
            hK_pos hCfluct hΓ.thetaHat_pos ha ht hαt hell hnq hqm
      have htau_pos : 0 < tau := by
        dsimp [tau]
        exact lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
      have hsoft_raw :
          P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
            softPairTail pref highLam tau := by
        by_cases hlam : 1 ≤ highLam
        · have hraw :=
            hrawAll (t := t) (αbad := αbad)
              hP hStruct hΓ hσ_eq hparams
              (q := q) (m := m) (n := n)
          dsimp only at hraw
          have hbad :
              P.real (badPairEvent Hshift t αbad q m n) ≤
                (S.card : ℝ) *
                  ((D.card : ℝ) * Real.exp (-(highLam ^ tau))) := by
            simpa [K, x, ell, selectedBadPairScale, N0, Hshift, D, S, tau,
              highScale, T, highLam] using
              hraw hell hnm hqm hlam
          have hmono :
              P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
                P.real (badPairEvent Hshift t αbad q m n) :=
            measureReal_mono (μ := P) (by
              intro ω hω
              exact hω.2.2)
          have hpref : 0 ≤ pref := by
            dsimp [pref]
            positivity
          exact
            hmono.trans
              (hbad.trans
                (by
                  simpa [pref, mul_assoc] using
                    pref_mul_exp_le_softPairTail_of_one_le_lam
                      (pref := pref) (lam := highLam) (η := tau)
                      hpref hlam))
        · exact
            (measureReal_le_one
              (μ := P)
              (s := highBottomPairEvent Hshift K a t αbad q m n)).trans
              (one_le_softPairTail_of_not_one_le_lam
                (pref := pref) (lam := highLam) (η := tau) hlam)
      exact
        hsoft_raw.trans
          (softPairTail_mono_lam
            (pref := pref) (lam₁ := highA) (lam₂ := highLam)
            (η := tau) htau_pos hHighLam)
    · have hempty :
          highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
        ext ω
        simp [highBottomPairEvent, hell]
      rw [hempty]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
      exact softPairTail_nonneg
  · have hempty :
        highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [highBottomPairEvent, hnq]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact softPairTail_nonneg

/-- Direct crude estimate for the mixed bottom branch.

This is independent of the selected localized scale: the event is a subset of
the bad-pair event, and the unit-scale crude input supplies the discount
parameter in the bottom range. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_crude
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccrude Centry a : ℝ,
      0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        let crudeA : ℝ :=
          (3 : ℝ) ^
              (t * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ)) /
            (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → αbad < t →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          softPairTail pref crudeA σ := by
  obtain ⟨Cfluct, Centry, a, _hCfluct, hCentry, ha, _hhighRaw⟩ :=
    measureReal_shiftedHigh_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  obtain ⟨Ccrude, hCcrude, hcrudeRaw⟩ :=
    measureReal_shiftedCrude_badPairEvent_quenchedProbeEnvelope_le_card_mul_card_mul_exp_noLog
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Ccrude, Centry, a, hCcrude, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n
  dsimp only
  intro hnm hqm hαt
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
  let crudeA : ℝ :=
    (3 : ℝ) ^
        (t * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ)) /
      (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
  by_cases hnq : n ≤ q
  · let crudeScale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
    let T : ℝ := Real.rpow (3 : ℝ) (-x)
    let crudeLam : ℝ := T / crudeScale
    have hK_pos : 0 < K := by
      simpa [K] using quenchedProbeEnvelopeConst_pos d
    have hCrudeLam : crudeA ≤ crudeLam := by
      simpa [K, x, crudeScale, T, crudeLam, crudeA] using
        crudeBottom_tailParameter_discount_lower_bound
          (K := K) (C := Ccrude) (θ := hΓ.thetaHat)
          (t := t) (α := αbad) (q := q) (m := m) (n := n)
          hK_pos hCcrude hΓ.thetaHat_pos hnq hqm
    have hsoft_raw :
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          softPairTail pref crudeLam σ := by
      by_cases hlam : 1 ≤ crudeLam
      · have hraw :=
          hcrudeRaw (t := t) (αbad := αbad)
            hP hStruct hΓ hσ_eq hparams
            (N0 := N0) (q := q) (m := m) (n := n)
        dsimp only at hraw
        have hbad :
            P.real (badPairEvent Hshift t αbad q m n) ≤
              (S.card : ℝ) *
                ((D.card : ℝ) * Real.exp (-(crudeLam ^ σ))) := by
          simpa [K, Hshift, x, D, S, crudeScale, T, crudeLam] using
            hraw hnm hqm hlam
        have hmono :
            P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
              P.real (badPairEvent Hshift t αbad q m n) :=
          measureReal_mono (μ := P) (by
            intro ω hω
            exact hω.2.2)
        have hpref : 0 ≤ pref := by
          dsimp [pref]
          positivity
        exact
          hmono.trans
            (hbad.trans
              (by
                simpa [pref, mul_assoc] using
                  pref_mul_exp_le_softPairTail_of_one_le_lam
                    (pref := pref) (lam := crudeLam) (η := σ)
                    hpref hlam))
      · exact
          (measureReal_le_one
            (μ := P)
            (s := highBottomPairEvent Hshift K a t αbad q m n)).trans
            (one_le_softPairTail_of_not_one_le_lam
              (pref := pref) (lam := crudeLam) (η := σ) hlam)
    exact
      hsoft_raw.trans
        (softPairTail_mono_lam
          (pref := pref) (lam₁ := crudeA) (lam₂ := crudeLam)
          (η := σ) hσ_pos hCrudeLam)
  · have hempty :
        highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [highBottomPairEvent, hnq]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact softPairTail_nonneg

/-- Exact probability-level estimate for the mixed bottom localized branch.

This is the delicate `n <= q` and `ell < n` region.  The conclusion deliberately
keeps the two honest raw mechanisms visible: the localized interpolation scale
and the crude discount scale.  The theorem-facing bad-scale tail must still
collapse these without turning the localized interpolation term into a leading
`c*q` estimate. -/
theorem measureReal_shiftedHighBottomPairEvent_quenchedProbeEnvelope_le_soft_mixed
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ {q m n : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let D : Finset (TriadicCube d) :=
          descendantsAtScale
            (originCube d (((N0 + m : ℕ) : ℤ)))
            (((N0 + n : ℕ) : ℤ))
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let tau : ℝ := min σ 2
        let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
        let highA : ℝ :=
          (3 : ℝ) ^
              (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
            (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
        let crudeA : ℝ :=
          (3 : ℝ) ^
              (t * ((q - n : ℕ) : ℝ) +
                (t - αbad) * ((m - q : ℕ) : ℝ)) /
            (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
        n < m → q ≤ m → 0 < t → αbad < t →
        P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
          softPairTail pref highA tau + softPairTail pref crudeA σ := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, hpair⟩ :=
    measureReal_shiftedBadPairEvent_quenchedProbeEnvelope_le_soft_two_branch
      (d := d) (σ := σ) hσ_pos params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad P hP hStruct hΓ hσ_eq hparams q m n
  dsimp only
  intro hnm hqm ht hαt
  classical
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let x : ℝ :=
    αbad * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  let ell : ℕ := selectedBadPairScale K a t αbad q m n
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let D : Finset (TriadicCube d) :=
    descendantsAtScale
      (originCube d (((N0 + m : ℕ) : ℤ)))
      (((N0 + n : ℕ) : ℤ))
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let tau : ℝ := min σ 2
  let pref : ℝ := (S.card : ℝ) * (D.card : ℝ)
  let highA : ℝ :=
    (3 : ℝ) ^
        (b * (q : ℝ) - (b - t) * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ) - b * (L + 1)) /
      (2 * K * Cfluct * hΓ.thetaHat ^ (2 : ℕ))
  let crudeA : ℝ :=
    (3 : ℝ) ^
        (t * ((q - n : ℕ) : ℝ) +
          (t - αbad) * ((m - q : ℕ) : ℝ)) /
      (K * Ccrude * hΓ.thetaHat ^ (2 : ℕ))
  by_cases hnq : n ≤ q
  · by_cases hell : selectedBadPairScale K a t αbad q m n < n
    · let highScale : ℝ :=
        Cfluct *
          (3 : ℝ) ^
            ((-(d : ℝ) / 2) * ((n - ell : ℕ) : ℝ)) *
          hΓ.thetaHat ^ (2 : ℕ)
      let T : ℝ := Real.rpow (3 : ℝ) (-x)
      let highLam : ℝ := T / (2 * K * highScale)
      let crudeScale : ℝ := K * (Ccrude * hΓ.thetaHat ^ (2 : ℕ))
      let crudeLam : ℝ := T / crudeScale
      have hbad :
          P.real (badPairEvent Hshift t αbad q m n) ≤
            softPairTail pref highLam tau +
              softPairTail pref crudeLam σ := by
        have hraw :=
          hpair (t := t) (αbad := αbad)
            hP hStruct hΓ hσ_eq hparams
            (q := q) (m := m) (n := n)
        simpa [K, x, ell, N0, Hshift, D, S, tau,
          highScale, T, highLam, crudeScale, crudeLam, pref] using
          hraw hnm hqm
      have hmono :
          P.real (highBottomPairEvent Hshift K a t αbad q m n) ≤
            P.real (badPairEvent Hshift t αbad q m n) :=
        measureReal_mono (μ := P) (by
          intro ω hω
          exact hω.2.2)
      have hK_pos : 0 < K := by
        simpa [K] using quenchedProbeEnvelopeConst_pos d
      have hHighLam : highA ≤ highLam := by
        simpa [K, x, ell, b, L, highScale, T, highLam, highA] using
          highBottom_tailParameter_interpolation_lower_bound
            (d := d) (K := K) (Cfluct := Cfluct)
            (θ := hΓ.thetaHat) (a := a) (t := t) (α := αbad)
            (q := q) (m := m) (n := n)
            hK_pos hCfluct hΓ.thetaHat_pos ha ht hαt hell hnq hqm
      have hCrudeLam : crudeA ≤ crudeLam := by
        simpa [K, x, crudeScale, T, crudeLam, crudeA] using
          crudeBottom_tailParameter_discount_lower_bound
            (K := K) (C := Ccrude) (θ := hΓ.thetaHat)
            (t := t) (α := αbad) (q := q) (m := m) (n := n)
            hK_pos hCcrude hΓ.thetaHat_pos hnq hqm
      have htau_pos : 0 < tau := by
        dsimp [tau]
        exact lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
      exact
        hmono.trans
          (hbad.trans
            (add_le_add
              (softPairTail_mono_lam
                (pref := pref) (lam₁ := highA) (lam₂ := highLam)
                (η := tau) htau_pos hHighLam)
              (softPairTail_mono_lam
                (pref := pref) (lam₁ := crudeA) (lam₂ := crudeLam)
                (η := σ) hσ_pos hCrudeLam)))
    · have hempty :
          highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
        ext ω
        simp [highBottomPairEvent, hell]
      rw [hempty]
      simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
      exact add_nonneg softPairTail_nonneg softPairTail_nonneg
  · have hempty :
        highBottomPairEvent Hshift K a t αbad q m n = ∅ := by
      ext ω
      simp [highBottomPairEvent, hnq]
    rw [hempty]
    simp only [Measure.real, measure_empty, ENNReal.toReal_zero]
    exact add_nonneg softPairTail_nonneg softPairTail_nonneg

end

end Section57
end Ch05
end Book
end Homogenization
