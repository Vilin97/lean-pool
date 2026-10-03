/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadPairSelection

/-! # Exponent Competition -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Exponent competition for the quenched minimal scale

This file contains the deterministic real-variable inequalities behind the
"on top of the exponent" step in Theorem `t.homogenization.quenched`.
-/

noncomputable section

theorem natCeil_le_add_max_zero_add_one
    {L y : ℝ} (hL : 0 ≤ L) :
    (Nat.ceil (L + y) : ℝ) ≤ L + max y 0 + 1 := by
  by_cases hsum : 0 ≤ L + y
  · have hceil : (Nat.ceil (L + y) : ℝ) < L + y + 1 :=
      Nat.ceil_lt_add_one hsum
    have hy : y ≤ max y 0 := le_max_left y 0
    linarith
  · have hceil_zero : Nat.ceil (L + y) = 0 :=
      Nat.ceil_eq_zero.mpr (le_of_not_ge hsum)
    have hnonneg : 0 ≤ L + max y 0 + 1 := by
      have hy_nonneg : 0 ≤ max y 0 := le_max_right y 0
      linarith
    simpa [hceil_zero] using hnonneg

theorem highExponentCompetitionConst_pos
    {a b t α : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hαt : α < t) (hαb : α < b)
    (hαharm : α * (1 + b / a) < b) :
    0 <
      min b
        (min (t - α)
          (min (b - α)
            (min ((t - α) * (1 + b / a))
              (b - α * (1 + b / a))))) := by
  have htα_pos : 0 < t - α := sub_pos.mpr hαt
  have hbα_pos : 0 < b - α := sub_pos.mpr hαb
  have hfactor_pos : 0 < 1 + b / a := by
    have hbdiv_pos : 0 < b / a := div_pos hb ha
    linarith
  have hc1_pos : 0 < (t - α) * (1 + b / a) :=
    mul_pos htα_pos hfactor_pos
  have hc2_pos : 0 < b - α * (1 + b / a) := by
    linarith
  exact
    lt_min hb
      (lt_min htα_pos
        (lt_min hbα_pos
          (lt_min hc1_pos hc2_pos)))

theorem highSharpExponentCompetitionConst_pos
    {a b t α : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hαt : α < t) (hαb : α < b)
    (hαharm : α * (1 + b / a) < b) :
    0 <
      min (t - α)
        (min (b - α)
          (min ((t - α) * (1 + b / a))
            (b - α * (1 + b / a)))) := by
  have hfull :=
    highExponentCompetitionConst_pos
      (a := a) (b := b) (t := t) (α := α)
      ha hb hαt hαb hαharm
  exact lt_of_lt_of_le hfull (min_le_right b _)

theorem exists_alpha_for_highCompetition
    {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    ∃ α : ℝ,
      0 < α ∧ α < t ∧ α < a ∧ α < b ∧
        α * (1 + b / a) < b := by
  let h : ℝ := a * b / (a + b)
  let M : ℝ := min t (min a (min b h))
  let α : ℝ := M / 2
  have hab_pos : 0 < a + b := by linarith
  have hh_pos : 0 < h := by
    dsimp [h]
    positivity
  have hM_pos : 0 < M := by
    dsimp [M]
    exact lt_min ht (lt_min ha (lt_min hb hh_pos))
  have hα_pos : 0 < α := by
    dsimp [α]
    linarith
  have hα_lt_M : α < M := by
    dsimp [α]
    linarith
  have hM_le_t : M ≤ t := by
    dsimp [M]
    exact min_le_left _ _
  have hM_le_a : M ≤ a := by
    dsimp [M]
    exact (min_le_right t _).trans (min_le_left _ _)
  have hM_le_b : M ≤ b := by
    dsimp [M]
    exact (min_le_right t _).trans
      ((min_le_right a _).trans (min_le_left _ _))
  have hM_le_h : M ≤ h := by
    dsimp [M, h]
    exact (min_le_right t _).trans
      ((min_le_right a _).trans (min_le_right _ _))
  have hα_lt_t : α < t := hα_lt_M.trans_le hM_le_t
  have hα_lt_a : α < a := hα_lt_M.trans_le hM_le_a
  have hα_lt_b : α < b := hα_lt_M.trans_le hM_le_b
  have hα_lt_h : α < h := hα_lt_M.trans_le hM_le_h
  have hfactor_pos : 0 < 1 + b / a := by
    have hbdiv_pos : 0 < b / a := div_pos hb ha
    linarith
  have hh_eq : h = b / (1 + b / a) := by
    dsimp [h]
    field_simp [ha.ne', hab_pos.ne']
  have hαharm : α * (1 + b / a) < b := by
    have hα_lt_div : α < b / (1 + b / a) := by
      simpa [hh_eq] using hα_lt_h
    exact (lt_div_iff₀ hfactor_pos).1 hα_lt_div
  exact ⟨α, hα_pos, hα_lt_t, hα_lt_a, hα_lt_b, hαharm⟩

private theorem high_positive_branch_c2_eq
    {a b t α : ℝ} (ha : 0 < a) :
    b - α * (1 + b / a) =
      (t - α) * (1 + b / a) + (b - t * (1 + b / a)) := by
  field_simp [ha.ne']
  ring

private theorem coefficient_switch_mul_le
    {c c1 c2 e r j : ℝ}
    (hc_le_c1 : c ≤ c1) (hc_le_c2 : c ≤ c2)
    (hc2_eq : c2 = c1 + e)
    (hr : 0 ≤ r) (hj : 0 ≤ j) (hjr : j ≤ r) :
    c * r ≤ c1 * r + e * j := by
  by_cases he : 0 ≤ e
  · have hr_le : c * r ≤ c1 * r :=
      mul_le_mul_of_nonneg_right hc_le_c1 hr
    have hej_nonneg : 0 ≤ e * j := mul_nonneg he hj
    nlinarith
  · have he_nonpos : e ≤ 0 := le_of_not_ge he
    have hj_mul : e * r ≤ e * j :=
      mul_le_mul_of_nonpos_left hjr he_nonpos
    have hr_le : c * r ≤ c2 * r :=
      mul_le_mul_of_nonneg_right hc_le_c2 hr
    rw [hc2_eq] at hr_le
    nlinarith

/-- Core real-variable exponent competition in the high range `q ≤ n`.

The variables are `r = m - q` and `j = n - q`, so `0 ≤ j ≤ r`.  The term
`L + max (x/a) 0 + 1` is the ceiling upper bound for the intermediate scale,
where `x = α r - t (r - j) = (α - t)r + t j`. -/
theorem highExponentCompetition_lower_bound
    {a b t α L q r j : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hαt : α < t) (hαb : α < b)
    (hαharm : α * (1 + b / a) < b)
    (_hL : 0 ≤ L) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hj : 0 ≤ j) (hjr : j ≤ r) :
    let x : ℝ := (α - t) * r + t * j
    let c : ℝ :=
      min b
        (min (t - α)
          (min (b - α)
            (min ((t - α) * (1 + b / a))
              (b - α * (1 + b / a)))))
    b * (q + j) - b * (L + max (x / a) 0 + 1) - x ≥
      c * (q + r) - b * (L + 1) := by
  intro x c
  let c1 : ℝ := (t - α) * (1 + b / a)
  let c2 : ℝ := b - α * (1 + b / a)
  let c3 : ℝ := t - α
  let c4 : ℝ := b - α
  let cj : ℝ := b - t * (1 + b / a)
  have hc_pos : 0 < c := by
    simpa [c, c1, c2, c3, c4] using
      highExponentCompetitionConst_pos
        (a := a) (b := b) (t := t) (α := α)
        ha hb hαt hαb hαharm
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hc_le_b : c ≤ b := by
    dsimp [c]
    exact min_le_left _ _
  have hc_le_c1 : c ≤ c1 := by
    dsimp [c, c1]
    exact (min_le_right b _).trans
      ((min_le_right (t - α) _).trans
        ((min_le_right (b - α) _).trans
          (min_le_left _ _)))
  have hc_le_c2 : c ≤ c2 := by
    dsimp [c, c2]
    exact (min_le_right b _).trans
      ((min_le_right (t - α) _).trans
        ((min_le_right (b - α) _).trans
          (min_le_right _ _)))
  have hc_le_c3 : c ≤ c3 := by
    dsimp [c, c3]
    exact (min_le_right b _).trans (min_le_left _ _)
  have hc_le_c4 : c ≤ c4 := by
    dsimp [c, c4]
    exact (min_le_right b _).trans
      ((min_le_right (t - α) _).trans (min_le_left _ _))
  by_cases hx : 0 ≤ x / a
  · have hmax : max (x / a) 0 = x / a := max_eq_left hx
    have heq :
        b * (q + j) - b * (L + max (x / a) 0 + 1) - x =
          b * q - b * (L + 1) + c1 * r + cj * j := by
      dsimp [x, c1, cj]
      rw [hmax]
      field_simp [ha.ne']
      ring
    rw [heq]
    have hq_le : c * q ≤ b * q :=
      mul_le_mul_of_nonneg_right hc_le_b hq
    have hc2_eq : c2 = c1 + cj := by
      simpa [c1, c2, cj] using
        high_positive_branch_c2_eq (a := a) (b := b) (t := t) (α := α) ha
    have hcomb : c * r ≤ c1 * r + cj * j :=
      coefficient_switch_mul_le hc_le_c1 hc_le_c2 hc2_eq hr hj hjr
    have hsum : c * q + c * r ≤ b * q + (c1 * r + cj * j) :=
      add_le_add hq_le hcomb
    calc
      c * (q + r) - b * (L + 1)
          = (c * q + c * r) - b * (L + 1) := by ring
      _ ≤ (b * q + (c1 * r + cj * j)) - b * (L + 1) :=
          sub_le_sub_right hsum _
      _ = b * q - b * (L + 1) + c1 * r + cj * j := by ring
  · have hmax : max (x / a) 0 = 0 := max_eq_right (le_of_not_ge hx)
    have heq :
        b * (q + j) - b * (L + max (x / a) 0 + 1) - x =
          b * q - b * (L + 1) + c3 * r + (b - t) * j := by
      dsimp [x, c3]
      rw [hmax]
      ring
    rw [heq]
    have hq_le : c * q ≤ b * q :=
      mul_le_mul_of_nonneg_right hc_le_b hq
    have hc4_eq : c4 = c3 + (b - t) := by
      dsimp [c3, c4]
      ring
    have hcomb : c * r ≤ c3 * r + (b - t) * j :=
      coefficient_switch_mul_le hc_le_c3 hc_le_c4 hc4_eq hr hj hjr
    have hsum : c * q + c * r ≤ b * q + (c3 * r + (b - t) * j) :=
      add_le_add hq_le hcomb
    calc
      c * (q + r) - b * (L + 1)
          = (c * q + c * r) - b * (L + 1) := by ring
      _ ≤ (b * q + (c3 * r + (b - t) * j)) - b * (L + 1) :=
          sub_le_sub_right hsum _
      _ = b * q - b * (L + 1) + c3 * r + (b - t) * j := by ring

/-- Integer-scale version of `highExponentCompetition_lower_bound`.

This is the form used for high bad pairs, where the bad scale `q` is below the
localized scale `n`. -/
theorem highNatScaleExponent_lower_bound_of_ceil
    {a b t α L : ℝ} {q m n ℓ : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (hαt : α < t) (hαb : α < b)
    (hαharm : α * (1 + b / a) < b)
    (hL : 0 ≤ L) (hℓn : ℓ ≤ n) (hqn : q ≤ n) (hnm : n ≤ m)
    (hceil :
      let x : ℝ :=
        α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
      (ℓ : ℝ) ≤ L + max (x / a) 0 + 1) :
    let x : ℝ :=
      α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let c : ℝ :=
      min b
        (min (t - α)
          (min (b - α)
            (min ((t - α) * (1 + b / a))
              (b - α * (1 + b / a)))))
    b * ((n - ℓ : ℕ) : ℝ) - x ≥
      c * ((q : ℝ) + ((m - q : ℕ) : ℝ)) - b * (L + 1) := by
  intro x c
  let r : ℝ := ((m - q : ℕ) : ℝ)
  let j : ℝ := ((n - q : ℕ) : ℝ)
  have hqm : q ≤ m := hqn.trans hnm
  have hjr_nat : n - q ≤ m - q := Nat.sub_le_sub_right hnm q
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
  have hj_nonneg : 0 ≤ j := by dsimp [j]; positivity
  have hjr : j ≤ r := by
    dsimp [j, r]
    exact_mod_cast hjr_nat
  have hmn_nat : m - n = (m - q) - (n - q) := by
    omega
  have hmn_cast :
      ((m - n : ℕ) : ℝ) =
        ((m - q : ℕ) : ℝ) - ((n - q : ℕ) : ℝ) := by
    rw [hmn_nat]
    exact_mod_cast (Nat.cast_sub hjr_nat :
      (((m - q) - (n - q) : ℕ) : ℝ) =
        ((m - q : ℕ) : ℝ) - ((n - q : ℕ) : ℝ))
  have hx_eq : x = (α - t) * r + t * j := by
    dsimp [x, r, j]
    rw [hmn_cast]
    ring
  have hn_decomp : (n : ℝ) = (q : ℝ) + j := by
    have hn_nat : q + (n - q) = n := Nat.add_sub_of_le hqn
    dsimp [j]
    exact_mod_cast hn_nat.symm
  have hnℓ_cast : ((n - ℓ : ℕ) : ℝ) = (n : ℝ) - (ℓ : ℝ) := by
    exact_mod_cast (Nat.cast_sub hℓn :
      ((n - ℓ : ℕ) : ℝ) = (n : ℝ) - (ℓ : ℝ))
  have hceil' : (ℓ : ℝ) ≤ L + max (x / a) 0 + 1 := by
    simpa [x] using hceil
  have hleft_ge :
      b * ((q : ℝ) + j) - b * (L + max (x / a) 0 + 1) - x ≤
        b * ((n - ℓ : ℕ) : ℝ) - x := by
    have hsub :
        (q : ℝ) + j - (L + max (x / a) 0 + 1) ≤
          ((n - ℓ : ℕ) : ℝ) := by
      rw [hnℓ_cast, hn_decomp]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsub hb.le
    linarith
  have hcore :=
    highExponentCompetition_lower_bound
      (a := a) (b := b) (t := t) (α := α) (L := L)
      (q := (q : ℝ)) (r := r) (j := j)
      ha hb hαt hαb hαharm hL hq_nonneg hr_nonneg hj_nonneg hjr
  dsimp only at hcore
  have hcore' :
      b * ((q : ℝ) + j) - b * (L + max (x / a) 0 + 1) - x ≥
        c * ((q : ℝ) + r) - b * (L + 1) := by
    simpa [x, c, r, j, hx_eq] using hcore
  exact hcore'.trans hleft_ge

/-- Sharp high-range exponent competition when the bad scale is below the
localized scale.  This keeps the manuscript's `b q` concentration gain. -/
theorem highExponentCompetition_lower_bound_sharp
    {a b t α L q r j : ℝ}
    (ha : 0 < a) (_hb : 0 < b)
    (_hαt : α < t) (_hαb : α < b)
    (_hαharm : α * (1 + b / a) < b)
    (_hL : 0 ≤ L) (hr : 0 ≤ r)
    (hj : 0 ≤ j) (hjr : j ≤ r) :
    let x : ℝ := (α - t) * r + t * j
    let c : ℝ :=
      min (t - α)
        (min (b - α)
          (min ((t - α) * (1 + b / a))
            (b - α * (1 + b / a))))
    b * (q + j) - b * (L + max (x / a) 0 + 1) - x ≥
      b * q + c * r - b * (L + 1) := by
  intro x c
  let c1 : ℝ := (t - α) * (1 + b / a)
  let c2 : ℝ := b - α * (1 + b / a)
  let c3 : ℝ := t - α
  let c4 : ℝ := b - α
  let cj : ℝ := b - t * (1 + b / a)
  have hc_le_c1 : c ≤ c1 := by
    dsimp [c, c1]
    exact (min_le_right (t - α) _).trans
      ((min_le_right (b - α) _).trans (min_le_left _ _))
  have hc_le_c2 : c ≤ c2 := by
    dsimp [c, c2]
    exact (min_le_right (t - α) _).trans
      ((min_le_right (b - α) _).trans (min_le_right _ _))
  have hc_le_c3 : c ≤ c3 := by
    dsimp [c, c3]
    exact min_le_left _ _
  have hc_le_c4 : c ≤ c4 := by
    dsimp [c, c4]
    exact (min_le_right (t - α) _).trans (min_le_left _ _)
  by_cases hx : 0 ≤ x / a
  · have hmax : max (x / a) 0 = x / a := max_eq_left hx
    have heq :
        b * (q + j) - b * (L + max (x / a) 0 + 1) - x =
          b * q - b * (L + 1) + c1 * r + cj * j := by
      dsimp [x, c1, cj]
      rw [hmax]
      field_simp [ha.ne']
      ring
    rw [heq]
    have hc2_eq : c2 = c1 + cj := by
      simpa [c1, c2, cj] using
        high_positive_branch_c2_eq (a := a) (b := b) (t := t) (α := α) ha
    have hcomb : c * r ≤ c1 * r + cj * j :=
      coefficient_switch_mul_le hc_le_c1 hc_le_c2 hc2_eq hr hj hjr
    calc
      b * q + c * r - b * (L + 1)
          ≤ b * q + (c1 * r + cj * j) - b * (L + 1) :=
        sub_le_sub_right (add_le_add le_rfl hcomb) _
      _ = b * q - b * (L + 1) + c1 * r + cj * j := by ring
  · have hmax : max (x / a) 0 = 0 := max_eq_right (le_of_not_ge hx)
    have heq :
        b * (q + j) - b * (L + max (x / a) 0 + 1) - x =
          b * q - b * (L + 1) + c3 * r + (b - t) * j := by
      dsimp [x, c3]
      rw [hmax]
      ring
    rw [heq]
    have hc4_eq : c4 = c3 + (b - t) := by
      dsimp [c3, c4]
      ring
    have hcomb : c * r ≤ c3 * r + (b - t) * j :=
      coefficient_switch_mul_le hc_le_c3 hc_le_c4 hc4_eq hr hj hjr
    calc
      b * q + c * r - b * (L + 1)
          ≤ b * q + (c3 * r + (b - t) * j) - b * (L + 1) :=
        sub_le_sub_right (add_le_add le_rfl hcomb) _
      _ = b * q - b * (L + 1) + c3 * r + (b - t) * j := by ring

/-- Integer-scale sharp high-range exponent competition in the case `q ≤ n`. -/
theorem highNatScaleExponent_lower_bound_of_ceil_q_le_n_sharp
    {a b t α L : ℝ} {q m n ℓ : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (hαt : α < t) (hαb : α < b)
    (hαharm : α * (1 + b / a) < b)
    (hL : 0 ≤ L) (hℓn : ℓ ≤ n) (hqn : q ≤ n) (hnm : n ≤ m)
    (hceil :
      let x : ℝ :=
        α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
      (ℓ : ℝ) ≤ L + max (x / a) 0 + 1) :
    let x : ℝ :=
      α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let c : ℝ :=
      min (t - α)
        (min (b - α)
          (min ((t - α) * (1 + b / a))
            (b - α * (1 + b / a))))
    b * ((n - ℓ : ℕ) : ℝ) - x ≥
      b * (q : ℝ) + c * ((m - q : ℕ) : ℝ) - b * (L + 1) := by
  intro x c
  let r : ℝ := ((m - q : ℕ) : ℝ)
  let j : ℝ := ((n - q : ℕ) : ℝ)
  have hjr_nat : n - q ≤ m - q := Nat.sub_le_sub_right hnm q
  have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
  have hj_nonneg : 0 ≤ j := by dsimp [j]; positivity
  have hjr : j ≤ r := by
    dsimp [j, r]
    exact_mod_cast hjr_nat
  have hmn_nat : m - n = (m - q) - (n - q) := by
    omega
  have hmn_cast :
      ((m - n : ℕ) : ℝ) =
        ((m - q : ℕ) : ℝ) - ((n - q : ℕ) : ℝ) := by
    rw [hmn_nat]
    exact_mod_cast (Nat.cast_sub hjr_nat :
      (((m - q) - (n - q) : ℕ) : ℝ) =
        ((m - q : ℕ) : ℝ) - ((n - q : ℕ) : ℝ))
  have hx_eq : x = (α - t) * r + t * j := by
    dsimp [x, r, j]
    rw [hmn_cast]
    ring
  have hn_decomp : (n : ℝ) = (q : ℝ) + j := by
    have hn_nat : q + (n - q) = n := Nat.add_sub_of_le hqn
    dsimp [j]
    exact_mod_cast hn_nat.symm
  have hnℓ_cast : ((n - ℓ : ℕ) : ℝ) = (n : ℝ) - (ℓ : ℝ) := by
    exact_mod_cast (Nat.cast_sub hℓn :
      ((n - ℓ : ℕ) : ℝ) = (n : ℝ) - (ℓ : ℝ))
  have hceil' : (ℓ : ℝ) ≤ L + max (x / a) 0 + 1 := by
    simpa [x] using hceil
  have hleft_ge :
      b * ((q : ℝ) + j) - b * (L + max (x / a) 0 + 1) - x ≤
        b * ((n - ℓ : ℕ) : ℝ) - x := by
    have hsub :
        (q : ℝ) + j - (L + max (x / a) 0 + 1) ≤
          ((n - ℓ : ℕ) : ℝ) := by
      rw [hnℓ_cast, hn_decomp]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsub hb.le
    linarith
  have hcore :=
    highExponentCompetition_lower_bound_sharp
      (a := a) (b := b) (t := t) (α := α) (L := L)
      (q := (q : ℝ)) (r := r) (j := j)
      ha hb hαt hαb hαharm hL hr_nonneg hj_nonneg hjr
  dsimp only at hcore
  have hcore' :
      b * ((q : ℝ) + j) - b * (L + max (x / a) 0 + 1) - x ≥
        b * (q : ℝ) + c * r - b * (L + 1) := by
    simpa [x, c, r, j, hx_eq] using hcore
  exact hcore'.trans hleft_ge

/-- High-scale exponent competition without assuming that the bad scale lies
below the localized scale.  If `q ≤ n`, this is the previous bridge with a
slightly smaller constant; if `n < q`, the post-discount exponent itself gives
the missing decay in `q - n`. -/
theorem highNatScaleExponent_lower_bound_of_ceil_any_q
    {a b t α L : ℝ} {q m n ℓ : ℕ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (hαt : α < t) (hαb : α < b)
    (hαharm : α * (1 + b / a) < b)
    (hL : 0 ≤ L) (hℓn : ℓ ≤ n) (hqm : q ≤ m) (hnm : n ≤ m)
    (hceil :
      let x : ℝ :=
        α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
      (ℓ : ℝ) ≤ L + max (x / a) 0 + 1) :
    let x : ℝ :=
      α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let c : ℝ :=
      min t
        (min b
          (min (t - α)
            (min (b - α)
              (min ((t - α) * (1 + b / a))
                (b - α * (1 + b / a))))))
    b * ((n - ℓ : ℕ) : ℝ) - x ≥
      c * ((q : ℝ) + ((m - q : ℕ) : ℝ)) - b * (L + 1) := by
  intro x c
  let cold : ℝ :=
    min b
      (min (t - α)
        (min (b - α)
          (min ((t - α) * (1 + b / a))
            (b - α * (1 + b / a)))))
  have hc_le_cold : c ≤ cold := by
    dsimp [c, cold]
    exact min_le_right _ _
  have hc_le_b : c ≤ b := by
    exact hc_le_cold.trans (by dsimp [cold]; exact min_le_left _ _)
  have hc_le_t : c ≤ t := by
    dsimp [c]
    exact min_le_left _ _
  have hc_le_tα : c ≤ t - α := by
    exact hc_le_cold.trans
      (by dsimp [cold]; exact (min_le_right b _).trans (min_le_left _ _))
  by_cases hqn : q ≤ n
  · have hcore :=
      highNatScaleExponent_lower_bound_of_ceil
        (a := a) (b := b) (t := t) (α := α) (L := L)
        (q := q) (m := m) (n := n) (ℓ := ℓ)
        ha hb hαt hαb hαharm hL hℓn hqn hnm hceil
    dsimp only at hcore
    have hqr_nonneg :
        0 ≤ ((q : ℝ) + ((m - q : ℕ) : ℝ)) := by positivity
    have hcold_bound :
        c * ((q : ℝ) + ((m - q : ℕ) : ℝ)) ≤
          cold * ((q : ℝ) + ((m - q : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hc_le_cold hqr_nonneg
    calc
      b * ((n - ℓ : ℕ) : ℝ) - x
          ≥ cold * ((q : ℝ) + ((m - q : ℕ) : ℝ)) - b * (L + 1) := hcore
      _ ≥ c * ((q : ℝ) + ((m - q : ℕ) : ℝ)) - b * (L + 1) :=
          sub_le_sub_right hcold_bound _
  · have hnq : n < q := Nat.lt_of_not_ge hqn
    have hx_nonpos : x / a ≤ 0 := by
      have hm_sub : m - n = (m - q) + (q - n) := by omega
      have hx_eq :
          x =
            -(t - α) * ((m - q : ℕ) : ℝ) -
              t * ((q - n : ℕ) : ℝ) := by
        dsimp [x]
        rw [hm_sub]
        norm_num [Nat.cast_add]
        ring
      have htα_pos : 0 < t - α := sub_pos.mpr hαt
      have hr_nonneg : 0 ≤ ((m - q : ℕ) : ℝ) := by positivity
      have hs_pos : 0 < ((q - n : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt hnq
      have hx_nonpos' : x ≤ 0 := by
        have hleft_nonpos :
            -(t - α) * ((m - q : ℕ) : ℝ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr htα_pos.le) hr_nonneg
        have hright_nonneg : 0 ≤ t * ((q - n : ℕ) : ℝ) :=
          (mul_pos ht hs_pos).le
        calc
          x = -(t - α) * ((m - q : ℕ) : ℝ) -
                t * ((q - n : ℕ) : ℝ) := hx_eq
          _ ≤ 0 - t * ((q - n : ℕ) : ℝ) :=
              sub_le_sub_right hleft_nonpos _
          _ ≤ 0 := sub_nonpos.mpr hright_nonneg
      exact div_nonpos_of_nonpos_of_nonneg hx_nonpos' ha.le
    have hceil_L :
        (ℓ : ℝ) ≤ L + 1 := by
      have hceil' : (ℓ : ℝ) ≤ L + max (x / a) 0 + 1 := by
        simpa [x] using hceil
      simpa [max_eq_right hx_nonpos] using hceil'
    have hnℓ_cast :
        ((n - ℓ : ℕ) : ℝ) = (n : ℝ) - (ℓ : ℝ) := by
      exact_mod_cast (Nat.cast_sub hℓn :
        ((n - ℓ : ℕ) : ℝ) = (n : ℝ) - (ℓ : ℝ))
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
      have hnat : n + (q - n) = q := Nat.add_sub_of_le (le_of_lt hnq)
      exact_mod_cast hnat.symm
    have hleft_ge :
        b * ((n - ℓ : ℕ) : ℝ) - x ≥
          b * (n : ℝ) - b * (L + 1) - x := by
      rw [hnℓ_cast]
      have hmul := mul_le_mul_of_nonneg_left hceil_L hb.le
      calc
        b * ((n : ℝ) - (ℓ : ℝ)) - x
            = b * (n : ℝ) - b * (ℓ : ℝ) - x := by ring
        _ ≥ b * (n : ℝ) - b * (L + 1) - x :=
            sub_le_sub_right (sub_le_sub_left hmul (b * (n : ℝ))) x
    have hmain :
        b * (n : ℝ) - x ≥
          c * ((q : ℝ) + ((m - q : ℕ) : ℝ)) := by
      have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
      have hs_nonneg : 0 ≤ ((q - n : ℕ) : ℝ) := by positivity
      have hr_nonneg : 0 ≤ ((m - q : ℕ) : ℝ) := by positivity
      have hn_part : c * (n : ℝ) ≤ b * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hc_le_b hn_nonneg
      have hs_part : c * ((q - n : ℕ) : ℝ) ≤
          t * ((q - n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hc_le_t hs_nonneg
      have hr_part : c * ((m - q : ℕ) : ℝ) ≤
          (t - α) * ((m - q : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hc_le_tα hr_nonneg
      have hleft_eq :
          b * (n : ℝ) - x =
            b * (n : ℝ) +
              ((t - α) * ((m - q : ℕ) : ℝ) +
                t * ((q - n : ℕ) : ℝ)) := by
        rw [← hx_neg_eq]
        ring
      have hright_eq :
          c * ((q : ℝ) + ((m - q : ℕ) : ℝ)) =
              c * ((n : ℝ) + ((q - n : ℕ) : ℝ) +
                ((m - q : ℕ) : ℝ)) := by
        rw [hq_decomp]
      rw [hleft_eq, hright_eq]
      have hsum :
          c * ((n : ℝ) + ((q - n : ℕ) : ℝ) +
              ((m - q : ℕ) : ℝ)) ≤
            b * (n : ℝ) + t * ((q - n : ℕ) : ℝ) +
              (t - α) * ((m - q : ℕ) : ℝ) := by
        calc
          c * ((n : ℝ) + ((q - n : ℕ) : ℝ) +
                ((m - q : ℕ) : ℝ))
              = c * (n : ℝ) + c * ((q - n : ℕ) : ℝ) +
                  c * ((m - q : ℕ) : ℝ) := by ring
          _ ≤ b * (n : ℝ) + t * ((q - n : ℕ) : ℝ) +
                (t - α) * ((m - q : ℕ) : ℝ) :=
              add_le_add (add_le_add hn_part hs_part) hr_part
      calc
        c * ((n : ℝ) + ((q - n : ℕ) : ℝ) +
            ((m - q : ℕ) : ℝ))
            ≤ b * (n : ℝ) + t * ((q - n : ℕ) : ℝ) +
                (t - α) * ((m - q : ℕ) : ℝ) := hsum
        _ = b * (n : ℝ) +
              ((t - α) * ((m - q : ℕ) : ℝ) +
                t * ((q - n : ℕ) : ℝ)) := by ring
    calc
      b * ((n - ℓ : ℕ) : ℝ) - x
          ≥ b * (n : ℝ) - b * (L + 1) - x := hleft_ge
      _ = b * (n : ℝ) - x - b * (L + 1) := by ring
      _ ≥ c * ((q : ℝ) + ((m - q : ℕ) : ℝ)) - b * (L + 1) :=
          sub_le_sub_right hmain _

/-- If the selected high scale is not below `n` and the exponent correction is
nonpositive, then `n` is bounded by the deterministic logarithmic offset. -/
theorem n_le_logOffset_add_one_of_not_high_x_nonpos
    {a L x : ℝ} {n ℓ : ℕ}
    (hceil : (ℓ : ℝ) ≤ L + max (x / a) 0 + 1)
    (hx : x / a ≤ 0) (hnℓ : n ≤ ℓ) :
    (n : ℝ) ≤ L + 1 := by
  have hn_le_ℓ : (n : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hnℓ
  have hℓ_bound : (ℓ : ℝ) ≤ L + 1 := by
    simpa [max_eq_right hx] using hceil
  linarith

/-- If the selected high scale is not below `n`, and the exponent correction is
at most `α n` with `α < a`, then `n` is bounded by the deterministic logarithmic
offset with buffer `1 - α/a`. -/
theorem scale_bound_of_not_high_x_le_alpha_mul_n
    {a α L x : ℝ} {n ℓ : ℕ}
    (ha : 0 < a) (hα_nonneg : 0 ≤ α) (_hαa : α < a)
    (hceil : (ℓ : ℝ) ≤ L + max (x / a) 0 + 1)
    (hx : x ≤ α * (n : ℝ)) (hnℓ : n ≤ ℓ) :
    (1 - α / a) * (n : ℝ) ≤ L + 1 := by
  have hn_le_ℓ : (n : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hnℓ
  have hxa :
      x / a ≤ (α / a) * (n : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hx ha.le
    calc
      x / a ≤ α * (n : ℝ) / a := hdiv
      _ = (α / a) * (n : ℝ) := by ring
  have htarget_nonneg : 0 ≤ (α / a) * (n : ℝ) := by positivity
  have hmax_le : max (x / a) 0 ≤ (α / a) * (n : ℝ) :=
    max_le hxa htarget_nonneg
  have hℓ_bound : (ℓ : ℝ) ≤ L + (α / a) * (n : ℝ) + 1 := by
    linarith
  have hn_bound : (n : ℝ) ≤ L + (α / a) * (n : ℝ) + 1 :=
    hn_le_ℓ.trans hℓ_bound
  calc
    (1 - α / a) * (n : ℝ) = (n : ℝ) - (α / a) * (n : ℝ) := by ring
    _ ≤ (L + (α / a) * (n : ℝ) + 1) - (α / a) * (n : ℝ) :=
        sub_le_sub_right hn_bound _
    _ = L + 1 := by ring

/-- In the complementary high-scale range with `n ≤ q`, the exponent correction
is nonpositive. -/
theorem highComplement_x_div_nonpos_of_n_le_q
    {a t α : ℝ} {q m n : ℕ}
    (ha : 0 < a) (ht : 0 < t) (hαt : α < t)
    (hnq : n ≤ q) (hqm : q ≤ m) :
    let x : ℝ :=
      α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    x / a ≤ 0 := by
  intro x
  have hm_sub : m - n = (m - q) + (q - n) := by
    omega
  have hx_eq :
      x =
        -(t - α) * ((m - q : ℕ) : ℝ) -
          t * ((q - n : ℕ) : ℝ) := by
    dsimp [x]
    rw [hm_sub]
    norm_num [Nat.cast_add]
    ring
  have htα_pos : 0 < t - α := sub_pos.mpr hαt
  have hleft_nonneg :
      0 ≤ (t - α) * ((m - q : ℕ) : ℝ) := by
    positivity
  have hright_nonneg :
      0 ≤ t * ((q - n : ℕ) : ℝ) := by
    positivity
  have hx_nonpos : x ≤ 0 := by
    have hleft_nonpos :
        -(t - α) * ((m - q : ℕ) : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr htα_pos.le) (by positivity)
    calc
      x = -(t - α) * ((m - q : ℕ) : ℝ) -
            t * ((q - n : ℕ) : ℝ) := hx_eq
      _ ≤ 0 - t * ((q - n : ℕ) : ℝ) :=
          sub_le_sub_right hleft_nonpos _
      _ ≤ 0 := sub_nonpos.mpr hright_nonneg
  exact div_nonpos_of_nonpos_of_nonneg hx_nonpos ha.le

/-- In the complementary high-scale range with `q ≤ n`, the exponent correction
is at most `α n`. -/
theorem highComplement_x_le_alpha_mul_n_of_q_le_n
    {t α : ℝ} {q m n : ℕ}
    (hα_nonneg : 0 ≤ α) (hαt : α < t)
    (hqn : q ≤ n) (hnm : n ≤ m) :
    let x : ℝ :=
      α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    x ≤ α * (n : ℝ) := by
  intro x
  have hmq_sub : m - q = (m - n) + (n - q) := by
    omega
  have hx_eq :
      x =
        (α - t) * ((m - n : ℕ) : ℝ) +
          α * ((n - q : ℕ) : ℝ) := by
    dsimp [x]
    rw [hmq_sub]
    norm_num [Nat.cast_add]
    ring
  have hcoeff_nonpos : α - t ≤ 0 := by
    linarith
  have hmn_nonneg : 0 ≤ ((m - n : ℕ) : ℝ) := by
    positivity
  have hfirst_nonpos :
      (α - t) * ((m - n : ℕ) : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcoeff_nonpos hmn_nonneg
  have hnq_le_n : ((n - q : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n q
  have htail_le : α * ((n - q : ℕ) : ℝ) ≤ α * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnq_le_n hα_nonneg
  rw [hx_eq]
  linarith

/-- If the selected high scale is not below `n` and `n ≤ q`, then `n` is
bounded by the logarithmic offset. -/
theorem n_le_logOffset_add_one_of_not_high_n_le_q
    {a t α L : ℝ} {q m n ℓ : ℕ}
    (ha : 0 < a) (ht : 0 < t) (hαt : α < t)
    (hceil :
      let x : ℝ :=
        α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
      (ℓ : ℝ) ≤ L + max (x / a) 0 + 1)
    (hnℓ : n ≤ ℓ) (hnq : n ≤ q) (hqm : q ≤ m) :
    (n : ℝ) ≤ L + 1 := by
  let x : ℝ :=
    α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  exact
    n_le_logOffset_add_one_of_not_high_x_nonpos
      (a := a) (L := L) (x := x) (n := n) (ℓ := ℓ)
      (by simpa [x] using hceil)
      (by
        simpa [x] using
          highComplement_x_div_nonpos_of_n_le_q
            (a := a) (t := t) (α := α) (q := q) (m := m) (n := n)
            ha ht hαt hnq hqm)
      hnℓ

/-- If the selected high scale is not below `n` and `q ≤ n`, then `n` is
bounded by the logarithmic offset with the buffer `1 - α/a`. -/
theorem scale_bound_of_not_high_q_le_n
    {a t α L : ℝ} {q m n ℓ : ℕ}
    (ha : 0 < a) (hα_nonneg : 0 ≤ α) (hαt : α < t) (hαa : α < a)
    (hceil :
      let x : ℝ :=
        α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
      (ℓ : ℝ) ≤ L + max (x / a) 0 + 1)
    (hnℓ : n ≤ ℓ) (hqn : q ≤ n) (hnm : n ≤ m) :
    (1 - α / a) * (n : ℝ) ≤ L + 1 := by
  let x : ℝ :=
    α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
  exact
    scale_bound_of_not_high_x_le_alpha_mul_n
      (a := a) (α := α) (L := L) (x := x) (n := n) (ℓ := ℓ)
      ha hα_nonneg hαa
      (by simpa [x] using hceil)
      (by
        simpa [x] using
          highComplement_x_le_alpha_mul_n_of_q_le_n
            (t := t) (α := α) (q := q) (m := m) (n := n)
            hα_nonneg hαt hqn hnm)
      hnℓ

/-- Bottom-range exponent competition for the crude estimate.  Here
`r = m - q` and `j = q - n`, so the discount gives decay in both directions. -/
theorem crudeBottomExponent_lower_bound
    {t α : ℝ} {q m n : ℕ}
    (hnq : n ≤ q) (hqm : q ≤ m) :
    let x : ℝ :=
      α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    let c : ℝ := min (t - α) t
    (-x) ≥ c * (((m - q : ℕ) : ℝ) + ((q - n : ℕ) : ℝ)) := by
  intro x c
  have hc_le_left : c ≤ t - α := by
    dsimp [c]
    exact min_le_left _ _
  have hc_le_right : c ≤ t := by
    dsimp [c]
    exact min_le_right _ _
  have hr_nonneg : 0 ≤ ((m - q : ℕ) : ℝ) := by positivity
  have hj_nonneg : 0 ≤ ((q - n : ℕ) : ℝ) := by positivity
  have hm_sub :
      m - n = (m - q) + (q - n) := by
    omega
  have hx_eq :
      -x =
        (t - α) * ((m - q : ℕ) : ℝ) +
          t * ((q - n : ℕ) : ℝ) := by
    dsimp [x]
    rw [hm_sub]
    norm_num [Nat.cast_add]
    ring
  rw [hx_eq]
  have hleft :
      c * ((m - q : ℕ) : ℝ) ≤
        (t - α) * ((m - q : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hc_le_left hr_nonneg
  have hright :
      c * ((q - n : ℕ) : ℝ) ≤
        t * ((q - n : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hc_le_right hj_nonneg
  calc
    c * (((m - q : ℕ) : ℝ) + ((q - n : ℕ) : ℝ))
        = c * ((m - q : ℕ) : ℝ) + c * ((q - n : ℕ) : ℝ) := by ring
    _ ≤ (t - α) * ((m - q : ℕ) : ℝ) +
          t * ((q - n : ℕ) : ℝ) :=
        add_le_add hleft hright

/-- Crude exponent competition in the range `q ≤ n`.  The price is an
`α n` offset, which is harmless once the complementary high-scale argument has
bounded `n`. -/
theorem crudeTopExponent_lower_bound_of_q_le_n
    {t α c : ℝ} {q m n : ℕ}
    (hα_nonneg : 0 ≤ α) (hc_le : c ≤ t - α)
    (hqn : q ≤ n) (hnm : n ≤ m) :
    let x : ℝ :=
      α * ((m - q : ℕ) : ℝ) - t * ((m - n : ℕ) : ℝ)
    (-x) ≥ c * ((m - n : ℕ) : ℝ) - α * (n : ℝ) := by
  intro x
  have hmq_sub : m - q = (m - n) + (n - q) := by
    omega
  have hx_neg_eq :
      -x =
        (t - α) * ((m - n : ℕ) : ℝ) -
          α * ((n - q : ℕ) : ℝ) := by
    dsimp [x]
    rw [hmq_sub]
    norm_num [Nat.cast_add]
    ring
  have hmn_nonneg : 0 ≤ ((m - n : ℕ) : ℝ) := by
    positivity
  have hc_part :
      c * ((m - n : ℕ) : ℝ) ≤
        (t - α) * ((m - n : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hc_le hmn_nonneg
  have hnq_le_n : ((n - q : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n q
  have htail_le : α * ((n - q : ℕ) : ℝ) ≤ α * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnq_le_n hα_nonneg
  rw [hx_neg_eq]
  linarith

end

end Section57
end Ch05
end Book
end Homogenization
