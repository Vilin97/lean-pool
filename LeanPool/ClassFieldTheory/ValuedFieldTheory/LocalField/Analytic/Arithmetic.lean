/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic
/-!
# Arithmetic lemmas for local-field index calculations

This file contains the pure natural-number cancellation steps used after local-field
norm and value-group arguments have produced an lcm divisibility.

It also contains the elementary `p`-adic valuation estimates used in the local-field structure
  development,
the logarithm and exponential estimates for the convergence and valuation behavior of the
logarithm and exponential series.
-/

@[expose] public section

namespace LocalFieldTheory.DiscreteValuationField

open Filter

section PadicLogArithmetic

variable {p n : ℕ}

/-- Arithmetic estimate for the field-unit logarithm:
`p^(v_p n) <= n` for nonzero `n`.

This is the arithmetic input for the logarithm-series convergence estimate
`v_p(n) <= log_p n`. -/
theorem pow_padicValNat_le_self
    (hn : n ≠ 0) :
    p ^ padicValNat p n ≤ n :=
  Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hn) pow_padicValNat_dvd

/-- Arithmetic estimate for the field-unit logarithm in real logarithmic
form: `v_p(n) <= log_p(n)`. -/
theorem padicValNat_le_real_logb
    (n : ℕ) :
    (padicValNat p n : ℝ) ≤ Real.logb p n := by
  exact
    (Nat.cast_le.mpr (padicValNat_le_nat_log (p := p) n)).trans
      (Real.natLog_le_logb n p)

/-- Asymptotic estimate for the field-unit logarithm:
for every positive slope `c`, the linear term `n * c` eventually dominates
the logarithmic denominator contribution `log_p(n)`. -/
theorem tendsto_nat_mul_const_sub_logb_atTop
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * c - Real.logb p n) atTop atTop := by
  have hhalf : 0 < c / 2 := by positivity
  have hsmall :
      (fun n : ℕ => Real.logb (p : ℝ) (n : ℝ)) =o[atTop]
        (fun n : ℕ => (n : ℝ)) := by
    simpa [Function.comp_def] using
      (Real.isLittleO_logb_id_atTop (b := (p : ℝ))).comp_tendsto
        tendsto_natCast_atTop_atTop
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖Real.logb (p : ℝ) (n : ℝ)‖ ≤
          (c / 2) * ‖(n : ℝ)‖ :=
    hsmall.def hhalf
  have hle :
      (fun n : ℕ => (c / 2) * (n : ℝ)) ≤ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) * c - Real.logb (p : ℝ) (n : ℝ)) := by
    filter_upwards [hbound] with n hn
    have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog_le :
        Real.logb (p : ℝ) (n : ℝ) ≤ (c / 2) * (n : ℝ) := by
      calc
        Real.logb (p : ℝ) (n : ℝ) ≤
            ‖Real.logb (p : ℝ) (n : ℝ)‖ :=
          le_abs_self _
        _ ≤ (c / 2) * ‖(n : ℝ)‖ := hn
        _ = (c / 2) * (n : ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnnonneg]
    calc
      (c / 2) * (n : ℝ) =
          (n : ℝ) * c - (c / 2) * (n : ℝ) := by
        ring
      _ ≤ (n : ℝ) * c - Real.logb (p : ℝ) (n : ℝ) :=
        sub_le_sub_left hlog_le ((n : ℝ) * c)
  have hlin :
      Tendsto (fun n : ℕ => (c / 2) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hhalf tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono' atTop hle hlin

/-- The same logarithmic domination estimate with the natural series indexing
`n + 1`, avoiding the zero denominator in the logarithm series. -/
theorem tendsto_nat_succ_mul_const_sub_logb_atTop
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * c - Real.logb p (n + 1))
      atTop atTop := by
  simpa [Function.comp_def] using
    (tendsto_nat_mul_const_sub_logb_atTop (p := p) hc).comp
      (tendsto_add_atTop_nat 1)

/-- Variant of the logarithmic domination estimate with a fixed real multiple
of the logarithmic term.  This is the form needed after inserting the
ramification index into the valuation of integer denominators. -/
theorem tendsto_nat_succ_mul_const_sub_const_mul_logb_atTop
    {c C : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) * c -
          C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ))
      atTop atTop := by
  have hhalf : 0 < c / 2 := by positivity
  have htend :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsmall :
      (fun n : ℕ => C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) =o[atTop]
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
    have hlog :
        (fun n : ℕ => Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) =o[atTop]
          (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
      simpa [Function.comp_def] using
        (Real.isLittleO_logb_id_atTop (b := (p : ℝ))).comp_tendsto
          htend
    simpa using hlog.const_mul_left C
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)‖ ≤
          (c / 2) * ‖((n + 1 : ℕ) : ℝ)‖ :=
    hsmall.def hhalf
  have hle :
      (fun n : ℕ => (c / 2) * ((n + 1 : ℕ) : ℝ)) ≤ᶠ[atTop]
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) * c -
            C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [hbound] with n hn
    have hnnonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hlog_le :
        C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) ≤
          (c / 2) * ((n + 1 : ℕ) : ℝ) := by
      calc
        C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) ≤
            ‖C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)‖ :=
          le_abs_self _
        _ ≤ (c / 2) * ‖((n + 1 : ℕ) : ℝ)‖ := hn
        _ = (c / 2) * ((n + 1 : ℕ) : ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnnonneg]
    calc
      (c / 2) * ((n + 1 : ℕ) : ℝ) =
          ((n + 1 : ℕ) : ℝ) * c -
            (c / 2) * ((n + 1 : ℕ) : ℝ) := by
        ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * c -
          C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) :=
        sub_le_sub_left hlog_le (((n + 1 : ℕ) : ℝ) * c)
  have hlin :
      Tendsto (fun n : ℕ => (c / 2) * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hhalf htend
  exact tendsto_atTop_mono' atTop hle hlin

/-- Exponential-series estimate for the field-unit logarithm:
for every slope `c > 1`, the linear term `n * c` dominates the factorial
denominator contribution `v_p(n!)`.  The proof uses mathlib's Legendre-bound
`padicValNat_factorial_le`; no factorial valuation formula is reproved here. -/
theorem tendsto_nat_mul_const_sub_padicValNat_factorial_atTop
    [Fact p.Prime] {c : ℝ} (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => (n : ℝ) * c - (padicValNat p n.factorial : ℝ))
      atTop atTop := by
  have hpos : 0 < c - 1 := sub_pos.mpr hc
  have hsource :
      Tendsto (fun n : ℕ => (n : ℝ) * (c - 1)) atTop atTop := by
    simpa [mul_comm] using
      Tendsto.const_mul_atTop hpos tendsto_natCast_atTop_atTop
  have hle :
      (fun n : ℕ => (n : ℝ) * (c - 1)) ≤ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) * c - (padicValNat p n.factorial : ℝ)) := by
    exact Eventually.of_forall fun n => by
      have hdenNat : padicValNat p n.factorial ≤ n :=
        padicValNat_factorial_le (p := p) n
      have hden : (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) :=
        Nat.cast_le.mpr hdenNat
      nlinarith
  exact tendsto_atTop_mono' atTop hle hsource

/-- Legendre's factorial-valuation formula, Legendre's formula in digit form:
if `n = a_0 + a_1 p + ... + a_r p^r`, then multiplying the displayed digit formula by `p - 1` gives
`(p - 1) v_p(n!) = (a_0 p^0 + ... + a_r p^r) - (a_0 + ... + a_r)`. -/
theorem padicValNat_factorial_digits
    [Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p n.factorial =
      Nat.ofDigits p (p.digits n) - (p.digits n).sum := by
  simpa [Nat.ofDigits_digits] using
    (sub_one_mul_padicValNat_factorial (p := p) n)

/-- Legendre's factorial-valuation formula with the digit expansion written out as an
indexed sum. -/
theorem padicValNat_factorial_digits_sum
    [Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p n.factorial =
      ((p.digits n).mapIdx fun i a => a * p ^ i).sum -
        (p.digits n).sum := by
  simpa [Nat.ofDigits_eq_sum_mapIdx] using
    padicValNat_factorial_digits (p := p) n

/-- A nonzero natural number has positive sum of base-`p` digits. -/
theorem digits_sum_pos_of_ne_zero (hn : n ≠ 0) :
    0 < (p.digits n).sum := by
  by_contra hnot
  have hsum0 : (p.digits n).sum = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hnot)
  have hall : ∀ a ∈ p.digits n, a = 0 :=
    List.sum_eq_zero_iff.mp hsum0
  have hmapZero :
      (List.mapIdx (fun i a => a * p ^ i) (p.digits n)).sum = 0 := by
    apply List.sum_eq_zero
    intro b hb
    rw [List.mem_mapIdx] at hb
    rcases hb with ⟨i, hi, rfl⟩
    have hdigit : (p.digits n)[i] = 0 :=
      hall _ (List.getElem_mem hi)
    simp [hdigit]
  have hof : Nat.ofDigits p (p.digits n) = 0 := by
    simpa [Nat.ofDigits_eq_sum_mapIdx] using hmapZero
  have hn0 : n = 0 := by
    simpa [Nat.ofDigits_digits] using hof
  exact hn hn0

/-- Legendre's formula gives the sharp bound
`(p - 1) * v_p(n!) <= n - 1` for nonzero `n`. -/
theorem sub_one_mul_padicValNat_factorial_le_sub_one
    [Fact p.Prime] (hn : n ≠ 0) :
    (p - 1) * padicValNat p n.factorial ≤ n - 1 := by
  rw [padicValNat_factorial_digits, Nat.ofDigits_digits]
  have hsumpos : 1 ≤ (p.digits n).sum :=
    Nat.succ_le_of_lt (digits_sum_pos_of_ne_zero (p := p) hn)
  omega

/-- Factorial-denominator analogue of the factorial quotient estimate:
`v_p(n!) / (n-1) <= 1/(p-1)`. -/
theorem padicValNat_factorial_div_sub_one_le_inv_sub_one
    [Fact p.Prime] (hn : 1 < n) :
    (padicValNat p n.factorial : ℚ) / ((n : ℚ) - 1) ≤
      1 / ((p : ℚ) - 1) := by
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℚ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℚ) - 1 := by
    linarith
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast hn
    linarith
  have hNat :
      (p - 1) * padicValNat p n.factorial ≤ n - 1 :=
    sub_one_mul_padicValNat_factorial_le_sub_one
      (p := p) (n := n) (by omega)
  have hmul :
      ((p : ℚ) - 1) * (padicValNat p n.factorial : ℚ) ≤
        (n : ℚ) - 1 := by
    have hcast :
        (((p - 1) * padicValNat p n.factorial : ℕ) : ℚ) ≤
          ((n - 1 : ℕ) : ℚ) := by
      exact_mod_cast hNat
    have hpone : 1 ≤ p := hpNat.one_lt.le
    have hnone : 1 ≤ n := by omega
    simpa [Nat.cast_mul, Nat.cast_sub hpone, Nat.cast_sub hnone] using hcast
  field_simp [hnden.ne', hpden.ne']
  nlinarith

/-- Real factorial-denominator bound used for the sharp convergence radius of
the exponential series. -/
theorem padicValNat_factorial_le_sub_one_div_sub_one_real
    [Fact p.Prime] (hn : n ≠ 0) :
    (padicValNat p n.factorial : ℝ) ≤
      ((n : ℝ) - 1) / ((p : ℝ) - 1) := by
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℝ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℝ) - 1 := by
    linarith
  have hNat :
      (p - 1) * padicValNat p n.factorial ≤ n - 1 :=
    sub_one_mul_padicValNat_factorial_le_sub_one
      (p := p) (n := n) hn
  have hmul :
      ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) ≤
        (n : ℝ) - 1 := by
    have hcast :
        (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) ≤
          ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hNat
    have hpone : 1 ≤ p := hpNat.one_lt.le
    have hnone : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    simpa [Nat.cast_mul, Nat.cast_sub hpone, Nat.cast_sub hnone] using hcast
  exact (le_div_iff₀ hpden).2 (by simpa [mul_comm] using hmul)

/-- Sharp asymptotic estimate for the exponential series denominator:
any real slope strictly above `C/(p-1)` dominates
`C * v_p(n!)`. -/
theorem tendsto_nat_mul_const_sub_const_mul_padicValNat_factorial_atTop
    [Fact p.Prime] {c C : ℝ} (hC : 0 ≤ C)
    (hc : C / ((p : ℝ) - 1) < c) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) * c - C * (padicValNat p n.factorial : ℝ))
      atTop atTop := by
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℝ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℝ) - 1 := by
    linarith
  have hdelta : 0 < c - C / ((p : ℝ) - 1) := sub_pos.mpr hc
  have hsource :
      Tendsto
        (fun n : ℕ => (n : ℝ) * (c - C / ((p : ℝ) - 1)))
        atTop atTop := by
    simpa [mul_comm] using
      Tendsto.const_mul_atTop hdelta tendsto_natCast_atTop_atTop
  have hle :
      (fun n : ℕ => (n : ℝ) * (c - C / ((p : ℝ) - 1))) ≤ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) * c - C * (padicValNat p n.factorial : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    have hfac :=
      padicValNat_factorial_le_sub_one_div_sub_one_real
        (p := p) (n := n) hn0
    have hCfac :
        C * (padicValNat p n.factorial : ℝ) ≤
          C * (((n : ℝ) - 1) / ((p : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hfac hC
    have hCp_nonneg : 0 ≤ C / ((p : ℝ) - 1) :=
      div_nonneg hC hpden.le
    have hden_bound :
        C * (((n : ℝ) - 1) / ((p : ℝ) - 1)) ≤
          (n : ℝ) * (C / ((p : ℝ) - 1)) := by
      calc
        C * (((n : ℝ) - 1) / ((p : ℝ) - 1)) =
            ((n : ℝ) - 1) * (C / ((p : ℝ) - 1)) := by
          ring
        _ ≤ (n : ℝ) * (C / ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hCp_nonneg
    calc
      (n : ℝ) * (c - C / ((p : ℝ) - 1)) =
          (n : ℝ) * c - (n : ℝ) * (C / ((p : ℝ) - 1)) := by
        ring
      _ ≤ (n : ℝ) * c - C * (padicValNat p n.factorial : ℝ) := by
        linarith [hCfac.trans hden_bound]
  exact tendsto_atTop_mono' atTop hle hsource

/-- Higher exponential terms have strictly larger integer valuation than the
linear term when the input has integer valuation at least two.  This is the
termwise arithmetic input for `exp(x) - 1` having the same valuation as `x`
on the normalized convergence ball. -/
theorem exp_higher_term_integer_valuation_gt
    [Fact p.Prime] {n : ℕ} (hn : 2 ≤ n) {m : ℤ} (hm : 2 ≤ m) :
    m < (n : ℤ) * m - (padicValNat p n.factorial : ℤ) := by
  have hn0 : n ≠ 0 := by omega
  have hdenNat :
      padicValNat p n.factorial + 1 ≤ n :=
    Nat.succ_le_of_lt
      (padicValNat_factorial_lt_of_ne_zero (p := p) hn0)
  have hden : (padicValNat p n.factorial : ℤ) ≤ (n : ℤ) - 1 := by
    omega
  have hnsub : (1 : ℤ) ≤ (n : ℤ) - 1 := by
    omega
  have hmsub : (1 : ℤ) ≤ m - 1 := by
    omega
  have hpos : (0 : ℤ) < ((n : ℤ) - 1) * (m - 1) := by
    nlinarith
  nlinarith

/-- Ramified sharp-threshold version of
`exp_higher_term_integer_valuation_gt`: if the factorial denominator
contributes `e * v_p(n!)`, then every higher exponential term has larger
integer valuation than the linear term above `e/(p-1)`. -/
theorem exp_higher_term_integer_valuation_gt_scaled
    [Fact p.Prime] {n e : ℕ} (hn : 2 ≤ n) {m : ℤ}
    (hm : (e : ℚ) / ((p : ℚ) - 1) < (m : ℚ)) :
    m < (n : ℤ) * m - (e : ℤ) * (padicValNat p n.factorial : ℤ) := by
  have hquot :=
    padicValNat_factorial_div_sub_one_le_inv_sub_one
      (p := p) (n := n) (by omega)
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast (by omega : 1 < n)
    linarith
  have he_nonneg : 0 ≤ (e : ℚ) := by
    positivity
  have hscaled_div :
      ((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
          ((n : ℚ) - 1) ≤
        (e : ℚ) / ((p : ℚ) - 1) := by
    calc
      ((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
          ((n : ℚ) - 1) =
          (e : ℚ) *
            ((padicValNat p n.factorial : ℚ) / ((n : ℚ) - 1)) := by
        ring
      _ ≤ (e : ℚ) * (1 / ((p : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_left hquot he_nonneg
      _ = (e : ℚ) / ((p : ℚ) - 1) := by
        ring
  have hstrict :
      ((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
          ((n : ℚ) - 1) < (m : ℚ) :=
    lt_of_le_of_lt hscaled_div hm
  have hdenlt :
      (e : ℚ) * (padicValNat p n.factorial : ℚ) <
        ((n : ℚ) - 1) * (m : ℚ) := by
    calc
      (e : ℚ) * (padicValNat p n.factorial : ℚ) =
          (((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
              ((n : ℚ) - 1)) *
            ((n : ℚ) - 1) := by
        field_simp [hnden.ne']
      _ < (m : ℚ) * ((n : ℚ) - 1) :=
        mul_lt_mul_of_pos_right hstrict hnden
      _ = ((n : ℚ) - 1) * (m : ℚ) := by
        ring
  have hgoal :
      (m : ℚ) <
        (n : ℚ) * (m : ℚ) -
          (e : ℚ) * (padicValNat p n.factorial : ℚ) := by
    nlinarith
  have hgoal' :
      (m : ℚ) <
        (((n : ℤ) * m -
          (e : ℤ) * (padicValNat p n.factorial : ℤ) : ℤ) : ℚ) := by
    simpa [Int.cast_mul, Int.cast_sub, Int.cast_natCast] using hgoal
  exact_mod_cast hgoal'

/-- Arithmetic estimate at the deep exponential–logarithm threshold:
for `n > 1`, the quotient `v_p(n)/(n-1)` is at most `1/(p-1)`.

This is the exact numerical inequality used later to show that, above the
threshold `1/(p-1)`, the linear term of the logarithm or exponential series
has strictly smaller valuation than every higher term. -/
theorem padicValNat_div_sub_one_le_inv_sub_one
    [Fact p.Prime] (hn : 1 < n) :
    (padicValNat p n : ℚ) / ((n : ℚ) - 1) ≤
      1 / ((p : ℚ) - 1) := by
  let a := padicValNat p n
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℚ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℚ) - 1 := by
    linarith
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast hn
    linarith
  have hpowNat : p ^ a ≤ n :=
    Nat.le_of_dvd (lt_trans Nat.zero_lt_one hn) pow_padicValNat_dvd
  have hpow : (p : ℚ) ^ a ≤ (n : ℚ) := by
    exact_mod_cast hpowNat
  have hbern :
      (a : ℚ) ≤ (((p : ℚ) ^ a - 1) / ((p : ℚ) - 1)) :=
    Nat.cast_le_pow_sub_div_sub (α := ℚ) (a := (p : ℚ)) hp a
  have hsub :
      ((p : ℚ) ^ a - 1) / ((p : ℚ) - 1) ≤
        ((n : ℚ) - 1) / ((p : ℚ) - 1) :=
    div_le_div_of_nonneg_right (sub_le_sub_right hpow 1) hpden.le
  have hbound :
      (a : ℚ) ≤ ((n : ℚ) - 1) / ((p : ℚ) - 1) :=
    hbern.trans hsub
  calc
    (padicValNat p n : ℚ) / ((n : ℚ) - 1) =
        (a : ℚ) / ((n : ℚ) - 1) := rfl
    _ ≤ (((n : ℚ) - 1) / ((p : ℚ) - 1)) /
        ((n : ℚ) - 1) :=
      div_le_div_of_nonneg_right hbound hnden.le
    _ = 1 / ((p : ℚ) - 1) := by
      field_simp [hnden.ne', hpden.ne']

/-- Strict form of the preceding estimate: any slope strictly bigger than
`1/(p-1)` eventually dominates `v_p(n)` already termwise for every `n > 1`. -/
theorem padicValNat_lt_sub_one_mul_of_inv_sub_one_lt
    [Fact p.Prime] (hn : 1 < n) {c : ℚ}
    (hc : 1 / ((p : ℚ) - 1) < c) :
    (padicValNat p n : ℚ) < ((n : ℚ) - 1) * c := by
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast hn
    linarith
  have hquot :=
    padicValNat_div_sub_one_le_inv_sub_one (p := p) (n := n) hn
  have hstrict :
      (padicValNat p n : ℚ) / ((n : ℚ) - 1) < c :=
    lt_of_le_of_lt hquot hc
  calc
    (padicValNat p n : ℚ) =
        ((padicValNat p n : ℚ) / ((n : ℚ) - 1)) *
          ((n : ℚ) - 1) := by
      field_simp [hnden.ne']
    _ < c * ((n : ℚ) - 1) :=
      mul_lt_mul_of_pos_right hstrict hnden
    _ = ((n : ℚ) - 1) * c := by
      ring

/-- Positivity form used in the valuation computation
`v_p(x^n / n) = n v_p(x) - v_p(n)`. -/
theorem sub_padicValNat_pos_of_inv_sub_one_lt
    [Fact p.Prime] (hn : 1 < n) {c : ℚ}
    (hc : 1 / ((p : ℚ) - 1) < c) :
    0 < (n : ℚ) * c - (padicValNat p n : ℚ) := by
  have hpNat : Nat.Prime p := Fact.out
  have hpden : 0 < (p : ℚ) - 1 := by
    have hp : (1 : ℚ) < p := by
      exact_mod_cast hpNat.one_lt
    linarith
  have hcpos : 0 < c :=
    (one_div_pos.mpr hpden).trans hc
  have hlt :=
    padicValNat_lt_sub_one_mul_of_inv_sub_one_lt
      (p := p) (n := n) hn hc
  have hstep : ((n : ℚ) - 1) * c < (n : ℚ) * c := by
    nlinarith
  exact sub_pos.mpr (hlt.trans hstep)

/-- Higher logarithm terms have strictly larger integer valuation than the
linear term above the usual `1/(p-1)` threshold. -/
theorem log_higher_term_integer_valuation_gt
    [Fact p.Prime] {n : ℕ} (hn : 2 ≤ n) {m : ℤ}
    (hm : 1 / ((p : ℚ) - 1) < (m : ℚ)) :
    m < (n : ℤ) * m - (padicValNat p n : ℤ) := by
  have hlt :=
    padicValNat_lt_sub_one_mul_of_inv_sub_one_lt
      (p := p) (n := n) (by omega) (c := (m : ℚ)) hm
  have hgoal :
      (m : ℚ) < (n : ℚ) * (m : ℚ) - (padicValNat p n : ℚ) := by
    nlinarith
  have hgoal' :
      (m : ℚ) <
        (((n : ℤ) * m - (padicValNat p n : ℤ) : ℤ) : ℚ) := by
    simpa [Int.cast_mul, Int.cast_sub, Int.cast_natCast] using hgoal
  exact_mod_cast hgoal'

/-- Ramified-denominator version of
`log_higher_term_integer_valuation_gt`: if the denominator contributes
`e * v_p(n)`, then the sharp comparison threshold is `e/(p-1)`. -/
theorem log_higher_term_integer_valuation_gt_scaled
    [Fact p.Prime] {n e : ℕ} (hn : 2 ≤ n) {m : ℤ}
    (hm : (e : ℚ) / ((p : ℚ) - 1) < (m : ℚ)) :
    m < (n : ℤ) * m - (e : ℤ) * (padicValNat p n : ℤ) := by
  have hquot :=
    padicValNat_div_sub_one_le_inv_sub_one
      (p := p) (n := n) (by omega)
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast (by omega : 1 < n)
    linarith
  have he_nonneg : 0 ≤ (e : ℚ) := by
    positivity
  have hscaled_div :
      ((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1) ≤
        (e : ℚ) / ((p : ℚ) - 1) := by
    calc
      ((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1) =
          (e : ℚ) * ((padicValNat p n : ℚ) / ((n : ℚ) - 1)) := by
        ring
      _ ≤ (e : ℚ) * (1 / ((p : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_left hquot he_nonneg
      _ = (e : ℚ) / ((p : ℚ) - 1) := by
        ring
  have hstrict :
      ((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1) < (m : ℚ) :=
    lt_of_le_of_lt hscaled_div hm
  have hdenlt :
      (e : ℚ) * (padicValNat p n : ℚ) <
        ((n : ℚ) - 1) * (m : ℚ) := by
    calc
      (e : ℚ) * (padicValNat p n : ℚ) =
          (((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1)) *
            ((n : ℚ) - 1) := by
        field_simp [hnden.ne']
      _ < (m : ℚ) * ((n : ℚ) - 1) :=
        mul_lt_mul_of_pos_right hstrict hnden
      _ = ((n : ℚ) - 1) * (m : ℚ) := by
        ring
  have hgoal :
      (m : ℚ) <
        (n : ℚ) * (m : ℚ) -
          (e : ℚ) * (padicValNat p n : ℚ) := by
    nlinarith
  have hgoal' :
      (m : ℚ) <
        (((n : ℤ) * m -
          (e : ℤ) * (padicValNat p n : ℤ) : ℤ) : ℚ) := by
    simpa [Int.cast_mul, Int.cast_sub, Int.cast_natCast] using hgoal
  exact_mod_cast hgoal'

end PadicLogArithmetic

/-- If `e` divides the base-change index, the primitive quotient
`e / gcd e e'` is one. -/
theorem nat_div_gcd_eq_one_of_dvd {e e' : ℕ}
    (he : 0 < e) (hdiv : e ∣ e') :
    e / Nat.gcd e e' = 1 := by
  rw [Nat.gcd_eq_left hdiv, Nat.div_self he]

/-- Dividing the lcm by the right input removes exactly the common gcd from
the left input. -/
theorem nat_lcm_div_right_eq_div_gcd {a b : ℕ} (hb : 0 < b) :
    Nat.lcm a b / b = a / Nat.gcd a b := by
  calc
    Nat.lcm a b / b = (a * b / Nat.gcd a b) / b := by
      rfl
    _ = (a * (b / Nat.gcd a b)) / b := by
      rw [Nat.mul_div_assoc a (Nat.gcd_dvd_right a b)]
    _ = ((b / Nat.gcd a b) * a) /
          ((b / Nat.gcd a b) * Nat.gcd a b) := by
      rw [Nat.mul_comm a (b / Nat.gcd a b),
        Nat.div_mul_cancel (Nat.gcd_dvd_right a b)]
    _ = a / Nat.gcd a b := by
      rw [Nat.mul_div_mul_left]
      exact Nat.div_pos
        (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b))
        (Nat.gcd_pos_of_pos_right a hb)

/-- Dividing the lcm by the left input removes exactly the common gcd from
the right input. -/
theorem nat_lcm_div_left_eq_div_gcd {a b : ℕ} (ha : 0 < a) :
    Nat.lcm a b / a = b / Nat.gcd a b := by
  simpa [Nat.lcm_comm, Nat.gcd_comm] using
    (nat_lcm_div_right_eq_div_gcd (a := b) (b := a) ha)

/-- If the lcm of two value steps divides `a * c`, the primitive part of
the second step after removing the common gcd with `a` divides `c`. -/
theorem nat_div_gcd_dvd_of_lcm_dvd_mul_left {a b c : ℕ}
    (ha : 0 < a) (hdiv : Nat.lcm a b ∣ a * c) :
    b / Nat.gcd a b ∣ c := by
  have hquot : Nat.lcm a b / a ∣ c := by
    rcases hdiv with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left ha
    have hlcm : a * (Nat.lcm a b / a) = Nat.lcm a b := by
      rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_lcm_left a b)]
    calc
      a * c = Nat.lcm a b * q := hq
      _ = (a * (Nat.lcm a b / a)) * q := by
        rw [hlcm]
      _ = a * ((Nat.lcm a b / a) * q) := by
        rw [mul_assoc]
  simpa [nat_lcm_div_left_eq_div_gcd (a := a) (b := b) ha] using hquot

/-- Symmetric cancellation form: if the lcm divides `c * b`, then the
primitive part of `a` after removing the common gcd with `b` divides `c`. -/
theorem nat_div_gcd_dvd_of_lcm_dvd_mul_right {a b c : ℕ}
    (hb : 0 < b) (hdiv : Nat.lcm a b ∣ c * b) :
    a / Nat.gcd b a ∣ c := by
  have hdiv' : Nat.lcm b a ∣ b * c := by
    simpa [Nat.lcm_comm, mul_comm] using hdiv
  exact nat_div_gcd_dvd_of_lcm_dvd_mul_left
    (a := b) (b := a) (c := c) hb hdiv'

/-- If multiplying by the right branch gives the lcm exactly, the remaining
factor is the primitive left branch after removing the common gcd. -/
theorem nat_eq_div_gcd_of_right_mul_eq_lcm {a b c : ℕ}
    (hb : 0 < b) (h : b * c = Nat.lcm a b) :
    c = a / Nat.gcd a b := by
  calc
    c = Nat.lcm a b / b := by
      exact Nat.eq_div_of_mul_eq_right (ne_of_gt hb) h
    _ = a / Nat.gcd a b :=
      nat_lcm_div_right_eq_div_gcd (a := a) (b := b) hb

/-- Left-handed exact lcm cancellation. -/
theorem nat_eq_div_gcd_of_left_mul_eq_lcm {a b c : ℕ}
    (ha : 0 < a) (h : a * c = Nat.lcm a b) :
    c = b / Nat.gcd a b := by
  calc
    c = Nat.lcm a b / a := by
      exact Nat.eq_div_of_mul_eq_right (ne_of_gt ha) h
    _ = b / Nat.gcd a b :=
      nat_lcm_div_left_eq_div_gcd (a := a) (b := b) ha

/-- If a right-branch multiple divides the lcm, the remaining factor divides
the primitive left branch after removing the common gcd. -/
theorem nat_dvd_div_gcd_of_right_mul_dvd_lcm {a b c : ℕ}
    (hb : 0 < b) (h : b * c ∣ Nat.lcm a b) :
    c ∣ a / Nat.gcd a b := by
  rcases h with ⟨q, hq⟩
  have hmul : b * (c * q) = Nat.lcm a b := by
    simpa [mul_assoc] using hq.symm
  have hquot : c * q = Nat.lcm a b / b :=
    Nat.eq_div_of_mul_eq_right (ne_of_gt hb) hmul
  exact ⟨q, by
    rw [← nat_lcm_div_right_eq_div_gcd (a := a) (b := b) hb]
    exact hquot.symm⟩

/-- Left-handed divisibility form of lcm cancellation. -/
theorem nat_dvd_div_gcd_of_left_mul_dvd_lcm {a b c : ℕ}
    (ha : 0 < a) (h : a * c ∣ Nat.lcm a b) :
    c ∣ b / Nat.gcd a b := by
  rcases h with ⟨q, hq⟩
  have hmul : a * (c * q) = Nat.lcm a b := by
    simpa [mul_assoc] using hq.symm
  have hquot : c * q = Nat.lcm a b / a :=
    Nat.eq_div_of_mul_eq_right (ne_of_gt ha) hmul
  exact ⟨q, by
    rw [← nat_lcm_div_left_eq_div_gcd (a := a) (b := b) ha]
    exact hquot.symm⟩

/-- Arithmetic endpoint for the tame Abhyankar formula: once the actual
common-top calculation supplies `e' * e_top = lcm e e'`, the top ramification
index is the primitive quotient of `e`. -/
theorem nat_abhyankar_quotient_eq_of_right_mul_eq_lcm {e e' eTop : ℕ}
    (he' : 0 < e') (h : e' * eTop = Nat.lcm e e') :
    eTop = e / Nat.gcd e e' :=
  nat_eq_div_gcd_of_right_mul_eq_lcm (a := e) (b := e') (c := eTop) he' h

/-- Divisibility form used before the actual common-top equality is sharpened
to an equality. -/
theorem nat_abhyankar_quotient_dvd_of_right_mul_dvd_lcm {e e' eTop : ℕ}
    (he' : 0 < e') (h : e' * eTop ∣ Nat.lcm e e') :
    eTop ∣ e / Nat.gcd e e' :=
  nat_dvd_div_gcd_of_right_mul_dvd_lcm
    (a := e) (b := e') (c := eTop) he' h

/-- If the lower ramification index already divides the base-change index,
the tame Abhyankar quotient is one. -/
theorem nat_abhyankar_quotient_eq_one_of_dvd {e e' : ℕ}
    (he : 0 < e) (hdiv : e ∣ e') :
    e / Nat.gcd e e' = 1 :=
  nat_div_gcd_eq_one_of_dvd he hdiv

/-- Exact index-one corollary from the common-top lcm equality. -/
theorem nat_abhyankar_index_eq_one_of_right_mul_eq_lcm_of_dvd
    {e e' eTop : ℕ} (he : 0 < e) (he' : 0 < e')
    (hdiv : e ∣ e') (h : e' * eTop = Nat.lcm e e') :
    eTop = 1 := by
  rw [nat_abhyankar_quotient_eq_of_right_mul_eq_lcm he' h,
    nat_abhyankar_quotient_eq_one_of_dvd he hdiv]

end LocalFieldTheory.DiscreteValuationField
