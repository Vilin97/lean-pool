/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.WeakOrlicz

/-! # Psi Calculus -/

namespace Homogenization
namespace IndependentSums

/-!
The first abstract calculus for Chapter 4 weak-Orlicz tails.

This file begins the formalization of the growth-condition arguments from the
notes. The immediate goal is Step 1 of the `O_Ψ` calculus: polynomial factors
can be absorbed into a dilation of the argument of `Ψ`.
-/

/-- The Chapter 4 growth hypothesis `t Ψ(t) ≤ Ψ(K t)` for `t ≥ 1`. -/
def HasPsiGrowth (Ψ : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 1 ≤ t → t * Ψ t ≤ Ψ (K * t)

/-- The abstract doubling condition used in Step 5 of the Chapter 4
generalized triangle inequality argument. -/
def HasPsiAbstractDoubling (Ψ : ℝ → ℝ) (q C₀ : ℝ) : Prop :=
  ∀ ⦃t s : ℝ⦄, 1 ≤ t → 1 ≤ s → s ^ q ≤ C₀ * (Ψ (t * s) / Ψ t)

/-- The recursive triangular-number exponent that appears in the inductive
polynomial-absorption estimate. -/
def natTriangular : ℕ → ℕ
  | 0 => 0
  | n + 1 => natTriangular n + n

@[simp] theorem natTriangular_zero : natTriangular 0 = 0 :=
  rfl

@[simp] theorem natTriangular_succ (n : ℕ) :
    natTriangular (n + 1) = natTriangular n + n :=
  rfl

theorem one_le_pow_of_one_le_real {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    1 ≤ x ^ n := by
  simpa using (one_le_pow₀ hx : 1 ≤ x ^ n)

theorem hasPsiGrowth_nat_polyAbsorptionPre
    {Ψ : ℝ → ℝ} {K : ℝ} (hK : 1 ≤ K) (hΨ : HasPsiGrowth Ψ K) :
    ∀ n : ℕ, ∀ ⦃t : ℝ⦄, 1 ≤ t →
      t ^ n * Ψ t ≤ (K ^ natTriangular n)⁻¹ * Ψ ((K ^ n) * t)
  | 0, t, ht => by
      simp [natTriangular]
  | n + 1, t, ht => by
      have ht0 : 0 ≤ t := le_trans zero_le_one ht
      have hKn_one : 1 ≤ K ^ n := by
        exact one_le_pow_of_one_le_real hK n
      have hKn_pos : 0 < K ^ n := by
        have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
        exact pow_pos hK0 n
      have hKn_t_one : 1 ≤ (K ^ n) * t := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (K ^ n) * t :=
            mul_le_mul hKn_one ht (by norm_num : (0 : ℝ) ≤ 1)
              (le_trans zero_le_one hKn_one)
      have hstep := hΨ (t := (K ^ n) * t) hKn_t_one
      have hstep' : t * Ψ ((K ^ n) * t) ≤ (K ^ n)⁻¹ * Ψ ((K ^ (n + 1)) * t) := by
        have hscaled :
            (K ^ n)⁻¹ * (((K ^ n) * t) * Ψ ((K ^ n) * t))
              ≤ (K ^ n)⁻¹ * Ψ ((K ^ (n + 1)) * t) := by
          have :=
          mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr (le_of_lt hKn_pos))
          simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using this
        have hleft :
            (K ^ n)⁻¹ * (((K ^ n) * t) * Ψ ((K ^ n) * t)) = t * Ψ ((K ^ n) * t) := by
          field_simp [hKn_pos.ne']
        simpa [hleft] using hscaled
      calc
        t ^ (n + 1) * Ψ t = t * (t ^ n * Ψ t) := by
          ring_nf
        _ ≤ t * ((K ^ natTriangular n)⁻¹ * Ψ ((K ^ n) * t)) := by
          exact mul_le_mul_of_nonneg_left (hasPsiGrowth_nat_polyAbsorptionPre hK hΨ n ht) ht0
        _ = (K ^ natTriangular n)⁻¹ * (t * Ψ ((K ^ n) * t)) := by
          ring
        _ ≤ (K ^ natTriangular n)⁻¹ * ((K ^ n)⁻¹ * Ψ ((K ^ (n + 1)) * t)) := by
          exact mul_le_mul_of_nonneg_left hstep' (by positivity)
        _ = (K ^ natTriangular (n + 1))⁻¹ * Ψ ((K ^ (n + 1)) * t) := by
          rw [natTriangular_succ, pow_add]
          ring

/-- A weaker but convenient corollary of the pre-absorption estimate:
natural polynomial factors can be absorbed into the argument of `Ψ` without
tracking the sharpening prefactor from the notes. -/
theorem hasPsiGrowth_nat_polyAbsorption
    {Ψ : ℝ → ℝ} {K : ℝ} (hK : 1 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) :
    ∀ n : ℕ, ∀ ⦃t : ℝ⦄, 1 ≤ t →
      t ^ n * Ψ t ≤ Ψ ((K ^ n) * t) := by
  intro n t ht
  have hpre := hasPsiGrowth_nat_polyAbsorptionPre hK hΨ n ht
  have hfac : (K ^ natTriangular n)⁻¹ ≤ 1 := by
    have hpow : 1 ≤ K ^ natTriangular n := by
      exact one_le_pow_of_one_le_real hK (natTriangular n)
    exact inv_le_one_of_one_le₀ hpow
  have hPsi_nonneg : 0 ≤ Ψ ((K ^ n) * t) := by
    have hKn_nonneg : 0 ≤ K ^ n := by positivity
    exact le_trans zero_le_one (hAdmissible.2 (mul_nonneg hKn_nonneg (le_trans zero_le_one ht)))
  exact hpre.trans <| by
    calc
      (K ^ natTriangular n)⁻¹ * Ψ ((K ^ n) * t)
        ≤ 1 * Ψ ((K ^ n) * t) := by
            exact mul_le_mul_of_nonneg_right hfac hPsi_nonneg
    _ = Ψ ((K ^ n) * t) := by ring

theorem admissiblePsi_lowerBound_pow_natTriangular
    {Ψ : ℝ → ℝ} {K : ℝ} (hK : 1 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) :
    ∀ n : ℕ, K ^ natTriangular n ≤ Ψ (K ^ n)
  | n => by
      have hpre := hasPsiGrowth_nat_polyAbsorptionPre hK hΨ n (show 1 ≤ (1 : ℝ) by norm_num)
      have hΨone : 1 ≤ Ψ 1 := hAdmissible.2 zero_le_one
      have hKtri_pos : 0 < K ^ natTriangular n := by positivity
      have hmul := mul_le_mul_of_nonneg_left hpre (le_of_lt hKtri_pos)
      calc
        K ^ natTriangular n ≤ K ^ natTriangular n * Ψ 1 := by
          have hKtri_nonneg : 0 ≤ K ^ natTriangular n := le_of_lt hKtri_pos
          calc
            K ^ natTriangular n = K ^ natTriangular n * 1 := by ring
            _ ≤ K ^ natTriangular n * Ψ 1 :=
              mul_le_mul_of_nonneg_left hΨone hKtri_nonneg
        _ ≤ Ψ (K ^ n) := by
          simpa [hKtri_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Note-facing Step 1: polynomial powers with a real exponent can be absorbed
by replacing the exponent with its ceiling. -/
theorem hasPsiGrowth_rpow_absorption
    {Ψ : ℝ → ℝ} {K p t : ℝ} (hK : 1 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (ht : 1 ≤ t) :
    t ^ p * Ψ t ≤ Ψ ((K ^ Nat.ceil p) * t) := by
  let n : ℕ := Nat.ceil p
  have hpceil : p ≤ n := Nat.le_ceil p
  have htpow : t ^ p ≤ t ^ (n : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le ht hpceil
  have hPsi_nonneg : 0 ≤ Ψ t := by
    exact le_trans zero_le_one (hAdmissible.2 (le_trans zero_le_one ht))
  calc
    t ^ p * Ψ t ≤ t ^ (n : ℝ) * Ψ t := by
      exact mul_le_mul_of_nonneg_right htpow hPsi_nonneg
    _ = t ^ n * Ψ t := by rw [Real.rpow_natCast]
    _ ≤ Ψ ((K ^ n) * t) := by
      exact hasPsiGrowth_nat_polyAbsorption hK hΨ hAdmissible n ht

/-- Step 2 pre-estimate from the notes: once `t` dominates a power of `K`,
the discrete lower bound for `Ψ(K^m)` propagates to `Ψ(t)` by monotonicity. -/
theorem admissiblePsi_minimalGrowthPre
    {Ψ : ℝ → ℝ} {K : ℝ} (hK : 1 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (m : ℕ) {t : ℝ} (ht : K ^ m ≤ t) :
    K ^ natTriangular m ≤ Ψ t := by
  have hKm_nonneg : 0 ≤ K ^ m := by
    positivity
  have ht_nonneg : 0 ≤ t := le_trans hKm_nonneg ht
  have hmono : Ψ (K ^ m) ≤ Ψ t := by
    exact hAdmissible.1 hKm_nonneg ht_nonneg ht
  exact (admissiblePsi_lowerBound_pow_natTriangular hK hΨ hAdmissible m).trans hmono

theorem two_mul_natTriangular (n : ℕ) :
    2 * natTriangular n = n * (n - 1) := by
  induction n with
  | zero =>
      simp [natTriangular]
  | succ n ih =>
      rw [natTriangular_succ]
      calc
        2 * (natTriangular n + n) = 2 * natTriangular n + 2 * n := by ring
        _ = n * (n - 1) + 2 * n := by rw [ih]
        _ = (n - 1) * n + 2 * n := by rw [Nat.mul_comm n (n - 1)]
        _ = ((n - 1) + 2) * n := by rw [Nat.add_mul]
        _ = (n + 1) * n := by
          cases n with
          | zero =>
              simp
          | succ n =>
              simp [add_left_comm, add_comm]
        _ = (n + 1) * ((n + 1) - 1) := by simp

theorem natTriangular_real_eq (n : ℕ) :
    (natTriangular n : ℝ) = (n : ℝ) * ((n - 1 : ℕ) : ℝ) / 2 := by
  have hcast : (2 : ℝ) * (natTriangular n : ℝ) = (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (two_mul_natTriangular n)
  apply (eq_div_iff (show (2 : ℝ) ≠ 0 by norm_num)).2
  linarith

private theorem exists_pow_le_and_exp_log_sq_div_le_pow_natTriangular
    {K x : ℝ} (hK : 2 ≤ K) (hx : K ^ (2 : ℕ) ≤ x) :
    ∃ n : ℕ,
      K ^ n ≤ x ∧
        Real.exp (Real.log x ^ (2 : ℕ) / (9 * Real.log K)) ≤ K ^ natTriangular n := by
  have hK_one_le : 1 ≤ K := le_trans one_le_two hK
  have hK_one : 1 < K := lt_of_lt_of_le one_lt_two hK
  have hK_pos : 0 < K := lt_trans zero_lt_one hK_one
  have hlogK_pos : 0 < Real.log K := Real.log_pos hK_one
  have hx_pos : 0 < x := lt_of_lt_of_le (pow_pos hK_pos 2) hx
  have hx_one : 1 ≤ x := by
    have hKsq_one : 1 ≤ K ^ (2 : ℕ) := by
      simpa using one_le_pow_of_one_le_real hK_one_le 2
    exact hKsq_one.trans hx
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx_one
  let n : ℕ := Nat.floor (Real.log x / Real.log K)
  have hdiv_nonneg : 0 ≤ Real.log x / Real.log K := by
    exact div_nonneg hlogx_nonneg hlogK_pos.le
  have hn_le : (n : ℝ) ≤ Real.log x / Real.log K := by
    simpa [n] using (Nat.floor_le hdiv_nonneg :
      (Nat.floor (Real.log x / Real.log K) : ℝ) ≤ _)
  have hdiv_lt : Real.log x / Real.log K < n + 1 := by
    simpa [n] using
      (Nat.lt_floor_add_one (Real.log x / Real.log K) :
        Real.log x / Real.log K < (Nat.floor (Real.log x / Real.log K) : ℕ) + 1)
  have hlog_lower : (n : ℝ) * Real.log K ≤ Real.log x := by
    exact (le_div_iff₀ hlogK_pos).1 hn_le
  have hlog_upper_lt : Real.log x < (n + 1 : ℝ) * Real.log K := by
    exact (div_lt_iff₀ hlogK_pos).1 hdiv_lt
  have hpow_lower : K ^ n ≤ x := by
    have : K ^ (n : ℝ) ≤ x := by
      exact (Real.rpow_le_iff_le_log hK_pos hx_pos).2 hlog_lower
    simpa [Real.rpow_natCast] using this
  have htwo_log : (2 : ℝ) * Real.log K ≤ Real.log x := by
    exact Real.le_log_of_pow_le hK_pos (by simpa using hx)
  have htwo_div : (2 : ℝ) ≤ Real.log x / Real.log K := by
    exact (le_div_iff₀ hlogK_pos).2 htwo_log
  have hn_two : 2 ≤ n := by
    exact Nat.le_floor htwo_div
  have htri_lb : (((n : ℝ) + 1) ^ (2 : ℕ)) / 9 ≤ (natTriangular n : ℝ) := by
    rw [natTriangular_real_eq]
    have hn_one : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn_two
    rw [Nat.cast_sub hn_one]
    have hn_two_real : (2 : ℝ) ≤ n := by
      exact_mod_cast hn_two
    nlinarith only [hn_two_real]
  have hsq :
      Real.log x ^ (2 : ℕ) ≤ (((n : ℝ) + 1) * Real.log K) ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ hlogx_nonneg hlog_upper_lt.le 2
  have hfirst :
      Real.log x ^ (2 : ℕ) / (9 * Real.log K)
        ≤ (((n : ℝ) + 1) * Real.log K) ^ (2 : ℕ) / (9 * Real.log K) := by
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have hsecond :
      (((n : ℝ) + 1) * Real.log K) ^ (2 : ℕ) / (9 * Real.log K)
        ≤ (natTriangular n : ℝ) * Real.log K := by
    have := mul_le_mul_of_nonneg_right htri_lb hlogK_pos.le
    have hlogK_ne : Real.log K ≠ 0 := ne_of_gt hlogK_pos
    simpa [pow_two, div_eq_mul_inv, hlogK_ne, mul_assoc, mul_left_comm, mul_comm] using this
  have hexp_le :
      Real.exp (Real.log x ^ (2 : ℕ) / (9 * Real.log K))
        ≤ K ^ natTriangular n := by
    have hKpow :
        K ^ natTriangular n = Real.exp ((natTriangular n : ℝ) * Real.log K) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hK_pos]
      simp [mul_comm]
    rw [hKpow]
    exact (Real.exp_le_exp).2 (hfirst.trans hsecond)
  exact ⟨n, hpow_lower, hexp_le⟩

/-- Step 2 of the Chapter 4 `O_Ψ` calculus: the growth hypothesis forces at
least log-squared growth of `Ψ`. -/
theorem admissiblePsi_minimalGrowth
    {Ψ : ℝ → ℝ} {K t : ℝ} (hK : 2 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (ht : K ^ (2 : ℕ) ≤ t) :
    Real.exp (Real.log t ^ (2 : ℕ) / (9 * Real.log K)) ≤ Ψ t := by
  have hK_one_le : 1 ≤ K := le_trans one_le_two hK
  obtain ⟨n, hpow_lower, hexp_le⟩ :=
    exists_pow_le_and_exp_log_sq_div_le_pow_natTriangular hK ht
  exact hexp_le.trans (admissiblePsi_minimalGrowthPre hK_one_le hΨ hAdmissible n hpow_lower)

/-- Discrete lower bounds for the normalized ratio `Ψ(t K^m) / Ψ(t)`. -/
theorem admissiblePsi_ratioLowerBound_pow_natTriangular
    {Ψ : ℝ → ℝ} {K t : ℝ} (hK : 1 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (ht : 1 ≤ t) :
    ∀ m : ℕ, K ^ natTriangular m ≤ Ψ (t * K ^ m) / Ψ t
  | m => by
      let Φ : ℝ → ℝ := fun s => Ψ (t * s)
      have hΦ : HasPsiGrowth Φ K := by
        intro s hs
        have hts : 1 ≤ t * s := by
          calc
            (1 : ℝ) = 1 * 1 := by ring
            _ ≤ t * s := mul_le_mul ht hs (by norm_num : (0 : ℝ) ≤ 1)
              (le_trans zero_le_one ht)
        have hΨ_nonneg : 0 ≤ Ψ (t * s) := by
          exact le_trans zero_le_one (hAdmissible.2 (le_trans zero_le_one hts))
        have hscale : s * Ψ (t * s) ≤ (t * s) * Ψ (t * s) := by
          have hmul : s ≤ t * s := by
            calc
              s = 1 * s := by ring
              _ ≤ t * s := mul_le_mul_of_nonneg_right ht (le_trans zero_le_one hs)
          exact mul_le_mul_of_nonneg_right hmul hΨ_nonneg
        exact hscale.trans <| by
          simpa [Φ, mul_assoc, mul_left_comm, mul_comm] using hΨ (t := t * s) hts
      have hpre := hasPsiGrowth_nat_polyAbsorptionPre hK hΦ m (show 1 ≤ (1 : ℝ) by norm_num)
      have hpre' : Ψ t ≤ (K ^ natTriangular m)⁻¹ * Ψ (t * K ^ m) := by
        simpa [Φ, mul_assoc, mul_left_comm, mul_comm] using hpre
      have hΨt_one : 1 ≤ Ψ t := hAdmissible.2 (le_trans zero_le_one ht)
      have hΨt_pos : 0 < Ψ t := lt_of_lt_of_le zero_lt_one hΨt_one
      have hKtri_pos : 0 < K ^ natTriangular m := by
        positivity
      have hmul : K ^ natTriangular m * Ψ t ≤ Ψ (t * K ^ m) := by
        have :=
          mul_le_mul_of_nonneg_left hpre' (le_of_lt hKtri_pos)
        simpa [hKtri_pos.ne', mul_assoc, mul_left_comm, mul_comm] using this
      exact (le_div_iff₀ hΨt_pos).2 hmul

/-- The discrete ratio lower bound extends from `K^m` to every larger `s` by
monotonicity of `Ψ`. -/
theorem admissiblePsi_ratioMinimalGrowthPre
    {Ψ : ℝ → ℝ} {K t : ℝ} (hK : 1 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (ht : 1 ≤ t) (m : ℕ) {s : ℝ} (hs : K ^ m ≤ s) :
    K ^ natTriangular m ≤ Ψ (t * s) / Ψ t := by
  have hratio :=
    admissiblePsi_ratioLowerBound_pow_natTriangular hK hΨ hAdmissible ht m
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hKs_nonneg : 0 ≤ K ^ m := by positivity
  have hs_nonneg : 0 ≤ s := le_trans hKs_nonneg hs
  have harg : t * K ^ m ≤ t * s := by
    exact mul_le_mul_of_nonneg_left hs ht0
  have hmono : Ψ (t * K ^ m) ≤ Ψ (t * s) := by
    exact hAdmissible.1 (mul_nonneg ht0 hKs_nonneg) (mul_nonneg ht0 hs_nonneg) harg
  have hΨt_one : 1 ≤ Ψ t := hAdmissible.2 (le_trans zero_le_one ht)
  have hΨt_nonneg : 0 ≤ Ψ t := le_trans zero_le_one hΨt_one
  have hdiv :
      Ψ (t * K ^ m) / Ψ t ≤ Ψ (t * s) / Ψ t := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hmono (inv_nonneg.mpr hΨt_nonneg)
  exact hratio.trans hdiv

/-- The log-squared minimal-growth bound for the normalized ratio
`Ψ(ts) / Ψ(t)`. -/
theorem admissiblePsi_ratioMinimalGrowth
    {Ψ : ℝ → ℝ} {K t s : ℝ} (hK : 2 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (ht : 1 ≤ t) (hs : K ^ (2 : ℕ) ≤ s) :
    Real.exp (Real.log s ^ (2 : ℕ) / (9 * Real.log K)) ≤ Ψ (t * s) / Ψ t := by
  have hK_one_le : 1 ≤ K := le_trans one_le_two hK
  obtain ⟨n, hpow_lower, hexp_le⟩ :=
    exists_pow_le_and_exp_log_sq_div_le_pow_natTriangular hK hs
  exact hexp_le.trans (admissiblePsi_ratioMinimalGrowthPre hK_one_le hΨ hAdmissible ht n hpow_lower)

/-- Step 4 in the Chapter 4 proof: the growth condition implies a doubling
estimate for `Ψ`. -/
theorem admissiblePsi_doubling
    {Ψ : ℝ → ℝ} {K q t s : ℝ} (hK : 2 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 2 ≤ q) (ht : 1 ≤ t) (hs : 1 ≤ s) :
    s ^ q ≤ K ^ (3 * q ^ (2 : ℕ)) * (Ψ (t * s) / Ψ t) := by
  have hK_one_le : 1 ≤ K := le_trans one_le_two hK
  have hK_one : 1 < K := lt_of_lt_of_le one_lt_two hK
  have hK_pos : 0 < K := lt_trans zero_lt_one hK_one
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hq_nonneg : 0 ≤ q := le_trans zero_le_two hq
  by_cases hs_large : K ^ (2 : ℕ) ≤ s
  · have hratio :=
      admissiblePsi_ratioMinimalGrowth hK hΨ hAdmissible ht hs_large
    have hlogs_nonneg : 0 ≤ Real.log s := Real.log_nonneg hs
    have hlogK_pos : 0 < Real.log K := Real.log_pos hK_one
    have hpoly :
        s ^ q ≤ K ^ (3 * q ^ (2 : ℕ)) *
          Real.exp (Real.log s ^ (2 : ℕ) / (9 * Real.log K)) := by
      have haux :
          Real.log s * q - (3 * q ^ (2 : ℕ)) * Real.log K
            ≤ Real.log s ^ (2 : ℕ) / (9 * Real.log K) := by
        have hnine : 0 < 9 * Real.log K := by positivity
        refine (le_div_iff₀ hnine).2 ?_
        have hsqnonneg : 0 ≤ (Real.log s - (9 / 2 : ℝ) * q * Real.log K) ^ (2 : ℕ) := by
          exact sq_nonneg _
        nlinarith only [hsqnonneg, hlogK_pos]
      have hexpArg :
          Real.log s * q
            ≤ (3 * q ^ (2 : ℕ)) * Real.log K
              + Real.log s ^ (2 : ℕ) / (9 * Real.log K) := by
        linarith [haux]
      rw [Real.rpow_def_of_pos hs_pos, Real.rpow_def_of_pos hK_pos, ← Real.exp_add]
      refine (Real.exp_le_exp).2 ?_
      simpa [mul_assoc, mul_left_comm, mul_comm] using hexpArg
    calc
      s ^ q ≤ K ^ (3 * q ^ (2 : ℕ)) *
          Real.exp (Real.log s ^ (2 : ℕ) / (9 * Real.log K)) := hpoly
      _ ≤ K ^ (3 * q ^ (2 : ℕ)) * (Ψ (t * s) / Ψ t) := by
          exact mul_le_mul_of_nonneg_left hratio (by positivity)
  · have hs_upper : s ≤ K ^ (2 : ℕ) := le_of_not_ge hs_large
    have hsmall :
        s ^ q ≤ K ^ (3 * q ^ (2 : ℕ)) := by
      have hs_two :
          s ^ q ≤ (K ^ (2 : ℕ) : ℝ) ^ q := by
        exact Real.rpow_le_rpow (le_trans zero_le_one hs) hs_upper hq_nonneg
      have hK_nonneg : 0 ≤ K := le_trans zero_le_one hK_one_le
      have hpow_two : (K ^ (2 : ℕ) : ℝ) ^ q = K ^ ((2 : ℕ) * q) := by
        symm
        simpa [mul_comm] using (Real.rpow_natCast_mul hK_nonneg 2 q)
      have hs_bound : s ^ q ≤ K ^ ((2 : ℕ) * q) := by
        simpa [hpow_two] using hs_two
      have hpow_mono : K ^ ((2 : ℝ) * q) ≤ K ^ (3 * q ^ (2 : ℕ)) := by
        refine Real.rpow_le_rpow_of_exponent_le hK_one_le ?_
        have htwo_le_threeq : (2 : ℝ) ≤ 3 * q := by
          calc
            (2 : ℝ) ≤ q := hq
            _ = 1 * q := by ring
            _ ≤ 3 * q := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) hq_nonneg
        calc
          (2 : ℝ) * q ≤ (3 * q) * q := mul_le_mul_of_nonneg_right htwo_le_threeq hq_nonneg
          _ = 3 * q ^ (2 : ℕ) := by ring
      exact hs_bound.trans hpow_mono
    have ht0 : 0 ≤ t := le_trans zero_le_one ht
    have hnum : Ψ t ≤ Ψ (t * s) := by
      have harg : t ≤ t * s := by
        simpa using (mul_le_mul_of_nonneg_left hs ht0 : t * 1 ≤ t * s)
      exact hAdmissible.1 ht0 (mul_nonneg ht0 (le_trans zero_le_one hs)) harg
    have hΨt_one : 1 ≤ Ψ t := hAdmissible.2 ht0
    have hΨt_pos : 0 < Ψ t := lt_of_lt_of_le zero_lt_one hΨt_one
    have hratio_one : 1 ≤ Ψ (t * s) / Ψ t := by
      exact (le_div_iff₀ hΨt_pos).2 (by simpa using hnum)
    have hKpow_nonneg : 0 ≤ K ^ (3 * q ^ (2 : ℕ)) := by
      positivity
    calc
      s ^ q ≤ K ^ (3 * q ^ (2 : ℕ)) := hsmall
      _ ≤ K ^ (3 * q ^ (2 : ℕ)) * (Ψ (t * s) / Ψ t) := by
          calc
            K ^ (3 * q ^ (2 : ℕ)) =
                K ^ (3 * q ^ (2 : ℕ)) * 1 := by ring
            _ ≤ K ^ (3 * q ^ (2 : ℕ)) * (Ψ (t * s) / Ψ t) :=
              mul_le_mul_of_nonneg_left hratio_one hKpow_nonneg

theorem admissiblePsi_hasPsiAbstractDoubling
    {Ψ : ℝ → ℝ} {K q : ℝ} (hK : 2 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) (hq : 2 ≤ q) :
    HasPsiAbstractDoubling Ψ q (K ^ (3 * q ^ (2 : ℕ))) := by
  intro t s ht hs
  exact admissiblePsi_doubling hK hΨ hAdmissible hq ht hs

theorem admissiblePsi_hasPsiAbstractDoubling_two
    {Ψ : ℝ → ℝ} {K : ℝ} (hK : 2 ≤ K) (hΨ : HasPsiGrowth Ψ K)
    (hAdmissible : AdmissiblePsi Ψ) :
    HasPsiAbstractDoubling Ψ 2 (K ^ (12 : ℝ)) := by
  convert
    (admissiblePsi_hasPsiAbstractDoubling (K := K) (q := (2 : ℝ))
      hK hΨ hAdmissible (by norm_num : (2 : ℝ) ≤ 2))
  norm_num

/-- Under the abstract doubling hypothesis, the doubling constant is at least `1`. -/
theorem hasPsiAbstractDoubling_one_le_const
    {Ψ : ℝ → ℝ} {q C₀ : ℝ} (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) :
    1 ≤ C₀ := by
  have hΨone : 1 ≤ Ψ 1 := hAdmissible.2 zero_le_one
  have hΨone_pos : 0 < Ψ 1 := lt_of_lt_of_le zero_lt_one hΨone
  simpa [hΨone_pos.ne'] using hD (t := 1) (s := 1) (by norm_num) (by norm_num)

/-- Step 5 helper: the abstract doubling estimate can be rewritten as an upper
bound on the inverse tail profile. -/
theorem hasPsiAbstractDoubling_inv_mul_le
    {Ψ : ℝ → ℝ} {q C₀ u v : ℝ} (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    (Ψ (u * v))⁻¹ ≤ C₀ * v ^ (-q) * (Ψ u)⁻¹ := by
  have hC₀_one : 1 ≤ C₀ := hasPsiAbstractDoubling_one_le_const hD hAdmissible
  have hC₀_pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀_one
  have hv_pos : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hΨu_one : 1 ≤ Ψ u := hAdmissible.2 (le_trans zero_le_one hu)
  have hΨu_pos : 0 < Ψ u := lt_of_lt_of_le zero_lt_one hΨu_one
  have huv_one : 1 ≤ u * v := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ u * v := mul_le_mul hu hv (by norm_num : (0 : ℝ) ≤ 1) (le_trans zero_le_one hu)
  have hΨuv_one : 1 ≤ Ψ (u * v) := hAdmissible.2 (le_trans zero_le_one huv_one)
  have hΨuv_pos : 0 < Ψ (u * v) := lt_of_lt_of_le zero_lt_one hΨuv_one
  have hdiv : v ^ q * Ψ u / C₀ ≤ Ψ (u * v) := by
    have htmp := hD hu hv
    field_simp [hC₀_pos.ne', hΨu_pos.ne'] at htmp ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm] using htmp
  have hdiv_pos : 0 < v ^ q * Ψ u / C₀ := by
    have hvq_pos : 0 < v ^ q := Real.rpow_pos_of_pos hv_pos q
    positivity
  have hrhs :
      C₀ * v ^ (-q) * (Ψ u)⁻¹ = (v ^ q * Ψ u / C₀)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hv_pos)]
    field_simp [hC₀_pos.ne', hΨu_pos.ne', (Real.rpow_pos_of_pos hv_pos q).ne']
  rw [hrhs]
  exact (inv_le_inv₀ hΨuv_pos hdiv_pos).2 hdiv

/-- Note-facing Step 5 helper: specialize abstract doubling to the tail profile
`s ↦ Ψ (s / a)⁻¹` on the half-line `s ≥ ta / 2`. -/
theorem hasPsiAbstractDoubling_scaledInvTail
    {Ψ : ℝ → ℝ} {q C₀ a t s : ℝ} (hD : HasPsiAbstractDoubling Ψ q C₀)
    (hAdmissible : AdmissiblePsi Ψ) (ha : 0 < a) (ht : 2 ≤ t)
    (hs : t * a / 2 ≤ s) :
    (Ψ (s / a))⁻¹ ≤
      C₀ * (Ψ (t / 2))⁻¹ * ((2 * s) / (a * t)) ^ (-q) := by
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_two ht
  have hu : 1 ≤ t / 2 := by
    calc
      (1 : ℝ) = 2 / 2 := by norm_num
      _ ≤ t / 2 := div_le_div_of_nonneg_right ht (by norm_num)
  have hv : 1 ≤ (2 * s) / (a * t) := by
    rw [one_le_div_iff]
    left
    constructor
    · positivity
    · calc
        a * t = 2 * (t * a / 2) := by ring
        _ ≤ 2 * s := mul_le_mul_of_nonneg_left hs (by norm_num)
  have hmain :=
    hasPsiAbstractDoubling_inv_mul_le (hD := hD) (hAdmissible := hAdmissible)
      (u := t / 2) (v := (2 * s) / (a * t)) hu hv
  have harg : (t / 2) * (s * 2 / (a * t)) = s / a := by
    field_simp [ha.ne', ht_pos.ne']
  simpa [harg, mul_assoc, mul_left_comm, mul_comm] using hmain

/-- The power-tail integral appearing in Step 5 of the Chapter 4
generalized triangle inequality proof. -/
theorem integral_Ioi_div_rpow_neg
    {q c : ℝ} (hq : 1 < q) (hc : 0 < c) :
    ∫ s : ℝ in Set.Ioi c, (s / c) ^ (-q) = c / (q - 1) := by
  calc
    ∫ s : ℝ in Set.Ioi c, (s / c) ^ (-q)
      = ∫ s : ℝ in Set.Ioi c, c ^ q * s ^ (-q) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro s hs
          have hs_pos : 0 < s := lt_trans hc hs
          calc
            (s / c) ^ (-q) = s ^ (-q) / c ^ (-q) := by
              rw [Real.div_rpow (le_of_lt hs_pos) hc.le]
            _ = s ^ (-q) / (c ^ q)⁻¹ := by
              rw [Real.rpow_neg (le_of_lt hc)]
            _ = s ^ (-q) * c ^ q := by
              rw [div_eq_mul_inv, inv_inv]
            _ = c ^ q * s ^ (-q) := by ring
    _ = c ^ q * ∫ s : ℝ in Set.Ioi c, s ^ (-q) := by
          rw [MeasureTheory.integral_const_mul]
    _ = c ^ q * (-c ^ (-q + 1) / (-q + 1)) := by
          rw [integral_Ioi_rpow_of_lt (by linarith : -q < -1) hc]
    _ = c / (q - 1) := by
          have hpow : c ^ q * c ^ (-q + 1) = c := by
            calc
              c ^ q * c ^ (-q + 1) = c ^ (q + (-q + 1)) := by
                rw [← Real.rpow_add hc q (-q + 1)]
              _ = c ^ (1 : ℝ) := by ring_nf
              _ = c := by rw [Real.rpow_one]
          calc
            c ^ q * (-c ^ (-q + 1) / (-q + 1))
                = -(c ^ q * c ^ (-q + 1)) / (-q + 1) := by ring
            _ = -c / (-q + 1) := by rw [hpow]
            _ = c / (q - 1) := by
              rw [show -q + 1 = -(q - 1) by ring, div_neg, neg_div, neg_neg]

/-- A concrete growth constant for the stretched-exponential model class
`Γ_σ`, chosen so that the Chapter 4 growth hypothesis holds for every
`σ > 0`. -/
noncomputable def gammaGrowthConst (σ : ℝ) : ℝ :=
  max 2 ((1 + σ⁻¹) ^ (σ⁻¹))

theorem two_le_gammaGrowthConst (σ : ℝ) :
    2 ≤ gammaGrowthConst σ := by
  exact le_max_left _ _

theorem hasPsiGrowth_gammaSigma {σ : ℝ} (hσ : 0 < σ) :
    HasPsiGrowth (gammaSigma σ) (gammaGrowthConst σ) := by
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hσinv_pos : 0 < σ⁻¹ := inv_pos.mpr hσ
  have hbase_pos : 0 < 1 + σ⁻¹ := by positivity
  have hbase_nonneg : 0 ≤ 1 + σ⁻¹ := hbase_pos.le
  have hK_nonneg : 0 ≤ gammaGrowthConst σ := le_trans zero_le_two (two_le_gammaGrowthConst σ)
  have hpow_nonneg : 0 ≤ t ^ σ := Real.rpow_nonneg ht0 σ
  have hlog :
      Real.log t ≤ σ⁻¹ * t ^ σ := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (Real.log_le_rpow_div ht0 hσ)
  have harg_le :
      Real.log t + t ^ σ ≤ (1 + σ⁻¹) * t ^ σ := by
    calc
      Real.log t + t ^ σ ≤ σ⁻¹ * t ^ σ + t ^ σ := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hlog (t ^ σ)
      _ = (1 + σ⁻¹) * t ^ σ := by ring
  have hKpow_lower :
      1 + σ⁻¹ ≤ gammaGrowthConst σ ^ σ := by
    have hcandidate_le :
        ((1 + σ⁻¹) ^ (σ⁻¹)) ^ σ ≤ gammaGrowthConst σ ^ σ := by
      exact Real.rpow_le_rpow
        (Real.rpow_nonneg hbase_nonneg _)
        (le_max_right 2 ((1 + σ⁻¹) ^ (σ⁻¹)))
        hσ.le
    rw [← Real.rpow_mul hbase_nonneg, inv_mul_cancel₀ hσ.ne', Real.rpow_one] at hcandidate_le
    exact hcandidate_le
  have htarget :
      (1 + σ⁻¹) * t ^ σ ≤ ((gammaGrowthConst σ) * t) ^ σ := by
    calc
      (1 + σ⁻¹) * t ^ σ ≤ (gammaGrowthConst σ ^ σ) * t ^ σ := by
        exact mul_le_mul_of_nonneg_right hKpow_lower hpow_nonneg
      _ = ((gammaGrowthConst σ) * t) ^ σ := by
        rw [Real.mul_rpow hK_nonneg ht0]
  calc
    t * gammaSigma σ t = Real.exp (Real.log t) * Real.exp (t ^ σ) := by
      rw [Real.exp_log ht_pos, gammaSigma]
    _ = Real.exp (Real.log t + t ^ σ) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (((gammaGrowthConst σ) * t) ^ σ) := by
      exact (Real.exp_le_exp).2 (harg_le.trans htarget)
    _ = gammaSigma σ (gammaGrowthConst σ * t) := by
      simp [gammaSigma]

/-- The explicit Chapter 4 growth constant for the log-normal model class
`Ψ_σ`. -/
noncomputable def psiGrowthConst (σ : ℝ) : ℝ :=
  2 * Real.exp (2 * σ ^ (2 : ℕ))

theorem two_le_psiGrowthConst (σ : ℝ) :
    2 ≤ psiGrowthConst σ := by
  have hexp_one : 1 ≤ Real.exp (2 * σ ^ (2 : ℕ)) := by
    apply Real.one_le_exp
    positivity
  dsimp [psiGrowthConst]
  calc
    (2 : ℝ) = 2 * 1 := by ring
    _ ≤ 2 * Real.exp (2 * σ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hexp_one (by norm_num)

theorem hasPsiGrowth_psiSigma {σ : ℝ} (hσ : 1 ≤ σ) :
    HasPsiGrowth (psiSigma σ) (psiGrowthConst σ) := by
  intro t ht
  let K : ℝ := psiGrowthConst σ
  let A : ℝ := Real.log (1 + σ * (K * t))
  let B : ℝ := Real.log (1 + σ * t)
  have hσ_pos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hσsq_pos : 0 < σ ^ (2 : ℕ) := by positivity
  have hK_two : 2 ≤ K := by
    simpa [K] using two_le_psiGrowthConst σ
  have hKσ_one : 1 ≤ K * σ := by
    have hK_nonneg : 0 ≤ K := le_trans zero_le_two hK_two
    calc
      (1 : ℝ) ≤ 2 * 1 := by norm_num
      _ ≤ K * σ := mul_le_mul hK_two hσ (by norm_num : (0 : ℝ) ≤ 1) hK_nonneg
  have hargA_pos : 0 < 1 + σ * (K * t) := by positivity
  have hargB_pos : 0 < 1 + σ * t := by positivity
  have hargA_ge_t : t ≤ 1 + σ * (K * t) := by
    have hKt : t ≤ K * σ * t := by
      have hmul : 1 * t ≤ (K * σ) * t := by
        exact mul_le_mul_of_nonneg_right hKσ_one (le_of_lt ht_pos)
      simpa using hmul
    calc
      t ≤ K * σ * t := hKt
      _ = σ * (K * t) := by ring
      _ ≤ 1 + σ * (K * t) := le_add_of_nonneg_left zero_le_one
  have hA_ge_logt : Real.log t ≤ A := by
    exact Real.log_le_log ht_pos (by simpa [A] using hargA_ge_t)
  have hlogt_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht
  have hargB_one : 1 ≤ 1 + σ * t := by
    exact le_add_of_nonneg_right (mul_nonneg hσ_pos.le ht_pos.le)
  have hB_nonneg : 0 ≤ B := by
    exact Real.log_nonneg (by simpa [B] using hargB_one)
  have hden_le : 1 + σ * t ≤ 2 * σ * t := by
    have hσt_one : 1 ≤ σ * t := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ σ * t := mul_le_mul hσ ht (by norm_num : (0 : ℝ) ≤ 1) hσ_pos.le
    calc
      1 + σ * t ≤ σ * t + σ * t := by
        simpa [add_comm] using add_le_add_right hσt_one (σ * t)
      _ = 2 * σ * t := by ring
  have hratio_lower : K / 2 ≤ (1 + σ * (K * t)) / (1 + σ * t) := by
    rw [le_div_iff₀ hargB_pos]
    calc
      (K / 2) * (1 + σ * t) ≤ (K / 2) * (2 * σ * t) := by
        refine mul_le_mul_of_nonneg_left hden_le ?_
        positivity
      _ = K * σ * t := by ring
      _ = σ * (K * t) := by ring
      _ ≤ 1 + σ * (K * t) := le_add_of_nonneg_left zero_le_one
  have hK_div_two_pos : 0 < K / 2 := by
    have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_two hK_two
    positivity
  have hlog_gap :
      Real.log (K / 2) ≤ A - B := by
    calc
      Real.log (K / 2) ≤ Real.log ((1 + σ * (K * t)) / (1 + σ * t)) := by
        exact Real.log_le_log hK_div_two_pos hratio_lower
      _ = A - B := by
        simp [A, B, Real.log_div, hargA_pos.ne', hargB_pos.ne']
  have hlog_K_div_two :
      Real.log (K / 2) = 2 * σ ^ (2 : ℕ) := by
    calc
      Real.log (K / 2) = Real.log (Real.exp (2 * σ ^ (2 : ℕ))) := by
        rw [show K / 2 = Real.exp (2 * σ ^ (2 : ℕ)) by
          dsimp [K, psiGrowthConst]
          field_simp]
      _ = 2 * σ ^ (2 : ℕ) := by rw [Real.log_exp]
  have hgap : 2 * σ ^ (2 : ℕ) ≤ A - B := by
    rw [← hlog_K_div_two]
    exact hlog_gap
  have hgap_nonneg : 0 ≤ A - B := by
    have : 0 ≤ 2 * σ ^ (2 : ℕ) := by positivity
    exact this.trans hgap
  have hA_nonneg : 0 ≤ A := le_trans hlogt_nonneg hA_ge_logt
  have hprod :
      Real.log t * (2 * σ ^ (2 : ℕ)) ≤ A * (A - B) := by
    calc
      Real.log t * (2 * σ ^ (2 : ℕ)) ≤ A * (2 * σ ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_right hA_ge_logt (by positivity)
      _ ≤ A * (A - B) := by
        exact mul_le_mul_of_nonneg_left hgap hA_nonneg
  have hsum_prod :
      A * (A - B) ≤ (A + B) * (A - B) := by
    have hA_le : A ≤ A + B := le_add_of_nonneg_right hB_nonneg
    exact mul_le_mul_of_nonneg_right hA_le hgap_nonneg
  have hsqdiff :
      σ ^ (2 : ℕ) * Real.log t ≤ A ^ (2 : ℕ) - B ^ (2 : ℕ) := by
    calc
      σ ^ (2 : ℕ) * Real.log t ≤ (2 * σ ^ (2 : ℕ)) * Real.log t := by
        have hprod_nonneg : 0 ≤ σ ^ (2 : ℕ) * Real.log t :=
          mul_nonneg (sq_nonneg σ) hlogt_nonneg
        calc
          σ ^ (2 : ℕ) * Real.log t =
              1 * (σ ^ (2 : ℕ) * Real.log t) := by ring
          _ ≤ 2 * (σ ^ (2 : ℕ) * Real.log t) :=
            mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hprod_nonneg
          _ = (2 * σ ^ (2 : ℕ)) * Real.log t := by ring
      _ = Real.log t * (2 * σ ^ (2 : ℕ)) := by ring
      _ ≤ A * (A - B) := hprod
      _ ≤ (A + B) * (A - B) := hsum_prod
      _ = A ^ (2 : ℕ) - B ^ (2 : ℕ) := by ring
  have harg_main :
      Real.log t + (σ ^ (2 : ℕ))⁻¹ * B ^ (2 : ℕ) ≤
        (σ ^ (2 : ℕ))⁻¹ * A ^ (2 : ℕ) := by
    have hsqdiff_div :
        Real.log t ≤ (σ ^ (2 : ℕ))⁻¹ * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) := by
      have hmul :=
        mul_le_mul_of_nonneg_left hsqdiff (inv_nonneg.mpr (sq_nonneg σ))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hσsq_pos.ne'] using hmul
    calc
      Real.log t + (σ ^ (2 : ℕ))⁻¹ * B ^ (2 : ℕ) ≤
          (σ ^ (2 : ℕ))⁻¹ * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) +
            (σ ^ (2 : ℕ))⁻¹ * B ^ (2 : ℕ) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right hsqdiff_div ((σ ^ (2 : ℕ))⁻¹ * B ^ (2 : ℕ))
      _ = (σ ^ (2 : ℕ))⁻¹ * A ^ (2 : ℕ) := by ring
  calc
    t * psiSigma σ t =
        Real.exp (Real.log t) *
          Real.exp ((σ ^ (2 : ℕ))⁻¹ * B ^ (2 : ℕ)) := by
            rw [Real.exp_log ht_pos, psiSigma]
    _ = Real.exp (Real.log t + (σ ^ (2 : ℕ))⁻¹ * B ^ (2 : ℕ)) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp ((σ ^ (2 : ℕ))⁻¹ * A ^ (2 : ℕ)) := by
      exact (Real.exp_le_exp).2 harg_main
    _ = psiSigma σ (K * t) := by
      simp [psiSigma, A]

end IndependentSums
end Homogenization
