/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.EulerProductLogDeriv
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A prime power log term used in the Odlyzko-bound argument. -/
noncomputable def primePowerLogTerm
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) (s : ℂ) : ℂ :=
  Complex.log (primeIdealNorm K P) *
    inverseNormPower (primeIdealNorm K P) s ^ (e + 1)

theorem primePowerLogTerm_eq_log_mul_cexp_neg
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) (s : ℂ) :
    primePowerLogTerm K P e s =
      (Real.log (primeIdealNorm K P) : ℂ) *
        Complex.exp
          (-(((e + 1 : ℕ) : ℝ) *
            Real.log (primeIdealNorm K P)) * s) := by
  have hq : (0 : ℝ) ≤ primeIdealNorm K P := by positivity
  have hqC : (primeIdealNorm K P : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt (one_lt_primeIdealNorm K P)).ne'
  rw [primePowerLogTerm, inverseNormPower,
    Complex.cpow_def_of_ne_zero hqC, ← Complex.exp_nat_mul]
  rw [Complex.ofReal_log hq]
  push_cast
  ring_nf

lemma norm_primePowerLogTerm
    (P : HeightOneSpectrum (𝓞 K)) (e : ℕ) (s : ℂ) :
    ‖primePowerLogTerm K P e s‖ =
      Real.log (primeIdealNorm K P) *
        ((primeIdealNorm K P : ℝ) ^ (-s.re)) ^ (e + 1) := by
  let q := primeIdealNorm K P
  have hq : 1 < q := one_lt_primeIdealNorm K P
  have hlog : ‖Complex.log (q : ℂ)‖ = Real.log q := by
    calc
      ‖Complex.log (q : ℂ)‖ =
          ‖((Real.log (q : ℝ) : ℝ) : ℂ)‖ := by simp
      _ = Real.log q := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_nonneg (by exact_mod_cast
            (Nat.le_of_lt hq)))]
  rw [primePowerLogTerm, norm_mul, norm_pow, hlog,
    norm_inverseNormPower q (Nat.zero_lt_of_lt hq)]

theorem summable_norm_primePowerLogTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
      ‖primePowerLogTerm K pe.1 pe.2 s‖) := by
  rw [summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)]
  constructor
  · intro P
    rw [show (fun e ↦ ‖primePowerLogTerm K P e s‖) =
        fun e ↦ Real.log (primeIdealNorm K P) *
          ((primeIdealNorm K P : ℝ) ^ (-s.re)) ^ (e + 1) by
      funext e
      exact norm_primePowerLogTerm K P e s]
    exact ((summable_geometric_of_lt_one
      (Real.rpow_nonneg (by positivity) _)
      (by
        rw [← norm_inverseNormPower
          (primeIdealNorm K P)
          (Nat.zero_lt_of_lt <| one_lt_primeIdealNorm K P) s]
        exact (norm_inverseNormPower_primeIdeal_lt_half K P hs).trans
          (by norm_num))).comp_injective
            (fun _ _ h ↦ Nat.add_right_cancel h)).mul_left _
  · have hmajor :=
      (summable_primeIdeal_log_mul_rpow K hs).mul_left 2
    apply hmajor.of_nonneg_of_le
      (fun _ ↦ tsum_nonneg fun _ ↦ norm_nonneg _)
    intro P
    let q := primeIdealNorm K P
    let r : ℝ := (q : ℝ) ^ (-s.re)
    have hq : 1 < q := one_lt_primeIdealNorm K P
    have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
    have hrhalf : r < 1 / 2 := by
      dsimp [r]
      rw [← norm_inverseNormPower q (Nat.zero_lt_of_lt hq) s]
      exact norm_inverseNormPower_primeIdeal_lt_half K P hs
    rw [show (fun e ↦ ‖primePowerLogTerm K P e s‖) =
        fun e ↦ Real.log q * r ^ (e + 1) by
      funext e
      exact norm_primePowerLogTerm K P e s]
    rw [tsum_mul_left]
    have hgeom :
        ∑' e : ℕ, r ^ (e + 1) = r / (1 - r) := by
      rw [show (fun e : ℕ ↦ r ^ (e + 1)) =
          fun e ↦ r * r ^ e by
        grind]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 (hrhalf.trans (by norm_num))]
      simp [div_eq_mul_inv]
    rw [hgeom]
    calc
      Real.log q * (r / (1 - r)) ≤ Real.log q * (2 * r) := by
        gcongr
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      _ = 2 * (Real.log q * (q : ℝ) ^ (-s.re)) := by grind

theorem neg_logDeriv_dedekindZeta_eq_tsum_primePower {s : ℂ}
    (hs : 1 < s.re) :
    -logDeriv (dedekindZeta K) s =
      ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
        primePowerLogTerm K pe.1 pe.2 s := by
  have habs := summable_norm_primePowerLogTerm K hs
  have hsum :
      Summable (fun pe : HeightOneSpectrum (𝓞 K) × ℕ ↦
        primePowerLogTerm K pe.1 pe.2 s) :=
    summable_norm_iff.mp habs
  rw [neg_logDeriv_dedekindZeta_eq_tsum_primeIdeal K hs]
  rw [hsum.tsum_prod]
  congr 1
  funext P
  exact (hasSum_neg_logDeriv_primeIdealFactor K P
    (zero_lt_one.trans hs)).tsum_eq.symm

end NumberField.Odlyzko
