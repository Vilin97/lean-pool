/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.Convergence
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealFactor
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem summable_ideal_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-σ)) := by
  let e := Equiv.sigmaFiberEquiv (absNorm : Ideal (𝓞 K) → ℕ)
  rw [← e.summable_iff]
  apply (summable_sigma_of_nonneg (fun x ↦
    Real.rpow_nonneg (Nat.cast_nonneg (absNorm (e x))) _)).2
  constructor
  · intro n
    letI : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq n).fintype
    exact Summable.of_finite
  · have hseries :=
      (lSeriesSummable_idealNormCount K (s := (σ : ℂ)) (by simpa using hσ)).norm
    convert hseries using 1
    ext n
    simp only [e, Equiv.sigmaFiberEquiv_apply, LSeries.norm_term_eq]
    split_ifs with hn
    · subst n
      have hzero :
          (fun y : {I : Ideal (𝓞 K) // absNorm I = 0} ↦
            (absNorm (y : Ideal (𝓞 K)) : ℝ) ^ (-σ)) = 0 := by
        funext y
        rw [y.2]
        simp [ne_of_gt (zero_lt_one.trans hσ)]
      rw [hzero]
      change (∑' _ : {I : Ideal (𝓞 K) // absNorm I = 0}, (0 : ℝ)) = 0
      simp
    · have hconst :
          (fun y : {I : Ideal (𝓞 K) // absNorm I = n} ↦
            (absNorm (y : Ideal (𝓞 K)) : ℝ) ^ (-σ)) =
            fun _ ↦ (n : ℝ) ^ (-σ) := by grind
      rw [hconst, tsum_const]
      simp only [idealNormCount, nsmul_eq_mul, norm_natCast]
      rw [Real.rpow_neg (Nat.cast_nonneg n)]
      simp [div_eq_mul_inv]

theorem summable_primeIdealNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable
      (fun P : HeightOneSpectrum (𝓞 K) ↦ (primeIdealNorm K P : ℝ) ^ (-σ)) := by
  change Summable
    ((fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-σ)) ∘
      HeightOneSpectrum.asIdeal)
  exact (summable_ideal_absNorm_rpow K hσ).comp_injective
    HeightOneSpectrum.asIdeal_injective

theorem summable_primeIdeal_log_mul_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun P : HeightOneSpectrum (𝓞 K) ↦
      Real.log (primeIdealNorm K P) *
        (primeIdealNorm K P : ℝ) ^ (-σ)) := by
  let ε : ℝ := (σ - 1) / 2
  let τ : ℝ := (σ + 1) / 2
  have hε : 0 < ε := by grind
  have hτ : 1 < τ := by grind
  apply ((summable_primeIdealNorm_rpow K hτ).mul_left (1 / ε)).of_nonneg_of_le
    (fun P ↦ mul_nonneg
      (Real.log_nonneg (by exact_mod_cast
        (Nat.le_of_lt (one_lt_primeIdealNorm K P))))
      (Real.rpow_nonneg (by positivity) _))
  intro P
  let q := primeIdealNorm K P
  have hq : (0 : ℝ) < q := by
    exact_mod_cast (Nat.zero_lt_of_lt (one_lt_primeIdealNorm K P))
  calc
    Real.log q * (q : ℝ) ^ (-σ) ≤
        ((q : ℝ) ^ ε / ε) * (q : ℝ) ^ (-σ) := by
      gcongr
      exact Real.log_le_rpow_div (by positivity) hε
    _ = (1 / ε) * (q : ℝ) ^ (-τ) := by
      have hexp : ε + -σ = -τ := by grind
      rw [div_mul_eq_mul_div, ← Real.rpow_add hq, hexp]
      ring

lemma norm_inverseNormPower_primeIdeal_lt_half
    (P : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    ‖inverseNormPower (primeIdealNorm K P) s‖ < 1 / 2 := by
  let q := primeIdealNorm K P
  have hq : 1 < q := one_lt_primeIdealNorm K P
  rw [norm_inverseNormPower q (Nat.zero_lt_of_lt hq) s, Real.rpow_neg]
  · have hpow : (q : ℝ) < (q : ℝ) ^ s.re :=
      Real.self_lt_rpow_of_one_lt (by simp_all) hs
    have hinv : ((q : ℝ) ^ s.re)⁻¹ < (q : ℝ)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by positivity)).mpr hpow
    exact hinv.trans_le <| by
      rw [inv_le_comm₀ (by positivity) (by positivity)]
      norm_num
      grind
  · simp

theorem summable_norm_primeIdealFactor_sub_one {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun P : HeightOneSpectrum (𝓞 K) ↦ ‖primeIdealFactor K P s - 1‖) := by
  have hbase := (summable_primeIdealNorm_rpow K hs).mul_left 2
  apply hbase.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro P
  let x := inverseNormPower (primeIdealNorm K P) s
  have hx : ‖x‖ < 1 / 2 :=
    norm_inverseNormPower_primeIdeal_lt_half K P hs
  have hden : 1 - inverseNormPower (primeIdealNorm K P) s ≠ 0 :=
    one_sub_inverseNormPower_ne_zero (one_lt_primeIdealNorm K P) (zero_lt_one.trans hs)
  have hrewrite : primeIdealFactor K P s - 1 = x / (1 - x) := by
    simp only [primeIdealFactor, localFactor, x]
    grind
  rw [hrewrite, norm_div]
  have hdenLower : 1 / 2 ≤ ‖1 - x‖ := by
    calc
      1 / 2 ≤ 1 - ‖x‖ := by linarith
      _ ≤ ‖1 - x‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) x
  calc
    ‖x‖ / ‖1 - x‖ ≤ ‖x‖ / (1 / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg x) (by positivity) hdenLower
    _ = 2 * (primeIdealNorm K P : ℝ) ^ (-s.re) := by
      rw [show ‖x‖ = (primeIdealNorm K P : ℝ) ^ (-s.re) by
        exact norm_inverseNormPower _ (Nat.zero_lt_of_lt <| one_lt_primeIdealNorm K P) s]
      ring

theorem norm_primeIdealFactor_sub_one_le
    (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ} {s : ℂ}
    (hσ : 1 < σ) (hs : σ ≤ s.re) :
    ‖primeIdealFactor K P s - 1‖ ≤
      2 * (primeIdealNorm K P : ℝ) ^ (-σ) := by
  let x := inverseNormPower (primeIdealNorm K P) s
  have hs1 : 1 < s.re := hσ.trans_le hs
  have hx : ‖x‖ < 1 / 2 :=
    norm_inverseNormPower_primeIdeal_lt_half K P hs1
  have hden : 1 - inverseNormPower (primeIdealNorm K P) s ≠ 0 :=
    one_sub_inverseNormPower_ne_zero (one_lt_primeIdealNorm K P)
      (zero_lt_one.trans hs1)
  have hrewrite : primeIdealFactor K P s - 1 = x / (1 - x) := by
    simp only [primeIdealFactor, localFactor, x]
    grind
  rw [hrewrite, norm_div]
  have hdenLower : 1 / 2 ≤ ‖1 - x‖ := by
    calc
      1 / 2 ≤ 1 - ‖x‖ := by linarith
      _ ≤ ‖1 - x‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) x
  calc
    ‖x‖ / ‖1 - x‖ ≤ ‖x‖ / (1 / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg x) (by positivity) hdenLower
    _ = 2 * (primeIdealNorm K P : ℝ) ^ (-s.re) := by
      rw [show ‖x‖ = (primeIdealNorm K P : ℝ) ^ (-s.re) by
        exact norm_inverseNormPower _ (Nat.zero_lt_of_lt <| one_lt_primeIdealNorm K P) s]
      ring
    _ ≤ 2 * (primeIdealNorm K P : ℝ) ^ (-σ) := by
      have hq : (1 : ℝ) ≤ primeIdealNorm K P := by
        exact_mod_cast (Nat.le_of_lt (one_lt_primeIdealNorm K P))
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq (by linarith)) (by norm_num)

theorem multipliable_primeIdealFactor {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun P : HeightOneSpectrum (𝓞 K) ↦ primeIdealFactor K P s) := by
  simpa only [add_sub_cancel] using
    multipliable_one_add_of_summable (summable_norm_primeIdealFactor_sub_one K hs)

theorem tprod_primeIdealFactor_ne_zero {s : ℂ} (hs : 1 < s.re) :
    ∏' P : HeightOneSpectrum (𝓞 K), primeIdealFactor K P s ≠ 0 := by
  let f := fun P : HeightOneSpectrum (𝓞 K) ↦ primeIdealFactor K P s - 1
  have hnonzero : ∀ P, 1 + f P ≠ 0 := fun P ↦ by
    simpa [f] using primeIdealFactor_ne_zero K P (zero_lt_one.trans hs)
  have hsum : Summable (fun P ↦ ‖f P‖) := by
    simpa [f] using summable_norm_primeIdealFactor_sub_one K hs
  simpa [f] using tprod_one_add_ne_zero_of_summable hnonzero hsum

end NumberField.Odlyzko
