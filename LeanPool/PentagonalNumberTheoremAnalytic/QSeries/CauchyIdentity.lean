/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.InfPochhammer
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The Cauchy identity (infinite q-binomial theorem)

This file proves the **infinite q-binomial / Cauchy identity**:
for $\|q\| < 1$ and $\|z\| < 1$,
$$\sum_{n=0}^{\infty} \frac{(a;q)_n}{(q;q)_n} z^n = \frac{(az;q)_\infty}{(z;q)_\infty}.$$

The proof follows Heine's classical functional-equation argument.

## Main results

* `QSeries.hasSum_qPochhammer_div_mul_pow` — the Cauchy identity.
-/

open Finset Filter
open scoped Topology

namespace QSeries

section CauchyIdentity

/-- A product of two complex numbers of norm `< 1` again has norm `< 1`. -/
private theorem norm_mul_lt_one {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    ‖q * z‖ < 1 := by
  rw [norm_mul]
  nlinarith [norm_nonneg q, norm_nonneg z]

/-- If `‖q‖ < 1` and `‖z‖ < 1` then `‖q ^ n * z‖ < 1` for every `n`. -/
private theorem norm_pow_mul_lt_one {q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (n : ℕ) :
    ‖q ^ n * z‖ < 1 := by
  rw [norm_mul, norm_pow]
  nlinarith [pow_le_one₀ (norm_nonneg q) hq.le (n := n), norm_nonneg z,
    pow_nonneg (norm_nonneg q) n]

/-- The coefficient sequence $c_n = (a;q)_n / (q;q)_n$. -/
noncomputable def cauchyCoeff (a q : ℂ) (n : ℕ) : ℂ :=
  qPochhammer a q n / qPochhammer q q n

/-- The zeroth Cauchy coefficient $c_0 = 1$. -/
@[simp] theorem cauchyCoeff_zero (a q : ℂ) : cauchyCoeff a q 0 = 1 := by
  simp [cauchyCoeff]

/-- **Coefficient recurrence.** $c_{n+1}(1 - q^{n+1}) = c_n(1 - aq^n)$. -/
theorem cauchyCoeff_succ_mul {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) (n : ℕ) :
    cauchyCoeff a q (n + 1) * (1 - q ^ (n + 1))
      = cauchyCoeff a q n * (1 - a * q ^ n) := by
  unfold cauchyCoeff
  have hqn : qPochhammer q q n ≠ 0 := qPochhammer_self_ne_zero hq n
  have hqn1 : qPochhammer q q (n + 1) ≠ 0 := qPochhammer_self_ne_zero hq (n + 1)
  rw [qPochhammer_succ a q n, qPochhammer_succ q q n,
      show (1 : ℂ) - q * q ^ n = 1 - q ^ (n + 1) from by ring]
  have hq_ne : (1 : ℂ) - q ^ (n + 1) ≠ 0 := fun habs =>
    hqn1 (by rw [qPochhammer_succ q q n,
      show (1 : ℂ) - q * q ^ n = 1 - q ^ (n + 1) from by ring, habs, mul_zero])
  field_simp

/-- **Boundedness of the coefficients.**

The quotients `(a;q)_n / (q;q)_n` converge, hence form a bounded sequence. -/
theorem exists_norm_cauchyCoeff_le {q : ℂ} (hq : ‖q‖ < 1) (a : ℂ) :
    ∃ C, ∀ n, ‖cauchyCoeff a q n‖ ≤ C := by
  have h : Tendsto (fun n => ‖cauchyCoeff a q n‖) atTop
      (𝓝 ‖qPochhammerInf a q / qPochhammerInf q q‖) :=
    ((tendsto_qPochhammer hq).div (tendsto_qPochhammer hq)
      (qPochhammerInf_ne_zero hq hq)).norm
  obtain ⟨C, hC⟩ := h.bddAbove_range
  exact ⟨C, fun n => hC ⟨n, rfl⟩⟩

/-- The series $\sum_n c_n z^n$ is summable for $\|z\| < 1$. -/
theorem summable_cauchyCoeff_mul_pow {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => cauchyCoeff a q n * z ^ n) := by
  obtain ⟨C, hC⟩ := exists_norm_cauchyCoeff_le hq a
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  refine Summable.of_norm_bounded (g := fun n => C * ‖z‖ ^ n)
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C) fun n => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul (hC n) le_rfl (pow_nonneg (norm_nonneg z) n) hCnn

/-- **Functional equation for $G$.**
$(1-z)\, G(z) = (1 - az)\, G(qz)$. -/
theorem one_sub_mul_qPochhammerInf_div_eq (a z : ℂ) {q : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    (1 - z) * (qPochhammerInf (a * z) q / qPochhammerInf z q)
      = (1 - a * z) *
          (qPochhammerInf (a * z * q) q / qPochhammerInf (z * q) q) := by
  have hz_ne : qPochhammerInf z q ≠ 0 := qPochhammerInf_ne_zero hz hq
  have hzq_ne : qPochhammerInf (z * q) q ≠ 0 :=
    qPochhammerInf_ne_zero (norm_mul_lt_one hz hq) hq
  have hone_sub_z_ne : (1 : ℂ) - z ≠ 0 := fun h => by
    rw [show z = 1 from by linear_combination -h] at hz; norm_num at hz
  rw [qPochhammerInf_eq_one_sub_mul (z := z) hq, qPochhammerInf_eq_one_sub_mul (z := a * z) hq]
  field_simp

/-- **The shifted-difference series.**

If `d 0 = 1` and `∑ d n zⁿ = S`, then the series with terms `(d n - u * d (n-1)) zⁿ`
(and constant term `1`) sums to `(1 - u z) S`. This is the single computation behind
both sides of the functional equation for `F`. -/
private theorem hasSum_ite_sub_mul_pow {d : ℕ → ℂ} {z u S : ℂ} (hd0 : d 0 = 1)
    (hd : HasSum (fun n : ℕ => d n * z ^ n) S) :
    HasSum (fun n : ℕ => if n = 0 then (1 : ℂ) else (d n - u * d (n - 1)) * z ^ n)
      ((1 - u * z) * S) := by
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else u * d (n - 1) * z ^ n with hg_def
  have hg : HasSum g (u * z * S) := by
    refine (hasSum_nat_add_iff' (f := g) 1).mp ?_
    have hshift : (fun n : ℕ => g (n + 1)) = fun n : ℕ => u * z * (d n * z ^ n) := by
      funext n
      simp only [hg_def, ite_eq_right (Nat.succ_ne_zero n), Nat.add_sub_cancel, pow_succ]
      ring
    rw [hshift]
    simpa [hg_def] using hd.mul_left (u * z)
  have hfun : (fun n : ℕ => if n = 0 then (1 : ℂ) else (d n - u * d (n - 1)) * z ^ n)
      = fun n : ℕ => d n * z ^ n - g n := by
    funext n
    by_cases hn : n = 0
    · simp [hn, hg_def, hd0]
    · simp only [ite_eq_right hn, hg_def]; ring
  rw [hfun, show (1 - u * z) * S = S - u * z * S from by ring]
  exact hd.sub hg

private theorem hasSum_one_sub_mul_tsum_cauchyCoeff {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => if n = 0 then (1 : ℂ)
                          else (cauchyCoeff a q n - cauchyCoeff a q (n - 1)) * z ^ n)
      ((1 - z) * ∑' n, cauchyCoeff a q n * z ^ n) := by
  simpa using hasSum_ite_sub_mul_pow (u := 1) (cauchyCoeff_zero a q)
    (summable_cauchyCoeff_mul_pow hq hz).hasSum

private theorem hasSum_one_sub_mul_tsum_cauchyCoeff_mul_pow {a q z : ℂ} (hq : ‖q‖ < 1)
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => if n = 0 then (1 : ℂ)
                          else (cauchyCoeff a q n * q ^ n
                                  - a * cauchyCoeff a q (n - 1) * q ^ (n - 1)) * z ^ n)
      ((1 - a * z) * ∑' n, cauchyCoeff a q n * (q * z) ^ n) := by
  have hd : HasSum (fun n : ℕ => cauchyCoeff a q n * q ^ n * z ^ n)
      (∑' n, cauchyCoeff a q n * (q * z) ^ n) := by
    simpa [mul_pow, mul_assoc] using
      (summable_cauchyCoeff_mul_pow hq (norm_mul_lt_one hq hz)).hasSum
  simpa [mul_assoc] using
    hasSum_ite_sub_mul_pow (u := a) (d := fun n => cauchyCoeff a q n * q ^ n)
      (by simp) hd

/-- **Functional equation for $F$.**
$(1-z)\, F(z) = (1 - az)\, F(qz)$. -/
theorem one_sub_mul_tsum_cauchyCoeff_eq {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    (1 - z) * ∑' n, cauchyCoeff a q n * z ^ n
      = (1 - a * z) * ∑' n, cauchyCoeff a q n * (q * z) ^ n := by
  have hL := hasSum_one_sub_mul_tsum_cauchyCoeff (a := a) (q := q) (z := z) hq hz
  have hfunc : (fun n : ℕ => if n = 0 then (1 : ℂ)
                  else (cauchyCoeff a q n - cauchyCoeff a q (n - 1)) * z ^ n)
              = (fun n : ℕ => if n = 0 then (1 : ℂ)
                  else (cauchyCoeff a q n * q ^ n
                          - a * cauchyCoeff a q (n - 1) * q ^ (n - 1)) * z ^ n) := by
    ext n
    obtain _ | m := n
    · simp
    · simp only [ite_eq_right (Nat.succ_ne_zero m), Nat.succ_sub_one]
      rw [show cauchyCoeff a q (m + 1) - cauchyCoeff a q m
            = cauchyCoeff a q (m + 1) * q ^ (m + 1) - a * cauchyCoeff a q m * q ^ m from by
          linear_combination cauchyCoeff_succ_mul (a := a) hq m]
  rw [hfunc] at hL
  exact hL.unique (hasSum_one_sub_mul_tsum_cauchyCoeff_mul_pow hq hz)

/-- **Iterated functional equation.** -/
theorem mul_qPochhammer_eq_of_functional_eq {H : ℂ → ℂ} {a q : ℂ} (hq : ‖q‖ < 1)
    (hH : ∀ w, ‖w‖ < 1 → (1 - w) * H w = (1 - a * w) * H (q * w))
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∀ n : ℕ, H z * qPochhammer z q n
              = H (q ^ n * z) * qPochhammer (a * z) q n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have key := hH _ (norm_pow_mul_lt_one hq hz n)
      rw [show q * (q ^ n * z) = q ^ (n + 1) * z from by ring] at key
      rw [qPochhammer_succ z q n, qPochhammer_succ (a * z) q n]
      linear_combination (1 - q ^ n * z) * ih + qPochhammer (a * z) q n * key

/-- **$F(q^n z) \to 1$ as $n \to \infty$**, by Tannery's theorem. -/
theorem tendsto_tsum_cauchyCoeff_mul_pow {a q z : ℂ} (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    Tendsto (fun n : ℕ => ∑' k, cauchyCoeff a q k * (q ^ n * z) ^ k)
      atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := exists_norm_cauchyCoeff_le hq a
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set g : ℕ → ℂ := fun k => if k = 0 then 1 else 0 with hg_def
  have hab : ∀ k : ℕ, Tendsto (fun n : ℕ => cauchyCoeff a q k * (q ^ n * z) ^ k)
                              atTop (𝓝 (g k)) := by
    intro k
    obtain _ | m := k
    · simp [hg_def]
    · have hqpow : ‖q ^ (m + 1)‖ < 1 := by
        rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero m)
      have hmul := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hqpow).const_mul
        (cauchyCoeff a q (m + 1) * z ^ (m + 1))
      simp only [hg_def, ite_eq_right (Nat.succ_ne_zero m), mul_zero] at hmul ⊢
      exact hmul.congr fun n => by ring
  have h_bound : ∀ᶠ n in atTop, ∀ k : ℕ,
                    ‖cauchyCoeff a q k * (q ^ n * z) ^ k‖ ≤ C * ‖z‖ ^ k := by
    refine Filter.Eventually.of_forall fun n k => ?_
    rw [norm_mul, norm_pow, norm_mul, norm_pow, mul_pow]
    calc ‖cauchyCoeff a q k‖ * ((‖q‖ ^ n) ^ k * ‖z‖ ^ k)
        = ‖cauchyCoeff a q k‖ * (‖q‖ ^ n) ^ k * ‖z‖ ^ k := by ring
      _ ≤ C * 1 * ‖z‖ ^ k := by
          gcongr
          · exact hC k
          · exact pow_le_one₀ (pow_nonneg (norm_nonneg _) n)
              (pow_le_one₀ (norm_nonneg _) hq.le)
      _ = C * ‖z‖ ^ k := by ring
  have h := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left C) hab h_bound
  have hgsum : (∑' k : ℕ, g k) = 1 := by
    rw [tsum_eq_single 0 fun k hk => by simp [hg_def, hk]]; simp [hg_def]
  rwa [hgsum] at h

/-- **Infinite q-binomial / Cauchy identity.**

For $\|q\| < 1$ and $\|z\| < 1$,
$$\sum_{n=0}^{\infty} \frac{(a;q)_n}{(q;q)_n} z^n = \frac{(az;q)_\infty}{(z;q)_\infty}.$$ -/
theorem hasSum_qPochhammer_div_mul_pow (a z q : ℂ) (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => qPochhammer a q n / qPochhammer q q n * z ^ n)
      (qPochhammerInf (a * z) q / qPochhammerInf z q) := by
  change HasSum (fun n => cauchyCoeff a q n * z ^ n) _
  have hF_summable : Summable (fun n : ℕ => cauchyCoeff a q n * z ^ n) :=
    summable_cauchyCoeff_mul_pow hq hz
  set F : ℂ := ∑' n, cauchyCoeff a q n * z ^ n with hF_def
  have hden_ne : qPochhammerInf z q ≠ 0 := qPochhammerInf_ne_zero hz hq
  suffices hFG : F * qPochhammerInf z q = qPochhammerInf (a * z) q by
    rw [← (eq_div_iff hden_ne).mpr hFG]
    exact hF_summable.hasSum
  set H : ℂ → ℂ := fun w => if ‖w‖ < 1 then ∑' k, cauchyCoeff a q k * w ^ k else 0
    with hH_def
  have hH_disc : ∀ w, ‖w‖ < 1 → H w = ∑' k, cauchyCoeff a q k * w ^ k :=
    fun w hw => by simp [hH_def, hw]
  have hH_fe : ∀ w, ‖w‖ < 1 → (1 - w) * H w = (1 - a * w) * H (q * w) := by
    intro w hw
    rw [hH_disc w hw, hH_disc _ (norm_mul_lt_one hq hw)]
    exact one_sub_mul_tsum_cauchyCoeff_eq hq hw
  have key : ∀ n : ℕ,
      F * qPochhammer z q n = H (q ^ n * z) * qPochhammer (a * z) q n := by
    rw [hF_def, ← hH_disc z hz]
    exact mul_qPochhammer_eq_of_functional_eq hq hH_fe hz
  have hH_lim : Tendsto (fun n => H (q ^ n * z)) atTop (𝓝 1) :=
    (tendsto_tsum_cauchyCoeff_mul_pow hq hz).congr fun n =>
      (hH_disc _ (norm_pow_mul_lt_one hq hz n)).symm
  have hLHS : Tendsto (fun n => F * qPochhammer z q n) atTop
      (𝓝 (F * qPochhammerInf z q)) := (tendsto_qPochhammer hq).const_mul F
  have hRHS : Tendsto (fun n => H (q ^ n * z) * qPochhammer (a * z) q n) atTop
      (𝓝 (qPochhammerInf (a * z) q)) := by
    simpa using hH_lim.mul (tendsto_qPochhammer (a := a * z) hq)
  exact tendsto_nhds_unique (by simpa [key] using hLHS) hRHS

end CauchyIdentity

end QSeries
