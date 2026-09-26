/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Infinite q-Pochhammer symbol

Under $\|q\| < 1$, the infinite product $(a;q)_\infty = \prod_{k \geq 0}(1 - aq^k)$
converges. We define it via `tprod` and prove convergence, non-vanishing, and
partial-product convergence.

## Main definitions

* `QSeries.qPochhammerInf a q` — the infinite q-Pochhammer symbol $(a;q)_\infty$.

## Main results

* `QSeries.multipliable_one_sub_mul_pow` — multipliability for $\|q\| < 1$.
* `QSeries.tendsto_qPochhammer` — partial products converge to $(a;q)_\infty$.
* `QSeries.qPochhammerInf_ne_zero` — non-vanishing for $\|z\| < 1$, $\|q\| < 1$.
* `QSeries.qPochhammerInf_eq_one_sub_mul` — telescoping $(z;q)_\infty = (1-z)(zq;q)_\infty$.
-/

public section

open Finset Filter
open scoped Topology

namespace QSeries

/-- **Infinite q-Pochhammer symbol** $(a;q)_\infty = \prod_{k=0}^{\infty}(1 - aq^k)$.

Defined unconditionally as a `tprod`; convergence (under $\|q\| < 1$) is provided
by `multipliable_one_sub_mul_pow`. -/
@[expose] noncomputable def qPochhammerInf (a q : ℂ) : ℂ := ∏' k : ℕ, (1 - a * q ^ k)

/-- For $\|q\| < 1$ the sequence $n \mapsto \|{-}(a q^n)\|$ is summable: it is the
geometric series $\|a\| \cdot \|q\|^n$. -/
theorem summable_norm_neg_mul_pow {a q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(a * q ^ n)‖ := by
  simpa [norm_neg, norm_mul, norm_pow] using
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a‖

/-- If $\|z\| < 1$ and $\|q\| \le 1$ then $z q^k \ne 1$, so the q-Pochhammer factors
$1 - z q^k$ are all nonzero. -/
theorem one_sub_mul_pow_ne_zero {z q : ℂ} (hz : ‖z‖ < 1) (hq : ‖q‖ ≤ 1) (k : ℕ) :
    (1 : ℂ) - z * q ^ k ≠ 0 := by
  intro h
  have hnorm : ‖z‖ * ‖q‖ ^ k = 1 := by
    rw [← norm_pow, ← norm_mul, show z * q ^ k = 1 from by linear_combination -h, norm_one]
  nlinarith [norm_nonneg z, pow_le_one₀ (norm_nonneg q) hq (n := k),
    pow_nonneg (norm_nonneg q) k]

/-- For $\|q\| < 1$, the product $\prod_{k \geq 0}(1 - aq^k)$ is multipliable. -/
theorem multipliable_one_sub_mul_pow {a q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable (fun k : ℕ => 1 - a * q ^ k) := by
  simpa [sub_eq_add_neg] using
    multipliable_one_add_of_summable (summable_norm_neg_mul_pow (a := a) hq)

/-- **Non-vanishing of $(q;q)_n$ for $\|q\| < 1$.** -/
theorem qPochhammer_self_ne_zero {q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammer q q n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => one_sub_mul_pow_ne_zero hq hq.le k

/-- **Non-vanishing of $(z;q)_n$ when $\|z\| < 1$ and $\|q\| \le 1$.** -/
theorem qPochhammer_ne_zero {z q : ℂ} (hz : ‖z‖ < 1) (hq : ‖q‖ ≤ 1)
    (n : ℕ) : qPochhammer z q n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => one_sub_mul_pow_ne_zero hz hq k

/-- Helper: $(a;q)_\infty \neq 0$ when every factor is nonzero. -/
theorem qPochhammerInf_ne_zero_of_forall_ne_zero {a q : ℂ} (hq : ‖q‖ < 1)
    (hfac : ∀ k : ℕ, (1 : ℂ) - a * q ^ k ≠ 0) :
    qPochhammerInf a q ≠ 0 := by
  have h_main := tprod_one_add_ne_zero_of_summable
    (f := fun k : ℕ => -(a * q ^ k))
    (fun i => by rw [← sub_eq_add_neg]; exact hfac i) (summable_norm_neg_mul_pow hq)
  simpa [qPochhammerInf, sub_eq_add_neg] using h_main

/-- **Non-vanishing of $(z;q)_\infty$ for $\|z\| < 1, \|q\| < 1$.** -/
theorem qPochhammerInf_ne_zero {z q : ℂ} (hz : ‖z‖ < 1) (hq : ‖q‖ < 1) :
    qPochhammerInf z q ≠ 0 :=
  qPochhammerInf_ne_zero_of_forall_ne_zero hq fun k => one_sub_mul_pow_ne_zero hz hq.le k

/-- **Partial products converge to $(a;q)_\infty$.** -/
theorem tendsto_qPochhammer {a q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun n => qPochhammer a q n) atTop (𝓝 (qPochhammerInf a q)) := by
  have hmul : Multipliable (fun k : ℕ => 1 - a * q ^ k) :=
    multipliable_one_sub_mul_pow hq
  simpa [qPochhammer, qPochhammerInf] using hmul.hasProd.tendsto_prod_nat

/-- **Telescoping recursion for $(z;q)_\infty$.**
$(z;q)_\infty = (1 - z) \cdot (zq;q)_\infty$. -/
theorem qPochhammerInf_eq_one_sub_mul {z q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf z q = (1 - z) * qPochhammerInf (z * q) q := by
  have h_fin : ∀ n : ℕ,
      qPochhammer z q (n + 1) = (1 - z) * qPochhammer (z * q) q n := by
    intro n
    rw [qPochhammer, qPochhammer, Finset.prod_range_succ', mul_comm]
    simp [pow_succ', mul_assoc]
  have hLHS : Tendsto (fun n => (1 - z) * qPochhammer (z * q) q n) atTop
                (𝓝 (qPochhammerInf z q)) := by
    simpa only [h_fin] using
      (tendsto_add_atTop_iff_nat 1).mpr (tendsto_qPochhammer (a := z) hq)
  exact tendsto_nhds_unique hLHS ((tendsto_qPochhammer (a := z * q) hq).const_mul (1 - z))

end QSeries
