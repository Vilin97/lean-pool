/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import LeanPool.Shannon1948Formalization.Entropy.Final

/-!
# Shannon.Entropy.Gibbs

Gibbs inequality and single-variable entropy bounds.

The Gibbs inequality (`∑ pᵢ log(qᵢ/pᵢ) ≤ 0`) is the analytical workhorse for
deriving the properties of Shannon entropy listed in Section 6 of Shannon (1948).
It follows from `log x ≤ x - 1` and the fact that probability masses sum to one.

We also connect `entropyNat` to Mathlib's `Real.negMulLog`, giving access to
Mathlib's concavity infrastructure for later proofs.

## Main results

- `entropyNat_eq_sum_negMulLog`: bridge between `entropyNat` and `Real.negMulLog`
- `gibbs_inequality`: `∑ pᵢ log(qᵢ/pᵢ) ≤ 0`
- `entropyNat_nonneg`: `H(p) ≥ 0`
- `entropyNat_uniformPNat`: `H(uniform n) = log n`
- `entropyNat_le_log_card`: `H(p) ≤ log |α|`
-/
namespace LeanPool.Shannon1948Formalization

noncomputable section
open Finset Real

/-! ## Bridge to negMulLog -/

/-- `entropyNat p = ∑ a, negMulLog (p a)`, connecting our definition to Mathlib's
`Real.negMulLog` which carries concavity and differentiability lemmas. -/
lemma entropyNat_eq_sum_negMulLog {α : Type} [Fintype α] (p : ProbDist α) :
    entropyNat p = ∑ a, Real.negMulLog (p a) := by
  unfold entropyNat Real.negMulLog
  simp [Finset.sum_neg_distrib, neg_mul]

/-! ## Gibbs inequality -/

/-- **Gibbs inequality**: for probability distributions `p` and `q` where `q` covers
the support of `p`, we have `∑ pᵢ log(qᵢ/pᵢ) ≤ 0`. Equivalently, the
Kullback-Leibler divergence `D(p ‖ q) ≥ 0`.

The proof uses `log x ≤ x - 1` on each ratio `qᵢ/pᵢ`, then telescopes via
`∑ qᵢ = ∑ pᵢ = 1`. -/
theorem gibbs_inequality {α : Type} [Fintype α]
    (p q : ProbDist α) (hsupp : ∀ a, 0 < p a → 0 < q a) :
    ∑ a, p a * Real.log (q a / p a) ≤ 0 := by
  have key : ∀ a, p a * Real.log (q a / p a) ≤ q a - p a := fun a => by
    by_cases hp : p a = 0
    · simp [hp, prob_nonneg q a]
    · have hpa : 0 < p a := lt_of_le_of_ne (prob_nonneg p a) (Ne.symm hp)
      have hqa : 0 < q a := hsupp a hpa
      have := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hqa hpa)) hpa.le
      linarith [show p a * (q a / p a - 1) = q a - p a by field_simp]
  have hle : ∑ a, p a * Real.log (q a / p a) ≤ ∑ a, (q a - p a) :=
    Finset.sum_le_sum (fun a _ => key a)
  simp_rw [Finset.sum_sub_distrib, prob_sum_eq_one q, prob_sum_eq_one p] at hle
  linarith

/-! ## Single-variable entropy bounds -/

/-- Entropy is nonnegative: each `negMulLog(pᵢ) ≥ 0` for `pᵢ ∈ [0, 1]`. -/
theorem entropyNat_nonneg {α : Type} [Fintype α] (p : ProbDist α) :
    0 ≤ entropyNat p := by
  rw [entropyNat_eq_sum_negMulLog]
  exact Finset.sum_nonneg fun a _ => Real.negMulLog_nonneg (prob_nonneg p a) (prob_le_one p a)

/-- Entropy of the uniform distribution on `n` outcomes equals `log n`. -/
theorem entropyNat_uniformPNat (n : ℕ+) :
    entropyNat (uniformPNat n) = Real.log n := by
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt n.2
  rw [entropyNat_eq_sum_negMulLog]
  simp_rw [show ∀ a : Fin n, (uniformPNat n : Fin n → ℝ) a = 1 / (n : ℝ) from fun _ => rfl,
    Real.negMulLog, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Real.log_div one_ne_zero hn_ne, Real.log_one, zero_sub]
  simp [nsmul_eq_mul, hn_ne]

/-- Entropy is at most `log |α|`, with equality at the uniform distribution.
The proof applies `gibbs_inequality` with `q = uniform`. -/
theorem entropyNat_le_log_card {α : Type} [Fintype α] [Nonempty α]
    (p : ProbDist α) :
    entropyNat p ≤ Real.log (Fintype.card α) := by
  have hcard_pos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt hcard_pos
  let q : ProbDist α := ⟨fun _ => 1 / (Fintype.card α : ℝ),
    fun _ => by positivity, by simp [Finset.card_univ, hcard_ne]⟩
  have hsupp : ∀ a, 0 < p a → 0 < q a := fun _ _ => by positivity
  have hgibbs := gibbs_inequality p q hsupp
  suffices h : ∑ a, p a * Real.log (q a / p a) =
      entropyNat p - Real.log (Fintype.card α) by linarith
  have hterm : ∀ a, p a * Real.log (q a / p a) =
      p a * Real.log (q a) - p a * Real.log (p a) := fun a => by
    by_cases hp : p a = 0
    · simp [hp]
    · have hpa : 0 < p a := lt_of_le_of_ne (prob_nonneg p a) (Ne.symm hp)
      rw [Real.log_div (ne_of_gt (hsupp a hpa)) (ne_of_gt hpa), mul_sub]
  simp_rw [hterm, sub_eq_add_neg, Finset.sum_add_distrib]
  have hlogq : ∑ a, p a * Real.log (q a) = -Real.log (Fintype.card α) := by
    simp_rw [show ∀ a, q a = 1 / (Fintype.card α : ℝ) from fun _ => rfl,
      Real.log_div one_ne_zero hcard_ne, Real.log_one, zero_sub,
      ← Finset.sum_mul, prob_sum_eq_one p, one_mul]
  rw [hlogq, Finset.sum_neg_distrib]
  unfold entropyNat; ring

end

end LeanPool.Shannon1948Formalization
