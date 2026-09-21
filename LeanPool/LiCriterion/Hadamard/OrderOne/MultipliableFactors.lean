/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import LeanPool.LiCriterion.Hadamard.Basic
import LeanPool.LiCriterion.Hadamard.OrderOne.CofiniteControl

/-!
Genus‑1 canonical factors are multipliable under the standard hypothesis `∑ 1/‖z i‖² < ∞`.

This isolates the analytic input used repeatedly when building canonical products:
for fixed `s`, the family `i ↦ weierstrassE 1 (s / z i)` is an infinite product that converges.
-/

open Complex Filter
open scoped BigOperators

namespace Hadamard
namespace OrderOne

lemma summable_norm_weierstrass_E_one_sub_one_of_summable_inv_norm_sq {ι : Type} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i => (1 : ℝ) / ‖z i‖ ^ 2))
    (s : ℂ) :
    Summable (fun i : ι => ‖weierstrassE 1 (s / z i) - 1‖) := by
  classical
  by_cases hs : s = 0
  · subst hs
    simp [weierstrass_E_zero_arg]
  · have hs_norm : 0 < ‖s‖ := norm_pos_iff.2 hs
    have hR : 0 < (2 : ℝ) * ‖s‖ := by nlinarith
    let S : Set ι := {i : ι | ‖z i‖ ≤ (2 : ℝ) * ‖s‖}
    have hSfinite : S.Finite :=
      finite_norm_le_of_summable_inv_norm_sq (z := z) hz0 h (R := (2 : ℝ) * ‖s‖) hR
    -- Split the norm-series into a finite “bad” part on `S` plus a summable tail on `Sᶜ`.
    have hS_part :
        Summable (fun i : ι => if i ∈ S then ‖weierstrassE 1 (s / z i) - 1‖ else 0) := by
      refine summable_of_hasFiniteSupport ?_
      have hsupp : Function.support
          (fun i : ι => if i ∈ S then ‖weierstrassE 1 (s / z i) - 1‖ else 0) ⊆ S := by
        intro i hi
        by_contra hnot
        have : (if i ∈ S then ‖weierstrassE 1 (s / z i) - 1‖ else 0) ≠ 0 := by
          simpa [Function.support] using hi
        simp [hnot] at this
      exact hSfinite.subset hsupp
    -- Tail: for `i ∉ S`, we have `‖s / z i‖ ≤ 1/2`, so the genus‑1 bound applies.
    have hTail :
        Summable (fun i : ι => if i ∈ S then 0 else ‖weierstrassE 1 (s / z i) - 1‖) := by
      have hu :
          Summable (fun i : ι => (4 * ‖s‖ ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2)) := by
        exact h.mul_left (4 * ‖s‖ ^ 2)
      refine Summable.of_nonneg_of_le
          (f := fun i : ι => (4 * ‖s‖ ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2))
          (g := fun i : ι => if i ∈ S then 0 else ‖weierstrassE 1 (s / z i) - 1‖) ?_ ?_ hu
      · intro i
        by_cases hi : i ∈ S <;> simp [hi, norm_nonneg]
      · intro i
        by_cases hi : i ∈ S
        · have hnonneg :
              0 ≤ (4 * ‖s‖ ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2) := by
            positivity
          simpa [hi] using hnonneg
        · have hz_gt : (2 : ℝ) * ‖s‖ < ‖z i‖ := by
            have : ¬‖z i‖ ≤ (2 : ℝ) * ‖s‖ := by simpa [S] using hi
            exact lt_of_not_ge this
          have hz_pos : 0 < ‖z i‖ := norm_pos_iff.2 (hz0 i)
          have hratio : ‖s‖ / ‖z i‖ ≤ (1 / 2 : ℝ) := by
            refine (div_le_iff₀ hz_pos).2 ?_
            have hz_ge : (2 : ℝ) * ‖s‖ ≤ ‖z i‖ := le_of_lt hz_gt
            have := mul_le_mul_of_nonneg_left hz_ge (by positivity : 0 ≤ (1 / 2 : ℝ))
            simpa [mul_assoc] using this
          have hdiv : ‖s / z i‖ ≤ (1 / 2 : ℝ) := by
            simpa [norm_div] using hratio
          have hE :
              ‖weierstrassE 1 (s / z i) - 1‖ ≤ (4 * ‖s‖ ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2) := by
            have hE' := weierstrass_E_small_disk_norm_sub_one_le (h := 1) (z := s / z i) hdiv
            simpa [pow_two, norm_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hE'
          simpa [hi] using hE
    -- Recombine.
    have :
        Summable (fun i : ι =>
          (if i ∈ S then ‖weierstrassE 1 (s / z i) - 1‖ else 0) +
            (if i ∈ S then 0 else ‖weierstrassE 1 (s / z i) - 1‖)) :=
      hS_part.add hTail
    have hsum :
        (fun i : ι =>
          (if i ∈ S then ‖weierstrassE 1 (s / z i) - 1‖ else 0) +
            (if i ∈ S then 0 else ‖weierstrassE 1 (s / z i) - 1‖))
          = (fun i : ι => ‖weierstrassE 1 (s / z i) - 1‖) := by
      funext i
      by_cases hi : i ∈ S <;> simp [hi]
    simpa [hsum] using this

lemma multipliable_weierstrass_E_one_of_summable_inv_norm_sq {ι : Type} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i => (1 : ℝ) / ‖z i‖ ^ 2))
    (s : ℂ) :
    Multipliable (fun i : ι => weierstrassE 1 (s / z i)) := by
  have hsumm :
      Summable (fun i : ι => ‖weierstrassE 1 (s / z i) - 1‖) :=
    summable_norm_weierstrass_E_one_sub_one_of_summable_inv_norm_sq (z := z) hz0 h s
  have hmul : Multipliable (fun i : ι => 1 + (weierstrassE 1 (s / z i) - 1)) :=
    multipliable_one_add_of_summable hsumm
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmul

/-! ### General-rank versions -/

/-- **Rank-`p` analogue of `summable_norm_weierstrass_E_one_sub_one_of_summable_inv_norm_sq`.**

Under `∑ 1/‖z i‖^(p+1) < ∞`, the family `‖E_p(s/z i) - 1‖` is summable for every `s : ℂ`. -/
lemma summable_norm_weierstrass_E_sub_one_of_summable_inv_norm_pow
    {ι : Type*} {z : ι → ℂ} {p : ℕ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i => (1 : ℝ) / ‖z i‖ ^ (p + 1)))
    (s : ℂ) :
    Summable (fun i : ι => ‖weierstrassE p (s / z i) - 1‖) := by
  classical
  by_cases hs : s = 0
  · subst hs
    simp [weierstrass_E_zero_arg]
  · have hs_norm : 0 < ‖s‖ := norm_pos_iff.2 hs
    have hR : 0 < (2 : ℝ) * ‖s‖ := by nlinarith
    let S : Set ι := {i : ι | ‖z i‖ ≤ (2 : ℝ) * ‖s‖}
    have hSfinite : S.Finite :=
      finite_norm_le_of_summable_inv_norm_pow (z := z) (p := p) hz0 h (R := (2 : ℝ) * ‖s‖) hR
    -- Bad (finite) part.
    have hS_part :
        Summable (fun i : ι => if i ∈ S then ‖weierstrassE p (s / z i) - 1‖ else 0) := by
      refine summable_of_hasFiniteSupport ?_
      have hsupp : Function.support
          (fun i : ι => if i ∈ S then ‖weierstrassE p (s / z i) - 1‖ else 0) ⊆ S := by
        intro i hi
        by_contra hnot
        have : (if i ∈ S then ‖weierstrassE p (s / z i) - 1‖ else 0) ≠ 0 := by
          simpa [Function.support] using hi
        simp [hnot] at this
      exact hSfinite.subset hsupp
    have hTail :
        Summable (fun i : ι => if i ∈ S then 0 else ‖weierstrassE p (s / z i) - 1‖) := by
      have hu :
          Summable (fun i : ι => (4 * ‖s‖ ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1))) := by
        exact h.mul_left (4 * ‖s‖ ^ (p + 1))
      refine Summable.of_nonneg_of_le
          (f := fun i : ι => (4 * ‖s‖ ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)))
          (g := fun i : ι => if i ∈ S then 0 else ‖weierstrassE p (s / z i) - 1‖) ?_ ?_ hu
      · intro i
        by_cases hi : i ∈ S <;> simp [hi, norm_nonneg]
      · intro i
        by_cases hi : i ∈ S
        · have hnonneg :
              0 ≤ (4 * ‖s‖ ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)) := by
            positivity
          simpa [hi] using hnonneg
        · have hz_gt : (2 : ℝ) * ‖s‖ < ‖z i‖ := by
            have : ¬‖z i‖ ≤ (2 : ℝ) * ‖s‖ := by simpa [S] using hi
            exact lt_of_not_ge this
          have hz_pos : 0 < ‖z i‖ := norm_pos_iff.2 (hz0 i)
          have hratio : ‖s‖ / ‖z i‖ ≤ (1 / 2 : ℝ) := by
            refine (div_le_iff₀ hz_pos).2 ?_
            have hz_ge : (2 : ℝ) * ‖s‖ ≤ ‖z i‖ := le_of_lt hz_gt
            have := mul_le_mul_of_nonneg_left hz_ge (by positivity : 0 ≤ (1 / 2 : ℝ))
            simpa [mul_assoc] using this
          have hdiv : ‖s / z i‖ ≤ (1 / 2 : ℝ) := by
            simpa [norm_div] using hratio
          have hE :
              ‖weierstrassE p (s / z i) - 1‖ ≤ 4 * ‖s / z i‖ ^ (p + 1) :=
            weierstrass_E_small_disk_norm_sub_one_le (h := p) (z := s / z i) hdiv
          -- Rewrite `4 * ‖s/z i‖^(p+1)` as `(4 * ‖s‖^(p+1)) * (1/‖z i‖^(p+1))`.
          have hz_pos_pow : (0 : ℝ) < ‖z i‖ ^ (p + 1) := by positivity
          have hrw : 4 * ‖s / z i‖ ^ (p + 1)
              = (4 * ‖s‖ ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)) := by
            rw [norm_div, div_pow]
            field_simp
          have hfinal :
              ‖weierstrassE p (s / z i) - 1‖ ≤
                (4 * ‖s‖ ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)) := by
            rw [← hrw]; exact hE
          simpa [hi] using hfinal
    have :
        Summable (fun i : ι =>
          (if i ∈ S then ‖weierstrassE p (s / z i) - 1‖ else 0) +
            (if i ∈ S then 0 else ‖weierstrassE p (s / z i) - 1‖)) :=
      hS_part.add hTail
    have hsum :
        (fun i : ι =>
          (if i ∈ S then ‖weierstrassE p (s / z i) - 1‖ else 0) +
            (if i ∈ S then 0 else ‖weierstrassE p (s / z i) - 1‖))
          = (fun i : ι => ‖weierstrassE p (s / z i) - 1‖) := by
      funext i
      by_cases hi : i ∈ S <;> simp [hi]
    simpa [hsum] using this

/-- **Rank-`p` analogue of `multipliable_weierstrass_E_one_of_summable_inv_norm_sq`.** -/
lemma multipliable_weierstrass_E_of_summable_inv_norm_pow
    {ι : Type*} {z : ι → ℂ} {p : ℕ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i => (1 : ℝ) / ‖z i‖ ^ (p + 1)))
    (s : ℂ) :
    Multipliable (fun i : ι => weierstrassE p (s / z i)) := by
  have hsumm :
      Summable (fun i : ι => ‖weierstrassE p (s / z i) - 1‖) :=
    summable_norm_weierstrass_E_sub_one_of_summable_inv_norm_pow (z := z) (p := p) hz0 h s
  have hmul : Multipliable (fun i : ι => 1 + (weierstrassE p (s / z i) - 1)) :=
    multipliable_one_add_of_summable hsumm
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmul

end OrderOne
end Hadamard
