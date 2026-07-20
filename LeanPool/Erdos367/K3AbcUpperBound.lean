/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem #367 (k = 3 case), conditional on abc

We formalize:
  1. rad(m)  — the radical (squarefree kernel) of m
  2. B₂(m)  — the powerful (2-full) part of m
  3. LEMMA STAR:  rad(m)² · B₂(m) ≤ m²
  4. Submultiplicativity of rad
  5. The abc conjecture (as a hypothesis)
  6. The main theorem:  B₂(n) · B₂(n+1) · B₂(n+2) ≤ C'_ε · n^{2+ε}
-/

open Finset BigOperators Nat

noncomputable section

namespace Erdos367

/-! ## Definitions -/

/-- The radical (squarefree kernel) of n: the product of distinct prime factors. -/
def Nat.rad (n : ℕ) : ℕ := n.primeFactors.prod id

/-- The powerful (2-full) part of n: ∏_{p : v_p(n) ≥ 2} p^{v_p(n)}. -/
def Nat.powerfulPart (n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun p => 2 ≤ n.factorization p)).prod
    (fun p => p ^ n.factorization p)

/-! ## Basic properties of rad -/

@[simp] theorem Nat.rad_zero : Nat.rad 0 = 1 := by simp [Nat.rad]

@[simp] theorem Nat.rad_one : Nat.rad 1 = 1 := by simp [Nat.rad]

theorem Nat.rad_pos (n : ℕ) (_hn : 0 < n) : 0 < Nat.rad n := by
  exact Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp

/-! ## Basic properties of powerfulPart -/

@[simp] theorem Nat.powerfulPart_zero : Nat.powerfulPart 0 = 1 := by
  simp [Nat.powerfulPart]

@[simp] theorem Nat.powerfulPart_one : Nat.powerfulPart 1 = 1 := by
  simp [Nat.powerfulPart]

theorem Nat.powerfulPart_pos (n : ℕ) (_hn : 0 < n) : 0 < Nat.powerfulPart n := by
  exact Finset.prod_pos fun p hp =>
    pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp |>.1)) _

/-! ## LEMMA STAR: rad(m)² · B₂(m) ≤ m²

The key integer-arithmetic lemma. For every m > 0,
  rad(m)² * powerfulPart(m) ≤ m².

Proof sketch: Write m = ∏ p^{a_p}. Then
  rad(m)² * B₂(m) = ∏_{a_p=1} p² · ∏_{a_p≥2} p^{2+a_p}
  m²              = ∏ p^{2a_p}
Compare primewise: for a_p = 1, 2 ≤ 2; for a_p ≥ 2, 2+a_p ≤ 2a_p.
-/

theorem lemma_star (m : ℕ) (hm : 0 < m) :
    Nat.rad m ^ 2 * Nat.powerfulPart m ≤ m ^ 2 := by
  -- We need to compare rad(m)² * powerfulPart(m) and m² term by term.
  have h_term_by_term :
      (Nat.primeFactors m).prod
          (fun p => p ^ 2 * if 2 ≤ m.factorization p then p ^ m.factorization p else 1) ≤
        (Nat.primeFactors m).prod (fun p => p ^ (2 * m.factorization p)) := by
    refine Finset.prod_le_prod' ?_
    intro p hp
    split_ifs with h_factorization
    · rw [← pow_add]
      exact Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).one_lt.le (by
        nlinarith)
    · interval_cases _ : m.factorization p <;> simp_all +decide [Nat.pow_succ']
      simp_all +decide [ Nat.factorization_eq_zero_iff ];
  -- By definition of $rad$ and $powerfulPart$, we can rewrite the left-hand side of the inequality.
  simp only [Nat.rad, Nat.powerfulPart, ge_iff_le] at *
  convert h_term_by_term using 1
  · simp +decide [Finset.prod_ite, Finset.prod_mul_distrib, Finset.prod_pow]
    ring_nf
    rw [← Finset.prod_filter_mul_prod_filter_not m.primeFactors
      (fun x => 2 ≤ m.factorization x)]
    ring_nf
    grind
  · conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm.ne']
    simp +decide [pow_mul', Finset.prod_pow, Finsupp.prod]

/-! ## Submultiplicativity of rad

rad(a * b) ≤ rad(a) * rad(b) for positive a, b.
This follows because primeFactors(ab) = primeFactors(a) ∪ primeFactors(b),
and the product over a union is ≤ the product of products (intersection terms ≥ 1).
-/

theorem Nat.rad_mul_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.rad (a * b) ≤ Nat.rad a * Nat.rad b := by
  unfold Nat.rad
  rw [Nat.primeFactors_mul ha hb]
  simp only [id_eq]
  rw [← Finset.prod_union_inter]
  exact le_mul_of_one_le_right (Nat.zero_le _)
    (Finset.prod_pos fun p hp =>
      Nat.pos_of_mem_primeFactors (Finset.mem_inter.mp hp |>.1))

/-! ## The abc conjecture (stated as a hypothesis) -/

/-- The abc conjecture: for every ε > 0, there exists C > 0 such that for all
coprime positive integers a, b with a + b = c, we have c ≤ C · rad(abc)^{1+ε}. -/
def ABCConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ C * ((Nat.rad (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

/-! ## Key identity and the abc application step -/

/-- (n+1)² = n(n+2) + 1, the "squaring trick" identity. -/
theorem squaring_trick (n : ℕ) : (n + 1) ^ 2 = n * (n + 2) + 1 := by ring

/-
rad(n(n+1)²(n+2)) = rad(n(n+1)(n+2)) since rad ignores exponents.
-/
theorem rad_ignore_sq (n : ℕ) (hn : 0 < n) :
    Nat.rad (n * (n + 1) ^ 2 * (n + 2)) = Nat.rad (n * (n + 1) * (n + 2)) := by
  unfold Nat.rad;
  norm_num [ Nat.primeFactors_mul, hn.ne', Nat.primeFactors_pow ]

/-! ## Main theorem: Erdős #367 (k=3), conditional on abc

**Theorem.** Assume abc. For every ε > 0, there exists C' > 0 such that for all n ≥ 1,
  B₂(n) · B₂(n+1) · B₂(n+2) ≤ C' · n^{2+ε}.

The proof proceeds in two stages:
  (1) *Integer core*: Use the squaring trick + abc to get
        (n+1)² ≤ C_ε · rad(n(n+1)(n+2))^{1+ε},
      then apply rad submultiplicativity and LEMMA STAR to bound the radical
      in terms of n and the powerful parts.
  (2) *Real-analytic rearrangement*: Rearrange the resulting inequality
      using real-valued exponents to isolate B₂(n)B₂(n+1)B₂(n+2) ≤ C'·n^{2+ε}.
-/

/-
The integer core: from abc, we get
  (n+1)² ≤ C_ε · [n(n+1)(n+2) / (B₂(n)B₂(n+1)B₂(n+2))^{1/2}]^{1+ε}.
  Stated as: (n+1)^2 * P^{(1+ε)/2} ≤ C_ε * (n(n+1)(n+2))^{1+ε},
  where P = B₂(n)·B₂(n+1)·B₂(n+2).
-/
theorem integer_core_ineq (habc : ABCConjecture) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ((n + 1 : ℕ) : ℝ) ^ 2 ≤ C *
        ((Nat.rad n : ℝ) * (Nat.rad (n + 1) : ℝ) *
          (Nat.rad (n + 2) : ℝ)) ^ (1 + ε) := by
  obtain ⟨C, hC_pos, hC⟩ := habc ε hε
  use C
  refine ⟨hC_pos, fun n hn ↦ ?_⟩
  have hC_applied :=
    hC (n * (n + 2)) 1 ((n + 1) ^ 2) (by positivity) (by norm_num)
      (by positivity) (by ring) (by simp)
  norm_num [mul_assoc] at hC_applied ⊢
  refine le_trans hC_applied ?_
  gcongr
  -- `Nat.rad_mul_le` gives the radical bound; `rad_ignore_sq` removes the square.
  have h_rad_mul :
      Nat.rad (n * (n + 2) * (n + 1) ^ 2) ≤
        Nat.rad n * Nat.rad (n + 2) * Nat.rad ((n + 1) ^ 2) := by
    convert
      Nat.rad_mul_le (n * (n + 2)) ((n + 1) ^ 2) (by positivity) (by positivity)
        |> le_trans <|
          Nat.mul_le_mul (Nat.rad_mul_le n (n + 2) (by positivity) (by positivity))
            le_rfl
      using 1
  -- Since rad((n + 1)^2) = rad(n + 1), we can simplify the inequality.
  have h_rad_sq : Nat.rad ((n + 1) ^ 2) = Nat.rad (n + 1) := by
    unfold Nat.rad; simp +decide [ Nat.primeFactors_pow ] ;
  rw [h_rad_sq] at h_rad_mul
  have h_rad_mul' :
      Nat.rad (n * ((n + 2) * (n + 1) ^ 2)) ≤
        Nat.rad n * (Nat.rad (n + 1) * Nat.rad (n + 2)) := by
    convert h_rad_mul using 1 <;> ring
  exact_mod_cast h_rad_mul'

/-! ## Helper: product of three LEMMA STAR instances (pure ℕ) -/

/-
Multiplying three instances of LEMMA STAR: if R = rad(n)·rad(n+1)·rad(n+2)
and P = B₂(n)·B₂(n+1)·B₂(n+2), then R² · P ≤ (n(n+1)(n+2))².
-/
theorem triple_lemma_star (n : ℕ) (hn : 0 < n) :
    (Nat.rad n * Nat.rad (n + 1) * Nat.rad (n + 2)) ^ 2 *
      (Nat.powerfulPart n * Nat.powerfulPart (n + 1) *
        Nat.powerfulPart (n + 2)) ≤
    (n * (n + 1) * (n + 2)) ^ 2 := by
  convert
    Nat.mul_le_mul
      (Nat.mul_le_mul (lemma_star n hn) (lemma_star (n + 1) (by linarith)))
      (lemma_star (n + 2) (by linarith))
    using 1
  all_goals ring

/-
**Real-analytic rearrangement lemma** (clearly marked).
Given the bound from the integer core and LEMMA STAR applied to each of
n, n+1, n+2, the real-exponent bookkeeping yields
  B₂(n)·B₂(n+1)·B₂(n+2) ≤ C'·n^{2+ε}.

The key steps are:
  1. rad(n+i) ≤ (n+i) / B₂(n+i)^{1/2}  (from LEMMA STAR)
  2. Substituting into the abc bound and using n(n+1)(n+2) ≤ 27n³
  3. Rearranging to isolate the product of powerful parts
  4. The resulting exponent 6 - 4/(1+ε) = 2 + 4ε/(1+ε) ≤ 2 + 4ε,
     then relabeling ε' = ε/4.
-/
theorem real_analytic_rearrangement (habc : ABCConjecture) (ε : ℝ) (hε : 0 < ε) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ, 0 < n →
      ((Nat.powerfulPart n * Nat.powerfulPart (n + 1) *
        Nat.powerfulPart (n + 2) : ℕ) : ℝ) ≤
        C' * (n : ℝ) ^ (2 + ε) := by
  obtain ⟨ C₁, hC₁, hC₁' ⟩ := integer_core_ineq habc ( ε / 4 ) ( by positivity );
  -- From triple_lemma_star, we have `R^2 * P ≤ (n(n+1)(n+2))^2`.
  have h_triple_lemma_star :
      ∀ n : ℕ, 0 < n →
        ((Nat.rad n : ℝ) * (Nat.rad (n + 1) : ℝ) *
          (Nat.rad (n + 2) : ℝ)) ^ 2 *
          (Nat.powerfulPart n * Nat.powerfulPart (n + 1) *
            Nat.powerfulPart (n + 2)) ≤
          (n * (n + 1) * (n + 2)) ^ 2 := by
    exact fun n hn => mod_cast triple_lemma_star n hn
  -- So `P^((1+ε/4)/2) ≤ C * (n(n+1)(n+2))^(1+ε/4) / (n+1)^2`.
  have h_bound :
      ∀ n : ℕ, 0 < n →
        ((Nat.powerfulPart n * Nat.powerfulPart (n + 1) *
          Nat.powerfulPart (n + 2)) : ℝ) ^ ((1 + ε / 4) / 2) ≤
          C₁ * ((n * (n + 1) * (n + 2)) ^ (1 + ε / 4)) / ((n + 1) ^ 2) := by
    intro n hn
    have h_powerful_pos :
        0 < Nat.powerfulPart n * Nat.powerfulPart (n + 1) *
          Nat.powerfulPart (n + 2) := by
      exact
        mul_pos
          (mul_pos (Nat.powerfulPart_pos _ hn)
            (Nat.powerfulPart_pos _ (Nat.succ_pos _)))
          (Nat.powerfulPart_pos _ (Nat.succ_pos _))
    have h_powerful_pos_real :
        0 < (Nat.powerfulPart n : ℝ) * (Nat.powerfulPart (n + 1) : ℝ) *
          (Nat.powerfulPart (n + 2) : ℝ) := by
      exact
        mul_pos
          (mul_pos (Nat.cast_pos.mpr (Nat.powerfulPart_pos _ hn))
            (Nat.cast_pos.mpr (Nat.powerfulPart_pos _ (Nat.succ_pos _))))
          (Nat.cast_pos.mpr (Nat.powerfulPart_pos _ (Nat.succ_pos _)))
    have h_bound_step :
        ((Nat.rad n : ℝ) * (Nat.rad (n + 1) : ℝ) *
          (Nat.rad (n + 2) : ℝ)) ^ (1 + ε / 4) ≤
          ((n * (n + 1) * (n + 2)) ^ (1 + ε / 4)) /
            ((Nat.powerfulPart n * Nat.powerfulPart (n + 1) *
              Nat.powerfulPart (n + 2)) : ℝ) ^ ((1 + ε / 4) / 2) := by
      have h_bound_step :
          ((Nat.rad n : ℝ) * (Nat.rad (n + 1) : ℝ) *
            (Nat.rad (n + 2) : ℝ)) ^ 2 ≤
            ((n * (n + 1) * (n + 2)) ^ 2) /
              ((Nat.powerfulPart n * Nat.powerfulPart (n + 1) *
                Nat.powerfulPart (n + 2)) : ℝ) := by
        rw [le_div_iff₀]
        · norm_cast at *
          simp_all +decide only [CanonicallyOrderedAdd.mul_pos]
        · exact h_powerful_pos_real
      convert
        Real.rpow_le_rpow (by positivity) h_bound_step
          (show 0 ≤ (1 + ε / 4) / 2 by positivity)
        using 1
      · rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
        ring
      · rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        ring
    rw [le_div_iff₀] at *
    · norm_cast at *
      simp_all +decide only [cast_mul, cast_pow, cast_add, cast_one, cast_ofNat]
      refine le_trans ?_ (mul_le_mul_of_nonneg_left h_bound_step hC₁.le)
      convert
        mul_le_mul_of_nonneg_right (hC₁' n hn)
          (Real.rpow_nonneg
            (show 0 ≤
              (Nat.powerfulPart n *
                (Nat.powerfulPart (n + 1) * Nat.powerfulPart (n + 2)) : ℝ) by
              positivity)
            ((1 + ε / 4) / 2))
        using 1
      · ring
      · ring
    · exact
        Real.rpow_pos_of_pos h_powerful_pos_real _
    · positivity
  -- So `P^((1+ε/4)/2) ≤ C * 27^(1+ε/4) * n^(1+3ε/4)`.
  have h_bound_simplified :
      ∀ n : ℕ, 0 < n →
        ((Nat.powerfulPart n * Nat.powerfulPart (n + 1) *
          Nat.powerfulPart (n + 2)) : ℝ) ^ ((1 + ε / 4) / 2) ≤
          C₁ * (27 ^ (1 + ε / 4)) * (n ^ (1 + 3 * ε / 4)) := by
    intros n hn_pos
    specialize h_bound n hn_pos
    have h_bound_simplified_step :
        ((n * (n + 1) * (n + 2)) : ℝ) ^ (1 + ε / 4) ≤
          (27 : ℝ) ^ (1 + ε / 4) * (n ^ (3 * (1 + ε / 4))) := by
      have h_bound_simplified_step :
          ((n * (n + 1) * (n + 2)) : ℝ) ≤ (27 : ℝ) * (n ^ 3) := by
        norm_cast
        nlinarith [pow_pos hn_pos 2]
      exact
        le_trans
          (Real.rpow_le_rpow (by positivity) h_bound_simplified_step (by positivity))
          (by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_mul (by positivity)]
            ring_nf
            norm_num)
    refine le_trans h_bound ?_
    rw [div_le_iff₀ (by positivity)]
    refine le_trans (mul_le_mul_of_nonneg_left h_bound_simplified_step <| by positivity) ?_
    rw [show (3 * (1 + ε / 4) : ℝ) = (1 + 3 * ε / 4) + 2 by ring,
      Real.rpow_add] <;> norm_num
    ring_nf
    norm_num [hn_pos]
    rw [show (3 + ε * (3 / 4) : ℝ) = (1 + ε * (3 / 4)) + 2 by ring,
      Real.rpow_add]
    · norm_num
      ring_nf
      norm_num [hn_pos]
      positivity
    · positivity
  -- So `P ≤ [C * 27^(1+ε/4)]^(2/(1+ε/4)) * n^(2(1+3ε/4)/(1+ε/4))`.
  have h_bound_final :
      ∀ n : ℕ, 0 < n →
        ((Nat.powerfulPart n * Nat.powerfulPart (n + 1) *
          Nat.powerfulPart (n + 2)) : ℝ) ≤
          (C₁ * (27 ^ (1 + ε / 4))) ^ (2 / (1 + ε / 4)) *
            (n ^ (2 * (1 + 3 * ε / 4) / (1 + ε / 4))) := by
    intro n hn
    specialize h_bound_simplified n hn
    have :
        ((Nat.powerfulPart n * Nat.powerfulPart (n + 1) *
          Nat.powerfulPart (n + 2)) : ℝ) ≤
          ((C₁ * (27 ^ (1 + ε / 4))) * (n ^ (1 + 3 * ε / 4))) ^
            (2 / (1 + ε / 4)) := by
      exact
        le_trans
          (by
            rw [← Real.rpow_mul (by positivity), div_mul_div_cancel₀ (by positivity),
              div_self (by positivity), Real.rpow_one])
          (Real.rpow_le_rpow (by positivity) h_bound_simplified (by positivity))
    convert this using 1
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
    ring
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity)]
    ring
  refine
    ⟨(C₁ * 27 ^ (1 + ε / 4)) ^ (2 / (1 + ε / 4)), by positivity, fun n hn => ?_⟩
  exact
    le_trans (mod_cast h_bound_final n hn)
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (mod_cast hn) (by
          rw [div_le_iff₀] <;> nlinarith))
        (by positivity))

/-- **Main theorem (Erdős #367, k=3 case, conditional on abc).**
For every ε > 0, there exists C' > 0 such that for all n ≥ 1,
  B₂(n) · B₂(n+1) · B₂(n+2) ≤ C' · n^{2+ε}. -/
theorem erdos_367_k3 (habc : ABCConjecture) (ε : ℝ) (hε : 0 < ε) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ, 0 < n →
      ((Nat.powerfulPart n * Nat.powerfulPart (n+1) * Nat.powerfulPart (n+2) : ℕ) : ℝ) ≤
        C' * (n : ℝ) ^ (2 + ε) :=
  real_analytic_rearrangement habc ε hε

end Erdos367

end
