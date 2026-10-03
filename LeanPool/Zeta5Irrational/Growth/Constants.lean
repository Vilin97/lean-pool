/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Growth.TablePrime
import Mathlib.Data.Rat.Star
import Mathlib.Data.Int.Star
public import LeanPool.Zeta5Irrational.Growth.OuterPrime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Uniform bounds for the additive constants of the per-prime bounds
-/

public section

open Finset

namespace Zeta5Irrational

lemma abs_bcoef_le (h : ℕ → ℝ) {M : ℝ} (hM : ∀ a ≤ 2, |h a| ≤ M) (i : Fin 3) :
    |bcoef h i| ≤ 2 * M := by
  have h0 := hM 0 (by norm_num); have h1 := hM 1 (by norm_num); have h2 := hM 2 (by norm_num)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans h0
  fin_cases i <;>
    simp only [bcoef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · linarith
  · exact (abs_sub _ _).trans (by linarith)
  · exact (abs_sub _ _).trans (by linarith)

lemma abs_bcoef2_le (h : ℕ → ℕ → ℝ) {M : ℝ} (hM : ∀ a ≤ 2, ∀ b ≤ 2, |h a b| ≤ M) (i j : Fin 3) :
    |bcoef (fun a => bcoef (fun b => h a b) j) i| ≤ 4 * M := by
  have :=
    abs_bcoef_le (fun a => bcoef (fun b => h a b) j) (M := 2 * M)
      (fun a ha => abs_bcoef_le (fun b => h a b) (fun b hb => hM a ha b hb) j) i
  linarith

lemma psiR_nonneg (k β : ℤ) : 0 ≤ psiR k β := by
  unfold psiR
  refine Finset.sum_nonneg fun i hi => ?_
  have := lrow_lt (Finset.mem_range.mp hi)
  linarith

lemma abs_psiR_le (k β : ℤ) : |(psiR k β : ℝ)| ≤ ((k - β + 1 : ℤ) : ℝ) ^ 2 := by
  have h1 := psiR_nonneg k β
  have h2 := psiR_le k β
  rw [abs_of_nonneg (by exact_mod_cast h1)]
  have : (psiR k β : ℝ) ≤ ((k - β + 1 : ℤ) : ℝ) ^ 2 / 8 := by exact_mod_cast h2
  nlinarith [sq_nonneg ((k - β + 1 : ℤ) : ℝ)]

/-- The inner coefficients. -/
lemma sum_abs_bIn_le {q q' : ℕ} (hq' : q' ≤ q) {k : ℤ} (hk1 : -2 * (q : ℤ) - 6 ≤ k)
    (hk2 : k ≤ 8 * (q : ℤ) + 20) : ∑ i, ∑ j, |bIn q q' k i j| ≤ 36 * (22 * (q : ℝ) + 30) ^ 2 := by
  have hM :
    ∀ a : ℕ,
      a ≤ 2 →
        ∀ b : ℕ,
          b ≤ 2 →
            |(psiR k (12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a) : ℝ)| ≤
              (22 * (q : ℝ) + 30) ^ 2 := by
    intro a ha b hb
    refine (abs_psiR_le _ _).trans ?_
    have hb' : (b : ℤ) ≤ 2 := by exact_mod_cast hb
    have ha' : (a : ℤ) ≤ 2 := by exact_mod_cast ha
    have hq'' : (q' : ℤ) ≤ q := by exact_mod_cast hq'
    have hb0 : (0 : ℤ) ≤ b := by positivity
    have ha0 : (0 : ℤ) ≤ a := by positivity
    have hq0 : (0 : ℤ) ≤ q' := by positivity
    have hbd :
      |k - (12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a) + 1| ≤ 22 * (q : ℤ) + 30 := by
      rw [abs_le]; constructor <;> linarith
    have hbdR :
      |((k - (12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a) + 1 : ℤ) : ℝ)| ≤
        22 * (q : ℝ) + 30 :=
      by exact_mod_cast hbd
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hbdR 2
  have hb := fun i j => abs_bcoef2_le _ hM i j
  calc
    ∑ i, ∑ j, |bIn q q' k i j| ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 4 * (22 * (q : ℝ) + 30) ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = 36 * (22 * (q : ℝ) + 30) ^ 2 := by simp; ring

/-- The outer coefficients. -/
lemma abs_GO_le (q a d : ℕ) : |(GO q a d : ℝ)| ≤ (2 * (q : ℝ) + a) * ((q : ℝ) + a + 3) := by
  unfold GO
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ i ∈ range (2 * q + a - 2), |min 0 ((i : ℝ) + 3 * d - (2 * (q : ℝ) + a + 4) / 2)| ≤
        ∑ _i ∈ range (2 * q + a - 2), ((q : ℝ) + a + 3) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_le]
      have : (0 : ℝ) ≤ i := by positivity
      have : (0 : ℝ) ≤ d := by positivity
      have ha : (0 : ℝ) ≤ a := by positivity
      constructor
      · have := min_le_right (0 : ℝ) ((i : ℝ) + 3 * d - ((2 * q + a : ℝ) + 4) / 2)
        have hq0 : (0 : ℝ) ≤ q := by positivity
        have :=
          le_min (show -((q : ℝ) + a + 3) ≤ 0 by linarith)
            (show -((q : ℝ) + a + 3) ≤ (i : ℝ) + 3 * d - ((2 * q + a : ℝ) + 4) / 2 by linarith)
        exact this
      · have := min_le_left (0 : ℝ) ((i : ℝ) + 3 * d - ((2 * q + a : ℝ) + 4) / 2)
        linarith [show (0 : ℝ) ≤ (q : ℝ) + a + 3 by positivity]
    _ = ((2 * q + a - 2 : ℕ) : ℝ) * ((q : ℝ) + a + 3) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (2 * (q : ℝ) + a) * ((q : ℝ) + a + 3) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : 2 * q + a - 2 ≤ 2 * q + a := Nat.sub_le _ _
      exact_mod_cast this

lemma sum_abs_bGO_le {q : ℕ} (hq : q ≤ 2) : ∑ i, ∑ j, |bGO q i j| ≤ 36 * 70 := by
  have hM : ∀ a : ℕ, a ≤ 2 → ∀ b : ℕ, b ≤ 2 → |(GO q a b : ℝ)| ≤ 70 := by
    intro a ha b _
    refine (abs_GO_le q a b).trans ?_
    have hq' : (q : ℝ) ≤ 2 := by exact_mod_cast hq
    have ha' : (a : ℝ) ≤ 2 := by exact_mod_cast ha
    have : (0 : ℝ) ≤ q := by positivity
    have : (0 : ℝ) ≤ a := by positivity
    nlinarith
  have hb := fun i j => abs_bcoef2_le _ hM i j
  calc
    ∑ i, ∑ j, |bGO q i j| ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, 4 * (70 : ℝ) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ ≤ 36 * 70 := by simp; norm_num

end Zeta5Irrational
