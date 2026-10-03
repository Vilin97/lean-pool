/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import LeanPool.Zeta5Irrational.Growth.Constants
public import LeanPool.Zeta5Irrational.Growth.OuterPrime
public import LeanPool.Zeta5Irrational.Growth.TablePrime
public import LeanPool.Zeta5Irrational.Constants
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

import Mathlib.Algebra.Order.Floor.Semifield

/-! # Growth: the three prime ranges `K/400 < p ≤ K/20`, `K/20 < p ≤ K/3`, `K/3 < p ≤ 2h`
-/

public section

open Finset Filter

namespace Zeta5Irrational

lemma floor_Kr_div (n d : ℕ) (_hd : 0 < d) : ⌊Kr n / d⌋₊ = 40 * n / d := by
  rw [show Kr n / d = ((40 * n : ℕ) : ℝ) / (d : ℕ) by simp [Kr]]
  exact Nat.floor_div_eq_div _ _

lemma floor_Kr_outer (n : ℕ) : ⌊Kr n / (20 / 37)⌋₊ = 74 * n := by
  rw [show Kr n / (20 / 37) = ((74 * n : ℕ) : ℝ) by simp [Kr]; ring]
  exact Nat.floor_natCast _

/-! ### Bounds on the additive constants -/

lemma Bmax_le {n p Q : ℕ} (hq : 40 * n / p ≤ Q) : Bmax n p ≤ (5 * (Q : ℝ) + 10) * (3 * Q + 6) := by
  unfold Bmax ktopI
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  have hQ : ((40 * n / p : ℕ) : ℝ) ≤ Q := by exact_mod_cast hq
  have h0' : (0 : ℝ) ≤ ((3 * n / p : ℕ) : ℝ) := by positivity
  generalize ((40 * n / p : ℕ) : ℝ) = qR at hQ ⊢
  generalize ((3 * n / p : ℕ) : ℝ) = qR' at h0' ⊢
  set D := max 0 ((8 * qR + 20) / 2 - ((5 + 12 * qR' - 2 * qR) - 4) / 2) with hD
  have hD0 : 0 ≤ D := le_max_left _ _
  have hD1 : D ≤ 5 * (Q : ℝ) + 10 := max_le (by positivity) (by linarith)
  nlinarith

lemma ktop_sub_klo (n p : ℕ) :
    ((ktopI n p - kloI n p : ℤ) : ℝ) = 10 * ((40 * n / p : ℕ) : ℝ) + 26 := by
  unfold ktopI kloI
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Int.cast_neg]
  ring

lemma Ctail_le {n p : ℕ} (hp : 0 < p) (hq : 40 * n / p < 400) (hn : (n : ℝ) ≤ 10 * p) :
    Ctail n p ≤ 10 ^ 7 := by
  unfold Ctail
  rw [ktop_sub_klo]
  unfold L0I
  have hB := Bmax_le (n := n) (p := p) (Q := 399) (by omega)
  have hQ : ((40 * n / p : ℕ) : ℝ) ≤ 399 := by exact_mod_cast (show 40 * n / p ≤ 399 by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : 4 * (37 * (n : ℝ)) / p ≤ 1480 := by rw [div_le_iff₀ hpR]; linarith
  have h0 : (0 : ℝ) ≤ ((40 * n / p : ℕ) : ℝ) := by positivity
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  generalize ((40 * n / p : ℕ) : ℝ) = qR at hQ h0 ⊢
  norm_num at hB
  nlinarith

lemma Ctab_le {n p : ℕ} (hq : 40 * n / p ≤ 20) {k : ℤ} (hk1 : kloI n p ≤ k)
    (hk2 : k ≤ ktopI n p) : Ctab n p k ≤ 10 ^ 8 := by
  unfold Ctab
  have hq' : 3 * n / p ≤ 40 * n / p := Nat.div_le_div_right (by omega)
  have hk1' : -2 * ((40 * n / p : ℕ) : ℤ) - 6 ≤ k := hk1
  have hk2' : k ≤ 8 * ((40 * n / p : ℕ) : ℤ) + 20 := hk2
  have hs := sum_abs_bIn_le hq' hk1' hk2'
  have hB := Bmax_le (n := n) (p := p) (Q := 20) hq
  rw [ktop_sub_klo]
  unfold L0I
  have hQ : ((40 * n / p : ℕ) : ℝ) ≤ 20 := by exact_mod_cast hq
  have h0 : (0 : ℝ) ≤ ((40 * n / p : ℕ) : ℝ) := by positivity
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  generalize ((40 * n / p : ℕ) : ℝ) = qR at hQ h0 hs ⊢
  norm_num at hB
  nlinarith

lemma Cout_le {n p : ℕ} (hq : 40 * n / p ≤ 2) : Cout n p ≤ 10 ^ 5 := by
  unfold Cout
  have := sum_abs_bGO_le hq
  linarith

end Zeta5Irrational
