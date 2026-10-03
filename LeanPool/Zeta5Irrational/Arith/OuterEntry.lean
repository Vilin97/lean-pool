/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

import Mathlib.RingTheory.Int.Basic

public import LeanPool.Zeta5Irrational.Arith.TEntry
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic

/-! # Outer range: general residue and pole-value lemmas

For a numerator `tpol M = ∏_{γ ∈ M} (t + γ²)`:
* `res_tpol` : `res K (tpol M) j = ∏_γ (γ² - j²) / ∏_{i ≠ j} (i² - j²)`;
* valuation bounds for residues and pole values;
* `PV_congr` : `poleValue (p - c) ≡ poleValue c (mod p)`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

lemma eval_tpol (M : Multiset ℤ) (x : ℚ) :
    (tpol M).eval x = (M.map fun γ : ℤ => x + (γ : ℚ) ^ 2).prod := by
  unfold tpol
  rw [eval_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun γ _ => by simp

lemma res_tpol {K j : ℕ} (hj : j ∈ Icc 1 K) (M : Multiset ℤ) :
    res K (tpol M) j =
      (M.map fun γ : ℤ => (γ : ℚ) ^ 2 - (j : ℚ) ^ 2).prod /
        ∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) := by
  unfold res
  rw [eval_derivative_D hj, eval_tpol]
  congr 1
  congr 1
  exact Multiset.map_congr rfl fun γ _ => by ring

lemma res_tpol_eq_zero {K j : ℕ} (hj : j ∈ Icc 1 K) {M : Multiset ℤ} {γ : ℤ} (hγ : γ ∈ M)
    (h : γ ^ 2 = (j : ℤ) ^ 2) : res K (tpol M) j = 0 := by
  rw [res_tpol hj, Multiset.prod_eq_zero, zero_div]
  rw [Multiset.mem_map]
  exact ⟨γ, hγ, by rw [sub_eq_zero]; exact_mod_cast h⟩

/-- The numerator valuation: at least the number of roots `γ` with `γ² ≡ j²`. -/
lemma VG_prod_sq_sub (M : Multiset ℤ) (j : ℤ) :
    VG p ((M.map fun γ : ℤ => (γ : ℚ) ^ 2 - (j : ℚ) ^ 2).prod)
      ((M.filter fun γ : ℤ => ((γ : ZMod p)) ^ 2 = (j : ZMod p) ^ 2).card) := by
  induction M using Multiset.induction_on with
  | empty => right; simp
  | cons a M ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.filter_cons]
    split_ifs with h
    · rw [Multiset.card_add, Multiset.card_singleton]
      have h1 : VG p ((a : ℚ) ^ 2 - (j : ℚ) ^ 2) 1 := by
        have :=
          VG_int_one (p := p) (z := a ^ 2 - j ^ 2)
            (by rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h, sub_self])
        simpa using this
      convert h1.mul ih using 1; push_cast; ring
    · rw [zero_add]
      have h1 : VG p ((a : ℚ) ^ 2 - (j : ℚ) ^ 2) 0 := by
        have := VG.intCast (p := p) (a ^ 2 - j ^ 2); push_cast at this; exact this
      simpa using h1.mul ih

/-- The denominator valuation for a nonzero class: at most the number of other nodes in the
class (each factor has valuation `≤ 1`). -/
lemma padicValRat_den_le (hp3 : 3 ≤ p) {K j : ℕ} (hj : j ∈ Icc 1 K) (hK : 2 * K < p ^ 2)
    (hj0 : ¬(p : ℤ) ∣ (j : ℤ)) :
    (padicValRat p (∏ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2)) : ℚ) ≤
      (((Icc 1 K).erase j).filter fun i : ℕ =>
          ((i : ℤ) : ZMod p) ^ 2 = ((j : ℤ) : ZMod p) ^ 2).card := by
  have hne : ∀ i ∈ (Icc 1 K).erase j, ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) ≠ 0 := by
    intro i hi
    have hij := (Finset.mem_erase.mp hi).1
    have : (i : ℚ) ≠ j := by exact_mod_cast hij
    intro h
    have h2 : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact this (by linarith)
    · have : (0 : ℚ) ≤ i := by positivity
      have : (1 : ℚ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      linarith
  rw [padicValRat_finset_prod _ _ hne]
  push_cast
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_erase.mp hi
  have hiK := (Finset.mem_Icc.mp hi'.2)
  have hjK := (Finset.mem_Icc.mp hj)
  rw [show ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) = (((i - j) * (i + j) : ℤ) : ℚ) by push_cast; ring]
  split_ifs with hc
  · -- exactly one factor divisible by `p`, with valuation `≤ 1`
    rw [padicValRat.of_int]
    have hz : ((i : ℤ) - j) * ((i : ℤ) + j) ≠ 0 := by
      have := hne i hi
      intro h; apply this;
      rw [show ((i : ℚ) ^ 2 - (j : ℚ) ^ 2) = (((i - j) * (i + j) : ℤ) : ℚ) by
      push_cast; ring, h];
      simp
    have hz1 := (mul_ne_zero_iff.mp hz).1
    have hz2 := (mul_ne_zero_iff.mp hz).2
    rw [padicValInt.mul hz1 hz2]
    have hle : ∀ z : ℤ, z ≠ 0 → |z| ≤ 2 * K → padicValInt p z ≤ 1 := by
      intro z hz0 hzK
      have :=
        padicValRat_int_le_one (p := p) (z := z)
          (fun hd => by
            have h1 := Int.natAbs_dvd_natAbs.mpr hd
            rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
            have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hz0) h1
            have h3 : (z.natAbs : ℤ) ≤ 2 * K := by rw [Int.natCast_natAbs]; exact hzK
            omega)
      rw [padicValRat.of_int] at this; exact_mod_cast this
    have hb1 : padicValInt p ((i : ℤ) - j) ≤ 1 :=
      hle _ hz1 (by rw [abs_le]; constructor <;> omega)
    have hb2 : padicValInt p ((i : ℤ) + j) ≤ 1 :=
      hle _ hz2 (by rw [abs_le]; constructor <;> omega)
    have hp2 : ¬((p : ℤ) ∣ ((i : ℤ) - j) ∧ (p : ℤ) ∣ ((i : ℤ) + j)) := by
      rintro ⟨h1, h2⟩
      apply hj0
      have h3 : (p : ℤ) ∣ 2 * (j : ℤ) := by
        have := dvd_sub h2 h1;
        rw [show (i : ℤ) + j - (i - j) = 2 * j by ring] at this; exact this
      rcases (Int.Prime.dvd_mul' hp.out h3) with h4 | h4
      · exfalso
        have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h4
        omega
      · exact h4
    by_cases hd1 : (p : ℤ) ∣ ((i : ℤ) - j)
    · have hd2 : ¬(p : ℤ) ∣ ((i : ℤ) + j) := fun h => hp2 ⟨hd1, h⟩
      have : padicValInt p ((i : ℤ) + j) = 0 := padicValInt.eq_zero_of_not_dvd hd2
      rw [this]; push_cast;
      linarith [(show (padicValInt p ((i : ℤ) - j) : ℚ) ≤ 1 by exact_mod_cast hb1)]
    · have : padicValInt p ((i : ℤ) - j) = 0 := padicValInt.eq_zero_of_not_dvd hd1
      rw [this]; push_cast;
      linarith [(show (padicValInt p ((i : ℤ) + j) : ℚ) ≤ 1 by exact_mod_cast hb2)]
  · have hnd : ¬(p : ℤ) ∣ ((i : ℤ) - j) * ((i : ℤ) + j) := by
      intro hd
      apply hc
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
      push_cast at hd
      linear_combination hd
    rw [padicValRat_int_eq_zero hnd]; simp

end Zeta5Irrational
