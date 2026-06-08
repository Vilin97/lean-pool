/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/

import Mathlib.Order.Filter.Finite
import LeanPool.Redhill.Common.PairwiseCoprime
import LeanPool.Redhill.General.Defs

/-!
# Coprimality proof for the general case

In the paper it is claimed in the proof of coprimality of `a₃` and `a₄` over there –
`isCoprime_natAdd_two_three` here – that "as 101 is prime and `10y - 1 > 101`,
they have no common factor". This is not always true even with the paper's definition of `y`,
but can be made so by adding 101 to the factors of `y`.
-/

namespace GeneralCase

open Fin Filter IsCoprime

variable {n : ℕ} {F : Finset ℕ}

lemma even_Y : Even (Y F) := even_iff_two_dvd.mpr (dvd_mul_of_dvd_left (by decide) _)
lemma three_dvd_Y : 3 ∣ Y F := dvd_mul_of_dvd_left (by decide) _
lemma ten_dvd_Y : 10 ∣ Y F := dvd_mul_of_dvd_left (by decide) _
lemma eleven_dvd_Y : 11 ∣ Y F := dvd_mul_of_dvd_left (by decide) _
lemma hundredone_dvd_Y : 101 ∣ Y F := dvd_mul_of_dvd_left (by decide) _
lemma odd_X {h : ℕ} : Odd (X F h) := even_Y.add_one.pow

section Helpers

open Nat

lemma X_coprime_Y {h : ℕ} : (X F h).Coprime (Y F) := by
  apply Coprime.pow_left
  simp

lemma Yp1_coprime_10Yp1 : (Y F + 1).Coprime (10 * Y F + 1) := by
  rw [show 10 * Y F + 1 = Y F + 1 + 3 ^ 2 * Y F by lia, coprime_self_add_right]
  refine (Coprime.pow_right _ ?_).mul_right (by simp)
  rw [coprime_comm, prime_three.coprime_iff_not_dvd]
  grind [three_dvd_Y]

lemma Yp1_coprime_10Ym1 : (Y F + 1).Coprime (10 * Y F - 1) := by
  rw [← coprime_self_add_right, show Y F + 1 + (10 * Y F - 1) = 11 * Y F by grind [Y_pos]]
  refine Coprime.mul_right ?_ (by simp)
  rw [coprime_comm, prime_eleven.coprime_iff_not_dvd]
  grind [eleven_dvd_Y]

lemma Ym1_coprime_10Yp1 : (Y F - 1).Coprime (10 * Y F + 1) := by
  rw [← coprime_self_add_right, show Y F - 1 + (10 * Y F + 1) = 11 * Y F by grind [Y_pos]]
  refine Coprime.mul_right ?_ ?_
  · rw [coprime_comm, prime_eleven.coprime_iff_not_dvd]
    grind [Y_pos, eleven_dvd_Y]
  · rw [← sub_one_add_one Y_pos.ne']
    simp

lemma Ym1_coprime_10Ym1 : (Y F - 1).Coprime (10 * Y F - 1) := by
  rw [show 10 * Y F - 1 = Y F - 1 + 3 ^ 2 * Y F by lia, coprime_self_add_right]
  refine (Coprime.pow_right _ ?_).mul_right ?_
  · rw [coprime_comm, prime_three.coprime_iff_not_dvd]
    grind [Y_pos, three_dvd_Y]
  · rw [← sub_one_add_one Y_pos.ne']
    simp

/-- Given `Q` independent of `h` with `Y F + 1` coprime to `Q F`,
`X F h ≡ 1` mod `Q F` for sufficiently large `h`. -/
lemma eventually_X_modEq_one_of_coprime (Q : Finset ℕ → ℕ) (hQ : (Y F + 1).Coprime (Q F)) :
    ∀ᶠ h in atTop, X F h ≡ 1 [MOD Q F] := by
  refine eventually_atTop.mpr ⟨φ (Q F), fun k hk ↦ ?_⟩
  have meq := ModEq.pow_totient hQ
  have tpos : 0 < φ (Q F) := by
    rw [totient_pos]
    contrapose! hQ
    rw [le_zero] at hQ
    rw [hQ, Nat.gcd_zero_right]
    grind [Y_pos]
  obtain ⟨d, hd⟩ := dvd_factorial tpos hk
  replace meq := meq.pow d
  rwa [← pow_mul, ← hd, one_pow] at meq

lemma eventually_X_modEq_10Yp1 : ∀ᶠ h in atTop, X F h ≡ 1 [MOD 10 * Y F + 1] :=
  eventually_X_modEq_one_of_coprime (10 * Y · + 1) Yp1_coprime_10Yp1

lemma eventually_X_modEq_10Ym1 : ∀ᶠ h in atTop, X F h ≡ 1 [MOD 10 * Y F - 1] :=
  eventually_X_modEq_one_of_coprime (10 * Y · - 1) Yp1_coprime_10Ym1

/-- In this file's context "rough" means "having only large ODD prime factors".
All elements of `tup n F h` are odd by construction, except `natAdd n 0` when `n` is odd,
so the factor 2 is not an obstacle to pairwise coprimality. -/
lemma coprime_of_rough (Q K L : Finset ℕ → ℕ) (hQ : ∀ {d}, 3 ≤ d → d ∣ Q F → L F < d)
    (hK : Odd (K F)) (hL : K F ≤ L F) : (K F).Coprime (Q F) := by
  by_contra h
  rw [Prime.not_coprime_iff_dvd] at h
  obtain ⟨p, pp, dp₁, dp₂⟩ := h
  have lp : 3 ≤ p := by
    contrapose dp₁
    rw [← pp.odd_iff, not_odd_iff_even, pp.even_iff] at dp₁
    subst dp₁
    rwa [← even_iff_two_dvd, not_even_iff_odd]
  specialize hQ lp dp₂
  replace dp₁ := le_of_dvd (by grind [hK.pos]) dp₁
  lia

end Helpers

lemma isCoprime_natAdd_four_five {h : ℕ} :
    IsCoprime (tup n F h (natAdd n 4)) (tup n F h (natAdd n 5)) := by
  rw [tup_natAdd_four, tup_natAdd_five]
  apply (pow_left ?_).pow_right.neg_right
  rw [← add_mul_right_left_iff (z := -1)]
  ring_nf
  apply (mul_left ?_ ?_).neg_left
  · rw [← add_mul_left_right_iff (z := -1), mul_neg_one, add_neg_cancel_right,
      Nat.isCoprime_iff_coprime]
    exact X_coprime_Y.symm
  · rw [← Nat.cast_add, ← Nat.cast_two, Nat.isCoprime_iff_coprime, Nat.coprime_two_left]
    exact odd_X.add_even even_Y

lemma isCoprime_natAdd_three_four :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 3)) (tup n F h (natAdd n 4)) := by
  filter_upwards [eventually_X_modEq_10Ym1 (F := F)] with h hx
  simp_rw [tup_natAdd_three, tup_natAdd_four]
  apply (mul_left ?_ (pow_left ?_)).pow_right
  · rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm] at hx
    obtain ⟨m, hm⟩ := hx
    rw [sub_eq_iff_eq_add] at hm
    rw [show (10 * Y F - 1 : ℤ) = (10 * Y F - 1 : ℕ) by grind [Y_pos], hm, add_sub_assoc,
      mul_add_left_right_iff, show (1 - Y F : ℤ) = -(Y F - 1 : ℕ) by grind [Y_pos], neg_right_iff,
      Nat.isCoprime_iff_coprime]
    exact Ym1_coprime_10Ym1.symm
  · rw [← add_mul_left_right_iff (z := -1), mul_neg_one, ← sub_eq_add_neg, sub_sub_cancel_left,
      neg_right_iff, Nat.isCoprime_iff_coprime]
    exact X_coprime_Y

lemma isCoprime_natAdd_three_five :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 3)) (tup n F h (natAdd n 5)) := by
  filter_upwards [eventually_X_modEq_10Ym1 (F := F)] with h hx
  rw [tup_natAdd_three, tup_natAdd_five]
  apply (mul_left ?_ (pow_left ?_)).pow_right.neg_right
  · rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm] at hx
    obtain ⟨m, hm⟩ := hx
    rw [sub_eq_iff_eq_add] at hm
    rw [show (10 * Y F - 1 : ℤ) = (10 * Y F - 1 : ℕ) by grind [Y_pos], hm, add_assoc,
      mul_add_left_right_iff, add_comm, ← Nat.cast_add_one, Nat.isCoprime_iff_coprime]
    exact Yp1_coprime_10Ym1.symm
  · rw [← add_mul_left_right_iff (z := -1), mul_neg_one, ← sub_eq_add_neg, add_sub_cancel_left,
      Nat.isCoprime_iff_coprime]
    exact X_coprime_Y

lemma isCoprime_natAdd_two_three :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 2)) (tup n F h (natAdd n 3)) := by
  filter_upwards [eventually_X_modEq_10Ym1 (F := F)] with h hx
  rw [tup_natAdd_two, tup_natAdd_three]
  apply (mul_right ?_ (pow_right ?_)).pow_left
  · have mcast : (10 * Y F - 1 : ℤ) = (10 * Y F - 1 : ℕ) := by grind [Y_pos]
    replace hx := hx.pow 2
    rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, one_pow, Nat.cast_one, dvd_sub_comm] at hx
    obtain ⟨m, hm⟩ := hx
    rw [sub_eq_iff_eq_add, Nat.cast_pow] at hm
    rw [hm, add_assoc, ← mcast, mul_add_left_left_iff,
      show 1 + 10 * (Y F : ℤ) ^ 3 = Y F ^ 2 + 1 + (10 * Y F - 1) * Y F ^ 2 by ring,
      add_mul_left_left_iff, ← add_mul_right_left_iff (z := 10 * (Y F : ℤ) + 1),
      ← mul_self_sub_one, ← sq, add_add_sub_cancel, mul_pow, ← one_add_mul]
    apply mul_left ?_ (pow_left ?_)
    · rw [mcast, show (1 + 10 ^ 2 : ℤ) = (101 : ℕ) by rfl, Nat.isCoprime_iff_coprime,
        (show Nat.Prime 101 by decide).coprime_iff_not_dvd]
      grind [hundredone_dvd_Y]
    · rw [sub_eq_add_neg, mul_add_right_right_iff, neg_right_iff]
      exact isCoprime_one_right
  · rw [sq, mul_add_right_left_iff, X, Nat.cast_pow]
    apply (mul_left ?_ (pow_left ?_)).pow_right
    · rw [Nat.cast_add_one]
      exact add_one_right_of_dvd (mod_cast ten_dvd_Y)
    · rw [Nat.isCoprime_iff_coprime]
      simp

lemma isCoprime_natAdd_two_sq_sub_sq :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 2)) (X F h ^ 2 - Y F ^ 2) := by
  filter_upwards [eventually_X_modEq_10Yp1 (F := F)] with h hx
  rw [tup_natAdd_two]
  apply pow_left
  rw [← add_mul_left_left_iff (z := -1), mul_neg_one, neg_sub, ← add_sub_assoc, add_assoc,
    add_sub_cancel_left, pow_succ', ← mul_assoc, ← add_one_mul, sq_sub_sq]
  refine mul_left ?_ (pow_left (mul_right ?_ ?_))
  · rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm] at hx
    obtain ⟨m, hm⟩ := hx
    rw [sub_eq_iff_eq_add] at hm
    rw [show (10 * Y F + 1 : ℤ) = (10 * Y F + 1 : ℕ) by lia, hm]
    apply mul_right
    · rw [add_assoc, mul_add_left_right_iff, add_comm (1 : ℤ), ← Nat.cast_add_one,
        Nat.isCoprime_iff_coprime]
      exact Yp1_coprime_10Yp1.symm
    · rw [add_sub_assoc, mul_add_left_right_iff,
        show (1 - Y F : ℤ) = -(Y F - 1 : ℕ) by grind [Y_pos], neg_right_iff,
        Nat.isCoprime_iff_coprime]
      exact Ym1_coprime_10Yp1.symm
  · rw [← add_mul_left_right_iff (z := -1), mul_neg_one, add_neg_cancel_right,
      Nat.isCoprime_iff_coprime]
    exact X_coprime_Y.symm
  · rw [← add_mul_left_right_iff (z := 1), mul_one, sub_add_cancel, Nat.isCoprime_iff_coprime]
    exact X_coprime_Y.symm

lemma isCoprime_natAdd_two_four :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 2)) (tup n F h (natAdd n 4)) := by
  filter_upwards [isCoprime_natAdd_two_sq_sub_sq (n := n) (F := F)] with h hx
  rw [sq_sub_sq, mul_right_iff] at hx
  rw [tup_natAdd_four]
  exact hx.2.pow_right

lemma isCoprime_natAdd_two_five :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 2)) (tup n F h (natAdd n 5)) := by
  filter_upwards [isCoprime_natAdd_two_sq_sub_sq (n := n) (F := F)] with h hx
  rw [sq_sub_sq, mul_right_iff] at hx
  rw [tup_natAdd_five]
  exact hx.1.pow_right.neg_right

lemma isCoprime_natAdd_five_of_rough
    {Q : Finset ℕ → ℕ} (hQ : ∀ {d}, 3 ≤ d → d ∣ Q F → Y F + 1 < d) :
    ∀ᶠ h in atTop, IsCoprime (Q F : ℤ) (tup n F h (natAdd n 5)) := by
  replace hQ := coprime_of_rough Q (Y · + 1) (Y · + 1) hQ (by grind [even_Y]) le_rfl
  filter_upwards [eventually_X_modEq_one_of_coprime Q hQ] with h hx
  rw [tup_natAdd_five]
  apply (pow_right ?_).neg_right
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm] at hx
  obtain ⟨m, hm⟩ := hx
  rw [sub_eq_iff_eq_add] at hm
  rw [hm, add_assoc, mul_add_left_right_iff, add_comm, ← Nat.cast_add_one,
    Nat.isCoprime_iff_coprime]
  exact hQ.symm

lemma isCoprime_natAdd_four_of_rough
    {Q : Finset ℕ → ℕ} (hQ : ∀ {d}, 3 ≤ d → d ∣ Q F → Y F + 1 < d) :
    ∀ᶠ h in atTop, IsCoprime (Q F : ℤ) (tup n F h (natAdd n 4)) := by
  have cpQ := coprime_of_rough Q (Y · + 1) (Y · + 1) hQ (by grind [even_Y]) le_rfl
  filter_upwards [eventually_X_modEq_one_of_coprime Q cpQ] with h hx
  rw [tup_natAdd_four]
  apply pow_right ?_
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm] at hx
  obtain ⟨m, hm⟩ := hx
  rw [sub_eq_iff_eq_add] at hm
  rw [hm, add_sub_assoc, mul_add_left_right_iff, ← neg_sub, neg_right_iff, ← Nat.cast_pred Y_pos,
    Nat.isCoprime_iff_coprime]
  exact (coprime_of_rough Q (Y · - 1) (Y · + 1) hQ (by grind [Y_pos, even_Y]) (by lia)).symm

lemma isCoprime_natAdd_three_of_rough
    {Q : Finset ℕ → ℕ} (hQ : ∀ {d}, 3 ≤ d → d ∣ Q F → 10 * Y F - 1 < d) :
    ∀ᶠ h in atTop, IsCoprime (Q F : ℤ) (tup n F h (natAdd n 3)) := by
  have cpQ := coprime_of_rough Q (Y · + 1) (10 * Y · - 1) hQ (by grind [even_Y]) (by grind [Y_pos])
  filter_upwards [eventually_X_modEq_one_of_coprime Q cpQ] with h hx
  rw [tup_natAdd_three]
  apply mul_right ?_ (pow_right ?_)
  · rw [show (10 * Y F - 1 : ℤ) = (10 * Y F - 1 : ℕ) by grind [Y_pos], Nat.isCoprime_iff_coprime]
    exact (coprime_of_rough Q (10 * Y · - 1) (10 * Y · - 1) hQ (by grind [Y_pos]) le_rfl).symm
  · rw [← mul_one (X F h)] at hx
    replace hx := (Nat.coprime_of_mul_modEq_one _ hx).symm
    rwa [Nat.isCoprime_iff_coprime]

lemma isCoprime_natAdd_two_of_rough
    {Q : Finset ℕ → ℕ} (hQ : ∀ {d}, 3 ≤ d → d ∣ Q F → 10 * Y F ^ 3 + 1 < d) :
    ∀ᶠ h in atTop, IsCoprime (Q F : ℤ) (tup n F h (natAdd n 2)) := by
  have prele : Y F + 1 ≤ 10 * Y F ^ 3 + 1 := by
    nth_rw 1 [show Y F = 1 * Y F ^ 1 by simp]
    gcongr <;> grind [Y_pos]
  have cpQ := coprime_of_rough Q (Y · + 1) (10 * Y · ^ 3 + 1) hQ (by grind [even_Y]) prele
  filter_upwards [eventually_X_modEq_one_of_coprime Q cpQ] with h hx
  rw [tup_natAdd_two]
  apply pow_right ?_
  replace hx := hx.pow 2
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, one_pow, Nat.cast_one, Nat.cast_pow,
    dvd_sub_comm] at hx
  obtain ⟨m, hm⟩ := hx
  rw [sub_eq_iff_eq_add] at hm
  rw [hm, add_assoc, mul_add_left_right_iff, add_comm]
  norm_cast
  exact (coprime_of_rough Q (10 * Y · ^ 3 + 1) (10 * Y · ^ 3 + 1) hQ (by grind) le_rfl).symm

lemma tenY3p1_le_U : 10 * Y F ^ 3 + 1 ≤ U n F :=
  calc
    _ ≤ 11 * Y F ^ 3 := by
      rw [show 11 = 10 + 1 by rfl, add_one_mul]
      exact add_le_add_right (Nat.one_le_pow _ _ Y_pos) _
    _ ≤ (100 * Y F - 2) * Y F ^ 5 := by gcongr <;> grind [Y_pos]
    _ ≤ _ := by simp [U]

lemma tenYm1_le_U : 10 * Y F - 1 ≤ U n F :=
  calc
    _ ≤ 10 * Y F + 1 := by lia
    _ ≤ 10 * Y F ^ 3 + 1 := by gcongr; exact Nat.le_pow zero_lt_three
    _ ≤ _ := tenY3p1_le_U

lemma Yp1_le_U : Y F + 1 ≤ U n F :=
  calc
    _ ≤ 10 * Y F + 1 := by lia
    _ ≤ 10 * Y F ^ 3 + 1 := by gcongr; exact Nat.le_pow zero_lt_three
    _ ≤ _ := tenY3p1_le_U

lemma isCoprime_natAdd_natAdd {i j : Fin 6} (hij : i < j) :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n i)) (tup n F h (natAdd n j)) := by
  fin_cases i <;> simp only [reduceFinMk] at *
  · simp_rw [tup_natAdd_zero]
    obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by lia
    · simp_rw [tup_natAdd_one, neg_right_iff, Nat.isCoprime_iff_coprime]
      exact .of_forall fun _ ↦ VWPair.of_coprime U_pos le_rfl
    · refine isCoprime_natAdd_two_of_rough (Q := fun F ↦ (VW n F).v) fun {f} lf df ↦ ?_
      have := (VW n F).not_dvd
      contrapose! df
      exact (this _ (Finset.mem_Icc.mpr ⟨lf, df.trans tenY3p1_le_U⟩)).1
    · refine isCoprime_natAdd_three_of_rough (Q := fun F ↦ (VW n F).v) fun {f} lf df ↦ ?_
      have := (VW n F).not_dvd
      contrapose! df
      exact (this _ (Finset.mem_Icc.mpr ⟨lf, df.trans tenYm1_le_U⟩)).1
    · refine isCoprime_natAdd_four_of_rough (Q := fun F ↦ (VW n F).v) fun {f} lf df ↦ ?_
      have := (VW n F).not_dvd
      contrapose! df
      exact (this _ (Finset.mem_Icc.mpr ⟨lf, df.trans Yp1_le_U⟩)).1
    · refine isCoprime_natAdd_five_of_rough (Q := fun F ↦ (VW n F).v) fun {f} lf df ↦ ?_
      have := (VW n F).not_dvd
      contrapose! df
      exact (this _ (Finset.mem_Icc.mpr ⟨lf, df.trans Yp1_le_U⟩)).1
  · simp_rw [tup_natAdd_one, neg_left_iff]
    obtain rfl | rfl | rfl | rfl : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by lia
    · refine isCoprime_natAdd_two_of_rough (Q := fun F ↦ (VW n F).w) fun {f} lf df ↦ ?_
      have := (VW n F).not_dvd
      contrapose! df
      exact (this _ (Finset.mem_Icc.mpr ⟨lf, df.trans tenY3p1_le_U⟩)).2
    · refine isCoprime_natAdd_three_of_rough (Q := fun F ↦ (VW n F).w) fun {f} lf df ↦ ?_
      have := (VW n F).not_dvd
      contrapose! df
      exact (this _ (Finset.mem_Icc.mpr ⟨lf, df.trans tenYm1_le_U⟩)).2
    · refine isCoprime_natAdd_four_of_rough (Q := fun F ↦ (VW n F).w) fun {f} lf df ↦ ?_
      have := (VW n F).not_dvd
      contrapose! df
      exact (this _ (Finset.mem_Icc.mpr ⟨lf, df.trans Yp1_le_U⟩)).2
    · refine isCoprime_natAdd_five_of_rough (Q := fun F ↦ (VW n F).w) fun {f} lf df ↦ ?_
      have := (VW n F).not_dvd
      contrapose! df
      exact (this _ (Finset.mem_Icc.mpr ⟨lf, df.trans Yp1_le_U⟩)).2
  · obtain rfl | rfl | rfl : j = 3 ∨ j = 4 ∨ j = 5 := by lia
    exacts [isCoprime_natAdd_two_three, isCoprime_natAdd_two_four, isCoprime_natAdd_two_five]
  · obtain rfl | rfl : j = 4 ∨ j = 5 := by lia
    exacts [isCoprime_natAdd_three_four, isCoprime_natAdd_three_five]
  · obtain rfl : j = 5 := by lia
    exact .of_forall fun _ ↦ isCoprime_natAdd_four_five
  · lia

lemma primeChain_mem_Icc {i : Fin n} : primeChain (100 * Y F ^ 6) i.1 ∈ Finset.Icc 3 (U n F) := by
  refine Finset.mem_Icc.mpr ⟨primeChain_gt.le.trans' ?_, le_add_self.trans' ?_⟩
  · calc
      _ ≤ 100 * 1 := by decide
      _ ≤ _ := by gcongr; exact Nat.one_le_pow _ _ Y_pos
  · exact Finset.single_le_sum_of_canonicallyOrdered (by simp_all)

lemma isCoprime_castAdd_natAdd {i : Fin n} {j : Fin 6} :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (castAdd 6 i)) (tup n F h (natAdd n j)) := by
  simp_rw [tup_castAdd]
  fin_cases j <;> simp only [reduceFinMk]
  · refine .of_forall fun h ↦ ?_
    rw [tup_natAdd_zero, Nat.isCoprime_iff_coprime, prime_primeChain.coprime_iff_not_dvd]
    exact ((VW n F).not_dvd _ primeChain_mem_Icc).1
  · refine .of_forall fun h ↦ ?_
    rw [tup_natAdd_one, neg_right_iff, Nat.isCoprime_iff_coprime,
      prime_primeChain.coprime_iff_not_dvd]
    exact ((VW n F).not_dvd _ primeChain_mem_Icc).2
  · refine isCoprime_natAdd_two_of_rough
      (Q := fun F ↦ primeChain (100 * Y F ^ 6) _) fun {f} lf df ↦ ?_
    rw [Nat.dvd_prime_two_le prime_primeChain (by lia)] at df
    subst f
    apply primeChain_gt.trans_le'
    calc
      _ ≤ 11 * Y F ^ 3 := by
        rw [show 11 = 10 + 1 by rfl, add_one_mul]
        exact add_le_add_right (Nat.one_le_pow _ _ Y_pos) _
      _ ≤ _ := by gcongr <;> grind [Y_pos]
  · refine isCoprime_natAdd_three_of_rough
      (Q := fun F ↦ primeChain (100 * Y F ^ 6) _) fun {f} lf df ↦ ?_
    rw [Nat.dvd_prime_two_le prime_primeChain (by lia)] at df
    subst f
    apply primeChain_gt.trans_le'
    calc
      _ ≤ 11 * Y F ^ 1 := by grind [Y_pos]
      _ ≤ _ := by gcongr <;> grind [Y_pos]
  · refine isCoprime_natAdd_four_of_rough
      (Q := fun F ↦ primeChain (100 * Y F ^ 6) _) fun {f} lf df ↦ ?_
    rw [Nat.dvd_prime_two_le prime_primeChain (by lia)] at df
    subst f
    apply primeChain_gt.trans_le'
    calc
      _ ≤ 2 * Y F ^ 1 := by grind [Y_pos]
      _ ≤ _ := by gcongr <;> grind [Y_pos]
  · refine isCoprime_natAdd_five_of_rough
      (Q := fun F ↦ primeChain (100 * Y F ^ 6) _) fun {f} lf df ↦ ?_
    rw [Nat.dvd_prime_two_le prime_primeChain (by lia)] at df
    subst f
    apply primeChain_gt.trans_le'
    calc
      _ ≤ 2 * Y F ^ 1 := by grind [Y_pos]
      _ ≤ _ := by gcongr <;> grind [Y_pos]

theorem pairwiseCoprime_tup : ∀ᶠ h in atTop, PairwiseCoprime (tup n F h) := by
  have cp₂' := @isCoprime_castAdd_natAdd n F
  have cp₃' (i j) (hij : i < j) := @isCoprime_natAdd_natAdd n F _ _ hij
  simp_rw [← eventually_all] at cp₂' cp₃'
  filter_upwards [cp₂', cp₃'] with h cp₂ cp₃
  refine Pairwise.of_lt (fun _ _ h ↦ h.symm) fun i j hij ↦ ?_
  cases i using Fin.addCases <;> cases j using Fin.addCases
  case left.left i j =>
    simp only [tup_castAdd, Nat.isCoprime_iff_coprime]
    rw [Nat.coprime_primes prime_primeChain prime_primeChain]
    exact (strictMono_primeChain hij).ne
  case left.right i j => exact cp₂ i j
  case right.left i j => grind
  case right.right i j => exact cp₃ i j (by simpa using hij)

end GeneralCase
