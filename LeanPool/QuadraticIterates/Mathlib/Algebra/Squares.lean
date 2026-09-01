/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.RingTheory.Int.Basic

/-!
# Lemmas about squares

Criteria for (non-)squareness in `ℚ`, `ℤ` and `ZMod m`.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

/-- If `P ≡ -Q mod m` with `Q` a unit mod `m` and `P/Q` a rational square, then `-1` is a
square mod `m`. -/
theorem ZMod.isSquare_neg_one_of_isSquare_div {P Q : ℤ} {m : ℕ} (hQne : Q ≠ 0)
    (hPnegQ : (P : ZMod m) = -(Q : ZMod m)) (hQunit : IsUnit (Q : ZMod m))
    (hsq : IsSquare ((P : ℚ) / (Q : ℚ))) : IsSquare (-1 : ZMod m) := by
  obtain ⟨s, hs⟩ := hsq
  have hQ0 : (Q : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hQne
  have hPval : (P : ℚ) = (s * s) * (Q : ℚ) := by
    field_simp at hs
    linarith [hs]
  have hsqPQ : IsSquare (P * Q : ℤ) := by
    rw [← Rat.isSquare_intCast_iff]
    push_cast
    exact ⟨s * (Q : ℚ), by rw [hPval]; ring⟩
  have hsqZ : IsSquare ((P * Q : ℤ) : ZMod m) := hsqPQ.map (Int.castRingHom (ZMod m))
  have hval : ((P * Q : ℤ) : ZMod m) = -((Q : ZMod m) * (Q : ZMod m)) := by
    push_cast
    rw [hPnegQ]; ring
  rw [hval] at hsqZ
  obtain ⟨w, hw⟩ := hsqZ
  obtain ⟨u, hu⟩ := hQunit
  refine ⟨w * (↑u⁻¹ : ZMod m), ?_⟩
  have huinv : (↑u⁻¹ : ZMod m) * (Q : ZMod m) = 1 := by
    rw [← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination ((↑u⁻¹ : ZMod m) * (↑u⁻¹ : ZMod m)) * hw
    + ((Q : ZMod m) * (↑u⁻¹ : ZMod m) + 1) * huinv

/-- A sum of two squares is never congruent to `3` modulo `4`, a square being `0` or `1`. -/
theorem Nat.not_sq_add_sq_modEq_three (x y : ℕ) : ¬x ^ 2 + y ^ 2 ≡ 3 [MOD 4] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  generalize (x : ZMod 4) = a, (y : ZMod 4) = b
  decide +revert

/-- If `d ∣ m` with `d ≡ 3 mod 4`, then `-1` is not a square in `ZMod m`. -/
theorem ZMod.not_isSquare_neg_one_of_dvd {m d : ℕ} (hdm : d ∣ m) (hd : d % 4 = 3) :
    ¬IsSquare (-1 : ZMod m) := by
  intro hsq
  obtain ⟨x, y, rfl⟩ :=
    Nat.eq_sq_add_sq_of_isSquare_mod_neg_one (ZMod.isSquare_neg_one_of_dvd hdm hsq)
  exact Nat.not_sq_add_sq_modEq_three x y hd

/-- If `4 ∣ m`, then `-1` is not a square in `ZMod m`. -/
theorem ZMod.not_isSquare_neg_one_of_four_dvd {m : ℕ} (hm : 4 ∣ m) : ¬IsSquare (-1 : ZMod m) :=
  fun hsq ↦ absurd (ZMod.isSquare_neg_one_of_dvd hm hsq) (by decide)

/-- If a family `f` is pairwise coprime on a finite set `S` and `∏_{i ∈ S} f i` is a square, then
`|f i|` is a square for every `i ∈ S`. -/
theorem Int.isSquare_abs_of_isSquare_prod_of_pairwise_isCoprime {ι : Type*} (f : ι → ℤ)
    (S : Finset ι) (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsCoprime (f i) (f j))
    (hsq : IsSquare (∏ i ∈ S, f i)) :
    ∀ i ∈ S, IsSquare |f i| := by
  classical
  intro i hi
  have hcopb : IsCoprime (f i) (∏ j ∈ S.erase i, f j) :=
    IsCoprime.prod_right fun j hj ↦
      hcop i hi j (Finset.mem_erase.mp hj).2 (Ne.symm (Finset.mem_erase.mp hj).1)
  obtain ⟨c, hc⟩ := hsq
  obtain ⟨a0, ha0⟩ := Int.sq_of_isCoprime hcopb (by rw [Finset.mul_prod_erase S f hi, hc, sq])
  refine ⟨|a0|, ?_⟩
  rcases ha0 with h | h <;> simpa [sq, abs_mul, abs_neg] using congrArg abs h

/-- A product of fixed nonzero base and varying integer exponents collapses to a single power. -/
theorem prod_zpow_eq_zpow_sum {ι : Type*} {x : ℚ} (hx : x ≠ 0) (s : Finset ι) (e : ι → ℤ) :
    ∏ p ∈ s, x ^ e p = x ^ (∑ p ∈ s, e p) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]
