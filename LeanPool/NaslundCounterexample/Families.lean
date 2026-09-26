/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.NaslundCounterexample.Lift
public import LeanPool.NaslundCounterexample.Bases

/-!
# The two families

Iterating the lift from the two bases gives a square-difference-free subset of `P_{3,n}` for
every `n` divisible by `4`:

* `A_0 = {0}` and `A_{8e+8} = L_{8e}(A_{8e})`, of size `810^e` inside `P_{3,8e}`;
* `A_4 = B_4` and `A_{8e+12} = L_{8e+4}(A_{8e+4})`, of size `27 · 810^e` inside `P_{3,8e+4}`.

Each induction step needs the lift's three conclusions at an even degree bound: `8e` and `8e + 4`
are both even, which is why the two families together cover every multiple of `4`.
-/

public section

namespace NaslundCounterexample

open Polynomial

/-- The first family: `A_0 = {0}` and `A_{8e+8} = L_{8e}(A_{8e})`. -/
noncomputable def familyFromZero : ℕ → Finset (ZMod 3)[X]
  | 0 => base0
  | e + 1 => lift (8 * e) (familyFromZero e)

/-- The second family: `A_4 = B_4` and `A_{8e+12} = L_{8e+4}(A_{8e+4})`. -/
noncomputable def familyFromFour : ℕ → Finset (ZMod 3)[X]
  | 0 => base4
  | e + 1 => lift (8 * e + 4) (familyFromFour e)

/-- The `e`-th member of the first family lies in `P_{3,8e}`. -/
theorem familyFromZero_allBelow (e : ℕ) : AllBelow (8 * e) (familyFromZero e) := by
  induction e with
  | zero => simpa [familyFromZero] using base0_allBelow
  | succ e ih =>
      have h : 8 * (e + 1) = 8 * e + 8 := by ring
      rw [h]
      simp only [familyFromZero]
      exact lift_allBelow (8 * e) (familyFromZero e) ih

/-- The `e`-th member of the first family has `810^e` elements. -/
theorem familyFromZero_card (e : ℕ) : (familyFromZero e).card = 810 ^ e := by
  induction e with
  | zero => simpa [familyFromZero] using base0_card
  | succ e ih =>
      simp only [familyFromZero]
      rw [lift_card (8 * e) (familyFromZero e) (familyFromZero_allBelow e), ih]
      ring

/-- Every member of the first family is square-difference-free. -/
theorem familyFromZero_sdf (e : ℕ) : SquareDifferenceFree (familyFromZero e) := by
  induction e with
  | zero => simpa [familyFromZero] using base0_sdf
  | succ e ih =>
      simp only [familyFromZero]
      exact lift_sdf (8 * e) (familyFromZero e) ⟨4 * e, by ring⟩ (familyFromZero_allBelow e) ih

/-- The `e`-th member of the second family lies in `P_{3,8e+4}`. -/
theorem familyFromFour_allBelow (e : ℕ) : AllBelow (8 * e + 4) (familyFromFour e) := by
  induction e with
  | zero => simpa [familyFromFour] using base4_allBelow
  | succ e ih =>
      have h : 8 * (e + 1) + 4 = (8 * e + 4) + 8 := by ring
      rw [h]
      simp only [familyFromFour]
      exact lift_allBelow (8 * e + 4) (familyFromFour e) ih

/-- The `e`-th member of the second family has `27 · 810^e` elements. -/
theorem familyFromFour_card (e : ℕ) : (familyFromFour e).card = 27 * 810 ^ e := by
  induction e with
  | zero => simpa [familyFromFour] using base4_card
  | succ e ih =>
      simp only [familyFromFour]
      rw [lift_card (8 * e + 4) (familyFromFour e) (familyFromFour_allBelow e), ih]
      ring

/-- Every member of the second family is square-difference-free. -/
theorem familyFromFour_sdf (e : ℕ) : SquareDifferenceFree (familyFromFour e) := by
  induction e with
  | zero => simpa [familyFromFour] using base4_sdf
  | succ e ih =>
      simp only [familyFromFour]
      exact lift_sdf (8 * e + 4) (familyFromFour e) ⟨4 * e + 2, by ring⟩ (familyFromFour_allBelow
          e) ih

end NaslundCounterexample
