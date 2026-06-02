/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic.Common
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Data.Nat.ModEq

/-!
# LeanPool.EcTateLean.Algebra.EllipticCurve.Kronecker

Imported Lean Pool material for `LeanPool.EcTateLean.Algebra.EllipticCurve.Kronecker`.
-/

open Nat

section Obvious


lemma div_succ_le_succ_div (m n : ℕ) : succ m / succ n ≤ succ (m / succ n) := by
  rw [Nat.succ_div]
  split
  · rw [succ_eq_add_one]
  · rw [add_zero]
    exact le_succ (m / succ n)

lemma div2_succ_succ_eq_succ_div2 (n : ℕ) : succ (succ n) / 2 = succ (n / 2) := by
  rw [succ_eq_add_one, succ_eq_add_one, add_assoc, add_div_eq_of_add_mod_lt,
    Nat.div_self (zero_lt_succ 1)]
  rw [mod_self, add_zero]
  exact mod_lt n (zero_lt_succ 1)

end Obvious

namespace Int

lemma div2_lt_self {x : ℕ} (h : 0 < x) : x / 2 < x :=
  Nat.div_lt_self h (Nat.lt_succ_self 1) -- todo why nat needed
lemma div2_succ_le_self (x : ℕ) : Nat.succ x / 2 ≤ x := by
  cases x with
  | zero => simp
  | succ x =>
    exact (div_succ_le_succ_div (Nat.succ x) 1).trans (succ_le_of_lt (div2_lt_self (succ_pos x)))


/-- The 2-adic valuation and odd part of a natural number: `valBinNat x = (v, r)`
where `x = 2 ^ v * r` with `r` odd (and `(0, 0)` for `x = 0`). -/
def valBinNat (x : ℕ) : ℕ × ℕ :=
  if h : 0 < x ∧ x % 2 = 0 then
    have decr := div2_lt_self h.left;
    let vbn_half := valBinNat (x / 2);
    (vbn_half.fst + 1, vbn_half.snd)
  else if 0 < x then
    (0, x)
  else
    (0, 0)
termination_by x
decreasing_by
  exact div2_lt_self h.left

lemma valBinNat_even {x : ℕ} (h : 0 < x ∧ x % 2 = 0) :
    valBinNat x = ((valBinNat (x / 2)).1 + 1, (valBinNat (x / 2)).2) := by
  conv_lhs => rw [valBinNat]
  rw [dif_pos h]

/-- The 2-adic valuation and signed odd part of an integer: `valBin x = (v, r)`
where `x = 2 ^ v * r` with `|r|` odd. -/
def valBin (x : ℤ) : ℕ × ℤ :=
  let (v, r) := valBinNat (natAbs x);
  (v, sign x * r)



lemma odd_part_le_self_nat (x : ℕ) : (valBinNat x).2 ≤ x := by
  have acc : ∀ y, y ≤ x → (valBinNat y).2 ≤ x := by
    induction x with
    | zero =>
      intro y h
      rw [le_zero_eq] at h
      subst h
      simp [valBinNat]
    | succ x ih =>
      intro y y_le_sx
      cases y_le_sx with
      | refl =>
        cases mod_two_eq_zero_or_one (Nat.succ x) with
        | inl even =>
          have h : 0 < Nat.succ x ∧ Nat.succ x % 2 = 0 :=
          And.intro (zero_lt_succ x) even;
          rw [valBinNat_even h]
          have h' := ih (Nat.succ x / 2) (div2_succ_le_self x);
          exact le_trans h' (le_succ x)
        | inr odd =>
          have not_even : Nat.succ x % 2 ≠ 0 := by
            rw [odd]
            simp
          rw [valBinNat, dif_neg (not_and_of_not_right (0 < Nat.succ x) not_even),
            if_pos (zero_lt_succ x)]
      | step y_le_x => exact le_trans (ih y y_le_x) (le_succ x);
  exact acc x (le_refl x)

lemma odd_part_succ_pos (x : ℕ) : 0 < (valBinNat (Nat.succ x)).2 := by
  have acc : ∀ y, (y ≤ x → 0 < (valBinNat (Nat.succ y)).2) := by
    induction x with
    | zero =>
      intro y y_le_x
      rw [le_zero_eq] at y_le_x
      subst y_le_x
      simp [valBinNat]
    | succ x ih =>
      intro y y_le_sx
      cases y_le_sx with
      | refl =>
        cases mod_two_eq_zero_or_one (Nat.succ (Nat.succ x)) with
        | inl even =>
          have h : 0 < Nat.succ (Nat.succ x) ∧ Nat.succ (Nat.succ x) % 2 = 0 :=
          And.intro (zero_lt_succ (Nat.succ x)) even;
          rw [valBinNat_even h, div2_succ_succ_eq_succ_div2]
          exact ih (x / 2) (Nat.div_le_self x 2)
        | inr odd =>
          have not_even : Nat.succ (Nat.succ x) % 2 ≠ 0 := by
            rw [odd]
            simp
          rw [valBinNat, dif_neg (not_and_of_not_right (0 < Nat.succ (Nat.succ x)) not_even),
            if_pos (zero_lt_succ (Nat.succ x))]
          exact zero_lt_succ (Nat.succ x)
      | step y_le_x => exact ih y y_le_x;
  exact acc x (le_refl x)

lemma odd_part_nat_pos (x : ℕ) : x ≠ 0 → 0 < (valBinNat x).2 := by
  cases x with
  | zero =>
    intro absurd
    apply False.elim
    apply absurd
    rfl
  | succ x =>
    intro _
    exact odd_part_succ_pos x

/-- The Kronecker symbol `(x / 2)`, which depends only on `x mod 8`. -/
def kronecker_2 (x : ℕ) : ℤ := match x % 8 with
  | 1 => 1 | 7 => 1
  | 3 => -1 | 5 => -1
  | _ => 0

/-- Auxiliary recursion computing the Kronecker symbol `(a / b)` for odd `b`,
carrying an accumulated sign `k`; it strips powers of two from `a` via quadratic
reciprocity until `a` is reduced. -/
def kroneckerOdd (k : ℤ) (a b : ℕ) : ℤ :=
  -- b is odd and a, b ≥ 0
  if a = 0 then if b > 1 then 0 else k else
  let v_r := valBinNat a;
  let k' := if v_r.fst % 2 = 0 then k else k * (kronecker_2 b);
  let k'' := if v_r.snd % 4 = 3 ∧ b % 4 = 3 then -k' else k';
  kroneckerOdd k'' (b % v_r.snd) v_r.snd
termination_by a
decreasing_by
  apply lt_of_lt_of_le _ (odd_part_le_self_nat _)
  apply mod_lt
  apply odd_part_nat_pos
  assumption


/-- The Kronecker symbol `(a / b)` for integers `a` and `b`. -/
def kronecker (a b : ℤ) : ℤ :=
  if b = 0 then if natAbs a = 1 then 1 else 0 else
  if b % 2 = 0 ∧ a % 2 = 0 then 0 else
  let (v2b, b') := valBin b;
  let k := if v2b % 2 = 0 then 1 else kronecker_2 (natAbs a);
  let k' := if b' < 0 ∧ a < 0 then -k else k;
  let abs_b' := natAbs b';
  let a_residue := natAbs ((a % ofNat abs_b' + abs_b') % ofNat abs_b');
  kroneckerOdd k' a_residue abs_b'

/-- Decides, via the Kronecker symbol, whether the quadratic `a x ^ 2 + b x + c`
has a root modulo `p`. This naive version fails for `p = 2`. -/
def exRootQuad (a b c p : ℤ) : Bool :=
  let (a', b', c') := (a % p, b % p, c % p);
  kronecker ((b' * b' - 4 * a' * c') % p) p = 1

/-- Decides whether the quadratic `a x ^ 2 + b x + c` has a root in `ℤ / p ℤ`,
assuming `p > 1` and `p ∤ a`. -/
def quadRootInZpZ (a b c : ℤ) (p : ℕ) : Bool :=
match p with
  | 0 => unreachable!
  | 1 => unreachable!
  | 2 => match a % 2 with
    | 0 => unreachable!
    | _ => (b % 2 = 0) || (c % 2 = 0)
  | _ => match a % (p : ℤ) with
    | 0 => unreachable!
    | a' => kronecker ((b * b - 4 * a' * c) % (p : ℤ)) (p : ℤ) = 1


end Int
