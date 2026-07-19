/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Egrs75.Defs
import Mathlib.Data.Nat.Digits.Lemmas

/-!
EGRS75 — the single-base density "Fact" (kernel-clean).

This isolates and proves the load-bearing density lemma from the original EGRS
1975 proof (Math. Comp. 29, the "Fact" inside the proof of their Theorem 1):

  **Fact.** For an odd prime base `p` (more generally any odd `p ≥ 3`) and every
  `x ≥ 1`, the half-open interval `[x, 2·x)` contains a number all of whose
  base-`p` digits are `≤ (p-1)/2` (i.e. a `LowDigits p` number).

In EGRS the ratio is `(p-1)/A`; with `A = (p-1)/2` (the central-binomial / Kummer
case) it is exactly `2`. This is the genuine density content
`#{n < X : LowDigits p n} ≍ X^{θ_p}` made into a *gap* bound: consecutive
`LowDigits p` numbers never differ by more than a factor `2`.

We prove it constructively via the explicit "round up to the next low-digit
number" map `ru`:  `ru x` is the smallest `LowDigits p` number `≥ x`, built by
well-founded recursion on the base-`p` digit recursion `x = p·(x/p) + x%p`.
Correctness (`x ≤ ru x < 2x`, `LowDigits p (ru x)`) is proven by strong induction.

KERNEL-CLEAN: `#print axioms` at the end must show only
`propext / Classical.choice / Quot.sound` (NO `sorryAx`).

NOTE: this Fact does NOT by itself prove the two-prime crux — it is the single
*per-base* density input. Combining the two per-base Facts into a simultaneous
low-digit number in both bases is the EGRS Diophantine "iterative digit repair"
step (their eq. (2) + the repair Lemma), which is the genuine remaining gap.
-/

namespace Egrs75.RoundUp

open Nat
open Egrs75

/-! ## The round-up map `ru` and its correctness -/

variable (p : ℕ)

/-- `ru p x` = the smallest `LowDigits p` number `≥ x`, built by rounding up the
base-`p` digits with carry. Defined by well-founded recursion on `x`:
* `x = 0` → `0`;
* `x < p` or degenerate `p < 3` → `x` if `x ≤ (p-1)/2` (single low digit), else `p`
  (carry to `10₍ₚ₎`);
* `x ≥ p` (and `p ≥ 3`), last digit `d = x % p`:
    * `d ≤ (p-1)/2` → keep it: `p · ru (x/p) + d`;
    * `d > (p-1)/2`   → drop it and carry: `p · ru (x/p + 1)`.

The `p < 3` guard makes the definition total (the recursion only fires for
`p ≥ 3`, where `x/p + 1 < x` for `x ≥ p`); correctness is only claimed for
odd `p ≥ 3` (`ru_spec`). -/
def ru (x : ℕ) : ℕ :=
  if x = 0 then 0
  else if x < p ∨ p < 3 then (if x ≤ (p - 1) / 2 then x else p)
  else
    if x % p ≤ (p - 1) / 2 then p * ru (x / p) + x % p
    else p * ru (x / p + 1)
termination_by x
decreasing_by
  · exact Nat.div_lt_self (by omega) (by omega)
  · -- x / p + 1 < x  when  p ≤ x  and  3 ≤ p (both from ¬(x < p ∨ p < 3))
    have hp3 : 3 ≤ p := by omega
    have _hpx : p ≤ x := by omega
    have hdiv : x / p ≤ x / 3 := Nat.div_le_div_left hp3 (by omega)
    have _hx3 : x / 3 + 1 < x := by omega
    omega

/-! ## `LowDigits` of `ru` (kernel-clean)

`ru p x` is always `LowDigits p`. Proven by strong induction using the digit
recursion: `LowDigits p (p·m + d) ` holds when `d ≤ (p-1)/2` and `LowDigits p m`. -/

/-- `0` has no digits, hence `LowDigits p 0` vacuously. -/
lemma lowDigits_zero (p : ℕ) : LowDigits p 0 := by
  unfold LowDigits
  simp_all

/-- A low last digit on top of a low number stays low: `LowDigits p (p*m + d)`
when `d ≤ (p-1)/2` and `LowDigits p m` (and `2 ≤ p`). -/
lemma lowDigits_cons {p m d : ℕ} (hp : 2 ≤ p) (hd : d ≤ (p - 1) / 2)
    (hm : LowDigits p m) : LowDigits p (p * m + d) := by
  have hp1 : 1 < p := by omega
  have hdp : d < p := by omega
  rcases eq_or_ne (p * m + d) 0 with h0 | h0
  · rw [show p * m + d = 0 from h0]; exact lowDigits_zero p
  · unfold LowDigits at hm ⊢
    -- digits p (p*m+d) = d :: digits p m   (since (p*m+d)%p = d, (p*m+d)/p = m)
    have hmod : (p * m + d) % p = d := by
      rw [Nat.mul_add_mod_self_left]; exact Nat.mod_eq_of_lt hdp
    have hdiv : (p * m + d) / p = m := by
      rw [Nat.mul_add_div (by omega : 0 < p), Nat.div_eq_of_lt hdp, Nat.add_zero]
    rw [Nat.digits_def' hp1 (Nat.pos_of_ne_zero h0), hmod, hdiv]
    simp_all

/-- For `p ≥ 3`, the digit `1 ≤ (p-1)/2`. -/
lemma one_le_half {p : ℕ} (hp : 3 ≤ p) : (1 : ℕ) ≤ (p - 1) / 2 := by
  have : 2 ≤ p - 1 := by omega
  calc (1 : ℕ) = 2 / 2 := by norm_num
    _ ≤ (p - 1) / 2 := Nat.div_le_div_right this

/-- `LowDigits p 1` for `p ≥ 3` (digits of `1` are `[1]`, and `1 ≤ (p-1)/2`). -/
lemma lowDigits_one {p : ℕ} (hp : 3 ≤ p) : LowDigits p 1 := by
  have h : (1 : ℕ) = p * 0 + 1 := by ring
  rw [h]
  exact lowDigits_cons (by omega) (one_le_half hp) (lowDigits_zero p)

/-- `ru p x` has all base-`p` digits `≤ (p-1)/2`. KERNEL-CLEAN. -/
lemma lowDigits_ru {p : ℕ} (hp : 3 ≤ p) (x : ℕ) : LowDigits p (ru p x) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rw [ru]
    split_ifs with hx0 hsmall hlow hlow2
    · exact lowDigits_zero p
    · -- x ≤ (p-1)/2 : single low digit, x = p*0 + x  (hlow : x ≤ (p-1)/2)
      have h : x = p * 0 + x := by ring
      rw [h]
      exact lowDigits_cons (by omega) hlow (lowDigits_zero p)
    · -- carry to p : p = p*1 + 0
      have hpc : LowDigits p (p * 1 + 0) :=
        lowDigits_cons (by omega) (Nat.zero_le _) (lowDigits_one hp)
      simpa using hpc
    · -- keep low digit:  p * ru (x/p) + x%p,  x%p ≤ (p-1)/2
      exact lowDigits_cons (by omega) hlow2 (ih (x / p) (Nat.div_lt_self (by omega) (by omega)))
    · -- carry branch:  p * ru (x/p + 1) = p * ru (x/p + 1) + 0
      have hdec : x / p + 1 < x := by
        have hdiv : x / p ≤ x / 3 := Nat.div_le_div_left hp (by omega)
        omega
      have hcarry : LowDigits p (p * ru p (x / p + 1) + 0) :=
        lowDigits_cons (by omega) (Nat.zero_le _) (ih (x / p + 1) hdec)
      simpa using hcarry

/-! ## The bounds `x ≤ ru x < 2x` (kernel-clean): the density Fact

This is the quantitative core — consecutive `LowDigits p` numbers differ by a
factor `< 2`. Proven by strong induction following EGRS's "Fact". The tight case
is the carry branch (`x % p > (p-1)/2`), where `ru x = p · ru(x/p + 1)` and the
upper bound `p · ru(x/p+1) < 2x` uses `2·(x%p) > p` (which holds since
`x%p > (p-1)/2` and `p` is odd ⟹ `x%p ≥ (p+1)/2`). -/

/-- **The EGRS density Fact, as bounds on `ru`.** For odd `p ≥ 3` and `x ≥ 1`:
`x ≤ ru p x` and `ru p x < 2*x`. Hence the smallest `LowDigits p` number `≥ x`
lies in `[x, 2x)`. KERNEL-CLEAN. -/
lemma ru_bounds {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) :
    ∀ x, 1 ≤ x → x ≤ ru p x ∧ ru p x < 2 * x := by
  -- `Odd p` ⟹ `2 * ((p-1)/2) + 1 = p`, i.e. the half is exact: `(p-1)/2 = (p-1)/2`
  -- and any digit `> (p-1)/2` is `≥ (p+1)/2`, so `2*digit ≥ p+1 > p`.
  have hhalf : 2 * ((p - 1) / 2) + 1 = p := by
    obtain ⟨k, hk⟩ := hodd
    simp_all
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx1
    rw [ru]
    split_ifs with hx0 hsmall hlow hlow2
    · omega  -- x = 0 contradicts 1 ≤ x
    · -- single low digit: ru = x.  x ≤ x ✓; x < 2x since x ≥ 1
      omega
    · -- carry to p (here ¬(x ≤ (p-1)/2), and hsmall : x < p ∨ p < 3, with p ≥ 3 so x < p)
      -- ru = p.  Need x ≤ p (since x < p) and p < 2x.
      -- ¬hlow : (p-1)/2 < x, and 2*((p-1)/2)+1 = p ⟹ p ≤ 2x - 1 < 2x. x ≤ p since x < p.
      refine ⟨by omega, ?_⟩
      -- p < 2x : from (p-1)/2 < x ⟹ p = 2*((p-1)/2)+1 ≤ 2*(x-1)+1 = 2x-1 < 2x
      omega
    · -- keep low digit: ru = p * ru(x/p) + x%p,  hlow2 : x%p ≤ (p-1)/2
      -- Need x/p ≥ 1 to apply IH. Since ¬hsmall ⟹ p ≤ x ⟹ x/p ≥ 1.
      have hpx : p ≤ x := by omega
      have hr1 : 1 ≤ x / p := Nat.one_le_div_iff (by omega) |>.mpr hpx
      have hrlt : x / p < x := Nat.div_lt_self (by omega) (by omega)
      obtain ⟨hlo, hhi⟩ := ih (x / p) hrlt hr1
      have hsplit : x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
      constructor
      · -- x = p*(x/p) + x%p ≤ p*ru(x/p) + x%p
        calc x = p * (x / p) + x % p := hsplit
          _ ≤ p * ru p (x / p) + x % p := by
              exact Nat.add_le_add_right (Nat.mul_le_mul_left p hlo) _
      · -- p*ru(x/p) + x%p < 2x = 2*(p*(x/p) + x%p)
        -- ru(x/p) < 2*(x/p) ⟹ p*ru(x/p) < 2*(p*(x/p))
        -- so p*ru(x/p) + x%p < 2*(p*(x/p)) + x%p ≤ 2*(p*(x/p)) + 2*(x%p) = 2x
        have hstrict : p * ru p (x / p) < 2 * (p * (x / p)) := by
          have := Nat.mul_lt_mul_of_pos_left hhi (show 0 < p by omega)
          -- this : p * ru(x/p) < p * (2 * (x/p));  p*(2*(x/p)) = 2*(p*(x/p))
          calc p * ru p (x / p) < p * (2 * (x / p)) := this
            _ = 2 * (p * (x / p)) := by ring
        -- linear in atoms {p*ru(x/p), p*(x/p), x, x%p}:
        --   hsplit : x = p*(x/p) + x%p;  hstrict : p*ru(x/p) < 2*(p*(x/p))
        --   goal   : p*ru(x/p) + x%p < 2*x.
        have hge0 : 0 ≤ x % p := Nat.zero_le _
        linarith [hsplit, hstrict, hge0]
    · -- carry branch: ru = p * ru(x/p + 1),  ¬hlow2 : (p-1)/2 < x%p
      have hpx : p ≤ x := by omega
      have hdec : x / p + 1 < x := by
        have hdiv : x / p ≤ x / 3 := Nat.div_le_div_left hp (by omega)
        omega
      have hr1 : 1 ≤ x / p + 1 := Nat.le_add_left 1 (x / p)
      obtain ⟨hlo, hhi⟩ := ih (x / p + 1) hdec hr1
      have hsplit : x = p * (x / p) + x % p := (Nat.div_add_mod x p).symm
      have hxmod : x % p < p := Nat.mod_lt x (by omega)
      -- ¬hlow2 : (p-1)/2 < x%p ⟹ x%p ≥ (p-1)/2 + 1, and 2*((p-1)/2)+1 = p ⟹ 2*(x%p) ≥ p+1 > p
      have hmodbig : p < 2 * (x % p) := by
        -- hlow2 : ¬(x%p ≤ (p-1)/2); hhalf : 2*((p-1)/2)+1 = p
        omega
      refine ⟨le_of_lt ?_, ?_⟩
      · -- x = p*(x/p)+x%p < p*(x/p) + p = p*(x/p+1) ≤ p*ru(x/p+1)
        calc x = p * (x / p) + x % p := hsplit
          _ < p * (x / p) + p := by omega
          _ = p * (x / p + 1) := by ring
          _ ≤ p * ru p (x / p + 1) := Nat.mul_le_mul_left p hlo
      · -- p*ru(x/p+1) < 2x.  ru(x/p+1) < 2*(x/p+1) ⟹ ru(x/p+1) ≤ 2*(x/p)+1
        -- p*ru ≤ p*(2*(x/p)+1) = 2*(p*(x/p)) + p < 2*(p*(x/p)) + 2*(x%p) = 2x.
        have hru_le : ru p (x / p + 1) ≤ 2 * (x / p) + 1 := by omega
        have hmul : p * ru p (x / p + 1) ≤ 2 * (p * (x / p)) + p := by
          calc p * ru p (x / p + 1) ≤ p * (2 * (x / p) + 1) := Nat.mul_le_mul_left p hru_le
            _ = 2 * (p * (x / p)) + p := by ring
        -- linear in atoms {p*ru(x/p+1), p*(x/p), x, x%p, p}:
        --   hsplit : x = p*(x/p) + x%p; hmul : p*ru(x/p+1) ≤ 2*(p*(x/p)) + p;
        --   hmodbig : p < 2*(x%p).  goal : p*ru(x/p+1) < 2*x.
        linarith [hsplit, hmul, hmodbig]

/-- **EGRS density Fact (existence form).** For an odd prime base `p ≥ 3` (in fact
any odd `p ≥ 3`) and every `x ≥ 1`, the interval `[x, 2x)` contains a `LowDigits p`
number. This is the single load-bearing density input from EGRS75's proof of
their Theorem 1. KERNEL-CLEAN. -/
theorem exists_lowDigits_between {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) (x : ℕ)
    (hx : 1 ≤ x) : ∃ m, x ≤ m ∧ m < 2 * x ∧ LowDigits p m := by
  obtain ⟨hlo, hhi⟩ := ru_bounds hp hodd x hx
  exact ⟨ru p x, hlo, hhi, lowDigits_ru hp x⟩

end Egrs75.RoundUp
