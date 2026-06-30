/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Aesop

/-!
# The r = 3 case of the "13/9 theorem" (Erdős #367 r-full extension)

This file formalizes an unconditional, elementary lower-bound construction (the `r = 3`
case of a new lower bound for the `r`-full extension of Erdős problem #367).

`rFullPart r m` is the "`r`-full part" of `m`: the product of the prime powers `p ^ v`
occurring in the factorization of `m` for which `r ≤ v_p(m)`. We write `B₃ m := rFullPart 3 m`.

The construction fixes a prime `s ≠ 3`, a "seed" `t₀` with `1 ≤ t₀ ≤ s^3` such that
`s^3 ∣ g t₀`, and sets `t := t₀ + s^3`, `n := (t^3 - 1)^3`. The three main results are:

* `T1` : `B₃ n = n`;
* `T2` : `t^3 * s^3 ∣ B₃ (n+1)`;
* `T3` : `512 * (B₃ n * B₃ (n+1))^9 > n^13`, the integer form of `B₃ n · B₃ (n+1) > n^{13/9}/2`.

The "prime supply" (the existence of infinitely many suitable pairs `(s, t₀)`) is kept as a
hypothesis and is *not* part of this development.
-/

open scoped BigOperators

namespace Core139

/-- The `r`-full part of `m`: the product of prime powers `p ^ v_p(m)` with `r ≤ v_p(m)`. -/
def rFullPart (r m : ℕ) : ℕ :=
  (m.factorization.filter (fun p => r ≤ m.factorization p)).prod (fun p v => p ^ v)

/-- The auxiliary polynomial `g t = t^6 - 3 t^3 + 3` (with natural-number subtraction). -/
def g (t : ℕ) : ℕ := t ^ 6 - 3 * t ^ 3 + 3

/-! ## Generic facts about `rFullPart` -/

/-- `rFullPart` is always positive (it is a product of prime powers, each `≥ 1`). -/
lemma rFullPart_pos (r M : ℕ) : 1 ≤ rFullPart r M := by
  by_contra! h_contra
  simp_all +decide [rFullPart]

/-- For `m ≥ 1`, the `r`-full part of `m ^ r` is `m ^ r` itself: every prime dividing `m ^ r`
has multiplicity `r * v_p(m) ≥ r`, so the filter keeps the entire factorization. -/
lemma rFullPart_pow (r m : ℕ) (hm : 1 ≤ m) :
    rFullPart r (m ^ r) = m ^ r := by
  unfold rFullPart
  convert Nat.prod_factorization_pow_eq_self (pow_ne_zero r (ne_bot_of_gt hm)) using 2
  ext p
  by_cases hp : p ∈ (m ^ r).primeFactors
  · suffices r * m.factorization p < r → r = 0 ∨ m.factorization p = 0 by
      simpa +decide [Finsupp.filter_apply] using this
    exact fun _ => Or.inr (by nlinarith)
  · suffices r * m.factorization p < r → r = 0 ∨ m.factorization p = 0 by
      simpa +decide [Finsupp.filter_apply] using this
    exact fun _ => Or.inr (Nat.eq_zero_of_not_pos fun h' => by nlinarith)

/-- The factorization of `rFullPart r M` is the filtered factorization. -/
lemma factorization_rFullPart (r M : ℕ) :
    (rFullPart r M).factorization = M.factorization.filter (fun p => r ≤ M.factorization p) := by
  unfold rFullPart
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  have hp' : p ∈ M.factorization.support := Finset.mem_of_mem_filter p hp
  rw [Nat.support_factorization] at hp'
  exact Nat.prime_of_mem_primeFactors hp'

/-- If `d ≥ 1` and `d ^ r ∣ M` then `d ^ r ∣ rFullPart r M`: each prime `p ∣ d` has
`v_p(M) ≥ r * v_p(d) ≥ r`, so it survives the filter and `v_p(rFullPart r M) = v_p(M)`. -/
lemma pow_dvd_rFullPart (r d M : ℕ) (hd : 1 ≤ d) (hM : M ≠ 0)
    (h : d ^ r ∣ M) : d ^ r ∣ rFullPart r M := by
  rw [← Nat.factorization_le_iff_dvd] at *
  · rw [factorization_rFullPart _ _]
    intro p
    by_cases hp : r ≤ M.factorization p <;> simp_all +decide
    · simpa using h p
    · exact Or.inr (Nat.eq_zero_of_le_zero (by have := h p; norm_num at this; nlinarith))
  · positivity
  · assumption
  · positivity
  · exact Nat.ne_of_gt (rFullPart_pos r M)

/-! ## Arithmetic facts about `g` -/

/-- For `t ≥ 2`, the natural subtraction in `g` is exact: `g t + 3 t^3 = t^6 + 3`. -/
lemma g_add (t : ℕ) (ht : 2 ≤ t) : g t + 3 * t ^ 3 = t ^ 6 + 3 := by
  unfold g
  linarith [Nat.sub_add_cancel
    (show 3 * t ^ 3 ≤ t ^ 6 by nlinarith [Nat.pow_le_pow_left ht 3, Nat.pow_le_pow_left ht 6])]

/-- Casting `g` to any commutative ring (for `t ≥ 2`): `(g t : R) = t^6 - 3 t^3 + 3`. -/
lemma g_cast {R : Type*} [CommRing R] (t : ℕ) (ht : 2 ≤ t) :
    (g t : R) = (t : R) ^ 6 - 3 * (t : R) ^ 3 + 3 := by
  have h_cast : (g t : R) + 3 * (t : R) ^ 3 = (t : R) ^ 6 + 3 := by
    exact mod_cast (g_add t ht) ▸ rfl
  linear_combination h_cast

/-! ## The construction -/

/-- The shifted seed `t = t₀ + s^3`. -/
def tval (s t₀ : ℕ) : ℕ := t₀ + s ^ 3

/-- The constructed integer `n = (t^3 - 1)^3`. -/
def nval (s t₀ : ℕ) : ℕ := (tval s t₀ ^ 3 - 1) ^ 3

section Construction

/-- Basic bound: `t = t₀ + s^3 ≥ 9` (since `s ≥ 2` so `s^3 ≥ 8`, and `t₀ ≥ 1`). -/
lemma tval_ge (s t₀ : ℕ) (hs : s.Prime) (ht₀ : 1 ≤ t₀ ∧ t₀ ≤ s ^ 3) :
    9 ≤ tval s t₀ := by
  unfold tval
  nlinarith [Nat.pow_le_pow_left hs.two_le 3]

/-- Key identity: `n + 1 = t^3 * g t`, i.e. `(t^3 - 1)^3 + 1 = t^3 (t^6 - 3 t^3 + 3)`. -/
lemma key_identity (s t₀ : ℕ) (hs : s.Prime) (ht₀ : 1 ≤ t₀ ∧ t₀ ≤ s ^ 3) :
    nval s t₀ + 1 = tval s t₀ ^ 3 * g (tval s t₀) := by
  convert Nat.cast_injective (R := ℤ) _
  have ht_ge_2 : 2 ≤ tval s t₀ := le_trans (by decide) (tval_ge s t₀ hs ht₀)
  simp only [g_cast, ht_ge_2, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow]
  unfold nval
  norm_num [Nat.cast_sub (show 1 ≤ tval s t₀ ^ 3 from Nat.one_le_pow _ _ (by linarith))]
  ring

/-- Congruence step: `s^3 ∣ g t`. Since `t ≡ t₀ (mod s^3)` and `g` is a polynomial,
`g t ≡ g t₀ ≡ 0 (mod s^3)`. -/
lemma s3_dvd_g_t (s t₀ : ℕ) (hs : s.Prime) (ht₀ : 1 ≤ t₀ ∧ t₀ ≤ s ^ 3)
    (hroot : s ^ 3 ∣ g t₀) : s ^ 3 ∣ g (tval s t₀) := by
  have h_cast : (g (tval s t₀) : ZMod (s ^ 3)) = (g t₀ : ZMod (s ^ 3)) := by
    rw [g_cast, g_cast]
    · simp +decide [tval]
    · contrapose! hroot
      interval_cases t₀ <;> norm_num [g] at *
      exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by nlinarith [hs.two_le, pow_succ s 2])
    · exact le_trans (by decide) (tval_ge s t₀ hs ht₀)
  simp_all +decide [← ZMod.natCast_eq_zero_iff]

/-- `s` does not divide `t`: otherwise `s ∣ g t` together with `s ∣ t^6`, `s ∣ 3 t^3` would
force `s ∣ 3`, hence `s = 3`, contradicting `hs3`. -/
lemma s_not_dvd_t (s t₀ : ℕ) (hs : s.Prime) (hs3 : s ≠ 3) (ht₀ : 1 ≤ t₀ ∧ t₀ ≤ s ^ 3)
    (hroot : s ^ 3 ∣ g t₀) : ¬ s ∣ tval s t₀ := by
  intro hdiv
  have hdiv_gt : s ∣ g (tval s t₀) :=
    dvd_trans (dvd_pow_self _ (by decide)) (s3_dvd_g_t s t₀ hs ht₀ hroot)
  have hdiv_t3 : s ∣ tval s t₀ ^ 3 := dvd_pow hdiv three_ne_zero
  have hdiv_t6 : s ∣ tval s t₀ ^ 6 := dvd_trans hdiv (dvd_pow_self _ (by decide))
  have hdiv_3t3 : s ∣ 3 * tval s t₀ ^ 3 := dvd_mul_of_dvd_right hdiv_t3 _
  have hdiv_3 : s ∣ 3 := by
    convert Nat.dvd_sub (hdiv_gt.add hdiv_3t3) hdiv_t6 using 1
    exact eq_tsub_of_add_eq
      (by linarith [g_add (tval s t₀) (by linarith [tval_ge s t₀ hs ht₀])])
  have := Nat.le_of_dvd (by decide) hdiv_3
  interval_cases s <;> trivial

/-! ## The three theorems -/

/-- (T1) The `3`-full part of `n` is `n`. Since `n = (t^3-1)^3` is a perfect cube with
`t^3 - 1 ≥ 1`, this is `rFullPart_pow`.

(The hypotheses `hs3` and `hroot` are part of the construction's hypothesis structure but
turn out to be unnecessary for this particular statement.) -/
theorem T1 (s t₀ : ℕ) (hs : s.Prime) (_hs3 : s ≠ 3) (ht₀ : 1 ≤ t₀ ∧ t₀ ≤ s ^ 3)
    (_hroot : s ^ 3 ∣ g t₀) : rFullPart 3 (nval s t₀) = nval s t₀ := by
  have hm : 1 ≤ tval s t₀ ^ 3 - 1 :=
    Nat.le_sub_one_of_lt (one_lt_pow₀ (by linarith [tval_ge s t₀ hs ht₀]) (by norm_num))
  unfold nval
  exact rFullPart_pow 3 (tval s t₀ ^ 3 - 1) hm

/-- (T2) `t^3 * s^3` divides the `3`-full part of `n + 1`. Both `t^3` and `s^3` divide `n+1`
(via `n+1 = t^3 g t` and `s^3 ∣ g t`), each survives into `B₃` by `pow_dvd_rFullPart`, and
they are coprime since `s ∤ t`. -/
theorem T2 (s t₀ : ℕ) (hs : s.Prime) (hs3 : s ≠ 3) (ht₀ : 1 ≤ t₀ ∧ t₀ ≤ s ^ 3)
    (hroot : s ^ 3 ∣ g t₀) : tval s t₀ ^ 3 * s ^ 3 ∣ rFullPart 3 (nval s t₀ + 1) := by
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
  · exact Nat.Coprime.pow _ _ <| Nat.Coprime.symm <|
      hs.coprime_iff_not_dvd.mpr <| s_not_dvd_t s t₀ hs hs3 ht₀ hroot
  · convert pow_dvd_rFullPart 3 (tval s t₀) (nval s t₀ + 1)
      (by linarith [tval_ge s t₀ hs ht₀]) (Nat.succ_ne_zero _) _ using 1
    exact key_identity s t₀ hs ht₀ ▸ dvd_mul_right _ _
  · convert pow_dvd_rFullPart 3 s (nval s t₀ + 1)
      (Nat.Prime.pos hs) (Nat.succ_ne_zero _) _ using 1
    exact dvd_trans (s3_dvd_g_t s t₀ hs ht₀ hroot) (key_identity s t₀ hs ht₀ ▸ dvd_mul_left _ _)

/-- (T3) The integer form of `B₃(n) B₃(n+1) > n^{13/9} / 2`:
`512 * (B₃ n * B₃ (n+1))^9 > n^13`.

Proof chain: `B₃ n = n` and `t^3 s^3 ≤ B₃ (n+1)`, with `t ≤ 2 s^3` giving
`2 (B₃ n · B₃ (n+1)) ≥ n t^4`; raising to the `9`-th power and using `t^9 > n` (so
`t^36 > n^4`) yields `512 (B₃ n · B₃ (n+1))^9 ≥ n^9 t^36 > n^13`. -/
theorem T3 (s t₀ : ℕ) (hs : s.Prime) (hs3 : s ≠ 3) (ht₀ : 1 ≤ t₀ ∧ t₀ ≤ s ^ 3)
    (hroot : s ^ 3 ∣ g t₀) :
    512 * (rFullPart 3 (nval s t₀) * rFullPart 3 (nval s t₀ + 1)) ^ 9
    > nval s t₀ ^ 13 := by
  have hB0 : rFullPart 3 (nval s t₀) = nval s t₀ := T1 s t₀ hs hs3 ht₀ hroot
  have hB1 : tval s t₀ ^ 3 * s ^ 3 ∣ rFullPart 3 (nval s t₀ + 1) := T2 s t₀ hs hs3 ht₀ hroot
  have hB1pos : 0 < rFullPart 3 (nval s t₀ + 1) := rFullPart_pos _ _
  have hts_le : tval s t₀ ^ 3 * s ^ 3 ≤ rFullPart 3 (nval s t₀ + 1) := Nat.le_of_dvd hB1pos hB1
  have ht9 : 9 ≤ tval s t₀ := tval_ge s t₀ hs ht₀
  have ht_le : tval s t₀ ≤ 2 * s ^ 3 := by unfold tval; linarith
  have hn_pos : 0 < nval s t₀ :=
    pow_pos (Nat.sub_pos_of_lt (one_lt_pow₀ (by linarith) (by linarith))) _
  have ht9n : tval s t₀ ^ 9 > nval s t₀ := by
    unfold nval; zify
    rw [Nat.cast_sub] <;> push_cast <;>
      nlinarith only [ht9, pow_pos (by linarith : 0 < tval s t₀) 3,
        pow_pos (by linarith : 0 < tval s t₀) 6]
  -- `2 * (B₃ n · B₃ (n+1)) ≥ n * t^4`
  have h2BB_ge_nt4 :
      2 * (nval s t₀ * rFullPart 3 (nval s t₀ + 1)) ≥ nval s t₀ * tval s t₀ ^ 4 := by
    nlinarith [Nat.mul_le_mul_left (nval s t₀) hts_le, Nat.mul_le_mul_left (nval s t₀) ht_le]
  -- `512 * (B₃ n · B₃ (n+1))^9 ≥ n^9 * t^36`
  have h512BB_ge_nt36 :
      512 * (nval s t₀ * rFullPart 3 (nval s t₀ + 1)) ^ 9 ≥ nval s t₀ ^ 9 * tval s t₀ ^ 36 := by
    have := Nat.pow_le_pow_left h2BB_ge_nt4 9
    ring_nf at *
    aesop
  simp_all +decide only [gt_iff_lt]
  exact lt_of_lt_of_le
    (by nlinarith [pow_pos hn_pos 9, pow_pos hn_pos 4,
      pow_lt_pow_left₀ ht9n (by positivity) (by positivity : (4 : ℕ) ≠ 0)])
    h512BB_ge_nt36

end Construction

end Core139
