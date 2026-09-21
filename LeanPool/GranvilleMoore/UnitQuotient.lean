/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import LeanPool.GranvilleMoore.Defs.TheFermatQuotient
public import LeanPool.GranvilleMoore.Defs.TheIteratedFermatQuotients
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Multiplicity

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The unit quotient

The integrality of the Fermat quotient and of the unit quotient, and the congruence between
them. For a prime `p` not dividing `x`, Fermat's little theorem says that the unit
`t_x = x ^ (p - 1)` is a *principal* unit at `p`, so `q_p(x) = (t_x - 1) / p` is an integer.
For an odd prime, lifting the exponent upgrades this to `p ^ (k + 1) ∣ t_x ^ (p ^ k) - 1`,
which makes the unit quotient `g_k(x) = (t_x ^ (p ^ k) - 1) / p ^ (k + 1)` an integer as
well; and a binomial expansion along the tower shows `g_k(x) ≡ q_p(x)` modulo `p` for every
`k`.

## Main results

* `GranvilleMoore.dvd_fermatUnit_sub_one`: `p ∣ t_x - 1`, the unit is principal.
* `GranvilleMoore.fermatQuotient_eq_intCast`: `q_p(x)` is an integer.
* `GranvilleMoore.pow_dvd_fermatUnit_pow_sub_one`: `p ^ (k + 1) ∣ t_x ^ (p ^ k) - 1` for odd
  `p`, by lifting the exponent.
* `GranvilleMoore.unitQuot_eq_intCast`: `g_k(x)` is an integer.
* `GranvilleMoore.fermatUnit_pow_eq_one_add_pow_mul`: the expansion
  `t_x ^ (p ^ k) = 1 + p ^ (k + 1) g_k(x)`, as an identity in `ℤ`.
* `GranvilleMoore.dvd_unitQuot_sub_fermatQuotient`: `g_k(x) ≡ q_p(x)` modulo `p`.

## Implementation notes

`fermatQuotient` and `unitQuot` are `ℚ`-valued, so "is an integer" is stated as the
existence of an integer whose cast is the value. The statements that consume those integers
therefore take them as arguments together with the hypothesis identifying them, e.g.
`fermatUnit_pow_eq_one_add_pow_mul` takes `hg : unitQuot p x k = (g : ℚ)`; the integer is
unique, so this loses nothing and keeps every downstream statement inside `ℤ`.

The inductive step of `dvd_unitQuot_sub_fermatQuotient` is isolated as
`one_add_pow_eq_of_pow_dvd`, a statement about an arbitrary `A` divisible by `p ^ n`: the
binomial expansion of `(1 + A) ^ p` is `1 + p A` up to `p ^ (n + 2)`. Stating it that way
avoids truncated subtraction in the exponents that appear in the paper's proof.
-/

@[expose] public section

open Finset

namespace GranvilleMoore

/-! ### Integrality of the Fermat quotient -/

/-- **The unit is principal**: for a prime `p` with `p ∤ x`, `p` divides `t_x - 1`.

This is Fermat's little theorem in the form the Frobenius tower uses: `t_x = x ^ (p - 1)`
is congruent to `1` modulo `p`, so it is a principal unit at `p`. -/
theorem dvd_fermatUnit_sub_one {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) :
    (p : ℤ) ∣ fermatUnit p x - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx' : (x : ZMod p) ≠ 0 := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hx
  have h1 := ZMod.pow_card_sub_one_eq_one hx'
  have h2 : ((fermatUnit p x - 1 : ℤ) : ZMod p) = 0 := by push_cast [fermatUnit, h1]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2

/-- **The Fermat quotient is an integer**: for a prime `p` with `p ∤ x` the rational number
`q_p(x)` is the cast of an integer.

Integrality is phrased as the existence of an integer `q` with `q_p(x) = q`, since
`fermatQuotient` is `ℚ`-valued by definition. -/
theorem fermatQuotient_eq_intCast {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) :
    ∃ q : ℤ, fermatQuotient p x = (q : ℚ) := by
  obtain ⟨q, hq⟩ := dvd_fermatUnit_sub_one hp hx
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine ⟨q, ?_⟩
  rw [fermatQuotient, show (fermatUnit p x - 1 : ℤ) = (p : ℤ) * q from hq]
  push_cast
  field_simp

/-- The unit `t_x = x ^ (p - 1)` is prime to `p` whenever `x` is: a prime dividing a power
divides the base. -/
theorem not_dvd_fermatUnit {p : ℕ} (hp : p.Prime) {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) :
    ¬ (p : ℤ) ∣ fermatUnit p x :=
  fun h => hx ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h)

/-! ### Divisibility along the Frobenius tower -/

/-- **Divisibility of the Frobenius power of the unit**: for an odd prime `p` with `p ∤ x`,
`p ^ (k + 1)` divides `t_x ^ (p ^ k) - 1`.

This is lifting the exponent applied to `t_x` and `1`: the `p`-adic valuation of
`t_x ^ (p ^ k) - 1` exceeds that of `t_x - 1` by exactly `k`, and `t_x - 1` is already
divisible by `p` by `GranvilleMoore.dvd_fermatUnit_sub_one`. -/
theorem pow_dvd_fermatUnit_pow_sub_one {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) (k : ℕ) : (p : ℤ) ^ (k + 1) ∣ fermatUnit p x ^ p ^ k - 1 := by
  have hp' : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hdvd := dvd_fermatUnit_sub_one hp hx
  have hnot := not_dvd_fermatUnit hp hx
  have hlte := emultiplicity_pow_prime_pow_sub_pow_prime_pow hp' hodd hdvd hnot k
  simp only [one_pow] at hlte
  have h1 : (1 : ℕ∞) ≤ emultiplicity ((p : ℤ)) (fermatUnit p x - 1) := by
    simpa using le_emultiplicity_of_pow_dvd (k := 1) (by simpa using hdvd)
  refine pow_dvd_of_le_emultiplicity ?_
  rw [hlte]
  calc ((k + 1 : ℕ) : ℕ∞) = 1 + (k : ℕ∞) := by push_cast; ring
    _ ≤ emultiplicity ((p : ℤ)) (fermatUnit p x - 1) + (k : ℕ∞) := by gcongr

/-- **The unit quotient is an integer**: for an odd prime `p` with `p ∤ x` the rational
number `g_k(x)` is the cast of an integer.

The numerator of `GranvilleMoore.unitQuot` is divisible by the denominator `p ^ (k + 1)` by
`GranvilleMoore.pow_dvd_fermatUnit_pow_sub_one`. -/
theorem unitQuot_eq_intCast {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) (k : ℕ) : ∃ g : ℤ, unitQuot p x k = (g : ℚ) := by
  obtain ⟨g, hg⟩ := pow_dvd_fermatUnit_pow_sub_one hp hodd hx k
  have hg' : (x ^ (p - 1)) ^ p ^ k - 1 = (p : ℤ) ^ (k + 1) * g := hg
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine ⟨g, ?_⟩
  rw [unitQuot_eq, hg']
  push_cast
  field_simp

/-- **Expansion of the Frobenius power of the unit**, over `ℤ`:
`t_x ^ (p ^ k) = 1 + p ^ (k + 1) g_k(x)`.

`GranvilleMoore.pow_eq_one_add_pow_mul_unitQuot` is this identity in `ℚ`; combined with an
integer `g` representing `g_k(x)` — which exists by `GranvilleMoore.unitQuot_eq_intCast` —
it becomes an identity between integers, which is the form consumers of the tower use. Only
`p ≠ 0` is needed: the hypotheses making `g` exist are carried by `hg`. -/
theorem fermatUnit_pow_eq_one_add_pow_mul {p : ℕ} (hp : p ≠ 0) {x : ℤ} {k : ℕ} {g : ℤ}
    (hg : unitQuot p x k = (g : ℚ)) :
    fermatUnit p x ^ p ^ k = 1 + (p : ℤ) ^ (k + 1) * g := by
  have h : (x ^ (p - 1)) ^ p ^ k = 1 + (p : ℤ) ^ (k + 1) * g := by
    refine Int.cast_injective (α := ℚ) ?_
    push_cast
    rw [← hg]
    exact pow_eq_one_add_pow_mul_unitQuot hp x k
  exact h

/-! ### The unit quotient modulo `p` -/

/-- The binomial expansion of `(1 + A) ^ p` for `p` a prime with `p ≥ 3` and `p ^ n ∣ A`
with `n ≥ 1`: it is `1 + p A` modulo `p ^ (n + 2)`.

Every binomial term `C(p, m) A ^ m` with `2 ≤ m ≤ p` is divisible by `p ^ (n + 2)`: for
`m < p` because `p ∣ C(p, m)` and `p ^ (2n) ∣ A ^ m`, and for `m = p` because
`p ^ (3n) ∣ A ^ p`. This is the inductive step of
`GranvilleMoore.dvd_unitQuot_sub_fermatQuotient`. -/
private theorem one_add_pow_eq_of_pow_dvd {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {n : ℕ}
    (hn : 1 ≤ n) {A : ℤ} (hA : (p : ℤ) ^ n ∣ A) :
    ∃ w : ℤ, (1 + A) ^ p = 1 + (p : ℤ) * A + (p : ℤ) ^ (n + 2) * w := by
  have key : (1 + A) ^ p = ∑ m ∈ range (p + 1), A ^ m * (p.choose m : ℤ) := by
    rw [add_comm, add_pow]
    exact Finset.sum_congr rfl fun m _ => by rw [one_pow, mul_one]
  have hsplit := Finset.sum_Ico_consecutive (fun m => A ^ m * (p.choose m : ℤ))
    (Nat.zero_le 2) (show 2 ≤ p + 1 by omega)
  have hlow : ∑ m ∈ Finset.Ico 0 2, A ^ m * (p.choose m : ℤ) = 1 + (p : ℤ) * A := by
    rw [← Finset.range_eq_Ico, Finset.sum_range_succ, Finset.sum_range_one,
      Nat.choose_zero_right, Nat.choose_one_right]
    push_cast
    ring
  have hT : (p : ℤ) ^ (n + 2) ∣ ∑ m ∈ Finset.Ico 2 (p + 1), A ^ m * (p.choose m : ℤ) := by
    refine Finset.dvd_sum fun m hm => ?_
    obtain ⟨hm2, hmp⟩ := Finset.mem_Ico.mp hm
    have hAm : (p : ℤ) ^ (m * n) ∣ A ^ m := by
      rw [mul_comm, pow_mul]
      exact pow_dvd_pow_of_dvd hA m
    have h2n : 2 * n ≤ m * n := Nat.mul_le_mul hm2 (le_refl n)
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hmp) with hlt | hme
    · obtain ⟨c, hc⟩ :=
        Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self (by omega) hlt)
      obtain ⟨d, hd⟩ := hAm
      refine dvd_trans (pow_dvd_pow ((p : ℤ)) (show n + 2 ≤ m * n + 1 by omega)) ⟨d * c, ?_⟩
      rw [hd, hc]
      ring
    · have h3n : 3 * n ≤ m * n := Nat.mul_le_mul (by omega) (le_refl n)
      exact dvd_mul_of_dvd_left
        (dvd_trans (pow_dvd_pow ((p : ℤ)) (show n + 2 ≤ m * n by omega)) hAm) _
  obtain ⟨w, hw⟩ := hT
  exact ⟨w, by rw [key, Finset.range_eq_Ico, ← hsplit, hlow, hw]⟩

/-- The congruence `g_k(x) ≡ q_p(x)` modulo `p` with the integers exhibited: for every `k`
there is an integer `g` with `t_x ^ (p ^ k) - 1 = p ^ (k + 1) g` and `g ≡ q` modulo `p`,
where `t_x - 1 = p q`.

Induction on `k`, carrying the witness along: at `k = 0` the witness is `q` itself, and the
step expands `t_x ^ (p ^ (k + 1)) = (1 + p ^ (k + 1) g) ^ p` with
`one_add_pow_eq_of_pow_dvd`, whose error term contributes a multiple of `p` to the new
witness. -/
private theorem exists_witness_dvd_sub {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {t q : ℤ}
    (hq : t - 1 = (p : ℤ) * q) (k : ℕ) :
    ∃ g : ℤ, t ^ p ^ k - 1 = (p : ℤ) ^ (k + 1) * g ∧ (p : ℤ) ∣ g - q := by
  induction k with
  | zero => exact ⟨q, by simpa using hq, by simp⟩
  | succ k ih =>
    obtain ⟨g, hg, hgq⟩ := ih
    obtain ⟨w, hw⟩ :=
      one_add_pow_eq_of_pow_dvd hp hp3 (n := k + 1) (Nat.le_add_left 1 k) (Dvd.intro g rfl)
    refine ⟨g + (p : ℤ) * w, ?_, ?_⟩
    · have ht : t ^ p ^ k = 1 + (p : ℤ) ^ (k + 1) * g := by rw [← hg]; ring
      have hpow : t ^ p ^ (k + 1) = (1 + (p : ℤ) ^ (k + 1) * g) ^ p := by
        rw [pow_succ, pow_mul, ht]
      rw [hpow, hw]
      ring
    · obtain ⟨c, hc⟩ := hgq
      exact ⟨c + w, by linear_combination hc⟩

/-- **The unit quotient modulo `p`**: for an odd prime `p` with `p ∤ x`, the unit quotient
`g_k(x)` is congruent to the Fermat quotient `q_p(x)` modulo `p`.

The integers `g` and `q` are the ones provided by `GranvilleMoore.unitQuot_eq_intCast` and
`GranvilleMoore.fermatQuotient_eq_intCast`; they are unique, so the hypotheses `hg` and `hq` pin
them down. No hypothesis `p ∤ x` is needed here: it is what makes `g` and `q` exist, and `hg` and
`hq` already assert that. -/
theorem dvd_unitQuot_sub_fermatQuotient {p : ℕ} (hp : p.Prime) (hodd : Odd p) {x : ℤ}
    {k : ℕ} {g q : ℤ} (hg : unitQuot p x k = (g : ℚ))
    (hq : fermatQuotient p x = (q : ℚ)) : (p : ℤ) ∣ g - q := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    have : p % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hqz : x ^ (p - 1) - 1 = (p : ℤ) * q := by
    have h := natCast_mul_fermatQuotient hp.ne_zero x
    rw [hq] at h
    refine Int.cast_injective (α := ℚ) ?_
    push_cast
    linarith [h]
  obtain ⟨g₀, h₀, hg₀⟩ := exists_witness_dvd_sub hp hp3 hqz k
  have h5 : (x ^ (p - 1)) ^ p ^ k - 1 = (p : ℤ) ^ (k + 1) * g := by
    have := fermatUnit_pow_eq_one_add_pow_mul hp.ne_zero hg
    have h : (x ^ (p - 1)) ^ p ^ k = 1 + (p : ℤ) ^ (k + 1) * g := this
    rw [h]
    ring
  have hpz : ((p : ℤ)) ^ (k + 1) ≠ 0 :=
    pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.ne_zero)
  have : g = g₀ := mul_left_cancel₀ hpz (h5.symm.trans h₀)
  rw [this]
  exact hg₀

end GranvilleMoore
