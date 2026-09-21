/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Ring.Parity

/-!
# Rational square classes via `p`-adic valuations

Layer 1 of the Hasse–Minkowski development. A rational number `q` is a square in `ℚ`
if and only if `q` is nonnegative and every one of its `p`-adic valuations is even.

The proof reduces `q = q.num / q.den` to the corresponding statement for naturals: an
integer (resp. natural) is a square exactly when all exponents in its prime
factorization are even. Since `q.num` and `q.den` are coprime, at most one of them is
divisible by any given prime, so the evenness of the difference
`padicValRat p q = (q.num).factorization p - (q.den).factorization p`
forces the two exponents to be even individually.
-/

namespace HasseMinkowski

/-! ### Squares in `ℕ` -/

-- Theorem: a natural number is a square exactly when all the exponents in its prime
-- factorization are even. (Not available in Mathlib in this toolchain, so proved here.)
lemma isSquare_nat_iff_even_factorization {n : ℕ} :
    IsSquare n ↔ ∀ p : ℕ, p.Prime → Even (n.factorization p) := by
  constructor
  · rintro ⟨m, rfl⟩ p hp
    by_cases hm : m = 0
    · simp [hm]
    · rw [Nat.factorization_mul hm hm]
      exact ⟨m.factorization p, rfl⟩
  · intro h
    by_cases hn : n = 0
    · exact ⟨0, by simp [hn]⟩
    obtain ⟨b, a, hab, ha⟩ := exists_sq_mul_squarefree n
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hn (by simpa using hab.symm)
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hn (by simpa using hab.symm)
    have ha1 : a = 1 := by
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hfac1 : a.factorization p = 1 :=
        Nat.factorization_eq_one_of_squarefree ha hp hpd
      have hfac : n.factorization p = 2 * b.factorization p + 1 := by
        rw [← hab, Nat.factorization_mul (pow_ne_zero 2 hb0) ha0, Nat.factorization_pow]
        simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
        rw [hfac1]
      obtain ⟨c, hc⟩ := h p hp
      rw [hfac] at hc
      omega
    exact ⟨b, by rw [← hab, ha1, mul_one, pow_two]⟩

-- Theorem: if `a` and `b` are coprime naturals, then for any prime `p` at most one of
-- `a.factorization p`, `b.factorization p` is nonzero.
lemma factorization_eq_zero_or_eq_zero_of_coprime {a b p : ℕ} (hp : p.Prime)
    (hab : Nat.Coprime a b) : a.factorization p = 0 ∨ b.factorization p = 0 := by
  rcases eq_or_ne (a.factorization p) 0 with h | h
  · exact Or.inl h
  rcases eq_or_ne (b.factorization p) 0 with h' | h'
  · exact Or.inr h'
  exfalso
  have ha : a ≠ 0 := by rintro rfl; simp at h
  have hb : b ≠ 0 := by rintro rfl; simp at h'
  have hpa : p ∣ a :=
    (hp.dvd_iff_one_le_factorization ha).mpr (Nat.one_le_iff_ne_zero.mpr h)
  have hpb : p ∣ b :=
    (hp.dvd_iff_one_le_factorization hb).mpr (Nat.one_le_iff_ne_zero.mpr h')
  have hpg : p ∣ 1 := by
    have := Nat.dvd_gcd hpa hpb
    rwa [hab] at this
  exact hp.ne_one (Nat.dvd_one.mp hpg)

/-! ### Rational squares via `p`-adic valuations

Since `q.num` and `q.den` are coprime, at most one of them is divisible by a given
prime `p`, so only one of the two exponents in `padicValRat p q` is nonzero. Evenness
of the difference therefore forces evenness of each exponent separately, which by
`isSquare_nat_iff_even_factorization` makes both `q.num` and `q.den` squares. -/

-- Theorem: the `p`-adic valuation of a nonzero rational is the difference of the
-- `p`-adic valuations (prime factorizations) of its numerator and denominator.
lemma padicValRat_eq_factorization {q : ℚ} (_hq : q ≠ 0) {p : ℕ} (hp : p.Prime) :
    padicValRat p q =
      (q.num.natAbs.factorization p : ℤ) - (q.den.factorization p : ℤ) := by
  simp only [padicValRat, padicValInt]
  rw [Nat.padicValNat_def, Nat.padicValNat_def,
    Nat.multiplicity_eq_factorization hp,
    Nat.multiplicity_eq_factorization hp]

-- Theorem: if `q : ℚ` is a square then all of its `p`-adic valuations are even.
theorem even_padicValRat_of_isSquare {q : ℚ} (hq : IsSquare q) (p : ℕ) (hp : p.Prime) :
    Even (padicValRat p q) := by
  obtain ⟨r, rfl⟩ := hq
  by_cases hr : r = 0
  · simp [hr]
  · rw [padicValRat.mul (p := p) (hp := Fact.mk hp) hr hr]
    exact ⟨padicValRat p r, rfl⟩

-- Theorem: a square rational is nonnegative.
theorem nonneg_of_isSquare {q : ℚ} (hq : IsSquare q) : 0 ≤ q :=
  hq.nonneg

-- Theorem: for `q : ℚ`, `q` is a square iff `q ≥ 0` and every `p`-adic valuation
-- of `q` is even.
theorem Rat.isSquare_iff_even_padicValRat {q : ℚ} :
    IsSquare q ↔ 0 ≤ q ∧ ∀ p : ℕ, p.Prime → Even (padicValRat p q) := by
  constructor
  · intro hq
    exact ⟨hq.nonneg, even_padicValRat_of_isSquare hq⟩
  · rintro ⟨hq0, h⟩
    by_cases hq : q = 0
    · exact ⟨0, by simp [hq]⟩
    have hc : Nat.Coprime q.num.natAbs q.den := q.reduced
    have heven : ∀ p : ℕ, p.Prime →
        Even (q.num.natAbs.factorization p) ∧ Even (q.den.factorization p) := by
      intro p hp
      have hdiff : Even ((q.num.natAbs.factorization p : ℤ) -
          (q.den.factorization p : ℤ)) := by
        rw [← padicValRat_eq_factorization hq hp]
        exact h p hp
      rcases factorization_eq_zero_or_eq_zero_of_coprime hp hc with hA | hB
      · have hA' : Even (q.num.natAbs.factorization p) := by rw [hA]; exact Even.zero
        have hB' : Even (q.den.factorization p) := by
          have hx : ((q.num.natAbs.factorization p : ℤ)) = 0 := by rw [hA]; simp
          have : Even (-(q.den.factorization p : ℤ)) := by
            rwa [hx, zero_sub] at hdiff
          exact (Int.even_coe_nat (q.den.factorization p)).mp (even_neg.mp this)
        exact ⟨hA', hB'⟩
      · have hA' : Even (q.num.natAbs.factorization p) := by
          have hy : ((q.den.factorization p : ℤ)) = 0 := by rw [hB]; simp
          have : Even ((q.num.natAbs.factorization p : ℤ)) := by
            rwa [hy, sub_zero] at hdiff
          exact (Int.even_coe_nat (q.num.natAbs.factorization p)).mp this
        have hB' : Even (q.den.factorization p) := by rw [hB]; exact Even.zero
        exact ⟨hA', hB'⟩
    have hden_sq : IsSquare q.den :=
      isSquare_nat_iff_even_factorization.mpr fun p hp => (heven p hp).2
    have hnumAbs_sq : IsSquare q.num.natAbs :=
      isSquare_nat_iff_even_factorization.mpr fun p hp => (heven p hp).1
    have hnonneg : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
    have hnum_sq : IsSquare q.num := by
      rw [← Int.natAbs_of_nonneg hnonneg]
      exact Int.isSquare_natCast_iff.mpr hnumAbs_sq
    exact Rat.isSquare_iff.mpr ⟨hnum_sq, hden_sq⟩

-- Theorem: a nonnegative rational all of whose `p`-adic valuations are even is a
-- square.
theorem isSquare_of_nonneg_of_even_padicValRat {q : ℚ} (hq : 0 ≤ q)
    (h : ∀ p : ℕ, p.Prime → Even (padicValRat p q)) : IsSquare q :=
  Rat.isSquare_iff_even_padicValRat.mpr ⟨hq, h⟩

end HasseMinkowski
