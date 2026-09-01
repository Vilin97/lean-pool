/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Auxiliary results on p-adic valuations

Valuations of products, gcds and casts, and integrality via valuations. (No longer used by
the project itself — the corresponding steps now run through the UFD `factorization` API — but
kept as self-contained upstreaming candidates.)

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[simp]
theorem padicValInt_neg (p : ℕ) (a : ℤ) : padicValInt p (-a) = padicValInt p a := by
  simp only [padicValInt, Int.natAbs_neg]

/-- Over `ℤ`, the multiplicity of a positive prime `p` (count of normalized factors) is the
`p`-adic valuation. -/
theorem factorization_int_eq_padicValInt (p : ℕ) [Fact p.Prime] {x : ℤ} (hx : x ≠ 0) :
    factorization x ((p : ℕ) : ℤ) = padicValInt p x := by
  have hirr : Irreducible ((p : ℕ) : ℤ) :=
    (Int.prime_iff_natAbs_prime.mpr (by simpa using Fact.out)).irreducible
  have h1 : (factorization x ((p : ℕ) : ℤ) : ℕ∞)
      = emultiplicity ((p : ℕ) : ℤ) x := by
    rw [factorization_eq_count,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hirr hx,
      Int.normalize_of_nonneg (by positivity)]
  have h2 : emultiplicity ((p : ℕ) : ℤ) x = emultiplicity p x.natAbs := by
    rw [emultiplicity_eq_emultiplicity_iff]
    intro n
    rw [← Int.natAbs_dvd_natAbs]
    simp [Int.natAbs_pow]
  have h3 : (padicValInt p x : ℕ∞) = emultiplicity p x.natAbs :=
    padicValNat_eq_emultiplicity (Int.natAbs_ne_zero.mpr hx)
  exact_mod_cast h1.trans (h2.trans h3.symm)

/-- The `p`-adic valuation of a `gcd` is the minimum of the valuations. -/
theorem padicValNat_gcd (p : ℕ) [Fact p.Prime] {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (Nat.gcd a b) = min (padicValNat p a) (padicValNat p b) := by
  rw [← Nat.factorization_def _ Fact.out, ← Nat.factorization_def _ Fact.out,
    ← Nat.factorization_def _ Fact.out, Nat.factorization_gcd ha hb, Finsupp.inf_apply]

/-- The `p`-adic valuation is additive over a finite product of nonzero rationals. -/
theorem padicValRat_prod {ι : Type*} (p : ℕ) [Fact (Nat.Prime p)] (s : Finset ι)
    (f : ι → ℚ) (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValRat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValRat p (f x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ x ∈ s, f x ≠ 0 := fun x hx ↦ hf x (Finset.mem_insert_of_mem hx)
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih hs,
      padicValRat.mul (hf a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 hs)]

/-- A rational whose `p`-adic valuation is nonnegative at every prime is an integer (`den = 1`). -/
theorem Rat.den_eq_one_of_padicValRat_nonneg (q : ℚ)
    (h : ∀ (p : ℕ) [Fact (Nat.Prime p)], 0 ≤ padicValRat p q) : q.den = 1 := by
  by_contra hden
  obtain ⟨p, hp, hpd⟩ := (q.den).exists_prime_and_dvd hden
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hpnum : ¬ (p : ℤ) ∣ q.num := fun hpn ↦
    hp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left
      (by simpa using Int.natAbs_dvd_natAbs.mpr hpn) q.reduced).eq_one_of_dvd hpd)
  have hden1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.pos.ne' hpd
  have hh := h p
  rw [padicValRat_def p q, padicValInt.eq_zero_of_not_dvd hpnum] at hh
  lia
