/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/

import LeanPool.LehmerE10.Kronecker
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-!
# no cyclotomic polynomial divides Lehmer's polynomial, and the
characteristic-polynomial identity conditional on irreducibility.
`no_cyclotomic_divisor`: no cyclotomic polynomial divides `L`.  One uniform
argument, using that 2 is a primitive root mod `1291 = L(2)` (order 1290):
  Φ_k ∣ L  ⟹  Φ_k(2) ∣ L(2) = 1291 (prime), and |Φ_k(2)| ≥ 2 (Mathlib's
  `sub_one_lt_natAbs_cyclotomic_eval`)  ⟹  |Φ_k(2)| = 1291  ⟹  1291 ∣ 2^k − 1
  ⟹  1290 = ord₁₂₉₁(2) ∣ k  ⟹  336 = φ(1290) ∣ φ(k)  (`totient_dvd_of_dvd`)
  — but Φ_k ∣ L forces φ(k) = deg Φ_k ≤ 10.  Contradiction.  (k = 1: L(1) = −1.)
`charpoly_eq_lehmer_of_irreducible`: if `L` is irreducible over ℚ, then any 10×10
integer matrix annihilated by `L` has characteristic polynomial `L` (over ℚ), via
Cayley–Hamilton + minimal-polynomial divisibility + degree count.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace LehmerE10

open Polynomial

/-! ### The primitive-root certificate: ord₁₂₉₁(2) = 1290. -/

instance : Fact (Nat.Prime 1291) := ⟨witness_1291_prime⟩

set_option maxRecDepth 40000 in
/-- 2 has order exactly 1290 = 2·3·5·43 in (ℤ/1291)ˣ — certified by Fermat plus the
    four maximal-divisor refusals (kernel bignum arithmetic). -/
theorem orderOf_two_mod_1291 : orderOf (2 : ZMod 1291) = 1290 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · have h := ZMod.pow_card_sub_one_eq_one (p := 1291) (a := 2) (by decide)
    simpa using h
  · intro p hp hdvd
    -- p prime ∣ 1290 = 2·3·5·43 ⟹ p ∈ {2,3,5,43}, by the prime-divisor chain
    have hc1 : p = 2 ∨ p ∣ 645 := by
      rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 645 from hdvd) with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      · exact Or.inr h
    have hcase : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 43 := by
      rcases hc1 with h | h645
      · exact Or.inl h
      have hc2 : p = 3 ∨ p ∣ 215 := by
        rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 3 * 215 from h645) with h | h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
        · exact Or.inr h
      rcases hc2 with h | h215
      · exact Or.inr (Or.inl h)
      rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 5 * 43 from h215) with h | h
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))
      · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))
    rcases hcase with rfl | rfl | rfl | rfl
    · decide  -- p = 2 : 2^645 ≠ 1
    · decide  -- p = 3 : 2^430 ≠ 1
    · decide  -- p = 5 : 2^258 ≠ 1
    · decide  -- p = 43 : 2^30 ≠ 1

/-! ### LEG (a): the uniform cyclotomic kill. -/

/-- **NO CYCLOTOMIC DIVIDES LEHMER (proven)** — the uniform 1291 argument. -/
theorem no_cyclotomic_divisor {k : ℕ} (hk : 1 ≤ k) :
    ¬ (cyclotomic k ℤ ∣ lehmerPolynomial) := by
  intro hdvd
  rcases Nat.eq_or_lt_of_le hk with h1 | h2
  · -- k = 1 : X − 1 ∣ L would force L(1) = 0, but L(1) = −1
    have : (cyclotomic 1 ℤ).eval 1 ∣ lehmerPolynomial.eval 1 := eval_dvd (h1 ▸ hdvd)
    rw [cyclotomic_one, lehmer_eval_one] at this
    simp at this
  -- k ≥ 2
  have hφ10 : k.totient ≤ 10 := by
    have := Polynomial.natDegree_le_of_dvd hdvd lehmerPolynomial_ne_zero
    rwa [natDegree_cyclotomic, lehmerPolynomial_natDegree] at this
  -- Φ_k(2) divides the prime 1291 and exceeds 1 in absolute value
  have hdvd1291 : (cyclotomic k ℤ).eval 2 ∣ 1291 := by
    have := eval_dvd (x := (2 : ℤ)) hdvd
    rwa [lehmer_eval_two] at this
  have hgt1 : 1 < ((cyclotomic k ℤ).eval 2).natAbs := by
    have h := Polynomial.sub_one_lt_natAbs_cyclotomic_eval (n := k) (q := 2) h2 (by norm_num)
    simpa using h
  have habs : ((cyclotomic k ℤ).eval 2).natAbs = 1291 := by
    have hdvdN : ((cyclotomic k ℤ).eval 2).natAbs ∣ 1291 := by
      have := Int.natAbs_dvd_natAbs.mpr hdvd1291
      simpa using this
    rcases (Nat.Prime.eq_one_or_self_of_dvd witness_1291_prime _ hdvdN) with h | h
    · omega
    · exact h
  -- hence 1291 ∣ 2^k − 1
  have hdvd2k : (1291 : ℤ) ∣ 2 ^ k - 1 := by
    have hΦdvd : (cyclotomic k ℤ).eval 2 ∣ (2 : ℤ) ^ k - 1 := by
      have := eval_dvd (x := (2 : ℤ)) (cyclotomic.dvd_X_pow_sub_one k ℤ)
      simpa using this
    have := Int.natAbs_dvd.mpr hΦdvd
    rwa [habs] at this
  -- pass to ZMod 1291: 2^k = 1, so 1290 ∣ k
  have hzmod : (2 : ZMod 1291) ^ k = 1 := by
    have h0 : ((2 ^ k - 1 : ℤ) : ZMod 1291) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd2k
    push_cast at h0
    linear_combination h0
  have hord : (1290 : ℕ) ∣ k := by
    have := orderOf_dvd_of_pow_eq_one hzmod
    rwa [orderOf_two_mod_1291] at this
  -- totient divisibility: 336 = φ(1290) ∣ φ(k) ≤ 10
  have h336 : (336 : ℕ) ∣ k.totient := by
    have := Nat.totient_dvd_of_dvd hord
    rwa [show Nat.totient 1290 = 336 from by
      set_option maxRecDepth 40000 in decide] at this
  have hpos : 0 < k.totient := Nat.totient_pos.mpr (by omega)
  have := Nat.le_of_dvd hpos h336
  omega

/-! ### The charpoly identity, conditional on irreducibility. -/

/-- If Lehmer's polynomial is irreducible over ℚ, then any 10×10 integer matrix it
    annihilates has characteristic polynomial `L` over ℚ.
    (Cayley–Hamilton gives minpoly ∣ charpoly; annihilation gives minpoly ∣ L;
    irreducibility forces minpoly = L; degree 10 monic on both sides closes it.) -/
theorem charpoly_eq_lehmer_of_irreducible {M : Matrix (Fin 10) (Fin 10) ℤ}
    (hann : (Polynomial.aeval M) lehmerPolynomial = 0)
    (hirr : Irreducible (lehmerPolynomial.map (Int.castRingHom ℚ))) :
    (M.map (Int.castRingHom ℚ)).charpoly =
      lehmerPolynomial.map (Int.castRingHom ℚ) := by
  set Cq := M.map (Int.castRingHom ℚ) with hCq
  set Lq := lehmerPolynomial.map (Int.castRingHom ℚ) with hLq
  have hLmonic : Lq.Monic := lehmerPolynomial_monic.map _
  have hLdeg : Lq.natDegree = 10 := by
    rw [hLq, lehmerPolynomial_monic.natDegree_map]; exact lehmerPolynomial_natDegree
  -- the annihilation over ℚ, by pushing the entry-cast ring hom through eval₂
  have hannQ : (Polynomial.aeval Cq) Lq = 0 := by
    have h2 := congrArg (RingHom.mapMatrix (Int.castRingHom ℚ)
      (m := Fin 10)) hann
    rw [map_zero, aeval_def, Polynomial.hom_eval₂] at h2
    rw [hLq, aeval_def, Polynomial.eval₂_map]
    have hcomp : ((RingHom.mapMatrix (Int.castRingHom ℚ) (m := Fin 10)).comp
        (algebraMap ℤ (Matrix (Fin 10) (Fin 10) ℤ))) =
        ((algebraMap ℚ (Matrix (Fin 10) (Fin 10) ℚ)).comp (Int.castRingHom ℚ)) :=
      RingHom.ext_int _ _
    rw [hcomp] at h2
    exact h2
  -- minpoly divides both L and charpoly
  have hminL : minpoly ℚ Cq ∣ Lq := minpoly.dvd ℚ Cq hannQ
  have hminC : minpoly ℚ Cq ∣ Cq.charpoly := Cq.minpoly_dvd_charpoly
  -- irreducibility: minpoly = L (both monic, minpoly nonunit divisor)
  have hint : IsIntegral ℚ Cq := Matrix.isIntegral Cq
  have hmin_eq : minpoly ℚ Cq = Lq := by
    obtain ⟨g, hg⟩ := hminL
    rcases hirr.isUnit_or_isUnit hg with h | h
    · exact absurd h (minpoly.not_isUnit ℚ Cq)
    · obtain ⟨c, hcu, hc⟩ := Polynomial.isUnit_iff.mp h
      have hLg : Lq = minpoly ℚ Cq * Polynomial.C c := by rw [hg, hc]
      have hlead := congrArg Polynomial.leadingCoeff hLg
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        (minpoly.monic hint).leadingCoeff, one_mul, hLmonic.leadingCoeff] at hlead
      rw [hLg, ← hlead, Polynomial.C_1, mul_one]
  -- charpoly: monic, degree 10, divisible by the degree-10 monic minpoly ⟹ equal
  have hchdeg : Cq.charpoly.natDegree = 10 := by
    simp
  have hchmonic : Cq.charpoly.Monic := Cq.charpoly_monic
  have hdvd : Lq ∣ Cq.charpoly := hmin_eq ▸ hminC
  obtain ⟨u, hu⟩ := hdvd
  have hudeg : u.natDegree = 0 := by
    have h0 : Cq.charpoly ≠ 0 := hchmonic.ne_zero
    have := congrArg Polynomial.natDegree hu
    rw [Polynomial.natDegree_mul hLmonic.ne_zero (by rintro rfl; rw [mul_zero] at hu; exact h0 hu),
      hchdeg, hLdeg] at this
    omega
  have hulead : u.leadingCoeff = 1 := by
    have := congrArg Polynomial.leadingCoeff hu
    rwa [Polynomial.leadingCoeff_mul, hLmonic.leadingCoeff, hchmonic.leadingCoeff,
      one_mul, eq_comm] at this
  have hu1 : u = 1 := by
    have := Polynomial.eq_C_of_natDegree_eq_zero hudeg
    rw [this]
    rw [this, Polynomial.leadingCoeff_C] at hulead
    rw [hulead, Polynomial.C_1]
  rw [hu, hu1, mul_one]


end LehmerE10
