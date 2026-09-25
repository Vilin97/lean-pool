/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.TameDifferentTrace
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.FieldTheory.Galois.Basic
/-!
# The different at a prime not dividing a Galois degree

The local factor P^e of q times the integer ring has absolute norm
q^(e*f). The Galois fundamental identity makes e*f a divisor of the
extension degree, so it is prime to q. The literal CRT trace witness then
proves that P^e does not divide the different. No completion comparison or
an assumed different-exponent formula is used.
-/

@[expose] public section

open scoped NumberField
open NumberField

noncomputable section

namespace AlgebraicNumberTheory.Discriminant

/-- A full ramification power cannot divide the different at a rational
prime that does not divide the finite Galois degree. -/
theorem ramification_power_not_dvd_differentIdeal_of_not_dvd_degree
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (q : ℕ) (hq : q.Prime) (P : Ideal (𝓞 L)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(q : ℤ)})]
    (hDegree : ¬ q ∣ Module.finrank ℚ L) :
    ¬ P ^ P.ramificationIdx ℤ ∣ differentIdeal ℤ (𝓞 L) := by
  classical
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  have : Fact q.Prime := ⟨hq⟩
  have hp0 : p ≠ ⊥ := by
    exact mt Ideal.span_singleton_eq_bot.mp (Int.natCast_ne_zero.mpr hq.ne_zero)
  have hpMap0 : p.map (algebraMap ℤ (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp0
  obtain ⟨Q, hPQ, hFactor⟩ := Ideal.eq_prime_pow_mul_coprime hpMap0 P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p P hpMap0]
    at hFactor
  have hNorm : (P ^ P.ramificationIdx ℤ).absNorm =
      q ^ (P.ramificationIdx ℤ * P.inertiaDeg ℤ) := by
    rw [map_pow, ← Ideal.pow_inertiaDeg q P, ← pow_mul, Nat.mul_comm]
  have hFundamental :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 L) Gal(L/ℚ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(L/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg p P Gal(L/ℚ),
    IsGalois.card_aut_eq_finrank] at hFundamental
  have hEF : P.ramificationIdx ℤ * P.inertiaDeg ℤ ∣ Module.finrank ℚ L := by
    refine ⟨(Ideal.primesOver p (𝓞 L)).ncard, ?_⟩
    simpa only [Nat.mul_comm] using hFundamental.symm
  exact not_dvd_differentIdeal_of_coprime_norm_exponent L q
    (P.ramificationIdx ℤ * P.inertiaDeg ℤ) hq
    (P ^ P.ramificationIdx ℤ) Q
    (IsCoprime.pow_left (Ideal.isCoprime_iff_sup_eq.mpr hPQ))
    hFactor.symm hNorm (fun h ↦ hDegree (h.trans hEF))

end AlgebraicNumberTheory.Discriminant
