/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.MultiQuadratic.Order

/-!
# Legendre choice and reduction of the multiquadratic order

Blueprint nodes L01 and L02: at least one of `ℓ`, `ℓ'`, `ℓℓ'` is a square in a finite field
of odd prime cardinality, and a choice of square roots of the `rⱼ` induces a reduction map
`𝒪_r → F`.
-/

@[expose] public section

open MvPolynomial

namespace Nikodym.MultiQuad

noncomputable section

variable {m : ℕ}

/-- Blueprint L01: a field of prime cardinality `q` has characteristic `q`. -/
theorem charP_of_card_prime {F : Type*} [Field F] [Fintype F]
    (hp : (Fintype.card F).Prime) : CharP F (Fintype.card F) := by
  obtain ⟨p, hchar, n, -, hcard⟩ := FiniteField.card' F
  have hpk : p ^ (n : ℕ) = Fintype.card F := hcard.symm
  have hpn : p = Fintype.card F ∧ (n : ℕ) = 1 := (Nat.Prime.pow_eq_iff hp).mp hpk
  exact CharP.congr p hpn.1

/-- Blueprint L01: a prime strictly smaller than `|F|` remains nonzero in a
prime-cardinality field `F`. -/
theorem natCast_ne_zero_of_lt_card {F : Type*} [Field F] [Fintype F]
    (hp : (Fintype.card F).Prime) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hlt : ℓ < Fintype.card F) : (ℓ : F) ≠ 0 := by
  have : CharP F (Fintype.card F) := charP_of_card_prime hp
  intro h0
  have hdvd : Fintype.card F ∣ ℓ := (CharP.cast_eq_zero_iff F (Fintype.card F) ℓ).mp h0
  rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | heq
  · exact hp.ne_one h1
  · exact (ne_of_lt hlt) heq.symm

/-- Blueprint L01: in a finite field of odd prime cardinality, at least one of `ℓ`, `ℓ'`,
`ℓℓ'` is a square. -/
theorem exists_isSquare_of_primes {F : Type*} [Field F] [Fintype F]
    (hp : (Fintype.card F).Prime) (hodd : Odd (Fintype.card F)) {ℓ ℓ' : ℕ}
    (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (h1 : ℓ < Fintype.card F)
    (h2 : ℓ' < Fintype.card F) :
    IsSquare (ℓ : F) ∨ IsSquare (ℓ' : F) ∨ IsSquare ((ℓ * ℓ' : ℕ) : F) := by
  classical
  have hℓ0 : (ℓ : F) ≠ 0 := natCast_ne_zero_of_lt_card hp hℓ h1
  have hℓ'0 : (ℓ' : F) ≠ 0 := natCast_ne_zero_of_lt_card hp hℓ' h2
  have _hne2 : ringChar F ≠ 2 := by
    intro hchar2
    have : Fintype.card F % 2 = 0 := FiniteField.even_card_of_char_two hchar2
    rw [Nat.odd_iff] at hodd
    omega
  have hprod0 : ((ℓ : F) * (ℓ' : F)) ≠ 0 := mul_ne_zero hℓ0 hℓ'0
  rcases quadraticChar_dichotomy hℓ0 with hχ | hχ
  · exact Or.inl ((quadraticChar_one_iff_isSquare hℓ0).mp hχ)
  · rcases quadraticChar_dichotomy hℓ'0 with hχ' | hχ'
    · exact Or.inr (Or.inl ((quadraticChar_one_iff_isSquare hℓ'0).mp hχ'))
    · refine Or.inr (Or.inr ?_)
      have hχprod : quadraticChar F ((ℓ : F) * (ℓ' : F)) = 1 := by
        rw [map_mul, hχ, hχ']
        norm_num
      rw [Nat.cast_mul]
      exact (quadraticChar_one_iff_isSquare hprod0).mp hχprod

/-- Blueprint L02: a choice of square roots `sⱼ² = rⱼ` in `F` induces `𝒪_r → F`. -/
def reduce (r : Fin m → ℕ) {F : Type*} [Field F] (s : Fin m → F)
    (hs : ∀ j, s j ^ 2 = (r j : F)) : Order r →+* F :=
  Ideal.Quotient.lift _ (eval₂Hom (Int.castRingHom F) s)
    (eval₂Hom_eq_zero_of_mem_relIdeal r (Int.castRingHom F) s fun j => by
      simpa using hs j)

/-- Blueprint L02: reduction sends `gen j` to `s j`. -/
@[simp]
theorem reduce_gen (r : Fin m → ℕ) {F : Type*} [Field F] (s : Fin m → F)
    (hs : ∀ j, s j ^ 2 = (r j : F)) (j : Fin m) :
    reduce r s hs (gen r j) = s j := by
  simp [reduce, gen]

/-- Blueprint L02: reduction sends integers to themselves. -/
theorem reduce_intCast (r : Fin m → ℕ) {F : Type*} [Field F] (s : Fin m → F)
    (hs : ∀ j, s j ^ 2 = (r j : F)) (z : ℤ) :
    reduce r s hs z = z :=
  map_intCast _ _

/-- Blueprint L02: reduction of a monomial is the product of the chosen square roots. -/
theorem reduce_mono (r : Fin m → ℕ) {F : Type*} [Field F] (s : Fin m → F)
    (hs : ∀ j, s j ^ 2 = (r j : F)) (S : Finset (Fin m)) :
    reduce r s hs (mono r S) = ∏ j ∈ S, s j := by
  simp [mono_eq_prod_gen, map_prod, reduce_gen]

end

end Nikodym.MultiQuad

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
