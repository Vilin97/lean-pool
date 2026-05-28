/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/

import LeanPool.OrderPQ.Basic

namespace OrderPQ

-- Let `p` and `q` be prime numbers.
variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- There exists a noncyclic group `G` of order `p * q` if and only if `p` equals `q` or `p` divides
  `q - 1` or `q` divides `p - 1`. -/
theorem exists_card_eq_prime_mul_prime_and_not_isCyclic_iff :
    (∃ (G : Type) (_ : Group G), Nat.card G = p * q ∧ ¬IsCyclic G)
    ↔ p = q ∨ p ∣ q - 1 ∨ q ∣ p - 1 := by
  constructor
  · rintro ⟨G, _, h1, h2⟩
    contrapose! h2
    exact isCyclic_of_card_eq_prime_mul_prime' h1 h2
  · rintro (h1 | h2 | h3)
    · use MulZMod p × MulZMod p, Prod.instGroup
      rw [Nat.card_prod, nat_card_mulZMod, h1.symm, not_isCyclic_iff_exponent_eq_prime hp.elim]
      · simp [Monoid.exponent_prod, IsCyclic.exponent_eq_card]
      · simp [p.pow_two.symm]
    · exact exists_group_card_eq_prime_mul_prime_and_not_isCyclic h2
    · exact mul_comm p q ▸ exists_group_card_eq_prime_mul_prime_and_not_isCyclic h3

/-- Any two noncyclic groups of order `p * q` are isomorphic. -/
theorem nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic
    {G1 : Type*} [Group G1] (h1 : Nat.card G1 = p * q) (h1' : ¬IsCyclic G1)
    {G2 : Type*} [Group G2] (h2 : Nat.card G2 = p * q) (h2' : ¬IsCyclic G2) :
    Nonempty (G1 ≃* G2) := by
  obtain (heq | hlt | hgt) : p = q ∨ p < q ∨ p > q := Iff.subst Nat.lt_or_gt (em (p = q))
  · rw [← heq, ← p.pow_two] at h1 h2
    exact Nonempty.map2 (fun x y => x.trans y.symm)
      (nonempty_mulEquiv_prod_of_card_eq_prime_pow_two_of_not_isCyclic h1 h1')
      (nonempty_mulEquiv_prod_of_card_eq_prime_pow_two_of_not_isCyclic h2 h2')
  · exact nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic' hlt h1 h1' h2 h2'
  · exact nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic'
      hgt (mul_comm p q ▸ h1) h1' (mul_comm p q ▸ h2) h2'

/-- Every noncyclic group of order `p ^ 2` is isomorphic to the direct product of `MulZMod p` with
  itself. -/
theorem nonempty_mulEquiv_prod_of_card_eq_prime_pow_two_of_not_isCyclic
    {G : Type*} [Group G] (h : Nat.card G = p ^ 2) (h' : ¬IsCyclic G) :
    Nonempty (G ≃* MulZMod p × MulZMod p) :=
  _root_.nonempty_mulEquiv_prod_of_card_eq_prime_pow_two_of_not_isCyclic h h'

/-- If `p < q`, then for any noncyclic group `G` of order `p * q` there exists a homomorphism `φ`
  from `MulZMod p` to the automorphism group of `MulZMod q` such that `G` is isomorphic to the
  semidirect product of `MulZMod q` and `MulZMod p` defined by `φ`. -/
theorem nonempty_mulEquiv_semidirectProduct_of_card_eq_prime_mul_prime
    (hpq : p < q) {G : Type*} [Group G] (h : Nat.card G = p * q) :
    ∃ φ : MulZMod p →* MulAut (MulZMod q), Nonempty (G ≃* MulZMod q ⋊[φ] MulZMod p) :=
  _root_.nonempty_mulEquiv_semidirectProduct_of_card_eq_prime_mul_prime hpq h

/-- If `p < q`, then every noncyclic group of order `p * q` is isomorphic to the semidirect product
  of `MulZMod q` and `MulZMod p` defined by any nontrivial homomorphism from `MulZMod p` to the
  automorphism group of `MulZMod q`. -/
theorem nonempty_mulEquiv_semidirectProduct_of_card_eq_prime_mul_prime_of_not_isCyclic
    (hpq : p < q) {G : Type*} [Group G] (h : Nat.card G = p * q) (h' : ¬IsCyclic G)
    (φ : MulZMod p →* MulAut (MulZMod q)) (hφ : φ ≠ 1) :
    Nonempty (G ≃* MulZMod q ⋊[φ] MulZMod p) := by
  have ⟨_, ⟨hφ1, hne⟩⟩ := exists_monoidHom_ne_one_and_nonempty_mulEquiv_semidirectProduct hpq h h'
  refine hne.elim fun ψ1 => ?_
  exact (nonempty_mulEquiv_mulZMod_prime_semidirectProduct_mulZMod_prime hφ1 hφ).elim
    fun ψ2 => ⟨MulEquiv.trans ψ1 ψ2⟩

end OrderPQ
