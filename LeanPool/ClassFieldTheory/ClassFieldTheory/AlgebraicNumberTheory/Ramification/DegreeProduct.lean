/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.InertiaCardinality
/-!
# A finite-group degree product

Once the chosen inertia groups generate the full abelian Galois group and
their orders satisfy the local prime-power bounds, the global degree is at
most the totient of the conductor candidate.  This file isolates that finite
group calculation from the arithmetic construction of the chosen primes.
-/

noncomputable section

namespace AlgebraicNumberTheory.Ramification

open RamificationTheory
open scoped BigOperators IsMulCommutative

/-- Euler's totient is multiplicative on a finite product of powers of
distinct primes. -/
theorem totient_prod_primePowers
    (S : Finset Nat.Primes) (e : Nat.Primes → ℕ) :
    Nat.totient (∏ p ∈ S, p.1 ^ e p) =
      ∏ p ∈ S, Nat.totient (p.1 ^ e p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      have hcoprime : Nat.Coprime (p.1 ^ e p) (∏ q ∈ S, q.1 ^ e q) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        apply Nat.Coprime.pow_left
        apply Nat.Coprime.pow_right
        exact (Nat.coprime_primes p.2 q.2).2
          (Subtype.coe_ne_coe.mpr fun hpq => hp (hpq.symm ▸ hq))
      rw [Finset.prod_insert hp, Finset.prod_insert hp,
        Nat.totient_mul hcoprime, ih]

/-- The finite-group degree bound obtained from the inertia subgroups. -/
theorem finrank_le_totient_prod_primePowers_of_inertia_bounds
    (M : Type) [Field M] [Algebra ℚ M]
    [FiniteDimensional ℚ M] [IsAbelianGalois ℚ M]
    (S : Finset Nat.Primes) (e : Nat.Primes → ℕ)
    (I : Nat.Primes → Subgroup (M ≃ₐ[ℚ] M))
    (hgenerate : S.sup I = ⊤)
    (hcard : ∀ p ∈ S, Nat.card (I p) ≤ Nat.totient (p.1 ^ e p)) :
    Module.finrank ℚ M ≤
      Nat.totient (∏ p ∈ S, p.1 ^ e p) := by
  let : Finite (M ≃ₐ[ℚ] M) := inferInstance
  calc
    Module.finrank ℚ M = Nat.card (M ≃ₐ[ℚ] M) :=
      (IsGalois.card_aut_eq_finrank ℚ M).symm
    _ = Nat.card (S.sup I : Subgroup (M ≃ₐ[ℚ] M)) := by
      rw [hgenerate]
      simp
    _ ≤ ∏ p ∈ S, Nat.card (I p) :=
      natCard_finsetSup_le_prod_natCard
        (G := M ≃ₐ[ℚ] M) (ι := Nat.Primes) S I
    _ ≤ ∏ p ∈ S, Nat.totient (p.1 ^ e p) := by
      exact Finset.prod_le_prod (fun p hp => hcard p hp)
    _ = Nat.totient (∏ p ∈ S, p.1 ^ e p) :=
      (totient_prod_primePowers S e).symm

end AlgebraicNumberTheory.Ramification

end
