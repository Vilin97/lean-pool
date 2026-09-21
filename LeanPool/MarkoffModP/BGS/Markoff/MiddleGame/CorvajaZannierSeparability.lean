/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierGeometry
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Derivation.Basic

/-!
# Prime-to-characteristic torsion exponents for Corvaja--Zannier

Corvaja--Zannier, Theorem 2, assumes that the two rational functions have nonzero
differentials.  In Corollary 2 those functions are coordinate powers whose exponents are
the orders of the two root-of-unity groups.  The source suppresses the resulting
prime-to-characteristic check.

For the actual Markoff application, both exponents are cardinalities of subgroups of the
multiplicative group of a finite field.  This file proves that they are prime to the
characteristic, that the associated root-of-unity polynomials are separable, and that
raising a nonzero coordinate with nonzero differential to either exponent preserves a
nonzero differential.  Thus inseparability is not part of the remaining
Corvaja--Zannier wall.
-/

namespace BGS.Markoff

open Polynomial

section FiniteFieldSubgroupOrders

variable {E : Type*} [Field E] [Fintype E]

/-- The order of a multiplicative subgroup of a finite field is prime to the field
characteristic.  This is the hidden separability check in the passage from
Corvaja--Zannier Theorem 2 to Corollary 2. -/
theorem characteristic_not_dvd_multiplicativeSubgroup_natCard
    (p : ℕ) [Fact p.Prime] [CharP E p] (H : Subgroup Eˣ) :
    ¬ p ∣ Nat.card H := by
  have hHdiv : Nat.card H ∣ Nat.card Eˣ := H.card_subgroup_dvd_card
  intro hpH
  have hpUnits : p ∣ Nat.card Eˣ := hpH.trans hHdiv
  rcases FiniteField.card E p with ⟨n, -, hcard⟩
  have hpE : p ∣ Nat.card E := by
    rw [← Fintype.card_eq_nat_card, hcard]
    exact dvd_pow_self p n.ne_zero
  have hdiff : Nat.card E - Nat.card Eˣ = 1 := by
    rw [Nat.card_eq_card_units_add_one E]
    omega
  have hpOne : p ∣ 1 := by
    rw [← hdiff]
    exact Nat.dvd_sub hpE hpUnits
  exact (Fact.out : p.Prime).not_dvd_one hpOne

/-- Both exponents occurring in the exact weighted torsion intersection are prime to the
characteristic. -/
theorem weightedTraceCurveTorsionIntersection_orders_primeToCharacteristic
    (p : ℕ) [Fact p.Prime] [CharP E p] (H₁ H₂ : Subgroup Eˣ) :
    ¬ p ∣ Nat.card H₁ ∧ ¬ p ∣ Nat.card H₂ :=
  ⟨characteristic_not_dvd_multiplicativeSubgroup_natCard p H₁,
    characteristic_not_dvd_multiplicativeSubgroup_natCard p H₂⟩

/-- The root-of-unity polynomial attached to an actual finite-field subgroup has no
inseparable multiplicity. -/
theorem multiplicativeSubgroup_torsionPolynomial_separable
    (p : ℕ) [Fact p.Prime] [CharP E p] (H : Subgroup Eˣ) :
    (Polynomial.X ^ Nat.card H - 1 : E[X]).Separable := by
  simpa only [Polynomial.C_1] using
    Polynomial.separable_X_pow_sub_C' p (Nat.card H) (1 : E)
      (characteristic_not_dvd_multiplicativeSubgroup_natCard p H) one_ne_zero

/-- The two torsion equations defining the exact geometric intersection are reduced. -/
theorem weightedTraceCurveTorsionIntersection_torsionPolynomials_separable
    (p : ℕ) [Fact p.Prime] [CharP E p] (H₁ H₂ : Subgroup Eˣ) :
    (Polynomial.X ^ Nat.card H₁ - 1 : E[X]).Separable ∧
      (Polynomial.X ^ Nat.card H₂ - 1 : E[X]).Separable :=
  ⟨multiplicativeSubgroup_torsionPolynomial_separable p H₁,
    multiplicativeSubgroup_torsionPolynomial_separable p H₂⟩

end FiniteFieldSubgroupOrders

section NonzeroDifferentials

variable {k L M : Type*} [CommRing k] [Field L] [AddCommGroup M] [Module L M]
  [Algebra k L] [Module k M]

/-- A prime-to-characteristic power of a nonzero function with nonzero differential
again has nonzero differential.  This is the exact derivation calculation used when
Corvaja--Zannier Theorem 2 is specialized to root-of-unity exponents. -/
theorem derivation_pow_ne_zero
    (D : Derivation k L M) (x : L) (n : ℕ)
    (hn : (n : L) ≠ 0) (hx : x ≠ 0) (hDx : D x ≠ 0) :
    D (x ^ n) ≠ 0 := by
  rw [D.leibniz_pow]
  rw [← Nat.cast_smul_eq_nsmul L, smul_smul]
  exact smul_ne_zero (mul_ne_zero hn (pow_ne_zero _ hx)) hDx

/-- Actual finite-field subgroup orders satisfy the nonzero-differential condition after
transport to any function field of the same characteristic. -/
theorem multiplicativeSubgroup_order_pow_has_nonzeroDifferential
    {E : Type*} [Field E] [Fintype E]
    (p : ℕ) [Fact p.Prime] [CharP E p] [CharP L p]
    (H : Subgroup Eˣ) (D : Derivation k L M) (x : L)
    (hx : x ≠ 0) (hDx : D x ≠ 0) :
    D (x ^ Nat.card H) ≠ 0 := by
  apply derivation_pow_ne_zero D x (Nat.card H)
  · rw [ne_eq, CharP.cast_eq_zero_iff L p]
    exact characteristic_not_dvd_multiplicativeSubgroup_natCard p H
  · exact hx
  · exact hDx

/-- The two coordinate powers in Corvaja--Zannier Corollary 2 retain nonzero
differentials for the exact pair of subgroup orders used in the Markoff middle game. -/
theorem weightedTraceCurveTorsionIntersection_coordinatePowers_haveNonzeroDifferentials
    {E : Type*} [Field E] [Fintype E]
    (p : ℕ) [Fact p.Prime] [CharP E p] [CharP L p]
    (H₁ H₂ : Subgroup Eˣ) (D : Derivation k L M) (x y : L)
    (hx : x ≠ 0) (hy : y ≠ 0) (hDx : D x ≠ 0) (hDy : D y ≠ 0) :
    D (x ^ Nat.card H₁) ≠ 0 ∧ D (y ^ Nat.card H₂) ≠ 0 :=
  ⟨multiplicativeSubgroup_order_pow_has_nonzeroDifferential p H₁ D x hx hDx,
    multiplicativeSubgroup_order_pow_has_nonzeroDifferential p H₂ D y hy hDy⟩

end NonzeroDifferentials

end BGS.Markoff
