/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm.Noetherian
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm.Polynomial

/-!
# Elementary factorization of analytic germs

[Jakóbczak–Jarnicki][JakobczakJarnicki2021], Proposition 1.8.4: scalar analytic germ rings in
finite dimension are unique factorization domains. The analytic ingredient is that an
irreducible germ is prime. Together with Noetherianity this supplies Mathlib's
`UniqueFactorizationMonoid` instance and its usual existence and uniqueness results.

The source's “relatively prime” is expressed as `IsRelPrime`, meaning that common divisors are
units. It is not `IsCoprime`: two germs vanishing at the base point cannot generate the unit
ideal. No geometric conclusions from §1.8.5 are included.

## Main results

* `prime_of_irreducible`: Irreducible analytic germs are prime in finite dimension: transport to the
  origin of a coordinate presentation using the induction on dimension above.
* `exists_prime_factors`: Every nonzero analytic germ is associated to a finite product of prime
  germs.
* `factors_unique`: Irreducible factorizations agree up to reordering and multiplication by units.
* `isRelPrime_iff_common_divisors`: Relative primality of germs means that every common divisor is a
  unit.
* `not_isCoprime_of_eval_eq_zero`: Two germs vanishing at the base point cannot generate the unit
  ideal.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

namespace SeveralComplexVariables.AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}

/-- Two germs vanishing at the base point cannot generate the unit ideal. This does not prevent them
from being relatively prime in the factorization sense. -/
theorem not_isCoprime_of_eval_eq_zero {f g : AnalyticGerm ℂ x}
    (hf : eval x f = 0) (hg : eval x g = 0) : ¬ IsCoprime f g := by
  rintro ⟨a, b, h⟩
  have he := congrArg (eval x) h
  simp [hf, hg] at he

/-- Irreducible germs on `n` complex coordinates are prime, by induction using
`prime_of_irreducible_of_baseUFD`. Dimension zero has no irreducible elements, since the germ
ring there is a field. -/
theorem prime_of_irreducible_coordinates (n : ℕ) :
    ∀ {f : AnalyticGerm ℂ (0 : Fin n → ℂ)}, Irreducible f → Prime f := by
  induction n with
  | zero =>
      intro f hf
      exfalso
      set e := equivScalarOfSubsingleton ℂ (0 : Fin 0 → ℂ)
      have hf' : Irreducible (e f) := hf.map e
      rcases eq_or_ne (e f) 0 with h0 | h0
      · rw [h0] at hf'
        exact (hf'.isUnit_or_isUnit (by ring)).elim not_isUnit_zero not_isUnit_zero
      · exact hf'.not_isUnit (isUnit_iff_ne_zero.mpr h0)
  | succ n ih =>
      intro f hf
      have : UniqueFactorizationMonoid (AnalyticGerm ℂ (0 : Fin n → ℂ)) :=
        { irreducible_iff_prime := ⟨ih, Prime.irreducible⟩ }
      let e : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × ℂ :=
        (LinearEquiv.piCongrLeft ℂ (fun _ => ℂ) (finSuccEquiv n)).trans
          ((LinearEquiv.piOptionEquivProd ℂ).trans (LinearEquiv.prodComm ℂ _ _))
      set eqv : AnalyticGerm ℂ (0 : Fin (n + 1) → ℂ) ≃ₐ[ℂ] AnalyticGerm ℂ (0 : (Fin n → ℂ) × ℂ) :=
        (linearEquivPullbackZero e.toContinuousLinearEquiv).symm with heqv
      have hfe : Irreducible (eqv f) := hf.map eqv
      have hpe : Prime (eqv f) := prime_of_irreducible_of_baseUFD hfe
      exact (MulEquiv.prime_iff eqv).mp hpe

/-- Irreducible analytic germs are prime in finite dimension: transport to the origin of a
coordinate presentation using the induction on dimension above. -/
theorem prime_of_irreducible [FiniteDimensional ℂ E] {f : AnalyticGerm ℂ x}
    (hf : Irreducible f) : Prime f := by
  let e := (Module.finBasis ℂ E).equivFunL
  set eqv0 : AnalyticGerm ℂ (0 : E) ≃ₐ[ℂ] AnalyticGerm ℂ (0 : Fin (Module.finrank ℂ E) → ℂ) :=
    (linearEquivPullbackZero e).symm with heqv0
  set eqvx : AnalyticGerm ℂ x ≃ₐ[ℂ] AnalyticGerm ℂ (0 : E) := translateEquiv x with heqvx
  have hf1 : Irreducible (eqvx f) := hf.map eqvx
  have hf2 : Irreducible (eqv0 (eqvx f)) := hf1.map eqv0
  have hp2 : Prime (eqv0 (eqvx f)) := prime_of_irreducible_coordinates _ hf2
  have hp1 : Prime (eqvx f) := (MulEquiv.prime_iff eqv0).mp hp2
  exact (MulEquiv.prime_iff eqvx).mp hp1

/-- The finite-dimensional analytic germ ring is a unique factorization domain. This instance
combines Noetherianity with the prime-germ lemma. -/
instance [FiniteDimensional ℂ E] : UniqueFactorizationMonoid (AnalyticGerm ℂ x) where
  irreducible_iff_prime := ⟨prime_of_irreducible, Prime.irreducible⟩

/-- Every nonzero analytic germ is associated to a finite product of prime germs. The empty product
accounts for units, including all nonzero zero-dimensional germs. -/
theorem exists_prime_factors [FiniteDimensional ℂ E] (f : AnalyticGerm ℂ x) (hf : f ≠ 0) :
    ∃ s : Multiset (AnalyticGerm ℂ x), (∀ p ∈ s, Prime p) ∧ Associated s.prod f :=
  UniqueFactorizationMonoid.exists_prime_factors f hf

/-- Irreducible factorizations agree up to reordering and multiplication by units. -/
theorem factors_unique [FiniteDimensional ℂ E] {s t : Multiset (AnalyticGerm ℂ x)}
    (hs : ∀ p ∈ s, Irreducible p) (ht : ∀ p ∈ t, Irreducible p)
    (h : Associated s.prod t.prod) : Multiset.Rel Associated s t :=
  UniqueFactorizationMonoid.factors_unique hs ht h

/-- Relative primality of germs means that every common divisor is a unit. -/
theorem isRelPrime_iff_common_divisors {f g : AnalyticGerm ℂ x} :
    IsRelPrime f g ↔ ∀ d, d ∣ f → d ∣ g → IsUnit d := by
  rfl

end SeveralComplexVariables.AnalyticGerm

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
