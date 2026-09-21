/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Content

/-!
# Greatest common divisors in multivariate polynomial rings

A polynomial ring in an arbitrary type of variables over a normalized GCD domain is a GCD
domain. Each pair of polynomials uses only finitely many variables. Mathlib's univariate
polynomial GCD structure gives a GCD in that finite-variable ring. Splitting off the remaining
variables and applying `MvPolynomial.dvd_C_iff_exists` shows that the same element remains a GCD
in the full polynomial ring.

Gilmer and Parker (1974), Corollary 4.5 gives the classical result for an arbitrary GCD
coefficient domain. The theorem here assumes a normalized GCD structure, which is the form used
by Mathlib's univariate content theory and is sufficient for the finite-support Hahn-series ring.

The result is stated through `Nonempty (GCDMonoid R)` because `GCDMonoid` contains a choice of
greatest common divisors rather than a proposition alone.
-/

public noncomputable section

universe u v

variable {A B : Type*}
variable [CommMonoidWithZero A] [CommMonoidWithZero B]

private theorem existsGCD_pullback (e : A ≃* B)
    (h : ∀ a b : B, ∃ c : B, ∀ d : B, d ∣ a ∧ d ∣ b ↔ d ∣ c) :
    ∀ a b : A, ∃ c : A, ∀ d : A, d ∣ a ∧ d ∣ b ↔ d ∣ c := by
  intro a b
  obtain ⟨c, hc⟩ := h (e a) (e b)
  refine ⟨e.symm c, fun d ↦ ?_⟩
  simpa only [← map_dvd_iff e, e.apply_symm_apply] using hc (e d)

/-- The existence of greatest common divisors transfers across a multiplicative equivalence. -/
theorem MulEquiv.nonemptyGCDMonoid (e : A ≃* B) [IsCancelMulZero A]
    [Nonempty (GCDMonoid B)] : Nonempty (GCDMonoid A) := by
  classical
  letI : GCDMonoid B := Classical.choice inferInstance
  exact ⟨gcdMonoidOfExistsGCD (existsGCD_pullback e fun a b ↦
    ⟨gcd a b, fun d ↦ (dvd_gcd_iff d a b).symm⟩)⟩

@[implicit_reducible]
private noncomputable def pullbackNormalizationMonoid (e : A ≃* B)
    [NormalizationMonoid B] : NormalizationMonoid A where
  normUnit a := Units.map e.symm.toMonoidHom (normUnit (e a))
  normUnit_zero := by simp
  normUnit_mul ha hb := by
    ext
    simp [ha, hb]
  normUnit_coe_units u := by
    ext
    change e.symm ↑(normUnit (↑(Units.map e.toMonoidHom u) : B) : Bˣ) = ↑u⁻¹
    rw [normUnit_coe_units]
    simp

@[implicit_reducible]
private noncomputable def pullbackNormalizedGCDMonoid (e : A ≃* B)
    [IsCancelMulZero A] [NormalizedGCDMonoid B] : NormalizedGCDMonoid A := by
  classical
  letI : NormalizationMonoid A := pullbackNormalizationMonoid e
  exact normalizedGCDMonoidOfExistsGCD (existsGCD_pullback e fun a b ↦
    ⟨gcd a b, fun d ↦ (dvd_gcd_iff d a b).symm⟩)

namespace MvPolynomial

variable {R : Type u} {σ : Type v}
variable [CommRing R] [IsDomain R]

@[implicit_reducible]
private noncomputable def normalizedGCDMonoidFin [NormalizedGCDMonoid R] :
    (n : ℕ) → NormalizedGCDMonoid (MvPolynomial (Fin n) R)
  | 0 => pullbackNormalizedGCDMonoid (isEmptyRingEquiv R (Fin 0)).toMulEquiv
  | n + 1 => by
      letI : NormalizedGCDMonoid (MvPolynomial (Fin n) R) := normalizedGCDMonoidFin n
      exact pullbackNormalizedGCDMonoid (finSuccEquiv R n).toMulEquiv

@[implicit_reducible]
private noncomputable def normalizedGCDMonoidOfFinite [NormalizedGCDMonoid R]
    (τ : Type v) [Finite τ] : NormalizedGCDMonoid (MvPolynomial τ R) := by
  letI := Fintype.ofFinite τ
  letI : NormalizedGCDMonoid (MvPolynomial (Fin (Fintype.card τ)) R) :=
    normalizedGCDMonoidFin (Fintype.card τ)
  exact pullbackNormalizedGCDMonoid
    (renameEquiv R (Fintype.equivFin τ)).toMulEquiv

private noncomputable def adjoiningVariablesEquiv (S : Set σ) :
    MvPolynomial (↥(Sᶜ : Set σ)) (MvPolynomial S R) ≃ₐ[R] MvPolynomial σ R := by
  classical
  exact (sumAlgEquiv R (↥(Sᶜ : Set σ)) S).symm.trans
    (renameEquiv R
      ((Equiv.sumComm (↥(Sᶜ : Set σ)) S).trans (Equiv.Set.sumCompl S)))

omit [IsDomain R] in
private theorem adjoiningVariablesEquiv_C (S : Set σ) (p : MvPolynomial S R) :
    adjoiningVariablesEquiv S (C p) = rename ((↑) : S → σ) p := by
  let eqv := adjoiningVariablesEquiv (R := R) S
  have h : (rename ((↑) : S → σ)).toRingHom =
      eqv.toAlgHom.toRingHom.comp C := by
    apply ringHom_ext
    · intro r
      simp [eqv, adjoiningVariablesEquiv]
    · intro i
      simp [eqv, adjoiningVariablesEquiv]
  exact (DFunLike.congr_fun h p).symm

private theorem existsGCD [NormalizedGCDMonoid R] (a b : MvPolynomial σ R) :
    ∃ c : MvPolynomial σ R, ∀ d : MvPolynomial σ R, d ∣ a ∧ d ∣ b ↔ d ∣ c := by
  classical
  obtain ⟨s, p, q, rfl, rfl⟩ := exists_finset_rename₂ a b
  letI : NormalizedGCDMonoid (MvPolynomial s R) := normalizedGCDMonoidOfFinite s
  let S : Set σ := s
  let E := adjoiningVariablesEquiv (R := R) S
  have hrename (f : MvPolynomial s R) : E (C f) = rename ((↑) : s → σ) f :=
    adjoiningVariablesEquiv_C S f
  refine ⟨rename ((↑) : s → σ) (gcd p q), fun e ↦ ?_⟩
  constructor
  · rintro ⟨hep, heq⟩
    by_cases hp : p = 0
    · by_cases hq : q = 0
      · subst p
        subst q
        simp
      · have heq' : E.symm e ∣ C q := by
          rw [← map_dvd_iff E, E.apply_symm_apply, hrename q]
          exact heq
        obtain ⟨c, hcq, hec⟩ := (dvd_C_iff_exists hq).mp heq'
        have hcp : c ∣ p := by simp [hp]
        have hcd : c ∣ gcd p q := dvd_gcd hcp hcq
        rw [← hrename (gcd p q), ← E.apply_symm_apply e, map_dvd_iff E, hec]
        exact map_dvd C hcd
    · have hep' : E.symm e ∣ C p := by
        rw [← map_dvd_iff E, E.apply_symm_apply, hrename p]
        exact hep
      obtain ⟨c, hcp, hec⟩ := (dvd_C_iff_exists hp).mp hep'
      have heq' : E.symm e ∣ C q := by
        rw [← map_dvd_iff E, E.apply_symm_apply, hrename q]
        exact heq
      rw [hec] at heq'
      have hcq : c ∣ q := by
        rw [C_dvd_iff_dvd_coeff] at heq'
        simpa using heq' 0
      have hcd : c ∣ gcd p q := dvd_gcd hcp hcq
      rw [← hrename (gcd p q), ← E.apply_symm_apply e, map_dvd_iff E, hec]
      exact map_dvd C hcd
  · intro he
    exact ⟨he.trans (map_dvd (rename ((↑) : s → σ)) (gcd_dvd_left p q)),
      he.trans (map_dvd (rename ((↑) : s → σ)) (gcd_dvd_right p q))⟩

/-- A polynomial ring in an arbitrary type of variables over a normalized GCD domain has
greatest common divisors. -/
@[blueprint "lem:multivariate-polynomial-gcd"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Greatest common divisors in multivariate polynomial rings")
  (statement := /--
    Let $R$ be a commutative domain admitting a normalized GCD structure, and
    let $I$ be any type. Then $R[X_i:i\in I]$ admits greatest common divisors.
  -/)
  (proof := /--
  A pair of polynomials involves only finitely many variables. Regard their
  finite-variable ring as an iterated univariate polynomial ring and choose a
  greatest common divisor there. View the full ring as the polynomial ring in
  the complementary variables over this finite-variable ring. If at least one
  of the original polynomials is non-zero, a common divisor of their constant
  images is associated to a constant polynomial; its coefficient divides both
  finite-variable polynomials and hence their greatest common divisor. The
  case where both polynomials vanish is immediate. Thus the finite-variable
  greatest common divisor remains one in the full polynomial ring.
  -/)]
theorem nonemptyGCDMonoid [Nonempty (NormalizedGCDMonoid R)] :
    Nonempty (GCDMonoid (MvPolynomial σ R)) := by
  classical
  letI : NormalizedGCDMonoid R := Classical.choice inferInstance
  exact ⟨gcdMonoidOfExistsGCD existsGCD⟩

end MvPolynomial
