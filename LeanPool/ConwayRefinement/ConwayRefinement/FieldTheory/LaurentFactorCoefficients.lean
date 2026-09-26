/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Finsupp.Basic
public import LeanPool.ConwayRefinement.ConwayRefinement.FieldTheory.MonicFactorCoefficients

/-!
# Laurent factors over a relatively algebraically closed subfield

A Laurent polynomial becomes an ordinary polynomial after multiplication by a large enough power
of the variable, and that multiplication is invertible, so divisibility and coefficients transfer
between the two settings. Coefficient extension commutes with the inclusion of polynomials into
Laurent polynomials and fixes the Laurent monomials.

Combining these with the polynomial statement: if two Laurent polynomials over the extension have
monic polynomial shifts whose product is the extension of a polynomial over the subfield, then the
coefficients of each shift already lie in the subfield.
-/

universe u v

namespace LaurentPolynomial

public section

variable {R : Type u} [Semiring R]

/-- The Laurent image of a polynomial has the same coefficients at natural exponents. -/
theorem toLaurent_apply_natCast (p : Polynomial R) (n : ℕ) :
    (Polynomial.toLaurent p).coeff (n : ℤ) = p.coeff n := by
  rw [coeff_toLaurent]
  change (p.toFinsupp.coeff.mapDomain Nat.castEmbedding) (Nat.castEmbedding n) = p.coeff n
  rw [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective]
  rfl

/-- The Laurent image of a polynomial vanishes at negative exponents. -/
theorem toLaurent_apply_of_neg (p : Polynomial R) {z : ℤ} (hz : z < 0) :
    (Polynomial.toLaurent p).coeff z = 0 := by
  rw [coeff_toLaurent]
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨n, rfl⟩
  change (n : ℤ) < 0 at hz
  omega
/-- Coefficient extension commutes with the Laurent inclusion. -/
theorem toLaurent_map {S : Type*} [Semiring S] (f : R →+* S) (p : Polynomial R) :
    Polynomial.toLaurent (p.map f) = AddMonoidAlgebra.mapRingHom ℤ f (Polynomial.toLaurent p) := by
  ext z
  rcases lt_or_ge z 0 with hz | hz
  · rw [toLaurent_apply_of_neg _ hz]
    change (0 : S) = f ((Polynomial.toLaurent p).coeff z)
    rw [toLaurent_apply_of_neg _ hz, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [toLaurent_apply_natCast, Polynomial.coeff_map]
    change f (p.coeff n) = f ((Polynomial.toLaurent p).coeff (n : ℤ))
    rw [toLaurent_apply_natCast]

/-- Coefficient extension fixes the Laurent monomials. -/
theorem mapRingHom_T {S : Type*} [Semiring S] (f : R →+* S) (z : ℤ) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.T z) = LaurentPolynomial.T z := by
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]

section Core

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- One-variable core, with the shifts supplied: two monic polynomial shifts of Laurent factors
whose product is an extension have coefficients in the base field. -/
theorem coeff_mem_range_of_shifted
    (hclosed : Algebra.IsRelativelyAlgebraicallyClosed K L)
    {q r : AddMonoidAlgebra L ℤ} {P : AddMonoidAlgebra K ℤ}
    (hmul : q * r = AddMonoidAlgebra.mapRingHom ℤ (algebraMap K L) P)
    {q' r' : Polynomial L} {P' : Polynomial K} {n m : ℕ}
    (hq' : Polynomial.toLaurent q' = q * LaurentPolynomial.T (n : ℤ))
    (hr' : Polynomial.toLaurent r' = r * LaurentPolynomial.T (m : ℤ))
    (hP' : Polynomial.toLaurent P' = P * LaurentPolynomial.T ((n : ℤ) + (m : ℤ)))
    (hqm : q'.Monic) (hrm : r'.Monic) (j : ℕ) :
    q'.coeff j ∈ (algebraMap K L).range := by
  have hprod : q' * r' = P'.map (algebraMap K L) := by
    refine Polynomial.toLaurent_injective ?_
    rw [map_mul, hq', hr', toLaurent_map, hP', map_mul, mul_mul_mul_comm,
      ← LaurentPolynomial.T_add, hmul, mapRingHom_T]
  exact Polynomial.coeff_mem_range_of_mul_eq_map hclosed hqm hrm hprod j

end Core

section Shift

variable {R : Type u} [CommRing R]

private theorem mul_T_apply (f : AddMonoidAlgebra R ℤ) (n : ℤ) (z : ℤ) :
    (f * LaurentPolynomial.T n : AddMonoidAlgebra R ℤ).coeff z = f.coeff (z - n) := by
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply,
    mul_one, sub_eq_add_neg]

/-- Coefficients of a Laurent polynomial read off a polynomial shift, at natural indices. -/
theorem apply_sub_of_toLaurent_eq_mul_T {f : AddMonoidAlgebra R ℤ} {p : Polynomial R} {n : ℕ}
    (h : Polynomial.toLaurent p = f * LaurentPolynomial.T (n : ℤ)) (j : ℕ) :
    f.coeff ((j : ℤ) - n) = p.coeff j := by
  have hj := mul_T_apply f (n : ℤ) (j : ℤ)
  rw [← h, toLaurent_apply_natCast] at hj
  exact hj.symm

/-- Below the shift the Laurent polynomial vanishes. -/
theorem apply_eq_zero_of_toLaurent_eq_mul_T {f : AddMonoidAlgebra R ℤ} {p : Polynomial R} {n : ℕ}
    (h : Polynomial.toLaurent p = f * LaurentPolynomial.T (n : ℤ)) {z : ℤ} (hz : z + n < 0) :
    f.coeff z = 0 := by
  have hz' := mul_T_apply f (n : ℤ) (z + n)
  simp only [add_sub_cancel_right] at hz'
  rw [← h, toLaurent_apply_of_neg _ hz] at hz'
  exact hz'.symm

section Clearing

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Laurent form of scalar clearing: one scalar carries the first factor into the subfield. -/
theorem exists_scalar_of_mul_eq_map
    (hclosed : Algebra.IsRelativelyAlgebraicallyClosed K L)
    {q r : AddMonoidAlgebra L ℤ} {P : AddMonoidAlgebra K ℤ} (hq : q ≠ 0) (hr : r ≠ 0)
    (hqr : q * r = AddMonoidAlgebra.mapRingHom ℤ (algebraMap K L) P) :
    ∃ c : L, c ≠ 0 ∧ ∀ z, c * q.coeff z ∈ (algebraMap K L).range := by
  obtain ⟨n₀, q₀, hq₀⟩ := LaurentPolynomial.exists_T_pow q
  obtain ⟨m₀, r₀, hr₀⟩ := LaurentPolynomial.exists_T_pow r
  obtain ⟨l, P₀, hP₀⟩ := LaurentPolynomial.exists_T_pow P
  have hq'L : Polynomial.toLaurent (q₀ * Polynomial.X ^ l) =
      q * LaurentPolynomial.T ((n₀ + l : ℕ) : ℤ) := by
    rw [map_mul, hq₀, Polynomial.toLaurent_X_pow, mul_assoc, ← LaurentPolynomial.T_add]
    norm_cast
  have hr'L : Polynomial.toLaurent (r₀ * Polynomial.X ^ l) =
      r * LaurentPolynomial.T ((m₀ + l : ℕ) : ℤ) := by
    rw [map_mul, hr₀, Polynomial.toLaurent_X_pow, mul_assoc, ← LaurentPolynomial.T_add]
    norm_cast
  have hPL : Polynomial.toLaurent ((P₀ * Polynomial.X ^ (n₀ + m₀ + l)).map (algebraMap K L)) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap K L) P *
        LaurentPolynomial.T (((n₀ + l : ℕ) : ℤ) + ((m₀ + l : ℕ) : ℤ)) := by
    rw [toLaurent_map, map_mul, hP₀, Polynomial.toLaurent_X_pow, map_mul, mapRingHom_T,
      map_mul, mapRingHom_T, mul_assoc, ← LaurentPolynomial.T_add]
    push_cast
    ring_nf
  have hprod : (q₀ * Polynomial.X ^ l) * (r₀ * Polynomial.X ^ l) =
      (P₀ * Polynomial.X ^ (n₀ + m₀ + l)).map (algebraMap K L) := by
    refine Polynomial.toLaurent_injective ?_
    rw [map_mul, hq'L, hr'L, hPL, mul_mul_mul_comm, ← LaurentPolynomial.T_add, hqr]
  have hq'0 : q₀ * Polynomial.X ^ l ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hq'L
    exact hq ((mul_eq_zero.mp hq'L.symm).resolve_right (LaurentPolynomial.isUnit_T _).ne_zero)
  have hr'0 : r₀ * Polynomial.X ^ l ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hr'L
    exact hr ((mul_eq_zero.mp hr'L.symm).resolve_right (LaurentPolynomial.isUnit_T _).ne_zero)
  obtain ⟨c, hc, hcoeff⟩ := Polynomial.exists_scalar_of_mul_eq_map hclosed hq'0 hr'0 hprod
  refine ⟨c, hc, fun z ↦ ?_⟩
  rcases le_or_gt 0 (z + ((n₀ + l : ℕ) : ℤ)) with hcase | hcase
  · have hz : z = ((z + (n₀ + l : ℕ)).toNat : ℤ) - ((n₀ + l : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hcase]
      ring
    rw [hz, apply_sub_of_toLaurent_eq_mul_T hq'L]
    exact hcoeff _
  · rw [apply_eq_zero_of_toLaurent_eq_mul_T hq'L hcase, mul_zero]
    exact ⟨0, map_zero _⟩

end Clearing


end Shift

end
end LaurentPolynomial
