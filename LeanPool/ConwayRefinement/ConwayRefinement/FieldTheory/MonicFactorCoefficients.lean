/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.FieldTheory.RelativeAlgebraicClosure
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Coefficients of a monic factor over a relatively algebraically closed subfield

A monic divisor of a monic polynomial has coefficients integral over the base ring, because they
are symmetric functions of a subset of the roots. Over a field the integral elements are exactly
the algebraic ones, so if the base field is relatively algebraically closed in the coefficient
field then those coefficients already lie in the base field.
-/

universe u v

namespace Polynomial

public section

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Over a relatively algebraically closed subfield, a monic factor of a monic polynomial has all
its coefficients in the subfield. -/
theorem coeff_mem_range_of_monic_dvd
    (hclosed : Algebra.IsRelativelyAlgebraicallyClosed K L)
    {p : Polynomial K} {q : Polynomial L} (hp : p.Monic) (hq : q.Monic)
    (hdvd : q ∣ p.map (algebraMap K L)) (i : ℕ) :
    q.coeff i ∈ (algebraMap K L).range := by
  obtain ⟨k, hk⟩ := (Algebra.isRelativelyAlgebraicallyClosed_iff K L).mp hclosed _
    (Polynomial.isIntegral_coeff_of_dvd p q hp hq hdvd i).isAlgebraic
  exact ⟨k, hk⟩

/-- If a product of two monic polynomials over `L` is the extension of a polynomial over `K`, then
each factor already has all its coefficients in `K`. -/
theorem coeff_mem_range_of_mul_eq_map
    (hclosed : Algebra.IsRelativelyAlgebraicallyClosed K L)
    {q r : Polynomial L} {P : Polynomial K} (hq : q.Monic) (hr : r.Monic)
    (hqr : q * r = P.map (algebraMap K L)) (i : ℕ) :
    q.coeff i ∈ (algebraMap K L).range := by
  have hPmonic : P.Monic := Polynomial.monic_map_iff.mp (hqr ▸ hq.mul hr)
  exact coeff_mem_range_of_monic_dvd hclosed hPmonic hq ⟨r, hqr.symm⟩ i

/-- If a product of two nonzero polynomials over `L` is the extension of a polynomial over `K`,
one scalar clears the first factor into `K`. -/
theorem exists_scalar_of_mul_eq_map
    (hclosed : Algebra.IsRelativelyAlgebraicallyClosed K L)
    {q r : Polynomial L} {P : Polynomial K} (hq : q ≠ 0) (hr : r ≠ 0)
    (hqr : q * r = P.map (algebraMap K L)) :
    ∃ c : L, c ≠ 0 ∧ ∀ j, c * q.coeff j ∈ (algebraMap K L).range := by
  have hc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hd : r.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hr
  have hq1 : (Polynomial.C q.leadingCoeff⁻¹ * q).Monic := by
    unfold Polynomial.Monic
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, inv_mul_cancel₀ hc]
  have hr1 : (Polynomial.C r.leadingCoeff⁻¹ * r).Monic := by
    unfold Polynomial.Monic
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, inv_mul_cancel₀ hd]
  have hlc : (P.map (algebraMap K L)).leadingCoeff = q.leadingCoeff * r.leadingCoeff := by
    rw [← hqr, Polynomial.leadingCoeff_mul]
  have hPlc : (P.map (algebraMap K L)).leadingCoeff = algebraMap K L P.leadingCoeff := by
    rw [Polynomial.leadingCoeff_map]
  have hPne : P.leadingCoeff ≠ 0 := by
    intro h0
    rw [hPlc, h0, map_zero] at hlc
    exact (mul_ne_zero hc hd) hlc.symm
  have hprod : (Polynomial.C q.leadingCoeff⁻¹ * q) * (Polynomial.C r.leadingCoeff⁻¹ * r) =
      (Polynomial.C P.leadingCoeff⁻¹ * P).map (algebraMap K L) := by
    rw [Polynomial.map_mul, Polynomial.map_C, ← hqr]
    rw [show algebraMap K L P.leadingCoeff⁻¹ = (q.leadingCoeff * r.leadingCoeff)⁻¹ by
      rw [← hlc, hPlc, map_inv₀]]
    rw [mul_inv, Polynomial.C_mul]
    ring
  refine ⟨q.leadingCoeff⁻¹, inv_ne_zero hc, fun j ↦ ?_⟩
  have := coeff_mem_range_of_mul_eq_map hclosed hq1 hr1 hprod j
  rwa [Polynomial.coeff_C_mul] at this

end

end Polynomial
