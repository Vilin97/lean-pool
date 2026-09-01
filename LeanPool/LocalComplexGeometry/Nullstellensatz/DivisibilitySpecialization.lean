/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Nullstellensatz.GenericFiber
import LeanPool.LocalComplexGeometry.Nullstellensatz.PolynomialFibers
import LeanPool.LocalComplexGeometry.Nullstellensatz.QuotientPolynomialSpecialization
import LeanPool.LocalComplexGeometry.Noetherian.Ruckert

/-!
# Specializing denominator-cleared generic divisibility

A `GenericMinpolyDivisibilityLiftCertificate` is a polynomial identity over
base germs up to a coefficientwise contraction error.  On the contracted
prime's local zero set that error disappears.  Away from the explicit
denominator, every root of the lifted minimal polynomial is therefore a root
of the certified divisible polynomial.
-/

open Filter
open scoped Topology


namespace LocalComplexGeometry

noncomputable section

/-- The polynomial of chosen coefficient representatives attached to a WPT
remainder vector, before specialization at a base point. -/
def remainderGermPolynomialRepresentativeFunctions {n e : ℕ}
    (b : Fin e → HolomorphicGerm n) :
    Polynomial (ComplexEuclidean n → ℂ) :=
  ∑ i : Fin e,
    Polynomial.C (HolomorphicGerm.representative (b i)) *
      Polynomial.X ^ (i : ℕ)

@[simp]
theorem remainderGermPolynomialRepresentativeFunctions_map_eval
    {n e : ℕ} (b : Fin e → HolomorphicGerm n)
    (z : ComplexEuclidean n) :
    (remainderGermPolynomialRepresentativeFunctions b).map
        (Pi.evalRingHom (fun _ : ComplexEuclidean n ↦ ℂ) z) =
      remainderPolynomialAt
        (HolomorphicGerm.coefficientRepresentatives b) z := by
  unfold remainderGermPolynomialRepresentativeFunctions remainderPolynomialAt
    HolomorphicGerm.coefficientRepresentatives
  rw [Polynomial.map_sum]
  simp

/-- Mapping the representative-function polynomial to raw function germs
recovers the polynomial assembled from the original coefficient germs. -/
theorem remainderGermPolynomialRepresentativeFunctions_map_germ
    {n e : ℕ} (b : Fin e → HolomorphicGerm n) :
    (remainderGermPolynomialRepresentativeFunctions b).map
        (functionToGermRingHom n) =
      (remainderGermPolynomial b).map (holomorphicGermSubring n).subtype := by
  unfold remainderGermPolynomialRepresentativeFunctions remainderGermPolynomial
  rw [Polynomial.map_sum, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X]
  congr 2
  simpa [functionToGermRingHom] using
    (HolomorphicGerm.coe_representative (b i))

/-- Any sufficiently large fixed-degree display of a WPT remainder agrees
near the origin with its direct coefficient-vector specialization. -/
theorem eventually_germPolynomialRepresentativeAt_eq_remainderPolynomialAt
    {n e m : ℕ} (b : Fin e → HolomorphicGerm n)
    (hB : (remainderGermPolynomial b).natDegree ≤ m) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt m (remainderGermPolynomial b) z =
        remainderPolynomialAt
          (HolomorphicGerm.coefficientRepresentatives b) z := by
  let G := germPolynomialRepresentativeFunctions m (remainderGermPolynomial b)
  let F := remainderGermPolynomialRepresentativeFunctions b
  have hmap : G.map (functionToGermRingHom n) =
      F.map (functionToGermRingHom n) :=
    (germPolynomialRepresentativeFunctions_map_germ
      (remainderGermPolynomial b) hB).trans
        (remainderGermPolynomialRepresentativeFunctions_map_germ b).symm
  have hevent := eventually_polynomial_map_eval_eq_of_map_germ_eq G F hmap
  filter_upwards [hevent] with z hz
  simpa [G, F] using hz

section Prime

variable {n : ℕ} (P : Ideal (HolomorphicGerm (n + 1))) [P.IsPrime]

omit [P.IsPrime] in
/-- A denominator-cleared generic divisibility certificate specializes to
the expected root implication on the contracted analytic zero set. -/
theorem eventually_eval_eq_zero_of_genericMinpolyDivisibilityLiftCertificate
    {Q R : Polynomial (HolomorphicGerm n)}
    (C : GenericMinpolyDivisibilityLiftCertificate P Q R)
    {e k : ℕ} (hQ : Q.natDegree ≤ e) (hR : R.natDegree ≤ k) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      idealGeneratorZeroPredicate (lowerDimensionalContraction P) z →
      HolomorphicGerm.representative C.denominator z ≠ 0 →
      ∀ w : ℂ, (germPolynomialRepresentativeAt e Q z).eval w = 0 →
        (germPolynomialRepresentativeAt k R z).eval w = 0 := by
  let : IsNoetherianRing (HolomorphicGerm n) :=
    holomorphicGerm_isNoetherian_core n
  let I : Ideal (HolomorphicGerm n) := lowerDimensionalContraction P
  let π : HolomorphicGerm n →+* (HolomorphicGerm n ⧸ I) :=
    Ideal.Quotient.mk I
  let L : Polynomial (HolomorphicGerm n) := Polynomial.C C.denominator * R
  let T : Polynomial (HolomorphicGerm n) := Q * C.quotient
  let M : ℕ := L.natDegree + T.natDegree + Q.natDegree +
    R.natDegree + C.quotient.natDegree
  have hLM : L.natDegree ≤ M := by
    dsimp [M]
    omega
  have hTM : T.natDegree ≤ M := by
    dsimp [M]
    omega
  have hQM : Q.natDegree ≤ M := by
    dsimp [M]
    omega
  have hRM : R.natDegree ≤ M := by
    dsimp [M]
    omega
  have hSM : C.quotient.natDegree ≤ M := by
    dsimp [M]
    omega
  have hCM : (Polynomial.C C.denominator).natDegree ≤ M := by
    rw [Polynomial.natDegree_C]
    exact Nat.zero_le M
  have herror : C.error.map π = 0 := by
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (C.error_coeff_mem j)
  have hmap : L.map π = T.map π := by
    have hid := congrArg (fun p : Polynomial (HolomorphicGerm n) ↦ p.map π)
      C.identity
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      herror, add_zero] at hid
    dsimp [L, T]
    simp only [Polynomial.map_mul, Polynomial.map_C]
    exact hid
  have hspecial :=
    eventually_germPolynomialRepresentativeAt_eq_of_map_quotient_eq
      (m := M) I L T hmap
  have hleft : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt M L z =
        germPolynomialRepresentativeAt M (Polynomial.C C.denominator) z *
          germPolynomialRepresentativeAt M R z := by
    simpa only [L] using eventually_germPolynomialRepresentativeAt_mul
      (m := M) (Polynomial.C C.denominator) R hCM hRM hLM
  have hright : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt M T z =
        germPolynomialRepresentativeAt M Q z *
          germPolynomialRepresentativeAt M C.quotient z := by
    simpa only [T] using eventually_germPolynomialRepresentativeAt_mul
      (m := M) Q C.quotient hQM hSM hTM
  have hconstant :=
    eventually_germPolynomialRepresentativeAt_eq_of_degreeBounds
      (k := 0) (m := M) (Polynomial.C C.denominator)
      (by rw [Polynomial.natDegree_C]) hCM
  have hQbound :=
    eventually_germPolynomialRepresentativeAt_eq_of_degreeBounds
      (k := e) (m := M) Q hQ hQM
  have hRbound :=
    eventually_germPolynomialRepresentativeAt_eq_of_degreeBounds
      (k := k) (m := M) R hR hRM
  filter_upwards [hspecial, hleft, hright, hconstant, hQbound, hRbound]
    with z hzspec hzleft hzright hzconstant hzQ hzR
  intro hZ hden w hroot
  have heq := congrArg (fun p : Polynomial ℂ ↦ p.eval w) (hzspec hZ)
  rw [hzleft, hzright, Polynomial.eval_mul, Polynomial.eval_mul] at heq
  rw [← hzconstant, ← hzR, ← hzQ] at heq
  simp only [germPolynomialRepresentativeAt_zero_C,
    Polynomial.eval_C] at heq
  rw [hroot, zero_mul] at heq
  exact (mul_eq_zero.mp heq).resolve_left hden

/-- The strict Euclidean remainder in an arbitrary-target certificate
specializes, at every root of the lifted minimal polynomial, to the explicit
denominator times the certified target polynomial. -/
theorem eventually_remainder_eval_eq_denominator_mul_of_genericRemainderModMinpolyLiftCertificate
    {Q R : Polynomial (HolomorphicGerm n)}
    (C : GenericRemainderModMinpolyLiftCertificate P Q R)
    {e k : ℕ} (hQ : Q.natDegree ≤ e) (hR : R.natDegree ≤ k) :
    ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      idealGeneratorZeroPredicate (lowerDimensionalContraction P) z →
      ∀ w : ℂ, (germPolynomialRepresentativeAt e Q z).eval w = 0 →
        (remainderPolynomialAt
            (HolomorphicGerm.coefficientRepresentatives C.coefficients) z).eval w =
          HolomorphicGerm.representative C.denominator z *
            (germPolynomialRepresentativeAt k R z).eval w := by
  let : IsNoetherianRing (HolomorphicGerm n) :=
    holomorphicGerm_isNoetherian_core n
  let I : Ideal (HolomorphicGerm n) := lowerDimensionalContraction P
  let π : HolomorphicGerm n →+* (HolomorphicGerm n ⧸ I) :=
    Ideal.Quotient.mk I
  let B : Polynomial (HolomorphicGerm n) :=
    remainderGermPolynomial C.coefficients
  let L : Polynomial (HolomorphicGerm n) := Polynomial.C C.denominator * R
  let U : Polynomial (HolomorphicGerm n) := Q * C.quotient
  let T : Polynomial (HolomorphicGerm n) := U + B
  let M : ℕ := L.natDegree + T.natDegree + U.natDegree + B.natDegree +
    Q.natDegree + R.natDegree + C.quotient.natDegree
  have hLM : L.natDegree ≤ M := by dsimp [M]; omega
  have hTM : T.natDegree ≤ M := by dsimp [M]; omega
  have hUM : U.natDegree ≤ M := by dsimp [M]; omega
  have hBM : B.natDegree ≤ M := by dsimp [M]; omega
  have hQM : Q.natDegree ≤ M := by dsimp [M]; omega
  have hRM : R.natDegree ≤ M := by dsimp [M]; omega
  have hSM : C.quotient.natDegree ≤ M := by dsimp [M]; omega
  have hCM : (Polynomial.C C.denominator).natDegree ≤ M := by
    rw [Polynomial.natDegree_C]
    exact Nat.zero_le M
  have herror : C.error.map π = 0 := by
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (C.error_coeff_mem j)
  have hmap : L.map π = T.map π := by
    have hid := congrArg (fun p : Polynomial (HolomorphicGerm n) ↦ p.map π)
      C.identity
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      herror, add_zero] at hid
    dsimp [L, T, U, B]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    exact hid
  have hspecial :=
    eventually_germPolynomialRepresentativeAt_eq_of_map_quotient_eq
      (m := M) I L T hmap
  have hleft : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt M L z =
        germPolynomialRepresentativeAt M (Polynomial.C C.denominator) z *
          germPolynomialRepresentativeAt M R z := by
    simpa only [L] using eventually_germPolynomialRepresentativeAt_mul
      (m := M) (Polynomial.C C.denominator) R hCM hRM hLM
  have hsum : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt M T z =
        germPolynomialRepresentativeAt M U z +
          germPolynomialRepresentativeAt M B z := by
    simpa only [T] using eventually_germPolynomialRepresentativeAt_add
      (m := M) U B hUM hBM hTM
  have hproduct : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt M U z =
        germPolynomialRepresentativeAt M Q z *
          germPolynomialRepresentativeAt M C.quotient z := by
    simpa only [U] using eventually_germPolynomialRepresentativeAt_mul
      (m := M) Q C.quotient hQM hSM hUM
  have hconstant :=
    eventually_germPolynomialRepresentativeAt_eq_of_degreeBounds
      (k := 0) (m := M) (Polynomial.C C.denominator)
      (by rw [Polynomial.natDegree_C]) hCM
  have hQbound :=
    eventually_germPolynomialRepresentativeAt_eq_of_degreeBounds
      (k := e) (m := M) Q hQ hQM
  have hRbound :=
    eventually_germPolynomialRepresentativeAt_eq_of_degreeBounds
      (k := k) (m := M) R hR hRM
  have hBdirect : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      germPolynomialRepresentativeAt M B z =
        remainderPolynomialAt
          (HolomorphicGerm.coefficientRepresentatives C.coefficients) z := by
    simpa only [B] using
      eventually_germPolynomialRepresentativeAt_eq_remainderPolynomialAt
        C.coefficients hBM
  filter_upwards [hspecial, hleft, hsum, hproduct, hconstant,
    hQbound, hRbound, hBdirect]
    with z hzspec hzleft hzsum hzproduct hzconstant hzQ hzR hzB
  intro hZ w hroot
  have heq := congrArg (fun p : Polynomial ℂ ↦ p.eval w) (hzspec hZ)
  rw [hzleft, hzsum, hzproduct, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_mul] at heq
  rw [← hzconstant, ← hzR, ← hzQ, hzB] at heq
  simp only [germPolynomialRepresentativeAt_zero_C,
    Polynomial.eval_C] at heq
  rw [hroot, zero_mul, zero_add] at heq
  exact heq.symm

end Prime

end

end LocalComplexGeometry
