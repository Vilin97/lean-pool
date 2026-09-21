/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.SyntacticDivisionObstruction
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# An exact criterion for the remaining split trace-cover division theorem

For `sigma != 0, 1` and odd coprime cover degrees, the source-side syntactic division theorem is
equivalent to two concrete algebraic facts: irreducibility of the cleared affine cover polynomial
and injectivity of the comparison map after inverting the two coordinates.  The reverse direction
uses primeness to prove that localization has not killed an affine class.  Thus the `sigma = 1`
counterexample cannot be hidden by moving to the Laurent model.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

section OddCoprime

variable (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
  (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)

private lemma splitTraceCoverPolynomial_ne_zero (hdOdd : Odd d) :
    splitTraceCoverPolynomial (1 : K) sigma d e ≠ 0 := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hdOdd
  intro hzero
  have heval := congrArg (MvPolynomial.eval ![0, 1]) hzero
  rw [eval_splitTraceCoverPolynomial] at heval
  simp [hd] at heval

private lemma coordinateZero_not_dvd_splitTraceCoverPolynomial
    (hdOdd : Odd d) :
    ¬ MvPolynomial.X 0 ∣ splitTraceCoverPolynomial (1 : K) sigma d e := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hdOdd
  intro hdiv
  have hmap := map_dvd (MvPolynomial.eval ![0, 1]) hdiv
  simp [eval_splitTraceCoverPolynomial, hd] at hmap

private lemma coordinateOne_not_dvd_splitTraceCoverPolynomial
    (hsigma : sigma ≠ 0) (heOdd : Odd e) :
    ¬ MvPolynomial.X 1 ∣ splitTraceCoverPolynomial (1 : K) sigma d e := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at heOdd
  intro hdiv
  have hmap := map_dvd (MvPolynomial.eval ![1, 0]) hdiv
  simp [eval_splitTraceCoverPolynomial, he, hsigma] at hmap

/-- The cleared affine cover polynomial has no coordinate-axis factor.  This is the exact
saturation fact needed to pass faithfully from the affine quotient to the Laurent open; it uses
only `sigma ≠ 0` and positivity of the odd cover degrees, not irreducibility. -/
theorem splitTraceCoverPolynomial_isRelPrime_coordinateProduct :
    sigma ≠ 0 → Odd e → Odd d →
    IsRelPrime (splitTraceCoverPolynomial (1 : K) sigma d e)
      (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  intro hsigma heOdd hdOdd
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors
    (splitTraceCoverPolynomial_ne_zero sigma e d hdOdd)).2
  intro q hqCover hqProduct hqPrime
  rcases hqPrime.dvd_mul.mp hqProduct with hqZero | hqOne
  · have hassociated := hqPrime.associated_of_dvd
      (MvPolynomial.X_prime (i := (0 : Fin 2))) hqZero
    exact coordinateZero_not_dvd_splitTraceCoverPolynomial sigma e d hdOdd
      (hassociated.dvd_iff_dvd_left.mp hqCover)
  · have hassociated := hqPrime.associated_of_dvd
      (MvPolynomial.X_prime (i := (1 : Fin 2))) hqOne
    exact coordinateOne_not_dvd_splitTraceCoverPolynomial sigma e d hsigma heOdd
      (hassociated.dvd_iff_dvd_left.mp hqCover)

/-- Inverting the coordinate product does not kill any affine trace-cover class.  This affine
saturation theorem is independent of the unresolved irreducibility statement. -/
theorem splitTraceAffineToLaurent_injective :
    sigma ≠ 0 → Odd e → Odd d →
    Function.Injective
      (algebraMap (SplitTraceAffineCoordinateRing K sigma d e)
        (SplitTraceLaurentCoordinateRing K sigma d e)) := by
  intro hsigma heOdd hdOdd
  let I : Ideal (MvPolynomial (Fin 2) K) :=
    Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e}
  have hregular : splitTraceAffineCoordinateProduct sigma d e ∈
      nonZeroDivisors (SplitTraceAffineCoordinateRing K sigma d e) := by
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro x hx
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hmultiple : splitTraceCoverPolynomial (1 : K) sigma d e ∣
          (MvPolynomial.X 0 * MvPolynomial.X 1) * p := by
        rw [← Ideal.mem_span_singleton]
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simpa [I, splitTraceAffineCoordinateProduct] using hx
      have hp : splitTraceCoverPolynomial (1 : K) sigma d e ∣ p :=
        (splitTraceCoverPolynomial_isRelPrime_coordinateProduct
          sigma e d hsigma heOdd hdOdd).dvd_of_dvd_mul_left hmultiple
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rwa [Ideal.mem_span_singleton]
    · intro x hx
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hmultiple : splitTraceCoverPolynomial (1 : K) sigma d e ∣
          (MvPolynomial.X 0 * MvPolynomial.X 1) * p := by
        rw [← Ideal.mem_span_singleton]
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        simpa [I, splitTraceAffineCoordinateProduct, mul_comm] using hx
      have hp : splitTraceCoverPolynomial (1 : K) sigma d e ∣ p :=
        (splitTraceCoverPolynomial_isRelPrime_coordinateProduct
          sigma e d hsigma heOdd hdOdd).dvd_of_dvd_mul_left hmultiple
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rwa [Ideal.mem_span_singleton]
  exact IsLocalization.injective (SplitTraceLaurentCoordinateRing K sigma d e) (by
    rw [Submonoid.powers_le]
    exact hregular)

/-- Injectivity of the Laurent comparison already forces injectivity of the affine comparison:
the coordinate-product localization is faithful by the explicit saturation theorem above. -/
theorem splitTraceAffineToKummerTop_injective_of_laurentInjective
    (hLaurent : Function.Injective
      (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde)) :
    Function.Injective
      (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde) := by
  have hlocalization : Function.Injective
      (algebraMap (SplitTraceAffineCoordinateRing K sigma d e)
        (SplitTraceLaurentCoordinateRing K sigma d e)) :=
    splitTraceAffineToLaurent_injective sigma e d hsigma heOdd hdOdd
  intro x y hxy
  apply hlocalization
  apply hLaurent
  rw [splitTraceLaurentToKummerTop_algebraMap_apply,
    splitTraceLaurentToKummerTop_algebraMap_apply]
  exact hxy

/-- Injectivity on the Laurent open implies the exact source-side syntactic division theorem. -/
theorem splitTracePolynomialSyntacticNormalForm_division_of_laurentInjective
    (hLaurent : Function.Injective
      (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde))
    (p : MvPolynomial (Fin 2) K)
    (hnormal : splitTracePolynomialSyntacticNormalForm
      sigma hsigma e d heOdd hdOdd p = 0) :
    p ∈ Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e} := by
  let I : Ideal (MvPolynomial (Fin 2) K) :=
    Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e}
  have hAffine :=
    splitTraceAffineToKummerTop_injective_of_laurentInjective
      sigma hsigma e d heOdd hdOdd hde hLaurent
  have heval : splitTracePolynomialToKummerTop
      sigma hsigma e d heOdd hdOdd hde p = 0 :=
    (splitTracePolynomialSyntacticNormalForm_eq_zero_iff
      sigma hsigma e d heOdd hdOdd hde p).1 hnormal
  have hclass : Ideal.Quotient.mk I p = 0 := by
    apply hAffine
    change splitTracePolynomialToKummerTop sigma hsigma e d heOdd hdOdd hde p = 0
    exact heval
  exact Ideal.Quotient.eq_zero_iff_mem.mp hclass

/-- Laurent-to-Kummer injectivity also forces irreducibility of the cleared affine cover.
Indeed the affine quotient injects into the Kummer function field, hence is a domain. -/
theorem splitTraceCoverPolynomial_irreducible_of_laurentInjective
    (hLaurent : Function.Injective
      (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde)) :
    Irreducible (splitTraceCoverPolynomial (1 : K) sigma d e) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  letI : IsDomain (SplitTraceXiFunctionField K sigma e d) :=
    AdjoinRoot.isDomain_of_prime hXiIrred.prime
  let I : Ideal (MvPolynomial (Fin 2) K) :=
    Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e}
  have hAffine := splitTraceAffineToKummerTop_injective_of_laurentInjective
    sigma hsigma e d heOdd hdOdd hde hLaurent
  letI : IsDomain (SplitTraceAffineCoordinateRing K sigma d e) :=
    hAffine.isDomain
      (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde).toRingHom
  have hprimeIdeal : I.IsPrime := by
    exact (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  have hprimeElement : Prime (splitTraceCoverPolynomial (1 : K) sigma d e) :=
    (Ideal.span_singleton_prime
      (splitTraceCoverPolynomial_ne_zero sigma e d hdOdd)).1 (by
        simpa [I] using hprimeIdeal)
  exact irreducible_iff_prime.mpr hprimeElement

/-- Exact characterization of the remaining source-division wall.  In the nondegenerate case,
division by the cleared cover polynomial is equivalent to injectivity of the explicit
Laurent-to-Kummer comparison; the affine-to-Laurent map has already been proved faithful. -/
theorem splitTracePolynomialSyntacticNormalForm_division_iff_laurentInjective
    (hnondegenerate : sigma ≠ 1) :
    (∀ p : MvPolynomial (Fin 2) K,
      splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd p = 0 →
        p ∈ Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e}) ↔
      Function.Injective
        (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  letI : IsDomain (SplitTraceXiFunctionField K sigma e d) :=
    AdjoinRoot.isDomain_of_prime hXiIrred.prime
  constructor
  · intro hdivision
    have hAffine :=
      splitTraceAffineToKummerTop_injective_of_syntacticNormalForm_division
        sigma hsigma e d heOdd hdOdd hde hnondegenerate hdivision
    have hLaurent := splitTraceLaurentToKummerTop_injective_of_affine_injective
      sigma hsigma e d heOdd hdOdd hde hAffine
    exact hLaurent
  · intro hLaurent p hnormal
    exact splitTracePolynomialSyntacticNormalForm_division_of_laurentInjective
      sigma hsigma e d heOdd hdOdd hde hLaurent p hnormal

end OddCoprime

end

end BGS.Markoff
