/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.SyntacticDivisionCriterion
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedIrreducibility
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Injectivity of the Laurent comparison from cover irreducibility

This file identifies the remaining Laurent-to-Kummer comparison wall with the actual
irreducibility assertion in the paper.  The canonical `eta` coordinate in the Kummer tower is
proved transcendental over the constant field.  Consequently it may be used as the coefficient
parameter in a rational-function field.  An irreducible cleared cover polynomial then becomes the
minimal polynomial of the `xi` coordinate, so evaluation has exactly the expected principal
kernel.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

section Transcendence

/-- The rational radicand is not a constant rational function. -/
theorem splitTraceRadicand_not_constant (sigma : K) (hsigma : sigma ≠ 0) :
    ¬ ∃ c : K, splitTraceRadicand sigma = RatFunc.C c := by
  rintro ⟨c, hc⟩
  have hdegree := congrArg RatFunc.intDegree hc
  rw [splitTraceRadicand_intDegree sigma hsigma] at hdegree
  by_cases hc0 : c = 0
  · subst c
    exact splitTraceRadicand_ne_zero sigma hsigma (by simpa using hc)
  · simp at hdegree

/-- The quadratic base coordinate is transcendental over the constant field. -/
theorem splitTraceBaseV_transcendental (sigma : K) (hsigma : sigma ≠ 0) :
    Transcendental K (splitTraceBaseV sigma) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  have hradicand : Transcendental K (splitTraceRadicand sigma) :=
    RatFunc.transcendental_of_ne_C _
      (splitTraceRadicand_not_constant sigma hsigma)
  have hmapped : Transcendental K
      (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma)
        (splitTraceRadicand sigma)) :=
    (transcendental_algebraMap_iff
      (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma)).injective).2
        hradicand
  rw [← splitTraceBaseV_sq (sigma := sigma)] at hmapped
  intro hV
  exact hmapped (hV.pow 2)

/-- The `eta` coordinate of the explicit odd-coprime Kummer tower is transcendental over `K`.
This is the coefficient-field input needed to turn bivariate evaluation into honest univariate
minimal-polynomial evaluation. -/
theorem splitTraceEtaRootInXiField_transcendental
    (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
    (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    Transcendental K (splitTraceEtaRootInXiField sigma e d) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  have hBaseV : Transcendental K (splitTraceBaseV sigma) :=
    splitTraceBaseV_transcendental sigma hsigma
  have hBaseVTop : Transcendental K
      (splitTraceBaseElementInXiField sigma e d (splitTraceBaseV sigma)) := by
    have hmap : Transcendental K
        (algebraMap (SplitTraceBaseFunctionField K sigma)
          (SplitTraceXiFunctionField K sigma e d) (splitTraceBaseV sigma)) :=
      (transcendental_algebraMap_iff
        (algebraMap (SplitTraceBaseFunctionField K sigma)
          (SplitTraceXiFunctionField K sigma e d)).injective).2 hBaseV
    rw [splitTraceBaseElementInXiField,
      ← IsScalarTower.algebraMap_apply
        (SplitTraceBaseFunctionField K sigma)
        (SplitTraceEtaFunctionField K sigma e)
        (SplitTraceXiFunctionField K sigma e d)]
    exact hmap
  rw [← splitTraceEtaRootInXiField_pow (sigma := sigma) (e := e) (d := d)] at hBaseVTop
  intro hEta
  exact hBaseVTop (hEta.pow e)

end Transcendence

section IteratedPresentation

/-- The cleared cover, viewed as a polynomial in `x` with coefficients in `K[y]`. -/
noncomputable def splitTraceCoverIteratedPolynomial
    (sigma : K) (d e : ℕ) : Polynomial K[X] :=
  monomial (2 * d) (-(X ^ e)) +
    monomial d (X ^ (2 * e) + C sigma) +
    C (-(X ^ e))

theorem finTwoToIteratedPolynomial_splitTraceCoverPolynomial
    (sigma : K) (d e : ℕ) :
    finTwoToIteratedPolynomial (K := K)
        (splitTraceCoverPolynomial (1 : K) sigma d e) =
      splitTraceCoverIteratedPolynomial sigma d e := by
  simp [splitTraceCoverPolynomial, splitTraceCoverIteratedPolynomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem splitTraceCoverIteratedPolynomial_coeff_two_mul
    (sigma : K) (d e : ℕ) (hd : d ≠ 0) :
    (splitTraceCoverIteratedPolynomial sigma d e).coeff (2 * d) = -(X ^ e) := by
  have htwo_d_ne_d : 2 * d ≠ d := by omega
  have hd_ne_two_d : d ≠ 2 * d := by omega
  have htwo_d_ne_zero : 2 * d ≠ 0 := by omega
  rw [splitTraceCoverIteratedPolynomial, coeff_add, coeff_add,
    coeff_monomial, coeff_monomial, coeff_C_of_ne_zero htwo_d_ne_zero]
  simp [hd_ne_two_d]

theorem splitTraceCoverIteratedPolynomial_natDegree_ne_zero
    (sigma : K) (d e : ℕ) (hd : d ≠ 0) :
    (splitTraceCoverIteratedPolynomial sigma d e).natDegree ≠ 0 := by
  have hcoeff : (splitTraceCoverIteratedPolynomial sigma d e).coeff (2 * d) ≠ 0 := by
    rw [splitTraceCoverIteratedPolynomial_coeff_two_mul sigma d e hd]
    exact neg_ne_zero.mpr (pow_ne_zero e X_ne_zero)
  have hle := Polynomial.le_natDegree_of_ne_zero hcoeff
  omega

/-- Evaluation through the iterated-polynomial presentation is ordinary bivariate evaluation.
The outer polynomial variable is coordinate `0`, while the coefficient-polynomial variable is
coordinate `1`. -/
theorem finTwoToIteratedPolynomial_aeval
    {A : Type*} [CommRing A] [Algebra K A]
    (p : MvPolynomial (Fin 2) K) (x y : A) :
    Polynomial.aevalTower (Polynomial.aeval y) x
        (finTwoToIteratedPolynomial (K := K) p) =
      MvPolynomial.aeval ![x, y] p := by
  let lhs : MvPolynomial (Fin 2) K →ₐ[K] A :=
    (Polynomial.aevalTower (Polynomial.aeval y) x).comp
      (finTwoToIteratedPolynomial (K := K)).toAlgHom
  let rhs : MvPolynomial (Fin 2) K →ₐ[K] A :=
    MvPolynomial.aeval ![x, y]
  have heq : lhs = rhs := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [lhs, rhs, finTwoToIteratedPolynomial_X_zero,
        finTwoToIteratedPolynomial_X_one]
  exact DFunLike.congr_fun heq p

private def splitTraceEtaPolynomialEvaluation
    (sigma : K) (e d : ℕ) :
    K[X] →ₐ[K] SplitTraceXiFunctionField K sigma e d :=
  Polynomial.aeval (splitTraceEtaRootInXiField sigma e d)

private theorem splitTraceEtaPolynomialEvaluation_injective
    (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
    (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    Function.Injective (splitTraceEtaPolynomialEvaluation sigma e d) := by
  exact transcendental_iff_injective.mp
    (splitTraceEtaRootInXiField_transcendental
      sigma hsigma e d heOdd hdOdd hde)

private def splitTraceEtaRatFuncEvaluation
    (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
    (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    RatFunc K →ₐ[K] SplitTraceXiFunctionField K sigma e d := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  letI : IsDomain (SplitTraceXiFunctionField K sigma e d) :=
    AdjoinRoot.isDomain_of_prime hXiIrred.prime
  exact RatFunc.liftAlgHom (K := K) (S := K)
    (L := SplitTraceXiFunctionField K sigma e d)
    (splitTraceEtaPolynomialEvaluation sigma e d)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (splitTraceEtaPolynomialEvaluation_injective
        sigma hsigma e d heOdd hdOdd hde))

private theorem splitTraceEtaRatFuncEvaluation_algebraMap
    (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
    (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)
    (q : K[X]) :
    splitTraceEtaRatFuncEvaluation sigma hsigma e d heOdd hdOdd hde
        (algebraMap K[X] (RatFunc K) q) =
      splitTraceEtaPolynomialEvaluation sigma e d q := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  exact RatFunc.liftRingHom_algebraMap _ _ q

/-- Mapping an iterated polynomial to `K(y)[x]` and then specializing the transcendental
coefficient parameter `y` to the Kummer `eta` coordinate recovers direct bivariate evaluation. -/
theorem splitTraceIteratedFractionEvaluation
    (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
    (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)
    (p : MvPolynomial (Fin 2) K) :
    Polynomial.eval₂
        (splitTraceEtaRatFuncEvaluation sigma hsigma e d heOdd hdOdd hde).toRingHom
        (splitTraceXiRoot sigma e d)
        ((finTwoToIteratedPolynomial (K := K) p).map
          (algebraMap K[X] (RatFunc K))) =
      MvPolynomial.aeval
        ![splitTraceXiRoot sigma e d, splitTraceEtaRootInXiField sigma e d] p := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  rw [Polynomial.eval₂_map]
  have hcomp :
      (splitTraceEtaRatFuncEvaluation sigma hsigma e d heOdd hdOdd hde).toRingHom.comp
          (algebraMap K[X] (RatFunc K)) =
        (splitTraceEtaPolynomialEvaluation sigma e d).toRingHom := by
    apply DFunLike.ext _ _
    intro q
    exact splitTraceEtaRatFuncEvaluation_algebraMap
      sigma hsigma e d heOdd hdOdd hde q
  rw [hcomp]
  exact finTwoToIteratedPolynomial_aeval p
    (splitTraceXiRoot sigma e d) (splitTraceEtaRootInXiField sigma e d)

/-- Once the actual cleared cover polynomial is irreducible, its principal ideal is the full
kernel of evaluation at the Kummer coordinates.  The proof uses `eta` as a transcendental
coefficient parameter and the irreducible iterated polynomial as the minimal polynomial of
`xi`. -/
theorem splitTracePolynomial_mem_span_of_cover_irreducible_and_maps_to_zero
    (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
    (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)
    (hcover : Irreducible (splitTraceCoverPolynomial (1 : K) sigma d e))
    (p : MvPolynomial (Fin 2) K)
    (hp : splitTracePolynomialToKummerTop
      sigma hsigma e d heOdd hdOdd hde p = 0) :
    p ∈ Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e} := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  letI : IsDomain (SplitTraceXiFunctionField K sigma e d) :=
    AdjoinRoot.isDomain_of_prime hXiIrred.prime
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hdOdd
  let q : Polynomial K[X] := splitTraceCoverIteratedPolynomial sigma d e
  let r : Polynomial K[X] := finTwoToIteratedPolynomial (K := K) p
  have hqIrred : Irreducible q := by
    have hmapped := hcover.map (finTwoToIteratedPolynomial (K := K))
    simpa [q, finTwoToIteratedPolynomial_splitTraceCoverPolynomial] using hmapped
  have hqPrimitive : q.IsPrimitive :=
    hqIrred.isPrimitive
      (splitTraceCoverIteratedPolynomial_natDegree_ne_zero sigma d e hd)
  have hqFractionIrred : Irreducible
      (q.map (algebraMap K[X] (RatFunc K))) :=
    hqPrimitive.irreducible_iff_irreducible_map_fraction_map.mp hqIrred
  have hcoverEval : MvPolynomial.aeval
      ![splitTraceXiRoot sigma e d, splitTraceEtaRootInXiField sigma e d]
        (splitTraceCoverPolynomial (1 : K) sigma d e) = 0 := by
    simpa [splitTracePolynomialToKummerTop, MvPolynomial.aeval_def] using
      splitTracePolynomialToKummerTop_relation
        sigma hsigma e d heOdd hdOdd hde
  have hpEval : MvPolynomial.aeval
      ![splitTraceXiRoot sigma e d, splitTraceEtaRootInXiField sigma e d] p = 0 := by
    simpa [splitTracePolynomialToKummerTop, MvPolynomial.aeval_def] using hp
  let phi : RatFunc K →ₐ[K] SplitTraceXiFunctionField K sigma e d :=
    splitTraceEtaRatFuncEvaluation sigma hsigma e d heOdd hdOdd hde
  letI : Algebra (RatFunc K) (SplitTraceXiFunctionField K sigma e d) :=
    phi.toRingHom.toAlgebra
  have hqRoot : Polynomial.aeval (splitTraceXiRoot sigma e d)
      (q.map (algebraMap K[X] (RatFunc K))) = 0 := by
    rw [Polynomial.aeval_def]
    change Polynomial.eval₂ phi.toRingHom (splitTraceXiRoot sigma e d)
      (q.map (algebraMap K[X] (RatFunc K))) = 0
    simpa [phi, q, finTwoToIteratedPolynomial_splitTraceCoverPolynomial] using
      (splitTraceIteratedFractionEvaluation
        sigma hsigma e d heOdd hdOdd hde
          (splitTraceCoverPolynomial (1 : K) sigma d e)).trans hcoverEval
  have hpRoot : Polynomial.aeval (splitTraceXiRoot sigma e d)
      (r.map (algebraMap K[X] (RatFunc K))) = 0 := by
    rw [Polynomial.aeval_def]
    change Polynomial.eval₂ phi.toRingHom (splitTraceXiRoot sigma e d)
      (r.map (algebraMap K[X] (RatFunc K))) = 0
    simpa [phi, r] using
      (splitTraceIteratedFractionEvaluation
        sigma hsigma e d heOdd hdOdd hde p).trans hpEval
  have hminpoly :
      q.map (algebraMap K[X] (RatFunc K)) *
          C (q.map (algebraMap K[X] (RatFunc K))).leadingCoeff⁻¹ =
        minpoly (RatFunc K) (splitTraceXiRoot sigma e d) :=
    minpoly.eq_of_irreducible hqFractionIrred hqRoot
  have hqDvdMinpoly :
      q.map (algebraMap K[X] (RatFunc K)) ∣
        minpoly (RatFunc K) (splitTraceXiRoot sigma e d) :=
    ⟨C (q.map (algebraMap K[X] (RatFunc K))).leadingCoeff⁻¹,
      hminpoly.symm⟩
  have hminpolyDvd :
      minpoly (RatFunc K) (splitTraceXiRoot sigma e d) ∣
        r.map (algebraMap K[X] (RatFunc K)) :=
    minpoly.dvd (RatFunc K) (splitTraceXiRoot sigma e d) hpRoot
  have hqDvdFraction :
      q.map (algebraMap K[X] (RatFunc K)) ∣
        r.map (algebraMap K[X] (RatFunc K)) :=
    hqDvdMinpoly.trans hminpolyDvd
  have hqDvd : q ∣ r :=
    hqPrimitive.dvd_of_fraction_map_dvd_fraction_map hqDvdFraction
  rw [Ideal.mem_span_singleton]
  rcases hqDvd with ⟨s, hs⟩
  refine ⟨(finTwoToIteratedPolynomial (K := K)).symm s, ?_⟩
  apply (finTwoToIteratedPolynomial (K := K)).injective
  simpa [q, r, finTwoToIteratedPolynomial_splitTraceCoverPolynomial] using hs

/-- The paper's irreducibility assertion is sufficient for injectivity of the explicit
Laurent-to-Kummer comparison map.  There is no additional hidden localization hypothesis: the
coordinate-product localization was already proved faithful. -/
theorem splitTraceLaurentToKummerTop_injective_of_coverPolynomial_irreducible
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)
    (hcover : Irreducible (splitTraceCoverPolynomial (1 : K) sigma d e)) :
    Function.Injective
      (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde) := by
  apply (splitTracePolynomialSyntacticNormalForm_division_iff_laurentInjective
    sigma hsigma e d heOdd hdOdd hde hnondegenerate).1
  intro p hnormal
  apply splitTracePolynomial_mem_span_of_cover_irreducible_and_maps_to_zero
    sigma hsigma e d heOdd hdOdd hde hcover p
  exact (splitTracePolynomialSyntacticNormalForm_eq_zero_iff
    sigma hsigma e d heOdd hdOdd hde p).1 hnormal

/-- Exact endgame wall: in the nondegenerate odd-coprime case, injectivity of the constructed
Laurent comparison is equivalent to irreducibility of the paper's cleared trace-cover polynomial.
Thus proving the published irreducibility lemma closes the comparison; no extra quotient-division
axiom is required. -/
theorem splitTraceLaurentToKummerTop_injective_iff_coverPolynomial_irreducible
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    Function.Injective
        (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde) ↔
      Irreducible (splitTraceCoverPolynomial (1 : K) sigma d e) := by
  constructor
  · exact splitTraceCoverPolynomial_irreducible_of_laurentInjective
      sigma hsigma e d heOdd hdOdd hde
  · exact splitTraceLaurentToKummerTop_injective_of_coverPolynomial_irreducible
      sigma hsigma hnondegenerate e d heOdd hdOdd hde

end IteratedPresentation

end

end BGS.Markoff
