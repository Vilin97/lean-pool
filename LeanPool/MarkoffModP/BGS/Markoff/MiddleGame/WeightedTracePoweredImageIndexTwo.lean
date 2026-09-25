/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageExactSupportIndexBound
public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierFromGeneral
public import Mathlib.Tactic

/-!
# Powered-image index two for the weighted trace curve

Three always-present monomials of the nonzero-weight trace closure have
exponents `(1,0)`, `(2,1)`, and `(0,1)`. Their support determinant is `2`.
Retaining this exact sparse-support certificate lowers the source-to-powered
image index bound from the generic bidegree value `8` to `2`.
-/

@[expose] public section

namespace BGS.Markoff

open BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

private def weightedTraceSupportAlpha : Fin 2 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 2

private def weightedTraceSupportRightConstant : Fin 2 →₀ ℕ :=
  Finsupp.single 0 1

private def weightedTraceSupportMixed : Fin 2 →₀ ℕ :=
  Finsupp.single 0 2 + Finsupp.single 1 1

private def weightedTraceSupportLeftConstant : Fin 2 →₀ ℕ :=
  Finsupp.single 1 1

private theorem weightedTraceX_eq_monomial (i : Fin 2) :
    (MvPolynomial.X i : MvPolynomial (Fin 2) K) =
      MvPolynomial.monomial (Finsupp.single i 1) 1 := by
  rw [← pow_one (MvPolynomial.X i), MvPolynomial.X_pow_eq_monomial]

private theorem splitTraceCoverPolynomial_one_one_eq_monomials
    (alpha beta : K) :
    splitTraceCoverPolynomial alpha beta 1 1 =
      MvPolynomial.monomial weightedTraceSupportAlpha alpha +
        MvPolynomial.monomial weightedTraceSupportRightConstant beta -
        MvPolynomial.monomial weightedTraceSupportMixed 1 -
        MvPolynomial.monomial weightedTraceSupportLeftConstant 1 := by
  rw [splitTraceCoverPolynomial]
  norm_num only [pow_one, mul_one]
  rw [MvPolynomial.C_mul_X_eq_monomial,
    MvPolynomial.C_mul_X_eq_monomial,
    MvPolynomial.X_pow_eq_monomial,
    weightedTraceX_eq_monomial, weightedTraceX_eq_monomial]
  simp [MvPolynomial.monomial_pow, weightedTraceSupportAlpha,
    weightedTraceSupportRightConstant, weightedTraceSupportMixed,
    weightedTraceSupportLeftConstant]

private theorem weightedTraceSupportRightConstant_mem
    (alpha beta : K) (hbeta : beta ≠ 0) :
    weightedTraceSupportRightConstant ∈
      (weightedTraceTorusClosurePolynomial alpha beta).support := by
  rw [weightedTraceTorusClosurePolynomial, ite_eq_right hbeta]
  rw [splitTraceCoverPolynomial_one_one_eq_monomials]
  rw [MvPolynomial.mem_support_iff]
  simp [weightedTraceSupportAlpha, weightedTraceSupportRightConstant,
    weightedTraceSupportMixed, weightedTraceSupportLeftConstant, hbeta,
    Finsupp.ext_iff]

private theorem weightedTraceSupportMixed_mem
    (alpha beta : K) (hbeta : beta ≠ 0) :
    weightedTraceSupportMixed ∈
      (weightedTraceTorusClosurePolynomial alpha beta).support := by
  rw [weightedTraceTorusClosurePolynomial, ite_eq_right hbeta]
  rw [splitTraceCoverPolynomial_one_one_eq_monomials]
  rw [MvPolynomial.mem_support_iff]
  simp [weightedTraceSupportAlpha, weightedTraceSupportRightConstant,
    weightedTraceSupportMixed, weightedTraceSupportLeftConstant,
    Finsupp.ext_iff]

private theorem weightedTraceSupportLeftConstant_mem
    (alpha beta : K) (hbeta : beta ≠ 0) :
    weightedTraceSupportLeftConstant ∈
      (weightedTraceTorusClosurePolynomial alpha beta).support := by
  rw [weightedTraceTorusClosurePolynomial, ite_eq_right hbeta]
  rw [splitTraceCoverPolynomial_one_one_eq_monomials]
  rw [MvPolynomial.mem_support_iff]
  simp [weightedTraceSupportAlpha, weightedTraceSupportRightConstant,
    weightedTraceSupportMixed, weightedTraceSupportLeftConstant,
    Finsupp.ext_iff]

private theorem weightedTraceSupportDeterminant :
    planeCurveSupportDifferenceDet
        weightedTraceSupportRightConstant
        weightedTraceSupportMixed
        weightedTraceSupportLeftConstant = 2 := by
  simp [planeCurveSupportDifferenceDet,
    weightedTraceSupportRightConstant, weightedTraceSupportMixed,
    weightedTraceSupportLeftConstant]

/-- The exact support determinant gives powered-image index at most two for
every prime-to-characteristic pair of powers. -/
theorem weightedTraceTorusClosure_poweredImageIndex_le_two
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (alpha beta : K)
    (hadmissible : WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmPrime : ¬ p ∣ m) (hnPrime : ¬ p ∣ n) :
    let f := weightedTraceTorusClosurePolynomial alpha beta
    let hf : Irreducible f :=
      irreducible_of_irreducible_map_algebraicClosure
        hadmissible.2.2.2.1
    letI := planeCurveCoordinateRing_isDomain hf
    Module.finrank (PoweredImageOverFirst f m n)
        (PlaneCurveFunctionField f) ≤ 2 := by
  let f := weightedTraceTorusClosurePolynomial alpha beta
  let hf : Irreducible f :=
    irreducible_of_irreducible_map_algebraicClosure
      hadmissible.2.2.2.1
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  have hindex :=
    finrank_poweredImageOverFirst_le_supportDet
      (p := p) hadmissible.2.2.2.1
      (weightedTraceTorusClosurePolynomial_pderiv_first_ne_zero
        alpha beta hadmissible.2.1)
      (weightedTraceTorusClosurePolynomial_pderiv_second_ne_zero
        alpha beta hadmissible.2.1)
      (weightedTraceSupportRightConstant_mem
        alpha beta hadmissible.2.1)
      (weightedTraceSupportMixed_mem
        alpha beta hadmissible.2.1)
      (weightedTraceSupportLeftConstant_mem
        alpha beta hadmissible.2.1)
      (by rw [weightedTraceSupportDeterminant]; norm_num)
      m n hm hn hmPrime hnPrime
  rw [weightedTraceSupportDeterminant] at hindex
  norm_num at hindex ⊢
  exact hindex

end

end BGS.Markoff
