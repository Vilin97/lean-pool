/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.SemanticNormalForm
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Syntactic monomial reduction for the split trace cover

This file starts the source-side quotient reduction.  A monomial `xi^i * eta^j` is reduced by
Euclidean division of `i` by `d` and `j` by `e`.  Its rectangular basis index is
`(j % e, i % d)`, and its coefficient in the quadratic base function field is
`u^(i / d) * v^(i / d + j / e)`.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

theorem pow_eq_pow_div_mul_pow_mod
    {M : Type*} [Monoid M] (x : M) (n q : ℕ) :
    x ^ n = (x ^ q) ^ (n / q) * x ^ (n % q) := by
  calc
    x ^ n = x ^ (q * (n / q) + n % q) := by rw [Nat.div_add_mod n q]
    _ = x ^ (q * (n / q)) * x ^ (n % q) := by rw [pow_add]
    _ = (x ^ q) ^ (n / q) * x ^ (n % q) := by
      rw [pow_mul]

variable {K : Type*} [Field K]

section OddCoprime

variable (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
  (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)

private lemma etaExponent_pos (e : ℕ) (heOdd : Odd e) : 0 < e := by
  rcases heOdd with ⟨k, rfl⟩
  omega

private lemma xiExponent_pos (d : ℕ) (hdOdd : Odd d) : 0 < d := by
  rcases hdOdd with ⟨k, rfl⟩
  omega

private lemma etaExponent_ne_zero (e : ℕ) (heOdd : Odd e) : e ≠ 0 :=
  (etaExponent_pos e heOdd).ne'

private lemma xiExponent_ne_zero (d : ℕ) (hdOdd : Odd d) : d ≠ 0 :=
  (xiExponent_pos d hdOdd).ne'

theorem splitTraceEtaKummerPolynomial_natDegree
    (sigma : K) (hsigma : sigma ≠ 0) (e : ℕ) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    (splitTraceEtaKummerPolynomial sigma e).natDegree = e := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  change (X ^ e - C (splitTraceBaseV sigma)).natDegree = e
  exact natDegree_X_pow_sub_C

theorem splitTraceXiKummerPolynomial_natDegree
    (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ) (heOdd : Odd e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    (splitTraceXiKummerPolynomial sigma e d).natDegree = d := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  change (X ^ d - C (splitTraceXiRadicand sigma e)).natDegree = d
  exact natDegree_X_pow_sub_C

/-- Residual rectangular index of the monomial `xi^i * eta^j`. -/
def splitTraceMonomialNormalIndex (i j : ℕ) :
    Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  exact (⟨j % e, by
      rw [splitTraceEtaKummerPolynomial_natDegree sigma hsigma e]
      exact Nat.mod_lt _ (etaExponent_pos e heOdd)⟩,
    ⟨i % d, by
      rw [splitTraceXiKummerPolynomial_natDegree sigma hsigma e d heOdd]
      exact Nat.mod_lt _ (xiExponent_pos d hdOdd)⟩)

@[simp]
theorem splitTraceMonomialNormalIndex_fst_val (i j : ℕ) :
    (splitTraceMonomialNormalIndex sigma hsigma e d heOdd hdOdd i j).1.val = j % e := by
  rfl

@[simp]
theorem splitTraceMonomialNormalIndex_snd_val (i j : ℕ) :
    (splitTraceMonomialNormalIndex sigma hsigma e d heOdd hdOdd i j).2.val = i % d := by
  rfl

/-- Base-function-field coefficient extracted from `xi^i * eta^j`. -/
def splitTraceMonomialNormalCoefficient (i j : ℕ) :
    SplitTraceBaseFunctionField K sigma :=
  splitTraceBaseU sigma ^ (i / d) *
    splitTraceBaseV sigma ^ (i / d + j / e)

/-- Evaluate a rectangular coefficient vector by the explicit normal monomial family. -/
def splitTraceExplicitNormalFormEvaluation
    (c : (Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) →₀
        AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :
    SplitTraceXiFunctionField K sigma e d := by
  letI : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
    AdjoinRoot.instCommRing _
  exact Finsupp.linearCombination (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
    (fun ji ↦ splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
      splitTraceXiRoot sigma e d ^ (ji.2 : ℕ)) c

/-- Explicit source-side rectangular coefficients of a polynomial in the two affine coordinates.
Each source monomial is reduced independently by quotient and remainder of its two exponents. -/
def splitTracePolynomialSyntacticNormalForm
    (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
    (heOdd : Odd e) (hdOdd : Odd d)
    (p : MvPolynomial (Fin 2) K) :
    (Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) →₀
        AdjoinRoot (splitTraceBaseKummerPolynomial sigma) :=
  (AddMonoidAlgebra.coeff p).sum fun ex c ↦
    Finsupp.single
      (splitTraceMonomialNormalIndex sigma hsigma e d heOdd hdOdd (ex 0) (ex 1))
      (algebraMap K (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) c *
        splitTraceMonomialNormalCoefficient sigma e d (ex 0) (ex 1))

@[simp]
theorem splitTracePolynomialSyntacticNormalForm_zero :
    splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd 0 = 0 := by
  simp [splitTracePolynomialSyntacticNormalForm]

theorem splitTracePolynomialSyntacticNormalForm_add
    (p q : MvPolynomial (Fin 2) K) :
    splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd (p + q) =
      splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd p +
        splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd q := by
  classical
  simp only [splitTracePolynomialSyntacticNormalForm]
  apply Finsupp.sum_add_index
  · intro ex
    simp
  · intro ex _ a b
    simp only [map_add, add_mul, Finsupp.single_add]

@[simp]
theorem splitTracePolynomialSyntacticNormalForm_monomial
    (ex : Fin 2 →₀ ℕ) (c : K) :
    splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd
        (MvPolynomial.monomial ex c) =
      Finsupp.single
        (splitTraceMonomialNormalIndex sigma hsigma e d heOdd hdOdd (ex 0) (ex 1))
        (algebraMap K (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) c *
          splitTraceMonomialNormalCoefficient sigma e d (ex 0) (ex 1)) := by
  rw [splitTracePolynomialSyntacticNormalForm]
  apply MvPolynomial.sum_monomial_eq
  simp

lemma splitTraceEtaRootInXiField_pow :
    splitTraceEtaRootInXiField sigma e d ^ e =
      splitTraceBaseElementInXiField sigma e d (splitTraceBaseV sigma) := by
  have h := congrArg
    (algebraMap (SplitTraceEtaFunctionField K sigma e)
      (SplitTraceXiFunctionField K sigma e d))
    (splitTraceEtaRoot_pow (K := K) sigma e)
  simpa [splitTraceEtaRootInXiField, splitTraceBaseElementInXiField] using h

/-- Explicit source-side monomial reduction in the Kummer top algebra. -/
theorem splitTraceKummer_monomial_reduction
    (sigma : K) (e d i j : ℕ) :
    splitTraceXiRoot sigma e d ^ i * splitTraceEtaRootInXiField sigma e d ^ j =
      splitTraceBaseElementInXiField sigma e d
          (splitTraceMonomialNormalCoefficient sigma e d i j) *
        (splitTraceEtaRootInXiField sigma e d ^ (j % e) *
          splitTraceXiRoot sigma e d ^ (i % d)) := by
  rw [pow_eq_pow_div_mul_pow_mod _ i d,
    pow_eq_pow_div_mul_pow_mod _ j e,
    splitTraceXiRoot_pow, splitTraceEtaRootInXiField_pow]
  simp only [splitTraceXiRadicand, splitTraceMonomialNormalCoefficient,
    splitTraceBaseElementInXiField, map_mul, map_pow]
  ring

/-- The explicit normal-form evaluation of the singleton produced from a source monomial is the
original monomial in the Kummer top algebra. -/
theorem splitTraceExplicitNormalFormEvaluation_single_monomial (i j : ℕ) :
    splitTraceExplicitNormalFormEvaluation sigma e d
        (Finsupp.single
          (splitTraceMonomialNormalIndex sigma hsigma e d heOdd hdOdd i j)
          (splitTraceMonomialNormalCoefficient sigma e d i j)) =
      splitTraceXiRoot sigma e d ^ i * splitTraceEtaRootInXiField sigma e d ^ j := by
  letI : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
    AdjoinRoot.instCommRing _
  rw [splitTraceExplicitNormalFormEvaluation, Finsupp.linearCombination_single]
  simp only [Algebra.smul_def, splitTraceMonomialNormalIndex_fst_val,
    splitTraceMonomialNormalIndex_snd_val]
  rw [IsScalarTower.algebraMap_apply
    (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
    (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e))
    (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d))]
  simpa [splitTraceBaseElementInXiField] using
    (splitTraceKummer_monomial_reduction (K := K) sigma e d i j).symm

/-- Including the source coefficient, explicit evaluation of the syntactic singleton agrees with
evaluation of the original source monomial. -/
theorem splitTraceExplicitNormalFormEvaluation_single_scaled_monomial
    (c : K) (i j : ℕ) :
    splitTraceExplicitNormalFormEvaluation sigma e d
        (Finsupp.single
          (splitTraceMonomialNormalIndex sigma hsigma e d heOdd hdOdd i j)
          (algebraMap K (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) c *
            splitTraceMonomialNormalCoefficient sigma e d i j)) =
      algebraMap K (SplitTraceXiFunctionField K sigma e d) c *
        (splitTraceXiRoot sigma e d ^ i * splitTraceEtaRootInXiField sigma e d ^ j) := by
  letI : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
    AdjoinRoot.instCommRing _
  rw [splitTraceExplicitNormalFormEvaluation, Finsupp.linearCombination_single]
  simp only [Algebra.smul_def, splitTraceMonomialNormalIndex_fst_val,
    splitTraceMonomialNormalIndex_snd_val, map_mul]
  have hred := (splitTraceKummer_monomial_reduction
    (K := K) sigma e d i j).symm
  rw [← hred]
  simp only [splitTraceBaseElementInXiField]
  simp_rw [IsScalarTower.algebraMap_apply K
    (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
    (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d))]
  simp_rw [IsScalarTower.algebraMap_apply
    (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
    (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e))
    (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d))]
  ring

theorem splitTracePolynomialToKummerTop_monomial
    (ex : Fin 2 →₀ ℕ) (c : K) :
    splitTracePolynomialToKummerTop sigma hsigma e d heOdd hdOdd hde
        (MvPolynomial.monomial ex c) =
      algebraMap K (SplitTraceXiFunctionField K sigma e d) c *
        (splitTraceXiRoot sigma e d ^ (ex 0) *
          splitTraceEtaRootInXiField sigma e d ^ (ex 1)) := by
  simp [splitTracePolynomialToKummerTop, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_monomial, Fin.prod_univ_two]

/-- Evaluation of the explicit syntactic coefficient vector agrees with direct polynomial
evaluation at the two Kummer roots. -/
theorem splitTracePolynomialSyntacticNormalForm_evaluation
    (p : MvPolynomial (Fin 2) K) :
    splitTraceExplicitNormalFormEvaluation sigma e d
        (splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd p) =
      splitTracePolynomialToKummerTop sigma hsigma e d heOdd hdOdd hde p := by
  induction p using MvPolynomial.induction_on' with
  | monomial ex c =>
      rw [splitTracePolynomialSyntacticNormalForm_monomial,
        splitTraceExplicitNormalFormEvaluation_single_scaled_monomial,
        splitTracePolynomialToKummerTop_monomial]
  | add p q hp hq =>
      rw [splitTracePolynomialSyntacticNormalForm_add]
      change Finsupp.linearCombination
          (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
          (fun ji ↦ splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
            splitTraceXiRoot sigma e d ^ (ji.2 : ℕ))
          (splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd p +
            splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd q) = _
      change Finsupp.linearCombination
          (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
          (fun ji ↦ splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
            splitTraceXiRoot sigma e d ^ (ji.2 : ℕ))
          (splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd p) = _ at hp
      change Finsupp.linearCombination
          (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
          (fun ji ↦ splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
            splitTraceXiRoot sigma e d ^ (ji.2 : ℕ))
          (splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd q) = _ at hq
      rw [map_add, hp, hq, map_add]

/-- The committed normal-monomial independence theorem makes explicit normal-form evaluation
injective. -/
theorem splitTraceExplicitNormalFormEvaluation_eq_zero_iff
    (sigma : K) (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)
    (c : (Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) →₀
        AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :
    letI : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
      AdjoinRoot.instCommRing _
    letI : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
      AdjoinRoot.instCommRing _
    letI : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
      AdjoinRoot.instCommRing _
    splitTraceExplicitNormalFormEvaluation sigma e d c = 0 ↔ c = 0 := by
  letI : CommRing (AdjoinRoot (splitTraceBaseKummerPolynomial sigma)) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (AdjoinRoot (splitTraceEtaKummerPolynomial sigma e)) :=
    AdjoinRoot.instCommRing _
  letI : CommRing (AdjoinRoot (splitTraceXiKummerPolynomial sigma e d)) :=
    AdjoinRoot.instCommRing _
  change Finsupp.linearCombination (AdjoinRoot (splitTraceBaseKummerPolynomial sigma))
      (fun ji ↦ splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
        splitTraceXiRoot sigma e d ^ (ji.2 : ℕ)) c = 0 ↔ c = 0
  exact splitTraceEtaXiNormalForm_evaluation_eq_zero_iff
    sigma e d heOdd hdOdd hde c

/-- A source polynomial has zero syntactic normal form exactly when its evaluation at the Kummer
roots vanishes.  The remaining injectivity wall is to identify this explicit zero condition with
membership in the principal ideal generated by the trace-cover polynomial. -/
theorem splitTracePolynomialSyntacticNormalForm_eq_zero_iff
    (p : MvPolynomial (Fin 2) K) :
    splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd p = 0 ↔
      splitTracePolynomialToKummerTop sigma hsigma e d heOdd hdOdd hde p = 0 := by
  rw [← splitTracePolynomialSyntacticNormalForm_evaluation
    sigma hsigma e d heOdd hdOdd hde p]
  exact (splitTraceExplicitNormalFormEvaluation_eq_zero_iff
    sigma e d heOdd hdOdd hde
      (splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd p)).symm

/-- For a nondegenerate trace parameter, the remaining source-side division theorem is sufficient
for injectivity of the affine comparison map.  The division hypothesis is deliberately an ordinary
explicit proposition: it is not an assumed declaration, typeclass, or structure field.  The
condition `sigma ≠ 1` is essential: at `sigma = 1` the cleared cover factors and the Kummer tower
selects only one component; see `TraceCurveSyntacticDivisionObstruction`. -/
theorem splitTraceAffineToKummerTop_injective_of_syntacticNormalForm_division
    (_hnondegenerate : sigma ≠ 1)
    (hdivision : ∀ p : MvPolynomial (Fin 2) K,
      splitTracePolynomialSyntacticNormalForm sigma hsigma e d heOdd hdOdd p = 0 →
        p ∈ Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e}) :
    Function.Injective
      (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  let I : Ideal (MvPolynomial (Fin 2) K) :=
    Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e}
  let f : MvPolynomial (Fin 2) K →+*
      SplitTraceXiFunctionField K sigma e d :=
    (splitTracePolynomialToKummerTop sigma hsigma e d heOdd hdOdd hde).toRingHom
  have hIdeal : ∀ p : MvPolynomial (Fin 2) K, p ∈ I → f p = 0 := by
    have hle : I ≤ RingHom.ker f := by
      dsimp [I]
      rw [Ideal.span_le]
      intro q hq
      simp only [Set.mem_singleton_iff] at hq
      subst q
      exact splitTracePolynomialToKummerTop_relation sigma hsigma e d heOdd hdOdd hde
    intro p hp
    exact hle hp
  have hKernel : RingHom.ker f ≤ I := by
    intro p hp
    apply hdivision p
    apply (splitTracePolynomialSyntacticNormalForm_eq_zero_iff
      sigma hsigma e d heOdd hdOdd hde p).2
    exact hp
  have hinjective := RingHom.lift_injective_of_ker_le_ideal I hIdeal hKernel
  have hsame :
      (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde).toRingHom =
        Ideal.Quotient.lift I f hIdeal := by
    apply Ideal.Quotient.ringHom_ext
    apply DFunLike.ext _ _
    intro p
    change f p = Ideal.Quotient.lift I f hIdeal (Ideal.Quotient.mk I p)
    rw [Ideal.Quotient.lift_mk]
  intro x y hxy
  apply hinjective
  rw [← hsame]
  exact hxy

end OddCoprime

end

end BGS.Markoff
