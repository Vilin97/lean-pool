/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.LaurentComparisonInjectivity

/-!
# Irreducibility of the odd coprime split trace cover

The key source-side argument is a residue decomposition.  Every polynomial in `x,y` is written
uniquely as a sum of terms

`x^r * y^s * q_{r,s}(x^d, y^e)`, with `r < d` and `s < e`.

Evaluation in the Kummer tower sends the coefficient polynomial `q_{r,s}` to the degree-one
base trace curve at `(u*v,v)`.  Irreducibility of that already-proved degree-one curve therefore
forces each `q_{r,s}` to be divisible by the base cover equation.  Power substitution then shows
that the original polynomial is divisible by the `(d,e)` cover equation.  This proves the
source-division theorem without assuming the target irreducibility or either comparison-map
injectivity statement.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

section ResidueBlocks

variable (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
  (heOdd : Odd e) (hdOdd : Odd d)

/-- A two-variable exponent with the displayed exponents in coordinates `0,1`. -/
def finTwoExponent (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

theorem monomial_finTwoExponent (i j : ℕ) (c : K) :
    MvPolynomial.monomial (finTwoExponent i j) c =
      MvPolynomial.C c * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j := by
  rw [finTwoExponent, MvPolynomial.monomial_add_single,
    ← MvPolynomial.C_mul_X_pow_eq_monomial]

theorem finTwoExponent_of_finsupp (ex : Fin 2 →₀ ℕ) :
    finTwoExponent (ex 0) (ex 1) = ex := by
  ext k
  fin_cases k <;> simp [finTwoExponent]

/-- Substitute `x^d,y^e` for the two variables. -/
def splitTracePowerSubstitution :
    MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval ![MvPolynomial.X 0 ^ d, MvPolynomial.X 1 ^ e]

@[simp]
theorem splitTracePowerSubstitution_X_zero :
    splitTracePowerSubstitution (K := K) e d (MvPolynomial.X 0) =
      MvPolynomial.X 0 ^ d := by
  simp [splitTracePowerSubstitution]

@[simp]
theorem splitTracePowerSubstitution_X_one :
    splitTracePowerSubstitution (K := K) e d (MvPolynomial.X 1) =
      MvPolynomial.X 1 ^ e := by
  simp [splitTracePowerSubstitution]

@[simp]
theorem splitTracePowerSubstitution_C (c : K) :
    splitTracePowerSubstitution (K := K) e d (MvPolynomial.C c) =
      MvPolynomial.C c := by
  simp [splitTracePowerSubstitution]

/-- The polynomial coefficient in one residue block.  A monomial `x^i y^j` contributes
`X^(i/d) Y^(j/e)` to block `(j mod e, i mod d)`. -/
def splitTracePolynomialResidueBlocks (p : MvPolynomial (Fin 2) K) :
    (Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) →₀
        MvPolynomial (Fin 2) K :=
  (AddMonoidAlgebra.coeff p).sum fun ex c ↦
    Finsupp.single
      (splitTraceMonomialNormalIndex sigma hsigma e d heOdd hdOdd (ex 0) (ex 1))
      (MvPolynomial.monomial (finTwoExponent (ex 0 / d) (ex 1 / e)) c)

@[simp]
theorem splitTracePolynomialResidueBlocks_zero :
    splitTracePolynomialResidueBlocks sigma hsigma e d heOdd hdOdd 0 = 0 := by
  simp [splitTracePolynomialResidueBlocks]

theorem splitTracePolynomialResidueBlocks_add
    (p q : MvPolynomial (Fin 2) K) :
    splitTracePolynomialResidueBlocks sigma hsigma e d heOdd hdOdd (p + q) =
      splitTracePolynomialResidueBlocks sigma hsigma e d heOdd hdOdd p +
        splitTracePolynomialResidueBlocks sigma hsigma e d heOdd hdOdd q := by
  classical
  simp only [splitTracePolynomialResidueBlocks]
  apply Finsupp.sum_add_index
  · intro ex
    simp
  · intro ex _ a b
    simp only [map_add, Finsupp.single_add]

@[simp]
theorem splitTracePolynomialResidueBlocks_monomial
    (ex : Fin 2 →₀ ℕ) (c : K) :
    splitTracePolynomialResidueBlocks sigma hsigma e d heOdd hdOdd
        (MvPolynomial.monomial ex c) =
      Finsupp.single
        (splitTraceMonomialNormalIndex sigma hsigma e d heOdd hdOdd (ex 0) (ex 1))
        (MvPolynomial.monomial (finTwoExponent (ex 0 / d) (ex 1 / e)) c) := by
  rw [splitTracePolynomialResidueBlocks]
  apply MvPolynomial.sum_monomial_eq
  simp

/-- Reassemble residue blocks after power substitution. -/
def splitTraceRecomposeResidueBlocks
    (q : (Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) →₀
        MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  q.sum fun ji a ↦
    MvPolynomial.X 0 ^ (ji.2 : ℕ) * MvPolynomial.X 1 ^ (ji.1 : ℕ) *
      splitTracePowerSubstitution (K := K) e d a

theorem splitTracePowerSubstitution_monomial
    (i j : ℕ) (c : K) :
    splitTracePowerSubstitution (K := K) e d
        (MvPolynomial.monomial (finTwoExponent i j) c) =
      MvPolynomial.C c * MvPolynomial.X 0 ^ (d * i) *
        MvPolynomial.X 1 ^ (e * j) := by
  rw [monomial_finTwoExponent]
  simp only [map_mul, map_pow, splitTracePowerSubstitution_C,
    splitTracePowerSubstitution_X_zero, splitTracePowerSubstitution_X_one]
  rw [pow_mul, pow_mul]

theorem splitTraceRecomposeResidueBlocks_single_monomial
    (i j : ℕ) (c : K) :
    splitTraceRecomposeResidueBlocks sigma e d
        (Finsupp.single
          (splitTraceMonomialNormalIndex sigma hsigma e d heOdd hdOdd i j)
          (MvPolynomial.monomial (finTwoExponent (i / d) (j / e)) c)) =
      MvPolynomial.monomial (finTwoExponent i j) c := by
  rw [splitTraceRecomposeResidueBlocks, Finsupp.sum_single_index]
  · rw [splitTracePowerSubstitution_monomial]
    simp only [splitTraceMonomialNormalIndex_fst_val,
      splitTraceMonomialNormalIndex_snd_val]
    rw [monomial_finTwoExponent]
    have hi : i % d + d * (i / d) = i := Nat.mod_add_div i d
    have hj : j % e + e * (j / e) = j := Nat.mod_add_div j e
    calc
      MvPolynomial.X (0 : Fin 2) ^ (i % d) * MvPolynomial.X 1 ^ (j % e) *
          (MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ (d * (i / d)) *
            MvPolynomial.X (1 : Fin 2) ^ (e * (j / e))) =
          MvPolynomial.C c *
            (MvPolynomial.X (0 : Fin 2) ^ (i % d) *
              MvPolynomial.X (0 : Fin 2) ^ (d * (i / d))) *
            (MvPolynomial.X (1 : Fin 2) ^ (j % e) *
              MvPolynomial.X (1 : Fin 2) ^ (e * (j / e))) := by
              ring
      _ = MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ i *
          MvPolynomial.X (1 : Fin 2) ^ j := by
        rw [← pow_add, ← pow_add, hi, hj]
  · simp

theorem splitTraceRecomposeResidueBlocks_add
    (q r : (Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) →₀
        MvPolynomial (Fin 2) K) :
    splitTraceRecomposeResidueBlocks sigma e d (q + r) =
      splitTraceRecomposeResidueBlocks sigma e d q +
        splitTraceRecomposeResidueBlocks sigma e d r := by
  classical
  simp only [splitTraceRecomposeResidueBlocks]
  apply Finsupp.sum_add_index
  · intro ji
    simp
  · intro ji _ a b
    simp [map_add, mul_add]

/-- Exact reconstruction from the residue blocks. -/
theorem splitTraceRecomposeResidueBlocks_polynomial
    (p : MvPolynomial (Fin 2) K) :
    splitTraceRecomposeResidueBlocks sigma e d
        (splitTracePolynomialResidueBlocks sigma hsigma e d heOdd hdOdd p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial ex c =>
      rw [splitTracePolynomialResidueBlocks_monomial,
        splitTraceRecomposeResidueBlocks_single_monomial]
      rw [finTwoExponent_of_finsupp]
  | add p q hp hq =>
      rw [splitTracePolynomialResidueBlocks_add,
        splitTraceRecomposeResidueBlocks_add, hp, hq]

/-- Evaluate a residue-block polynomial on the degree-one base cover coordinates `(u*v,v)`. -/
def splitTraceBaseResidueEvaluation :
    MvPolynomial (Fin 2) K →ₐ[K] SplitTraceBaseFunctionField K sigma :=
  MvPolynomial.aeval
    ![splitTraceBaseU sigma * splitTraceBaseV sigma, splitTraceBaseV sigma]

theorem splitTraceBaseResidueEvaluation_monomial
    (a b : ℕ) (c : K) :
    splitTraceBaseResidueEvaluation sigma
        (MvPolynomial.monomial (finTwoExponent a b) c) =
      algebraMap K (SplitTraceBaseFunctionField K sigma) c *
        splitTraceBaseU sigma ^ a * splitTraceBaseV sigma ^ (a + b) := by
  rw [monomial_finTwoExponent]
  simp only [map_mul, map_pow]
  simp only [splitTraceBaseResidueEvaluation, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_pow, pow_add]
  ring

/-- Each syntactic Kummer coefficient is exactly the degree-one base-curve evaluation of the
corresponding residue-block polynomial. -/
theorem splitTraceBaseResidueEvaluation_residueBlock
    (p : MvPolynomial (Fin 2) K)
    (ji : Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) :
    splitTraceBaseResidueEvaluation sigma
        (splitTracePolynomialResidueBlocks sigma hsigma e d heOdd hdOdd p ji) =
      splitTracePolynomialSyntacticNormalForm
        sigma hsigma e d heOdd hdOdd p ji := by
  induction p using MvPolynomial.induction_on' with
  | monomial ex c =>
      rw [splitTracePolynomialResidueBlocks_monomial,
        splitTracePolynomialSyntacticNormalForm_monomial]
      by_cases hindex :
          splitTraceMonomialNormalIndex sigma hsigma e d heOdd hdOdd (ex 0) (ex 1) = ji
      · subst ji
        simp only [Finsupp.single_eq_same]
        rw [splitTraceBaseResidueEvaluation_monomial]
        simp only [splitTraceMonomialNormalCoefficient, mul_assoc]
      · simp [hindex]
  | add p q hp hq =>
      rw [splitTracePolynomialResidueBlocks_add,
        splitTracePolynomialSyntacticNormalForm_add]
      simp only [Finsupp.add_apply, map_add, hp, hq]

end ResidueBlocks

section DegreeOneKernel

variable (sigma : K) (hsigma : sigma ≠ 0)

private lemma splitTraceEtaRootInXiField_one_one :
    splitTraceEtaRootInXiField sigma 1 1 =
      splitTraceBaseElementInXiField sigma 1 1 (splitTraceBaseV sigma) := by
  simpa using (splitTraceEtaRootInXiField_pow (K := K) sigma 1 1)

private lemma splitTraceXiRoot_one_one :
    splitTraceXiRoot sigma 1 1 =
      splitTraceBaseElementInXiField sigma 1 1
        (splitTraceBaseU sigma * splitTraceBaseV sigma) := by
  have h := splitTraceXiRoot_pow (K := K) (sigma := sigma) (e := 1) (d := 1)
  simpa [splitTraceXiRadicand, splitTraceBaseElementInXiField] using h

/-- For the degree-one tower, evaluation at the two Kummer roots is just base-curve evaluation
at `(u*v,v)`, followed by the canonical inclusion of the base function field. -/
theorem splitTracePolynomialToKummerTop_one_one_eq_baseResidueEvaluation
    (q : MvPolynomial (Fin 2) K) :
    splitTracePolynomialToKummerTop sigma hsigma 1 1
        (by decide) (by decide) (by decide) q =
      IsScalarTower.toAlgHom K (SplitTraceBaseFunctionField K sigma)
        (SplitTraceXiFunctionField K sigma 1 1)
          (splitTraceBaseResidueEvaluation sigma q) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma 1 (by decide)
  letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma 1)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma 1 1
      (by decide) (by decide) (by decide)
  letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma 1 1)) := ⟨hXiIrred⟩
  let lhs : MvPolynomial (Fin 2) K →ₐ[K]
      SplitTraceXiFunctionField K sigma 1 1 :=
    splitTracePolynomialToKummerTop sigma hsigma 1 1
      (by decide) (by decide) (by decide)
  let rhs : MvPolynomial (Fin 2) K →ₐ[K]
      SplitTraceXiFunctionField K sigma 1 1 :=
    (IsScalarTower.toAlgHom K (SplitTraceBaseFunctionField K sigma)
      (SplitTraceXiFunctionField K sigma 1 1)).comp
        (splitTraceBaseResidueEvaluation sigma)
  have heq : lhs = rhs := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · dsimp [lhs, rhs, splitTracePolynomialToKummerTop,
        splitTraceBaseResidueEvaluation]
      simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero]
      change splitTraceXiRoot sigma 1 1 =
        algebraMap (SplitTraceBaseFunctionField K sigma)
          (SplitTraceXiFunctionField K sigma 1 1)
            (splitTraceBaseU sigma * splitTraceBaseV sigma)
      simpa [lhs, rhs, splitTracePolynomialToKummerTop,
        splitTraceBaseResidueEvaluation, splitTraceBaseElementInXiField,
        IsScalarTower.algebraMap_apply
          (SplitTraceBaseFunctionField K sigma)
          (SplitTraceEtaFunctionField K sigma 1)
          (SplitTraceXiFunctionField K sigma 1 1)] using
        (splitTraceXiRoot_one_one (K := K) sigma)
    · dsimp [lhs, rhs, splitTracePolynomialToKummerTop,
        splitTraceBaseResidueEvaluation]
      simp only [MvPolynomial.aeval_X, Matrix.cons_val_one]
      change splitTraceEtaRootInXiField sigma 1 1 =
        algebraMap (SplitTraceBaseFunctionField K sigma)
          (SplitTraceXiFunctionField K sigma 1 1) (splitTraceBaseV sigma)
      simpa [lhs, rhs, splitTracePolynomialToKummerTop,
        splitTraceBaseResidueEvaluation, splitTraceBaseElementInXiField,
        IsScalarTower.algebraMap_apply
          (SplitTraceBaseFunctionField K sigma)
          (SplitTraceEtaFunctionField K sigma 1)
          (SplitTraceXiFunctionField K sigma 1 1)] using
        (splitTraceEtaRootInXiField_one_one (K := K) sigma)
  exact DFunLike.congr_fun heq q

/-- The independently proved irreducibility of the degree-one trace curve gives the exact kernel
of base residue evaluation. -/
theorem splitTraceBaseResiduePolynomial_mem_baseCover
    (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (q : MvPolynomial (Fin 2) K)
    (hq : splitTraceBaseResidueEvaluation sigma q = 0) :
    q ∈ Ideal.span {splitTraceCoverPolynomial (1 : K) sigma 1 1} := by
  have hcover : Irreducible (splitTraceCoverPolynomial (1 : K) sigma 1 1) := by
    have hirred := weightedTraceTorusClosurePolynomial_irreducible
      (1 : K) sigma one_ne_zero hsigma (by simpa using hnondegenerate)
    simpa [weightedTraceTorusClosurePolynomial, hsigma] using hirred
  apply splitTracePolynomial_mem_span_of_cover_irreducible_and_maps_to_zero
    sigma hsigma 1 1 (by decide) (by decide) (by decide) hcover q
  rw [splitTracePolynomialToKummerTop_one_one_eq_baseResidueEvaluation]
  simp [hq]

end DegreeOneKernel

section SourceDivision

variable (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
  (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)

/-- Power substitution carries the degree-one base equation to the exact `(d,e)` cover
equation. -/
theorem splitTracePowerSubstitution_baseCover :
    splitTracePowerSubstitution (K := K) e d
        (splitTraceCoverPolynomial (1 : K) sigma 1 1) =
      splitTraceCoverPolynomial (1 : K) sigma d e := by
  simp only [splitTraceCoverPolynomial, map_add, map_sub, map_mul, map_pow,
    splitTracePowerSubstitution_C, splitTracePowerSubstitution_X_zero,
    splitTracePowerSubstitution_X_one]
  simp only [pow_one, ← pow_mul]
  rw [Nat.mul_comm e 2, Nat.mul_comm d 2]

/-- Every residue-block term whose coefficient vanishes on the degree-one base curve is already
in the principal ideal of the full power-cover equation. -/
theorem splitTraceResidueBlockTerm_mem_coverIdeal
    (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (ji : Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree)
    (q : MvPolynomial (Fin 2) K)
    (hq : splitTraceBaseResidueEvaluation sigma q = 0) :
    MvPolynomial.X 0 ^ (ji.2 : ℕ) * MvPolynomial.X 1 ^ (ji.1 : ℕ) *
        splitTracePowerSubstitution (K := K) e d q ∈
      Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e} := by
  rw [Ideal.mem_span_singleton]
  have hbase : splitTraceCoverPolynomial (1 : K) sigma 1 1 ∣ q := by
    rw [← Ideal.mem_span_singleton]
    exact splitTraceBaseResiduePolynomial_mem_baseCover
      sigma hsigma hnondegenerate q hq
  have hmapped := map_dvd (splitTracePowerSubstitution (K := K) e d) hbase
  rw [splitTracePowerSubstitution_baseCover] at hmapped
  exact dvd_mul_of_dvd_right hmapped
    (MvPolynomial.X 0 ^ (ji.2 : ℕ) * MvPolynomial.X 1 ^ (ji.1 : ℕ))

/-- The missing source-division theorem for the nondegenerate odd-coprime cover.  Its proof is
entirely bottom-up: residue decomposition, the independently proved degree-one kernel, and exact
power substitution. -/
theorem splitTracePolynomialSyntacticNormalForm_division_of_oddCoprime
    (hnondegenerate : sigma ≠ 1) (p : MvPolynomial (Fin 2) K)
    (hnormal : splitTracePolynomialSyntacticNormalForm
      sigma hsigma e d heOdd hdOdd p = 0) :
    p ∈ Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e} := by
  rw [← splitTraceRecomposeResidueBlocks_polynomial
    sigma hsigma e d heOdd hdOdd p]
  rw [splitTraceRecomposeResidueBlocks, Finsupp.sum]
  apply Ideal.sum_mem
  intro ji hji
  apply splitTraceResidueBlockTerm_mem_coverIdeal
    sigma e d hsigma hnondegenerate ji
  rw [splitTraceBaseResidueEvaluation_residueBlock]
  rw [hnormal]
  rfl

end SourceDivision

section Irreducibility

/-- The explicit Laurent comparison is injective in the nondegenerate
odd-coprime range; no irreducibility premise remains. -/
theorem splitTraceLaurentToKummerTop_injective_of_oddCoprime
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    Function.Injective
      (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde) := by
  apply (splitTracePolynomialSyntacticNormalForm_division_iff_laurentInjective
    sigma hsigma e d heOdd hdOdd hde hnondegenerate).1
  intro p hp
  exact splitTracePolynomialSyntacticNormalForm_division_of_oddCoprime
    sigma hsigma e d heOdd hdOdd hnondegenerate p hp

/-- The affine comparison is injective in the same range because the
coordinate-product localization has already been proved faithful. -/
theorem splitTraceAffineToKummerTop_injective_of_oddCoprime
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    Function.Injective
      (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde) :=
  splitTraceAffineToKummerTop_injective_of_laurentInjective
    sigma hsigma e d heOdd hdOdd hde
      (splitTraceLaurentToKummerTop_injective_of_oddCoprime
        sigma hsigma hnondegenerate e d heOdd hdOdd hde)

/-- The normalized split trace-cover polynomial is irreducible for nondegenerate odd coprime
exponents.  No characteristic restriction is needed. -/
theorem splitTraceCoverPolynomial_irreducible_of_oddCoprime
    (sigma : K) (hsigma : sigma ≠ 0) (hnondegenerate : sigma ≠ 1)
    (e d : ℕ) (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e) :
    Irreducible (splitTraceCoverPolynomial (1 : K) sigma d e) := by
  have hLaurent : Function.Injective
      (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde) :=
    splitTraceLaurentToKummerTop_injective_of_oddCoprime
      sigma hsigma hnondegenerate e d heOdd hdOdd hde
  exact splitTraceCoverPolynomial_irreducible_of_laurentInjective
    sigma hsigma e d heOdd hdOdd hde hLaurent

end Irreducibility

end


end BGS.Markoff
