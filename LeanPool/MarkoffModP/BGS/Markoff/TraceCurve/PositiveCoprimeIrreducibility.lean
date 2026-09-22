/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.OddCoprimeIrreducibility

/-!
# Irreducibility of positive coprime split trace covers

This module removes the oddness restriction from the split-cover proof.  A Capelli-style
binomial criterion constructs the Kummer tower for arbitrary positive coprime exponents over a
field containing a square root of `-1`.  A parity-free residue decomposition then reconnects the
tower to the actual affine cover polynomial and proves its principal ideal prime.

The coprimality restriction is still real in this proof: common prime divisors require a separate
Kummer-class independence argument and are not hidden here.
-/

namespace BGS.Markoff

open Polynomial AdjoinRoot IntermediateField

noncomputable section

variable {K : Type*} [Field K]

lemma exists_primePowerRootOfNegOne
    (i : K) (hi : i ^ 2 = -1) (q : ℕ) (hq : q.Prime) :
    ∃ c : K, c ^ q = -1 := by
  by_cases hqTwo : q = 2
  · exact ⟨i, by simpa [hqTwo] using hi⟩
  · refine ⟨-1, ?_⟩
    simpa using (hq.odd_of_ne_two hqTwo).neg_one_pow (α := K)

/-- Over a field in which `-1` is a square, the usual prime-radicand criterion for
`X^n-a` is valid also for even `n`. -/
theorem X_pow_sub_C_irreducible_of_sqrt_neg_one
    (i : K) (hi : i ^ 2 = -1) {n : ℕ} (hn : n ≠ 0) {a : K}
    (ha : ∀ q : ℕ, q.Prime → q ∣ n → ∀ b : K, b ^ q ≠ a) :
    Irreducible (X ^ n - C a) := by
  induction n using induction_on_primes generalizing K a with
  | zero => exact (hn rfl).elim
  | one => simpa using irreducible_X_sub_C a
  | prime_mul p n hp IH =>
    have hn' : n ≠ 0 := by
      intro hnZero
      apply hn
      simp [hnZero]
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (ha p hp (dvd_mul_right _ _)))
    intro E _ _ x hx
    have hxIntegral : IsIntegral K x := not_not.mp fun h => by
      simpa only [degree_zero, degree_X_pow_sub_C hp.pos,
        WithBot.natCast_ne_bot] using congr_arg degree (hx.symm.trans (dite_eq_right h))
    let iE : ↥(IntermediateField.adjoin K {x}) :=
      algebraMap K (↥(IntermediateField.adjoin K {x})) i
    have hiE : iE ^ 2 = -1 := by
      dsimp [iE]
      rw [← map_pow, hi, map_neg, map_one]
    apply IH iE hiE hn'
    intro q hq hqn b hb
    by_cases hpTwo : p = 2
    · have hnormNeg : (Algebra.norm K b) ^ q = -a := by
        rw [← map_pow, hb, ← adjoin.powerBasis_gen hxIntegral,
          Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
        simp [minpoly_gen, hx, hpTwo]
      obtain ⟨c, hc⟩ := exists_primePowerRootOfNegOne i hi q hq
      apply ha q hq (dvd_mul_of_dvd_right hqn p) (c * Algebra.norm K b)
      rw [mul_pow, hc, hnormNeg]
      simp
    · apply ha q hq (dvd_mul_of_dvd_right hqn p) (Algebra.norm K b)
      rw [← map_pow, hb, ← adjoin.powerBasis_gen hxIntegral,
        Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
      simp [minpoly_gen, hx, hp.ne_zero.symm, (hp.odd_of_ne_two hpTwo).neg_pow]

/-- The first trace-curve Kummer polynomial is irreducible for every positive exponent once
the constant field contains a square root of `-1`. -/
theorem splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    (sigma : K) (hsigma : sigma ≠ 0) (i : K) (hi : i ^ 2 = -1)
    (e : ℕ) (he : 0 < e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    Irreducible (splitTraceEtaKummerPolynomial sigma e) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  apply X_pow_sub_C_irreducible_of_sqrt_neg_one
    (algebraMap K (SplitTraceBaseFunctionField K sigma) i)
  · rw [← map_pow, hi, map_neg, map_one]
  · exact he.ne'
  · intro q hq _ z
    exact splitTraceBaseRoot_not_primePower sigma hsigma q hq z

lemma splitTraceEtaFunctionField_finrank_of_sqrt_neg_one
    (sigma : K) (hsigma : sigma ≠ 0) (i : K) (hi : i ^ 2 = -1)
    (e : ℕ) (he : 0 < e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma hsigma i hi e he⟩
    Module.finrank (SplitTraceBaseFunctionField K sigma)
      (SplitTraceEtaFunctionField K sigma e) = e := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma hsigma i hi e he
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hEtaIrred.ne_zero)]
  change (splitTraceEtaKummerPolynomial sigma e).natDegree = e
  simp [splitTraceEtaKummerPolynomial]

/-- The norm-degree obstruction for the second radicand does not depend on parity.  It applies
to every prime not dividing the first exponent. -/
theorem splitTraceXiRadicand_not_primePower_of_sqrt_neg_one
    (sigma : K) (hsigma : sigma ≠ 0) (i : K) (hi : i ^ 2 = -1)
    (e : ℕ) (he : 0 < e) (q : ℕ) (hq : q.Prime) (hqe : ¬ q ∣ e)
    (z : letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
          ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
        letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
          ⟨splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
            sigma hsigma i hi e he⟩
        SplitTraceEtaFunctionField K sigma e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma hsigma i hi e he⟩
    z ^ q ≠ splitTraceXiRadicand sigma e := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma hsigma i hi e he
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let : Module.Finite (RatFunc K) (SplitTraceBaseFunctionField K sigma) :=
    (monic_X_pow_sub_C _ (by norm_num : (2 : ℕ) ≠ 0)).finite_adjoinRoot
  let : Module.Finite (SplitTraceBaseFunctionField K sigma)
      (SplitTraceEtaFunctionField K sigma e) :=
    (monic_X_pow_sub_C _ he.ne').finite_adjoinRoot
  have hBaseV : splitTraceBaseV sigma ≠ 0 := by
    change AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma) ≠ 0
    exact (root_X_pow_sub_C_ne_zero_iff hBaseIrred).mpr
      (splitTraceRadicand_ne_zero sigma hsigma)
  have hBaseU : splitTraceBaseU sigma ≠ 0 := by
    exact (map_ne_zero_iff _
      (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma)).injective).mpr
        RatFunc.X_ne_zero
  have hBaseUV : splitTraceBaseU sigma * splitTraceBaseV sigma ≠ 0 :=
    mul_ne_zero hBaseU hBaseV
  have hXiRadicand : splitTraceXiRadicand sigma e ≠ 0 := by
    exact (map_ne_zero_iff _
      (algebraMap (SplitTraceBaseFunctionField K sigma)
        (SplitTraceEtaFunctionField K sigma e)).injective).mpr hBaseUV
  intro hpow
  have hz : z ≠ 0 := by
    intro hz
    apply hXiRadicand
    simpa [hz, hq.ne_zero] using hpow.symm
  have hFirstNorm := congrArg
    (Algebra.norm (SplitTraceBaseFunctionField K sigma)) hpow
  rw [map_pow, splitTraceXiRadicand, Algebra.norm_algebraMap,
    splitTraceEtaFunctionField_finrank_of_sqrt_neg_one sigma hsigma i hi e he] at hFirstNorm
  have hSecondNorm := congrArg (Algebra.norm (RatFunc K)) hFirstNorm
  rw [map_pow, map_pow] at hSecondNorm
  have hNormZNe :
      Algebra.norm (SplitTraceBaseFunctionField K sigma) z ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hz
  have hDoubleNormZNe :
      Algebra.norm (RatFunc K)
        (Algebra.norm (SplitTraceBaseFunctionField K sigma) z) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hNormZNe
  have hNormBaseUVNe :
      Algebra.norm (RatFunc K) (splitTraceBaseU sigma * splitTraceBaseV sigma) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hBaseUV
  have hDegree := congrArg RatFunc.intDegree hSecondNorm
  rw [RatFunc.intDegree_pow _ hDoubleNormZNe,
    RatFunc.intDegree_pow _ hNormBaseUVNe,
    norm_splitTraceBaseU_mul_V_intDegree sigma hsigma] at hDegree
  apply hqe
  rw [← Int.natCast_dvd_natCast]
  exact ⟨_, by simpa using hDegree.symm⟩

/-- For arbitrary positive coprime exponents, including even exponents, the second Kummer
polynomial is irreducible once the constant field contains a square root of `-1`. -/
theorem splitTraceXiKummerPolynomial_irreducible_of_sqrt_neg_one_coprime
    (sigma : K) (hsigma : sigma ≠ 0) (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (hd : 0 < d) (hde : d.Coprime e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma hsigma i hi e he⟩
    Irreducible (splitTraceXiKummerPolynomial sigma e d) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma hsigma i hi e he
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  rw [splitTraceXiKummerPolynomial]
  apply X_pow_sub_C_irreducible_of_sqrt_neg_one
    (algebraMap K (SplitTraceEtaFunctionField K sigma e) i)
  · rw [← map_pow, hi, map_neg, map_one]
  · exact hd.ne'
  · intro q hq hqd z
    exact splitTraceXiRadicand_not_primePower_of_sqrt_neg_one
      sigma hsigma i hi e he q hq
        (hq.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hqd hde)) z

section PositiveCoprimeCover

variable (sigma : K) (hsigma : sigma ≠ 0) (i : K) (hi : i ^ 2 = -1)
  (e d : ℕ) (he : 0 < e) (hd : 0 < d) (hde : d.Coprime e)

private theorem generalSplitTraceEtaKummerPolynomial_natDegree
    (sigma : K) (hsigma : sigma ≠ 0) (e : ℕ) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    (splitTraceEtaKummerPolynomial sigma e).natDegree = e := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  change (X ^ e - C (splitTraceBaseV sigma)).natDegree = e
  exact natDegree_X_pow_sub_C

private theorem generalSplitTraceXiKummerPolynomial_natDegree
    (sigma : K) (hsigma : sigma ≠ 0) (i : K) (hi : i ^ 2 = -1)
    (e : ℕ) (he : 0 < e) (d : ℕ) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma hsigma i hi e he⟩
    (splitTraceXiKummerPolynomial sigma e d).natDegree = d := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma hsigma i hi e he
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  change (X ^ d - C (splitTraceXiRadicand sigma e)).natDegree = d
  exact natDegree_X_pow_sub_C

/-- Rectangular residue index for arbitrary positive coprime exponents. -/
def generalSplitTraceMonomialNormalIndex
    (sigma : K) (hsigma : sigma ≠ 0) (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (hd : 0 < d) (a b : ℕ) :
    Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree := by
  exact (⟨b % e, by
      rw [generalSplitTraceEtaKummerPolynomial_natDegree sigma hsigma e]
      exact Nat.mod_lt _ he⟩,
    ⟨a % d, by
      rw [generalSplitTraceXiKummerPolynomial_natDegree sigma hsigma i hi e he d]
      exact Nat.mod_lt _ hd⟩)

@[simp] theorem generalSplitTraceMonomialNormalIndex_fst_val (a b : ℕ) :
    (generalSplitTraceMonomialNormalIndex sigma hsigma i hi e d he hd a b).1.val = b % e := rfl

@[simp] theorem generalSplitTraceMonomialNormalIndex_snd_val (a b : ℕ) :
    (generalSplitTraceMonomialNormalIndex sigma hsigma i hi e d he hd a b).2.val = a % d := rfl

/-- Syntactic rectangular coefficients without parity assumptions. -/
def generalSplitTracePolynomialSyntacticNormalForm
    (sigma : K) (hsigma : sigma ≠ 0) (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (hd : 0 < d)
    (p : MvPolynomial (Fin 2) K) :
    (Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) →₀
        SplitTraceBaseFunctionField K sigma :=
  (AddMonoidAlgebra.coeff p).sum fun ex c ↦
    Finsupp.single
      (generalSplitTraceMonomialNormalIndex sigma hsigma i hi e d he hd (ex 0) (ex 1))
      (algebraMap K (SplitTraceBaseFunctionField K sigma) c *
        splitTraceMonomialNormalCoefficient sigma e d (ex 0) (ex 1))

@[simp] theorem generalSplitTracePolynomialSyntacticNormalForm_zero :
    generalSplitTracePolynomialSyntacticNormalForm
      sigma hsigma i hi e d he hd 0 = 0 := by
  simp [generalSplitTracePolynomialSyntacticNormalForm]

theorem generalSplitTracePolynomialSyntacticNormalForm_add
    (p q : MvPolynomial (Fin 2) K) :
    generalSplitTracePolynomialSyntacticNormalForm sigma hsigma i hi e d he hd (p + q) =
      generalSplitTracePolynomialSyntacticNormalForm sigma hsigma i hi e d he hd p +
        generalSplitTracePolynomialSyntacticNormalForm sigma hsigma i hi e d he hd q := by
  classical
  simp only [generalSplitTracePolynomialSyntacticNormalForm]
  apply Finsupp.sum_add_index
  · intro ex
    simp
  · intro ex _ a b
    simp only [map_add, add_mul, Finsupp.single_add]

@[simp] theorem generalSplitTracePolynomialSyntacticNormalForm_monomial
    (ex : Fin 2 →₀ ℕ) (c : K) :
    generalSplitTracePolynomialSyntacticNormalForm sigma hsigma i hi e d he hd
        (MvPolynomial.monomial ex c) =
      Finsupp.single
        (generalSplitTraceMonomialNormalIndex sigma hsigma i hi e d he hd (ex 0) (ex 1))
        (algebraMap K (SplitTraceBaseFunctionField K sigma) c *
          splitTraceMonomialNormalCoefficient sigma e d (ex 0) (ex 1)) := by
  rw [generalSplitTracePolynomialSyntacticNormalForm]
  apply MvPolynomial.sum_monomial_eq
  simp

/-- Evaluation at the two roots in the general positive-coprime Kummer tower. -/
def generalSplitTracePolynomialToKummerTop :
    MvPolynomial (Fin 2) K →ₐ[K] SplitTraceXiFunctionField K sigma e d :=
  MvPolynomial.aeval
    ![splitTraceXiRoot sigma e d, splitTraceEtaRootInXiField sigma e d]

@[simp] theorem generalSplitTracePolynomialToKummerTop_monomial
    (ex : Fin 2 →₀ ℕ) (c : K) :
    generalSplitTracePolynomialToKummerTop sigma e d (MvPolynomial.monomial ex c) =
      algebraMap K (SplitTraceXiFunctionField K sigma e d) c *
        (splitTraceXiRoot sigma e d ^ (ex 0) *
          splitTraceEtaRootInXiField sigma e d ^ (ex 1)) := by
  simp [generalSplitTracePolynomialToKummerTop, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_monomial, Fin.prod_univ_two]

theorem generalSplitTracePolynomialSyntacticNormalForm_evaluation
    (p : MvPolynomial (Fin 2) K) :
    splitTraceExplicitNormalFormEvaluation sigma e d
        (generalSplitTracePolynomialSyntacticNormalForm
          sigma hsigma i hi e d he hd p) =
      generalSplitTracePolynomialToKummerTop sigma e d p := by
  induction p using MvPolynomial.induction_on' with
  | monomial ex c =>
      rw [generalSplitTracePolynomialSyntacticNormalForm_monomial,
        splitTraceExplicitNormalFormEvaluation]
      let : CommRing (SplitTraceBaseFunctionField K sigma) := AdjoinRoot.instCommRing _
      let : CommRing (SplitTraceEtaFunctionField K sigma e) := AdjoinRoot.instCommRing _
      let : CommRing (SplitTraceXiFunctionField K sigma e d) := AdjoinRoot.instCommRing _
      rw [Finsupp.linearCombination_single]
      simp only [Algebra.smul_def, generalSplitTraceMonomialNormalIndex_fst_val,
        generalSplitTraceMonomialNormalIndex_snd_val, map_mul]
      have hred := (splitTraceKummer_monomial_reduction
        (K := K) sigma e d (ex 0) (ex 1)).symm
      rw [generalSplitTracePolynomialToKummerTop_monomial]
      calc
        (algebraMap (SplitTraceBaseFunctionField K sigma)
              (SplitTraceXiFunctionField K sigma e d))
              ((algebraMap K (SplitTraceBaseFunctionField K sigma)) c) *
            (algebraMap (SplitTraceBaseFunctionField K sigma)
              (SplitTraceXiFunctionField K sigma e d))
              (splitTraceMonomialNormalCoefficient sigma e d (ex 0) (ex 1)) *
            (splitTraceEtaRootInXiField sigma e d ^ (ex 1 % e) *
              splitTraceXiRoot sigma e d ^ (ex 0 % d)) =
            algebraMap K (SplitTraceXiFunctionField K sigma e d) c *
              (splitTraceBaseElementInXiField sigma e d
                (splitTraceMonomialNormalCoefficient sigma e d (ex 0) (ex 1)) *
                (splitTraceEtaRootInXiField sigma e d ^ (ex 1 % e) *
                  splitTraceXiRoot sigma e d ^ (ex 0 % d))) := by
                    simp only [splitTraceBaseElementInXiField]
                    simp_rw [IsScalarTower.algebraMap_apply K
                      (SplitTraceBaseFunctionField K sigma)
                      (SplitTraceXiFunctionField K sigma e d)]
                    simp_rw [IsScalarTower.algebraMap_apply
                      (SplitTraceBaseFunctionField K sigma)
                      (SplitTraceEtaFunctionField K sigma e)
                      (SplitTraceXiFunctionField K sigma e d)]
                    ring
        _ = algebraMap K (SplitTraceXiFunctionField K sigma e d) c *
              (splitTraceXiRoot sigma e d ^ ex 0 *
                splitTraceEtaRootInXiField sigma e d ^ ex 1) := by rw [hred]
  | add p q hp hq =>
      rw [generalSplitTracePolynomialSyntacticNormalForm_add]
      change Finsupp.linearCombination (SplitTraceBaseFunctionField K sigma)
          (fun ji ↦ splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
            splitTraceXiRoot sigma e d ^ (ji.2 : ℕ))
          (generalSplitTracePolynomialSyntacticNormalForm sigma hsigma i hi e d he hd p +
            generalSplitTracePolynomialSyntacticNormalForm sigma hsigma i hi e d he hd q) = _
      change Finsupp.linearCombination (SplitTraceBaseFunctionField K sigma)
          (fun ji ↦ splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
            splitTraceXiRoot sigma e d ^ (ji.2 : ℕ))
          (generalSplitTracePolynomialSyntacticNormalForm
            sigma hsigma i hi e d he hd p) = _ at hp
      change Finsupp.linearCombination (SplitTraceBaseFunctionField K sigma)
          (fun ji ↦ splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
            splitTraceXiRoot sigma e d ^ (ji.2 : ℕ))
          (generalSplitTracePolynomialSyntacticNormalForm
            sigma hsigma i hi e d he hd q) = _ at hq
      rw [map_add, hp, hq, map_add]

theorem generalSplitTracePolynomialSyntacticNormalForm_eq_zero_iff
    (p : MvPolynomial (Fin 2) K) :
    generalSplitTracePolynomialSyntacticNormalForm sigma hsigma i hi e d he hd p = 0 ↔
      generalSplitTracePolynomialToKummerTop sigma e d p = 0 := by
  rw [← generalSplitTracePolynomialSyntacticNormalForm_evaluation
    sigma hsigma i hi e d he hd p]
  let : CommRing (SplitTraceBaseFunctionField K sigma) := AdjoinRoot.instCommRing _
  let : CommRing (SplitTraceEtaFunctionField K sigma e) := AdjoinRoot.instCommRing _
  let : CommRing (SplitTraceXiFunctionField K sigma e d) := AdjoinRoot.instCommRing _
  change generalSplitTracePolynomialSyntacticNormalForm
      sigma hsigma i hi e d he hd p = 0 ↔
    Finsupp.linearCombination (SplitTraceBaseFunctionField K sigma)
      (fun ji ↦ splitTraceEtaRootInXiField sigma e d ^ (ji.1 : ℕ) *
        splitTraceXiRoot sigma e d ^ (ji.2 : ℕ))
      (generalSplitTracePolynomialSyntacticNormalForm
        sigma hsigma i hi e d he hd p) = 0
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    apply splitTraceEtaXiNormalMonomials_linearIndependent sigma e d he.ne' hd.ne'
    simpa using h

/-- Residue-block coefficient polynomials for arbitrary positive exponents. -/
def generalSplitTracePolynomialResidueBlocks
    (p : MvPolynomial (Fin 2) K) :
    (Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) →₀
        MvPolynomial (Fin 2) K :=
  (AddMonoidAlgebra.coeff p).sum fun ex c ↦
    Finsupp.single
      (generalSplitTraceMonomialNormalIndex sigma hsigma i hi e d he hd (ex 0) (ex 1))
      (MvPolynomial.monomial (finTwoExponent (ex 0 / d) (ex 1 / e)) c)

@[simp] theorem generalSplitTracePolynomialResidueBlocks_zero :
    generalSplitTracePolynomialResidueBlocks
      sigma hsigma i hi e d he hd 0 = 0 := by
  simp [generalSplitTracePolynomialResidueBlocks]

theorem generalSplitTracePolynomialResidueBlocks_add
    (p q : MvPolynomial (Fin 2) K) :
    generalSplitTracePolynomialResidueBlocks sigma hsigma i hi e d he hd (p + q) =
      generalSplitTracePolynomialResidueBlocks sigma hsigma i hi e d he hd p +
        generalSplitTracePolynomialResidueBlocks sigma hsigma i hi e d he hd q := by
  classical
  simp only [generalSplitTracePolynomialResidueBlocks]
  apply Finsupp.sum_add_index
  · intro ex
    simp
  · intro ex _ a b
    simp only [map_add, Finsupp.single_add]

@[simp] theorem generalSplitTracePolynomialResidueBlocks_monomial
    (ex : Fin 2 →₀ ℕ) (c : K) :
    generalSplitTracePolynomialResidueBlocks sigma hsigma i hi e d he hd
        (MvPolynomial.monomial ex c) =
      Finsupp.single
        (generalSplitTraceMonomialNormalIndex sigma hsigma i hi e d he hd (ex 0) (ex 1))
        (MvPolynomial.monomial (finTwoExponent (ex 0 / d) (ex 1 / e)) c) := by
  rw [generalSplitTracePolynomialResidueBlocks]
  apply MvPolynomial.sum_monomial_eq
  simp

theorem splitTraceRecomposeGeneralResidueBlocks_single_monomial
    (a b : ℕ) (c : K) :
    splitTraceRecomposeResidueBlocks sigma e d
        (Finsupp.single
          (generalSplitTraceMonomialNormalIndex sigma hsigma i hi e d he hd a b)
          (MvPolynomial.monomial (finTwoExponent (a / d) (b / e)) c)) =
      MvPolynomial.monomial (finTwoExponent a b) c := by
  rw [splitTraceRecomposeResidueBlocks, Finsupp.sum_single_index]
  · rw [splitTracePowerSubstitution_monomial]
    simp only [generalSplitTraceMonomialNormalIndex_fst_val,
      generalSplitTraceMonomialNormalIndex_snd_val]
    rw [monomial_finTwoExponent]
    have ha : a % d + d * (a / d) = a := Nat.mod_add_div a d
    have hb : b % e + e * (b / e) = b := Nat.mod_add_div b e
    calc
      MvPolynomial.X (0 : Fin 2) ^ (a % d) * MvPolynomial.X 1 ^ (b % e) *
          (MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ (d * (a / d)) *
            MvPolynomial.X (1 : Fin 2) ^ (e * (b / e))) =
          MvPolynomial.C c *
            (MvPolynomial.X (0 : Fin 2) ^ (a % d) *
              MvPolynomial.X (0 : Fin 2) ^ (d * (a / d))) *
            (MvPolynomial.X (1 : Fin 2) ^ (b % e) *
              MvPolynomial.X (1 : Fin 2) ^ (e * (b / e))) := by ring
      _ = MvPolynomial.C c * MvPolynomial.X (0 : Fin 2) ^ a *
          MvPolynomial.X (1 : Fin 2) ^ b := by
        rw [← pow_add, ← pow_add, ha, hb]
  · simp

/-- Exact reconstruction from the general residue blocks. -/
theorem splitTraceRecomposeGeneralResidueBlocks_polynomial
    (p : MvPolynomial (Fin 2) K) :
    splitTraceRecomposeResidueBlocks sigma e d
        (generalSplitTracePolynomialResidueBlocks
          sigma hsigma i hi e d he hd p) = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial ex c =>
      rw [generalSplitTracePolynomialResidueBlocks_monomial,
        splitTraceRecomposeGeneralResidueBlocks_single_monomial]
      rw [finTwoExponent_of_finsupp]
  | add p q hp hq =>
      rw [generalSplitTracePolynomialResidueBlocks_add,
        splitTraceRecomposeResidueBlocks_add, hp, hq]

/-- Each general syntactic coefficient is the base-curve evaluation of its residue block. -/
theorem splitTraceBaseResidueEvaluation_generalResidueBlock
    (p : MvPolynomial (Fin 2) K)
    (ji : Fin (splitTraceEtaKummerPolynomial sigma e).natDegree ×
      Fin (splitTraceXiKummerPolynomial sigma e d).natDegree) :
    splitTraceBaseResidueEvaluation sigma
        (generalSplitTracePolynomialResidueBlocks
          sigma hsigma i hi e d he hd p ji) =
      generalSplitTracePolynomialSyntacticNormalForm
        sigma hsigma i hi e d he hd p ji := by
  induction p using MvPolynomial.induction_on' with
  | monomial ex c =>
      rw [generalSplitTracePolynomialResidueBlocks_monomial,
        generalSplitTracePolynomialSyntacticNormalForm_monomial]
      by_cases hindex :
          generalSplitTraceMonomialNormalIndex sigma hsigma i hi e d he hd
            (ex 0) (ex 1) = ji
      · subst ji
        simp only [Finsupp.single_eq_same]
        rw [splitTraceBaseResidueEvaluation_monomial]
        simp only [splitTraceMonomialNormalCoefficient, mul_assoc]
      · simp [hindex]
  | add p q hp hq =>
      rw [generalSplitTracePolynomialResidueBlocks_add,
        generalSplitTracePolynomialSyntacticNormalForm_add]
      simp only [Finsupp.add_apply, map_add, hp, hq]

/-- Source division for every positive coprime cover once the even Kummer criterion applies. -/
theorem generalSplitTracePolynomialSyntacticNormalForm_division
    (hnondegenerate : sigma ≠ 1) (p : MvPolynomial (Fin 2) K)
    (hnormal : generalSplitTracePolynomialSyntacticNormalForm
      sigma hsigma i hi e d he hd p = 0) :
    p ∈ Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e} := by
  rw [← splitTraceRecomposeGeneralResidueBlocks_polynomial
    sigma hsigma i hi e d he hd p]
  rw [splitTraceRecomposeResidueBlocks, Finsupp.sum]
  apply Ideal.sum_mem
  intro ji hji
  apply splitTraceResidueBlockTerm_mem_coverIdeal
    sigma e d hsigma hnondegenerate ji
  rw [splitTraceBaseResidueEvaluation_generalResidueBlock]
  rw [hnormal]
  rfl

/-- The roots of the positive-coprime tower satisfy the cleared affine cover equation. -/
theorem generalSplitTraceKummerTower_cover_maps_to_zero :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
        sigma hsigma i hi e he⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible_of_sqrt_neg_one_coprime
        sigma hsigma i hi e d he hd hde⟩
    generalSplitTracePolynomialToKummerTop sigma e d
      (splitTraceCoverPolynomial (1 : K) sigma d e) = 0 := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma hsigma i hi e he
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred := splitTraceXiKummerPolynomial_irreducible_of_sqrt_neg_one_coprime
    sigma hsigma i hi e d he hd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  let baseToXi : SplitTraceBaseFunctionField K sigma →+*
      SplitTraceXiFunctionField K sigma e d :=
    (algebraMap (SplitTraceEtaFunctionField K sigma e)
      (SplitTraceXiFunctionField K sigma e d)).comp
      (algebraMap (SplitTraceBaseFunctionField K sigma)
        (SplitTraceEtaFunctionField K sigma e))
  have hBase := splitTraceBaseU_V_equation sigma hsigma
  have hBaseTop := congrArg baseToXi hBase
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero] at hBaseTop
  have hEtaRoot :
      (AdjoinRoot.root (splitTraceEtaKummerPolynomial sigma e)) ^ e =
        algebraMap (SplitTraceBaseFunctionField K sigma)
          (SplitTraceEtaFunctionField K sigma e) (splitTraceBaseV sigma) := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root (splitTraceEtaKummerPolynomial sigma e)
    rw [splitTraceEtaKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  have hEtaTop := congrArg
    (algebraMap (SplitTraceEtaFunctionField K sigma e)
      (SplitTraceXiFunctionField K sigma e d)) hEtaRoot
  simp only [map_pow] at hEtaTop
  have hXiRoot :
      splitTraceXiRoot sigma e d ^ d =
        algebraMap (SplitTraceEtaFunctionField K sigma e)
          (SplitTraceXiFunctionField K sigma e d) (splitTraceXiRadicand sigma e) := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root (splitTraceXiKummerPolynomial sigma e d)
    rw [splitTraceXiKummerPolynomial] at h
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h
    rw [← AdjoinRoot.algebraMap_eq] at h
    exact h
  have hCover := eval_splitTraceCoverPolynomial_of_powerRootRelations
    (splitTraceBaseElementInXiField sigma e d
      (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma) (RatFunc.C sigma)))
    (splitTraceBaseElementInXiField sigma e d (splitTraceBaseU sigma))
    (splitTraceBaseElementInXiField sigma e d (splitTraceBaseV sigma))
    (splitTraceXiRoot sigma e d) (splitTraceEtaRootInXiField sigma e d) d e
    (by simpa [baseToXi, splitTraceBaseElementInXiField] using hBaseTop)
    (by simpa [splitTraceEtaRootInXiField, splitTraceBaseElementInXiField, baseToXi]
      using hEtaTop)
    (by simpa [splitTraceXiRadicand, splitTraceBaseElementInXiField, baseToXi,
      splitTraceXiRoot] using hXiRoot)
  have hsigmaTop :
      splitTraceBaseElementInXiField sigma e d
          (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma) (RatFunc.C sigma)) =
        algebraMap K (SplitTraceXiFunctionField K sigma e d) sigma := by
    change algebraMap (SplitTraceEtaFunctionField K sigma e)
        (SplitTraceXiFunctionField K sigma e d)
          (algebraMap (SplitTraceBaseFunctionField K sigma)
            (SplitTraceEtaFunctionField K sigma e)
              (algebraMap (RatFunc K) (SplitTraceBaseFunctionField K sigma)
                (algebraMap K (RatFunc K) sigma))) = _
    rw [← IsScalarTower.algebraMap_apply K (RatFunc K)
      (SplitTraceBaseFunctionField K sigma)]
    rw [← IsScalarTower.algebraMap_apply K
      (SplitTraceBaseFunctionField K sigma) (SplitTraceEtaFunctionField K sigma e)]
    rw [← IsScalarTower.algebraMap_apply K
      (SplitTraceEtaFunctionField K sigma e) (SplitTraceXiFunctionField K sigma e d)]
  rw [hsigmaTop] at hCover
  simpa [generalSplitTracePolynomialToKummerTop, MvPolynomial.aeval_def,
    splitTraceCoverPolynomial] using hCover

private lemma generalSplitTraceCoverPolynomial_ne_zero
    (sigma : K) (d : ℕ) (hd : 0 < d) :
    splitTraceCoverPolynomial (1 : K) sigma d e ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval ![(0 : K), (1 : K)]) hzero
  rw [eval_splitTraceCoverPolynomial] at heval
  norm_num [hd.ne'] at heval

/-- The normalized split trace-cover polynomial is irreducible for all positive coprime
exponents, including even exponents, over a field containing a square root of `-1`. -/
theorem splitTraceCoverPolynomial_irreducible_of_sqrt_neg_one_coprime
    (sigma : K) (hsigma : sigma ≠ 0) (i : K) (hi : i ^ 2 = -1)
    (e d : ℕ) (he : 0 < e) (hd : 0 < d) (hde : d.Coprime e)
    (hnondegenerate : sigma ≠ 1) :
    Irreducible (splitTraceCoverPolynomial (1 : K) sigma d e) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible_of_sqrt_neg_one
    sigma hsigma i hi e he
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred := splitTraceXiKummerPolynomial_irreducible_of_sqrt_neg_one_coprime
    sigma hsigma i hi e d he hd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  let : IsDomain (SplitTraceXiFunctionField K sigma e d) :=
    AdjoinRoot.isDomain_of_prime hXiIrred.prime
  let f : MvPolynomial (Fin 2) K →+* SplitTraceXiFunctionField K sigma e d :=
    (generalSplitTracePolynomialToKummerTop sigma e d).toRingHom
  let I : Ideal (MvPolynomial (Fin 2) K) :=
    Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e}
  have hCoverZero :
      generalSplitTracePolynomialToKummerTop sigma e d
        (splitTraceCoverPolynomial (1 : K) sigma d e) = 0 :=
    generalSplitTraceKummerTower_cover_maps_to_zero
      sigma hsigma i hi e d he hd hde
  have hI_le : I ≤ RingHom.ker f := by
    change Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e} ≤ RingHom.ker f
    rw [Ideal.span_le]
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst p
    exact hCoverZero
  have hker_le : RingHom.ker f ≤ I := by
    intro p hp
    apply generalSplitTracePolynomialSyntacticNormalForm_division
      sigma hsigma i hi e d he hd hnondegenerate p
    apply (generalSplitTracePolynomialSyntacticNormalForm_eq_zero_iff
      sigma hsigma i hi e d he hd p).2
    exact hp
  let quotientToTop : MvPolynomial (Fin 2) K ⧸ I →+*
      SplitTraceXiFunctionField K sigma e d :=
    Ideal.Quotient.lift I f hI_le
  have hInjective : Function.Injective quotientToTop :=
    RingHom.lift_injective_of_ker_le_ideal I hI_le hker_le
  let : IsDomain (MvPolynomial (Fin 2) K ⧸ I) :=
    hInjective.isDomain quotientToTop
  have hprimeIdeal : I.IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  have hprimeElement : Prime (splitTraceCoverPolynomial (1 : K) sigma d e) :=
    (Ideal.span_singleton_prime
      (generalSplitTraceCoverPolynomial_ne_zero e sigma d hd)).1 (by
        simpa [I] using hprimeIdeal)
  exact irreducible_iff_prime.mpr hprimeElement

end PositiveCoprimeCover

end

end BGS.Markoff
