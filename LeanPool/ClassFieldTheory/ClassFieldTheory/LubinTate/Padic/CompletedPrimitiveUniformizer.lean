/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerPrimitive
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
/-!
# The completed p-adic primitive point is a uniformizer

The primitive multiplicative Lubin--Tate polynomial remains Eisenstein over
the completed-unramified valuation ring.  This file uses that actual
Eisenstein equation and the fundamental ramification identity to prove that
the chosen completed primitive point has normalized additive valuation one.
Consequently it is a genuine uniformizer of the completed level.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial Topology

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

private noncomputable local instance
    padicCompletedPrimitiveUniformizerTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

private noncomputable local instance
    padicCompletedPrimitiveUniformizerTargetCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

private noncomputable local instance
    padicCompletedPrimitiveUniformizerTargetT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

private theorem completedPolynomial_eval₂_mem_ideal_of_coeff_mem
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (I : Ideal S) (P : Polynomial R) (z : S)
    (hcoeff : ∀ i, f (P.coeff i) ∈ I) :
    P.eval₂ f z ∈ I := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_right (z ^ i) I (hcoeff i)

private theorem eisenstein_sub_X_pow_coeff_mem
    {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R) (Q : Polynomial R)
    (d : ℕ) (hQnatDegree : Q.natDegree = d) (hQmonic : Q.Monic)
    (hQeisenstein : Q.IsEisensteinAt I) (i : ℕ) :
    (Q - Polynomial.X ^ d).coeff i ∈ I := by
  rcases lt_trichotomy i d with hi | hi | hi
  · have hQi : Q.coeff i ∈ I := by
      apply hQeisenstein.mem
      rwa [hQnatDegree]
    change (Q - Polynomial.X ^ d).coeff i ∈ I
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      ite_eq_right (ne_of_lt hi), sub_zero]
    exact hQi
  · subst i
    have hQd : Q.coeff d = 1 := by
      rw [← hQnatDegree]
      exact hQmonic.coeff_natDegree
    change (Q - Polynomial.X ^ d).coeff d ∈ I
    rw [Polynomial.coeff_sub, hQd, Polynomial.coeff_X_pow,
      ite_eq_left rfl, sub_self]
    exact I.zero_mem
  · have hQi : Q.coeff i = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rwa [hQnatDegree]
    change (Q - Polynomial.X ^ d).coeff i ∈ I
    rw [Polynomial.coeff_sub, hQi, Polynomial.coeff_X_pow,
      ite_eq_right (ne_of_gt hi), sub_zero]
    exact I.zero_mem

private theorem addVal_mul_degree_of_polynomial_tail
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (j : R →+* S) (P : Polynomial R) (x : S) (e d : ℕ)
    (hconst : IsDiscreteValuationRing.addVal S (j (P.coeff 0)) = (e : ℕ∞))
    (htail : x * P.divX.eval₂ j x ∈ IsLocalRing.maximalIdeal S ^ (e + 1))
    (hrootDecomp : x ^ d + P.eval₂ j x = 0) :
    (d : ℕ∞) * IsDiscreteValuationRing.addVal S x = (e : ℕ∞) := by
  let tail := P.divX.eval₂ j x
  have hR_eval :
      P.eval₂ j x = j (P.coeff 0) + x * tail := by
    have h :=
      congrArg (Polynomial.eval₂ j x)
        (Polynomial.X_mul_divX_add P)
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h
    calc
      P.eval₂ j x = x * tail + j (P.coeff 0) := by
        simpa only [tail] using h.symm
      _ = j (P.coeff 0) + x * tail := add_comm _ _
  have htailVal :
      ((e + 1 : ℕ) : ℕ∞) ≤
        IsDiscreteValuationRing.addVal S
          (x * tail) :=
    (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
      (x * tail) (e + 1)).1 htail
  have heCastLt :
      (e : ℕ∞) <
        IsDiscreteValuationRing.addVal S
          (x * tail) := by
    exact
      (show (e : ℕ∞) < ((e + 1 : ℕ) : ℕ∞) by
        exact_mod_cast Nat.lt_succ_self e).trans_le htailVal
  have hdistinct :
      IsDiscreteValuationRing.addVal S
          (j (P.coeff 0)) ≠
        IsDiscreteValuationRing.addVal S
          (x * tail) := by
    rw [hconst]
    exact ne_of_lt heCastLt
  have hRval :
      IsDiscreteValuationRing.addVal S
          (P.eval₂ j x) = (e : ℕ∞) := by
    rw [hR_eval,
      (IsDiscreteValuationRing.addVal
        S).map_add_of_distinct_val hdistinct,
      hconst, min_eq_left]
    exact heCastLt.le
  have hpowEq : x ^ d = -(P.eval₂ j x) :=
    eq_neg_of_add_eq_zero_left hrootDecomp
  have hmul :
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal S x =
        (e : ℕ∞) := by
    calc
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal S x =
          d • IsDiscreteValuationRing.addVal
            S x := by rw [nsmul_eq_mul]
      _ = IsDiscreteValuationRing.addVal S
          (x ^ d) := by
        symm
        exact IsDiscreteValuationRing.addVal_pow x d
      _ = IsDiscreteValuationRing.addVal S
          (-(P.eval₂ j x)) := by rw [hpowEq]
      _ = IsDiscreteValuationRing.addVal S
          (P.eval₂ j x) :=
        (IsDiscreteValuationRing.addVal S).map_neg _
      _ = (e : ℕ∞) := hRval
  exact hmul

private theorem
    padicCompletedPrimitiveRootInteger_addVal_and_ramificationIndex
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (padicCompletedLevelCompleteDVF p n).valuationSubring
        (padicCompletedPrimitiveRootInteger p n) = 1 ∧
      ramificationIndex
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF =
        degree
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF := by
  let A := padicCompletedUnramifiedField p
  let E := padicCompletedLevelField p n
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let Q := padicCompletedPrimitivePolynomialInteger p n
  let d := (p - 1) * p ^ n
  let e := ramificationIndex base.toDVF target.toDVF
  let f := residueDegree base.toDVF target.toDVF
  let 𝔭 := base.maximalIdeal
  let 𝔓 := target.maximalIdeal
  let j := integerMap base.toDVF target.toDVF
  let root := padicCompletedPrimitiveRootInteger p n
  let R := Q - Polynomial.X ^ d
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let πA : base.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p π
  let : IsScalarTower base.valuationSubring
      target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
      (Nat.pow_pos (Fact.out : p.Prime).pos)
  have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
  have hQnatDegree : Q.natDegree = d := by
    simpa only [Q, d] using
      padicCompletedPrimitivePolynomialInteger_natDegree p n
  have hQmonic : Q.Monic := by
    simpa only [Q] using
      padicCompletedPrimitivePolynomialInteger_monic p n
  have hQeisenstein : Q.IsEisensteinAt 𝔭 := by
    simpa only [Q, 𝔭, base] using
      padicCompletedPrimitivePolynomialInteger_isEisensteinAt p n
  have hdegree : degree base.toDVF target.toDVF = d := by
    change Module.finrank A E = d
    calc
      Module.finrank A E =
          (padicCompletedPrimitivePowerBasis p n).dim :=
        PowerBasis.finrank (padicCompletedPrimitivePowerBasis p n)
      _ =
          (minpoly A
            (padicCompletedPrimitivePowerBasis p n).gen).natDegree :=
        (padicCompletedPrimitivePowerBasis p n).natDegree_minpoly.symm
      _ =
          (padicCompletedPrimitivePolynomial p n).natDegree := by
        rw [padicCompletedPrimitivePowerBasis_gen,
          padicCompletedPrimitiveRoot_minpoly]
      _ = d := by
        simpa only [d] using
          padicCompletedPrimitivePolynomial_natDegree p n
  have hfund : d = e * f := by
    calc
      d = degree base.toDVF target.toDVF := hdegree.symm
      _ = e * f := by
        simpa only [e, f] using
          degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable
            base target
  have he_ne : e ≠ 0 := by
    intro he
    apply hdne
    rw [hfund, he, zero_mul]
  have hf_ne : f ≠ 0 := by
    intro hf
    apply hdne
    rw [hfund, hf, mul_zero]
  have hele : e ≤ d := by
    rw [hfund]
    exact Nat.le_mul_of_pos_right e (Nat.pos_of_ne_zero hf_ne)
  have hRcoeff (i : ℕ) : R.coeff i ∈ 𝔭 :=
    eisenstein_sub_X_pow_coeff_mem 𝔭 Q d hQnatDegree hQmonic hQeisenstein i
  have hR_eval_mem_map :
      R.eval₂ j root ∈ Ideal.map j 𝔭 :=
    completedPolynomial_eval₂_mem_ideal_of_coeff_mem
      j (Ideal.map j 𝔭) R root
      (fun i => Ideal.mem_map_of_mem j (hRcoeff i))
  have hmap :
      Ideal.map j 𝔭 = 𝔓 ^ e := by
    simpa only [j, 𝔭, 𝔓, e] using
      maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex
        base target
  have hR_eval_mem_pow : R.eval₂ j root ∈ 𝔓 ^ e := by
    rw [← hmap]
    exact hR_eval_mem_map
  have hroot : Q.eval₂ j root = 0 := by
    simpa only [Polynomial.aeval_def, Q, j, root, base, target,
      integerMap] using
      padicCompletedPrimitiveRootInteger_aeval p n
  have hQdecomp : Q = Polynomial.X ^ d + R := by
    calc
      Q = (Q - Polynomial.X ^ d) + Polynomial.X ^ d :=
        (sub_add_cancel Q (Polynomial.X ^ d)).symm
      _ = Polynomial.X ^ d + R := by rw [add_comm]
  have hrootDecomp : root ^ d + R.eval₂ j root = 0 := by
    rw [hQdecomp, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X] at hroot
    exact hroot
  have hrootMem : root ∈ 𝔓 := by
    simpa only [root, 𝔓, target] using
      padicCompletedPrimitiveRootInteger_mem_maximalIdeal p n
  have hdivCoeff (i : ℕ) : R.divX.coeff i ∈ 𝔭 := by
    rw [Polynomial.coeff_divX]
    exact hRcoeff (i + 1)
  let tail := R.divX.eval₂ j root
  have htail_mem_map : tail ∈ Ideal.map j 𝔭 :=
    completedPolynomial_eval₂_mem_ideal_of_coeff_mem
      j (Ideal.map j 𝔭) R.divX root
      (fun i => Ideal.mem_map_of_mem j (hdivCoeff i))
  have htail_mem_pow : tail ∈ 𝔓 ^ e := by
    rw [← hmap]
    exact htail_mem_map
  have hrootTailMem : root * tail ∈ 𝔓 ^ (e + 1) := by
    rw [pow_succ]
    have hmul : tail * root ∈ 𝔓 ^ e * 𝔓 :=
      Ideal.mul_mem_mul htail_mem_pow hrootMem
    rwa [mul_comm tail root] at hmul
  have hRcoeffZero : R.coeff 0 = πA := by
    change
      (padicCompletedPrimitivePolynomialInteger p n -
        Polynomial.X ^ d).coeff 0 = πA
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      ite_eq_right hdne.symm, sub_zero,
      padicCompletedPrimitivePolynomialInteger, Polynomial.coeff_map]
    exact congrArg (padicCompletedUnramifiedIntegerMap p)
      (standardLubinTatePrimitivePolynomial_coeff_zero (padicLocalField p) π n)
  have hπA :
      base.valuation.IsUniformizer
        (πA : padicCompletedUnramifiedField p) := by
    simpa only [base, π, πA] using
      padicCompletedUnramifiedIntegerMap_isUniformizer p
  have hπAIrreducible : Irreducible πA := by
    exact
      (IsDiscreteValuationRing.irreducible_iff_uniformizer πA).2
        (base.maximalIdeal_eq_span_uniformizer hπA)
  have hconst :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (j (R.coeff 0)) = (e : ℕ∞) := by
    rw [hRcoeffZero,
      addVal_integerMap_eq_ramificationIndex_nsmul base target πA,
      IsDiscreteValuationRing.addVal_uniformizer hπAIrreducible]
    simp only [e, nsmul_eq_mul, mul_one]
  have hmul := addVal_mul_degree_of_polynomial_tail j R root e d
    hconst hrootTailMem hrootDecomp
  have honele :
      1 ≤ IsDiscreteValuationRing.addVal
        target.valuationSubring root := by
    simpa using
      (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
        root 1).1
        (by simpa only [pow_one] using hrootMem)
  have hdcoe : (d : ℕ∞) ≠ 0 := by
    exact_mod_cast hdne
  have hmul_le :
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal target.valuationSubring root ≤
        (d : ℕ∞) * 1 := by
    rw [hmul]
    have hcast : (e : ℕ∞) ≤ (d : ℕ∞) := by
      exact_mod_cast hele
    simpa using hcast
  have hvle :
      IsDiscreteValuationRing.addVal target.valuationSubring root ≤ 1 :=
    (ENat.mul_le_mul_left_iff hdcoe (ENat.natCast_ne_top d)).1 hmul_le
  have hrootVal :
      IsDiscreteValuationRing.addVal target.valuationSubring root = 1 :=
    le_antisymm hvle honele
  have hed : e = d := by
    rw [hrootVal, mul_one] at hmul
    exact_mod_cast hmul.symm
  have heramDegree :
      ramificationIndex
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF =
        degree
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF := by
    simpa only [base, target, e] using hed.trans hdegree.symm
  exact ⟨hrootVal, heramDegree⟩

/-- The chosen completed primitive point has normalized additive valuation
one in the completed-level valuation ring. -/
theorem padicCompletedPrimitiveRootInteger_addVal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (padicCompletedLevelCompleteDVF p n).valuationSubring
        (padicCompletedPrimitiveRootInteger p n) = 1 :=
  (padicCompletedPrimitiveRootInteger_addVal_and_ramificationIndex
    p n).1

/-- The completed multiplicative Lubin--Tate level is totally ramified over
the completed-unramified coefficient field. -/
theorem padicCompletedLevel_ramificationIndex_eq_degree
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ramificationIndex
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF =
      degree
        (padicCompletedUnramifiedCompleteDVF p).toDVF
        (padicCompletedLevelCompleteDVF p n).toDVF :=
  (padicCompletedPrimitiveRootInteger_addVal_and_ramificationIndex
    p n).2

/-- The completed primitive point is irreducible in the completed-level
valuation ring. -/
  theorem padicCompletedPrimitiveRootInteger_irreducible
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Irreducible (padicCompletedPrimitiveRootInteger p n) := by
  let target := padicCompletedLevelCompleteDVF p n
  let root := padicCompletedPrimitiveRootInteger p n
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  have hval :
      IsDiscreteValuationRing.addVal target.valuationSubring root =
        IsDiscreteValuationRing.addVal target.valuationSubring ϖ := by
    rw [padicCompletedPrimitiveRootInteger_addVal,
      IsDiscreteValuationRing.addVal_uniformizer hϖ]
  exact
    ((IsDiscreteValuationRing.addVal_eq_iff_associated root ϖ).1
      hval).symm.irreducible hϖ

/-- The chosen completed primitive point is a genuine uniformizer of the
completed level. -/
theorem padicCompletedPrimitiveRoot_isUniformizer
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedLevelCompleteDVF p n).valuation.IsUniformizer
      (padicCompletedPrimitiveRootInteger p n :
        padicCompletedLevelField p n) := by
  exact Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (padicCompletedLevelCompleteDVF p n).valuation)
    (padicCompletedPrimitiveRootInteger_irreducible p n).maximalIdeal_eq

private theorem
    padicChangedUniformizerThetaValue_addVal_and_ramificationIndex
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (padicCompletedLevelCompleteDVF p n).valuationSubring
        (padicChangedUniformizerThetaValue p u n) = 1 ∧
      ramificationIndex
          (padicCompletedUnramifiedCompleteDVF p).toDVF
          (padicCompletedLevelCompleteDVF p n).toDVF =
        (p - 1) * p ^ n := by
  let base := padicCompletedUnramifiedCompleteDVF p
  let target := padicCompletedLevelCompleteDVF p n
  let Q := padicChangedCompletedPrimitivePolynomialInteger p u n
  let d := (p - 1) * p ^ n
  let e := ramificationIndex base.toDVF target.toDVF
  let 𝔭 := base.maximalIdeal
  let 𝔓 := target.maximalIdeal
  let j := integerMap base.toDVF target.toDVF
  let θ := padicChangedUniformizerThetaValue p u n
  let R := Q - Polynomial.X ^ d
  let π := padicIntEquivValuationSubring p (p : ℤ_[p])
  let πu :=
    standardLubinTateChangedUniformizer
      (padicLocalField p) π u
  let πuA : base.valuationSubring :=
    padicCompletedUnramifiedIntegerMap p πu
  let : IsScalarTower base.valuationSubring
      target.valuationSubring (padicCompletedLevelField p n) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
      (Nat.pow_pos (Fact.out : p.Prime).pos)
  have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
  have hQnatDegree : Q.natDegree = d := by
    simpa only [Q, d] using
      padicChangedCompletedPrimitivePolynomialInteger_natDegree p u n
  have hQmonic : Q.Monic := by
    simpa only [Q] using
      padicChangedCompletedPrimitivePolynomialInteger_monic p u n
  have hQeisenstein : Q.IsEisensteinAt 𝔭 := by
    simpa only [Q, 𝔭, base] using
      padicChangedCompletedPrimitivePolynomialInteger_isEisensteinAt
        p u n
  have hdegree :
      degree base.toDVF target.toDVF = d := by
    let pb := padicCompletedPrimitivePowerBasis p n
    change Module.finrank
      (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) = d
    calc
      Module.finrank
          (padicCompletedUnramifiedField p)
          (padicCompletedLevelField p n) =
          pb.dim :=
        PowerBasis.finrank pb
      _ =
          (minpoly (padicCompletedUnramifiedField p) pb.gen).natDegree :=
        pb.natDegree_minpoly.symm
      _ =
          (padicCompletedPrimitivePolynomial p n).natDegree := by
        rw [padicCompletedPrimitivePowerBasis_gen,
          padicCompletedPrimitiveRoot_minpoly]
      _ = d := by
        simpa only [d] using
          padicCompletedPrimitivePolynomial_natDegree p n
  have hed : e = d := by
    calc
      e =
          degree
            (padicCompletedUnramifiedCompleteDVF p).toDVF
            (padicCompletedLevelCompleteDVF p n).toDVF := by
        simpa only [e, base, target] using
          padicCompletedLevel_ramificationIndex_eq_degree p n
      _ = d := by simpa only [base, target] using hdegree
  have hRcoeff (i : ℕ) : R.coeff i ∈ 𝔭 :=
    eisenstein_sub_X_pow_coeff_mem 𝔭 Q d hQnatDegree hQmonic hQeisenstein i
  have hmap :
      Ideal.map j 𝔭 = 𝔓 ^ e := by
    simpa only [j, 𝔭, 𝔓, e] using
      maximalIdeal_map_eq_target_maximalIdeal_pow_ramificationIndex
        base target
  have hθmem : θ ∈ 𝔓 := by
    have hadic : IsAdic 𝔓 := rfl
    have h𝔓nhds :
        ((𝔓 : Ideal target.valuationSubring) :
          Set target.valuationSubring) ∈
            𝓝 (0 : target.valuationSubring) := by
      simpa only [pow_one] using
        (hadic.hasBasis_nhds_zero.mem_of_mem (i := 1) trivial)
    have hThetaEval :=
      padicChangedUniformizerThetaValue_hasEval p u n
    obtain ⟨m, hm⟩ :=
      hThetaEval.exists_pow_mem_of_mem_nhds h𝔓nhds
    exact
      (IsLocalRing.maximalIdeal.isMaximal
        target.valuationSubring).isPrime.mem_of_pow_mem m hm
  have hcomp :
      j.comp (padicCompletedUnramifiedIntegerMap p) =
        padicCompletedLevelPadicIntegerCoefficientHom p n := by
    ext z
    rw [RingHom.comp_apply, integerMap_apply,
      padicCompletedUnramifiedIntegerMap_coe,
      padicCompletedLevelPadicIntegerCoefficientHom_coe]
    rfl
  have hroot : Q.eval₂ j θ = 0 := by
    have h :=
      padicChangedUniformizerThetaValue_isRoot p u n
    rw [Polynomial.IsRoot, Polynomial.eval_map] at h
    change
      Polynomial.eval₂ j θ
          ((standardLubinTatePrimitivePolynomial
            (padicLocalField p) πu n).map
              (padicCompletedUnramifiedIntegerMap p)) =
        0
    rw [Polynomial.eval₂_map, hcomp]
    simpa only [πu] using h
  have hQdecomp : Q = Polynomial.X ^ d + R := by
    calc
      Q = (Q - Polynomial.X ^ d) + Polynomial.X ^ d :=
        (sub_add_cancel Q (Polynomial.X ^ d)).symm
      _ = Polynomial.X ^ d + R := by rw [add_comm]
  have hrootDecomp : θ ^ d + R.eval₂ j θ = 0 := by
    rw [hQdecomp, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X] at hroot
    exact hroot
  have hdivCoeff (i : ℕ) : R.divX.coeff i ∈ 𝔭 := by
    rw [Polynomial.coeff_divX]
    exact hRcoeff (i + 1)
  let tail := R.divX.eval₂ j θ
  have htail_mem_map : tail ∈ Ideal.map j 𝔭 :=
    completedPolynomial_eval₂_mem_ideal_of_coeff_mem
      j (Ideal.map j 𝔭) R.divX θ
      (fun i => Ideal.mem_map_of_mem j (hdivCoeff i))
  have htail_mem_pow : tail ∈ 𝔓 ^ e := by
    rw [← hmap]
    exact htail_mem_map
  have hθtail_mem : θ * tail ∈ 𝔓 ^ (e + 1) := by
    rw [pow_succ]
    have hmul : tail * θ ∈ 𝔓 ^ e * 𝔓 :=
      Ideal.mul_mem_mul htail_mem_pow hθmem
    rwa [mul_comm tail θ] at hmul
  have hRcoeffZero : R.coeff 0 = πuA := by
    change
      (padicChangedCompletedPrimitivePolynomialInteger p u n -
        Polynomial.X ^ d).coeff 0 = πuA
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      ite_eq_right hdne.symm, sub_zero,
      padicChangedCompletedPrimitivePolynomialInteger, Polynomial.coeff_map]
    exact congrArg (padicCompletedUnramifiedIntegerMap p)
      (standardLubinTatePrimitivePolynomial_coeff_zero
        (padicLocalField p) πu n)
  have hπuA :
      base.valuation.IsUniformizer
        (πuA : padicCompletedUnramifiedField p) := by
    simpa only [base, π, πu, πuA] using
      padicChangedCompletedUniformizer_isUniformizer p u
  have hπuAIrreducible : Irreducible πuA := by
    exact
      (IsDiscreteValuationRing.irreducible_iff_uniformizer πuA).2
        (base.maximalIdeal_eq_span_uniformizer hπuA)
  have hconst :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (j (R.coeff 0)) = (e : ℕ∞) := by
    rw [hRcoeffZero,
      addVal_integerMap_eq_ramificationIndex_nsmul base target πuA,
      IsDiscreteValuationRing.addVal_uniformizer hπuAIrreducible]
    simp only [e, nsmul_eq_mul, mul_one]
  have hmul := addVal_mul_degree_of_polynomial_tail j R θ e d
    hconst hθtail_mem hrootDecomp
  have honele :
      1 ≤ IsDiscreteValuationRing.addVal
        target.valuationSubring θ := by
    simpa using
      (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge
        θ 1).1
        (by simpa only [pow_one] using hθmem)
  have hdcoe : (d : ℕ∞) ≠ 0 := by
    exact_mod_cast hdne
  have hmul_le :
      (d : ℕ∞) *
          IsDiscreteValuationRing.addVal target.valuationSubring θ ≤
        (d : ℕ∞) * 1 := by
    rw [hmul, hed, mul_one]
  have hvle :
      IsDiscreteValuationRing.addVal target.valuationSubring θ ≤ 1 :=
    (ENat.mul_le_mul_left_iff hdcoe (ENat.natCast_ne_top d)).1 hmul_le
  have hθval :
      IsDiscreteValuationRing.addVal target.valuationSubring θ = 1 :=
    le_antisymm hvle honele
  exact ⟨hθval, hed⟩

/-- The genuine changed-uniformizer theta point has normalized additive
valuation one in the completed standard level. -/
theorem padicChangedUniformizerThetaValue_addVal
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    IsDiscreteValuationRing.addVal
        (padicCompletedLevelCompleteDVF p n).valuationSubring
        (padicChangedUniformizerThetaValue p u n) = 1 :=
  (padicChangedUniformizerThetaValue_addVal_and_ramificationIndex
    p u n).1

/-- The genuine changed-uniformizer theta point is a uniformizer of the
completed standard level. -/
theorem padicChangedUniformizerThetaValue_isUniformizer
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    (padicCompletedLevelCompleteDVF p n).valuation.IsUniformizer
      ((padicChangedUniformizerThetaValue p u n :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) := by
  let target := padicCompletedLevelCompleteDVF p n
  let θ := padicChangedUniformizerThetaValue p u n
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  have hval :
      IsDiscreteValuationRing.addVal target.valuationSubring θ =
        IsDiscreteValuationRing.addVal target.valuationSubring ϖ := by
    rw [padicChangedUniformizerThetaValue_addVal,
      IsDiscreteValuationRing.addVal_uniformizer hϖ]
  have hθirreducible : Irreducible θ :=
    ((IsDiscreteValuationRing.addVal_eq_iff_associated θ ϖ).1
      hval).symm.irreducible hϖ
  exact Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := target.valuation) hθirreducible.maximalIdeal_eq

end LubinTate

end
