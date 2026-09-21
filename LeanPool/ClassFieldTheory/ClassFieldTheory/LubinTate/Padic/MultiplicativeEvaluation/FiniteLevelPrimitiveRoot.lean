/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.FiniteLevelEvaluation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.LocalRingEquiv
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
/-!
# Primitive roots from finite p-adic Lubin--Tate levels

The evaluated multiplicative point yields an actual primitive
`p ^ (n + 1)`-st root of unity.  This module proves its exact order and
identifies the genuine finite-level Galois action with the cyclotomic power
action.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

variable {K : Type u} [Field K]

attribute [local instance]
  padicMultiplicativeLevelCoefficientUniformSpace
  padicMultiplicativeLevelTargetWithIdeal
  padicMultiplicativeLevelTargetTopologicalSpace
  padicMultiplicativeLevelTargetCompleteSpace
  padicMultiplicativeLevelTargetT2Space

private theorem padicMultiplicativeScalarEndomorphism_nat
    (p : ℕ) [Fact p.Prime] (m : ℕ) :
    recursiveIntertwiner
        (padicMultiplicativeLubinTateSeries_isUniformizer p)
        (padicMultiplicativeLubinTateSeries p)
        (padicMultiplicativeLubinTateSeries p)
        (fun _ : Unit =>
          (m : (padicLocalField p).valuationSubring)) =
      (1 + PowerSeries.X) ^ m - 1 := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let A :
      PowerSeries (padicLocalField p).valuationSubring :=
    (1 + PowerSeries.X) ^ m - 1
  let Eps :
      PowerSeries (padicLocalField p).valuationSubring :=
    (padicMultiplicativeLubinTateSeries p).toPowerSeries
  have hEps :
      Eps =
        PowerSeries.binomialSeries
            (padicLocalField p).valuationSubring (p : ℤ) -
          1 :=
    rfl
  have hAconstant : PowerSeries.constantCoeff A = 0 := by
    simp [A]
  have hAcoeffOne :
      PowerSeries.coeff 1 A =
        (m : (padicLocalField p).valuationSubring) := by
    dsimp only [A]
    simp only [map_sub, PowerSeries.coeff_one]
    rw [PowerSeries.coeff_one_pow]
    simp
  have hAlinear :
      HasLinearTerm A
        (fun _ : Unit =>
          (m : (padicLocalField p).valuationSubring)) := by
    rw [HasLinearTerm]
    apply MvPowerSeries.nat_le_order
    intro d hd
    have hdNat : d.degree < 2 := by
      exact_mod_cast hd
    have hdegree : d.degree = d () := by
      simp [Finsupp.degree_eq_sum]
    have hd' : d () < 2 := by omega
    by_cases hd0 : d () = 0
    · have hdeq : d = 0 := by
        apply Finsupp.ext
        intro i
        cases i
        simp [hd0]
      subst d
      change
        PowerSeries.constantCoeff A -
            MvPowerSeries.constantCoeff
              (linearForm
                (fun _ : Unit =>
                  (m : (padicLocalField p).valuationSubring))) =
          0
      rw [hAconstant, constantCoeff_linearForm, sub_self]
    · have hd1 : d () = 1 := by omega
      have hdeq : d = Finsupp.single () 1 := by
        apply Finsupp.ext
        intro i
        cases i
        simp [hd1]
      subst d
      have hlinearForm :
          linearForm
              (fun _ : Unit =>
                (m : (padicLocalField p).valuationSubring)) =
            MvPowerSeries.C
                (m : (padicLocalField p).valuationSubring) *
              MvPowerSeries.X () := by
        simp [linearForm]
      change
        PowerSeries.coeff 1 A -
            MvPowerSeries.coeff (Finsupp.single () 1)
              (linearForm
                (fun _ : Unit =>
                  (m : (padicLocalField p).valuationSubring))) =
          0
      classical
      rw [hAcoeffOne, hlinearForm, MvPowerSeries.coeff_C_mul,
        MvPowerSeries.coeff_index_single_self_X, mul_one, sub_self]
  have hAsubst : PowerSeries.HasSubst A :=
    hAlinear.hasSubst
  have hEsubst :
      PowerSeries.HasSubst Eps := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero
    exact (padicMultiplicativeLubinTateSeries p).constantCoeff_eq_zero
  have hAsubstOne :
      PowerSeries.subst A
          (1 : PowerSeries (padicLocalField p).valuationSubring) =
        1 := by
    change
      PowerSeries.subst A
          (PowerSeries.C
            (1 : (padicLocalField p).valuationSubring)) =
        1
    rw [PowerSeries.subst_C]
    rfl
  have hEsubstOne :
      PowerSeries.subst Eps
          (1 : PowerSeries (padicLocalField p).valuationSubring) =
        1 := by
    change
      PowerSeries.subst Eps
          (PowerSeries.C
            (1 : (padicLocalField p).valuationSubring)) =
        1
    rw [PowerSeries.subst_C]
    rfl
  have hAone :
      1 + A = (1 + PowerSeries.X) ^ m := by
    dsimp only [A]
    ring
  have hEone :
      1 + Eps =
        (1 + PowerSeries.X) ^ p := by
    rw [hEps, PowerSeries.binomialSeries_nat (R := ℤ)]
    ring
  have hcommutes :
      PowerSeries.subst A Eps =
        PowerSeries.subst Eps A := by
    calc
      PowerSeries.subst A Eps =
          (1 + A) ^ p - 1 := by
        rw [hEps, PowerSeries.binomialSeries_nat (R := ℤ),
          PowerSeries.subst_sub hAsubst,
          PowerSeries.subst_pow hAsubst,
          PowerSeries.subst_add hAsubst,
          PowerSeries.subst_X hAsubst, hAsubstOne]
      _ = ((1 + PowerSeries.X) ^ m) ^ p - 1 := by
        rw [hAone]
      _ = (1 + PowerSeries.X) ^ (m * p) - 1 := by
        rw [← pow_mul]
      _ = (1 + PowerSeries.X) ^ (p * m) - 1 := by
        rw [mul_comm m p]
      _ = ((1 + PowerSeries.X) ^ p) ^ m - 1 := by
        rw [pow_mul]
      _ =
          (1 + Eps) ^ m - 1 := by
        rw [hEone]
      _ =
          PowerSeries.subst Eps
            ((1 +
              (PowerSeries.X :
                PowerSeries (padicLocalField p).valuationSubring)) ^ m -
              1) := by
        symm
        rw [PowerSeries.subst_sub hEsubst,
          PowerSeries.subst_pow hEsubst,
          PowerSeries.subst_add hEsubst,
          PowerSeries.subst_X hEsubst, hEsubstOne]
      _ =
          PowerSeries.subst Eps A :=
        rfl
  have hAintertwines :
      Intertwines
        (padicMultiplicativeLubinTateSeries p)
        (padicMultiplicativeLubinTateSeries p) A := by
    change
      PowerSeries.subst A Eps =
        MvPowerSeries.subst
          (fun i : Unit =>
            inVariable (padicMultiplicativeLubinTateSeries p) i) A
    calc
      PowerSeries.subst A Eps =
          PowerSeries.subst Eps A :=
        hcommutes
      _ =
          MvPowerSeries.subst
            (fun i : Unit =>
              inVariable (padicMultiplicativeLubinTateSeries p) i) A := by
        symm
        rw [PowerSeries.subst_def]
        congr 1
        funext i
        cases i
        change
          PowerSeries.subst PowerSeries.X Eps = Eps
        exact PowerSeries.X_subst Eps
  exact
    eq_of_hasLinearTerm_of_intertwines hπ
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit =>
        (m : (padicLocalField p).valuationSubring))
      (recursiveIntertwiner_hasLinearTerm hπ
        (padicMultiplicativeLubinTateSeries p)
        (padicMultiplicativeLubinTateSeries p)
        (fun _ : Unit =>
          (m : (padicLocalField p).valuationSubring)))
      (recursiveIntertwiner_intertwines hπ
        (padicMultiplicativeLubinTateSeries p)
        (padicMultiplicativeLubinTateSeries p)
        (fun _ : Unit =>
          (m : (padicLocalField p).valuationSubring)))
      hAlinear hAintertwines

private theorem
    padicValuationSubring_sub_toZModPow_val_mem_maximalIdeal_pow
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : (padicLocalField p).valuationSubring) :
    let z :=
      (padicIntEquivValuationSubring p).symm
        a
    let m := (PadicInt.toZModPow (p := p) (n + 1) z).val
    a - (m : (padicLocalField p).valuationSubring) ∈
      (padicLocalField p).toCompleteDVF.maximalIdeal ^ (n + 1) := by
  change (padicDVRValuation p).valuationSubring at a
  let e := padicIntEquivValuationSubring p
  let z : ℤ_[p] :=
    e.symm a
  let m := (PadicInt.toZModPow (p := p) (n + 1) z).val
  have hz :
      z - (m : ℤ_[p]) ∈
        Ideal.span ({(p : ℤ_[p]) ^ (n + 1)} : Set ℤ_[p]) := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    rw [map_sub, map_natCast]
    dsimp only [m]
    rw [ZMod.natCast_zmod_val, sub_self]
  have hzmax :
      z - (m : ℤ_[p]) ∈
        IsLocalRing.maximalIdeal ℤ_[p] ^ (n + 1) := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    exact hz
  have hmapped :
      e (z - (m : ℤ_[p])) ∈
        IsLocalRing.maximalIdeal
            (padicDVRValuation p).valuationSubring ^ (n + 1) :=
    (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff
      e (n + 1) (z - (m : ℤ_[p]))).2 hzmax
  change
    a - (m : (padicDVRValuation p).valuationSubring) ∈
      IsLocalRing.maximalIdeal
          (padicDVRValuation p).valuationSubring ^ (n + 1)
  simpa only [map_sub, map_natCast, e, z, m,
    RingEquiv.apply_symm_apply] using hmapped

private theorem
    padicStandardPrimitivePointIntegerAction_eq_toZModPow_val
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let m :=
      (PadicInt.toZModPow (p := p) (n + 1)
        ((padicIntEquivValuationSubring p).symm
          (u : (padicLocalField p).valuationSubring))).val
    standardLubinTatePrimitivePointIntegerAction
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n u =
      standardLubinTateEndomorphismValue
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (m : (padicLocalField p).valuationSubring) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let m :=
    (PadicInt.toZModPow (p := p) (n + 1)
      ((padicIntEquivValuationSubring p).symm
        (u : (padicLocalField p).valuationSubring))).val
  let d : (padicLocalField p).valuationSubring :=
    (u : (padicLocalField p).valuationSubring) - m
  have hd :
      d ∈ (padicLocalField p).toCompleteDVF.maximalIdeal ^ (n + 1) := by
    simpa only [d, m] using
      padicValuationSubring_sub_toZModPow_val_mem_maximalIdeal_pow p n
        (u : (padicLocalField p).valuationSubring)
  have hdzero :
      standardLubinTateEndomorphismValue hπ n d = 0 :=
    (standardLubinTateEndomorphismValue_eq_zero_iff_mem_maximalIdeal_pow
      hπ n d).2 hd
  change
    standardLubinTateEndomorphismValue hπ n
        (u : (padicLocalField p).valuationSubring) =
      standardLubinTateEndomorphismValue hπ n
        (m : (padicLocalField p).valuationSubring)
  calc
    standardLubinTateEndomorphismValue hπ n
        (u : (padicLocalField p).valuationSubring) =
        standardLubinTateEndomorphismValue hπ n
          ((m : (padicLocalField p).valuationSubring) + d) := by
      congr 1
      dsimp only [d]
      ring
    _ =
        standardLubinTateFormalAdd hπ n
          (standardLubinTateEndomorphismValue hπ n
            (m : (padicLocalField p).valuationSubring))
          (standardLubinTateEndomorphismValue hπ n d) :=
      standardLubinTateEndomorphismValue_add hπ n m d
    _ =
        standardLubinTateFormalAdd hπ n
          (standardLubinTateEndomorphismValue hπ n
            (m : (padicLocalField p).valuationSubring))
          (standardLubinTateEndomorphismValue hπ n 0) := by
      exact congrArg
        (standardLubinTateFormalAdd hπ n
          (standardLubinTateEndomorphismValue hπ n
            (m : (padicLocalField p).valuationSubring)))
        (hdzero.trans (standardLubinTateEndomorphismValue_zero hπ n).symm)
    _ =
        standardLubinTateEndomorphismValue hπ n
          ((m : (padicLocalField p).valuationSubring) + 0) :=
      (standardLubinTateEndomorphismValue_add hπ n m 0).symm
    _ =
        standardLubinTateEndomorphismValue hπ n
          (m : (padicLocalField p).valuationSubring) := by
      rw [add_zero]

private theorem padicStandardLubinTateSeries_eval_iterate
    (p : ℕ) [Fact p.Prime] (n i : ℕ) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTatePrimitivePointIterateInteger
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n i)
        (standardLubinTatePrimitivePointIterateInteger_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n i)
        (standardLubinTateSeries
          (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries =
      standardLubinTatePrimitivePointIterateInteger
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n (i + 1) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let x := standardLubinTatePrimitivePointIterateInteger hπ n i
  have hpoly :
      Polynomial.eval₂ (standardLubinTateLevelCoefficientHom hπ n) x
          (standardLubinTatePolynomial (padicLocalField p) π) =
        x ^ Nat.card (padicLocalField p).residueField +
          standardLubinTateLevelCoefficientHom hπ n π * x := by
    simp only [standardLubinTatePolynomial, Polynomial.eval₂_add,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_C]
  rw [← standardLubinTatePolynomial_toPowerSeries_eq_series hπ]
  exact (standardLubinTateLevelPowerSeriesEval_coe hπ n x
    (standardLubinTatePrimitivePointIterateInteger_hasEval hπ n i)
    (standardLubinTatePolynomial (padicLocalField p) π)).trans
      (hpoly.trans (standardLubinTatePrimitivePointIterateInteger_succ hπ n i).symm)

private theorem
    padicStandardLubinTatePrimitivePointIterateInteger_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    standardLubinTatePrimitivePointIterateInteger
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n n ≠
      0 := by
  intro hzero
  have hval :=
    standardLubinTatePrimitivePointIterateInteger_addVal
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n n le_rfl
  rw [hzero, IsDiscreteValuationRing.addVal_zero] at hval
  exact ENat.top_ne_natCast _ hval

private theorem padicMultiplicativePrimitivePoint_pow_primePower
    (p : ℕ) [Fact p.Prime] (n i : ℕ) :
    (1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ i) =
      1 +
        standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTatePrimitivePointIterateInteger
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n i)
          (standardLubinTatePrimitivePointIterateInteger_hasEval
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n i)
          (padicStandardToMultiplicativeIntertwiner p) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let points :
      ℕ →
        {z :
            (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
          PowerSeries.HasEval z} :=
    fun j =>
      ⟨standardLubinTatePrimitivePointIterateInteger hπ n j,
        standardLubinTatePrimitivePointIterateInteger_hasEval hπ n j⟩
  let evalH :
      {z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
        PowerSeries.HasEval z} →
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
    fun z =>
      standardLubinTateLevelPowerSeriesEval hπ n z.1 z.2 H
  change
    (1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ i) =
      1 + evalH (points i)
  induction i with
  | zero =>
      have hpacked : points 0 =
          ⟨standardLubinTatePrimitivePointInteger hπ n,
            standardLubinTatePrimitivePointInteger_hasEval hπ n⟩ :=
        Subtype.ext (standardLubinTatePrimitivePointIterateInteger_zero hπ n)
      have heval : evalH (points 0) =
          evalH ⟨standardLubinTatePrimitivePointInteger hπ n,
            standardLubinTatePrimitivePointInteger_hasEval hπ n⟩ :=
        congrArg evalH hpacked
      have hbase :
          evalH ⟨standardLubinTatePrimitivePointInteger hπ n,
            standardLubinTatePrimitivePointInteger_hasEval hπ n⟩ =
            padicMultiplicativePrimitivePoint p n := by
        simp only [evalH, H, padicMultiplicativePrimitivePoint,
          standardLubinTatePrimitivePointEvaluation]
      simpa only [pow_zero, pow_one] using
        congrArg (fun z : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =>
          1 + z) (heval.trans hbase).symm
  | succ i ih =>
      let Ebar := (standardLubinTateSeries hπ).toPowerSeries
      let mappedPoint :
          {z :
              (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
            PowerSeries.HasEval z} :=
        ⟨standardLubinTateLevelPowerSeriesEval hπ n
            (points i).1 (points i).2 Ebar,
          standardLubinTateLevelPowerSeriesEval_hasEval hπ n
            (points i).1 (points i).2 Ebar
            (PowerSeries.HasSubst.of_constantCoeff_zero
              (LubinTateSeries.constantCoeff_eq_zero
                (standardLubinTateSeries hπ)))⟩
      have hfunctional :=
        padicStandardToMultiplicativeIntertwiner_eval_functionalEquation
          p n (points i).1 (points i).2
      rw [padicMultiplicativeLubinTateSeries_eval] at hfunctional
      change
        (1 + evalH (points i)) ^ p - 1 =
          evalH mappedPoint at hfunctional
      have hiterate : mappedPoint.1 = (points (i + 1)).1 :=
        padicStandardLubinTateSeries_eval_iterate p n i
      have hpacked : mappedPoint = points (i + 1) :=
        Subtype.ext hiterate
      have hfunctionalClean :
          (1 + evalH (points i)) ^ p - 1 =
            evalH (points (i + 1)) :=
        hfunctional.trans (congrArg evalH hpacked)
      have hstep :
          (1 + evalH (points i)) ^ p =
            1 + evalH (points (i + 1)) := by
        calc
          _ = evalH (points (i + 1)) + 1 :=
            sub_eq_iff_eq_add.mp hfunctionalClean
          _ = _ := add_comm _ _
      calc
        (1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ (i + 1)) =
            ((1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ i)) ^ p := by
              rw [pow_succ, pow_mul]
        _ = (1 + evalH (points i)) ^ p := by rw [ih]
        _ = 1 + evalH (points (i + 1)) := hstep

/-- The root of unity obtained from the standard primitive Lubin--Tate
point through the multiplicative comparison.  Level `n` corresponds to
exact order `p ^ (n + 1)`. -/
noncomputable def padicMultiplicativePrimitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n :=
  1 + (padicMultiplicativePrimitivePoint p n :
    standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)

/-- The finite Lubin--Tate unit action becomes the usual power action on
the actual primitive `p ^ (n + 1)`-st root.  The exponent is the canonical
mathlib reduction of the corresponding `p`-adic integer modulo
`p ^ (n + 1)`. This is the finite-level cyclotomic action formula. -/
private theorem padicMultiplicativePrimitiveRoot_unitAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    1 +
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTatePrimitivePointIntegerAction
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n u)
          (standardLubinTatePrimitivePointIntegerAction_hasEval
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n u)
          (padicStandardToMultiplicativeIntertwiner p) :
          standardLubinTateLevelField
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n) =
      padicMultiplicativePrimitiveRoot p n ^
        (PadicInt.toZModPow (p := p) (n + 1)
          ((padicIntEquivValuationSubring p).symm
            (u : (padicLocalField p).valuationSubring))).val := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let m :=
    (PadicInt.toZModPow (p := p) (n + 1)
      ((padicIntEquivValuationSubring p).symm
        (u : (padicLocalField p).valuationSubring))).val
  let lambda :=
    standardLubinTatePrimitivePointInteger hπ n
  let hlambda :=
    standardLubinTatePrimitivePointInteger_hasEval hπ n
  let lambdaU :=
    standardLubinTatePrimitivePointIntegerAction hπ n u
  let hlambdaU :=
    standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u
  let zetaMinusOne := padicMultiplicativePrimitivePoint p n
  let hzetaMinusOne :=
    padicMultiplicativePrimitivePoint_hasEval p n
  have hlambdaUeq :
      lambdaU =
        standardLubinTateEndomorphismValue hπ n
          (m : (padicLocalField p).valuationSubring) := by
    simpa only [lambdaU, hπ, m] using
      padicStandardPrimitivePointIntegerAction_eq_toZModPow_val p n u
  have hscalar :
      standardLubinTateLevelPowerSeriesEval hπ n
          (standardLubinTateEndomorphismValue hπ n
            (m : (padicLocalField p).valuationSubring))
          (standardLubinTateEndomorphismValue_hasEval hπ n
            (m : (padicLocalField p).valuationSubring))
          H =
        standardLubinTateLevelPowerSeriesEval hπ n
          zetaMinusOne hzetaMinusOne
          (recursiveIntertwiner hπ
            (padicMultiplicativeLubinTateSeries p)
            (padicMultiplicativeLubinTateSeries p)
            (fun _ : Unit =>
              (m : (padicLocalField p).valuationSubring))) := by
    simpa [standardLubinTateEndomorphismValue,
      padicMultiplicativePrimitivePoint,
      standardLubinTatePrimitivePointEvaluation,
      hπ, H, lambda, hlambda, zetaMinusOne, hzetaMinusOne] using
      padicStandardToMultiplicativeIntertwiner_eval_endomorphism
        p n lambda hlambda
        (m : (padicLocalField p).valuationSubring)
  have heval :
      standardLubinTateLevelPowerSeriesEval hπ n
          lambdaU hlambdaU H =
        (1 + zetaMinusOne) ^ m - 1 := by
    have eval_eq_of_point_eq
        {x y :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring}
        (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
        (hxy : x = y) :
        standardLubinTateLevelPowerSeriesEval hπ n x hx H =
          standardLubinTateLevelPowerSeriesEval hπ n y hy H := by
      subst y
      rfl
    calc
      standardLubinTateLevelPowerSeriesEval hπ n
          lambdaU hlambdaU H =
          standardLubinTateLevelPowerSeriesEval hπ n
            (standardLubinTateEndomorphismValue hπ n
              (m : (padicLocalField p).valuationSubring))
            (standardLubinTateEndomorphismValue_hasEval hπ n
              (m : (padicLocalField p).valuationSubring))
            H := by
        exact eval_eq_of_point_eq hlambdaU _ hlambdaUeq
      _ =
          standardLubinTateLevelPowerSeriesEval hπ n
            zetaMinusOne hzetaMinusOne
            (recursiveIntertwiner hπ
              (padicMultiplicativeLubinTateSeries p)
              (padicMultiplicativeLubinTateSeries p)
              (fun _ : Unit =>
                (m : (padicLocalField p).valuationSubring))) :=
        hscalar
      _ =
          standardLubinTateLevelPowerSeriesEval hπ n
            zetaMinusOne hzetaMinusOne
            ((1 + PowerSeries.X) ^ m - 1) := by
        rw [padicMultiplicativeScalarEndomorphism_nat]
      _ = (1 + zetaMinusOne) ^ m - 1 := by
        simp only [map_sub, map_pow, map_add, map_one]
        exact congrArg
          (fun z : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =>
            (1 + z) ^ m - 1)
          (standardLubinTateLevelPowerSeriesEval_X
            hπ n zetaMinusOne hzetaMinusOne)
  have hrootInteger :
      1 +
          standardLubinTateLevelPowerSeriesEval hπ n
            lambdaU hlambdaU H =
        (1 + zetaMinusOne) ^ m := by
    rw [heval]
    ring
  have hrootField :=
    congrArg
      (fun x :
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =>
          (x : standardLubinTateLevelField hπ n))
      hrootInteger
  simpa [padicMultiplicativePrimitiveRoot, hπ, H, m,
    lambdaU, hlambdaU, zetaMinusOne] using hrootField

private theorem padicMultiplicativeLevelAlgEquiv_mem_valuationSubring_iff
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (σ : Gal((standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)/ℚ_[p]))
    (x : standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    x ∈ (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuation.valuationSubring ↔
      σ x ∈ (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuation.valuationSubring := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let target := standardLubinTateLevelCompleteDVF hπ n
  let L := standardLubinTateLevelField hπ n
  let : Algebra (padicLocalField p).valuationSubring target.valuationSubring :=
    (standardLubinTateLevelCoefficientHom hπ n).toAlgebra
  let : WithIdeal target.valuationSubring :=
    padicMultiplicativeLevelTargetWithIdeal
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  let : IsScalarTower
      (padicLocalField p).valuationSubring target.valuationSubring L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsIntegralClosure
      target.valuationSubring
      (padicLocalField p).valuationSubring L :=
    standardLubinTateLevelCompleteDVF_isIntegralClosure hπ n
  have hforward
      (τ : Gal(L / ℚ_[p])) {y : L}
      (hy : y ∈ target.valuation.valuationSubring) :
      τ y ∈ target.valuation.valuationSubring := by
    have hyIntegral :
        IsIntegral (padicLocalField p).valuationSubring y :=
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := (padicLocalField p).valuationSubring)
        (B := L)).2
          ⟨⟨y, hy⟩, rfl⟩
    have hτIntegral :
        IsIntegral (padicLocalField p).valuationSubring (τ y) :=
      IsIntegral.map τ.toAlgHom hyIntegral
    rcases
        (IsIntegralClosure.isIntegral_iff
          (A := target.valuationSubring)
          (R := (padicLocalField p).valuationSubring)
          (B := L)).1 hτIntegral
      with ⟨z, hz⟩
    exact hz ▸ z.property
  constructor
  · exact hforward σ
  · intro hσx
    have hback := hforward σ.symm hσx
    simpa using hback

private noncomputable def
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (σ : Gal((standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)/ℚ_[p])) :
    (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring ≃+*
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring :=
  higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves
    (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)
    σ.toRingEquiv
    (padicMultiplicativeLevelAlgEquiv_mem_valuationSubring_iff p n σ)

@[simp]
private theorem
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (σ : Gal((standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)/ℚ_[p]))
    (x : (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring) :
    ((padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ x :
        (standardLubinTateLevelCompleteDVF
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring) :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) =
      σ (x : standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :=
  rfl

private theorem
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv_continuous
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (σ : Gal((standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)/ℚ_[p])) :
    Continuous (padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let target := standardLubinTateLevelCompleteDVF hπ n
  let : WithIdeal target.valuationSubring :=
    padicMultiplicativeLevelTargetWithIdeal
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  let r := padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ
  apply continuous_of_continuousAt_zero r
  rw [ContinuousAt, map_zero]
  have hadic : IsAdic target.maximalIdeal := rfl
  apply (hadic.hasBasis_nhds_zero.tendsto_right_iff).2
  intro m _
  apply (hadic.hasBasis_nhds_zero.mem_iff).2
  refine ⟨m, trivial, ?_⟩
  intro x hx
  exact
    (higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves_mem_maximalIdeal_pow_iff
      target σ.toRingEquiv
      (padicMultiplicativeLevelAlgEquiv_mem_valuationSubring_iff p n σ)
      m x).2 hx

private theorem
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv_comp_coefficientHom
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (σ : Gal((standardLubinTateLevelField
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)/ℚ_[p])) :
    (padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ :
        (standardLubinTateLevelCompleteDVF
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring →+*
        (standardLubinTateLevelCompleteDVF
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring).comp
      (standardLubinTateLevelCoefficientHom
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) =
      standardLubinTateLevelCoefficientHom
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n := by
  ext a : 1
  apply Subtype.ext
  simp only [RingHom.comp_apply]
  exact σ.commutes (a : ℚ_[p])

private theorem
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv_primitivePointEvaluation
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n
        ((standardLubinTateUnitParameterEquivGal
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u))⁻¹)
        (padicMultiplicativePrimitivePoint p n) =
      standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTatePrimitivePointIntegerAction
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n u⁻¹)
        (standardLubinTatePrimitivePointIntegerAction_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n u⁻¹)
        (padicStandardToMultiplicativeIntertwiner p) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let target := standardLubinTateLevelCompleteDVF hπ n
  let L := standardLubinTateLevelField hπ n
  let σ : Gal(L / ℚ_[p]) :=
    (standardLubinTateUnitParameterEquivGal
      (padicLocalField p) hπ n
      (standardLubinTateUnitParameterClass
        (padicLocalField p) n u))⁻¹
  let r := padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ
  let H := padicStandardToMultiplicativeIntertwiner p
  let lambda := standardLubinTatePrimitivePointInteger hπ n
  let lambdaInv := standardLubinTatePrimitivePointIntegerAction hπ n u⁻¹
  let hlambdaInv :=
    standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u⁻¹
  let zetaMinusOne := padicMultiplicativePrimitivePoint p n
  let : WithIdeal target.valuationSubring :=
    padicMultiplicativeLevelTargetWithIdeal
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  have hrLambda : r lambda = lambdaInv := by
    apply Subtype.ext
    rw [padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply]
    change
      σ (standardLubinTateLevelGenerator hπ n) =
        standardLubinTatePrimitiveLevelAction hπ n u⁻¹
    simpa only [σ, standardLubinTateLevelGenerator] using
      standardLubinTateUnitParameterEquivGal_inv_class_apply_gen
        (padicLocalField p) hπ n u
  have hcoeffContinuous :
      @Continuous
        (padicLocalField p).valuationSubring
        target.valuationSubring
        (padicMultiplicativeLevelCoefficientUniformSpace
          (padicLocalField p)).toTopologicalSpace
        (inferInstance : UniformSpace target.valuationSubring).toTopologicalSpace
        (standardLubinTateLevelCoefficientHom hπ n) := by
    change @Continuous
      (padicLocalField p).valuationSubring target.valuationSubring ⊥ _ _
    exact
      @continuous_of_discreteTopology
        (padicLocalField p).valuationSubring
        ⊥
        (discreteTopology_bot (padicLocalField p).valuationSubring)
        target.valuationSubring
        _
        (standardLubinTateLevelCoefficientHom hπ n)
  let : T2Space target.valuationSubring :=
    padicMultiplicativeLevelTargetT2Space
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  let : CompleteSpace target.valuationSubring :=
    padicMultiplicativeLevelTargetCompleteSpace
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  have hcomp :=
    PowerSeries.comp_eval₂
      (R := (padicLocalField p).valuationSubring)
      (S := target.valuationSubring)
      (φ := standardLubinTateLevelCoefficientHom hπ n)
      (a := lambda)
      hcoeffContinuous
      (standardLubinTatePrimitivePointInteger_hasEval hπ n)
      (ε := (r : target.valuationSubring →+* target.valuationSubring))
      (padicMultiplicativeLevelAutomorphismIntegerRingEquiv_continuous p n σ)
  have happ := congrArg (fun f => f H) hcomp
  rw [padicMultiplicativeLevelAutomorphismIntegerRingEquiv_comp_coefficientHom
    p n σ] at happ
  have hrLambdaRing :
      (r : target.valuationSubring →+* target.valuationSubring) lambda =
        lambdaInv :=
    hrLambda
  rw [hrLambdaRing] at happ
  change
    r zetaMinusOne =
      standardLubinTateLevelPowerSeriesEval hπ n lambdaInv hlambdaInv H
  simpa [zetaMinusOne, padicMultiplicativePrimitivePoint,
    standardLubinTatePrimitivePointEvaluation,
    standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, Function.comp_apply,
    target, lambda, H] using happ

/-- For the finite Galois element supplied by the Lubin--Tate unit
parameter, the inverse automorphism acts on the actual primitive
`p ^ (n + 1)`-st root by the inverse unit exponent modulo `p ^ (n + 1)`.
This is the explicit cyclotomic norm-residue formula. -/
theorem padicMultiplicativePrimitiveRoot_galoisAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    (standardLubinTateUnitParameterEquivGal
        (padicLocalField p)
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u))⁻¹
        (padicMultiplicativePrimitiveRoot p n) =
      padicMultiplicativePrimitiveRoot p n ^
        (PadicInt.toZModPow (p := p) (n + 1)
          ((padicIntEquivValuationSubring p).symm
            ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring))).val := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let target := standardLubinTateLevelCompleteDVF hπ n
  let L := standardLubinTateLevelField hπ n
  let σ : Gal(L / ℚ_[p]) :=
    (standardLubinTateUnitParameterEquivGal
      (padicLocalField p) hπ n
      (standardLubinTateUnitParameterClass
        (padicLocalField p) n u))⁻¹
  let r := padicMultiplicativeLevelAutomorphismIntegerRingEquiv p n σ
  let H := padicStandardToMultiplicativeIntertwiner p
  let lambdaInv :=
    standardLubinTatePrimitivePointIntegerAction hπ n u⁻¹
  let hlambdaInv :=
    standardLubinTatePrimitivePointIntegerAction_hasEval hπ n u⁻¹
  let zetaMinusOne := padicMultiplicativePrimitivePoint p n
  have hσOneAdd (x : L) : σ (1 + x) = 1 + σ x := by
    calc
      σ (1 + x) = σ 1 + σ x := σ.map_add 1 x
      _ = 1 + σ x := congrArg (fun y : L => y + σ x) σ.map_one
  have hrApply (x : target.valuationSubring) :
      ((r x : target.valuationSubring) : L) =
        σ (x : L) :=
    padicMultiplicativeLevelAutomorphismIntegerRingEquiv_apply p n σ x
  have hrEval :
      r zetaMinusOne =
        standardLubinTateLevelPowerSeriesEval hπ n
          lambdaInv hlambdaInv H := by
    exact
      padicMultiplicativeLevelAutomorphismIntegerRingEquiv_primitivePointEvaluation
        p n u
  change
    σ (padicMultiplicativePrimitiveRoot p n) =
      padicMultiplicativePrimitiveRoot p n ^
        (PadicInt.toZModPow (p := p) (n + 1)
          ((padicIntEquivValuationSubring p).symm
            ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring))).val
  calc
    σ (padicMultiplicativePrimitiveRoot p n) =
        σ (1 + (zetaMinusOne : L)) := by
      rfl
    _ = 1 + σ (zetaMinusOne : L) :=
      hσOneAdd (zetaMinusOne : L)
    _ = 1 + (r zetaMinusOne : L) := by
      rw [hrApply]
    _ =
        1 +
          (standardLubinTateLevelPowerSeriesEval hπ n
            lambdaInv hlambdaInv H : L) := by
      rw [hrEval]
    _ =
        padicMultiplicativePrimitiveRoot p n ^
          (PadicInt.toZModPow (p := p) (n + 1)
            ((padicIntEquivValuationSubring p).symm
              ((u⁻¹ : (padicLocalField p).valuationSubringˣ) :
                (padicLocalField p).valuationSubring))).val := by
      simpa only [hπ, H, lambdaInv, hlambdaInv] using
        padicMultiplicativePrimitiveRoot_unitAction p n u⁻¹

/-- The finite Lubin--Tate parameter automorphism itself acts on the
genuine primitive `p ^ (n + 1)`-st root by the direct unit exponent.

This is the direct-orientation companion to
`padicMultiplicativePrimitiveRoot_galoisAction`: applying that theorem
to the inverse unit cancels both inversions. -/
theorem padicMultiplicativePrimitiveRoot_unitParameterGaloisAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    standardLubinTateUnitParameterEquivGal
        (padicLocalField p)
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u)
        (padicMultiplicativePrimitiveRoot p n) =
      padicMultiplicativePrimitiveRoot p n ^
        (PadicInt.toZModPow (p := p) (n + 1)
          ((padicIntEquivValuationSubring p).symm
            ((u : (padicLocalField p).valuationSubringˣ) :
              (padicLocalField p).valuationSubring))).val := by
  simpa only [map_inv, inv_inv] using
    padicMultiplicativePrimitiveRoot_galoisAction p n u⁻¹

/-- The multiplicative comparison identifies the standard level-`n`
Lubin--Tate generator with a primitive `p ^ (n + 1)`-st root of unity. -/
theorem padicMultiplicativePrimitiveRoot_isPrimitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsPrimitiveRoot (padicMultiplicativePrimitiveRoot p n) (p ^ (n + 1)) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let iteratePoint :=
    standardLubinTatePrimitivePointIterateInteger hπ n
  have hfinalInteger :
      (1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ (n + 1)) = 1 := by
    have hpow :=
      padicMultiplicativePrimitivePoint_pow_primePower p n (n + 1)
    have hevalZero :
        standardLubinTateLevelPowerSeriesEval hπ n
            (iteratePoint (n + 1))
            (standardLubinTatePrimitivePointIterateInteger_hasEval
              hπ n (n + 1)) H =
          0 := by
      have hpoint :
          iteratePoint (n + 1) = 0 := by
        simpa only [iteratePoint,
          standardLubinTatePrimitivePointIterateInteger,
          standardLubinTateLevelCoefficientHom] using
          standardLubinTatePrimitivePointInteger_iterate_succ_eq_zero hπ n
      let evalForward :
          {z :
              (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
            PowerSeries.HasEval z} →
            (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
        fun z =>
          standardLubinTateLevelPowerSeriesEval hπ n z.1 z.2 H
      have hpacked :
          (⟨iteratePoint (n + 1),
              standardLubinTatePrimitivePointIterateInteger_hasEval
                hπ n (n + 1)⟩ :
              {z :
                  (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
                PowerSeries.HasEval z}) =
            ⟨0, PowerSeries.HasEval.zero⟩ :=
        Subtype.ext hpoint
      exact
        (congrArg evalForward hpacked).trans
          (padicStandardToMultiplicativeIntertwiner_eval_zero p n)
    calc
      _ = 1 +
          standardLubinTateLevelPowerSeriesEval hπ n
            (iteratePoint (n + 1))
            (standardLubinTatePrimitivePointIterateInteger_hasEval
              hπ n (n + 1)) H := hpow
      _ = 1 := by rw [hevalZero, add_zero]
  have hfinal :
      padicMultiplicativePrimitiveRoot p n ^ (p ^ (n + 1)) = 1 := by
    simpa [padicMultiplicativePrimitiveRoot] using
      congrArg
        (fun z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =>
            (z : standardLubinTateLevelField hπ n))
        hfinalInteger
  have hprevious :
      ¬padicMultiplicativePrimitiveRoot p n ^ (p ^ n) = 1 := by
    intro hpower
    have hpowerInteger :
        (1 + padicMultiplicativePrimitivePoint p n) ^ (p ^ n) = 1 := by
      apply Subtype.ext
      simpa [padicMultiplicativePrimitiveRoot] using hpower
    have hiterateEvaluation :
        standardLubinTateLevelPowerSeriesEval hπ n (iteratePoint n)
            (standardLubinTatePrimitivePointIterateInteger_hasEval hπ n n) H =
          0 := by
      have hpow :=
        padicMultiplicativePrimitivePoint_pow_primePower p n n
      rw [hpowerInteger] at hpow
      have hsub := congrArg
        (fun z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring =>
            z - 1)
        hpow
      simpa using hsub.symm
    have hiterateZero : iteratePoint n = 0 := by
      apply padicStandardToMultiplicativeIntertwiner_eval_injective
        p n
        (standardLubinTatePrimitivePointIterateInteger_hasEval hπ n n)
        PowerSeries.HasEval.zero
      simpa [H, padicStandardToMultiplicativeIntertwiner_eval_zero] using
        hiterateEvaluation
    exact
      padicStandardLubinTatePrimitivePointIterateInteger_ne_zero p n
        hiterateZero
  rw [IsPrimitiveRoot.iff_orderOf]
  exact orderOf_eq_prime_pow hprevious hfinal

end LubinTate

end
