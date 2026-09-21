/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalGlobalNormalizedAutomatic
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurvePoweredHeightBounds
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredCoordinates
import Mathlib.Tactic

/-!
# The canonical Corvaja--Zannier bound for powered plane coordinates

This module composes the automatic canonical placewise estimate with the
first-coordinate model of a plane function field.  Linear independence of
the auxiliary family supplies the Wronskian nonvanishing, while the two
powered-coordinate height theorems replace abstract positive divisor degrees
by the actual bidegree budgets.
-/

namespace BGS.CorvajaZannier

noncomputable section

open scoped BigOperators Polynomial

/-- The automatic canonical placewise estimate, specialized to
`u = x^m`, `v = y^n` on a plane curve and expressed using the actual
coordinate degrees. -/
theorem finiteExtensionGcdBound_planeCurvePowers_of_auxiliaryFamily_linearIndependent
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h k : ℕ) (hcard : 0 < h * k + h + k) (chi : ℕ) :
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
      planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    LinearIndependent
        (frobeniusSubfield (PlaneCurveFunctionField f) p)
        (auxiliaryFamily ((planeCurveFunction f 0) ^ m)
          ((planeCurveFunction f 1) ^ n) h k) →
      finiteExtensionDivisorDegree K (PlaneCurveFunctionField f)
            (finiteExtensionCanonicalDifferentDivisor K
              (PlaneCurveFunctionField f)
              (finiteExtensionFiniteDifferentIdeal_ne_bot K
                (PlaneCurveFunctionField f))) +
          (∑ P ∈ propositionTwoExceptionalPlaces K (PlaneCurveFunctionField f)
              ((planeCurveFunction f 0) ^ m) ((planeCurveFunction f 1) ^ n),
            finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) P : ℤ) ≤
        (chi : ℤ) →
      (finiteExtensionGcdWeightedDegree K (PlaneCurveFunctionField f)
          (1 - (planeCurveFunction f 0) ^ m)
          (1 - (planeCurveFunction f 1) ^ n) : ℝ) ≤
        ((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            ((n * MvPolynomial.degreeOf 0 f : ℕ) : ℝ) +
          (k : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            ((m * MvPolynomial.degreeOf 1 f : ℕ) : ℝ) +
          ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  dsimp only
  intro hLI hEuler
  let F := frobeniusSubfield L p
  have hxTrans : Transcendental K x := hx
  have hyTrans : Transcendental K y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hxTrans
    rw [hzero]
    exact isAlgebraic_zero
  have hy0 : y ≠ 0 := by
    intro hzero
    apply hyTrans
    rw [hzero]
    exact isAlgebraic_zero
  have hxm0 : x ^ m ≠ 0 := pow_ne_zero m hx0
  have hyn0 : y ^ n ≠ 0 := pow_ne_zero n hy0
  have hxm1 : x ^ m ≠ 1 := by
    intro hone
    apply hxTrans.pow hm
    rw [hone]
    exact isAlgebraic_one
  have hyn1 : y ^ n ≠ 1 := by
    intro hone
    apply hyTrans.pow hn
    rw [hone]
    exact isAlgebraic_one
  have hsepX :=
    (finiteSeparable_over_firstCoordinate_of_irreducible
      hf hpartialSecond).2
  letI : Algebra.IsSeparable (FirstCoordinateSubfield f) L := hsepX
  letI : Algebra.IsSeparable (IntermediateField.adjoin F {x}) L :=
    isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin
      (K := K) (L := L) (p := p) x
  have hxNot : x ∉ F :=
    firstCoordinate_not_mem_frobeniusSubfield hf hpartialSecond
  obtain ⟨D, hDx, hconstants⟩ :=
    exists_derivation_with_exact_frobenius_constants (p := p) x hxNot
  have hmapX : algebraMap (RatFunc K) L RatFunc.X = x := by
    change ratFuncSpecialization x hx RatFunc.X = x
    exact planeCurveFirstCoordinateRatFuncAlgebra_X f hx
  have hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1 := by
    rw [hmapX]
    exact hDx
  have hWronskian :
      (indexedDedekindLocalWronskian D
        (auxiliaryFamilyDerivativeOrder h k)
        (auxiliaryFamily (x ^ m) (y ^ n) h k)).det ≠ 0 := by
    exact indexedAuxiliaryWronskian_det_ne_zero_of_linearIndependent D
      (fun z hz ↦ (hconstants z).mp hz) h k
        (auxiliaryFamily (x ^ m) (y ^ n) h k) hLI
  have hcanonical :=
    finiteExtensionGcdBound_of_normalizedCanonicalPlacewiseBounds
      K L D hDX (x ^ m) (y ^ n) hxm0 hyn0 hxm1 hyn1
        h k hcard chi hWronskian hEuler
  have hxDegree : finiteExtensionPositiveDegree K L (x ^ m) =
      m * MvPolynomial.degreeOf 1 f := by
    simpa only [L, x] using
      finiteExtensionPositiveDegree_planeCurveFirstCoordinate_pow
        hf hpartialSecond m hm
  have hyDegree : finiteExtensionPositiveDegree K L (y ^ n) ≤
      n * MvPolynomial.degreeOf 0 f := by
    simpa only [L, y] using
      finiteExtensionPositiveDegree_planeCurveSecondCoordinate_pow_le
        hf hpartialFirst hpartialSecond n
  have hdenom : (0 : ℝ) < (h * k + h + k : ℕ) := by
    exact_mod_cast hcard
  have hfirstCoeff :
      (0 : ℝ) ≤ ((h + 2 * k : ℕ) : ℝ) /
        ((h * k + h + k : ℕ) : ℝ) := by positivity
  calc
    (finiteExtensionGcdWeightedDegree K L (1 - x ^ m) (1 - y ^ n) : ℝ) ≤
        ((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            (finiteExtensionPositiveDegree K L (y ^ n) : ℝ) +
          (k : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            (finiteExtensionPositiveDegree K L (x ^ m) : ℝ) +
          ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ) := hcanonical
    _ ≤ ((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            ((n * MvPolynomial.degreeOf 0 f : ℕ) : ℝ) +
          (k : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            ((m * MvPolynomial.degreeOf 1 f : ℕ) : ℝ) +
          ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ) := by
      rw [hxDegree]
      gcongr

/-- The companion specialization with the powered coordinates exchanged.
Here the leading coefficient multiplies the exact height of `x^m`, while the
second coefficient multiplies the degree budget for `y^n`. -/
theorem finiteExtensionGcdBound_planeCurvePowers_swapped_of_auxiliaryFamily_linearIndependent
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h k : ℕ) (hcard : 0 < h * k + h + k) (chi : ℕ) :
    letI : IsDomain (PlaneCurveCoordinateRing f) :=
      planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    letI : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
      planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    LinearIndependent
        (frobeniusSubfield (PlaneCurveFunctionField f) p)
        (auxiliaryFamily ((planeCurveFunction f 1) ^ n)
          ((planeCurveFunction f 0) ^ m) h k) →
      finiteExtensionDivisorDegree K (PlaneCurveFunctionField f)
            (finiteExtensionCanonicalDifferentDivisor K
              (PlaneCurveFunctionField f)
              (finiteExtensionFiniteDifferentIdeal_ne_bot K
                (PlaneCurveFunctionField f))) +
          (∑ P ∈ propositionTwoExceptionalPlaces K (PlaneCurveFunctionField f)
              ((planeCurveFunction f 1) ^ n) ((planeCurveFunction f 0) ^ m),
            finiteExtensionPlaceDegree K (PlaneCurveFunctionField f) P : ℤ) ≤
        (chi : ℤ) →
      (finiteExtensionGcdWeightedDegree K (PlaneCurveFunctionField f)
          (1 - (planeCurveFunction f 1) ^ n)
          (1 - (planeCurveFunction f 0) ^ m) : ℝ) ≤
        ((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            ((m * MvPolynomial.degreeOf 1 f : ℕ) : ℝ) +
          (k : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            ((n * MvPolynomial.degreeOf 0 f : ℕ) : ℝ) +
          ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ) := by
  letI : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  letI : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  letI : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  letI : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  dsimp only
  intro hLI hEuler
  let F := frobeniusSubfield L p
  have hxTrans : Transcendental K x := hx
  have hyTrans : Transcendental K y :=
    secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hx0 : x ≠ 0 := by
    intro hzero
    apply hxTrans
    rw [hzero]
    exact isAlgebraic_zero
  have hy0 : y ≠ 0 := by
    intro hzero
    apply hyTrans
    rw [hzero]
    exact isAlgebraic_zero
  have hxm0 : x ^ m ≠ 0 := pow_ne_zero m hx0
  have hyn0 : y ^ n ≠ 0 := pow_ne_zero n hy0
  have hxm1 : x ^ m ≠ 1 := by
    intro hone
    apply hxTrans.pow hm
    rw [hone]
    exact isAlgebraic_one
  have hyn1 : y ^ n ≠ 1 := by
    intro hone
    apply hyTrans.pow hn
    rw [hone]
    exact isAlgebraic_one
  have hsepX :=
    (finiteSeparable_over_firstCoordinate_of_irreducible
      hf hpartialSecond).2
  letI : Algebra.IsSeparable (FirstCoordinateSubfield f) L := hsepX
  letI : Algebra.IsSeparable (IntermediateField.adjoin F {x}) L :=
    isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin
      (K := K) (L := L) (p := p) x
  have hxNot : x ∉ F :=
    firstCoordinate_not_mem_frobeniusSubfield hf hpartialSecond
  obtain ⟨D, hDx, hconstants⟩ :=
    exists_derivation_with_exact_frobenius_constants (p := p) x hxNot
  have hmapX : algebraMap (RatFunc K) L RatFunc.X = x := by
    change ratFuncSpecialization x hx RatFunc.X = x
    exact planeCurveFirstCoordinateRatFuncAlgebra_X f hx
  have hDX : D (algebraMap (RatFunc K) L RatFunc.X) = 1 := by
    rw [hmapX]
    exact hDx
  have hWronskian :
      (indexedDedekindLocalWronskian D
        (auxiliaryFamilyDerivativeOrder h k)
        (auxiliaryFamily (y ^ n) (x ^ m) h k)).det ≠ 0 := by
    exact indexedAuxiliaryWronskian_det_ne_zero_of_linearIndependent D
      (fun z hz ↦ (hconstants z).mp hz) h k
        (auxiliaryFamily (y ^ n) (x ^ m) h k) hLI
  have hcanonical :=
    finiteExtensionGcdBound_of_normalizedCanonicalPlacewiseBounds
      K L D hDX (y ^ n) (x ^ m) hyn0 hxm0 hyn1 hxm1
        h k hcard chi hWronskian hEuler
  have hxDegree : finiteExtensionPositiveDegree K L (x ^ m) =
      m * MvPolynomial.degreeOf 1 f := by
    simpa only [L, x] using
      finiteExtensionPositiveDegree_planeCurveFirstCoordinate_pow
        hf hpartialSecond m hm
  have hyDegree : finiteExtensionPositiveDegree K L (y ^ n) ≤
      n * MvPolynomial.degreeOf 0 f := by
    simpa only [L, y] using
      finiteExtensionPositiveDegree_planeCurveSecondCoordinate_pow_le
        hf hpartialFirst hpartialSecond n
  have hdenom : (0 : ℝ) < (h * k + h + k : ℕ) := by
    exact_mod_cast hcard
  have hsecondCoeff :
      (0 : ℝ) ≤ (k : ℝ) / ((h * k + h + k : ℕ) : ℝ) := by
    positivity
  calc
    (finiteExtensionGcdWeightedDegree K L (1 - y ^ n) (1 - x ^ m) : ℝ) ≤
        ((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            (finiteExtensionPositiveDegree K L (x ^ m) : ℝ) +
          (k : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            (finiteExtensionPositiveDegree K L (y ^ n) : ℝ) +
          ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ) := hcanonical
    _ ≤ ((h + 2 * k : ℕ) : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            ((m * MvPolynomial.degreeOf 1 f : ℕ) : ℝ) +
          (k : ℝ) / ((h * k + h + k : ℕ) : ℝ) *
            ((n * MvPolynomial.degreeOf 0 f : ℕ) : ℝ) +
          ((((h * k + h + k : ℕ) : ℝ) - 1) / 2) * (chi : ℝ) := by
      rw [hxDegree]
      gcongr

end

end BGS.CorvajaZannier
