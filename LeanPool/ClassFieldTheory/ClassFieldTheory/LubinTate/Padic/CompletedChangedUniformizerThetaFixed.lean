/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation
/-!
# Fixedness of completed p-adic changed-uniformizer theta values

The Frobenius lift whose primitive-point action is indexed by the inverse
unit is the genuine diagonal action relevant to change of uniformizer.
Semilinear evaluation changes theta coefficients by Witt Frobenius, while
the first changed-uniformizer identity changes the evaluation point by the
unit itself.  The unit and inverse-unit actions cancel, so the actual
convergent theta value is fixed.
-/

noncomputable section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

private noncomputable local instance (priority := 50)
    padicCompletedThetaFixedWittUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicCompletedUnramifiedWittRing p) :=
  ⊥

private noncomputable local instance
    padicCompletedThetaFixedTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

private noncomputable local instance
    padicCompletedThetaFixedTargetCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

private noncomputable local instance
    padicCompletedThetaFixedTargetT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

private theorem padicCompletedThetaFixedEvaluation_eq_of_point_eq
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x y : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y) :
    padicCompletedLevelPowerSeriesEval p n x hx =
      padicCompletedLevelPowerSeriesEval p n y hy := by
  subst y
  rfl

/-- On the genuine multiplicative primitive point, the multiplicative
unit action cancels the inverse-unit action prescribed by the diagonal
completed Frobenius lift. -/
theorem padicCompletedDiagonalFrobenius_multiplicativeUnitAction
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    let r :=
      padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹
    let x := padicCompletedMultiplicativePrimitivePoint p n
    let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (r x)
        (padicCompletedUnitFrobeniusIntegerEquiv_hasEval
          p n u⁻¹ x hx)
        (u : (padicLocalField p).valuationSubring) =
      x := by
  let r :=
    padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  have hpoint :
      r x =
        padicCompletedMultiplicativePrimitivePointUnitAction p u⁻¹ n := by
    simpa only [r, x] using
      padicCompletedUnitFrobeniusIntegerEquiv_multiplicativePrimitivePoint
        p n u⁻¹
  have htransport :=
    DFunLike.congr_fun
      (padicCompletedThetaFixedEvaluation_eq_of_point_eq p n
        (r x)
        (padicCompletedMultiplicativePrimitivePointUnitAction p u⁻¹ n)
        (padicCompletedUnitFrobeniusIntegerEquiv_hasEval
          p n u⁻¹ x hx)
        (padicCompletedMultiplicativePrimitivePointUnitAction_hasEval
          p u⁻¹ n)
        hpoint)
      (padicCompletedMultiplicativeUnitEndomorphism p u)
  calc
    padicCompletedMultiplicativeScalarEndomorphismValue p n
        (r x)
        (padicCompletedUnitFrobeniusIntegerEquiv_hasEval
          p n u⁻¹ x hx)
        (u : (padicLocalField p).valuationSubring) =
      padicCompletedMultiplicativeScalarEndomorphismValue p n
        (padicCompletedMultiplicativePrimitivePointUnitAction p u⁻¹ n)
        (padicCompletedMultiplicativePrimitivePointUnitAction_hasEval
          p u⁻¹ n)
        (u : (padicLocalField p).valuationSubring) := by
      simpa only [padicCompletedMultiplicativeUnitEndomorphism,
        padicCompletedMultiplicativeScalarEndomorphismValue] using
        htransport
    _ = x := by
      simpa only [x, hx,
        padicCompletedMultiplicativePrimitivePointUnitAction,
        padicCompletedMultiplicativeUnitEndomorphism,
        padicCompletedMultiplicativeScalarEndomorphismValue] using
        (padicCompletedMultiplicativeScalarEndomorphismValue_unit_after_inverse
          p n
          (padicCompletedMultiplicativePrimitivePoint p n)
          (padicCompletedMultiplicativePrimitivePoint_hasEval p n) u)

/-- The inverse-unit diagonal completed Frobenius fixes the genuine
changed-uniformizer theta value in the completed-level valuation ring. -/
theorem
    padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobeniusInteger
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹
        (padicChangedUniformizerThetaValue p u n) =
      padicChangedUniformizerThetaValue p u n := by
  let r :=
    padicCompletedUnitFrobeniusIntegerEquiv p n u⁻¹
  let x := padicCompletedMultiplicativePrimitivePoint p n
  let hx := padicCompletedMultiplicativePrimitivePoint_hasEval p n
  let rx := r x
  let hrx :=
    padicCompletedUnitFrobeniusIntegerEquiv_hasEval
      p n u⁻¹ x hx
  let U := padicCompletedMultiplicativeUnitEndomorphism p u
  let xBack :=
    padicCompletedLevelPowerSeriesEval p n rx hrx U
  let hxBack :=
    padicCompletedLevelPowerSeriesEval_hasEval p n rx hrx U
      (padicCompletedMultiplicativeUnitEndomorphism_hasSubst p u)
  let Θ := padicChangedUniformizerIntertwiner p u
  have hsemi :=
    padicCompletedUnitFrobeniusIntegerEquiv_evaluation
      p n u⁻¹ x hx Θ
  have hfrobenius :=
    padicChangedUniformizerIntertwiner_frobenius_evaluation
      p u n rx hrx
  have hpoint : xBack = x := by
    change
      padicCompletedMultiplicativeScalarEndomorphismValue p n rx hrx
          (u : (padicLocalField p).valuationSubring) =
        x
    simpa only [r, x, hx, rx, hrx] using
      (padicCompletedDiagonalFrobenius_multiplicativeUnitAction p u n)
  have hevaluation :
      padicCompletedLevelPowerSeriesEval p n xBack hxBack Θ =
        padicCompletedLevelPowerSeriesEval p n x hx Θ :=
    DFunLike.congr_fun
      (padicCompletedThetaFixedEvaluation_eq_of_point_eq
        p n xBack x hxBack hx hpoint) Θ
  change
    r (padicCompletedLevelPowerSeriesEval p n x hx Θ) =
      padicCompletedLevelPowerSeriesEval p n x hx Θ
  calc
    _ =
        padicCompletedLevelPowerSeriesEval p n rx hrx
          (PowerSeries.map WittVector.frobenius Θ) := by
      simpa only [r, x, hx, rx, hrx, Θ] using hsemi
    _ = padicCompletedLevelPowerSeriesEval p n xBack hxBack Θ := by
      simpa only [xBack, hxBack, U, Θ] using hfrobenius
    _ = padicCompletedLevelPowerSeriesEval p n x hx Θ :=
      hevaluation

/-- The inverse-unit diagonal completed Frobenius field automorphism fixes
the genuine changed-uniformizer theta value. -/
theorem
    padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobenius
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ) (n : ℕ) :
    padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹
        ((padicChangedUniformizerThetaValue p u n :
            (padicCompletedLevelCompleteDVF p n).valuationSubring) :
          padicCompletedLevelField p n) =
      ((padicChangedUniformizerThetaValue p u n :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n) := by
  simpa only [padicCompletedUnitFrobeniusIntegerEquiv_coe] using
    congrArg
      (fun z : (padicCompletedLevelCompleteDVF p n).valuationSubring =>
        (z : padicCompletedLevelField p n))
      (padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobeniusInteger
        p u n)

end LubinTate

end
