/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeIntertwiner
public import Mathlib.RingTheory.AdicCompletion.Topology
/-!
# Finite-level evaluation of the p-adic multiplicative comparison

This module evaluates the standard-to-multiplicative Lubin--Tate comparison
on topologically nilpotent integers in a standard finite level.  It proves
the functional equation, compatibility with scalar endomorphisms, the inverse
comparison identity, and injectivity of the evaluated comparison.
-/

@[expose] public section

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

variable {K : Type u} [Field K]

/-- The discrete coefficient uniformity used for finite-level analytic evaluation. -/
noncomputable local instance
    padicMultiplicativeLevelCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace F.valuationSubring :=
  ⊥

/-- The maximal-ideal adic structure on a standard finite Lubin--Tate level. -/
noncomputable local instance
    padicMultiplicativeLevelTargetWithIdeal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring where
  i := (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal

/-- Completeness of the standard finite-level valuation ring for its adic topology. -/
noncomputable local instance
    padicMultiplicativeLevelTargetCompleteSpace
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

/-- Separatedness of the standard finite-level valuation ring for its adic topology. -/
noncomputable local instance
    padicMultiplicativeLevelTargetT2Space
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

section PadicLevelTopology

/-- The specialized level uses the same maximal-ideal adic topology as the generic evaluator. -/
noncomputable local instance
    padicMultiplicativeLevelTargetTopologicalSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    TopologicalSpace
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring :=
  @WithIdeal.instTopologicalSpace _ _
    (padicMultiplicativeLevelTargetWithIdeal
      (F := padicLocalField p)
      (π := show (padicLocalField p).valuationSubring from
        padicIntEquivValuationSubring p (p : ℤ_[p]))
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n)

/-- Evaluation of the standard-to-multiplicative comparison at the chosen
standard primitive point of level `n + 1`. -/
noncomputable def padicMultiplicativePrimitivePoint
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring :=
  standardLubinTatePrimitivePointEvaluation
    (padicMultiplicativeLubinTateSeries_isUniformizer p) n
    (padicStandardToMultiplicativeIntertwiner p)

/-- The evaluated multiplicative point is topologically nilpotent. -/
theorem padicMultiplicativePrimitivePoint_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    PowerSeries.HasEval (padicMultiplicativePrimitivePoint p n) := by
  exact
    standardLubinTateLevelPowerSeriesEval_hasEval
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      (standardLubinTatePrimitivePointInteger
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n)
      (standardLubinTatePrimitivePointInteger_hasEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n)
      (padicStandardToMultiplicativeIntertwiner p)
      (padicStandardToMultiplicativeIntertwiner_hasSubst p)

/-- At every standard level, analytic evaluation of the multiplicative
Lubin--Tate series is the literal polynomial `(1 + x)^p - 1`. -/
theorem padicMultiplicativeLubinTateSeries_eval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
        (padicMultiplicativeLubinTateSeries p).toPowerSeries =
      (1 + x) ^ p - 1 := by
  rw [
    LubinTateSeries.padicMultiplicativeLubinTateSeries_toPowerSeries,
    PowerSeries.binomialSeries_nat (R := ℤ)]
  simp only [map_sub, map_pow, map_add, map_one]
  exact congrArg
    (fun z : (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring =>
        (1 + z) ^ p - 1)
    (standardLubinTateLevelPowerSeriesEval_X
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx)

/-- Analytic evaluation preserves the standard-to-multiplicative
intertwining equation at every topologically nilpotent level integer. -/
theorem padicStandardToMultiplicativeIntertwiner_eval_functionalEquation
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p))
        (standardLubinTateLevelPowerSeriesEval_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p)
          (padicStandardToMultiplicativeIntertwiner_hasSubst p))
        (padicMultiplicativeLubinTateSeries p).toPowerSeries =
      standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (standardLubinTateSeries
            (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries)
        (standardLubinTateLevelPowerSeriesEval_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (standardLubinTateSeries
            (padicMultiplicativeLubinTateSeries_isUniformizer p)).toPowerSeries
          (PowerSeries.HasSubst.of_constantCoeff_zero
            (LubinTateSeries.constantCoeff_eq_zero
              (standardLubinTateSeries
                (padicMultiplicativeLubinTateSeries_isUniformizer p)))))
        (padicStandardToMultiplicativeIntertwiner p) := by
  let hπ :=
    padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let E := padicMultiplicativeLubinTateSeries p
  let Ebar := standardLubinTateSeries hπ
  let hH : PowerSeries.HasSubst H :=
    padicStandardToMultiplicativeIntertwiner_hasSubst p
  let hEbar : PowerSeries.HasSubst Ebar.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero
      Ebar.constantCoeff_eq_zero
  let hHEval :
      PowerSeries.HasEval
        (standardLubinTateLevelPowerSeriesEval hπ n x hx H) :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n x hx H hH
  let hEbarEval :
      PowerSeries.HasEval
        (standardLubinTateLevelPowerSeriesEval
          hπ n x hx Ebar.toPowerSeries) :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n x hx Ebar.toPowerSeries hEbar
  calc
    standardLubinTateLevelPowerSeriesEval hπ n
        (standardLubinTateLevelPowerSeriesEval hπ n x hx H)
        hHEval E.toPowerSeries =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          (PowerSeries.subst H E.toPowerSeries) :=
      (standardLubinTateLevelPowerSeriesEval_subst
        hπ n x hx H E.toPowerSeries hH hHEval).symm
    _ =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          (PowerSeries.subst Ebar.toPowerSeries H) := by
      rw [padicStandardToMultiplicativeIntertwiner_functionalEquation]
    _ =
        standardLubinTateLevelPowerSeriesEval hπ n
          (standardLubinTateLevelPowerSeriesEval
            hπ n x hx Ebar.toPowerSeries)
          hEbarEval H :=
      standardLubinTateLevelPowerSeriesEval_subst
        hπ n x hx Ebar.toPowerSeries H hEbar hEbarEval

/-- Finite-level evaluation of the comparison carries the standard scalar
action with coefficient `a` to the unique multiplicative-series scalar
action with the same coefficient. -/
theorem padicStandardToMultiplicativeIntertwiner_eval_endomorphism
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a : (padicLocalField p).valuationSubring) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateEndomorphismEvalAt
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx a)
        (standardLubinTateEndomorphismEvalAt_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx a)
        (padicStandardToMultiplicativeIntertwiner p) =
      standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p))
        (standardLubinTateLevelPowerSeriesEval_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p)
          (padicStandardToMultiplicativeIntertwiner_hasSubst p))
        (recursiveIntertwiner
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          (padicMultiplicativeLubinTateSeries p)
          (padicMultiplicativeLubinTateSeries p)
          (fun _ : Unit => a)) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let S := standardLubinTateEndomorphism hπ a
  let M :=
    recursiveIntertwiner hπ
      (padicMultiplicativeLubinTateSeries p)
      (padicMultiplicativeLubinTateSeries p)
      (fun _ : Unit => a)
  let xS := standardLubinTateEndomorphismEvalAt hπ n x hx a
  let xH := standardLubinTateLevelPowerSeriesEval hπ n x hx H
  let hSSubst : PowerSeries.HasSubst S :=
    (standardLubinTateEndomorphism_hasLinearTerm hπ a).hasSubst
  let hHSubst : PowerSeries.HasSubst H :=
    padicStandardToMultiplicativeIntertwiner_hasSubst p
  let hxS : PowerSeries.HasEval xS :=
    standardLubinTateEndomorphismEvalAt_hasEval hπ n x hx a
  let hxH : PowerSeries.HasEval xH :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n x hx H hHSubst
  calc
    standardLubinTateLevelPowerSeriesEval hπ n xS hxS H =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          (PowerSeries.subst S H) :=
      (standardLubinTateLevelPowerSeriesEval_subst
        hπ n x hx S H hSSubst hxS).symm
    _ =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          (PowerSeries.subst H M) := by
      rw [padicStandardToMultiplicativeIntertwiner_endomorphism]
    _ =
        standardLubinTateLevelPowerSeriesEval hπ n xH hxH M :=
      standardLubinTateLevelPowerSeriesEval_subst
        hπ n x hx H M hHSubst hxH

/-- Evaluating the reverse comparison after the forward comparison recovers
every topologically nilpotent standard-level point. -/
theorem padicMultiplicativeToStandardIntertwiner_eval_comp
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p))
        (standardLubinTateLevelPowerSeriesEval_hasEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p)
          (padicStandardToMultiplicativeIntertwiner_hasSubst p))
        (padicMultiplicativeToStandardIntertwiner p) =
      x := by
  let hπ :=
    padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let G := padicMultiplicativeToStandardIntertwiner p
  let hH : PowerSeries.HasSubst H :=
    padicStandardToMultiplicativeIntertwiner_hasSubst p
  let hHEval :
      PowerSeries.HasEval
        (standardLubinTateLevelPowerSeriesEval hπ n x hx H) :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n x hx H hH
  calc
    standardLubinTateLevelPowerSeriesEval hπ n
        (standardLubinTateLevelPowerSeriesEval hπ n x hx H)
        hHEval G =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          (PowerSeries.subst H G) :=
      (standardLubinTateLevelPowerSeriesEval_subst
        hπ n x hx H G hH hHEval).symm
    _ =
        standardLubinTateLevelPowerSeriesEval hπ n x hx
          PowerSeries.X := by
      rw [padicMultiplicativeToStandardIntertwiner_subst_reverse]
    _ = x :=
      standardLubinTateLevelPowerSeriesEval_X
        hπ n x hx

/-- The forward comparison evaluates to zero at the zero point. -/
theorem padicStandardToMultiplicativeIntertwiner_eval_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    standardLubinTateLevelPowerSeriesEval
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        0 PowerSeries.HasEval.zero
        (padicStandardToMultiplicativeIntertwiner p) =
      0 := by
  obtain ⟨B, hB⟩ :
      (PowerSeries.X :
          PowerSeries (padicLocalField p).valuationSubring) ∣
        padicStandardToMultiplicativeIntertwiner p := by
    rw [PowerSeries.X_dvd_iff]
    exact
      (padicStandardToMultiplicativeIntertwiner_hasLinearTerm p
        ).constantCoeff_eq_zero
  rw [hB, map_mul]
  exact
    (congrArg
      (fun z : (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring =>
          z * standardLubinTateLevelPowerSeriesEval
            (padicMultiplicativeLubinTateSeries_isUniformizer p) n
            0 PowerSeries.HasEval.zero B)
      (standardLubinTateLevelPowerSeriesEval_X
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
        0 PowerSeries.HasEval.zero)).trans (zero_mul _)

/-- Evaluation of the forward comparison is injective on topologically
nilpotent points of every standard level. -/
theorem padicStandardToMultiplicativeIntertwiner_eval_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    {x y :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy :
      standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n x hx
          (padicStandardToMultiplicativeIntertwiner p) =
        standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n y hy
          (padicStandardToMultiplicativeIntertwiner p)) :
    x = y := by
  let hπ :=
    padicMultiplicativeLubinTateSeries_isUniformizer p
  let H := padicStandardToMultiplicativeIntertwiner p
  let G := padicMultiplicativeToStandardIntertwiner p
  let hxH :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n x hx H
        (padicStandardToMultiplicativeIntertwiner_hasSubst p)
  let hyH :=
    standardLubinTateLevelPowerSeriesEval_hasEval
      hπ n y hy H
        (padicStandardToMultiplicativeIntertwiner_hasSubst p)
  let evalReverse :
      {z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
        PowerSeries.HasEval z} →
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
    fun z =>
      standardLubinTateLevelPowerSeriesEval hπ n z.1 z.2 G
  let forwardX :=
    standardLubinTateLevelPowerSeriesEval hπ n x hx H
  let forwardY :=
    standardLubinTateLevelPowerSeriesEval hπ n y hy H
  let packedX :
      {z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
        PowerSeries.HasEval z} :=
    ⟨forwardX, hxH⟩
  let packedY :
      {z :
          (standardLubinTateLevelCompleteDVF hπ n).valuationSubring //
        PowerSeries.HasEval z} :=
    ⟨forwardY, hyH⟩
  have hpacked : packedX = packedY := by
    apply Subtype.ext
    exact hxy
  have hxback : evalReverse packedX = x :=
    padicMultiplicativeToStandardIntertwiner_eval_comp p n x hx
  have hyback : evalReverse packedY = y :=
    padicMultiplicativeToStandardIntertwiner_eval_comp p n y hy
  exact hxback.symm.trans ((congrArg evalReverse hpacked).trans hyback)

end PadicLevelTopology

end LubinTate

end
