/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
/-!
# Analytic evaluation in standard Lubin--Tate level fields

The scalar endomorphisms of a Lubin--Tate formal module are genuine infinite
power series.  This file evaluates them in the complete valuation ring of a
standard finite level.

The coefficient map is the canonical map of valuation rings attached to the
valued extension.  The target carries its maximal-ideal adic topology.  The
chosen primitive division point is a uniformizer, hence is topologically
nilpotent and is therefore a valid evaluation point.
-/

@[expose] public section

noncomputable
section

open Filter
open scoped PowerSeries
open scoped PowerSeries.WithPiTopology

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open SameUniformizer

variable {K : Type u} [Field K]

private noncomputable local instance (priority := 50)
    standardLubinTateLevelCoefficientUniformSpace
    (F : LocalField.{u, v} K) :
    UniformSpace F.valuationSubring :=
  ⊥

private noncomputable local instance
    standardLubinTateLevelTargetWithIdeal
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring where
  i := (standardLubinTateLevelCompleteDVF hπ n).maximalIdeal

private noncomputable local instance
    standardLubinTateLevelTargetCompleteSpace
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

private noncomputable local instance
    standardLubinTateLevelTargetT2Space
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring := by
  let target := standardLubinTateLevelCompleteDVF hπ n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

/-- The canonical coefficient map from the base valuation ring to the
valuation ring of a standard Lubin--Tate level. -/
noncomputable def standardLubinTateLevelCoefficientHom
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    F.valuationSubring →+*
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  integerMap F.toCompleteDVF.toDVF
    (standardLubinTateLevelCompleteDVF hπ n).toDVF

/-- The level coefficient map is the ambient field algebra map after
coercion from the two valuation rings. -/
@[simp]
theorem standardLubinTateLevelCoefficientHom_apply
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : F.valuationSubring) :
    ((standardLubinTateLevelCoefficientHom hπ n a :
        (standardLubinTateLevelCompleteDVF hπ n).valuationSubring) :
      standardLubinTateLevelField hπ n) =
        algebraMap K (standardLubinTateLevelField hπ n) (a : K) := by
  exact integerMap_apply F.toCompleteDVF.toDVF
    (standardLubinTateLevelCompleteDVF hπ n).toDVF a

/-- The primitive point is topologically nilpotent for the maximal-ideal
adic topology of the level valuation ring. -/
theorem standardLubinTatePrimitivePointInteger_hasEval
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    PowerSeries.HasEval
      (standardLubinTatePrimitivePointInteger hπ n) := by
  apply WithIdeal.isTopologicallyNilpotent_of_mem
  exact
    (standardLubinTateLevelCompleteDVF hπ n).uniformizer_mem_maximalIdeal
      (standardLubinTatePrimitivePoint_isUniformizer hπ n)

/-- Analytic evaluation of power series at a topologically nilpotent
integer of a standard Lubin--Tate level. -/
noncomputable def standardLubinTateLevelPowerSeriesEval
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    F.valuationSubring⟦X⟧ →+*
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  PowerSeries.eval₂Hom
    (φ := standardLubinTateLevelCoefficientHom hπ n)
    continuous_of_discreteTopology hx

/-- Evaluation sends the power-series variable to the chosen point. -/
@[simp]
theorem standardLubinTateLevelPowerSeriesEval_X
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateLevelPowerSeriesEval hπ n x hx PowerSeries.X = x := by
  rw [standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

/-- Evaluation sends a constant power series through the canonical
coefficient map. -/
@[simp]
theorem standardLubinTateLevelPowerSeriesEval_C
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (a : F.valuationSubring) :
    standardLubinTateLevelPowerSeriesEval hπ n x hx
        (PowerSeries.C a) =
      standardLubinTateLevelCoefficientHom hπ n a := by
  rw [standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]

/-- On polynomial power series, analytic evaluation agrees with ordinary
polynomial evaluation. -/
@[simp]
theorem standardLubinTateLevelPowerSeriesEval_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (P : Polynomial F.valuationSubring) :
    standardLubinTateLevelPowerSeriesEval hπ n x hx
        (P : PowerSeries F.valuationSubring) =
      Polynomial.eval₂
        (standardLubinTateLevelCoefficientHom hπ n) x P := by
  rw [standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_coe]

/-- Evaluation at a topologically nilpotent level integer is continuous. -/
theorem standardLubinTateLevelPowerSeriesEval_continuous
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    Continuous
      (standardLubinTateLevelPowerSeriesEval hπ n x hx) := by
  rw [standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom]
  exact PowerSeries.continuous_eval₂
    (φ := standardLubinTateLevelCoefficientHom hπ n)
    continuous_of_discreteTopology hx

/-- Evaluating a series with zero constant coefficient produces another
topologically nilpotent level integer. -/
theorem standardLubinTateLevelPowerSeriesEval_hasEval
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (f : PowerSeries F.valuationSubring)
    (hf : PowerSeries.HasSubst f) :
    PowerSeries.HasEval
      (standardLubinTateLevelPowerSeriesEval hπ n x hx f) := by
  exact hf.hasEval.map
    (standardLubinTateLevelPowerSeriesEval_continuous hπ n x hx)

/-- Analytic evaluation commutes with one-variable formal substitution. -/
theorem standardLubinTateLevelPowerSeriesEval_subst
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (a f : PowerSeries F.valuationSubring)
    (ha : PowerSeries.HasSubst a)
    (haEval : PowerSeries.HasEval
      (standardLubinTateLevelPowerSeriesEval hπ n x hx a)) :
    standardLubinTateLevelPowerSeriesEval hπ n x hx
        (PowerSeries.subst a f) =
      standardLubinTateLevelPowerSeriesEval hπ n
        (standardLubinTateLevelPowerSeriesEval hπ n x hx a)
        haEval f := by
  let R := F.valuationSubring
  let S :=
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring
  simp only [standardLubinTateLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom]
  change PowerSeries.eval₂ (algebraMap R S) x
      (PowerSeries.subst a f) =
    PowerSeries.eval₂ (algebraMap R S)
      (PowerSeries.eval₂ (algebraMap R S) x a) f
  simpa only [PowerSeries.eval₂, PowerSeries.subst,
    Function.const_apply] using
      (MvPowerSeries.eval₂_subst
        (R := R) (S := R) (T := S)
        (a := fun _ : Unit ↦ a) ha.const
        (PowerSeries.hasEval hx) f)

/-- The canonical evaluation homomorphism at the primitive point. -/
noncomputable def standardLubinTatePrimitivePointEvaluation
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    F.valuationSubring⟦X⟧ →+*
      (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  standardLubinTateLevelPowerSeriesEval hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n)

/-- The value of the standard scalar endomorphism `[a]` at an arbitrary
topologically nilpotent integer of a finite level. -/
noncomputable def standardLubinTateEndomorphismEvalAt
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (a : F.valuationSubring) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  standardLubinTateLevelPowerSeriesEval hπ n x hx
    (standardLubinTateEndomorphism hπ a)

/-- Every evaluated scalar endomorphism remains topologically nilpotent. -/
theorem standardLubinTateEndomorphismEvalAt_hasEval
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (a : F.valuationSubring) :
    PowerSeries.HasEval
      (standardLubinTateEndomorphismEvalAt hπ n x hx a) := by
  exact standardLubinTateLevelPowerSeriesEval_hasEval hπ n x hx
    (standardLubinTateEndomorphism hπ a)
    (standardLubinTateEndomorphism_hasLinearTerm hπ a).hasSubst

/-- The value `[a](lambda_(n+1))` at the chosen primitive division point. -/
noncomputable def standardLubinTateEndomorphismValue
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : F.valuationSubring) :
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring :=
  standardLubinTateEndomorphismEvalAt hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n) a

/-- Every scalar value at the primitive point is again topologically
nilpotent. -/
theorem standardLubinTateEndomorphismValue_hasEval
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a : F.valuationSubring) :
    PowerSeries.HasEval
      (standardLubinTateEndomorphismValue hπ n a) :=
  standardLubinTateEndomorphismEvalAt_hasEval hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n) a

/-- The value of `[1]` is the evaluation point. -/
@[simp]
theorem standardLubinTateEndomorphismEvalAt_one
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateEndomorphismEvalAt hπ n x hx 1 = x := by
  rw [standardLubinTateEndomorphismEvalAt,
    standardLubinTateEndomorphism_one,
    standardLubinTateLevelPowerSeriesEval_X]

/-- The value of `[0]` is zero. -/
@[simp]
theorem standardLubinTateEndomorphismEvalAt_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) :
    standardLubinTateEndomorphismEvalAt hπ n x hx 0 = 0 := by
  rw [standardLubinTateEndomorphismEvalAt,
    standardLubinTateEndomorphism_zero, map_zero]

/-- Multiplication of scalars becomes composition after analytic
evaluation. -/
theorem standardLubinTateEndomorphismEvalAt_mul
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ)
    (x : (standardLubinTateLevelCompleteDVF hπ n).valuationSubring)
    (hx : PowerSeries.HasEval x) (a b : F.valuationSubring) :
    standardLubinTateEndomorphismEvalAt hπ n x hx (a * b) =
      standardLubinTateEndomorphismEvalAt hπ n
        (standardLubinTateEndomorphismEvalAt hπ n x hx b)
        (standardLubinTateEndomorphismEvalAt_hasEval hπ n x hx b) a := by
  rw [standardLubinTateEndomorphismEvalAt,
    standardLubinTateEndomorphism_mul]
  exact standardLubinTateLevelPowerSeriesEval_subst hπ n x hx
    (standardLubinTateEndomorphism hπ b)
    (standardLubinTateEndomorphism hπ a)
    (standardLubinTateEndomorphism_hasLinearTerm hπ b).hasSubst
    (standardLubinTateEndomorphismEvalAt_hasEval hπ n x hx b)

/-- At the primitive point, multiplication of scalars is analytic
composition of their values. -/
theorem standardLubinTateEndomorphismValue_mul
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n : ℕ) (a b : F.valuationSubring) :
    standardLubinTateEndomorphismValue hπ n (a * b) =
      standardLubinTateEndomorphismEvalAt hπ n
        (standardLubinTateEndomorphismValue hπ n b)
        (standardLubinTateEndomorphismValue_hasEval hπ n b) a :=
  standardLubinTateEndomorphismEvalAt_mul hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n) a b

/-- The primitive-point value of `[1]` is the primitive point itself. -/
@[simp]
theorem standardLubinTateEndomorphismValue_one
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTateEndomorphismValue hπ n 1 =
      standardLubinTatePrimitivePointInteger hπ n :=
  standardLubinTateEndomorphismEvalAt_one hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n)

/-- The primitive-point value of `[0]` is zero. -/
@[simp]
theorem standardLubinTateEndomorphismValue_zero
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) :
    standardLubinTateEndomorphismValue hπ n 0 = 0 :=
  standardLubinTateEndomorphismEvalAt_zero hπ n
    (standardLubinTatePrimitivePointInteger hπ n)
    (standardLubinTatePrimitivePointInteger_hasEval hπ n)

end LubinTate

end
