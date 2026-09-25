/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveIrreducible
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.Core
public import Mathlib.SetTheory.Cardinal.Finite
/-!
# Primitive unit action on a completed p-adic Lubin--Tate level

The completed level is defined as the splitting field of the standard
primitive Lubin--Tate polynomial over the completed maximal-unramified
field.  This file identifies all of its roots with the genuine finite
unit-parameter quotient of the original p-adic field.

The construction first embeds the ordinary standard Lubin--Tate level into
the completed splitting field by sending its canonical primitive generator
to the chosen completed root.  The already constructed finite-level
unit-parameter automorphisms then give every completed root.  Comparing
cardinalities proves that these are all the roots, and hence that each one
generates the completed splitting field.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

private noncomputable local instance
    padicCompletedActionTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

private noncomputable local instance
    padicCompletedActionTargetCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

private noncomputable local instance
    padicCompletedActionTargetT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

/-- The chosen completed primitive root annihilates the original standard
primitive polynomial over `ℚ_[p]`. -/
theorem padicCompletedPrimitiveRoot_aeval_standardPrimitivePolynomial
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Polynomial.aeval (padicCompletedPrimitiveRoot p n)
        (standardLubinTatePrimitivePolynomialOverField
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) =
      0 := by
  have hroot := padicCompletedPrimitiveRoot_isRoot p n
  simpa [Polynomial.IsRoot, padicCompletedPrimitivePolynomial,
    standardLubinTatePrimitivePolynomialOverField,
    Polynomial.aeval_def, Polynomial.eval_map, Polynomial.eval₂_map,
    IsScalarTower.algebraMap_eq ℚ_[p]
      (padicCompletedUnramifiedField p) (padicCompletedLevelField p n),
    padicCompletedLevelPadicFieldCoefficientHom] using hroot

/-- The ordinary standard Lubin--Tate level embeds into the completed
splitting field by sending its canonical generator to the chosen completed
root. -/
noncomputable def padicStandardLevelEmbedding
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ :=
      padicMultiplicativeLubinTateSeries_isUniformizer p
    standardLubinTateLevelField hπ n →ₐ[ℚ_[p]]
      padicCompletedLevelField p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  exact
    (standardLubinTateLevelPowerBasis hπ n).lift
      (padicCompletedPrimitiveRoot p n) (by
        exact (congrArg
          (fun f : Polynomial ℚ_[p] =>
            Polynomial.aeval (padicCompletedPrimitiveRoot p n) f)
          (standardLubinTateLevelPowerBasis_minpoly
            (F := padicLocalField p)
            (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n)).trans
          (padicCompletedPrimitiveRoot_aeval_standardPrimitivePolynomial p n))

/-- The standard-level embedding has the prescribed value on the canonical
primitive generator. -/
@[simp]
theorem padicStandardLevelEmbedding_apply_gen
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ :=
      padicMultiplicativeLubinTateSeries_isUniformizer p
    padicStandardLevelEmbedding p n
        (standardLubinTateLevelPowerBasis hπ n).gen =
      padicCompletedPrimitiveRoot p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  simp only [padicStandardLevelEmbedding, PowerBasis.lift_gen]

/-- A finite unit parameter, realized as a root in the completed splitting
field. -/
noncomputable def padicCompletedUnitParameterRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    padicCompletedLevelField p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  exact
    padicStandardLevelEmbedding p n
      (standardLubinTateUnitParameterLevelRoot
        (padicLocalField p) hπ n a)

/-- The identity unit parameter gives the chosen completed primitive root. -/
@[simp]
theorem padicCompletedUnitParameterRoot_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedUnitParameterRoot p n 1 =
      padicCompletedPrimitiveRoot p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  exact (congrArg (padicStandardLevelEmbedding p n)
    (standardLubinTateUnitParameterLevelRoot_one (padicLocalField p)
      (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n)).trans
    (padicStandardLevelEmbedding_apply_gen p n)

/-- Distinct finite unit parameters give distinct roots in the completed
level. -/
theorem padicCompletedUnitParameterRoot_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Function.Injective (padicCompletedUnitParameterRoot p n) := by
  intro a b hab
  apply
    standardLubinTateUnitParameterLevelRoot_injective
      (padicLocalField p)
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
  exact (padicStandardLevelEmbedding p n).injective hab

/-- A completed parameter root annihilates the original primitive
polynomial over `ℚ_[p]`. -/
theorem padicCompletedUnitParameterRoot_aeval_standardPrimitivePolynomial
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    Polynomial.aeval (padicCompletedUnitParameterRoot p n a)
        (standardLubinTatePrimitivePolynomialOverField
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) =
      0 := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  have hlevel :=
    standardLubinTateUnitParameterLevelRoot_aeval_minpoly
      (padicLocalField p) hπ n a
  have hpoly := congrArg
    (fun f : Polynomial ℚ_[p] => Polynomial.aeval
      (standardLubinTateUnitParameterLevelRoot (padicLocalField p) hπ n a) f)
    (standardLubinTateLevelPowerBasis_minpoly
      (F := padicLocalField p)
      (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n)
  have hmap := congrArg (padicStandardLevelEmbedding p n) (hpoly.symm.trans hlevel)
  simpa only [map_zero, Polynomial.aeval_algHom_apply,
    padicCompletedUnitParameterRoot] using hmap

/-- Every completed finite-parameter point is a root of the genuine
completed primitive polynomial. -/
theorem padicCompletedUnitParameterRoot_isRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    ((padicCompletedPrimitivePolynomial p n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))).IsRoot
      (padicCompletedUnitParameterRoot p n a) := by
  have hroot :=
    padicCompletedUnitParameterRoot_aeval_standardPrimitivePolynomial
      p n a
  simpa [Polynomial.IsRoot, padicCompletedPrimitivePolynomial,
    standardLubinTatePrimitivePolynomialOverField,
    Polynomial.aeval_def, Polynomial.eval_map, Polynomial.eval₂_map,
    IsScalarTower.algebraMap_eq ℚ_[p]
      (padicCompletedUnramifiedField p) (padicCompletedLevelField p n),
    padicCompletedLevelPadicFieldCoefficientHom] using hroot

private theorem
    padicCompletedStandardScalarEndomorphismValue_congr_point
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    {x y : (padicCompletedLevelCompleteDVF p n).valuationSubring}
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : x = y) (a : (padicLocalField p).valuationSubring) :
    padicCompletedStandardScalarEndomorphismValue p n x hx a =
      padicCompletedStandardScalarEndomorphismValue p n y hy a := by
  subst y
  rfl

/-- The direct completed standard Lubin--Tate action of a p-adic unit on
the chosen integral primitive point. -/
noncomputable def padicCompletedStandardPrimitivePointUnitAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    (padicCompletedLevelCompleteDVF p n).valuationSubring :=
  padicCompletedStandardScalarEndomorphismValue p n
    (padicCompletedPrimitiveRootInteger p n)
    (padicCompletedPrimitiveRootInteger_hasEval p n)
    (u : (padicLocalField p).valuationSubring)

/-- A direct completed standard unit translate remains a convergent
evaluation point. -/
theorem padicCompletedStandardPrimitivePointUnitAction_hasEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    PowerSeries.HasEval
      (padicCompletedStandardPrimitivePointUnitAction p n u) :=
  padicCompletedStandardScalarEndomorphismValue_hasEval p n
    (padicCompletedPrimitiveRootInteger p n)
    (padicCompletedPrimitiveRootInteger_hasEval p n)
    (u : (padicLocalField p).valuationSubring)

/-- The identity unit fixes the chosen completed standard primitive point. -/
@[simp]
theorem padicCompletedStandardPrimitivePointUnitAction_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCompletedStandardPrimitivePointUnitAction p n 1 =
      padicCompletedPrimitiveRootInteger p n := by
  simp [padicCompletedStandardPrimitivePointUnitAction]

/-- A direct completed standard unit translate is killed at level
`n + 1`. -/
theorem
    padicCompletedStandardPrimitivePointUnitAction_iterate_succ_eq_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicCompletedStandardPrimitivePointUnitAction p n u)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) (n + 1)) =
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let x := padicCompletedPrimitiveRootInteger p n
  let hx := padicCompletedPrimitiveRootInteger_hasEval p n
  let y := padicCompletedStandardPrimitivePointUnitAction p n u
  let hy := padicCompletedStandardPrimitivePointUnitAction_hasEval p n u
  have hkill :
      padicCompletedStandardScalarEndomorphismValue p n x hx
          (π ^ (n + 1)) =
        0 := by
    exact
      (padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
        p n x hx (n + 1)).trans (by
          simpa only [x] using
            padicCompletedPrimitiveRootInteger_iterate_succ_eq_zero p n)
  rw [← padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
    p n y hy (n + 1)]
  calc
    padicCompletedStandardScalarEndomorphismValue p n y hy
        (π ^ (n + 1)) =
      padicCompletedStandardScalarEndomorphismValue p n x hx
        (π ^ (n + 1) *
          (u : (padicLocalField p).valuationSubring)) := by
      simpa only [y,
        padicCompletedStandardPrimitivePointUnitAction] using
        (padicCompletedStandardScalarEndomorphismValue_mul
          p n x hx (π ^ (n + 1))
            (u : (padicLocalField p).valuationSubring)).symm
    _ =
      padicCompletedStandardScalarEndomorphismValue p n x hx
        ((u : (padicLocalField p).valuationSubring) *
          π ^ (n + 1)) := by
      rw [mul_comm]
    _ =
      padicCompletedStandardScalarEndomorphismValue p n
        (padicCompletedStandardScalarEndomorphismValue p n x hx
          (π ^ (n + 1)))
        (padicCompletedStandardScalarEndomorphismValue_hasEval
          p n x hx (π ^ (n + 1)))
        (u : (padicLocalField p).valuationSubring) :=
      padicCompletedStandardScalarEndomorphismValue_mul
        p n x hx (u : (padicLocalField p).valuationSubring)
          (π ^ (n + 1))
    _ =
      padicCompletedStandardScalarEndomorphismValue p n
        0 PowerSeries.HasEval.zero
        (u : (padicLocalField p).valuationSubring) := by
      exact
        padicCompletedStandardScalarEndomorphismValue_congr_point
          p n
          (padicCompletedStandardScalarEndomorphismValue_hasEval
            p n x hx (π ^ (n + 1)))
          PowerSeries.HasEval.zero hkill
          (u : (padicLocalField p).valuationSubring)
    _ = 0 :=
      padicCompletedStandardScalarEndomorphismValue_zero p n
        (u : (padicLocalField p).valuationSubring)

/-- A direct completed standard unit translate is not killed one level
early. -/
theorem
    padicCompletedStandardPrimitivePointUnitAction_iterate_ne_zero
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n)
        (padicCompletedStandardPrimitivePointUnitAction p n u)
        (standardLubinTatePolynomialIterate
          (padicLocalField p)
          (padicIntEquivValuationSubring p (p : ℤ_[p])) n) ≠
      0 := by
  let π : (padicLocalField p).valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let x := padicCompletedPrimitiveRootInteger p n
  let hx := padicCompletedPrimitiveRootInteger_hasEval p n
  let y := padicCompletedStandardPrimitivePointUnitAction p n u
  let hy := padicCompletedStandardPrimitivePointUnitAction_hasEval p n u
  intro hyzero
  have hyEvalZero :
      padicCompletedStandardScalarEndomorphismValue p n y hy (π ^ n) =
        0 := by
    exact
      (padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
        p n y hy n).trans (by
          simpa only [y] using hyzero)
  let z :=
    padicCompletedStandardScalarEndomorphismValue p n x hx (π ^ n)
  let hz : PowerSeries.HasEval z :=
    padicCompletedStandardScalarEndomorphismValue_hasEval
      p n x hx (π ^ n)
  have huzero :
      padicCompletedStandardScalarEndomorphismValue p n z hz
          (u : (padicLocalField p).valuationSubring) =
        0 := by
    calc
      _ =
          padicCompletedStandardScalarEndomorphismValue p n x hx
            ((u : (padicLocalField p).valuationSubring) * π ^ n) := by
        simpa only [z] using
          (padicCompletedStandardScalarEndomorphismValue_mul
            p n x hx (u : (padicLocalField p).valuationSubring)
              (π ^ n)).symm
      _ =
          padicCompletedStandardScalarEndomorphismValue p n x hx
            (π ^ n * (u : (padicLocalField p).valuationSubring)) := by
        rw [mul_comm]
      _ =
          padicCompletedStandardScalarEndomorphismValue p n y hy
            (π ^ n) := by
        simpa only [y,
          padicCompletedStandardPrimitivePointUnitAction] using
          padicCompletedStandardScalarEndomorphismValue_mul
            p n x hx (π ^ n)
              (u : (padicLocalField p).valuationSubring)
      _ = 0 := hyEvalZero
  have hzzero : z = 0 := by
    apply
      padicCompletedStandardScalarEndomorphismValue_unit_injective
        p n u hz PowerSeries.HasEval.zero
    rw [huzero,
      padicCompletedStandardScalarEndomorphismValue_zero]
  apply padicCompletedPrimitiveRootInteger_iterate_ne_zero p n
  rw [← padicCompletedStandardScalarEndomorphismValue_uniformizer_pow
    p n x hx n]
  exact hzzero

/-- The direct completed standard action of every p-adic unit is a root of
the genuine completed primitive polynomial. -/
theorem padicCompletedStandardPrimitivePointUnitAction_isRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    ((padicCompletedPrimitivePolynomial p n).map
      (algebraMap (padicCompletedUnramifiedField p)
        (padicCompletedLevelField p n))).IsRoot
      ((padicCompletedStandardPrimitivePointUnitAction p n u :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
        padicCompletedLevelField p n) := by
  let F := padicLocalField p
  let π : F.valuationSubring :=
    padicIntEquivValuationSubring p (p : ℤ_[p])
  let y := padicCompletedStandardPrimitivePointUnitAction p n u
  have hsucc :=
    padicCompletedStandardPrimitivePointUnitAction_iterate_succ_eq_zero
      p n u
  have hn :=
    padicCompletedStandardPrimitivePointUnitAction_iterate_ne_zero
      p n u
  have hfactor :=
    congrArg
      (Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) y)
      (standardLubinTatePolynomialIterate_succ_factor F π n)
  rw [hsucc, Polynomial.eval₂_mul] at hfactor
  have hprimitive :
      Polynomial.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n) y
          (standardLubinTatePrimitivePolynomial F π n) =
        0 :=
    (mul_eq_zero.mp hfactor.symm).resolve_left hn
  have hcoe := congrArg
    (fun z : (padicCompletedLevelCompleteDVF p n).valuationSubring =>
      (z : padicCompletedLevelField p n)) hprimitive
  change
    ((Polynomial.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) y
        (standardLubinTatePrimitivePolynomial F π n) :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        0 at hcoe
  rw [padicCompletedLevelPadicIntegerPolynomialEval_coe] at hcoe
  simpa [Polynomial.IsRoot, padicCompletedPrimitivePolynomial,
    standardLubinTatePrimitivePolynomialOverField,
    Polynomial.eval_map, Polynomial.eval₂_map,
    padicCompletedLevelPadicFieldCoefficientHom, F, π, y] using hcoe

/-- A finite unit parameter, regarded as an element of the full root set in
the completed splitting field. -/
noncomputable def padicCompletedUnitParameterRootSet
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    (padicCompletedPrimitivePolynomial p n).rootSet
      (padicCompletedLevelField p n) :=
  ⟨padicCompletedUnitParameterRoot p n a,
    Polynomial.mem_rootSet.mpr
      ⟨(padicCompletedPrimitivePolynomial_monic p n).ne_zero,
        by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]
          exact padicCompletedUnitParameterRoot_isRoot p n a⟩⟩

/-- The root-set realization of finite unit parameters is injective. -/
theorem padicCompletedUnitParameterRootSet_injective
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Function.Injective (padicCompletedUnitParameterRootSet p n) := by
  intro a b hab
  apply padicCompletedUnitParameterRoot_injective p n
  exact congrArg Subtype.val hab

/-- The completed primitive polynomial has exactly its degree many roots in
the completed splitting field. -/
theorem padicCompletedPrimitiveRootSet_natCard
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Nat.card
        ((padicCompletedPrimitivePolynomial p n).rootSet
          (padicCompletedLevelField p n)) =
      (p - 1) * p ^ n := by
  rw [Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree
      (padicCompletedPrimitivePolynomial_separable p n)
      (padicCompletedPrimitivePolynomial_splits p n),
    padicCompletedPrimitivePolynomial_natDegree]

/-- The finite p-adic unit-parameter quotient has the degree of the
completed primitive polynomial. -/
theorem padicStandardUnitParameter_natCard
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Nat.card (standardLubinTateUnitParameter (padicLocalField p) n) =
      (p - 1) * p ^ n := by
  have hcard :
      Nat.card (padicLocalField p).residueField = p := by
    simpa [padicLocalField] using
      padicCompleteDVF_residueField_card p
  rw [standardLubinTateUnitParameter_natCard, hcard]

/-- Finite p-adic unit parameters enumerate every root of the completed
primitive polynomial. -/
theorem padicCompletedUnitParameterRootSet_bijective
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Function.Bijective (padicCompletedUnitParameterRootSet p n) := by
  apply
    (Nat.bijective_iff_injective_and_card
      (padicCompletedUnitParameterRootSet p n)).mpr
  exact
    ⟨padicCompletedUnitParameterRootSet_injective p n,
      (padicStandardUnitParameter_natCard p n).trans
        (padicCompletedPrimitiveRootSet_natCard p n).symm⟩

/-- A parameter root is itself a power-basis generator of the ordinary
standard level. -/
noncomputable def padicStandardLevelUnitParameterPowerBasis
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    let hπ :=
      padicMultiplicativeLubinTateSeries_isUniformizer p
    PowerBasis ℚ_[p] (standardLubinTateLevelField hπ n) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  exact
    (standardLubinTateLevelPowerBasis hπ n).map
      (standardLubinTateUnitParameterAlgEquiv
        (padicLocalField p) hπ n a)

/-- The generator of the parameter power basis is the corresponding
finite-level parameter root. -/
@[simp]
theorem padicStandardLevelUnitParameterPowerBasis_gen
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    let hπ :=
      padicMultiplicativeLubinTateSeries_isUniformizer p
    (padicStandardLevelUnitParameterPowerBasis p n a).gen =
      standardLubinTateUnitParameterLevelRoot
        (padicLocalField p) hπ n a := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  simp only [padicStandardLevelUnitParameterPowerBasis,
    PowerBasis.map_gen]
  exact standardLubinTateUnitParameterAlgEquiv_apply_gen
    (padicLocalField p)
    (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n a

private theorem padicPolynomialAeval_mem_completedUnramifiedAdjoin
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : padicCompletedLevelField p n) (f : Polynomial ℚ_[p]) :
    Polynomial.aeval x f ∈
      Algebra.adjoin (padicCompletedUnramifiedField p)
        ({x} : Set (padicCompletedLevelField p n)) := by
  let g :=
    f.map (algebraMap ℚ_[p] (padicCompletedUnramifiedField p))
  have hmem :=
    g.aeval_mem_adjoin_singleton (padicCompletedUnramifiedField p) x
  simpa only [Polynomial.aeval_def, Polynomial.eval₂_map,
    IsScalarTower.algebraMap_eq ℚ_[p]
      (padicCompletedUnramifiedField p) (padicCompletedLevelField p n),
    g]
    using hmem

/-- Every completed parameter root is a polynomial expression in any other
completed parameter root, with coefficients in the completed-unramified
base. -/
theorem padicCompletedUnitParameterRoot_mem_adjoin
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a b : standardLubinTateUnitParameter (padicLocalField p) n) :
    padicCompletedUnitParameterRoot p n b ∈
      Algebra.adjoin (padicCompletedUnramifiedField p)
        ({padicCompletedUnitParameterRoot p n a} :
          Set (padicCompletedLevelField p n)) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let pb := padicStandardLevelUnitParameterPowerBasis p n a
  let z :=
    standardLubinTateUnitParameterLevelRoot
      (padicLocalField p) hπ n b
  let S : Subalgebra (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
    Algebra.adjoin (padicCompletedUnramifiedField p)
      ({padicCompletedUnitParameterRoot p n a} :
        Set (padicCompletedLevelField p n))
  obtain ⟨f, hf⟩ := pb.exists_eq_aeval' z
  have hgen :
      padicStandardLevelEmbedding p n pb.gen =
        padicCompletedUnitParameterRoot p n a := by
    rw [padicStandardLevelUnitParameterPowerBasis_gen]
    rfl
  have hzimage :
      padicStandardLevelEmbedding p n z =
        Polynomial.aeval (padicCompletedUnitParameterRoot p n a) f := by
    calc
      padicStandardLevelEmbedding p n z =
          padicStandardLevelEmbedding p n
            (Polynomial.aeval pb.gen f) :=
        congrArg (padicStandardLevelEmbedding p n) hf
      _ = Polynomial.aeval
          (padicStandardLevelEmbedding p n pb.gen) f :=
        (Polynomial.aeval_algHom_apply
          (padicStandardLevelEmbedding p n) pb.gen f).symm
      _ = Polynomial.aeval
          (padicCompletedUnitParameterRoot p n a) f := by
        rw [hgen]
  change padicStandardLevelEmbedding p n z ∈ S
  rw [hzimage]
  exact
    padicPolynomialAeval_mem_completedUnramifiedAdjoin
      p n (padicCompletedUnitParameterRoot p n a) f

/-- All roots of the completed primitive polynomial lie in the field
generated by any chosen parameter root. -/
theorem padicCompletedPrimitiveRootSet_subset_adjoin_parameter
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    ((padicCompletedPrimitivePolynomial p n).rootSet
        (padicCompletedLevelField p n) :
      Set (padicCompletedLevelField p n)) ⊆
      Algebra.adjoin (padicCompletedUnramifiedField p)
        ({padicCompletedUnitParameterRoot p n a} :
          Set (padicCompletedLevelField p n)) := by
  intro y hy
  let yroot :
      (padicCompletedPrimitivePolynomial p n).rootSet
        (padicCompletedLevelField p n) :=
    ⟨y, hy⟩
  obtain ⟨b, hb⟩ :=
    (padicCompletedUnitParameterRootSet_bijective p n).surjective yroot
  have hby :
      padicCompletedUnitParameterRoot p n b = y :=
    congrArg Subtype.val hb
  rw [← hby]
  exact padicCompletedUnitParameterRoot_mem_adjoin p n a b

/-- Every completed parameter root generates the completed splitting field
over the completed maximal-unramified base. -/
theorem padicCompletedUnitParameterRoot_adjoin_eq_top
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    Algebra.adjoin (padicCompletedUnramifiedField p)
        ({padicCompletedUnitParameterRoot p n a} :
          Set (padicCompletedLevelField p n)) =
      ⊤ := by
  have hall :
      Algebra.adjoin (padicCompletedUnramifiedField p)
          ((padicCompletedPrimitivePolynomial p n).rootSet
            (padicCompletedLevelField p n) :
            Set (padicCompletedLevelField p n)) ≤
        Algebra.adjoin (padicCompletedUnramifiedField p)
          ({padicCompletedUnitParameterRoot p n a} :
            Set (padicCompletedLevelField p n)) :=
    Algebra.adjoin_le
      (padicCompletedPrimitiveRootSet_subset_adjoin_parameter p n a)
  rw [padicCompletedPrimitivePolynomial_adjoin_rootSet] at hall
  exact top_unique hall

/-- Every direct completed standard unit translate generates the completed
splitting field over the completed maximal-unramified base. -/
theorem
    padicCompletedStandardPrimitivePointUnitAction_adjoin_eq_top
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    Algebra.adjoin (padicCompletedUnramifiedField p)
        ({((padicCompletedStandardPrimitivePointUnitAction p n u :
              (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n)} :
          Set (padicCompletedLevelField p n)) =
      ⊤ := by
  let y : padicCompletedLevelField p n :=
    ((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n)
  let yroot :
      (padicCompletedPrimitivePolynomial p n).rootSet
        (padicCompletedLevelField p n) :=
    ⟨y, Polynomial.mem_rootSet.mpr
      ⟨(padicCompletedPrimitivePolynomial_monic p n).ne_zero,
        by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]
          exact
            padicCompletedStandardPrimitivePointUnitAction_isRoot
              p n u⟩⟩
  obtain ⟨a, ha⟩ :=
    (padicCompletedUnitParameterRootSet_bijective p n).surjective yroot
  have hay :
      padicCompletedUnitParameterRoot p n a = y :=
    congrArg Subtype.val ha
  change
    Algebra.adjoin (padicCompletedUnramifiedField p)
        ({y} : Set (padicCompletedLevelField p n)) =
      ⊤
  rw [← hay]
  exact padicCompletedUnitParameterRoot_adjoin_eq_top p n a

/-- The chosen completed primitive root generates the completed splitting
field. -/
theorem padicCompletedPrimitiveRoot_adjoin_eq_top
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra.adjoin (padicCompletedUnramifiedField p)
        ({padicCompletedPrimitiveRoot p n} :
          Set (padicCompletedLevelField p n)) =
      ⊤ := by
  simpa using
    (padicCompletedUnitParameterRoot_adjoin_eq_top p n
      (1 : standardLubinTateUnitParameter (padicLocalField p) n))

/-- The completed primitive polynomial is the minimal polynomial of the
chosen completed root. -/
theorem padicCompletedPrimitiveRoot_minpoly
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    minpoly (padicCompletedUnramifiedField p)
        (padicCompletedPrimitiveRoot p n) =
      padicCompletedPrimitivePolynomial p n := by
  have hroot :
      Polynomial.aeval (padicCompletedPrimitiveRoot p n)
          (padicCompletedPrimitivePolynomial p n) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact padicCompletedPrimitiveRoot_isRoot p n
  have hmin :=
    minpoly.eq_of_irreducible
      (padicCompletedPrimitivePolynomial_irreducible p n) hroot
  rw [(padicCompletedPrimitivePolynomial_monic p n).leadingCoeff,
    inv_one, Polynomial.C_1, mul_one] at hmin
  exact hmin.symm

/-- The chosen primitive root is integral over the completed-unramified
field. -/
theorem padicCompletedPrimitiveRoot_isIntegral_over_completedUnramified
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsIntegral (padicCompletedUnramifiedField p)
      (padicCompletedPrimitiveRoot p n) := by
  refine
    ⟨padicCompletedPrimitivePolynomial p n,
      padicCompletedPrimitivePolynomial_monic p n, ?_⟩
  have hroot := padicCompletedPrimitiveRoot_isRoot p n
  simpa [Polynomial.IsRoot, Polynomial.aeval_def,
    Polynomial.eval_map, Polynomial.eval₂_map] using hroot

/-- The power basis of the completed level generated by the chosen
primitive root. -/
noncomputable def padicCompletedPrimitivePowerBasis
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    PowerBasis (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  PowerBasis.ofAdjoinEqTop
    (padicCompletedPrimitiveRoot_isIntegral_over_completedUnramified p n)
    (padicCompletedPrimitiveRoot_adjoin_eq_top p n)

/-- The generator of the completed primitive power basis is the chosen
completed root. -/
@[simp]
theorem padicCompletedPrimitivePowerBasis_gen
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicCompletedPrimitivePowerBasis p n).gen =
      padicCompletedPrimitiveRoot p n :=
  PowerBasis.ofAdjoinEqTop_gen _ _

/-- Every parameter root is integral over the completed-unramified base. -/
theorem padicCompletedUnitParameterRoot_isIntegral
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    IsIntegral (padicCompletedUnramifiedField p)
      (padicCompletedUnitParameterRoot p n a) := by
  refine
    ⟨padicCompletedPrimitivePolynomial p n,
      padicCompletedPrimitivePolynomial_monic p n, ?_⟩
  have hroot := padicCompletedUnitParameterRoot_isRoot p n a
  simpa [Polynomial.IsRoot, Polynomial.aeval_def,
    Polynomial.eval_map, Polynomial.eval₂_map] using hroot

/-- The power basis of the completed level generated by a prescribed finite
unit parameter. -/
noncomputable def padicCompletedUnitParameterPowerBasis
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    PowerBasis (padicCompletedUnramifiedField p)
      (padicCompletedLevelField p n) :=
  PowerBasis.ofAdjoinEqTop
    (padicCompletedUnitParameterRoot_isIntegral p n a)
    (padicCompletedUnitParameterRoot_adjoin_eq_top p n a)

/-- The generator of a completed unit-parameter power basis is the
corresponding completed root. -/
@[simp]
theorem padicCompletedUnitParameterPowerBasis_gen
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (a : standardLubinTateUnitParameter (padicLocalField p) n) :
    (padicCompletedUnitParameterPowerBasis p n a).gen =
      padicCompletedUnitParameterRoot p n a :=
  PowerBasis.ofAdjoinEqTop_gen _ _

end LubinTate

end
