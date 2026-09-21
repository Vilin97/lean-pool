/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusLift
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
/-!
# Transporting a finite p-adic Lubin--Tate level to the completed level

The ordinary standard Lubin--Tate level embeds in the completed level by
sending its primitive generator to the chosen completed primitive point.
This file proves that the embedding also preserves the integral analytic
action.  In particular, the direct completed action of a p-adic unit is
the image of the finite action with the *same* unit-parameter class.

This fixes the parameter orientation before the completed Frobenius is
used in the changed-uniformizer norm argument.
-/

noncomputable section

open scoped PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField
open SameUniformizer

private noncomputable local instance
    padicStandardLevelTransportCoefficientUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicLocalField p).valuationSubring :=
  ⊥

private noncomputable local instance
    padicStandardLevelTransportCoefficientTopologicalSpace
    (p : ℕ) [Fact p.Prime] :
    TopologicalSpace (padicLocalField p).valuationSubring :=
  ⊥

private noncomputable local instance (priority := 50)
    padicStandardLevelTransportWittUniformSpace
    (p : ℕ) [Fact p.Prime] :
    UniformSpace (padicCompletedUnramifiedWittRing p) :=
  ⊥

private noncomputable local instance
    padicStandardLevelTransportSourceWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring where
  i :=
    (standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
    ).maximalIdeal

private noncomputable local instance
    padicStandardLevelTransportTargetWithIdeal
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    WithIdeal
      (padicCompletedLevelCompleteDVF p n).valuationSubring where
  i := (padicCompletedLevelCompleteDVF p n).maximalIdeal

private noncomputable local instance
    padicStandardLevelTransportSourceCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring := by
  let source :=
    standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
  have hadic : IsAdic source.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp source.isAdicComplete).1

private noncomputable local instance
    padicStandardLevelTransportSourceT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring := by
  let source :=
    standardLubinTateLevelCompleteDVF
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
  have hadic : IsAdic source.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp source.isAdicComplete).2

private noncomputable local instance
    padicStandardLevelTransportTargetCompleteSpace
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    CompleteSpace
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

private noncomputable local instance
    padicStandardLevelTransportTargetT2Space
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    T2Space
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let target := padicCompletedLevelCompleteDVF p n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2

/-- The standard finite-level embedding restricted to the actual valuation
rings. -/
noncomputable def padicStandardLevelIntegerEmbedding
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    (standardLubinTateLevelCompleteDVF hπ n).valuationSubring →+*
      (padicCompletedLevelCompleteDVF p n).valuationSubring := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let source := standardLubinTateLevelCompleteDVF hπ n
  let A := padicCompletedUnramifiedCompleteDVF p
  let E := padicCompletedLevelField p n
  let target := padicCompletedLevelCompleteDVF p n
  let ι : L →ₐ[ℚ_[p]] E := padicStandardLevelEmbedding p n
  letI : F.valuation.HasExtension source.valuation :=
    standardLubinTateLevelCompleteDVF_hasExtension
      (F := padicLocalField p)
      (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n
  letI : Algebra F.valuationSubring source.valuationSubring :=
    Valuation.HasExtension.instAlgebra_valuationSubring
      (padicLocalField p).valuation
      (standardLubinTateLevelCompleteDVF
        (F := padicLocalField p)
        (π := padicIntEquivValuationSubring p (p : ℤ_[p])) hπ n).valuation
  letI : IsScalarTower F.valuationSubring source.valuationSubring L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure
      source.valuationSubring F.valuationSubring L :=
    standardLubinTateLevelCompleteDVF_isIntegralClosure hπ n
  letI : IsScalarTower A.valuationSubring target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsIntegralClosure
      target.valuationSubring A.valuationSubring E :=
    padicCompletedLevelCompleteDVF_isIntegralClosure p n
  let f : source.valuationSubring →+* E :=
    ι.toRingHom.comp source.valuation.valuationSubring.subtype
  apply RingHom.codRestrict f target.valuation.valuationSubring
  intro x
  have hxIntegral :
      IsIntegral F.valuationSubring (x : L) :=
    (IsIntegralClosure.isIntegral_iff
      (A := source.valuationSubring)
      (R := F.valuationSubring)
      (B := L)).2 ⟨x, rfl⟩
  have hcomp :
      (algebraMap A.valuationSubring E).comp
          (padicCompletedUnramifiedIntegerMap p) =
        ι.toRingHom.comp (algebraMap F.valuationSubring L) := by
    ext a
    simp only [RingHom.comp_apply]
    change
      algebraMap (padicCompletedUnramifiedField p) E
          ((padicCompletedUnramifiedIntegerMap p a :
            A.valuationSubring) :
              padicCompletedUnramifiedField p) =
        ι (algebraMap ℚ_[p] L (a : ℚ_[p]))
    rw [padicCompletedUnramifiedIntegerMap_coe]
    calc
      algebraMap (padicCompletedUnramifiedField p) E
          (algebraMap ℚ_[p]
            (padicCompletedUnramifiedField p) (a : ℚ_[p])) =
          algebraMap ℚ_[p] E (a : ℚ_[p]) :=
        (IsScalarTower.algebraMap_apply ℚ_[p]
          (padicCompletedUnramifiedField p) E (a : ℚ_[p])).symm
      _ = ι (algebraMap ℚ_[p] L (a : ℚ_[p])) :=
        (ι.commutes (a : ℚ_[p])).symm
  have hxMappedIntegral :
      IsIntegral A.valuationSubring (ι (x : L)) :=
    IsIntegral.map_of_comp_eq
      (padicCompletedUnramifiedIntegerMap p)
      ι.toRingHom hcomp hxIntegral
  rcases
      (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring)
        (R := A.valuationSubring)
        (B := E)).1 hxMappedIntegral with
    ⟨z, hz⟩
  exact hz ▸ z.property

/-- Coercing the integral standard-level embedding to the completed field
recovers the field embedding. -/
@[simp]
theorem padicStandardLevelIntegerEmbedding_coe
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring) :
    ((padicStandardLevelIntegerEmbedding p n x :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        padicStandardLevelEmbedding p n
          (x :
            standardLubinTateLevelField
              (padicMultiplicativeLubinTateSeries_isUniformizer p) n) := by
  rfl

/-- The integral embedding sends the finite primitive point to the chosen
completed primitive point. -/
@[simp]
theorem padicStandardLevelIntegerEmbedding_apply_primitivePoint
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    padicStandardLevelIntegerEmbedding p n
        (standardLubinTatePrimitivePointInteger hπ n) =
      padicCompletedPrimitiveRootInteger p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  apply Subtype.ext
  rw [padicStandardLevelIntegerEmbedding_coe,
    padicCompletedPrimitiveRootInteger_coe]
  have hpoint := congrArg (padicStandardLevelEmbedding p n)
    (standardLubinTatePrimitivePointInteger_coe
      (F := padicLocalField p) hπ n)
  exact hpoint.trans (padicStandardLevelEmbedding_apply_gen p n)

/-- The integral standard-level embedding is continuous for the two
maximal-ideal adic topologies. -/
theorem padicStandardLevelIntegerEmbedding_continuous
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Continuous (padicStandardLevelIntegerEmbedding p n) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let source := standardLubinTateLevelCompleteDVF hπ n
  let target := padicCompletedLevelCompleteDVF p n
  let f : source.valuationSubring →+* target.valuationSubring :=
    padicStandardLevelIntegerEmbedding p n
  have hmap :
      Ideal.map f source.maximalIdeal ≤ target.maximalIdeal := by
    rw [source.maximalIdeal_eq_span_uniformizer
      (standardLubinTatePrimitivePoint_isUniformizer hπ n),
      Ideal.map_span, Set.image_singleton, Ideal.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    change
      padicStandardLevelIntegerEmbedding p n
          (standardLubinTatePrimitivePointInteger hπ n) ∈
        target.maximalIdeal
    rw [padicStandardLevelIntegerEmbedding_apply_primitivePoint]
    exact padicCompletedPrimitiveRootInteger_mem_maximalIdeal p n
  exact
    (WithIdeal.uniformContinuous_of_map_le (f := f) hmap).continuous

/-- The integral embedding commutes with the canonical maps of p-adic
integer coefficients. -/
theorem padicStandardLevelIntegerEmbedding_comp_coefficientHom
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    (padicStandardLevelIntegerEmbedding p n).comp
        (standardLubinTateLevelCoefficientHom hπ n) =
      padicCompletedLevelPadicIntegerCoefficientHom p n := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let E := padicCompletedLevelField p n
  ext a
  simp only [RingHom.comp_apply,
    padicStandardLevelIntegerEmbedding_coe,
    padicCompletedLevelPadicIntegerCoefficientHom_coe]
  change
    padicStandardLevelEmbedding p n
        (algebraMap ℚ_[p] L (a : ℚ_[p])) =
      algebraMap (padicCompletedUnramifiedField p) E
        (algebraMap ℚ_[p]
          (padicCompletedUnramifiedField p) (a : ℚ_[p]))
  rw [(padicStandardLevelEmbedding p n).commutes,
    ← IsScalarTower.algebraMap_apply ℚ_[p]
      (padicCompletedUnramifiedField p) E]

/-- Evaluation after extending p-adic coefficients to the completed Witt
ring is evaluation through the direct p-adic coefficient map. -/
theorem padicCompletedLevelPowerSeriesEval_map_padicCoefficients
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : (padicCompletedLevelCompleteDVF p n).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (f : PowerSeries (padicLocalField p).valuationSubring) :
    padicCompletedLevelPowerSeriesEval p n x hx
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p) f) =
      PowerSeries.eval₂
        (padicCompletedLevelPadicIntegerCoefficientHom p n) x f := by
  have hpadic :
      Continuous (padicCompletedLevelPadicIntegerCoefficientHom p n) :=
    continuous_of_discreteTopology
  rw [padicCompletedLevelPowerSeriesEval,
    PowerSeries.coe_eval₂Hom,
    PowerSeries.eval₂_eq_tsum
      (padicCompletedLevelWittCoefficientHom_continuous p n) hx,
    PowerSeries.eval₂_eq_tsum hpadic hx]
  apply tsum_congr
  intro d
  rw [PowerSeries.coeff_map]
  rfl

/-- Analytic evaluation in the finite standard level commutes with its
integral embedding into the completed level. -/
theorem padicStandardLevelIntegerEmbedding_powerSeriesEval
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x :
      (standardLubinTateLevelCompleteDVF
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      ).valuationSubring)
    (hx : PowerSeries.HasEval x)
    (f : PowerSeries (padicLocalField p).valuationSubring) :
    padicStandardLevelIntegerEmbedding p n
        (standardLubinTateLevelPowerSeriesEval
          (padicMultiplicativeLubinTateSeries_isUniformizer p)
          n x hx f) =
      padicCompletedLevelPowerSeriesEval p n
        (padicStandardLevelIntegerEmbedding p n x)
        (hx.map (padicStandardLevelIntegerEmbedding_continuous p n))
        (PowerSeries.map
          (padicValuationSubringToCompletedUnramifiedWittRing p) f) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let j := padicStandardLevelIntegerEmbedding p n
  have hraw :=
    congrFun
      (PowerSeries.comp_eval₂
        (φ := standardLubinTateLevelCoefficientHom hπ n)
        continuous_of_discreteTopology hx
        (padicStandardLevelIntegerEmbedding_continuous p n)) f
  have htransport :
      j
          (PowerSeries.eval₂
            (standardLubinTateLevelCoefficientHom hπ n) x f) =
        PowerSeries.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (j x) f := by
    rw [← padicStandardLevelIntegerEmbedding_comp_coefficientHom p n]
    simpa only [Function.comp_apply] using hraw
  calc
    j
        (standardLubinTateLevelPowerSeriesEval hπ n x hx f) =
        PowerSeries.eval₂
          (padicCompletedLevelPadicIntegerCoefficientHom p n)
          (j x) f := by
      simpa only [standardLubinTateLevelPowerSeriesEval,
        PowerSeries.coe_eval₂Hom] using htransport
    _ =
        padicCompletedLevelPowerSeriesEval p n (j x)
          (hx.map (padicStandardLevelIntegerEmbedding_continuous p n))
          (PowerSeries.map
            (padicValuationSubringToCompletedUnramifiedWittRing p) f) :=
      (padicCompletedLevelPowerSeriesEval_map_padicCoefficients
        p n (j x)
        (hx.map (padicStandardLevelIntegerEmbedding_continuous p n))
        f).symm

/-- The integral embedding carries the finite analytic unit action to the
direct completed analytic unit action with the same unit. -/
@[simp]
theorem
    padicStandardLevelIntegerEmbedding_apply_primitivePointUnitAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    padicStandardLevelIntegerEmbedding p n
        (standardLubinTatePrimitivePointIntegerAction hπ n u) =
      padicCompletedStandardPrimitivePointUnitAction p n u := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  have h :=
    padicStandardLevelIntegerEmbedding_powerSeriesEval p n
      (standardLubinTatePrimitivePointInteger hπ n)
      (standardLubinTatePrimitivePointInteger_hasEval hπ n)
      (standardLubinTateEndomorphism hπ
        (u : (padicLocalField p).valuationSubring))
  simpa only [
    standardLubinTatePrimitivePointIntegerAction,
    standardLubinTateEndomorphismValue,
    standardLubinTateEndomorphismEvalAt,
    padicCompletedStandardPrimitivePointUnitAction,
    padicCompletedStandardScalarEndomorphismValue,
    padicCompletedStandardScalarEndomorphism,
    padicStandardLevelIntegerEmbedding_apply_primitivePoint] using h

/-- At the finite p-adic level, the parameter class of a unit realizes
exactly its direct analytic action. -/
theorem padicStandardUnitParameterLevelRoot_class
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    let F := padicLocalField p
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    standardLubinTateUnitParameterLevelRoot F hπ n
        (standardLubinTateUnitParameterClass F n u) =
      standardLubinTatePrimitiveLevelAction hπ n u := by
  let F := padicLocalField p
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  apply Subtype.ext
  exact (standardLubinTateUnitParameterLevelRoot_coe F hπ n
    (standardLubinTateUnitParameterClass F n u)).trans
      ((standardLubinTateUnitParameterRoot_class F hπ n u).trans
        (standardLubinTatePrimitiveLevelAction_coe
          (F := F) hπ n u).symm)

/-- The direct completed unit action is the completed realization of the
same finite unit-parameter class. -/
@[simp]
theorem
    padicCompletedStandardPrimitivePointUnitAction_eq_unitParameterRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ) :
    ((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        padicCompletedUnitParameterRoot p n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let source := standardLubinTateLevelCompleteDVF hπ n
  calc
    ((padicCompletedStandardPrimitivePointUnitAction p n u :
        (padicCompletedLevelCompleteDVF p n).valuationSubring) :
      padicCompletedLevelField p n) =
        ((padicStandardLevelIntegerEmbedding p n
            (standardLubinTatePrimitivePointIntegerAction hπ n u) :
          (padicCompletedLevelCompleteDVF p n).valuationSubring) :
            padicCompletedLevelField p n) := by
      rw [
        padicStandardLevelIntegerEmbedding_apply_primitivePointUnitAction]
    _ =
        padicStandardLevelEmbedding p n
          ((standardLubinTatePrimitivePointIntegerAction hπ n u :
            source.valuationSubring) :
              standardLubinTateLevelField hπ n) := by
      rw [padicStandardLevelIntegerEmbedding_coe]
    _ =
        padicStandardLevelEmbedding p n
          (standardLubinTateUnitParameterLevelRoot
            (padicLocalField p) hπ n
            (standardLubinTateUnitParameterClass
              (padicLocalField p) n u)) := by
      congr 1
      change
        standardLubinTatePrimitiveLevelAction hπ n u =
          standardLubinTateUnitParameterLevelRoot
            (padicLocalField p) hπ n
            (standardLubinTateUnitParameterClass
              (padicLocalField p) n u)
      exact (padicStandardUnitParameterLevelRoot_class p n u).symm
    _ =
        padicCompletedUnitParameterRoot p n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) :=
      rfl

/-- The completed unit-indexed Frobenius lift restricts to the finite
standard-level automorphism with the same unit-parameter class. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_standardLevelEmbedding
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    padicCompletedUnitFrobeniusLiftEquiv p n u
        (padicStandardLevelEmbedding p n x) =
      padicStandardLevelEmbedding p n
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x) := by
  let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
  let L := standardLubinTateLevelField hπ n
  let E := padicCompletedLevelField p n
  let ι : L →ₐ[ℚ_[p]] E := padicStandardLevelEmbedding p n
  let δ : E →ₐ[ℚ_[p]] E :=
    { toRingHom :=
        (padicCompletedUnitFrobeniusLiftEquiv p n u).toRingHom
      commutes' := by
        intro b
        change
          padicCompletedUnitFrobeniusLiftEquiv p n u
              (algebraMap (padicCompletedUnramifiedField p) E
                (algebraMap ℚ_[p]
                  (padicCompletedUnramifiedField p) b)) =
            algebraMap (padicCompletedUnramifiedField p) E
              (algebraMap ℚ_[p]
                (padicCompletedUnramifiedField p) b)
        rw [padicCompletedUnitFrobeniusLiftEquiv_algebraMap,
          (padicCompletedUnramifiedFrobenius p).commutes] }
  let σ : L ≃ₐ[ℚ_[p]] L :=
    standardLubinTateUnitParameterAlgEquiv
      (padicLocalField p) hπ n
      (standardLubinTateUnitParameterClass
        (padicLocalField p) n u)
  have hintertwine : δ.comp ι = ι.comp σ.toAlgHom := by
    apply (standardLubinTateLevelPowerBasis hπ n).algHom_ext
    change
      padicCompletedUnitFrobeniusLiftEquiv p n u
          (padicStandardLevelEmbedding p n
            (standardLubinTateLevelPowerBasis hπ n).gen) =
        padicStandardLevelEmbedding p n
          (standardLubinTateUnitParameterAlgEquiv
            (padicLocalField p) hπ n
            (standardLubinTateUnitParameterClass
              (padicLocalField p) n u)
            (standardLubinTateLevelPowerBasis hπ n).gen)
    rw [padicStandardLevelEmbedding_apply_gen,
      padicCompletedUnitFrobeniusLiftEquiv_primitiveRoot]
    have hgen := congrArg (padicStandardLevelEmbedding p n)
      (standardLubinTateUnitParameterAlgEquiv_apply_gen
        (padicLocalField p) hπ n
        (standardLubinTateUnitParameterClass (padicLocalField p) n u))
    exact (padicCompletedStandardPrimitivePointUnitAction_eq_unitParameterRoot
      p n u).trans hgen.symm
  exact DFunLike.congr_fun hintertwine x

/-- The inverse completed unit-indexed Frobenius lift restricts to the
inverse finite unit-parameter automorphism. -/
theorem padicCompletedUnitFrobeniusLiftEquiv_symm_standardLevelEmbedding
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    (padicCompletedUnitFrobeniusLiftEquiv p n u).symm
        (padicStandardLevelEmbedding p n x) =
      padicStandardLevelEmbedding p n
        ((standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u)).symm x) := by
  apply (padicCompletedUnitFrobeniusLiftEquiv p n u).injective
  rw [
    (padicCompletedUnitFrobeniusLiftEquiv p n u).apply_symm_apply,
    padicCompletedUnitFrobeniusLiftEquiv_standardLevelEmbedding,
    (standardLubinTateUnitParameterAlgEquiv
      (padicLocalField p)
      (padicMultiplicativeLubinTateSeries_isUniformizer p) n
      (standardLubinTateUnitParameterClass
        (padicLocalField p) n u)).apply_symm_apply]

/-- With the inverse unit as Frobenius-lift parameter, the inverse completed
lift acts on the standard finite level by the direct unit parameter.  This is
the orientation used by the actual local Artin map after changed-uniformizer
descent. -/
theorem
    padicCompletedInverseUnitFrobeniusLiftEquiv_standardLevelEmbedding
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (padicLocalField p).valuationSubringˣ)
    (x :
      standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n) :
    (padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹).symm
        (padicStandardLevelEmbedding p n x) =
      padicStandardLevelEmbedding p n
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u) x) := by
  rw [
    padicCompletedUnitFrobeniusLiftEquiv_symm_standardLevelEmbedding]
  have hclass :
      standardLubinTateUnitParameterClass
          (padicLocalField p) n u⁻¹ =
        (standardLubinTateUnitParameterClass
          (padicLocalField p) n u)⁻¹ :=
    (standardLubinTateUnitParameterClass
      (padicLocalField p) n).map_inv u
  have hparameter :
      standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u⁻¹) =
        (standardLubinTateUnitParameterAlgEquiv
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u))⁻¹ := by
    change
      standardLubinTateUnitParameterEquivGal
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u⁻¹) =
        (standardLubinTateUnitParameterEquivGal
          (padicLocalField p)
          (padicMultiplicativeLubinTateSeries_isUniformizer p) n
          (standardLubinTateUnitParameterClass
            (padicLocalField p) n u))⁻¹
    rw [hclass,
      (standardLubinTateUnitParameterEquivGal
        (padicLocalField p)
        (padicMultiplicativeLubinTateSeries_isUniformizer p) n).map_inv]
  rw [hparameter]
  rfl

end LubinTate

end
