/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
public import Mathlib.FieldTheory.SplittingField.IsSplittingField
/-!
# The tower of standard Lubin--Tate level fields

The primitive roots defining the standard finite levels are chosen
independently in one separable closure.  Exact torsion and normality show
that the resulting simple fields nevertheless form an increasing tower.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The polynomial predecessor of the primitive level-`n + 1` generator,
regarded as an element of the level-`n + 1` field itself. -/
noncomputable def standardLubinTatePrimitivePredecessorInLevelField
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {m n : ℕ} (_hmn : m ≤ n) :
    standardLubinTateLevelField hπ n :=
  Polynomial.eval₂
    (algebraMap K (standardLubinTateLevelField hπ n))
    (standardLubinTateLevelGenerator hπ n)
    (standardLubinTatePolynomialIterateOverField F π (n - m))

/-- Coercing the internal predecessor to the separable closure gives the
ambient polynomial predecessor used by the exact-torsion theorem. -/
@[simp]
theorem standardLubinTatePrimitivePredecessorInLevelField_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {m n : ℕ} (hmn : m ≤ n) :
    (standardLubinTatePrimitivePredecessorInLevelField hπ hmn :
        SeparableClosure K) =
      (standardLubinTatePolynomialIterateOverSeparableClosure
        F π (n - m)).eval
          (chosenStandardLubinTatePrimitiveRoot hπ n) := by
  let E := standardLubinTateLevelField hπ n
  let ι : E →ₐ[K] SeparableClosure K := E.val
  change ι.toRingHom
      (Polynomial.eval₂ (algebraMap K E)
        (standardLubinTateLevelGenerator hπ n)
        (standardLubinTatePolynomialIterateOverField F π (n - m))) =
    _
  rw [Polynomial.hom_eval₂]
  have hcomp :
      ι.toRingHom.comp (algebraMap K E) =
        algebraMap K (SeparableClosure K) := by
    ext x
    rfl
  rw [hcomp]
  change Polynomial.eval₂ (algebraMap K (SeparableClosure K))
      ((standardLubinTateLevelGenerator hπ n : E) : SeparableClosure K)
      (standardLubinTatePolynomialIterateOverField F π (n - m)) =
    _
  rw [standardLubinTateLevelGenerator_coe]
  simp [standardLubinTatePolynomialIterateOverField,
    standardLubinTatePolynomialIterateOverSeparableClosure,
    Polynomial.eval_map, Polynomial.eval₂_map]

/-- The independently chosen standard Lubin--Tate level fields form an
increasing tower inside the fixed separable closure. -/
theorem standardLubinTateLevelField_mono
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {m n : ℕ} (hmn : m ≤ n) :
    standardLubinTateLevelField hπ m ≤
      standardLubinTateLevelField hπ n := by
  let S := SeparableClosure K
  let E := standardLubinTateLevelField hπ n
  let p := standardLubinTatePrimitivePolynomialOverField F π m
  let yE : E :=
    standardLubinTatePrimitivePredecessorInLevelField hπ hmn
  have hyp : (p.map (algebraMap K E)).IsRoot yE := by
    have hroot :=
      chosenStandardLubinTatePrimitivePredecessor_isRoot hπ hmn
    change Polynomial.eval
      ((standardLubinTatePolynomialIterateOverSeparableClosure
        F π (n - m)).eval
          (chosenStandardLubinTatePrimitiveRoot hπ n))
      (p.map (algebraMap K S)) = 0 at hroot
    change Polynomial.eval yE (p.map (algebraMap K E)) = 0
    apply E.val.injective
    rw [map_zero, Polynomial.eval_map, Polynomial.hom_eval₂]
    have hcomp :
        E.val.toRingHom.comp (algebraMap K E) =
          algebraMap K S := by
      ext x
      rfl
    rw [hcomp]
    simpa [yE, p, Polynomial.eval₂_eq_eval_map] using hroot
  have hp_minpoly : p = minpoly K yE := by
    apply minpoly.eq_of_irreducible_of_monic
      (standardLubinTatePrimitivePolynomialOverField_irreducible hπ m)
      _ (standardLubinTatePrimitivePolynomialOverField_monic F π m)
    simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hyp
  let : FiniteDimensional K E :=
    standardLubinTateLevelField_finiteDimensional hπ n
  let : IsGalois K E :=
    standardLubinTateLevelField_isGalois hπ n
  have hp_split_E : (p.map (algebraMap K E)).Splits := by
    rw [hp_minpoly]
    exact IsGalois.splits K yE
  have hp_split_S : (p.map (algebraMap K S)).Splits := by
    have h := hp_split_E.map E.val.toRingHom
    simpa [Polynomial.map_map] using h
  have hchosen_mem :
      chosenStandardLubinTatePrimitiveRoot hπ m ∈ E := by
    apply
      (IntermediateField.splits_iff_mem
        (F := E) hp_split_S).1 hp_split_E
    rw [Polynomial.mem_rootSet']
    constructor
    · exact
        ((standardLubinTatePrimitivePolynomialOverField_monic F π m).map
          (algebraMap K S)).ne_zero
    · simpa [Polynomial.aeval_def, p] using
        chosenStandardLubinTatePrimitiveRoot_isRoot hπ m
  change IntermediateField.adjoin K
      {chosenStandardLubinTatePrimitiveRoot hπ m} ≤ E
  rw [IntermediateField.adjoin_le_iff]
  simpa using hchosen_mem

end LubinTate

end
