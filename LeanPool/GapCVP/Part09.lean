/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part08
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Int.Star
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-! # GapCVP proof, part 09 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace Factor400BinaryConstructiveSourcePlaces

open scoped BigOperators

open GapCVP.Core GapCVP.BinaryFieldBasis

/-- GapCVP reduction support. -/
abbrev sourceFormulaField (encodingLength : ℕ) (formula : Formula) :=
  GapCVP.Core.sourceFormulaField encodingLength formula

theorem variableCount_le_fieldWordCount
    (encodingLength : ℕ) (formula : Formula) :
    formula.variableCount ≤
      2 ^ sourceFieldExponent
        (sourceSizeParameter encodingLength formula) := by
  let sourceSize := sourceSizeParameter encodingLength formula
  have hsource : 100 ≤ sourceSize :=
    sourceSizeParameter_ge_one_hundred encodingLength formula
  have hvariable : formula.variableCount ≤ sourceSize :=
    source_variableCount_le_size encodingLength formula
  have hpower : sourceSize ≤ sourceSize ^ 200 := by
    calc
      sourceSize = sourceSize ^ 1 := by simp only [pow_one]
      _ ≤ sourceSize ^ 200 :=
        Nat.pow_le_pow_right (by omega) (by norm_num)
  have hcard : sourceSize ^ 200 ≤
      2 ^ sourceFieldExponent sourceSize := by
    simpa only [sourceFiniteField_card hsource] using sourceFiniteField_card_lower hsource
  exact hvariable.trans (hpower.trans hcard)

/-- GapCVP reduction support. -/
def sourceFormulaVariableWordIndex
    (encodingLength : ℕ) (formula : Formula) :
    Fin formula.variableCount ↪
      Fin (2 ^ sourceFieldExponent
        (sourceSizeParameter encodingLength formula)) :=
  boundedWordIndex (variableCount_le_fieldWordCount
    encodingLength formula)

/-- GapCVP reduction support. -/
def sourceFormulaVariableWord
    (encodingLength : ℕ) (formula : Formula)
    (index : Fin formula.variableCount) :
    EffectiveBinaryField.Word
      (sourceFieldExponent
        (sourceSizeParameter encodingLength formula)) :=
  indexedWord _
    (sourceFormulaVariableWordIndex encodingLength formula index)

/-- GapCVP reduction support. -/
def sourceFormulaVariablePlace
    (encodingLength : ℕ) (formula : Formula) :
    Fin formula.variableCount → sourceFormulaField encodingLength formula :=
  effectiveAnchor
    (sourceFieldExponent (sourceSizeParameter encodingLength formula))
    (sourceFieldExponent_pos
      (sourceSizeParameter_ge_one_hundred encodingLength formula))
    (variableCount_le_fieldWordCount encodingLength formula)

theorem sourceFormulaVariablePlace_injective
    (encodingLength : ℕ) (formula : Formula) :
    Function.Injective
      (sourceFormulaVariablePlace encodingLength formula) :=
  (effectiveAnchor
    (sourceFieldExponent (sourceSizeParameter encodingLength formula))
    (sourceFieldExponent_pos
      (sourceSizeParameter_ge_one_hundred encodingLength formula))
    (variableCount_le_fieldWordCount encodingLength formula)).injective

/-- GapCVP reduction support. -/
def sourceFormulaFieldBasis (encodingLength : ℕ) (formula : Formula) :
    Module.Basis
      (Fin (sourceFieldExponent
        (sourceSizeParameter encodingLength formula)))
      (ZMod 2) (sourceFormulaField encodingLength formula) :=
  effectiveFieldBasis
    (sourceFieldExponent (sourceSizeParameter encodingLength formula))
    (sourceFieldExponent_pos
      (sourceSizeParameter_ge_one_hundred encodingLength formula))

/-- GapCVP reduction support. -/
def sourceFormulaGrid (encodingLength : ℕ) (formula : Formula) :
    Finset (sourceFormulaField encodingLength formula) :=
  sourceSATPuncturedGrid formula
    (sourceFormulaVariablePlace encodingLength formula)

private theorem sourceFormulaGrid_card
    (encodingLength : ℕ) (formula : Formula) :
    (sourceFormulaGrid encodingLength formula).card =
      Fintype.card (sourceFormulaField encodingLength formula) -
        formula.variableCount := by
  exact sourceSATPuncturedGrid_card formula
    (sourceFormulaVariablePlace encodingLength formula)
    (sourceFormulaVariablePlace_injective encodingLength formula)

theorem sourceFormulaGrid_card_eq_fieldWordCount
    (encodingLength : ℕ) (formula : Formula) :
    (sourceFormulaGrid encodingLength formula).card =
      2 ^ sourceFieldExponent
        (sourceSizeParameter encodingLength formula) -
          formula.variableCount := by
  rw [sourceFormulaGrid_card,
    sourceFiniteField_card
      (sourceSizeParameter_ge_one_hundred encodingLength formula)]

private theorem sourceFormulaGrid_max_degree_lt
    (encodingLength : ℕ) (formula : Formula) :
    sourceSizeParameter encodingLength formula ^ 31 <
      (sourceFormulaGrid encodingLength formula).card := by
  classical
  let sourceSize := sourceSizeParameter encodingLength formula
  let places : Finset (sourceFormulaField encodingLength formula) :=
    (Finset.univ : Finset (Fin formula.variableCount)).image
      (sourceFormulaVariablePlace encodingLength formula)
  have hplaces : places.card ≤ sourceSize := by
    calc
      places.card ≤
          (Finset.univ : Finset (Fin formula.variableCount)).card := by
        dsimp [places]
        exact Finset.card_image_le
      _ = formula.variableCount := by simp only [Finset.card_univ, Fintype.card_fin]
      _ ≤ sourceSize := source_variableCount_le_size encodingLength formula
  have hgrid := source_moment_degree_lt_actual_grid
    places (sourceSizeParameter_ge_one_hundred encodingLength formula)
    (sourceFiniteField_card_lower
      (sourceSizeParameter_ge_one_hundred encodingLength formula))
    hplaces
  simpa only [sourceFormulaGrid, sourceSATPuncturedGrid, gt_iff_lt] using hgrid

theorem sourceFormulaGrid_card_pos
    (encodingLength : ℕ) (formula : Formula) :
    0 < (sourceFormulaGrid encodingLength formula).card :=
  Nat.zero_lt_of_lt
    (sourceFormulaGrid_max_degree_lt encodingLength formula)

/-- GapCVP reduction support. -/
abbrev sourceFormulaDimension (encodingLength : ℕ) (formula : Formula) : ℕ :=
  sourceSATTableDimension formula
    (sourceFormulaField encodingLength formula)
    (sourceFormulaGrid encodingLength formula)

theorem sourceFormulaDimension_pos
    (encodingLength : ℕ) (formula : Formula) :
    0 < sourceFormulaDimension encodingLength formula := by
  unfold sourceFormulaDimension
  rw [sourceSATTableDimension_eq]
  have htypes : 0 < Fintype.card (sourceSATTableType formula) :=
    Fintype.card_pos_iff.mpr ⟨.inl ()⟩
  have hfield :
      0 < Fintype.card (sourceFormulaField encodingLength formula) :=
    Fintype.card_pos_iff.mpr ⟨0⟩
  exact Nat.mul_pos
    (Nat.mul_pos htypes
      (sourceFormulaGrid_card_pos encodingLength formula)) hfield

theorem sourceFormulaDimension_le
    (encodingLength : ℕ) (formula : Formula) :
    sourceFormulaDimension encodingLength formula ≤
      40 * sourceSizeParameter encodingLength formula ^ 401 := by
  unfold sourceFormulaDimension
  apply sourceSATTableDimension_le formula
    (sourceFormulaField encodingLength formula)
    (sourceFormulaGrid encodingLength formula)
    (sourceSizeParameter encodingLength formula)
    (sourceSizeParameter_ge_one_hundred encodingLength formula)
    (source_clauseCount_le_size encodingLength formula)
  · exact Finset.card_le_card (Finset.subset_univ _)
  · exact sourceFiniteField_card_upper
      (sourceSizeParameter_ge_one_hundred encodingLength formula)

/-- GapCVP reduction support. -/
def sourceFormulaBinarySystem
    (encodingLength : ℕ) (formula : Formula) : BinaryAffineSystem :=
  concreteSATBinaryAffineSystem formula
    (sourceFormulaFieldBasis encodingLength formula)
    (sourceFormulaGrid encodingLength formula)
    (sourceFormulaVariablePlace encodingLength formula)
    (sourceSizeParameter encodingLength formula ^ 30)

theorem sourceFormulaBinarySystem_solves_iff
    (encodingLength : ℕ) (formula : Formula)
    (z : Fin (sourceFormulaDimension encodingLength formula) → ℤ) :
    (sourceFormulaBinarySystem encodingLength formula).Solves z ↔
      concreteSATFieldChecks formula
        (sourceFormulaGrid encodingLength formula)
        (sourceFormulaVariablePlace encodingLength formula)
        (sourceSizeParameter encodingLength formula ^ 30)
        (fun position => algebraMap (ZMod 2)
          (sourceFormulaField encodingLength formula)
          (z position : ZMod 2)) := by
  exact concreteSATBinaryAffineSystem_solves_iff
    formula (sourceFormulaFieldBasis encodingLength formula)
    (sourceFormulaGrid encodingLength formula)
    (sourceFormulaVariablePlace encodingLength formula)
    (sourceSizeParameter encodingLength formula ^ 30) z

end Factor400BinaryConstructiveSourcePlaces

namespace BinarySourceCoordinateOrder

open GapCVP.Core GapCVP.BinaryFieldBasis GapCVP.Factor400BinaryConstructiveSourcePlaces

attribute [local instance] Classical.propDecidable

/-- GapCVP reduction support. -/
abbrev sourceFormulaWordDegree
    (encodingLength : ℕ) (formula : Formula) : ℕ :=
  sourceFieldExponent (sourceSizeParameter encodingLength formula)

/-- GapCVP reduction support. -/
def sourceFormulaFieldWordOrder
    (encodingLength : ℕ) (formula : Formula) :
    Fin (2 ^ sourceFormulaWordDegree encodingLength formula) ≃
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength formula :=
  indexedFieldEquiv (sourceFormulaWordDegree encodingLength formula)
    (sourceFieldExponent_pos
      (sourceSizeParameter_ge_one_hundred encodingLength formula))

theorem sourceFormulaFieldWordOrder_card
    (encodingLength : ℕ) (formula : Formula) :
    Fintype.card
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength formula) =
      2 ^ sourceFormulaWordDegree encodingLength formula :=
  sourceFiniteField_card
    (sourceSizeParameter_ge_one_hundred encodingLength formula)

/-- GapCVP reduction support. -/
def sourceFormulaFieldCardOrder
    (encodingLength : ℕ) (formula : Formula) :
    Fin (Fintype.card
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength formula)) ≃
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength formula :=
  (finCongr (sourceFormulaFieldWordOrder_card
    encodingLength formula)).trans
      (sourceFormulaFieldWordOrder encodingLength formula)

/-- GapCVP reduction support. -/
def sourceFormulaEvaluationWord
    (encodingLength : ℕ) (formula : Formula)
    (index : Fin
      (2 ^ sourceFormulaWordDegree encodingLength formula -
        formula.variableCount)) :
    GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
      encodingLength formula :=
  effectiveEvaluationEmbedding
    (sourceFormulaWordDegree encodingLength formula)
    (sourceFieldExponent_pos
      (sourceSizeParameter_ge_one_hundred encodingLength formula))
    (variableCount_le_fieldWordCount encodingLength formula) index

theorem sourceFormulaEvaluationWord_ne_variablePlace
    (encodingLength : ℕ) (formula : Formula)
    (index : Fin
      (2 ^ sourceFormulaWordDegree encodingLength formula -
        formula.variableCount))
    (variableIndex : Fin formula.variableCount) :
    sourceFormulaEvaluationWord encodingLength formula index ≠
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
        encodingLength formula variableIndex := by
  exact effectiveEvaluationEmbedding_ne_anchor
    (sourceFormulaWordDegree encodingLength formula)
    (sourceFieldExponent_pos
      (sourceSizeParameter_ge_one_hundred encodingLength formula))
    (variableCount_le_fieldWordCount encodingLength formula)
    index variableIndex

private def sourceFormulaGridWordEmbedding
    (encodingLength : ℕ) (formula : Formula) :
    Fin (2 ^ sourceFormulaWordDegree encodingLength formula -
      formula.variableCount) ↪
      sourceSATGridPoint
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
          encodingLength formula) where
  toFun index :=
    ⟨sourceFormulaEvaluationWord encodingLength formula index, by
      change sourceFormulaEvaluationWord encodingLength formula index ∈
        Finset.univ \
          ((Finset.univ : Finset (Fin formula.variableCount)).image
            (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
              encodingLength formula))
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro himage
      obtain ⟨variableIndex, _, hequal⟩ :=
        Finset.mem_image.mp himage
      exact (sourceFormulaEvaluationWord_ne_variablePlace
        encodingLength formula index variableIndex) hequal.symm⟩
  inj' := by
    intro first second hequal
    apply (effectiveEvaluationEmbedding
      (sourceFormulaWordDegree encodingLength formula)
      (sourceFieldExponent_pos
        (sourceSizeParameter_ge_one_hundred encodingLength formula))
      (variableCount_le_fieldWordCount encodingLength formula)).injective
    exact congrArg Subtype.val hequal

private theorem sourceFormulaGridWordEmbedding_bijective
    (encodingLength : ℕ) (formula : Formula) :
    Function.Bijective
      (sourceFormulaGridWordEmbedding encodingLength formula) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨(sourceFormulaGridWordEmbedding
    encodingLength formula).injective, ?_⟩
  simpa only [Fintype.card_fin, Fintype.card_coe] using
      (sourceFormulaGrid_card_eq_fieldWordCount encodingLength formula).symm

/-- GapCVP reduction support. -/
def sourceFormulaGridWordOrder
    (encodingLength : ℕ) (formula : Formula) :
    Fin (2 ^ sourceFormulaWordDegree encodingLength formula -
      formula.variableCount) ≃
      sourceSATGridPoint
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
          encodingLength formula) :=
  Equiv.ofBijective
    (sourceFormulaGridWordEmbedding encodingLength formula)
    (sourceFormulaGridWordEmbedding_bijective encodingLength formula)

/-- GapCVP reduction support. -/
def sourceFormulaGridOrder
    (encodingLength : ℕ) (formula : Formula) :
    Fin ((GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
      encodingLength formula).card) ≃
      sourceSATGridPoint
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
          encodingLength formula) :=
  (finCongr
    (sourceFormulaGrid_card_eq_fieldWordCount
      encodingLength formula)).trans
    (sourceFormulaGridWordOrder encodingLength formula)

/-- GapCVP reduction support. -/
def sourceFormulaCoordinateOrder
    (encodingLength : ℕ) (formula : Formula)
    (typeOrder :
      Fin (Fintype.card (sourceSATTableType formula)) ≃
        sourceSATTableType formula) :
    Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength formula) ≃
      sourceSATTableCoordinate formula
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength formula)
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
          encodingLength formula) := by
  let grid :=
    GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
      encodingLength formula
  let field :=
    GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
      encodingLength formula
  have hdimension :
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
          encodingLength formula =
        Fintype.card (sourceSATTableType formula) *
          grid.card * Fintype.card field := by
    exact sourceSATTableDimension_eq formula field grid
  refine (finCongr hdimension).trans ?_
  let first :=
    (finProdFinEquiv
      (m := Fintype.card (sourceSATTableType formula) * grid.card)
      (n := Fintype.card field)).symm
  let second :=
    (finProdFinEquiv
      (m := Fintype.card (sourceSATTableType formula))
      (n := grid.card)).symm
  exact first.trans
    ((second.prodCongr
      (sourceFormulaFieldCardOrder encodingLength formula)).trans
        ((Equiv.prodAssoc
          (Fin (Fintype.card (sourceSATTableType formula)))
          (Fin grid.card) field).trans
          (typeOrder.prodCongr
            ((sourceFormulaGridOrder encodingLength formula).prodCongr
              (Equiv.refl field)))))

end BinarySourceCoordinateOrder

namespace BinaryReedSolomonParity

open Polynomial Matrix

variable {K : Type*} [Field K]

/-- GapCVP reduction support. -/
def orderedInterpolationNode {p D : ℕ}
    (points : Fin p → K) (hdegree : D < p) : Fin (D + 1) → K :=
  fun index => points
    (Fin.castLE (Nat.succ_le_of_lt hdegree) index)

omit [Field K] in
private theorem orderedInterpolationNode_injective {p D : ℕ}
    (points : Fin p → K) (hdegree : D < p)
    (hpoints : Function.Injective points) :
    Function.Injective (orderedInterpolationNode points hdegree) := by
  intro first second heq
  have hcast :
      Fin.castLE (Nat.succ_le_of_lt hdegree) first =
        Fin.castLE (Nat.succ_le_of_lt hdegree) second :=
    hpoints heq
  apply Fin.ext
  simpa only [Nat.succ_eq_add_one, Fin.val_castLE] using congrArg (fun index : Fin p => index.val)
      hcast

/-- GapCVP reduction support. -/
def orderedInterpolationPrefix {p D : ℕ}
    (hdegree : D < p) :
    (Fin p → K) →ₗ[K] (Fin (D + 1) → K) where
  toFun values index :=
    values (Fin.castLE (Nat.succ_le_of_lt hdegree) index)
  map_add' first second := by
    funext index
    rfl
  map_smul' scalar values := by
    funext index
    rfl

/-- GapCVP reduction support. -/
def orderedInterpolationPolynomial {p D : ℕ}
    (points : Fin p → K) (hdegree : D < p)
    (values : Fin p → K) : K[X] :=
  Lagrange.interpolate (Finset.univ : Finset (Fin (D + 1)))
    (orderedInterpolationNode points hdegree)
    (orderedInterpolationPrefix hdegree values)

private def orderedGridEvaluation {p : ℕ}
    (points : Fin p → K) : K[X] →ₗ[K] (Fin p → K) where
  toFun polynomial index := polynomial.eval (points index)
  map_add' first second := by
    funext index
    simp only [eval_add, Pi.add_apply]
  map_smul' scalar polynomial := by
    funext index
    simp only [eval_smul, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]

/-- GapCVP reduction support. -/
def constructiveParityLinearMap {p D : ℕ}
    (points : Fin p → K) (hdegree : D < p) :
    (Fin p → K) →ₗ[K] (Fin p → K) :=
  LinearMap.id -
    (orderedGridEvaluation points).comp
      ((Lagrange.interpolate (Finset.univ : Finset (Fin (D + 1)))
        (orderedInterpolationNode points hdegree)).comp
          (orderedInterpolationPrefix hdegree))

/-- GapCVP reduction support. -/
def constructiveParityMatrix {p D : ℕ}
    (points : Fin p → K) (hdegree : D < p) :
    Matrix (Fin p) (Fin p) K :=
  LinearMap.toMatrix' (constructiveParityLinearMap points hdegree)

@[simp] theorem constructiveParityLinearMap_apply {p D : ℕ}
    (points : Fin p → K) (hdegree : D < p)
    (values : Fin p → K) (index : Fin p) :
    constructiveParityLinearMap points hdegree values index =
      values index -
        (orderedInterpolationPolynomial points hdegree values).eval
          (points index) := by
  rfl

private theorem orderedInterpolationPolynomial_natDegree_le {p D : ℕ}
    (points : Fin p → K) (hdegree : D < p)
    (hpoints : Function.Injective points)
    (values : Fin p → K) :
    (orderedInterpolationPolynomial points hdegree values).natDegree ≤ D := by
  let nodes := orderedInterpolationNode points hdegree
  have hnodes : Function.Injective nodes :=
    orderedInterpolationNode_injective points hdegree hpoints
  have hlt :
      (orderedInterpolationPolynomial points hdegree values).degree <
        ((D + 1 : ℕ) : WithBot ℕ) := by
    simpa only [orderedInterpolationPolynomial, Lagrange.interpolate_apply, Nat.cast_add,
        Nat.cast_one,
        Finset.card_univ, Fintype.card_fin] using
        (Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin (D + 1))))
          (orderedInterpolationPrefix hdegree values) hnodes.injOn)
  by_cases hzero : orderedInterpolationPolynomial points hdegree values = 0
  · simp only [hzero, natDegree_zero, zero_le]
  · have hnat :=
      (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hlt
    omega

private theorem constructiveParityMatrix_mulVec_eq_zero_iff_polynomial
    {p D : ℕ} (points : Fin p → K) (hdegree : D < p)
    (hpoints : Function.Injective points)
    (values : Fin p → K) :
    (constructiveParityMatrix points hdegree).mulVec values = 0 ↔
      ∃ polynomial : K[X], polynomial.natDegree ≤ D ∧
        ∀ index : Fin p, polynomial.eval (points index) = values index := by
  rw [constructiveParityMatrix, LinearMap.toMatrix'_mulVec]
  constructor
  · intro hzero
    refine ⟨orderedInterpolationPolynomial points hdegree values,
      orderedInterpolationPolynomial_natDegree_le
        points hdegree hpoints values, ?_⟩
    intro index
    have hindex := congrFun hzero index
    rw [constructiveParityLinearMap_apply] at hindex
    exact (sub_eq_zero.mp hindex).symm
  · rintro ⟨polynomial, hpoly, heval⟩
    let nodes := orderedInterpolationNode points hdegree
    have hnodes : Function.Injective nodes :=
      orderedInterpolationNode_injective points hdegree hpoints
    have hpolynomialdegree :
        polynomial.degree < ((D + 1 : ℕ) : WithBot ℕ) := by
      by_cases hzero : polynomial = 0
      · simp only [hzero, degree_zero, Nat.cast_add, Nat.cast_one, WithBot.bot_lt_add,
          WithBot.bot_lt_natCast,
            WithBot.bot_lt_one, and_self]
      · apply (Polynomial.natDegree_lt_iff_degree_lt hzero).mp
        omega
    have hinterpolation :
        polynomial = orderedInterpolationPolynomial
          points hdegree values := by
      unfold orderedInterpolationPolynomial
      have hpolynomialdegree' :
          polynomial.degree <
            (((Finset.univ : Finset (Fin (D + 1))).card : ℕ) : WithBot ℕ) := by
        simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
            using hpolynomialdegree
      apply Lagrange.eq_interpolate_of_eval_eq
        (orderedInterpolationPrefix hdegree values)
        hnodes.injOn hpolynomialdegree'
      intro index _
      exact heval (Fin.castLE (Nat.succ_le_of_lt hdegree) index)
    funext index
    rw [constructiveParityLinearMap_apply]
    change values index -
      (orderedInterpolationPolynomial points hdegree values).eval
        (points index) = 0
    rw [← hinterpolation, heval index, sub_self]

end BinaryReedSolomonParity

namespace Core

section

open Polynomial IsDedekindDomain

variable {K E : Type*} [Field K] [Field E]

private def functionFieldPlaceIdeal (a : K) : Ideal K[X] :=
  Ideal.span ({X - C a} : Set K[X])

private theorem functionFieldPlaceIdeal_isMaximal (a : K) :
    (functionFieldPlaceIdeal a).IsMaximal := by
  simpa only [functionFieldPlaceIdeal] using
      (PrincipalIdealRing.isMaximal_of_irreducible (Polynomial.irreducible_X_sub_C a))

private theorem functionFieldPlaceIdeal_ne_bot (a : K) :
    functionFieldPlaceIdeal a ≠ ⊥ := by
  intro h
  apply Polynomial.X_sub_C_ne_zero a
  exact Ideal.span_singleton_eq_bot.mp h

section

variable [Algebra (RatFunc K) E] [Algebra K[X] E]
variable [IsScalarTower K[X] (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E]
variable [Algebra.IsSeparable (RatFunc K) E]

omit [FiniteDimensional (RatFunc K) E]
  [Algebra.IsSeparable (RatFunc K) E] in
theorem functionFieldPolynomial_algebraMap_injective :
    Function.Injective (algebraMap K[X] E) := by
  rw [IsScalarTower.algebraMap_eq K[X] (RatFunc K) E]
  exact (algebraMap (RatFunc K) E).injective.comp
    (IsFractionRing.injective K[X] (RatFunc K))

omit [FiniteDimensional (RatFunc K) E]
  [Algebra.IsSeparable (RatFunc K) E] in
private theorem functionFieldIntegralClosure_algebraMap_injective :
    Function.Injective
      (algebraMap K[X] (integralClosure K[X] E)) := by
  intro x y h
  apply functionFieldPolynomial_algebraMap_injective (K := K) (E := E)
  calc
    algebraMap K[X] E x =
        algebraMap (integralClosure K[X] E) E
          (algebraMap K[X] (integralClosure K[X] E) x) :=
      IsScalarTower.algebraMap_apply K[X] (integralClosure K[X] E) E x
    _ = algebraMap (integralClosure K[X] E) E
          (algebraMap K[X] (integralClosure K[X] E) y) :=
      congrArg (algebraMap (integralClosure K[X] E) E) h
    _ = algebraMap K[X] E y :=
      (IsScalarTower.algebraMap_apply K[X]
        (integralClosure K[X] E) E y).symm

omit [FiniteDimensional (RatFunc K) E]
  [Algebra.IsSeparable (RatFunc K) E] in
private theorem exists_functionFieldPlace_maximal (a : K) :
    ∃ P : Ideal (integralClosure K[X] E),
      P.IsMaximal ∧
        P.comap (algebraMap K[X] (integralClosure K[X] E)) =
          functionFieldPlaceIdeal a := by
  let : (functionFieldPlaceIdeal a).IsMaximal :=
    functionFieldPlaceIdeal_isMaximal a
  apply Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := integralClosure K[X] E) (functionFieldPlaceIdeal a)
  rw [(RingHom.injective_iff_ker_eq_bot _).mp
    (functionFieldIntegralClosure_algebraMap_injective
      (K := K) (E := E))]
  exact bot_le

omit [FiniteDimensional (RatFunc K) E]
  [Algebra.IsSeparable (RatFunc K) E] in
private theorem exists_functionFieldPlace_heightOne (a : K) :
    ∃ P : HeightOneSpectrum (integralClosure K[X] E),
      P.asIdeal.comap (algebraMap K[X] (integralClosure K[X] E)) =
        functionFieldPlaceIdeal a := by
  obtain ⟨P, hmaximal, hover⟩ :=
    exists_functionFieldPlace_maximal (K := K) (E := E) a
  have hnonzero : P ≠ ⊥ := by
    intro hzero
    apply functionFieldPlaceIdeal_ne_bot a
    calc
      functionFieldPlaceIdeal a =
          P.comap (algebraMap K[X] (integralClosure K[X] E)) :=
        hover.symm
      _ = ⊥ := by
        rw [hzero]
        exact Ideal.comap_bot_of_injective
          (algebraMap K[X] (integralClosure K[X] E))
          (functionFieldIntegralClosure_algebraMap_injective
            (K := K) (E := E))
  exact ⟨⟨P, hmaximal.isPrime, hnonzero⟩, hover⟩

private def functionFieldPlaceValuation
    (place : HeightOneSpectrum (integralClosure K[X] E)) :
    Valuation E (WithZero (Multiplicative ℤ)) := by
  letI : IsDedekindDomain (integralClosure K[X] E) :=
    integralClosure.isDedekindDomain K[X] (RatFunc K) E
  letI : IsFractionRing (integralClosure K[X] E) E :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc K) E
  exact place.valuation E

private theorem functionFieldPlaceValuation_lt_one_iff_mem
    (place : HeightOneSpectrum (integralClosure K[X] E))
    (x : integralClosure K[X] E) :
    functionFieldPlaceValuation (K := K) (E := E) place
        (algebraMap (integralClosure K[X] E) E x) < 1 ↔
      x ∈ place.asIdeal := by
  let : IsDedekindDomain (integralClosure K[X] E) :=
    integralClosure.isDedekindDomain K[X] (RatFunc K) E
  let : IsFractionRing (integralClosure K[X] E) E :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc K) E
  change place.valuation E
    (algebraMap (integralClosure K[X] E) E x) < 1 ↔ _
  exact place.valuation_lt_one_iff_mem x

private theorem functionFieldPlaceValuation_polynomial_lt_one_iff
    (place : HeightOneSpectrum (integralClosure K[X] E)) (a : K)
    (hover : place.asIdeal.comap
      (algebraMap K[X] (integralClosure K[X] E)) =
        functionFieldPlaceIdeal a)
    (f : K[X]) :
    functionFieldPlaceValuation (K := K) (E := E) place
        (algebraMap K[X] E f) < 1 ↔
      f ∈ functionFieldPlaceIdeal a := by
  rw [IsScalarTower.algebraMap_apply K[X]
    (integralClosure K[X] E) E f]
  rw [functionFieldPlaceValuation_lt_one_iff_mem]
  change f ∈ place.asIdeal.comap
    (algebraMap K[X] (integralClosure K[X] E)) ↔ _
  rw [hover]

private def functionFieldHeightOnePlace (a : K) :
    HeightOneSpectrum (integralClosure K[X] E) :=
  Classical.choose
    (exists_functionFieldPlace_heightOne (K := K) (E := E) a)

omit [FiniteDimensional (RatFunc K) E]
  [Algebra.IsSeparable (RatFunc K) E] in
private theorem functionFieldHeightOnePlace_comap (a : K) :
    (functionFieldHeightOnePlace (K := K) (E := E) a).asIdeal.comap
        (algebraMap K[X] (integralClosure K[X] E)) =
      functionFieldPlaceIdeal a :=
  Classical.choose_spec
    (exists_functionFieldPlace_heightOne (K := K) (E := E) a)

/-- GapCVP reduction support. -/
def functionFieldExtendedValuation (a : K) :
    Valuation E (WithZero (Multiplicative ℤ)) :=
  functionFieldPlaceValuation (K := K) (E := E)
    (functionFieldHeightOnePlace (K := K) (E := E) a)

private theorem functionFieldExtendedValuation_polynomial_lt_one_iff
    (a : K) (f : K[X]) :
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E f) < 1 ↔
      f ∈ functionFieldPlaceIdeal a := by
  exact functionFieldPlaceValuation_polynomial_lt_one_iff
    (functionFieldHeightOnePlace (K := K) (E := E) a) a
    (functionFieldHeightOnePlace_comap (K := K) (E := E) a) f

theorem functionFieldExtendedValuation_place_lt_one (a : K) :
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E (X - C a)) < 1 := by
  apply (functionFieldExtendedValuation_polynomial_lt_one_iff
    (K := K) (E := E) a (X - C a)).mpr
  exact Ideal.mem_span_singleton_self (X - C a)

end

end

section

open Finset

private def badPoints {α : Type*}
    (points : Finset α) (fiberWeight : α → ℕ) (K : ℕ) : Finset α :=
  points.filter fun p => K < fiberWeight p

private def goodPoints {α : Type*}
    (points : Finset α) (fiberWeight : α → ℕ) (K : ℕ) : Finset α :=
  points.filter fun p => fiberWeight p ≤ K

private theorem badPoints_card_mul_le_sum {α : Type*}
    (points : Finset α) (fiberWeight : α → ℕ) (K : ℕ) :
    (badPoints points fiberWeight K).card * (K + 1) ≤
      ∑ p ∈ points, fiberWeight p := by
  classical
  calc
    (badPoints points fiberWeight K).card * (K + 1) =
        ∑ p ∈ badPoints points fiberWeight K, (K + 1) := by simp only [sum_const, smul_eq_mul]
    _ ≤ ∑ p ∈ badPoints points fiberWeight K, fiberWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      exact Nat.succ_le_of_lt (Finset.mem_filter.mp hp).2
    _ ≤ ∑ p ∈ points, fiberWeight p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro p _ _
        exact Nat.zero_le _

private theorem badPoints_card_le_div {α : Type*}
    (points : Finset α) (fiberWeight : α → ℕ) (K budget : ℕ)
    (hbudget : (∑ p ∈ points, fiberWeight p) ≤ budget) :
    (badPoints points fiberWeight K).card ≤ budget / (K + 1) := by
  classical
  apply (Nat.le_div_iff_mul_le (Nat.zero_lt_succ K)).2
  exact (badPoints_card_mul_le_sum points fiberWeight K).trans hbudget

private theorem goodPoints_card_add_badPoints_card {α : Type*}
    (points : Finset α) (fiberWeight : α → ℕ) (K : ℕ) :
    (goodPoints points fiberWeight K).card +
      (badPoints points fiberWeight K).card = points.card := by
  classical
  simpa only [goodPoints, badPoints, not_le] using
      (Finset.card_filter_add_card_filter_not (s := points) (fun p => fiberWeight p ≤ K))

private theorem goodPoints_card_lower_bound {α : Type*}
    (points : Finset α) (fiberWeight : α → ℕ) (K budget : ℕ)
    (hbudget : (∑ p ∈ points, fiberWeight p) ≤ budget) :
    points.card - budget / (K + 1) ≤
      (goodPoints points fiberWeight K).card := by
  classical
  have hbad := badPoints_card_le_div points fiberWeight K budget hbudget
  have hpartition := goodPoints_card_add_badPoints_card points fiberWeight K
  omega

end

section

open Finset Matrix Polynomial

private def polynomialHankel {K : Type*} [Field K]
    (moments : ℕ → K[X]) (h : ℕ) : Matrix (Fin h) (Fin h) K[X] :=
  Matrix.of fun i j => moments (i.val + j.val)

private noncomputable def leadingHankelDet {K : Type*} [Field K]
    (moments : ℕ → K[X]) (h : ℕ) : K[X] :=
  (polynomialHankel moments h).det

private theorem card_hankel_zero_points_le_natDegree
    {K : Type*} [Field K] [DecidableEq K]
    (moments : ℕ → K[X]) (h : ℕ)
    (points : Finset K)
    (hdet : leadingHankelDet moments h ≠ 0) :
    (points.filter fun p => (leadingHankelDet moments h).eval p = 0).card ≤
      (leadingHankelDet moments h).natDegree := by
  classical
  let d := leadingHankelDet moments h
  have hd : d ≠ 0 := hdet
  have hsubset : (points.filter fun p => d.eval p = 0) ⊆ d.roots.toFinset := by
    intro p hp
    have heval : d.eval p = 0 := (Finset.mem_filter.mp hp).2
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd).mpr heval)
  calc
    (points.filter fun p => d.eval p = 0).card ≤ d.roots.toFinset.card :=
      Finset.card_le_card hsubset
    _ ≤ d.roots.card := Multiset.toFinset_card_le _
    _ ≤ d.natDegree := Polynomial.card_roots' d

private theorem leadingHankelDet_zero {K : Type*} [Field K]
    (moments : ℕ → K[X]) : leadingHankelDet moments 0 = 1 := by
  simp only [leadingHankelDet, polynomialHankel, det_fin_zero]

private noncomputable def nonzeroHankelRanks {K : Type*} [Field K]
    (moments : ℕ → K[X]) (rankBound : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (rankBound + 1)).filter
    fun h => leadingHankelDet moments h ≠ 0

private theorem nonzeroHankelRanks_nonempty {K : Type*} [Field K]
    (moments : ℕ → K[X]) (rankBound : ℕ) :
    (nonzeroHankelRanks moments rankBound).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp only [nonzeroHankelRanks, ne_eq, mem_filter, mem_range, lt_add_iff_pos_left,
      Order.lt_add_one_iff,
      zero_le, leadingHankelDet_zero, one_ne_zero, not_false_eq_true, and_self]

private noncomputable def maximalLeadingHankelRank {K : Type*} [Field K]
    (moments : ℕ → K[X]) (rankBound : ℕ) : ℕ :=
  (nonzeroHankelRanks moments rankBound).max'
    (nonzeroHankelRanks_nonempty moments rankBound)

private theorem maximalLeadingHankelRank_mem {K : Type*} [Field K]
    (moments : ℕ → K[X]) (rankBound : ℕ) :
    maximalLeadingHankelRank moments rankBound ≤ rankBound ∧
      leadingHankelDet moments
        (maximalLeadingHankelRank moments rankBound) ≠ 0 := by
  classical
  have hmem := Finset.max'_mem
    (nonzeroHankelRanks moments rankBound)
    (nonzeroHankelRanks_nonempty moments rankBound)
  change maximalLeadingHankelRank moments rankBound ∈
    nonzeroHankelRanks moments rankBound at hmem
  have hf := Finset.mem_filter.mp (show
    maximalLeadingHankelRank moments rankBound ∈
      (Finset.range (rankBound + 1)).filter
        (fun h => leadingHankelDet moments h ≠ 0) from hmem)
  exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hf.1), hf.2⟩

private theorem leadingHankelDet_eq_zero_of_maximal_lt {K : Type*} [Field K]
    (moments : ℕ → K[X]) (rankBound h : ℕ)
    (hh : h ≤ rankBound)
    (hmax : maximalLeadingHankelRank moments rankBound < h) :
    leadingHankelDet moments h = 0 := by
  classical
  by_contra hne
  have hmem : h ∈ nonzeroHankelRanks moments rankBound := by
    change h ∈ (Finset.range (rankBound + 1)).filter
      (fun r => leadingHankelDet moments r ≠ 0)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hh), hne⟩
  have hle : h ≤ maximalLeadingHankelRank moments rankBound := by
    simpa only [maximalLeadingHankelRank] using (Finset.le_max' (nonzeroHankelRanks moments
        rankBound) h hmem)
  omega

private theorem card_good_nonzero_hankel_lower_bound
    {K : Type*} [Field K] [DecidableEq K]
    (moments : ℕ → K[X]) (h : ℕ)
    (points : Finset K) (fiberWeight : K → ℕ)
    (supportBound budget : ℕ)
    (hbudget : (∑ p ∈ points, fiberWeight p) ≤ budget)
    (hdet : leadingHankelDet moments h ≠ 0) :
    points.card - budget / (supportBound + 1) -
        (leadingHankelDet moments h).natDegree ≤
      ((goodPoints points fiberWeight supportBound).filter fun p =>
        (leadingHankelDet moments h).eval p ≠ 0).card := by
  classical
  let G := goodPoints points fiberWeight supportBound
  let d := leadingHankelDet moments h
  have hgood : points.card - budget / (supportBound + 1) ≤ G.card :=
    goodPoints_card_lower_bound points fiberWeight supportBound budget hbudget
  have hzero : (G.filter fun p => d.eval p = 0).card ≤ d.natDegree :=
    card_hankel_zero_points_le_natDegree moments h G hdet
  have hpartition :
      (G.filter fun p => d.eval p ≠ 0).card +
        (G.filter fun p => d.eval p = 0).card = G.card := by
    simpa only [ne_eq, Decidable.not_not] using
        (Finset.card_filter_add_card_filter_not (s := G) (fun p => d.eval p ≠ 0))
  change points.card - budget / (supportBound + 1) - d.natDegree ≤
    (G.filter fun p => d.eval p ≠ 0).card
  omega

end

section

open scoped BigOperators
open Matrix Finset Polynomial

private def powerSumHankel {R : Type*} [CommRing R] {n : ℕ}
    (roots : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ∑ k : Fin n, roots k ^ (i.val + j.val)

private theorem powerSumHankel_det_eq_vandermonde_det_sq
    {R : Type*} [CommRing R] {n : ℕ} (roots : Fin n → R) :
    (powerSumHankel roots).det = (Matrix.vandermonde roots).det ^ 2 := by
  exact hankel_det_eq_vandermonde_det_sq roots

private theorem powerSumHankel_det_ne_zero
    {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {roots : Fin n → R} (hroots : Function.Injective roots) :
    (powerSumHankel roots).det ≠ 0 := by
  exact hankel_det_ne_zero_of_injective hroots

private def shiftedPowerSumVector
    {K : Type*} [Field K] {h : ℕ} (roots : Fin h → K) : Fin h → K :=
  fun i => -(∑ j : Fin h, roots j ^ (i.val + h))

private def recoveredHankelCoefficients
    {K : Type*} [Field K] {h : ℕ} (roots : Fin h → K) : Fin h → K :=
  (powerSumHankel roots)⁻¹.mulVec (shiftedPowerSumVector roots)

private theorem powerSumHankel_mul_recoveredCoefficients
    {K : Type*} [Field K] {h : ℕ}
    (roots : Fin h → K) (hroots : Function.Injective roots) :
    (powerSumHankel roots).mulVec
        (recoveredHankelCoefficients roots) =
      shiftedPowerSumVector roots := by
  unfold recoveredHankelCoefficients
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv]
  · exact Matrix.one_mulVec _
  · exact isUnit_iff_ne_zero.mpr (powerSumHankel_det_ne_zero hroots)

private theorem recoveredHankelCoefficients_unique
    {K : Type*} [Field K] {h : ℕ}
    (roots : Fin h → K) (hroots : Function.Injective roots)
    (coefficients : Fin h → K)
    (hcoefficients : (powerSumHankel roots).mulVec coefficients =
      shiftedPowerSumVector roots) :
    coefficients = recoveredHankelCoefficients roots := by
  have hzero :
      (powerSumHankel roots).mulVec
        (coefficients - recoveredHankelCoefficients roots) = 0 := by
    rw [Matrix.mulVec_sub, hcoefficients,
      powerSumHankel_mul_recoveredCoefficients roots hroots, sub_self]
  have hcoeff : coefficients - recoveredHankelCoefficients roots = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero
      (powerSumHankel_det_ne_zero hroots) hzero
  exact sub_eq_zero.mp hcoeff

variable {K : Type*} [Field K]

/-- GapCVP reduction support. -/
def rootMoment {h : ℕ} (roots : Fin h → K) (j : ℕ) : K :=
  ∑ i : Fin h, roots i ^ j

/-- GapCVP reduction support. -/
def rootSupportPolynomial
    {h : ℕ} (roots : Fin h → K) : K[X] :=
  ∏ i : Fin h, (Polynomial.X - Polynomial.C (roots i))

private theorem rootSupportPolynomial_monic
    {h : ℕ} (roots : Fin h → K) :
    (rootSupportPolynomial roots).Monic := by
  classical
  simpa only [rootSupportPolynomial] using Polynomial.monic_prod_X_sub_C roots (Finset.univ :
      Finset (Fin h))

private theorem rootSupportPolynomial_natDegree
    {h : ℕ} (roots : Fin h → K) :
    (rootSupportPolynomial roots).natDegree = h := by
  classical
  simp only [rootSupportPolynomial, mem_univ, monic_X_sub_C, imp_self, implies_true,
      natDegree_prod_of_monic,
      natDegree_sub_C, natDegree_X, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

private theorem rootSupportPolynomial_eval_root
    {h : ℕ} (roots : Fin h → K) (i : Fin h) :
    (rootSupportPolynomial roots).eval (roots i) = 0 := by
  classical
  rw [rootSupportPolynomial, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [eval_sub, eval_X, eval_C, sub_self])

private theorem rootMoment_recurrence
    {h n : ℕ} (roots : Fin h → K)
    (polynomial : K[X])
    (hdegree : polynomial.natDegree < n)
    (hroots : ∀ i : Fin h, polynomial.eval (roots i) = 0)
    (j : ℕ) :
    ∑ l ∈ Finset.range n,
      polynomial.coeff l * rootMoment roots (j + l) = 0 := by
  classical
  calc
    ∑ l ∈ Finset.range n,
        polynomial.coeff l * rootMoment roots (j + l)
        = ∑ i : Fin h, ∑ l ∈ Finset.range n,
            polynomial.coeff l * roots i ^ (j + l) := by
              simp only [rootMoment, Finset.mul_sum]
              rw [Finset.sum_comm]
    _ = ∑ i : Fin h, roots i ^ j * polynomial.eval (roots i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Polynomial.eval_eq_sum_range' hdegree]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          rw [pow_add]
          ring
    _ = 0 := by simp only [hroots, mul_zero, sum_const_zero]

private theorem rootSupportPolynomial_moment_recurrence
    {h : ℕ} (roots : Fin h → K) (j : ℕ) :
    ∑ l ∈ Finset.range (h + 1),
      (rootSupportPolynomial roots).coeff l * rootMoment roots (j + l) = 0 := by
  apply rootMoment_recurrence roots (rootSupportPolynomial roots)
  · rw [rootSupportPolynomial_natDegree]
    omega
  · exact rootSupportPolynomial_eval_root roots

private def rootSupportCoefficients
    {h : ℕ} (roots : Fin h → K) : Fin h → K :=
  fun i => (rootSupportPolynomial roots).coeff i.val

private theorem powerSumHankel_mul_rootSupportCoefficients
    {h : ℕ} (roots : Fin h → K) :
    (powerSumHankel roots).mulVec (rootSupportCoefficients roots) =
      shiftedPowerSumVector roots := by
  classical
  funext i
  have hrec := rootSupportPolynomial_moment_recurrence roots i.val
  rw [Finset.sum_range_succ] at hrec
  have hleading : (rootSupportPolynomial roots).coeff h = 1 := by
    have hm := (rootSupportPolynomial_monic roots).leadingCoeff
    simpa only [Polynomial.leadingCoeff,
      rootSupportPolynomial_natDegree] using hm
  rw [hleading, one_mul] at hrec
  change
    (∑ j : Fin h,
      rootMoment roots (i.val + j.val) *
        (rootSupportPolynomial roots).coeff j.val) =
      -rootMoment roots (i.val + h)
  have hsum :
      (∑ j : Fin h,
        rootMoment roots (i.val + j.val) *
          (rootSupportPolynomial roots).coeff j.val) =
        ∑ l ∈ Finset.range h,
          (rootSupportPolynomial roots).coeff l *
            rootMoment roots (i.val + l) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro l hl
    have hlt : l < h := Finset.mem_range.mp hl
    simp only [hlt, ↓reduceDIte, mul_comm]
  rw [hsum]
  exact eq_neg_of_add_eq_zero_left hrec

private theorem recoveredHankelCoefficients_eq_rootSupportCoefficients
    {h : ℕ} (roots : Fin h → K)
    (hinj : Function.Injective roots) :
    recoveredHankelCoefficients roots = rootSupportCoefficients roots := by
  symm
  exact recoveredHankelCoefficients_unique roots hinj
    (rootSupportCoefficients roots)
    (powerSumHankel_mul_rootSupportCoefficients roots)

end

section

open scoped BigOperators
open Polynomial Matrix Finset

variable {K : Type*} [Field K]

/-- GapCVP reduction support. -/
def genericHankelDenominator (h : ℕ) (moments : ℕ → K[X]) : K[X] :=
  leadingHankelDet moments h

private def genericShiftedMoments (h : ℕ) (moments : ℕ → K[X]) :
    Fin h → K[X] :=
  fun i => -moments (i.val + h)

private def genericHankelNumerator (h : ℕ) (moments : ℕ → K[X]) :
    Fin h → K[X] :=
  (polynomialHankel moments h).cramer (genericShiftedMoments h moments)

private theorem polynomial_matrix_det_natDegree_le
    {h : ℕ} (matrix : Matrix (Fin h) (Fin h) K[X]) (D : ℕ)
    (hdegree : ∀ i j, (matrix i j).natDegree ≤ D) :
    matrix.det.natDegree ≤ h * D := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro permutation _
  calc
    (Equiv.Perm.sign permutation •
        ∏ i : Fin h, matrix (permutation i) i).natDegree
        ≤ (∏ i : Fin h, matrix (permutation i) i).natDegree :=
          Polynomial.natDegree_smul_le _ _
    _ ≤ ∑ i : Fin h, (matrix (permutation i) i).natDegree :=
          Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin h, D := by
          exact Finset.sum_le_sum
            (fun i _ => hdegree (permutation i) i)
    _ = h * D := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

private theorem genericHankelDenominator_natDegree_le
    {h : ℕ} (moments : ℕ → K[X]) (D : ℕ)
    (hdegree : ∀ j, j < 2 * h → (moments j).natDegree ≤ D) :
    (genericHankelDenominator h moments).natDegree ≤ h * D := by
  apply polynomial_matrix_det_natDegree_le
    (polynomialHankel moments h) D
  intro i j
  exact hdegree (i.val + j.val) (by omega)

private theorem genericHankelDenominator_natDegree_le_sharp
    {h : ℕ} (moments : ℕ → K[X]) (d : ℕ)
    (hdegree : ∀ j, j < 2 * h → (moments j).natDegree ≤ d * j) :
    (genericHankelDenominator h moments).natDegree ≤ d * h * (h - 1) := by
  classical
  unfold genericHankelDenominator leadingHankelDet
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro permutation _
  calc
    (Equiv.Perm.sign permutation •
      ∏ i : Fin h, polynomialHankel moments h (permutation i) i).natDegree
        ≤ (∏ i : Fin h,
            polynomialHankel moments h (permutation i) i).natDegree :=
          Polynomial.natDegree_smul_le _ _
    _ ≤ ∑ i : Fin h,
          (polynomialHankel moments h (permutation i) i).natDegree :=
          Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i : Fin h, d * ((permutation i).val + i.val) := by
          apply Finset.sum_le_sum
          intro i _
          exact hdegree ((permutation i).val + i.val) (by omega)
    _ = d * h * (h - 1) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          rw [Equiv.sum_comp permutation (fun i : Fin h => i.val)]
          rw [← mul_add, ← mul_two]
          rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) h]
          rw [Finset.sum_range_id_mul_two]
          simp only [mul_assoc]

private theorem genericHankelNumerator_natDegree_le
    {h : ℕ} (moments : ℕ → K[X]) (D : ℕ)
    (hdegree : ∀ j, j < 2 * h → (moments j).natDegree ≤ D)
    (i : Fin h) :
    (genericHankelNumerator h moments i).natDegree ≤ h * D := by
  classical
  unfold genericHankelNumerator
  rw [Matrix.cramer_apply]
  apply polynomial_matrix_det_natDegree_le _ D
  intro row column
  by_cases hcolumn : column = i
  · subst column
    rw [Matrix.updateCol_self]
    change (-moments (row.val + h)).natDegree ≤ D
    rw [Polynomial.natDegree_neg]
    exact hdegree (row.val + h) (by omega)
  · rw [Matrix.updateCol_ne hcolumn]
    exact hdegree (row.val + column.val) (by omega)

private theorem polynomialHankel_specializes
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      (moments j).eval point = rootMoment roots j) :
    (polynomialHankel moments h).map (Polynomial.evalRingHom point) =
      powerSumHankel roots := by
  ext i j
  change (moments (i.val + j.val)).eval point =
    ∑ r : Fin h, roots r ^ (i.val + j.val)
  exact hmoments (i.val + j.val) (by omega)

private theorem genericHankelDenominator_eval
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      (moments j).eval point = rootMoment roots j) :
    (genericHankelDenominator h moments).eval point =
      (powerSumHankel roots).det := by
  calc
    (genericHankelDenominator h moments).eval point
        = ((polynomialHankel moments h).map
            (Polynomial.evalRingHom point)).det := by
              simpa only [genericHankelDenominator, leadingHankelDet, coe_evalRingHom,
                  RingHom.mapMatrix_apply] using
                  ((Polynomial.evalRingHom point).map_det (polynomialHankel moments h))
    _ = (powerSumHankel roots).det := by
      rw [polynomialHankel_specializes moments point roots hmoments]

private theorem genericHankelDenominator_ne_zero_of_good_point
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K) (hinj : Function.Injective roots)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      (moments j).eval point = rootMoment roots j) :
    genericHankelDenominator h moments ≠ 0 := by
  intro hzero
  have heval := genericHankelDenominator_eval moments point roots hmoments
  rw [hzero, Polynomial.eval_zero] at heval
  exact powerSumHankel_det_ne_zero hinj heval.symm

private def genericHankelCoefficient
    (h : ℕ) (moments : ℕ → K[X]) (i : Fin h) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (genericHankelNumerator h moments i) /
    algebraMap K[X] (RatFunc K) (genericHankelDenominator h moments)

/-- GapCVP reduction support. -/
def maximalGenericHankelRank
    (moments : ℕ → K[X]) (rankBound : ℕ) : ℕ :=
  maximalLeadingHankelRank moments rankBound

theorem maximalGenericHankelRank_spec
    (moments : ℕ → K[X]) (rankBound : ℕ) :
    maximalGenericHankelRank moments rankBound ≤ rankBound ∧
      genericHankelDenominator
        (maximalGenericHankelRank moments rankBound) moments ≠ 0 := by
  exact maximalLeadingHankelRank_mem moments rankBound

private theorem genericHankelDenominator_eq_zero_of_maximal_lt
    (moments : ℕ → K[X]) (rankBound h : ℕ)
    (hh : h ≤ rankBound)
    (hmax : maximalGenericHankelRank moments rankBound < h) :
    genericHankelDenominator h moments = 0 := by
  exact leadingHankelDet_eq_zero_of_maximal_lt
    moments rankBound h hh hmax

private theorem card_good_nonzero_genericHankel_lower_bound
    [DecidableEq K] (moments : ℕ → K[X]) (h : ℕ)
    (points : Finset K) (fiberWeight : K → ℕ)
    (supportBound budget : ℕ)
    (hbudget : (∑ point ∈ points, fiberWeight point) ≤ budget)
    (hdet : genericHankelDenominator h moments ≠ 0) :
    points.card - budget / (supportBound + 1) -
        (genericHankelDenominator h moments).natDegree ≤
      ((goodPoints points fiberWeight supportBound).filter fun point =>
        (genericHankelDenominator h moments).eval point ≠ 0).card := by
  exact card_good_nonzero_hankel_lower_bound
    moments h points fiberWeight supportBound budget hbudget hdet

end

section

open Finset Polynomial

/-- GapCVP reduction support. -/
noncomputable def familySplittingPolynomial
    {F ι : Type*} [Field F] [Fintype ι]
    (family : ι → F[X]) : F[X] :=
  ∏ i : ι, family i

private abbrev CommonSplittingField
    {F ι : Type*} [Field F] [Fintype ι]
    (family : ι → F[X]) :=
  (familySplittingPolynomial family).SplittingField

private theorem familySplittingPolynomial_ne_zero
    {F ι : Type*} [Field F] [Fintype ι]
    (family : ι → F[X])
    (hnonzero : ∀ i, family i ≠ 0) :
    familySplittingPolynomial family ≠ 0 := by
  classical
  unfold familySplittingPolynomial
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hnonzero i)

private theorem commonSplittingField_splits
    {F ι : Type*} [Field F] [Fintype ι]
    (family : ι → F[X])
    (hnonzero : ∀ i, family i ≠ 0) (i : ι) :
    ((family i).map
      (algebraMap F (CommonSplittingField family))).Splits := by
  classical
  have hdiv : family i ∣ familySplittingPolynomial family := by
    unfold familySplittingPolynomial
    exact Finset.dvd_prod_of_mem family (Finset.mem_univ i)
  apply (Polynomial.SplittingField.splits
    (familySplittingPolynomial family)).of_dvd
  · exact Polynomial.map_ne_zero
      (familySplittingPolynomial_ne_zero family hnonzero)
  · exact Polynomial.map_dvd
      (algebraMap F (CommonSplittingField family)) hdiv

/-- GapCVP reduction support. -/
noncomputable abbrev CommonAmbientSplittingField {F : Type*} [Field F]
    {t : ℕ} (polynomials : Fin t → F[X]) :=
  CommonSplittingField polynomials

private noncomputable abbrev CommonSeparableSplittingField {F : Type*} [Field F]
    {t : ℕ} (polynomials : Fin t → F[X]) :=
  separableClosure F (CommonAmbientSplittingField polynomials)

private theorem commonAmbientSplittingField_splits {F : Type*} [Field F]
    {t : ℕ} (polynomials : Fin t → F[X])
    (hnonzero : ∀ i, polynomials i ≠ 0) (i : Fin t) :
    ((polynomials i).map
      (algebraMap F (CommonAmbientSplittingField polynomials))).Splits :=
  commonSplittingField_splits polynomials hnonzero i

private theorem separable_of_mem_separable_rootSet
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : F[X]) (hseparable : p.Separable) {root : E}
    (hroot : root ∈ p.rootSet E) : IsSeparable F root := by
  exact hseparable.of_dvd
    (minpoly.dvd F root (Polynomial.aeval_eq_zero_of_mem_rootSet hroot))

private theorem commonSeparableSplittingField_splits
    {F : Type*} [Field F] {t : ℕ}
    (polynomials : Fin t → F[X])
    (hnonzero : ∀ i, polynomials i ≠ 0)
    (hseparable : ∀ i, (polynomials i).Separable) (i : Fin t) :
    ((polynomials i).map
      (algebraMap F (CommonSeparableSplittingField polynomials))).Splits := by
  apply IntermediateField.splits_of_splits
    (commonAmbientSplittingField_splits polynomials hnonzero i)
  intro root hroot
  exact separable_of_mem_separable_rootSet
    (polynomials i) (hseparable i) hroot

end

section

open scoped BigOperators
open Polynomial Matrix Finset

variable {K : Type*} [Field K]

private def genericMomentSupportPolynomial (h : ℕ) (moments : ℕ → K[X]) :
    (RatFunc K)[X] :=
  Polynomial.X ^ h +
    ∑ i : Fin h,
      Polynomial.C (genericHankelCoefficient h moments i) *
        Polynomial.X ^ i.val

private def clearedGenericMomentSupportPolynomial (h : ℕ) (moments : ℕ → K[X]) :
    (K[X])[X] :=
  Polynomial.C (genericHankelDenominator h moments) * Polynomial.X ^ h +
    ∑ i : Fin h,
      Polynomial.C (genericHankelNumerator h moments i) *
        Polynomial.X ^ i.val

private theorem genericMomentSupportPolynomial_monic
    (h : ℕ) (moments : ℕ → K[X]) :
    (genericMomentSupportPolynomial h moments).Monic := by
  unfold genericMomentSupportPolynomial
  exact Polynomial.monic_X_pow_add
    (Polynomial.degree_sum_fin_lt
      (fun i : Fin h => genericHankelCoefficient h moments i))

private def specializedGenericHankelCoefficient
    (h : ℕ) (moments : ℕ → K[X]) (point : K) (i : Fin h) : K :=
  (genericHankelNumerator h moments i).eval point /
    (genericHankelDenominator h moments).eval point

private def specializedGenericMomentSupportPolynomial
    (h : ℕ) (moments : ℕ → K[X]) (point : K) : K[X] :=
  Polynomial.X ^ h +
    ∑ i : Fin h,
      Polynomial.C
          (specializedGenericHankelCoefficient h moments point i) *
        Polynomial.X ^ i.val

private theorem genericHankelNumerator_eval_eq_cramer
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      (moments j).eval point = rootMoment roots j)
    (i : Fin h) :
    (genericHankelNumerator h moments i).eval point =
      (powerSumHankel roots).cramer
        (shiftedPowerSumVector roots) i := by
  calc
    (genericHankelNumerator h moments i).eval point =
        (((polynomialHankel moments h).updateCol i
          (genericShiftedMoments h moments)).map
            (Polynomial.evalRingHom point)).det := by
      simpa only [genericHankelNumerator, cramer_apply, coe_evalRingHom, RingHom.mapMatrix_apply]
          using
          (Polynomial.evalRingHom point).map_det ((polynomialHankel moments h).updateCol i
              (genericShiftedMoments h moments))
    _ = (powerSumHankel roots).cramer
          (shiftedPowerSumVector roots) i := by
      rw [Matrix.map_updateCol]
      rw [polynomialHankel_specializes moments point roots hmoments]
      have hshift :
          (Polynomial.evalRingHom point) ∘
              genericShiftedMoments h moments =
            shiftedPowerSumVector roots := by
        funext row
        change (-(moments (row.val + h))).eval point =
          -(rootMoment roots (row.val + h))
        simpa only [eval_neg, neg_inj] using congrArg Neg.neg (hmoments (row.val + h) (by omega))
      rw [hshift, Matrix.cramer_apply]

private theorem genericHankelNumerator_eval_eq_det_mul_rootSupportCoefficient
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K) (hinjective : Function.Injective roots)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      (moments j).eval point = rootMoment roots j)
    (i : Fin h) :
    (genericHankelNumerator h moments i).eval point =
      (genericHankelDenominator h moments).eval point *
        rootSupportCoefficients roots i := by
  have hdet : (powerSumHankel roots).det ≠ 0 :=
    powerSumHankel_det_ne_zero hinjective
  calc
    (genericHankelNumerator h moments i).eval point =
        (powerSumHankel roots).cramer
          (shiftedPowerSumVector roots) i :=
      genericHankelNumerator_eval_eq_cramer
        moments point roots hmoments i
    _ = (powerSumHankel roots).det *
          recoveredHankelCoefficients roots i := by
      symm
      simpa only [recoveredHankelCoefficients, Pi.smul_apply, smul_eq_mul] using
          congrFun
            (Matrix.det_smul_inv_mulVec_eq_cramer (powerSumHankel roots) (shiftedPowerSumVector
                roots)
              (isUnit_iff_ne_zero.mpr hdet))
            i
    _ = (powerSumHankel roots).det *
          rootSupportCoefficients roots i := by
      rw [recoveredHankelCoefficients_eq_rootSupportCoefficients
        roots hinjective]
    _ = (genericHankelDenominator h moments).eval point *
          rootSupportCoefficients roots i := by
      rw [genericHankelDenominator_eval moments point roots hmoments]

private theorem genericHankelDenominator_eval_ne_zero_of_distinct_fiber
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K) (hinjective : Function.Injective roots)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      (moments j).eval point = rootMoment roots j) :
    (genericHankelDenominator h moments).eval point ≠ 0 := by
  rw [genericHankelDenominator_eval moments point roots hmoments]
  exact powerSumHankel_det_ne_zero hinjective

private theorem specializedGenericHankelCoefficient_eq_rootSupportCoefficient
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K) (hinjective : Function.Injective roots)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      (moments j).eval point = rootMoment roots j)
    (i : Fin h) :
    specializedGenericHankelCoefficient h moments point i =
      rootSupportCoefficients roots i := by
  unfold specializedGenericHankelCoefficient
  rw [genericHankelNumerator_eval_eq_det_mul_rootSupportCoefficient
    moments point roots hinjective hmoments i]
  exact mul_div_cancel_left₀
    (rootSupportCoefficients roots i)
    (genericHankelDenominator_eval_ne_zero_of_distinct_fiber
      moments point roots hinjective hmoments)

private theorem specializedGenericMomentSupportPolynomial_eq_rootSupportPolynomial
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K) (hinjective : Function.Injective roots)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      (moments j).eval point = rootMoment roots j) :
    specializedGenericMomentSupportPolynomial h moments point =
      rootSupportPolynomial roots := by
  unfold specializedGenericMomentSupportPolynomial
  simp_rw [specializedGenericHankelCoefficient_eq_rootSupportCoefficient
    moments point roots hinjective hmoments]
  have hsum :
      (∑ i : Fin h,
        Polynomial.C (rootSupportCoefficients roots i) *
          Polynomial.X ^ i.val) =
        ∑ i ∈ Finset.range h,
          Polynomial.C ((rootSupportPolynomial roots).coeff i) *
            Polynomial.X ^ i := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range.mp hi, ↓reduceDIte, rootSupportCoefficients]
  rw [hsum]
  simpa only [rootSupportPolynomial_natDegree] using (rootSupportPolynomial_monic
      roots).as_sum.symm

private theorem separable_ratFunc_map_of_separable_specialization
    (polynomial : (K[X])[X]) (point : K)
    (hleading : polynomial.leadingCoeff.eval point ≠ 0)
    (hspecial :
      (polynomial.map (Polynomial.evalRingHom point)).Separable) :
    (polynomial.map (algebraMap K[X] (RatFunc K))).Separable := by
  classical
  let evaluation : K[X] →+* K := Polynomial.evalRingHom point
  let embedding : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  let fiber : K[X] := polynomial.map evaluation
  let generic : (RatFunc K)[X] := polynomial.map embedding
  have hinjective : Function.Injective embedding := by
    exact FaithfulSMul.algebraMap_injective K[X] (RatFunc K)
  have hfiberseparable : fiber.Separable := by
    simpa only using hspecial
  have hfiberdegree : fiber.natDegree = polynomial.natDegree := by
    dsimp [fiber]
    apply Polynomial.natDegree_map_of_leadingCoeff_ne_zero evaluation
    exact hleading
  have hderivativedegree :
      fiber.derivative.natDegree ≤ polynomial.derivative.natDegree := by
    dsimp [fiber]
    rw [Polynomial.derivative_map]
    exact Polynomial.natDegree_map_le
  have hfiberleading : fiber.coeff polynomial.natDegree ≠ 0 := by
    intro hzero
    apply hleading
    change evaluation polynomial.leadingCoeff = 0
    have hcoefficient :
        fiber.coeff polynomial.natDegree =
          evaluation polynomial.leadingCoeff := by
      change (polynomial.map evaluation).coeff polynomial.natDegree =
        evaluation (polynomial.coeff polynomial.natDegree)
      exact Polynomial.coeff_map evaluation polynomial.natDegree
    rw [← hcoefficient, hzero]
  have hfiberresultant :
      fiber.resultant fiber.derivative ≠ 0 :=
    Polynomial.resultant_ne_zero fiber fiber.derivative hfiberseparable
  have hfiberfixed :
      fiber.resultant fiber.derivative
        polynomial.natDegree polynomial.derivative.natDegree ≠ 0 := by
    have hfactor := Polynomial.resultant_add_right_deg
      fiber fiber.derivative polynomial.natDegree fiber.derivative.natDegree
      (polynomial.derivative.natDegree - fiber.derivative.natDegree)
      (le_refl fiber.derivative.natDegree)
    rw [Nat.add_sub_of_le hderivativedegree] at hfactor
    rw [hfactor]
    exact mul_ne_zero
      (pow_ne_zero _ hfiberleading)
      (by simpa only [hfiberdegree] using hfiberresultant)
  have hpolynomialresultant :
      polynomial.resultant polynomial.derivative
        polynomial.natDegree polynomial.derivative.natDegree ≠ 0 := by
    intro hzero
    apply hfiberfixed
    calc
      fiber.resultant fiber.derivative
          polynomial.natDegree polynomial.derivative.natDegree =
        evaluation
          (polynomial.resultant polynomial.derivative
            polynomial.natDegree polynomial.derivative.natDegree) := by
        change
          (polynomial.map evaluation).resultant
              (polynomial.map evaluation).derivative
              polynomial.natDegree polynomial.derivative.natDegree =
            evaluation
              (polynomial.resultant polynomial.derivative
                polynomial.natDegree polynomial.derivative.natDegree)
        rw [Polynomial.derivative_map]
        exact Polynomial.resultant_map_map polynomial polynomial.derivative
          polynomial.natDegree polynomial.derivative.natDegree evaluation
      _ = 0 := by simp only [hzero, map_zero]
  have hgenericfixed :
      generic.resultant generic.derivative
        polynomial.natDegree polynomial.derivative.natDegree ≠ 0 := by
    intro hzero
    apply hpolynomialresultant
    apply hinjective
    have hmap :
        embedding
          (polynomial.resultant polynomial.derivative
            polynomial.natDegree polynomial.derivative.natDegree) = 0 := by
      calc
        embedding
            (polynomial.resultant polynomial.derivative
              polynomial.natDegree polynomial.derivative.natDegree) =
          generic.resultant generic.derivative
            polynomial.natDegree polynomial.derivative.natDegree := by
          symm
          change
            (polynomial.map embedding).resultant
                (polynomial.map embedding).derivative
                polynomial.natDegree polynomial.derivative.natDegree =
              embedding
                (polynomial.resultant polynomial.derivative
                  polynomial.natDegree polynomial.derivative.natDegree)
          rw [Polynomial.derivative_map]
          exact Polynomial.resultant_map_map polynomial polynomial.derivative
            polynomial.natDegree polynomial.derivative.natDegree embedding
        _ = 0 := hzero
    simpa only [map_zero] using hmap
  have hgenericdegree : generic.natDegree = polynomial.natDegree := by
    exact Polynomial.natDegree_map_eq_of_injective hinjective polynomial
  have hgenericderivativedegree :
      generic.derivative.natDegree = polynomial.derivative.natDegree := by
    dsimp [generic]
    rw [Polynomial.derivative_map]
    exact Polynomial.natDegree_map_eq_of_injective hinjective
      polynomial.derivative
  have hgenericresultant : generic.resultant generic.derivative ≠ 0 := by
    simpa only [hgenericdegree, hgenericderivativedegree] using hgenericfixed
  have hgenericnonzero : generic ≠ 0 := by
    intro hzero
    have hpolynomialzero : polynomial = 0 :=
      (Polynomial.map_eq_zero_iff hinjective).mp hzero
    apply hleading
    simp only [hpolynomialzero, leadingCoeff_zero, eval_zero]
  have hgenericseparable : generic.Separable := by
    apply (Polynomial.separable_def generic).2
    by_contra hnot
    apply hgenericresultant
    exact Polynomial.resultant_eq_zero_iff.mpr
      ⟨Or.inl hgenericnonzero, hnot⟩
  exact hgenericseparable

private theorem clearedGenericMomentSupportPolynomial_natDegree_le
    (h : ℕ) (moments : ℕ → K[X]) :
    (clearedGenericMomentSupportPolynomial h moments).natDegree ≤ h := by
  classical
  unfold clearedGenericMomentSupportPolynomial
  apply Polynomial.natDegree_add_le_of_degree_le
  · calc
      (Polynomial.C (genericHankelDenominator h moments) *
          (Polynomial.X : (K[X])[X]) ^ h).natDegree ≤
        ((Polynomial.X : (K[X])[X]) ^ h).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ = h := Polynomial.natDegree_X_pow h
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    calc
      (Polynomial.C (genericHankelNumerator h moments i) *
          (Polynomial.X : (K[X])[X]) ^ i.val).natDegree ≤
        ((Polynomial.X : (K[X])[X]) ^ i.val).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ = i.val := Polynomial.natDegree_X_pow i.val
      _ ≤ h := Nat.le_of_lt i.isLt

private theorem clearedGenericMomentSupportPolynomial_coeff_rank
    (h : ℕ) (moments : ℕ → K[X]) :
    (clearedGenericMomentSupportPolynomial h moments).coeff h =
      genericHankelDenominator h moments := by
  classical
  unfold clearedGenericMomentSupportPolynomial
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  simp only [ite_true, mul_one]
  have hsum :
      (∑ i : Fin h,
        Polynomial.C (genericHankelNumerator h moments i) *
          (Polynomial.X : (K[X])[X]) ^ i.val).coeff h = 0 := by
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro i _
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      ite_eq_right (Nat.ne_of_gt i.isLt), mul_zero]
  rw [hsum, add_zero]

private theorem clearedGenericMomentSupportPolynomial_leadingCoeff
    (h : ℕ) (moments : ℕ → K[X])
    (hdenominator : genericHankelDenominator h moments ≠ 0) :
    (clearedGenericMomentSupportPolynomial h moments).leadingCoeff =
      genericHankelDenominator h moments := by
  have hcoefficient := clearedGenericMomentSupportPolynomial_coeff_rank
    h moments
  have hdegree :
      (clearedGenericMomentSupportPolynomial h moments).natDegree = h :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (clearedGenericMomentSupportPolynomial_natDegree_le h moments)
      (by rw [hcoefficient]; exact hdenominator)
  simpa only [Polynomial.leadingCoeff, hdegree] using hcoefficient

private theorem clearedGenericMomentSupportPolynomial_specializes
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K) (hinjective : Function.Injective roots)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      (moments j).eval point = rootMoment roots j) :
    (clearedGenericMomentSupportPolynomial h moments).map
        (Polynomial.evalRingHom point) =
      Polynomial.C ((genericHankelDenominator h moments).eval point) *
        rootSupportPolynomial roots := by
  classical
  have hrootexpansion :
      rootSupportPolynomial roots =
        (Polynomial.X : K[X]) ^ h +
          ∑ i : Fin h,
            Polynomial.C (rootSupportCoefficients roots i) *
              Polynomial.X ^ i.val := by
    calc
      rootSupportPolynomial roots =
        specializedGenericMomentSupportPolynomial h moments point :=
          (specializedGenericMomentSupportPolynomial_eq_rootSupportPolynomial
            moments point roots hinjective hmoments).symm
      _ = (Polynomial.X : K[X]) ^ h +
          ∑ i : Fin h,
            Polynomial.C (rootSupportCoefficients roots i) *
              Polynomial.X ^ i.val := by
        unfold specializedGenericMomentSupportPolynomial
        simp_rw [specializedGenericHankelCoefficient_eq_rootSupportCoefficient
          moments point roots hinjective hmoments]
  rw [hrootexpansion]
  unfold clearedGenericMomentSupportPolynomial
  simp only [Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum]
  rw [mul_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) rfl ?_
  apply Finset.sum_congr rfl
  intro i _
  change
    Polynomial.C ((genericHankelNumerator h moments i).eval point) *
        (Polynomial.X : K[X]) ^ i.val =
      Polynomial.C ((genericHankelDenominator h moments).eval point) *
        (Polynomial.C (rootSupportCoefficients roots i) *
          Polynomial.X ^ i.val)
  rw [genericHankelNumerator_eval_eq_det_mul_rootSupportCoefficient
    moments point roots hinjective hmoments i]
  rw [Polynomial.C_mul]
  ring

private theorem clearedGenericMomentSupportPolynomial_map_ratFunc
    (h : ℕ) (moments : ℕ → K[X])
    (hdenominator : genericHankelDenominator h moments ≠ 0) :
    (clearedGenericMomentSupportPolynomial h moments).map
        (algebraMap K[X] (RatFunc K)) =
      Polynomial.C
        (algebraMap K[X] (RatFunc K)
          (genericHankelDenominator h moments)) *
        genericMomentSupportPolynomial h moments := by
  classical
  have hdenominator' :
      algebraMap K[X] (RatFunc K)
        (genericHankelDenominator h moments) ≠ 0 := by
    intro hzero
    apply hdenominator
    apply FaithfulSMul.algebraMap_injective K[X] (RatFunc K)
    simpa only [map_zero, FaithfulSMul.algebraMap_eq_zero_iff] using hzero
  unfold clearedGenericMomentSupportPolynomial
    genericMomentSupportPolynomial
  simp only [Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum]
  rw [mul_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) rfl ?_
  apply Finset.sum_congr rfl
  intro i _
  have hcoefficient :
      algebraMap K[X] (RatFunc K)
          (genericHankelDenominator h moments) *
        genericHankelCoefficient h moments i =
      algebraMap K[X] (RatFunc K)
        (genericHankelNumerator h moments i) := by
    unfold genericHankelCoefficient
    field_simp [hdenominator']
  rw [← hcoefficient, Polynomial.C_mul]
  ring

private theorem genericMomentSupportPolynomial_separable
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K) (hinjective : Function.Injective roots)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      (moments j).eval point = rootMoment roots j) :
    (genericMomentSupportPolynomial h moments).Separable := by
  have hnonzero : genericHankelDenominator h moments ≠ 0 :=
    genericHankelDenominator_ne_zero_of_good_point
      moments point roots hinjective hmoments
  have hfibernonzero :
      (genericHankelDenominator h moments).eval point ≠ 0 :=
    genericHankelDenominator_eval_ne_zero_of_distinct_fiber
      moments point roots hinjective hmoments
  have hspecial :
      ((clearedGenericMomentSupportPolynomial h moments).map
        (Polynomial.evalRingHom point)).Separable := by
    rw [clearedGenericMomentSupportPolynomial_specializes
      moments point roots hinjective hmoments]
    rw [mul_comm]
    apply (Polynomial.separable_prod_X_sub_C_iff.mpr hinjective).mul_unit
    exact Polynomial.isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr hfibernonzero)
  have hgeneric := separable_ratFunc_map_of_separable_specialization
    (clearedGenericMomentSupportPolynomial h moments) point
    (by rw [clearedGenericMomentSupportPolynomial_leadingCoeff
      h moments hnonzero]; exact hfibernonzero)
    hspecial
  rw [clearedGenericMomentSupportPolynomial_map_ratFunc
    h moments hnonzero] at hgeneric
  exact hgeneric.of_mul_right

private def finiteSupportRoots (support : Finset K) : Fin support.card → K :=
  fun i => ((Finset.equivFin support).symm i : K)

omit [Field K] in
private theorem finiteSupportRoots_injective (support : Finset K) :
    Function.Injective (finiteSupportRoots support) := by
  intro i j h
  exact (Finset.equivFin support).symm.injective (Subtype.ext h)

private theorem rootMoment_finiteSupportRoots (support : Finset K) (j : ℕ) :
    rootMoment (finiteSupportRoots support) j =
      supportMoment support j := by
  classical
  unfold rootMoment finiteSupportRoots supportMoment
  calc
    (∑ i : Fin support.card,
      ((Finset.equivFin support).symm i : K) ^ j) =
        ∑ a : support, (a : K) ^ j :=
      Equiv.sum_comp (Finset.equivFin support).symm
        (fun a : support => (a : K) ^ j)
    _ = ∑ a ∈ support, a ^ j :=
      (Finset.sum_subtype support (fun _ => Iff.rfl)
        (fun a : K => a ^ j)).symm

private def fiberPowerSumHankel {supportSize : ℕ}
    (rank : ℕ) (roots : Fin supportSize → K) :
    Matrix (Fin rank) (Fin rank) K :=
  fun i j => rootMoment roots (i.val + j.val)

private theorem polynomialHankel_specializes_fiberPowerSumHankel
    {rank supportSize : ℕ}
    (moments : ℕ → K[X]) (point : K)
    (roots : Fin supportSize → K)
    (hmoments : ∀ j : ℕ, j < 2 * rank →
      (moments j).eval point = rootMoment roots j) :
    (polynomialHankel moments rank).map
        (Polynomial.evalRingHom point) =
      fiberPowerSumHankel rank roots := by
  ext i j
  exact hmoments (i.val + j.val) (by omega)

private theorem fiberPowerSumHankel_det_eq_zero_of_support_lt
    {rank supportSize : ℕ}
    (roots : Fin supportSize → K) (hsize : supportSize < rank) :
    (fiberPowerSumHankel rank roots).det = 0 := by
  classical
  by_contra hdet
  let coefficients : Fin rank → K :=
    fun i => (rootSupportPolynomial roots).coeff i.val
  have hkernel :
      (fiberPowerSumHankel rank roots).mulVec coefficients = 0 := by
    funext row
    have hrec := rootMoment_recurrence roots
      (rootSupportPolynomial roots)
      (by simpa only [rootSupportPolynomial_natDegree] using hsize)
      (rootSupportPolynomial_eval_root roots) row.val
    change
      (∑ i : Fin rank,
        rootMoment roots (row.val + i.val) *
          (rootSupportPolynomial roots).coeff i.val) = 0
    rw [Finset.sum_fin_eq_sum_range]
    calc
      (∑ i ∈ Finset.range rank,
        if hi : i < rank then
          rootMoment roots (row.val + i) *
            (rootSupportPolynomial roots).coeff i
        else 0) =
        ∑ i ∈ Finset.range rank,
          (rootSupportPolynomial roots).coeff i *
            rootMoment roots (row.val + i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_range.mp hi, ↓reduceDIte, mul_comm]
      _ = 0 := hrec
  have hcoefficients : coefficients = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hkernel
  have hleading : (rootSupportPolynomial roots).coeff supportSize = 1 := by
    have hm := (rootSupportPolynomial_monic roots).leadingCoeff
    simpa only [Polynomial.leadingCoeff,
      rootSupportPolynomial_natDegree] using hm
  have hzero := congrFun hcoefficients ⟨supportSize, hsize⟩
  change (rootSupportPolynomial roots).coeff supportSize = 0 at hzero
  exact one_ne_zero (hleading.symm.trans hzero)

private theorem genericHankelDenominator_eval_eq_zero_of_smaller_fiber
    {rank supportSize : ℕ}
    (moments : ℕ → K[X]) (point : K)
    (roots : Fin supportSize → K)
    (hsize : supportSize < rank)
    (hmoments : ∀ j : ℕ, j < 2 * rank →
      (moments j).eval point = rootMoment roots j) :
    (genericHankelDenominator rank moments).eval point = 0 := by
  calc
    (genericHankelDenominator rank moments).eval point =
        ((polynomialHankel moments rank).map
          (Polynomial.evalRingHom point)).det := by
      simpa only [genericHankelDenominator, leadingHankelDet, coe_evalRingHom,
          RingHom.mapMatrix_apply] using
          (Polynomial.evalRingHom point).map_det (polynomialHankel moments rank)
    _ = (fiberPowerSumHankel rank roots).det := by
      rw [polynomialHankel_specializes_fiberPowerSumHankel
        moments point roots hmoments]
    _ = 0 := fiberPowerSumHankel_det_eq_zero_of_support_lt roots hsize

private theorem goodFiber_card_eq_maximalGenericHankelRank
    (moments : ℕ → K[X]) (supports : K → Finset K)
    (rankBound momentBudget : ℕ) (point : K)
    (hgood : (supports point).card ≤ rankBound)
    (hbudget : 2 * rankBound ≤ momentBudget + 1)
    (hmoments : ∀ j : ℕ, j ≤ momentBudget →
      (moments j).eval point = supportMoment (supports point) j)
    (hnonsingular :
      (genericHankelDenominator
        (maximalGenericHankelRank moments rankBound) moments).eval point ≠ 0) :
    (supports point).card = maximalGenericHankelRank moments rankBound := by
  have hmax := maximalGenericHankelRank_spec moments rankBound
  apply Nat.le_antisymm
  · by_contra hnot
    have hlarger :
        maximalGenericHankelRank moments rankBound < (supports point).card :=
      Nat.lt_of_not_ge hnot
    have hzero := genericHankelDenominator_eq_zero_of_maximal_lt
      moments rankBound (supports point).card hgood hlarger
    have hnonzero := genericHankelDenominator_ne_zero_of_good_point
      moments point (finiteSupportRoots (supports point))
      (finiteSupportRoots_injective (supports point))
      (fun j hj => by
        rw [rootMoment_finiteSupportRoots]
        apply hmoments j
        omega)
    exact hnonzero hzero
  · by_contra hnot
    have hsmaller :
        (supports point).card < maximalGenericHankelRank moments rankBound :=
      Nat.lt_of_not_ge hnot
    apply hnonsingular
    exact genericHankelDenominator_eval_eq_zero_of_smaller_fiber
      moments point (finiteSupportRoots (supports point)) hsmaller
      (fun j hj => by
        rw [rootMoment_finiteSupportRoots]
        apply hmoments j
        omega)

private def maximalGenericGoodFiberPoints
    (points : Finset K) (supports : K → Finset K)
    (moments : ℕ → K[X]) (rankBound : ℕ) : Finset K := by
  classical
  exact (goodPoints points (fun point => (supports point).card) rankBound).filter
    fun point =>
      (genericHankelDenominator
        (maximalGenericHankelRank moments rankBound) moments).eval point ≠ 0

private theorem mem_maximalGenericGoodFiberPoints
    (points : Finset K) (supports : K → Finset K)
    (moments : ℕ → K[X]) (rankBound : ℕ) (point : K) :
    point ∈ maximalGenericGoodFiberPoints points supports moments rankBound ↔
      point ∈ points ∧
        (supports point).card ≤ rankBound ∧
        (genericHankelDenominator
          (maximalGenericHankelRank moments rankBound) moments).eval point ≠ 0 := by
  classical
  simp only [maximalGenericGoodFiberPoints, ne_eq, goodPoints, mem_filter, and_assoc]

private theorem maximalGenericGoodFiberPoints_card_lower_bound
    (points : Finset K) (supports : K → Finset K)
    (moments : ℕ → K[X]) (rankBound supportBudget : ℕ)
    (hbudget : (∑ point ∈ points, (supports point).card) ≤ supportBudget) :
    points.card - supportBudget / (rankBound + 1) -
        (genericHankelDenominator
          (maximalGenericHankelRank moments rankBound) moments).natDegree ≤
      (maximalGenericGoodFiberPoints points supports moments rankBound).card := by
  classical
  simpa only [maximalGenericGoodFiberPoints, ne_eq, tsub_le_iff_right] using
      card_good_nonzero_genericHankel_lower_bound moments (maximalGenericHankelRank moments
          rankBound) points
        (fun point => (supports point).card) rankBound supportBudget hbudget
        (maximalGenericHankelRank_spec moments rankBound).2

private theorem maximalGenericGoodFiberPoints_card_eq_rank
    (points : Finset K) (supports : K → Finset K)
    (moments : ℕ → K[X]) (rankBound momentBudget : ℕ)
    (hbudget : 2 * rankBound ≤ momentBudget + 1)
    (hmoments : ∀ point ∈ points, ∀ j : ℕ, j ≤ momentBudget →
      (moments j).eval point = supportMoment (supports point) j)
    (point : K)
    (hpoint : point ∈
      maximalGenericGoodFiberPoints points supports moments rankBound) :
    (supports point).card = maximalGenericHankelRank moments rankBound := by
  have hp := (mem_maximalGenericGoodFiberPoints
    points supports moments rankBound point).mp hpoint
  exact goodFiber_card_eq_maximalGenericHankelRank
    moments supports rankBound momentBudget point hp.2.1 hbudget
    (hmoments point hp.1) hp.2.2

private theorem genericHankelDenominator_ratFunc_ne_zero_of_polynomial
    {h : ℕ} (moments : ℕ → K[X])
    (hdenominator : genericHankelDenominator h moments ≠ 0) :
    algebraMap K[X] (RatFunc K)
        (genericHankelDenominator h moments) ≠ 0 := by
  intro hzero
  apply hdenominator
  apply FaithfulSMul.algebraMap_injective K[X] (RatFunc K)
  simpa only [map_zero, FaithfulSMul.algebraMap_eq_zero_iff] using hzero

private def universalElementaryPowerSum
    (R : Type*) [CommRing R] (h j : ℕ) :
    MvPolynomial (Fin h) R :=
  (MvPolynomial.esymmAlgEquiv (Fin h) R (Fintype.card_fin h)).symm
    ⟨MvPolynomial.psum (Fin h) R j,
      MvPolynomial.psum_isSymmetric (Fin h) R j⟩

private theorem universalElementaryPowerSum_esymm_identity
    (R : Type*) [CommRing R] (h j : ℕ) :
    MvPolynomial.aeval
      (fun i : Fin h => MvPolynomial.esymm (Fin h) R (i.val + 1))
      (universalElementaryPowerSum R h j) =
    MvPolynomial.psum (Fin h) R j := by
  have hidentity := congrArg Subtype.val
    ((MvPolynomial.esymmAlgEquiv
      (Fin h) R (Fintype.card_fin h)).apply_symm_apply
      ⟨MvPolynomial.psum (Fin h) R j,
        MvPolynomial.psum_isSymmetric (Fin h) R j⟩)
  simpa only [universalElementaryPowerSum,
    MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom_apply] using hidentity

private theorem universalElementaryPowerSum_evaluates_to_rootMoment
    {R S : Type*} [CommRing R] [Field S] [Algebra R S]
    {h : ℕ} (roots : Fin h → S) (j : ℕ) :
    MvPolynomial.aeval
      (fun i : Fin h =>
        (((Finset.univ : Finset (Fin h)).val.map roots).esymm
          (i.val + 1)))
      (universalElementaryPowerSum R h j) =
    rootMoment roots j := by
  have hidentity := congrArg
    (fun p : MvPolynomial (Fin h) R => MvPolynomial.aeval roots p)
    (universalElementaryPowerSum_esymm_identity R h j)
  rw [MvPolynomial.comp_aeval_apply] at hidentity
  simp_rw [MvPolynomial.aeval_esymm_eq_multiset_esymm] at hidentity
  simpa only [Fin.univ_val_map, rootMoment, MvPolynomial.psum, map_sum, map_pow,
      MvPolynomial.aeval_X] using
      hidentity

private def supportElementaryCoefficients
    {R : Type*} [CommRing R] {h : ℕ}
    (coefficients : Fin h → R) (i : Fin h) : R :=
  (-1 : R) ^ (i.val + 1) * coefficients i.rev

private theorem supportElementaryCoefficients_rootSupport
    {S : Type*} [Field S] {h : ℕ}
    (roots : Fin h → S) (i : Fin h) :
    supportElementaryCoefficients (rootSupportCoefficients roots) i =
      (((Finset.univ : Finset (Fin h)).val.map roots).esymm
        (i.val + 1)) := by
  classical
  have hindex : h - i.rev.val = i.val + 1 := by
    rw [Fin.val_rev]
    omega
  have hcard :
      ((Finset.univ : Finset (Fin h)).val.map roots).card = h := by
    simp only [Fin.univ_val_map, Multiset.coe_card, List.length_ofFn]
  have hvieta := Multiset.prod_X_sub_C_coeff
    (((Finset.univ : Finset (Fin h)).val.map roots))
    (k := i.rev.val)
    (by omega)
  rw [hcard, hindex] at hvieta
  have hproduct :
      (Multiset.map (fun root : S =>
        (Polynomial.X : S[X]) - Polynomial.C root)
          (((Finset.univ : Finset (Fin h)).val.map roots))).prod =
        rootSupportPolynomial roots := by
    simp only [Multiset.map_map]
    rfl
  have hcoefficient :
      rootSupportCoefficients roots i.rev =
        (-1 : S) ^ (i.val + 1) *
          (((Finset.univ : Finset (Fin h)).val.map roots).esymm
            (i.val + 1)) := by
    change (rootSupportPolynomial roots).coeff i.rev.val =
      (-1 : S) ^ (i.val + 1) *
        (((Finset.univ : Finset (Fin h)).val.map roots).esymm
          (i.val + 1))
    rw [← hproduct]
    exact hvieta
  unfold supportElementaryCoefficients
  rw [hcoefficient, ← mul_assoc, ← pow_add]
  simp only [← two_mul, pow_mul, even_two, Even.neg_pow, one_pow, Fin.univ_val_map, one_mul]

private theorem universalElementaryPowerSum_evaluates_supportCoefficients
    {R S : Type*} [CommRing R] [Field S] [Algebra R S]
    {h : ℕ} (roots : Fin h → S) (j : ℕ) :
    MvPolynomial.aeval
      (supportElementaryCoefficients (rootSupportCoefficients roots))
      (universalElementaryPowerSum R h j) =
      rootMoment roots j := by
  have hvariables :
      supportElementaryCoefficients (rootSupportCoefficients roots) =
        (fun i : Fin h =>
          (((Finset.univ : Finset (Fin h)).val.map roots).esymm
            (i.val + 1))) := by
    funext i
    exact supportElementaryCoefficients_rootSupport roots i
  rw [hvariables]
  exact universalElementaryPowerSum_evaluates_to_rootMoment roots j

private def clearedMvPolynomialEvaluation {h : ℕ}
    (polynomial : MvPolynomial (Fin h) K)
    (denominator : K[X]) (numerators : Fin h → K[X]) : K[X] :=
  ∑ exponent ∈ polynomial.support,
    Polynomial.C (polynomial.coeff exponent) *
      denominator ^ (polynomial.totalDegree -
        exponent.sum (fun _ power => power)) *
      ∏ i ∈ exponent.support, numerators i ^ exponent i

private theorem clearedMvPolynomialEvaluation_map
    {h : ℕ} {E : Type*} [Field E]
    (polynomial : MvPolynomial (Fin h) K)
    (denominator : K[X]) (numerators : Fin h → K[X])
    (map : K[X] →+* E)
    (hnonzero : map denominator ≠ 0) :
    map (clearedMvPolynomialEvaluation polynomial denominator numerators) =
      map denominator ^ polynomial.totalDegree *
        MvPolynomial.eval₂ (map.comp Polynomial.C)
          (fun i => map (numerators i) / map denominator) polynomial := by
  classical
  unfold clearedMvPolynomialEvaluation
  rw [MvPolynomial.eval₂_eq]
  simp only [map_sum, map_mul, map_pow, map_prod]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  have hdegree :
      exponent.sum (fun _ power => power) ≤ polynomial.totalDegree :=
    MvPolynomial.le_totalDegree hexponent
  have hdenominatorProduct :
      (∏ i ∈ exponent.support,
        map denominator ^ exponent i) =
        map denominator ^ exponent.sum (fun _ power => power) := by
    simpa only [Finsupp.sum] using
        Finset.prod_pow_eq_pow_sum exponent.support (fun i => exponent i) (map denominator)
  simp only [RingHom.coe_comp, Function.comp_apply]
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, hdenominatorProduct]
  field_simp [hnonzero]
  have hpowers := pow_sub_mul_pow (map denominator) hdegree
  linear_combination map (Polynomial.C (polynomial.coeff exponent)) *
    (∏ i ∈ exponent.support, map (numerators i) ^ exponent i) * hpowers

private theorem genericMomentSupportPolynomial_coeff
    {h : ℕ} (moments : ℕ → K[X]) (i : Fin h) :
    (genericMomentSupportPolynomial h moments).coeff i.val =
      genericHankelCoefficient h moments i := by
  classical
  unfold genericMomentSupportPolynomial
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow,
    ite_eq_right (Nat.ne_of_lt i.isLt), zero_add,
    Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      ite_eq_left rfl, mul_one]
  · intro other _ hother
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have hne : i.val ≠ other.val := by
      intro heq
      exact hother (Fin.ext heq.symm)
    rw [ite_eq_right hne, mul_zero]
  · simp only [mem_univ, not_true_eq_false, coeff_C_mul, coeff_X_pow, ↓reduceIte, mul_one,
      IsEmpty.forall_iff]

private def genericSupportElementaryNumerator
    (h : ℕ) (moments : ℕ → K[X]) (i : Fin h) : K[X] :=
  (-1 : K[X]) ^ (i.val + 1) *
    genericHankelNumerator h moments i.rev

private def genericRootPowerSum
    (h : ℕ) (moments : ℕ → K[X]) (j : ℕ) : RatFunc K :=
  MvPolynomial.aeval
    (supportElementaryCoefficients
      (genericHankelCoefficient h moments))
    (universalElementaryPowerSum K h j)

private def clearedGenericRootPowerSum
    (h : ℕ) (moments : ℕ → K[X]) (j : ℕ) : K[X] :=
  clearedMvPolynomialEvaluation
    (universalElementaryPowerSum K h j)
    (genericHankelDenominator h moments)
    (genericSupportElementaryNumerator h moments)

private def genericRootMomentDifferencePolynomial
    (h : ℕ) (moments : ℕ → K[X]) (j : ℕ) : K[X] :=
  genericHankelDenominator h moments ^
      (universalElementaryPowerSum K h j).totalDegree *
    moments j -
    clearedGenericRootPowerSum h moments j

private theorem clearedGenericRootPowerSum_map_ratFunc
    (h : ℕ) (moments : ℕ → K[X]) (j : ℕ)
    (hdenominator : genericHankelDenominator h moments ≠ 0) :
    algebraMap K[X] (RatFunc K)
        (clearedGenericRootPowerSum h moments j) =
      algebraMap K[X] (RatFunc K)
          (genericHankelDenominator h moments) ^
        (universalElementaryPowerSum K h j).totalDegree *
        genericRootPowerSum h moments j := by
  have hnonzero :=
    genericHankelDenominator_ratFunc_ne_zero_of_polynomial
      moments hdenominator
  have hscalar :
      (algebraMap K[X] (RatFunc K)).comp
          (Polynomial.C : K →+* K[X]) =
        algebraMap K (RatFunc K) := by
    symm
    simpa only [Polynomial.algebraMap_eq] using
      IsScalarTower.algebraMap_eq K K[X] (RatFunc K)
  have hvariables :
      (fun i : Fin h =>
        algebraMap K[X] (RatFunc K)
            (genericSupportElementaryNumerator h moments i) /
          algebraMap K[X] (RatFunc K)
            (genericHankelDenominator h moments)) =
        supportElementaryCoefficients
          (genericHankelCoefficient h moments) := by
    funext i
    unfold genericSupportElementaryNumerator
      supportElementaryCoefficients genericHankelCoefficient
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
  unfold clearedGenericRootPowerSum
  rw [clearedMvPolynomialEvaluation_map
    (universalElementaryPowerSum K h j)
    (genericHankelDenominator h moments)
    (genericSupportElementaryNumerator h moments)
    (algebraMap K[X] (RatFunc K)) hnonzero]
  rw [hscalar, hvariables, ← MvPolynomial.aeval_def]
  rfl

private theorem clearedGenericRootPowerSum_eval_eq_rootMoment
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K) (hinjective : Function.Injective roots)
    (hmoments : ∀ k : ℕ, k < 2 * h →
      (moments k).eval point = rootMoment roots k)
    (j : ℕ) :
    (clearedGenericRootPowerSum h moments j).eval point =
      (genericHankelDenominator h moments).eval point ^
        (universalElementaryPowerSum K h j).totalDegree *
      rootMoment roots j := by
  have hnonzero :=
    genericHankelDenominator_eval_ne_zero_of_distinct_fiber
      moments point roots hinjective hmoments
  have hscalar :
      (Polynomial.evalRingHom point).comp
          (Polynomial.C : K →+* K[X]) =
        algebraMap K K := by
    ext x
    simp only [RingHom.coe_comp, coe_evalRingHom, Function.comp_apply, eval_C,
        Algebra.algebraMap_self,
        RingHom.id_apply]
  have hvariables :
      (fun i : Fin h =>
        (Polynomial.evalRingHom point)
            (genericSupportElementaryNumerator h moments i) /
          (Polynomial.evalRingHom point)
            (genericHankelDenominator h moments)) =
        supportElementaryCoefficients
          (rootSupportCoefficients roots) := by
    funext i
    unfold genericSupportElementaryNumerator
      supportElementaryCoefficients
    simp only [map_mul, map_pow, map_neg, map_one]
    change
      ((-1 : K) ^ (i.val + 1) *
          (genericHankelNumerator h moments i.rev).eval point) /
          (genericHankelDenominator h moments).eval point =
        (-1 : K) ^ (i.val + 1) *
          rootSupportCoefficients roots i.rev
    rw [genericHankelNumerator_eval_eq_det_mul_rootSupportCoefficient
      moments point roots hinjective hmoments i.rev]
    field_simp [hnonzero]
  unfold clearedGenericRootPowerSum
  change
    (Polynomial.evalRingHom point)
        (clearedMvPolynomialEvaluation
          (universalElementaryPowerSum K h j)
          (genericHankelDenominator h moments)
          (genericSupportElementaryNumerator h moments)) =
      (Polynomial.evalRingHom point)
          (genericHankelDenominator h moments) ^
        (universalElementaryPowerSum K h j).totalDegree *
        rootMoment roots j
  rw [clearedMvPolynomialEvaluation_map
    (universalElementaryPowerSum K h j)
    (genericHankelDenominator h moments)
    (genericSupportElementaryNumerator h moments)
    (Polynomial.evalRingHom point) hnonzero]
  rw [hscalar, hvariables, ← MvPolynomial.aeval_def]
  rw [universalElementaryPowerSum_evaluates_supportCoefficients roots j]

private theorem genericRootMomentDifferencePolynomial_eval_eq_zero_of_fiber
    {h : ℕ} (moments : ℕ → K[X]) (point : K)
    (roots : Fin h → K) (hinjective : Function.Injective roots)
    (hmoments : ∀ k : ℕ, k < 2 * h →
      (moments k).eval point = rootMoment roots k)
    (j : ℕ)
    (hmomentj : (moments j).eval point = rootMoment roots j) :
    (genericRootMomentDifferencePolynomial h moments j).eval point = 0 := by
  unfold genericRootMomentDifferencePolynomial
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    hmomentj, clearedGenericRootPowerSum_eval_eq_rootMoment
      moments point roots hinjective hmoments j]
  exact sub_self _

private theorem genericRootMomentDifferencePolynomial_eq_zero_of_maximal_good_fibers
    (points : Finset K) (supports : K → Finset K)
    (moments : ℕ → K[X]) (rankBound momentBudget j : ℕ)
    (hbudget : 2 * rankBound ≤ momentBudget + 1)
    (hj : j ≤ momentBudget)
    (hmoments : ∀ point ∈ points, ∀ k : ℕ, k ≤ momentBudget →
      (moments k).eval point = supportMoment (supports point) k)
    (hdegree :
      (genericRootMomentDifferencePolynomial
        (maximalGenericHankelRank moments rankBound) moments j).natDegree <
        (maximalGenericGoodFiberPoints points supports moments rankBound).card) :
    genericRootMomentDifferencePolynomial
      (maximalGenericHankelRank moments rankBound) moments j = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (genericRootMomentDifferencePolynomial
      (maximalGenericHankelRank moments rankBound) moments j)
    (maximalGenericGoodFiberPoints points supports moments rankBound)
  · intro point hpoint
    have hp := (mem_maximalGenericGoodFiberPoints
      points supports moments rankBound point).mp hpoint
    have hcard := maximalGenericGoodFiberPoints_card_eq_rank
      points supports moments rankBound momentBudget
      hbudget hmoments point hpoint
    have heval :=
      genericRootMomentDifferencePolynomial_eval_eq_zero_of_fiber
        moments point (finiteSupportRoots (supports point))
        (finiteSupportRoots_injective (supports point))
        (fun k hk => by
          rw [rootMoment_finiteSupportRoots]
          exact hmoments point hp.1 k (by omega))
        j
        (by rw [rootMoment_finiteSupportRoots]
            exact hmoments point hp.1 j hj)
    simpa only [hcard] using heval
  · exact hdegree

private theorem genericMoment_eq_genericRootPowerSum_of_cleared
    (h : ℕ) (moments : ℕ → K[X]) (j : ℕ)
    (hdenominator : genericHankelDenominator h moments ≠ 0)
    (hidentity : genericRootMomentDifferencePolynomial h moments j = 0) :
    algebraMap K[X] (RatFunc K) (moments j) =
      genericRootPowerSum h moments j := by
  have hnonzero :=
    genericHankelDenominator_ratFunc_ne_zero_of_polynomial
      moments hdenominator
  have hmapped := congrArg (algebraMap K[X] (RatFunc K)) hidentity
  simp only [genericRootMomentDifferencePolynomial, map_sub,
    map_mul, map_pow, map_zero] at hmapped
  rw [clearedGenericRootPowerSum_map_ratFunc
    h moments j hdenominator] at hmapped
  have hequality := sub_eq_zero.mp hmapped
  exact mul_left_cancel₀
    (pow_ne_zero _ hnonzero) hequality

private theorem genericRootPowerSum_map_eq_rootMoment
    {h : ℕ} (moments : ℕ → K[X]) (j : ℕ)
    {E : Type*} [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    (roots : Fin h → E)
    (hroots :
      (genericMomentSupportPolynomial h moments).map
          (algebraMap (RatFunc K) E) =
        rootSupportPolynomial roots) :
    algebraMap (RatFunc K) E (genericRootPowerSum h moments j) =
      rootMoment roots j := by
  have hcoefficients (i : Fin h) :
      algebraMap (RatFunc K) E
          (genericHankelCoefficient h moments i) =
        rootSupportCoefficients roots i := by
    have heq := congrArg (fun p : E[X] => p.coeff i.val) hroots
    rw [Polynomial.coeff_map,
      genericMomentSupportPolynomial_coeff moments i] at heq
    exact heq
  have hvariables :
      (fun i : Fin h =>
        algebraMap (RatFunc K) E
          (supportElementaryCoefficients
            (genericHankelCoefficient h moments) i)) =
        supportElementaryCoefficients
          (rootSupportCoefficients roots) := by
    funext i
    unfold supportElementaryCoefficients
    rw [map_mul, map_pow, map_neg, map_one,
      hcoefficients i.rev]
  unfold genericRootPowerSum
  calc
    algebraMap (RatFunc K) E
        (MvPolynomial.aeval
          (supportElementaryCoefficients
            (genericHankelCoefficient h moments))
          (universalElementaryPowerSum K h j)) =
      MvPolynomial.aeval
        (fun i : Fin h =>
          algebraMap (RatFunc K) E
            (supportElementaryCoefficients
              (genericHankelCoefficient h moments) i))
        (universalElementaryPowerSum K h j) := by
      simpa only [IsScalarTower.toAlgHom_apply] using
        MvPolynomial.comp_aeval_apply
          (supportElementaryCoefficients
            (genericHankelCoefficient h moments))
          (IsScalarTower.toAlgHom K (RatFunc K) E)
          (universalElementaryPowerSum K h j)
    _ = rootMoment roots j := by
      rw [hvariables]
      exact universalElementaryPowerSum_evaluates_supportCoefficients
        roots j

private theorem genericRootMoment_eq_rootMoment_of_maximal_good_fibers
    (points : Finset K) (supports : K → Finset K)
    (moments : ℕ → K[X]) (rankBound momentBudget j : ℕ)
    (hbudget : 2 * rankBound ≤ momentBudget + 1)
    (hj : j ≤ momentBudget)
    (hmoments : ∀ point ∈ points, ∀ k : ℕ, k ≤ momentBudget →
      (moments k).eval point = supportMoment (supports point) k)
    (hdegree :
      (genericRootMomentDifferencePolynomial
        (maximalGenericHankelRank moments rankBound) moments j).natDegree <
        (maximalGenericGoodFiberPoints points supports moments rankBound).card)
    {E : Type*} [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    (roots : Fin (maximalGenericHankelRank moments rankBound) → E)
    (hroots :
      (genericMomentSupportPolynomial
        (maximalGenericHankelRank moments rankBound) moments).map
          (algebraMap (RatFunc K) E) =
        rootSupportPolynomial roots) :
    algebraMap (RatFunc K) E
        (algebraMap K[X] (RatFunc K) (moments j)) =
      rootMoment roots j := by
  have hidentity :=
    genericRootMomentDifferencePolynomial_eq_zero_of_maximal_good_fibers
      points supports moments rankBound momentBudget j
      hbudget hj hmoments hdegree
  have hgeneric := genericMoment_eq_genericRootPowerSum_of_cleared
    (maximalGenericHankelRank moments rankBound) moments j
    (maximalGenericHankelRank_spec moments rankBound).2 hidentity
  calc
    algebraMap (RatFunc K) E
        (algebraMap K[X] (RatFunc K) (moments j)) =
      algebraMap (RatFunc K) E
        (genericRootPowerSum
          (maximalGenericHankelRank moments rankBound) moments j) :=
        congrArg (algebraMap (RatFunc K) E) hgeneric
    _ = rootMoment roots j :=
      genericRootPowerSum_map_eq_rootMoment moments j roots hroots

private theorem genericMoments_eq_rootMoments_of_maximal_good_grid
    (points : Finset K) (supports : K → Finset K)
    (moments : ℕ → K[X]) (rankBound momentBudget : ℕ)
    (hbudget : 2 * rankBound ≤ momentBudget + 1)
    (hmoments : ∀ point ∈ points, ∀ j : ℕ, j ≤ momentBudget →
      (moments j).eval point = supportMoment (supports point) j)
    (hdegrees : ∀ j : ℕ, j ≤ momentBudget →
      (genericRootMomentDifferencePolynomial
        (maximalGenericHankelRank moments rankBound) moments j).natDegree <
        (maximalGenericGoodFiberPoints points supports moments rankBound).card)
    {E : Type*} [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    (roots : Fin (maximalGenericHankelRank moments rankBound) → E)
    (hroots :
      (genericMomentSupportPolynomial
        (maximalGenericHankelRank moments rankBound) moments).map
          (algebraMap (RatFunc K) E) =
        rootSupportPolynomial roots) :
    ∀ j : ℕ, j ≤ momentBudget →
      algebraMap (RatFunc K) E
          (algebraMap K[X] (RatFunc K) (moments j)) =
        rootMoment roots j := by
  intro j hj
  exact genericRootMoment_eq_rootMoment_of_maximal_good_fibers
    points supports moments rankBound momentBudget j hbudget hj
    hmoments (hdegrees j hj) roots hroots

private def universalElementaryVariable
    (R : Type*) [Field R] (h k : ℕ) :
    MvPolynomial (Fin h) R :=
  if hzero : k = 0 then 1
  else if hbound : k ≤ h then
    MvPolynomial.X ⟨k - 1, by omega⟩
  else 0

private theorem universalElementaryVariable_esymm_identity
    (R : Type*) [Field R] (h k : ℕ) :
    MvPolynomial.aeval
      (fun i : Fin h => MvPolynomial.esymm (Fin h) R (i.val + 1))
      (universalElementaryVariable R h k) =
      MvPolynomial.esymm (Fin h) R k := by
  classical
  by_cases hzero : k = 0
  · subst k
    simp only [MvPolynomial.aeval_eq_bind₁, universalElementaryVariable, ↓reduceDIte, map_one,
        MvPolynomial.esymm_zero]
  · by_cases hbound : k ≤ h
    · have hpositive : 0 < k := Nat.pos_of_ne_zero hzero
      simp only [MvPolynomial.aeval_eq_bind₁, universalElementaryVariable, hzero, ↓reduceDIte,
          hbound,
          MvPolynomial.bind₁_X_right, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hzero)]
    · have hempty :
          (Finset.univ : Finset (Fin h)).powersetCard k = ∅ := by
        apply Finset.powersetCard_eq_empty.mpr
        simp only [card_univ, Fintype.card_fin]
        omega
      simp only [MvPolynomial.esymm, MvPolynomial.aeval_eq_bind₁, universalElementaryVariable,
          hzero, ↓reduceDIte,
          hbound, map_zero, hempty, sum_empty]

private theorem universalElementaryVariable_totalDegree_le_one
    (R : Type*) [Field R] (h k : ℕ) :
    (universalElementaryVariable R h k).totalDegree ≤ 1 := by
  classical
  by_cases hzero : k = 0
  · simp only [universalElementaryVariable, hzero, ↓reduceDIte, MvPolynomial.totalDegree_one,
      zero_le]
  · by_cases hbound : k ≤ h <;>
      simp [universalElementaryVariable, hzero, hbound]

private theorem universalElementaryPowerSum_zero
    (R : Type*) [Field R] (h : ℕ) :
    universalElementaryPowerSum R h 0 =
      MvPolynomial.C (h : R) := by
  apply (MvPolynomial.esymmAlgEquiv
    (Fin h) R (Fintype.card_fin h)).injective
  apply Subtype.ext
  simp only [MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom_apply]
  rw [universalElementaryPowerSum_esymm_identity]
  simp only [MvPolynomial.psum, pow_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one,
      MvPolynomial.aeval_eq_bind₁, map_natCast]

private theorem universalElementaryPowerSum_newton_recurrence
    (R : Type*) [Field R] (h j : ℕ) (hj : 0 < j) :
    universalElementaryPowerSum R h j =
      MvPolynomial.C ((-1 : R) ^ (j + 1) * (j : R)) *
        universalElementaryVariable R h j -
      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal j with a.1 ∈ Set.Ioo 0 j,
        MvPolynomial.C ((-1 : R) ^ a.1) *
          universalElementaryVariable R h a.1 *
          universalElementaryPowerSum R h a.2 := by
  classical
  apply (MvPolynomial.esymmAlgEquiv
    (Fin h) R (Fintype.card_fin h)).injective
  apply Subtype.ext
  simp only [MvPolynomial.esymmAlgEquiv_apply,
    MvPolynomial.esymmAlgHom_apply]
  rw [universalElementaryPowerSum_esymm_identity]
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin h) R j hj]
  simp only [map_sub, map_sum, map_mul,
    map_pow, map_neg, map_one, map_natCast]
  simp_rw [universalElementaryVariable_esymm_identity,
    universalElementaryPowerSum_esymm_identity]

private theorem universalElementaryPowerSum_totalDegree_le
    (R : Type*) [Field R] (h j : ℕ) :
    (universalElementaryPowerSum R h j).totalDegree ≤ j := by
  classical
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hzero : j = 0
    · subst j
      rw [universalElementaryPowerSum_zero]
      exact (MvPolynomial.totalDegree_C (h : R)).le
    · have hj : 0 < j := Nat.pos_of_ne_zero hzero
      rw [universalElementaryPowerSum_newton_recurrence R h j hj]
      apply (MvPolynomial.totalDegree_sub _ _).trans
      apply max_le
      · calc
          (MvPolynomial.C ((-1 : R) ^ (j + 1) * (j : R)) *
            universalElementaryVariable R h j).totalDegree ≤
              (MvPolynomial.C
                ((-1 : R) ^ (j + 1) * (j : R))).totalDegree +
                (universalElementaryVariable R h j).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
          _ ≤ j := by
            rw [MvPolynomial.totalDegree_C]
            have hvar := universalElementaryVariable_totalDegree_le_one R h j
            omega
      · apply MvPolynomial.totalDegree_finsetSum_le
        intro pair hpair
        have hp := Finset.mem_filter.mp hpair
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp.1
        have hpos : 0 < pair.1 := hp.2.1
        have hlt : pair.2 < j := by omega
        calc
          (MvPolynomial.C ((-1 : R) ^ pair.1) *
              universalElementaryVariable R h pair.1 *
              universalElementaryPowerSum R h pair.2).totalDegree ≤
            (MvPolynomial.C ((-1 : R) ^ pair.1) *
              universalElementaryVariable R h pair.1).totalDegree +
              (universalElementaryPowerSum R h pair.2).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
          _ ≤ 1 + pair.2 := by
            have hfirst :=
              MvPolynomial.totalDegree_mul
                (MvPolynomial.C ((-1 : R) ^ pair.1))
                (universalElementaryVariable R h pair.1)
            rw [MvPolynomial.totalDegree_C, zero_add] at hfirst
            exact Nat.add_le_add
              (hfirst.trans
                (universalElementaryVariable_totalDegree_le_one R h pair.1))
              (ih pair.2 hlt)
          _ ≤ j := by omega

private theorem clearedMvPolynomialEvaluation_natDegree_le
    {h : ℕ} (polynomial : MvPolynomial (Fin h) K)
    (denominator : K[X]) (numerators : Fin h → K[X])
    (degreeBound : ℕ)
    (hdenominator : denominator.natDegree ≤ degreeBound)
    (hnumerators : ∀ i, (numerators i).natDegree ≤ degreeBound) :
    (clearedMvPolynomialEvaluation polynomial denominator numerators).natDegree ≤
      polynomial.totalDegree * degreeBound := by
  classical
  unfold clearedMvPolynomialEvaluation
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent hexponent
  have hdegree :
      exponent.sum (fun _ power => power) ≤ polynomial.totalDegree :=
    MvPolynomial.le_totalDegree hexponent
  have hproduct :
      (∏ i ∈ exponent.support,
        numerators i ^ exponent i).natDegree ≤
        exponent.sum (fun _ power => power) * degreeBound := by
    calc
      (∏ i ∈ exponent.support,
        numerators i ^ exponent i).natDegree ≤
          ∑ i ∈ exponent.support,
            (numerators i ^ exponent i).natDegree :=
        Polynomial.natDegree_prod_le exponent.support
          (fun i => numerators i ^ exponent i)
      _ ≤ ∑ i ∈ exponent.support, exponent i * degreeBound := by
        apply Finset.sum_le_sum
        intro i _
        exact Polynomial.natDegree_pow_le.trans
          (Nat.mul_le_mul_left (exponent i) (hnumerators i))
      _ = exponent.sum (fun _ power => power) * degreeBound := by
        change
          (∑ i ∈ exponent.support, exponent i * degreeBound) =
            (∑ i ∈ exponent.support, exponent i) * degreeBound
        rw [Finset.sum_mul]
  calc
    (Polynomial.C (polynomial.coeff exponent) *
        denominator ^ (polynomial.totalDegree -
          exponent.sum (fun _ power => power)) *
        ∏ i ∈ exponent.support, numerators i ^ exponent i).natDegree =
      (Polynomial.C (polynomial.coeff exponent) *
        (denominator ^ (polynomial.totalDegree -
          exponent.sum (fun _ power => power)) *
          ∏ i ∈ exponent.support, numerators i ^ exponent i)).natDegree := by
        rw [mul_assoc]
    _ ≤ (denominator ^ (polynomial.totalDegree -
          exponent.sum (fun _ power => power)) *
          ∏ i ∈ exponent.support, numerators i ^ exponent i).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
    _ ≤ (denominator ^ (polynomial.totalDegree -
          exponent.sum (fun _ power => power))).natDegree +
        (∏ i ∈ exponent.support,
          numerators i ^ exponent i).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ (polynomial.totalDegree -
          exponent.sum (fun _ power => power)) * degreeBound +
        exponent.sum (fun _ power => power) * degreeBound := by
      apply Nat.add_le_add
      · exact Polynomial.natDegree_pow_le.trans
          (Nat.mul_le_mul_left
            (polynomial.totalDegree -
              exponent.sum (fun _ power => power)) hdenominator)
      · exact hproduct
    _ = polynomial.totalDegree * degreeBound := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hdegree]

private theorem genericSupportElementaryNumerator_natDegree_le
    (moments : ℕ → K[X]) (d h : ℕ)
    (hmomentdegree : ∀ k : ℕ, (moments k).natDegree ≤ d * k)
    (i : Fin h) :
    (genericSupportElementaryNumerator h moments i).natDegree ≤
      2 * d * h * h := by
  have hsmall : ∀ k : ℕ, k < 2 * h →
      (moments k).natDegree ≤ d * (2 * h) := by
    intro k hk
    exact (hmomentdegree k).trans
      (Nat.mul_le_mul_left d (Nat.le_of_lt hk))
  have hnumerator :=
    genericHankelNumerator_natDegree_le
      moments (d * (2 * h)) hsmall i.rev
  unfold genericSupportElementaryNumerator
  calc
    ((-1 : K[X]) ^ (i.val + 1) *
        genericHankelNumerator h moments i.rev).natDegree ≤
      ((-1 : K[X]) ^ (i.val + 1)).natDegree +
        (genericHankelNumerator h moments i.rev).natDegree :=
      Polynomial.natDegree_mul_le
    _ = (genericHankelNumerator h moments i.rev).natDegree := by simp only [natDegree_pow,
        natDegree_neg, natDegree_one, mul_zero, zero_add]
    _ ≤ h * (d * (2 * h)) := hnumerator
    _ = 2 * d * h * h := by ring

private theorem genericHankelDenominator_natDegree_le_uniform_source
    (moments : ℕ → K[X]) (d h : ℕ)
    (hmomentdegree : ∀ k : ℕ, (moments k).natDegree ≤ d * k) :
    (genericHankelDenominator h moments).natDegree ≤
      2 * d * h * h := by
  have hsmall : ∀ k : ℕ, k < 2 * h →
      (moments k).natDegree ≤ d * (2 * h) := by
    intro k hk
    exact (hmomentdegree k).trans
      (Nat.mul_le_mul_left d (Nat.le_of_lt hk))
  calc
    (genericHankelDenominator h moments).natDegree ≤
      h * (d * (2 * h)) :=
        genericHankelDenominator_natDegree_le
          moments (d * (2 * h)) hsmall
    _ = 2 * d * h * h := by ring

private theorem clearedGenericRootPowerSum_natDegree_le
    (moments : ℕ → K[X]) (d h j : ℕ)
    (hmomentdegree : ∀ k : ℕ, (moments k).natDegree ≤ d * k) :
    (clearedGenericRootPowerSum h moments j).natDegree ≤
      2 * d * h ^ 2 * j := by
  unfold clearedGenericRootPowerSum
  calc
    (clearedMvPolynomialEvaluation
      (universalElementaryPowerSum K h j)
      (genericHankelDenominator h moments)
      (genericSupportElementaryNumerator h moments)).natDegree ≤
        (universalElementaryPowerSum K h j).totalDegree *
          (2 * d * h * h) :=
      clearedMvPolynomialEvaluation_natDegree_le
        (universalElementaryPowerSum K h j)
        (genericHankelDenominator h moments)
        (genericSupportElementaryNumerator h moments)
        (2 * d * h * h)
        (genericHankelDenominator_natDegree_le_uniform_source
          moments d h hmomentdegree)
        (genericSupportElementaryNumerator_natDegree_le
          moments d h hmomentdegree)
    _ ≤ j * (2 * d * h * h) :=
      Nat.mul_le_mul_right (2 * d * h * h)
        (universalElementaryPowerSum_totalDegree_le K h j)
    _ = 2 * d * h ^ 2 * j := by ring

private theorem genericRootMomentDifferencePolynomial_natDegree_le
    (moments : ℕ → K[X]) (d h j : ℕ)
    (hmomentdegree : ∀ k : ℕ, (moments k).natDegree ≤ d * k) :
    (genericRootMomentDifferencePolynomial h moments j).natDegree ≤
      max (d * j) (2 * d * h ^ 2 * j) := by
  have hdenominator :
      (genericHankelDenominator h moments).natDegree ≤
        d * h * (h - 1) :=
    genericHankelDenominator_natDegree_le_sharp
      (h := h) moments d (fun k _ => hmomentdegree k)
  have huniversal :=
    universalElementaryPowerSum_totalDegree_le K h j
  have hfirst :
      (genericHankelDenominator h moments ^
          (universalElementaryPowerSum K h j).totalDegree *
        moments j).natDegree ≤
        max (d * j) (2 * d * h ^ 2 * j) := by
    have hbasic :
        (genericHankelDenominator h moments ^
            (universalElementaryPowerSum K h j).totalDegree *
          moments j).natDegree ≤
          (universalElementaryPowerSum K h j).totalDegree *
              (d * h * (h - 1)) +
            d * j := by
      calc
        (genericHankelDenominator h moments ^
            (universalElementaryPowerSum K h j).totalDegree *
          moments j).natDegree ≤
          (genericHankelDenominator h moments ^
            (universalElementaryPowerSum K h j).totalDegree).natDegree +
            (moments j).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ (universalElementaryPowerSum K h j).totalDegree *
              (d * h * (h - 1)) + d * j := by
          apply Nat.add_le_add
          · exact Polynomial.natDegree_pow_le.trans
              (Nat.mul_le_mul_left
                (universalElementaryPowerSum K h j).totalDegree
                hdenominator)
          · exact hmomentdegree j
    by_cases hzero : h = 0
    · subst h
      simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
          zero_le,
          sup_of_le_left, ge_iff_le, zero_tsub, zero_add] using hbasic
    · have hpositive : 0 < h := Nat.pos_of_ne_zero hzero
      have hsquare : 0 < h * h := Nat.mul_pos hpositive hpositive
      have hquadratic : h * (h - 1) + 1 ≤ 2 * h * h := by
        have hsmaller :=
          Nat.mul_le_mul_left h (Nat.sub_le h 1)
        calc
          h * (h - 1) + 1 ≤ h * h + h * h := by omega
          _ = 2 * h * h := by ring
      apply (hbasic.trans ?_).trans (le_max_right _ _)
      calc
        (universalElementaryPowerSum K h j).totalDegree *
              (d * h * (h - 1)) + d * j ≤
            j * (d * h * (h - 1)) + d * j :=
          Nat.add_le_add_right
            (Nat.mul_le_mul_right (d * h * (h - 1)) huniversal) _
        _ = (d * j) * (h * (h - 1) + 1) := by ring
        _ ≤ (d * j) * (2 * h * h) :=
          Nat.mul_le_mul_left (d * j) hquadratic
        _ = 2 * d * h ^ 2 * j := by ring
  unfold genericRootMomentDifferencePolynomial
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le hfirst
      ((clearedGenericRootPowerSum_natDegree_le
        moments d h j hmomentdegree).trans (le_max_right _ _)))

private theorem genericMoments_eq_rootMoments_of_maximal_good_grid_degree_bound
    (points : Finset K) (supports : K → Finset K)
    (moments : ℕ → K[X]) (rankBound momentBudget d : ℕ)
    (hbudget : 2 * rankBound ≤ momentBudget + 1)
    (hmoments : ∀ point ∈ points, ∀ j : ℕ, j ≤ momentBudget →
      (moments j).eval point = supportMoment (supports point) j)
    (hmomentdegree : ∀ j : ℕ, (moments j).natDegree ≤ d * j)
    (hgrid :
      max (d * momentBudget)
        (2 * d * (maximalGenericHankelRank moments rankBound) ^ 2 *
          momentBudget) <
        (maximalGenericGoodFiberPoints
          points supports moments rankBound).card)
    {E : Type*} [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    (roots : Fin (maximalGenericHankelRank moments rankBound) → E)
    (hroots :
      (genericMomentSupportPolynomial
        (maximalGenericHankelRank moments rankBound) moments).map
          (algebraMap (RatFunc K) E) =
        rootSupportPolynomial roots) :
    ∀ j : ℕ, j ≤ momentBudget →
      algebraMap (RatFunc K) E
          (algebraMap K[X] (RatFunc K) (moments j)) =
        rootMoment roots j := by
  apply genericMoments_eq_rootMoments_of_maximal_good_grid
    points supports moments rankBound momentBudget hbudget hmoments
    (E := E) (roots := roots) (hroots := hroots)
  intro j hj
  calc
    (genericRootMomentDifferencePolynomial
        (maximalGenericHankelRank moments rankBound)
        moments j).natDegree ≤
      max (d * j)
        (2 * d * (maximalGenericHankelRank moments rankBound) ^ 2 * j) :=
      genericRootMomentDifferencePolynomial_natDegree_le
        moments d (maximalGenericHankelRank moments rankBound) j
        hmomentdegree
    _ ≤ max (d * momentBudget)
        (2 * d * (maximalGenericHankelRank moments rankBound) ^ 2 *
          momentBudget) := by
      apply max_le_max
      · exact Nat.mul_le_mul_left d hj
      · exact Nat.mul_le_mul_left
          (2 * d * (maximalGenericHankelRank moments rankBound) ^ 2) hj
    _ < (maximalGenericGoodFiberPoints
          points supports moments rankBound).card := hgrid

private theorem maximalGenericHankelRank_pos_of_normalized_moment
    (moments : ℕ → K[X]) (rankBound : ℕ) (point : K)
    (hbound : 0 < rankBound)
    (hnormalized : (moments 0).eval point = 1) :
    0 < maximalGenericHankelRank moments rankBound := by
  have hone : genericHankelDenominator 1 moments ≠ 0 := by
    intro hzero
    have heval := congrArg (fun polynomial : K[X] =>
      polynomial.eval point) hzero
    have hdeterminant :
        genericHankelDenominator 1 moments = moments 0 := by
      simp only [genericHankelDenominator, leadingHankelDet, polynomialHankel, Fin.val_eq_zero,
          add_zero,
          det_unique, Fin.default_eq_zero, Fin.isValue, of_apply]
    rw [hdeterminant, hnormalized, Polynomial.eval_zero] at heval
    exact one_ne_zero heval
  by_contra hnot
  have hmax : maximalGenericHankelRank moments rankBound = 0 :=
    Nat.eq_zero_of_not_pos hnot
  apply hone
  exact genericHankelDenominator_eq_zero_of_maximal_lt
    moments rankBound 1 (by omega) (by omega)

private theorem sourceGenericMoments_eq_rootMoments
    (points : Finset K) (supports : K → Finset K)
    (moments : ℕ → K[X]) (N d : ℕ)
    (hN : 100 ≤ N) (hd : d ≤ N)
    (hmoments : ∀ point ∈ points, ∀ j : ℕ, j ≤ N ^ 30 →
      (moments j).eval point = supportMoment (supports point) j)
    (hmomentdegree : ∀ j : ℕ, (moments j).natDegree ≤ d * j)
    (hgrid :
      2 * N ^ 39 <
        (maximalGenericGoodFiberPoints
          points supports moments (N ^ 4)).card)
    {E : Type*} [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    (roots : Fin (maximalGenericHankelRank moments (N ^ 4)) → E)
    (hroots :
      (genericMomentSupportPolynomial
        (maximalGenericHankelRank moments (N ^ 4)) moments).map
          (algebraMap (RatFunc K) E) =
        rootSupportPolynomial roots) :
    ∀ j : ℕ, j ≤ N ^ 30 →
      algebraMap (RatFunc K) E
          (algebraMap K[X] (RatFunc K) (moments j)) =
        rootMoment roots j := by
  have hbudget : 2 * N ^ 4 ≤ N ^ 30 + 1 := by
    have hsource := source_clause_support_lt_moment_budget hN
    omega
  have hfirst : d * N ^ 30 ≤ 2 * N ^ 39 := by
    calc
      d * N ^ 30 ≤ N ^ 31 := source_moment_degree_le hd
      _ ≤ N ^ 39 :=
        Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ 2 * N ^ 39 := by omega
  have hrank :
      maximalGenericHankelRank moments (N ^ 4) ≤ N ^ 4 :=
    (maximalGenericHankelRank_spec moments (N ^ 4)).1
  have hsecond :
      2 * d * (maximalGenericHankelRank moments (N ^ 4)) ^ 2 *
          N ^ 30 ≤ 2 * N ^ 39 :=
    source_cleared_moment_degree_le hd hrank (le_refl _)
  apply genericMoments_eq_rootMoments_of_maximal_good_grid_degree_bound
    points supports moments (N ^ 4) (N ^ 30) d hbudget
    hmoments hmomentdegree
    (lt_of_le_of_lt (max_le hfirst hsecond) hgrid)
    roots hroots

/-- GapCVP reduction support. -/
def enumeratedRootSupport
    {E : Type*} {h : ℕ}
    (roots : Fin h → E) : Finset E := by
  classical
  exact Finset.univ.image roots

private theorem supportMoment_enumeratedRootSupport
    {E : Type*} [Field E] {h : ℕ}
    (roots : Fin h → E)
    (hinjective : Function.Injective roots) (j : ℕ) :
    supportMoment (enumeratedRootSupport roots) j =
      rootMoment roots j := by
  classical
  unfold supportMoment rootMoment enumeratedRootSupport
  rw [Finset.sum_image]
  intro first _ second _ hequal
  exact hinjective hequal

private theorem enumeratedRootSupport_card
    {E : Type*} {h : ℕ}
    (roots : Fin h → E)
    (hinjective : Function.Injective roots) :
    (enumeratedRootSupport roots).card = h := by
  classical
  unfold enumeratedRootSupport
  rw [Finset.card_image_iff.mpr (Set.injOn_of_injective hinjective)]
  exact Finset.card_fin h

end

section

open Polynomial IsDedekindDomain

variable {K E : Type*} [Field K] [Field E]
variable [Algebra (RatFunc K) E] [Algebra K[X] E]
variable [IsScalarTower K[X] (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E]
variable [Algebra.IsSeparable (RatFunc K) E]

theorem functionFieldExtendedValuation_polynomial_le_one
    (a : K) (f : K[X]) :
    functionFieldExtendedValuation (K := K) (E := E) a
      (algebraMap K[X] E f) ≤ 1 := by
  let : IsDedekindDomain (integralClosure K[X] E) :=
    integralClosure.isDedekindDomain K[X] (RatFunc K) E
  let : IsFractionRing (integralClosure K[X] E) E :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc K) E
  change
    (functionFieldHeightOnePlace (K := K) (E := E) a).valuation E
      (algebraMap K[X] E f) ≤ 1
  rw [IsScalarTower.algebraMap_apply K[X]
    (integralClosure K[X] E) E f]
  exact
    (functionFieldHeightOnePlace (K := K) (E := E) a).valuation_le_one
      (algebraMap K[X] (integralClosure K[X] E) f)

private theorem functionFieldExtendedValuation_polynomial_eq_one_of_eval_ne_zero
    (a : K) (f : K[X]) (heval : f.eval a ≠ 0) :
    functionFieldExtendedValuation (K := K) (E := E) a
      (algebraMap K[X] E f) = 1 := by
  apply le_antisymm
    (functionFieldExtendedValuation_polynomial_le_one a f)
  apply le_of_not_gt
  intro hlt
  have hmem :=
    (functionFieldExtendedValuation_polynomial_lt_one_iff
      (K := K) (E := E) a f).mp hlt
  have hdvd : (X - C a : K[X]) ∣ f :=
    Ideal.mem_span_singleton.mp
      (show f ∈ Ideal.span ({X - C a} : Set K[X]) by
        simpa only [functionFieldPlaceIdeal] using hmem)
  exact heval ((Polynomial.dvd_iff_isRoot.mp hdvd))

private theorem functionField_rootMultiplicity_le_natDegree
    (a : K) (f : K[X]) (hf : f ≠ 0) :
    f.rootMultiplicity a ≤ f.natDegree := by
  have hdegree := Polynomial.natDegree_le_of_dvd
    (Polynomial.pow_rootMultiplicity_dvd f a) hf
  simpa only [ge_iff_le, natDegree_pow, natDegree_sub_C, natDegree_X, mul_one] using hdegree

private theorem functionFieldExtendedValuation_polynomial_eq_place_pow
    (a : K) (f : K[X]) (hf : f ≠ 0) :
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E f) =
      functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E (X - C a)) ^ f.rootMultiplicity a := by
  obtain ⟨remaining, hfactor, hremaining⟩ :=
    f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf a
  have heval : remaining.eval a ≠ 0 := by
    intro hzero
    apply hremaining
    apply Polynomial.dvd_iff_isRoot.mpr
    exact hzero
  have hunit :=
    functionFieldExtendedValuation_polynomial_eq_one_of_eval_ne_zero
      (E := E) a remaining heval
  calc
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E f) =
      functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E
          ((X - C a) ^ f.rootMultiplicity a * remaining)) :=
      congrArg
        (fun polynomial : K[X] =>
          functionFieldExtendedValuation (K := K) (E := E) a
            (algebraMap K[X] E polynomial)) hfactor
    _ = functionFieldExtendedValuation (K := K) (E := E) a
          (algebraMap K[X] E (X - C a)) ^ f.rootMultiplicity a *
        functionFieldExtendedValuation (K := K) (E := E) a
          (algebraMap K[X] E remaining) := by
      rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
    _ = functionFieldExtendedValuation (K := K) (E := E) a
          (algebraMap K[X] E (X - C a)) ^ f.rootMultiplicity a := by
      rw [hunit, mul_one]

private theorem functionFieldExtendedValuation_place_pow_natDegree_le
    (a : K) (f : K[X]) (hf : f ≠ 0) :
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E (X - C a)) ^ f.natDegree ≤
      functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E f) := by
  rw [functionFieldExtendedValuation_polynomial_eq_place_pow a f hf]
  apply pow_le_pow_of_le_one
  · exact zero_le
  · exact le_of_lt
      (functionFieldExtendedValuation_place_lt_one (K := K) (E := E) a)
  · exact functionField_rootMultiplicity_le_natDegree a f hf

private theorem functionFieldExtendedValuation_polynomial_div_le
    (a : K) (numerator denominator : K[X]) :
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E numerator /
          algebraMap K[X] E denominator) ≤
      (functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E denominator))⁻¹ := by
  rw [Valuation.map_div, div_eq_mul_inv]
  calc
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E numerator) *
      (functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E denominator))⁻¹ ≤
      1 * (functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E denominator))⁻¹ := by
      rw [mul_comm]
      simpa only [mul_one, one_mul] using
        mul_le_mul_right
          (functionFieldExtendedValuation_polynomial_le_one a numerator)
          (functionFieldExtendedValuation (K := K) (E := E) a
            (algebraMap K[X] E denominator))⁻¹
    _ = _ := one_mul _

private theorem functionFieldExtendedValuation_genericHankelCoefficient_le
    (a : K) (moments : ℕ → K[X]) (h : ℕ) (i : Fin h) :
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap (RatFunc K) E
          (genericHankelCoefficient h moments i)) ≤
      (functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E
          (genericHankelDenominator h moments)))⁻¹ := by
  unfold genericHankelCoefficient
  rw [map_div₀,
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) E
      (genericHankelNumerator h moments i),
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) E
      (genericHankelDenominator h moments)]
  exact functionFieldExtendedValuation_polynomial_div_le
    a (genericHankelNumerator h moments i)
    (genericHankelDenominator h moments)

private theorem functionFieldExtendedValuation_genericHankelDenominator_place_pow_le
    (a : K) (moments : ℕ → K[X]) (d h : ℕ)
    (hmoments : ∀ j : ℕ, (moments j).natDegree ≤ d * j)
    (hdenominator : genericHankelDenominator h moments ≠ 0) :
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E (X - C a)) ^ (d * h * (h - 1)) ≤
      functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E
          (genericHankelDenominator h moments)) := by
  have hdegree := genericHankelDenominator_natDegree_le_sharp
    (h := h) moments d (fun j _ => hmoments j)
  calc
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E (X - C a)) ^ (d * h * (h - 1)) ≤
      functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E (X - C a)) ^
          (genericHankelDenominator h moments).natDegree := by
      apply pow_le_pow_of_le_one
      · exact zero_le
      · exact le_of_lt
          (functionFieldExtendedValuation_place_lt_one
            (K := K) (E := E) a)
      · exact hdegree
    _ ≤ functionFieldExtendedValuation (K := K) (E := E) a
          (algebraMap K[X] E
            (genericHankelDenominator h moments)) :=
      functionFieldExtendedValuation_place_pow_natDegree_le
        a (genericHankelDenominator h moments) hdenominator

private theorem functionFieldExtendedValuation_genericHankelCoefficient_le_place_inv_pow
    (a : K) (moments : ℕ → K[X]) (d h : ℕ)
    (hmoments : ∀ j : ℕ, (moments j).natDegree ≤ d * j)
    (hdenominator : genericHankelDenominator h moments ≠ 0)
    (i : Fin h) :
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap (RatFunc K) E
          (genericHankelCoefficient h moments i)) ≤
      (functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E (X - C a)) ^
          (d * h * (h - 1)))⁻¹ := by
  have hplaceNonzero : algebraMap K[X] E (X - C a) ≠ 0 :=
    (map_ne_zero_iff (algebraMap K[X] E)
      (functionFieldPolynomial_algebraMap_injective
        (K := K) (E := E))).mpr
      (Polynomial.X_sub_C_ne_zero a)
  have hplacePositive :
      0 < functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E (X - C a)) :=
    (Valuation.pos_iff _).mpr hplaceNonzero
  have hlower :=
    functionFieldExtendedValuation_genericHankelDenominator_place_pow_le
      (E := E) a moments d h hmoments hdenominator
  calc
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap (RatFunc K) E
          (genericHankelCoefficient h moments i)) ≤
      (functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E
          (genericHankelDenominator h moments)))⁻¹ :=
      functionFieldExtendedValuation_genericHankelCoefficient_le
        a moments h i
    _ ≤ (functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E (X - C a)) ^
          (d * h * (h - 1)))⁻¹ :=
      inv_anti₀ (pow_pos hplacePositive _) hlower

end

section

open scoped BigOperators
open Finset Polynomial

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] [Fintype K]

private def sourceSignedFiberSupport
    (F : Formula) (points : Finset K)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (tableType : sourceSATTableType F)
    (point : sourceSATGridPoint points) : Finset K := by
  classical
  exact Finset.univ.filter fun value : K =>
    (z (sourceSATColumnIndex F points tableType point value) : ZMod 2) ≠ 0

omit [Field K] [Algebra (ZMod 2) K] in
@[simp] private theorem mem_sourceSignedFiberSupport
    (F : Formula) (points : Finset K)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (tableType : sourceSATTableType F)
    (point : sourceSATGridPoint points) (value : K) :
    value ∈ sourceSignedFiberSupport F points z tableType point ↔
      (z (sourceSATColumnIndex F points tableType point value) : ZMod 2) ≠
        0 := by
  classical
  simp only [sourceSignedFiberSupport, ne_eq, mem_filter, mem_univ, true_and]

private theorem sourceBinaryResidue_eq_one_of_ne_zero
    (value : ZMod 2) (hvalue : value ≠ 0) : value = 1 := by
  apply ZMod.val_injective 2
  have hnonzero : value.val ≠ 0 := by
    intro hzero
    apply hvalue
    apply ZMod.val_injective 2
    simpa only [ZMod.val_zero, ZMod.val_eq_zero] using hzero
  have hlt := ZMod.val_lt value
  change value.val = 1
  omega

omit [Field K] [Algebra (ZMod 2) K] in
private theorem sourceSignedFiberSupport_card_le_rowSquaredNorm
    (F : Formula) (points : Finset K)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (tableType : sourceSATTableType F)
    (point : sourceSATGridPoint points) :
    (sourceSignedFiberSupport F points z tableType point).card ≤
      ∑ value : K,
        (z (sourceSATColumnIndex F points tableType point value)).natAbs ^
          2 := by
  classical
  calc
    (sourceSignedFiberSupport F points z tableType point).card =
        ∑ value ∈ sourceSignedFiberSupport F points z tableType point,
          (1 : ℕ) :=
      Finset.card_eq_sum_ones _
    _ ≤ ∑ value ∈ sourceSignedFiberSupport F points z tableType point,
          (z (sourceSATColumnIndex F points tableType point value)).natAbs ^
            2 := by
      apply Finset.sum_le_sum
      intro value hvalue
      have hnonzero :
          z (sourceSATColumnIndex F points tableType point value) ≠ 0 := by
        intro hzero
        have hodd :=
          (mem_sourceSignedFiberSupport F points z tableType point
            value).mp hvalue
        simp only [hzero, Int.cast_zero, ne_eq, not_true_eq_false] at hodd
      have hpositive := Int.natAbs_pos.mpr hnonzero
      nlinarith
    _ ≤ ∑ value : K,
          (z (sourceSATColumnIndex F points tableType point value)).natAbs ^
            2 :=
      Finset.sum_le_sum_of_subset
        (Finset.subset_univ _)

omit [Field K] [Algebra (ZMod 2) K] in
private theorem sourceSigned_totalFiberSupport_le_integerSquaredNorm
    (F : Formula) (points : Finset K)
    (z : Fin (sourceSATTableDimension F K points) → ℤ) :
    (∑ tableType : sourceSATTableType F,
      ∑ point : sourceSATGridPoint points,
        (sourceSignedFiberSupport F points z tableType point).card) ≤
      integerSquaredNorm z := by
  classical
  calc
    (∑ tableType : sourceSATTableType F,
      ∑ point : sourceSATGridPoint points,
        (sourceSignedFiberSupport F points z tableType point).card) ≤
      ∑ tableType : sourceSATTableType F,
        ∑ point : sourceSATGridPoint points,
          ∑ value : K,
            (z (sourceSATColumnIndex F points
              tableType point value)).natAbs ^ 2 := by
      apply Finset.sum_le_sum
      intro tableType _
      apply Finset.sum_le_sum
      intro point _
      exact sourceSignedFiberSupport_card_le_rowSquaredNorm
        F points z tableType point
    _ = ∑ coordinate : sourceSATTableCoordinate F K points,
          (z (Fintype.equivFin
            (sourceSATTableCoordinate F K points) coordinate)).natAbs ^
              2 := by
      symm
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ position : Fin (sourceSATTableDimension F K points),
          (z position).natAbs ^ 2 :=
      Equiv.sum_comp
        (Fintype.equivFin (sourceSATTableCoordinate F K points))
        (fun position : Fin (sourceSATTableDimension F K points) =>
          (z position).natAbs ^ 2)
    _ = integerSquaredNorm z := rfl

omit [Field K] [Algebra (ZMod 2) K] in
private theorem sourceSigned_typeFiberSupport_le_integerSquaredNorm
    (F : Formula) (points : Finset K)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (tableType : sourceSATTableType F) :
    (∑ point : sourceSATGridPoint points,
      (sourceSignedFiberSupport F points z tableType point).card) ≤
      integerSquaredNorm z := by
  calc
    (∑ point : sourceSATGridPoint points,
      (sourceSignedFiberSupport F points z tableType point).card) ≤
      ∑ otherType : sourceSATTableType F,
        ∑ point : sourceSATGridPoint points,
          (sourceSignedFiberSupport F points z otherType point).card := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun otherType : sourceSATTableType F =>
          ∑ point : sourceSATGridPoint points,
            (sourceSignedFiberSupport F points z otherType point).card)
        (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ tableType)
    _ ≤ integerSquaredNorm z :=
      sourceSigned_totalFiberSupport_le_integerSquaredNorm
        F points z

private def sourceSignedFiberSupportAt
    (F : Formula) (points : Finset K)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (tableType : sourceSATTableType F) (point : K) : Finset K := by
  classical
  exact if hpoint : point ∈ points then
    sourceSignedFiberSupport F points z tableType ⟨point, hpoint⟩
  else ∅

omit [Field K] [Algebra (ZMod 2) K] in
@[simp] private theorem sourceSignedFiberSupportAt_grid
    (F : Formula) (points : Finset K)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (tableType : sourceSATTableType F)
    (point : sourceSATGridPoint points) :
    sourceSignedFiberSupportAt F points z tableType point.val =
      sourceSignedFiberSupport F points z tableType point := by
  classical
  simp only [sourceSignedFiberSupportAt, point.property, ↓reduceDIte, Subtype.coe_eta]

omit [Field K] [Algebra (ZMod 2) K] in
private theorem sourceSignedFiberSupportAt_grid_budget
    (F : Formula) (points : Finset K)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (tableType : sourceSATTableType F) :
    (∑ point ∈ points,
      (sourceSignedFiberSupportAt F points z tableType point).card) ≤
        integerSquaredNorm z := by
  classical
  rw [Finset.sum_subtype points (fun _ => Iff.rfl)]
  · simp_rw [sourceSignedFiberSupportAt_grid]
    exact sourceSigned_typeFiberSupport_le_integerSquaredNorm
      F points z tableType

private theorem sourceSignedFiberSupport_moment
    (F : Formula) (points : Finset K)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (tableType : sourceSATTableType F)
    (point : sourceSATGridPoint points) (j : ℕ) :
    sourceOrdinaryMomentMap F points tableType j
      (fun position => algebraMap (ZMod 2) K
        (z position : ZMod 2)) point =
      supportMoment (sourceSignedFiberSupport F points z tableType point) j := by
  classical
  change
    (∑ value : K,
      algebraMap (ZMod 2) K
        (z (sourceSATColumnIndex F points tableType point value) : ZMod 2) *
          value ^ j) =
      ∑ value ∈ sourceSignedFiberSupport F points z tableType point,
        value ^ j
  unfold sourceSignedFiberSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro value _
  let b : ZMod 2 :=
    (z (sourceSATColumnIndex F points tableType point value) : ZMod 2)
  change algebraMap (ZMod 2) K b * value ^ j =
    if b ≠ 0 then value ^ j else 0
  by_cases hb : b = 0
  · simp only [hb, map_zero, zero_mul, ne_eq, not_true_eq_false, ↓reduceIte]
  · have hone := sourceBinaryResidue_eq_one_of_ne_zero b hb
    simp only [hone, map_one, one_mul, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte]

private theorem sourceSignedFiberSupport_moment_polynomial_of_solves
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hsolves :
      (concreteSATBinaryAffineSystem F fieldBasis points
        variablePlace momentBudget).Solves z)
    (tableType : sourceSATTableType F)
    (j : ℕ) (hj : j ≤ momentBudget) :
    ∃ polynomial : K[X],
      polynomial.natDegree ≤ F.variableCount * j ∧
        ∀ point : sourceSATGridPoint points,
          polynomial.eval point.val =
            supportMoment
              (sourceSignedFiberSupport F points z tableType point) j := by
  have hchecks :=
    (concreteSATBinaryAffineSystem_solves_iff
      F fieldBasis points variablePlace momentBudget z).mp hsolves
  simp only [GapCVP.Core.concreteSATFieldChecks, decide_eq_true_eq] at hchecks
  obtain ⟨_, _, hordinary, _⟩ := hchecks
  have hmem := hordinary tableType
    ⟨j, Nat.lt_succ_iff.mpr hj⟩
  obtain ⟨polynomial, hdegree, heval⟩ :=
    (sourceReedSolomonCode_mem_iff points
      (F.variableCount * j) _).mp hmem
  refine ⟨polynomial, hdegree, ?_⟩
  intro point
  exact (heval point).trans
    (sourceSignedFiberSupport_moment F points z tableType point j)

private def sourceSignedOrdinaryMomentPolynomials
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (tableType : sourceSATTableType F) : ℕ → K[X] := by
  classical
  intro j
  exact if hj : j ≤ momentBudget then
    Classical.choose
      (sourceSignedFiberSupport_moment_polynomial_of_solves F fieldBasis
        points variablePlace momentBudget z hz tableType j hj)
  else 0

private theorem sourceSignedOrdinaryMomentPolynomials_natDegree
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (tableType : sourceSATTableType F)
    (j : ℕ) :
    (sourceSignedOrdinaryMomentPolynomials F fieldBasis points
      variablePlace momentBudget z hz tableType j).natDegree ≤
        F.variableCount * j := by
  classical
  unfold sourceSignedOrdinaryMomentPolynomials
  by_cases hj : j ≤ momentBudget
  · rw [dite_eq_left hj]
    exact (Classical.choose_spec
      (sourceSignedFiberSupport_moment_polynomial_of_solves F fieldBasis
        points variablePlace momentBudget z hz tableType j hj)).1
  · rw [dite_eq_right hj]
    simp only [natDegree_zero, zero_le]

private theorem sourceSignedOrdinaryMomentPolynomials_eval
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (tableType : sourceSATTableType F)
    (point : sourceSATGridPoint points)
    (j : ℕ) (hj : j ≤ momentBudget) :
    (sourceSignedOrdinaryMomentPolynomials F fieldBasis points
      variablePlace momentBudget z hz tableType j).eval point.val =
      supportMoment
        (sourceSignedFiberSupport F points z tableType point) j := by
  classical
  unfold sourceSignedOrdinaryMomentPolynomials
  rw [dite_eq_left hj]
  exact (Classical.choose_spec
    (sourceSignedFiberSupport_moment_polynomial_of_solves F fieldBasis
      points variablePlace momentBudget z hz tableType j hj)).2 point

private theorem sourceSigned_globalSupportMoment_zero
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (point : sourceSATGridPoint points) :
    supportMoment
      (sourceSignedFiberSupport F points z (.inl ()) point) 0 =
        (1 : K) := by
  have hchecks :=
    (concreteSATBinaryAffineSystem_solves_iff F fieldBasis points
      variablePlace momentBudget z).mp hz
  have checks := hchecks
  simp only [GapCVP.Core.concreteSATFieldChecks, decide_eq_true_eq] at checks
  have hnormalization := congrFun checks.1 point
  change
    (∑ value : K,
      algebraMap (ZMod 2) K
        (z (sourceSATColumnIndex F points (.inl ()) point value) : ZMod 2)) = 1
    at hnormalization
  calc
    supportMoment
        (sourceSignedFiberSupport F points z (.inl ()) point) 0 =
      sourceOrdinaryMomentMap F points (.inl ()) 0
        (fun position => algebraMap (ZMod 2) K
          (z position : ZMod 2)) point :=
      (sourceSignedFiberSupport_moment
        F points z (.inl ()) point 0).symm
    _ = 1 := by
      change
        (∑ value : K,
          algebraMap (ZMod 2) K
            (z (sourceSATColumnIndex F points (.inl ()) point value) :
              ZMod 2) * value ^ 0) = 1
      simpa only [List.get_eq_getElem, map_intCast, pow_zero, mul_one] using hnormalization

private theorem sourceSigned_globalSupportMoment_eq_clauseSubtypeSum
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (clause : Fin F.clauses.length)
    (point : sourceSATGridPoint points)
    (j : ℕ) :
    supportMoment
      (sourceSignedFiberSupport F points z (.inl ()) point) j =
        ∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
          supportMoment
            (sourceSignedFiberSupport F points z
              (.inr ⟨clause, tuple⟩) point) j := by
  classical
  let values : Fin (sourceSATTableDimension F K points) → K :=
    fun position => algebraMap (ZMod 2) K (z position : ZMod 2)
  have hchecks : concreteSATFieldChecks F points variablePlace
      momentBudget values :=
    (concreteSATBinaryAffineSystem_solves_iff F fieldBasis points
      variablePlace momentBudget z).mp hz
  have checks := hchecks
  simp only [GapCVP.Core.concreteSATFieldChecks, decide_eq_true_eq] at checks
  have hrefinement : ∀ value : K,
      values (sourceSATColumnIndex F points (.inl ()) point value) =
        ∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
          values (sourceSATColumnIndex F points
            (.inr ⟨clause, tuple⟩) point value) := by
    intro value
    have hpoint := congrFun (checks.2.1 clause) (point, value)
    change
      values (sourceSATColumnIndex F points (.inl ()) point value) -
        (∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
          values (sourceSATColumnIndex F points
            (.inr ⟨clause, tuple⟩) point value)) = 0 at hpoint
    exact sub_eq_zero.mp hpoint
  calc
    supportMoment
        (sourceSignedFiberSupport F points z (.inl ()) point) j =
      sourceOrdinaryMomentMap F points (.inl ()) j values point :=
      (sourceSignedFiberSupport_moment
        F points z (.inl ()) point j).symm
    _ = ∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
        sourceOrdinaryMomentMap F points (.inr ⟨clause, tuple⟩) j
          values point := by
      change
        (∑ value : K,
          values
            (sourceSATColumnIndex F points (.inl ()) point value) *
              value ^ j) =
          ∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
            ∑ value : K,
              values
                (sourceSATColumnIndex F points
                  (.inr ⟨clause, tuple⟩) point value) * value ^ j
      simp_rw [hrefinement, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
        supportMoment
          (sourceSignedFiberSupport F points z
            (.inr ⟨clause, tuple⟩) point) j := by
      apply Finset.sum_congr rfl
      intro tuple _
      exact sourceSignedFiberSupport_moment
        F points z (.inr ⟨clause, tuple⟩) point j

private theorem sourceSignedShiftedMoment_eq_fiberPowerSum
    (F : Formula) (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (j : ℕ) (point : sourceSATGridPoint points) :
    sourceShiftedMomentMap F points variablePlace
        clause tuple localVar j
        (fun position => algebraMap (ZMod 2) K
          (z position : ZMod 2)) point =
      ∑ value ∈ sourceSignedFiberSupport F points z
        (.inr ⟨clause, tuple⟩) point,
          ((value - sourceSATFieldBit (K := K) (tuple.val localVar)) /
            (point.val - variablePlace localVar.val)) ^ j := by
  classical
  change
    (∑ value : K,
      algebraMap (ZMod 2) K
        (z (sourceSATColumnIndex F points
          (.inr ⟨clause, tuple⟩) point value) : ZMod 2) *
        ((value - sourceSATFieldBit (K := K) (tuple.val localVar)) /
          (point.val - variablePlace localVar.val)) ^ j) =
      ∑ value ∈ sourceSignedFiberSupport F points z
        (.inr ⟨clause, tuple⟩) point,
          ((value - sourceSATFieldBit (K := K) (tuple.val localVar)) /
            (point.val - variablePlace localVar.val)) ^ j
  unfold sourceSignedFiberSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro value _
  let b : ZMod 2 :=
    (z (sourceSATColumnIndex F points
      (.inr ⟨clause, tuple⟩) point value) : ZMod 2)
  change
    algebraMap (ZMod 2) K b *
        ((value - sourceSATFieldBit (K := K) (tuple.val localVar)) /
          (point.val - variablePlace localVar.val)) ^ j =
      if b ≠ 0 then
        ((value - sourceSATFieldBit (K := K) (tuple.val localVar)) /
          (point.val - variablePlace localVar.val)) ^ j
      else 0
  by_cases hb : b = 0
  · simp only [hb, map_zero, List.get_eq_getElem, zero_mul, ne_eq, not_true_eq_false, ↓reduceIte]
  · have hone := sourceBinaryResidue_eq_one_of_ne_zero b hb
    simp only [hone, map_one, List.get_eq_getElem, one_mul, ne_eq, one_ne_zero, not_false_eq_true,
        ↓reduceIte]

private theorem sourceSigned_exists_shiftedMomentPolynomial
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (j : ℕ) (hj : j ≤ momentBudget) :
    ∃ moment : K[X],
      moment.natDegree ≤ (F.variableCount - 1) * j ∧
        ∀ point : sourceSATGridPoint points,
          moment.eval point.val =
            ∑ value ∈ sourceSignedFiberSupport F points z
              (.inr ⟨clause, tuple⟩) point,
                ((value - sourceSATFieldBit (K := K) (tuple.val localVar)) /
                  (point.val - variablePlace localVar.val)) ^ j := by
  have hchecks :=
    (concreteSATBinaryAffineSystem_solves_iff F fieldBasis points
      variablePlace momentBudget z).mp hz
  have checks := hchecks
  simp only [GapCVP.Core.concreteSATFieldChecks, decide_eq_true_eq] at checks
  have hmoment := checks.2.2.2 clause tuple localVar
    (⟨j, Nat.lt_succ_iff.mpr hj⟩ : Fin (momentBudget + 1))
  obtain ⟨moment, hdegree, hvalues⟩ :=
    (sourceReedSolomonCode_mem_iff points
      ((F.variableCount - 1) * j) _).mp hmoment
  refine ⟨moment, hdegree, ?_⟩
  intro point
  rw [hvalues point]
  exact sourceSignedShiftedMoment_eq_fiberPowerSum
    F points variablePlace z clause tuple localVar j point

private def sourceSignedShiftedMomentPolynomials
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable) : ℕ → K[X] := by
  classical
  intro j
  exact if hj : j ≤ momentBudget then
    Classical.choose
      (sourceSigned_exists_shiftedMomentPolynomial
        F fieldBasis points variablePlace momentBudget z hz
        clause tuple localVar j hj)
  else 0

private theorem sourceSignedShiftedMomentPolynomials_natDegree
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (j : ℕ) :
    (sourceSignedShiftedMomentPolynomials F fieldBasis points
      variablePlace momentBudget z hz clause tuple localVar j).natDegree ≤
        (F.variableCount - 1) * j := by
  classical
  unfold sourceSignedShiftedMomentPolynomials
  split
  next hj =>
    exact
      (Classical.choose_spec
        (sourceSigned_exists_shiftedMomentPolynomial
          F fieldBasis points variablePlace momentBudget z hz
          clause tuple localVar j hj)).1
  next _ => simp only [natDegree_zero, zero_le]

private theorem sourceSignedShiftedMomentPolynomials_eval
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (j : ℕ) (hj : j ≤ momentBudget)
    (point : sourceSATGridPoint points) :
    (sourceSignedShiftedMomentPolynomials F fieldBasis points
      variablePlace momentBudget z hz clause tuple localVar j).eval point.val =
        ∑ value ∈ sourceSignedFiberSupport F points z
          (.inr ⟨clause, tuple⟩) point,
            ((value - sourceSATFieldBit (K := K) (tuple.val localVar)) /
              (point.val - variablePlace localVar.val)) ^ j := by
  classical
  unfold sourceSignedShiftedMomentPolynomials
  rw [dite_eq_left hj]
  exact
    (Classical.choose_spec
      (sourceSigned_exists_shiftedMomentPolynomial
        F fieldBasis points variablePlace momentBudget z hz
        clause tuple localVar j hj)).2 point

private theorem sourceSigned_shiftedMomentCombination_natDegree
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (tableType : sourceSATTableType F)
    (bit : K) (j : ℕ) :
    (shiftedMomentCombination
      (sourceSignedOrdinaryMomentPolynomials F fieldBasis points
        variablePlace momentBudget z hz tableType)
      bit j).natDegree ≤ F.variableCount * j := by
  classical
  have hterms : ∀ l ∈ Finset.range (j + 1),
      (Polynomial.C ((j.choose l : K) * (-bit) ^ (j - l)) *
        sourceSignedOrdinaryMomentPolynomials F fieldBasis points
          variablePlace momentBudget z hz tableType l).natDegree ≤
            F.variableCount * j := by
    intro l hl
    calc
      (Polynomial.C ((j.choose l : K) * (-bit) ^ (j - l)) *
        sourceSignedOrdinaryMomentPolynomials F fieldBasis points
          variablePlace momentBudget z hz tableType l).natDegree ≤
          (Polynomial.C ((j.choose l : K) * (-bit) ^ (j - l))).natDegree +
            (sourceSignedOrdinaryMomentPolynomials F fieldBasis points
              variablePlace momentBudget z hz tableType l).natDegree :=
        Polynomial.natDegree_mul_le
      _ = (sourceSignedOrdinaryMomentPolynomials F fieldBasis points
              variablePlace momentBudget z hz tableType l).natDegree := by
        rw [Polynomial.natDegree_C, Nat.zero_add]
      _ ≤ F.variableCount * l :=
        sourceSignedOrdinaryMomentPolynomials_natDegree F
          fieldBasis points variablePlace momentBudget z hz tableType l
      _ ≤ F.variableCount * j :=
        Nat.mul_le_mul_left F.variableCount
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl))
  have hmember :
      shiftedMomentCombination
          (sourceSignedOrdinaryMomentPolynomials F fieldBasis points
            variablePlace momentBudget z hz tableType)
          bit j ∈ Polynomial.degreeLE K
            (F.variableCount * j : WithBot ℕ) := by
    unfold shiftedMomentCombination
    apply Submodule.sum_mem
    intro l hl
    exact Polynomial.mem_degreeLE.mpr
      (Polynomial.natDegree_le_iff_degree_le.mp (hterms l hl))
  exact Polynomial.natDegree_le_iff_degree_le.mpr
    (Polynomial.mem_degreeLE.mp hmember)

private theorem sourceSigned_scaledShiftedMoment_natDegree
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (j : ℕ) :
    (((Polynomial.X - Polynomial.C
        (variablePlace localVar.val)) ^ j) *
      sourceSignedShiftedMomentPolynomials F fieldBasis points
        variablePlace momentBudget z hz clause tuple localVar j).natDegree ≤
      F.variableCount * j := by
  have hm : 0 < F.variableCount :=
    Nat.zero_lt_of_lt localVar.val.isLt
  calc
    (((Polynomial.X - Polynomial.C
        (variablePlace localVar.val)) ^ j) *
      sourceSignedShiftedMomentPolynomials F fieldBasis points
        variablePlace momentBudget z hz clause tuple localVar j).natDegree ≤
      ((Polynomial.X - Polynomial.C
          (variablePlace localVar.val)) ^ j).natDegree +
        (sourceSignedShiftedMomentPolynomials F fieldBasis points
          variablePlace momentBudget z hz clause tuple localVar j).natDegree :=
      Polynomial.natDegree_mul_le
    _ = j +
        (sourceSignedShiftedMomentPolynomials F fieldBasis points
          variablePlace momentBudget z hz clause tuple localVar j).natDegree := by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      simp only [mul_one]
    _ ≤ j + (F.variableCount - 1) * j :=
      Nat.add_le_add_left
        (sourceSignedShiftedMomentPolynomials_natDegree F
          fieldBasis points variablePlace momentBudget z hz
          clause tuple localVar j) j
    _ = F.variableCount * j := by
      have hone : 1 ≤ F.variableCount := hm
      have hdecomposition : 1 + (F.variableCount - 1) = F.variableCount := by
        omega
      calc
        j + (F.variableCount - 1) * j =
            (1 + (F.variableCount - 1)) * j := by ring
        _ = F.variableCount * j := by rw [hdecomposition]

private theorem sourceSigned_shiftedMomentPolynomial_identity
    (F : Formula)
    {e : ℕ} (fieldBasis : Module.Basis (Fin e) (ZMod 2) K)
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (z : Fin (sourceSATTableDimension F K points) → ℤ)
    (hz : (concreteSATBinaryAffineSystem F fieldBasis points
      variablePlace momentBudget).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (j : ℕ) (hj : j ≤ momentBudget)
    (hplace : ∀ point : sourceSATGridPoint points,
      point.val - variablePlace localVar.val ≠ 0)
    (hgrid : F.variableCount * j < points.card) :
    (Polynomial.X - Polynomial.C (variablePlace localVar.val)) ^ j *
        sourceSignedShiftedMomentPolynomials F fieldBasis points
          variablePlace momentBudget z hz clause tuple localVar j =
      shiftedMomentCombination
        (sourceSignedOrdinaryMomentPolynomials F fieldBasis points
          variablePlace momentBudget z hz (.inr ⟨clause, tuple⟩))
        (sourceSATFieldBit (K := K) (tuple.val localVar)) j := by
  classical
  apply polynomial_eq_of_agree_on_points points
  · apply lt_of_le_of_lt (max_le
      (sourceSigned_scaledShiftedMoment_natDegree F
        fieldBasis points variablePlace momentBudget z hz
        clause tuple localVar j)
      (sourceSigned_shiftedMomentCombination_natDegree F
        fieldBasis points variablePlace momentBudget z hz
        (.inr ⟨clause, tuple⟩)
        (sourceSATFieldBit (K := K) (tuple.val localVar)) j))
      hgrid
  · intro point hpoint
    let gridPoint : sourceSATGridPoint points := ⟨point, hpoint⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [sourceSignedShiftedMomentPolynomials_eval F
      fieldBasis points variablePlace momentBudget z hz clause tuple localVar
      j hj gridPoint]
    rw [scaled_shifted_supportMoment
      (sourceSignedFiberSupport F points z
        (.inr ⟨clause, tuple⟩) gridPoint)
      (sourceSATFieldBit (K := K) (tuple.val localVar))
      (point - variablePlace localVar.val) j
      (hplace gridPoint)]
    unfold shiftedMomentCombination
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C]
    apply Finset.sum_congr rfl
    intro l hl
    have hlbudget : l ≤ momentBudget := by
      have hlj : l ≤ j :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      exact hlj.trans hj
    rw [sourceSignedOrdinaryMomentPolynomials_eval F
      fieldBasis points variablePlace momentBudget z hz
      (.inr ⟨clause, tuple⟩) gridPoint l hlbudget]

end

section

open Finset Polynomial

private theorem source_variable_and_hankel_exceptions_ten_mul_le_field_size
    {N q m : ℕ}
    (hN : 100 ≤ N)
    (hq : N ^ 200 ≤ q)
    (hm : m ≤ N) :
    10 * (m + N ^ 9) ≤ q := by
  have hNnine : N ≤ N ^ 9 := by
    calc
      N = N ^ 1 := by simp only [pow_one]
      _ ≤ N ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc
    10 * (m + N ^ 9) ≤ 10 * (N ^ 9 + N ^ 9) := by
      gcongr
      exact hm.trans hNnine
    _ = 20 * N ^ 9 := by ring
    _ ≤ N * N ^ 9 := Nat.mul_le_mul_right (N ^ 9) (by omega)
    _ = N ^ 10 :=
      (mul_comm N (N ^ 9)).trans (pow_succ N 9).symm
    _ ≤ N ^ 200 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ q := hq

private theorem source_hankel_denominator_natDegree_le_power
    {K : Type*} [Field K]
    (moments : ℕ → K[X])
    {N d h : ℕ}
    (hd : d ≤ N)
    (hh : h ≤ N ^ 4)
    (hmoments : ∀ j : ℕ, (moments j).natDegree ≤ d * j) :
    (genericHankelDenominator h moments).natDegree ≤ N ^ 9 := by
  calc
    (genericHankelDenominator h moments).natDegree ≤
        d * h * (h - 1) :=
      genericHankelDenominator_natDegree_le_sharp moments d
        (fun j _ => hmoments j)
    _ ≤ N * (N ^ 4) * (N ^ 4) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul hd hh) (by omega)
    _ = N ^ 9 := by
      rw [show (9 : ℕ) = 1 + 4 + 4 by norm_num,
        pow_add, pow_add, pow_one]

end

section

private theorem sourceOneHotCompletenessRadius_le_two_sqrt
    (F : Formula) {α : Type*} (points : Finset α)
    (hpoints : 0 < points.card) :
    ((sourceOneHotCompletenessRadius F points : ℚ) : ℝ) ≤
      2 * Real.sqrt
        (((F.clauses.length + 1) * points.card : ℕ) : ℝ) := by
  have hweight : 0 < (F.clauses.length + 1) * points.card :=
    Nat.mul_pos (Nat.zero_lt_succ F.clauses.length) hpoints
  have hreal :
      (1 : ℝ) ≤
        (((F.clauses.length + 1) * points.card : ℕ) : ℝ) := by
    exact_mod_cast hweight
  have hroot :
      (1 : ℝ) ≤
        Real.sqrt (((F.clauses.length + 1) * points.card : ℕ) : ℝ) :=
    Real.one_le_sqrt.mpr hreal
  have hhalf :
      (2 : ℝ)⁻¹ ≤
        Real.sqrt (((F.clauses.length + 1) * points.card : ℕ) : ℝ) := by
    calc
      (2 : ℝ)⁻¹ ≤ 1 := by norm_num
      _ ≤ Real.sqrt
        (((F.clauses.length + 1) * points.card : ℕ) : ℝ) := hroot
  have hceil := Nat.ceil_le_two_mul hhalf
  unfold sourceOneHotCompletenessRadius
  norm_num only [Rat.cast_natCast]
  exact hceil

theorem sourceOneHotCompletenessRadius_squared_le_four_weight
    (F : Formula) {α : Type*} (points : Finset α)
    (hpoints : 0 < points.card) :
    ((sourceOneHotCompletenessRadius F points : ℚ) : ℝ) ^ 2 ≤
      4 * (((F.clauses.length + 1) * points.card : ℕ) : ℝ) := by
  let weight : ℝ :=
    (((F.clauses.length + 1) * points.card : ℕ) : ℝ)
  let radius : ℝ :=
    ((sourceOneHotCompletenessRadius F points : ℚ) : ℝ)
  have hbound : radius ≤ 2 * Real.sqrt weight :=
    sourceOneHotCompletenessRadius_le_two_sqrt F points hpoints
  have hradius : 0 ≤ radius := by
    dsimp [radius]
    exact_mod_cast le_of_lt
      (sourceOneHotCompletenessRadius_pos F points hpoints)
  have hweight : 0 ≤ weight := by
    dsimp [weight]
    positivity
  have hroot : 0 ≤ Real.sqrt weight := Real.sqrt_nonneg weight
  have hsquare : Real.sqrt weight ^ 2 = weight :=
    Real.sq_sqrt hweight
  have hproduct :
      0 ≤ (2 * Real.sqrt weight - radius) *
        (2 * Real.sqrt weight + radius) :=
    mul_nonneg (sub_nonneg.mpr hbound) (by positivity)
  change radius ^ 2 ≤ 4 * weight
  linarith

theorem source_oneHot_weight_four_mul_le
    {N q ell points : ℕ}
    (hN : 100 ≤ N)
    (hell : ell ≤ N)
    (hpoints : points ≤ q) :
    4 * ((ell + 1) * points) ≤ 8 * q * N := by
  have htypes : ell + 1 ≤ 2 * N := by omega
  calc
    4 * ((ell + 1) * points) ≤ 4 * ((2 * N) * q) := by
      gcongr
    _ = 8 * q * N := by ring

open scoped BigOperators

variable {E Γ₀ : Type*} [Field E] [LinearOrderedCommMonoidWithZero Γ₀]

/-- GapCVP reduction support. -/
noncomputable def inverseTransposeVandermonde {h : ℕ}
    (roots : Fin h → E) : Matrix (Fin h) (Fin h) E :=
  ((Matrix.vandermonde roots).transpose)⁻¹

private theorem valuation_coordinate_le_of_left_inverse
    {h : ℕ} (valuation : Valuation E Γ₀)
    (matrix inverse : Matrix (Fin h) (Fin h) E)
    (hinverse : inverse * matrix = 1)
    (bound : Γ₀)
    (hentries : ∀ i j, valuation (inverse i j) ≤ bound)
    (coordinates : Fin h → E)
    (houtputs : ∀ i, valuation ((matrix.mulVec coordinates) i) ≤ 1) :
    ∀ i, valuation (coordinates i) ≤ bound := by
  classical
  have hreconstruct : inverse.mulVec (matrix.mulVec coordinates) = coordinates := by
    rw [Matrix.mulVec_mulVec, hinverse, Matrix.one_mulVec]
  intro i
  rw [← congrFun hreconstruct i]
  change valuation (∑ j : Fin h,
    inverse i j * (matrix.mulVec coordinates) j) ≤ bound
  apply valuation.map_sum_le
  intro j _
  rw [valuation.map_mul]
  calc
    valuation (inverse i j) * valuation ((matrix.mulVec coordinates) j)
        ≤ bound * 1 := mul_le_mul' (hentries i j) (houtputs j)
    _ = bound := mul_one bound

private theorem valuation_root_power_le_of_shifted_moments
    {h : ℕ} (valuation : Valuation E Γ₀)
    (roots : Fin h → E) (hroots : Function.Injective roots)
    (bound : Γ₀) (z : ℕ)
    (hinverse : ∀ i j,
      valuation (inverseTransposeVandermonde roots i j) ≤ bound)
    (hmoments : ∀ r : Fin h,
      valuation (∑ i : Fin h, roots i ^ (z + r.val)) ≤ 1) :
    ∀ i : Fin h, valuation (roots i ^ z) ≤ bound := by
  let V : Matrix (Fin h) (Fin h) E := (Matrix.vandermonde roots).transpose
  have hdet : V.det ≠ 0 := by
    dsimp [V]
    simpa using (Matrix.det_vandermonde_ne_zero_iff.mpr hroots)
  have hleft : V⁻¹ * V = 1 :=
    Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.mpr hdet)
  apply valuation_coordinate_le_of_left_inverse valuation V V⁻¹ hleft bound
    (by simpa [V, inverseTransposeVandermonde] using hinverse)
    (fun i => roots i ^ z)
  intro r
  simpa [V, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
    ← pow_add, Nat.add_comm] using hmoments r

theorem valuation_roots_integral_of_shifted_moments
    {h : ℕ} (valuation : Valuation E Γ₀)
    (roots : Fin h → E) (hroots : Function.Injective roots)
    (bound : Γ₀) (z : ℕ)
    (hinverse : ∀ i j,
      valuation (inverseTransposeVandermonde roots i j) ≤ bound)
    (hmoments : ∀ r : Fin h,
      valuation (∑ i : Fin h, roots i ^ (z + r.val)) ≤ 1)
    (hseparation : ∀ i : Fin h,
      1 < valuation (roots i) → bound < valuation (roots i ^ z)) :
    ∀ i : Fin h, valuation (roots i) ≤ 1 := by
  intro i
  by_contra hnot
  have hroot : 1 < valuation (roots i) := lt_of_not_ge hnot
  have hbounded := valuation_root_power_le_of_shifted_moments
    valuation roots hroots bound z hinverse hmoments i
  exact (not_lt_of_ge hbounded) (hseparation i hroot)

end

section

open scoped BigOperators
open Finset Polynomial

private theorem valuation_matrix_det_le_pow
    {E Γ₀ : Type*} [Field E]
    [LinearOrderedCommGroupWithZero Γ₀]
    (valuation : Valuation E Γ₀)
    {h : ℕ} (matrix : Matrix (Fin h) (Fin h) E)
    (bound : Γ₀)
    (hentries : ∀ i j, valuation (matrix i j) ≤ bound) :
    valuation matrix.det ≤ bound ^ h := by
  classical
  rw [Matrix.det_apply']
  apply valuation.map_sum_le
  intro permutation _
  rw [valuation.map_mul]
  have hsign :
      valuation (((Equiv.Perm.sign permutation : ℤ) : E)) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with
      hpositive | hnegative
    · simp only [hpositive, Units.val_one, Int.cast_one, map_one]
    · simp only [hnegative, Units.val_neg, Units.val_one, Int.reduceNeg, Int.cast_neg,
        Int.cast_one,
          Valuation.map_neg, map_one]
  rw [hsign, one_mul]
  rw [show valuation (∏ i, matrix (permutation i) i) =
      ∏ i, valuation (matrix (permutation i) i) by simp only [map_prod]]
  simpa only [ge_iff_le, card_univ, Fintype.card_fin] using
      (Finset.prod_le_pow_card (Finset.univ : Finset (Fin h)) (fun i => valuation (matrix
          (permutation i) i)) bound
        (fun i _ => hentries (permutation i) i))

private theorem valuation_matrix_adjugate_le_pow
    {E Γ₀ : Type*} [Field E]
    [LinearOrderedCommGroupWithZero Γ₀]
    (valuation : Valuation E Γ₀)
    {h : ℕ} (matrix : Matrix (Fin h) (Fin h) E)
    (bound : Γ₀) (hbound : 1 ≤ bound)
    (hentries : ∀ i j, valuation (matrix i j) ≤ bound)
    (i j : Fin h) :
    valuation (matrix.adjugate i j) ≤ bound ^ h := by
  classical
  rw [Matrix.adjugate_apply]
  apply valuation_matrix_det_le_pow valuation
    (matrix.updateRow j (Pi.single i 1)) bound
  intro row column
  by_cases hrow : row = j
  · subst row
    by_cases hcolumn : column = i
    · simp only [hcolumn, Matrix.updateRow_apply, ↓reduceIte, Pi.single_eq_same, map_one, hbound]
    · simp only [Matrix.updateRow_apply, ↓reduceIte, ne_eq, hcolumn, not_false_eq_true,
        Pi.single_eq_of_ne,
          map_zero, zero_le]
  · simpa only [Matrix.updateRow_apply, hrow, ↓reduceIte] using hentries row column

private theorem valuation_matrix_inverse_le_det_inv_mul_pow
    {E Γ₀ : Type*} [Field E]
    [LinearOrderedCommGroupWithZero Γ₀]
    (valuation : Valuation E Γ₀)
    {h : ℕ} (matrix : Matrix (Fin h) (Fin h) E)
    (bound : Γ₀) (hbound : 1 ≤ bound)
    (hentries : ∀ i j, valuation (matrix i j) ≤ bound)
    (i j : Fin h) :
    valuation (matrix⁻¹ i j) ≤
      (valuation matrix.det)⁻¹ * bound ^ h := by
  classical
  rw [Matrix.inv_def]
  change valuation
    (Ring.inverse matrix.det * matrix.adjugate i j) ≤
      (valuation matrix.det)⁻¹ * bound ^ h
  rw [Ring.inverse_eq_inv, valuation.map_mul, valuation.map_inv]
  exact mul_le_mul_of_nonneg_left
    (valuation_matrix_adjugate_le_pow
      valuation matrix bound hbound hentries i j) zero_le

private theorem valuation_inverseTransposeVandermonde_le_det_inv_mul_pow
    {E Γ₀ : Type*} [Field E]
    [LinearOrderedCommGroupWithZero Γ₀]
    (valuation : Valuation E Γ₀)
    {h : ℕ} (roots : Fin h → E)
    (bound : Γ₀) (hbound : 1 ≤ bound)
    (hentries : ∀ i j : Fin h,
      valuation (roots j ^ i.val) ≤ bound)
    (i j : Fin h) :
    valuation (inverseTransposeVandermonde roots i j) ≤
      (valuation (Matrix.vandermonde roots).det)⁻¹ * bound ^ h := by
  classical
  unfold inverseTransposeVandermonde
  have hmatrix := valuation_matrix_inverse_le_det_inv_mul_pow
    valuation (Matrix.vandermonde roots).transpose
    bound hbound (fun row column => hentries row column) i j
  simpa only [ge_iff_le, Matrix.det_transpose] using hmatrix

private theorem valuation_root_le_of_monic_coefficient_bound
    {E Γ₀ : Type*} [Field E]
    [LinearOrderedCommGroupWithZero Γ₀]
    (valuation : Valuation E Γ₀)
    {h : ℕ} (coefficients : Fin h → E)
    (root : E) (bound : Γ₀)
    (hbound : 1 ≤ bound)
    (hcoefficients : ∀ i : Fin h,
      valuation (coefficients i) ≤ bound)
    (hroot : root ^ h +
      ∑ i : Fin h, coefficients i * root ^ i.val = 0) :
    valuation root ≤ bound := by
  classical
  by_cases hzero : h = 0
  · subst h
    simp only [pow_zero, univ_eq_empty, sum_empty, add_zero, one_ne_zero] at hroot
  · have hpositive : 0 < h := Nat.pos_of_ne_zero hzero
    by_contra hnot
    have hlarge : bound < valuation root := lt_of_not_ge hnot
    have hrootOne : 1 < valuation root := lt_of_le_of_lt hbound hlarge
    have hrootPositive : 0 < valuation root := lt_trans zero_lt_one hrootOne
    have hsum :
        valuation (∑ i : Fin h, coefficients i * root ^ i.val) ≤
          bound * valuation root ^ (h - 1) := by
      apply valuation.map_sum_le
      intro i _
      rw [valuation.map_mul, valuation.map_pow]
      calc
        valuation (coefficients i) * valuation root ^ i.val ≤
            bound * valuation root ^ i.val :=
          mul_le_mul_of_nonneg_right (hcoefficients i) zero_le
        _ ≤ bound * valuation root ^ (h - 1) := by
          apply mul_le_mul_of_nonneg_left _ zero_le
          apply pow_le_pow_right' (le_of_lt hrootOne)
          have hi := i.isLt
          omega
    have hleading :
        valuation root ^ h ≤ bound * valuation root ^ (h - 1) := by
      calc
        valuation root ^ h = valuation (root ^ h) :=
          (valuation.map_pow root h).symm
        _ = valuation (-(∑ i : Fin h, coefficients i * root ^ i.val)) := by
          congr 1
          exact eq_neg_of_add_eq_zero_left hroot
        _ = valuation (∑ i : Fin h, coefficients i * root ^ i.val) :=
          valuation.map_neg _
        _ ≤ bound * valuation root ^ (h - 1) := hsum
    have hstrict :
        bound * valuation root ^ (h - 1) < valuation root ^ h := by
      calc
        bound * valuation root ^ (h - 1) <
            valuation root * valuation root ^ (h - 1) :=
          mul_lt_mul_of_pos_right hlarge (pow_pos hrootPositive _)
        _ = valuation root ^ h := by
          rw [mul_comm, ← pow_succ]
          congr 1
          omega
    exact (not_lt_of_ge hleading) hstrict

private theorem scaled_shifted_rootMoment
    {E : Type*} [Field E]
    {h : ℕ} (roots : Fin h → E)
    (hinjective : Function.Injective roots)
    (bit place : E) (hplace : place ≠ 0) (j : ℕ) :
    place ^ j * rootMoment
        (fun i => (roots i - bit) / place) j =
      ∑ l ∈ Finset.range (j + 1),
        (j.choose l : E) * (-bit) ^ (j - l) * rootMoment roots l := by
  classical
  have hshift :
      rootMoment (fun i => (roots i - bit) / place) j =
        ∑ value ∈ enumeratedRootSupport roots,
          ((value - bit) / place) ^ j := by
    unfold rootMoment enumeratedRootSupport
    symm
    rw [Finset.sum_image]
    intro first _ second _ hequal
    exact hinjective hequal
  calc
    place ^ j * rootMoment (fun i => (roots i - bit) / place) j =
      place ^ j *
        (∑ value ∈ enumeratedRootSupport roots,
          ((value - bit) / place) ^ j) := by rw [hshift]
    _ = ∑ l ∈ Finset.range (j + 1),
        (j.choose l : E) * (-bit) ^ (j - l) *
          supportMoment (enumeratedRootSupport roots) l :=
      scaled_shifted_supportMoment
        (enumeratedRootSupport roots) bit place j hplace
    _ = ∑ l ∈ Finset.range (j + 1),
        (j.choose l : E) * (-bit) ^ (j - l) * rootMoment roots l := by
      apply Finset.sum_congr rfl
      intro l _
      rw [supportMoment_enumeratedRootSupport roots hinjective l]

private theorem map_shiftedMomentCombination_eq_rootMomentCombination
    {k E : Type*} [Field k] [Field E]
    [Algebra k E] [Algebra k[X] E] [IsScalarTower k k[X] E]
    (moments : ℕ → k[X]) (bit : k) (j : ℕ)
    {h : ℕ} (roots : Fin h → E)
    (hmoments : ∀ l : ℕ, l ≤ j →
      algebraMap k[X] E (moments l) = rootMoment roots l) :
    algebraMap k[X] E (shiftedMomentCombination moments bit j) =
      ∑ l ∈ Finset.range (j + 1),
        (j.choose l : E) * (-(algebraMap k E bit)) ^ (j - l) *
          rootMoment roots l := by
  classical
  have hbit :
      algebraMap k[X] E (Polynomial.C bit) = algebraMap k E bit := by
    change algebraMap k[X] E (algebraMap k k[X] bit) = algebraMap k E bit
    exact (IsScalarTower.algebraMap_apply k k[X] E bit).symm
  unfold shiftedMomentCombination
  simp only [map_sum, map_mul, map_pow]
  apply Finset.sum_congr rfl
  intro l hl
  have hlj : l ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [hmoments l hlj]
  simp only [map_natCast, map_neg, hbit]

private theorem shiftedGenericRootMoment_eq_mappedShiftedPolynomial
    {k E : Type*} [Field k] [Field E]
    [Algebra k E] [Algebra k[X] E] [IsScalarTower k k[X] E]
    (moments : ℕ → k[X]) (shifted : k[X])
    (variablePlace bit : k) (j : ℕ)
    {h : ℕ} (roots : Fin h → E)
    (hinjective : Function.Injective roots)
    (hplace :
      algebraMap k[X] E (Polynomial.X - Polynomial.C variablePlace) ≠ 0)
    (hmoments : ∀ l : ℕ, l ≤ j →
      algebraMap k[X] E (moments l) = rootMoment roots l)
    (hpolynomial :
      (Polynomial.X - Polynomial.C variablePlace) ^ j * shifted =
        shiftedMomentCombination moments bit j) :
    rootMoment
        (fun i =>
          (roots i - algebraMap k E bit) /
            algebraMap k[X] E
              (Polynomial.X - Polynomial.C variablePlace)) j =
      algebraMap k[X] E shifted := by
  classical
  let place : E :=
    algebraMap k[X] E (Polynomial.X - Polynomial.C variablePlace)
  have hscaled := scaled_shifted_rootMoment roots hinjective
    (algebraMap k E bit) place hplace j
  have hcombination :=
    map_shiftedMomentCombination_eq_rootMomentCombination
      moments bit j roots hmoments
  have hmap := congrArg (algebraMap k[X] E) hpolynomial
  have hequality :
      place ^ j * rootMoment
          (fun i => (roots i - algebraMap k E bit) / place) j =
        place ^ j * algebraMap k[X] E shifted := by
    calc
      place ^ j * rootMoment
          (fun i => (roots i - algebraMap k E bit) / place) j =
        ∑ l ∈ Finset.range (j + 1),
          (j.choose l : E) * (-(algebraMap k E bit)) ^ (j - l) *
            rootMoment roots l := hscaled
      _ = algebraMap k[X] E
          (shiftedMomentCombination moments bit j) := hcombination.symm
      _ = place ^ j * algebraMap k[X] E shifted := by
        symm
        simpa only [map_sub, map_mul, map_pow, place] using hmap
  exact mul_left_cancel₀ (pow_ne_zero j hplace) hequality

end

section

open scoped BigOperators symmDiff
open Polynomial Finset

private theorem genericMomentSupportPolynomial_natDegree
    {K : Type*} [Field K]
    (h : ℕ) (moments : ℕ → K[X]) :
    (genericMomentSupportPolynomial h moments).natDegree = h := by
  unfold genericMomentSupportPolynomial
  apply Polynomial.natDegree_eq_of_degree_eq_some
  calc
    (Polynomial.X ^ h +
      ∑ i : Fin h,
        Polynomial.C (genericHankelCoefficient h moments i) *
          Polynomial.X ^ i.val).degree =
        (Polynomial.X ^ h : (RatFunc K)[X]).degree := by
      apply Polynomial.degree_add_eq_left_of_degree_lt
      rw [Polynomial.degree_X_pow]
      exact Polynomial.degree_sum_fin_lt
        (fun i : Fin h => genericHankelCoefficient h moments i)
    _ = h := Polynomial.degree_X_pow h

private theorem rootSupportPolynomial_finiteSupportRoots
    {K : Type*} [Field K]
    (support : Finset K) :
    rootSupportPolynomial (finiteSupportRoots support) =
      ∏ root ∈ support, (Polynomial.X - Polynomial.C root) := by
  classical
  unfold rootSupportPolynomial finiteSupportRoots
  calc
    (∏ index : Fin support.card,
      (Polynomial.X -
        Polynomial.C ((Finset.equivFin support).symm index : K))) =
        ∏ root : support,
          (Polynomial.X - Polynomial.C (root : K)) :=
      Equiv.prod_comp (Finset.equivFin support).symm
        (fun root : support => Polynomial.X - Polynomial.C (root : K))
    _ = ∏ root ∈ support, (Polynomial.X - Polynomial.C root) :=
      (Finset.prod_subtype support (fun _ => Iff.rfl)
        (fun root : K => Polynomial.X - Polynomial.C root)).symm

private theorem exists_injective_roots_of_monic_separable_splits
    {K : Type*} [Field K]
    (polynomial : K[X])
    (hmonic : polynomial.Monic)
    (hseparable : polynomial.Separable)
    (hsplits : polynomial.Splits) :
    ∃ roots : Fin polynomial.natDegree → K,
      Function.Injective roots ∧
      polynomial = rootSupportPolynomial roots := by
  classical
  let support : Finset K := polynomial.roots.toFinset
  have hcard : support.card = polynomial.natDegree := by
    dsimp [support]
    rw [Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots hseparable)]
    exact hsplits.natDegree_eq_card_roots.symm
  let roots : Fin polynomial.natDegree → K :=
    fun index => finiteSupportRoots support ((finCongr hcard.symm) index)
  refine ⟨roots, ?_, ?_⟩
  · intro i j hij
    apply (finCongr hcard.symm).injective
    apply finiteSupportRoots_injective support
    exact hij
  · have hproduct :
        rootSupportPolynomial roots =
          ∏ root ∈ support, (Polynomial.X - Polynomial.C root) := by
      unfold rootSupportPolynomial
      dsimp [roots]
      calc
        (∏ index : Fin polynomial.natDegree,
          (Polynomial.X -
            Polynomial.C
              (finiteSupportRoots support
                ((finCongr hcard.symm) index)))) =
          ∏ index : Fin support.card,
            (Polynomial.X -
              Polynomial.C (finiteSupportRoots support index)) :=
          Equiv.prod_comp (finCongr hcard.symm)
            (fun index : Fin support.card =>
              Polynomial.X - Polynomial.C (finiteSupportRoots support index))
        _ = rootSupportPolynomial (finiteSupportRoots support) := rfl
        _ = ∏ root ∈ support, (Polynomial.X - Polynomial.C root) :=
          rootSupportPolynomial_finiteSupportRoots support
    rw [hproduct]
    calc
      polynomial =
          (polynomial.roots.map
            (fun root : K =>
              Polynomial.X - Polynomial.C root)).prod :=
        hsplits.eq_prod_roots_of_monic hmonic
      _ = ∏ root ∈ support,
          (Polynomial.X - Polynomial.C root) := by
        change
          (polynomial.roots.map
            (fun root : K =>
              Polynomial.X - Polynomial.C root)).prod =
            (polynomial.roots.toFinset.val.map
              (fun root : K =>
                Polynomial.X - Polynomial.C root)).prod
        rw [Multiset.toFinset_val,
          Multiset.dedup_eq_self.mpr
            (Polynomial.nodup_roots hseparable)]

theorem mem_enumeratedRootSupport_iff
    {E : Type*} {h : ℕ}
    (roots : Fin h → E) (value : E) :
    value ∈ enumeratedRootSupport roots ↔
      ∃ index : Fin h, roots index = value := by
  classical
  simp only [enumeratedRootSupport, mem_image, mem_univ, true_and]

private theorem sourceParitySupport_card_le
    {K : Type*} [DecidableEq K] (supports : List (Finset K)) :
    (paritySupport supports).card ≤ (supports.map Finset.card).sum := by
  induction supports with
  | nil => simp only [paritySupport, card_empty, List.map_nil, List.sum_nil, Std.le_refl]
  | cons support remaining ih =>
      change (support ∆ paritySupport remaining).card ≤
        support.card + (remaining.map Finset.card).sum
      calc
        (support ∆ paritySupport remaining).card ≤
            (support ∪ paritySupport remaining).card :=
          Finset.card_le_card
            (Finset.symmDiff_subset_union
              (s := support) (t := paritySupport remaining))
        _ ≤ support.card + (paritySupport remaining).card :=
          Finset.card_union_le support (paritySupport remaining)
        _ ≤ support.card + (remaining.map Finset.card).sum :=
          Nat.add_le_add_left ih support.card

private theorem genericRoot_mem_subtype_of_characteristicTwo_moments
    {E : Type*} [Field E] [CharP E 2] {h : ℕ}
    (globalRoots : Fin h → E)
    (hinjective : Function.Injective globalRoots)
    (subtypes : List (Finset E))
    (momentBudget : ℕ)
    (hbudget : h + (subtypes.map Finset.card).sum ≤ momentBudget)
    (hmoments : ∀ j : ℕ, j < momentBudget →
      rootMoment globalRoots j =
        (subtypes.map fun subtype => supportMoment subtype j).sum)
    (index : Fin h) :
    ∃ subtype ∈ subtypes, globalRoots index ∈ subtype := by
  classical
  apply global_root_mem_subtype_of_moment_refinement
    (enumeratedRootSupport globalRoots) subtypes
  · intro j hj
    rw [supportMoment_enumeratedRootSupport globalRoots hinjective]
    apply hmoments j
    have hcard :
        (enumeratedRootSupport globalRoots).card +
          (paritySupport subtypes).card ≤ momentBudget := by
      rw [enumeratedRootSupport_card globalRoots hinjective]
      exact (Nat.add_le_add_left
        (sourceParitySupport_card_le subtypes) h).trans hbudget
    exact lt_of_lt_of_le hj hcard
  · simp only [enumeratedRootSupport, mem_image, mem_univ, true_and, exists_apply_eq_apply]

end

section

open scoped BigOperators
open Polynomial Finset

variable {K E : Type*} [Field K] [Field E]
variable [Algebra (RatFunc K) E] [Algebra K[X] E]
variable [IsScalarTower K[X] (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E]
variable [Algebra.IsSeparable (RatFunc K) E]

private theorem functionFieldExtendedValuation_ratFunc_eq_place_zpow
    (a : K) (f : RatFunc K) (hf : f ≠ 0) :
    functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap (RatFunc K) E f) =
      functionFieldExtendedValuation (K := K) (E := E) a
          (algebraMap K[X] E (X - C a)) ^
        ((f.num.rootMultiplicity a : ℤ) -
          (f.denom.rootMultiplicity a : ℤ)) := by
  let valuation := functionFieldExtendedValuation (K := K) (E := E) a
  let place := algebraMap K[X] E (X - C a)
  have hplace : place ≠ 0 := by
    apply (map_ne_zero_iff (algebraMap K[X] E)
      (functionFieldPolynomial_algebraMap_injective
        (K := K) (E := E))).mpr
    exact Polynomial.X_sub_C_ne_zero a
  have hplaceval : valuation place ≠ 0 :=
    (Valuation.ne_zero_iff valuation).mpr hplace
  have hrat :
      algebraMap (RatFunc K) E f =
        algebraMap K[X] E f.num /
          algebraMap K[X] E f.denom := by
    calc
      algebraMap (RatFunc K) E f =
          algebraMap (RatFunc K) E
            (algebraMap K[X] (RatFunc K) f.num /
              algebraMap K[X] (RatFunc K) f.denom) :=
        congrArg (algebraMap (RatFunc K) E)
          (RatFunc.num_div_denom f).symm
      _ = algebraMap K[X] E f.num /
          algebraMap K[X] E f.denom := by
        rw [map_div₀,
          ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) E f.num,
          ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) E f.denom]
  calc
    valuation (algebraMap (RatFunc K) E f) =
        valuation
          (algebraMap K[X] E f.num /
            algebraMap K[X] E f.denom) := congrArg valuation hrat
    _ = valuation (algebraMap K[X] E f.num) /
          valuation (algebraMap K[X] E f.denom) :=
      valuation.map_div _ _
    _ = valuation place ^ f.num.rootMultiplicity a /
          valuation place ^ f.denom.rootMultiplicity a := by
      rw [functionFieldExtendedValuation_polynomial_eq_place_pow
        (E := E) a f.num (RatFunc.num_ne_zero hf)]
      rw [functionFieldExtendedValuation_polynomial_eq_place_pow
        (E := E) a f.denom (RatFunc.denom_ne_zero f)]
    _ = valuation place ^
          ((f.num.rootMultiplicity a : ℤ) -
            (f.denom.rootMultiplicity a : ℤ)) :=
      (zpow_natCast_sub_natCast₀ hplaceval
        (f.num.rootMultiplicity a)
        (f.denom.rootMultiplicity a)).symm

private theorem discrete_place_root_term_valuations_ne
    (place root : WithZero (Multiplicative ℤ))
    (hplace : 0 < place) (hplacelt : place < 1)
    (hroot : 1 < root)
    {degree i j : ℕ}
    (hi : i ≤ degree) (hj : j ≤ degree)
    (hsmall : root ^ degree < place⁻¹)
    (firstExponent secondExponent : ℤ)
    (hindex : i ≠ j) :
    place ^ firstExponent * root ^ i ≠
      place ^ secondExponent * root ^ j := by
  have hplacezero : place ≠ 0 := ne_of_gt hplace
  have hrootzero : root ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one hroot)
  have hplacelog : WithZero.log place < 0 := by
    have h := (WithZero.log_lt_log hplacezero
      (one_ne_zero :
        (1 : WithZero (Multiplicative ℤ)) ≠ 0)).mpr hplacelt
    simpa only [gt_iff_lt, WithZero.log_one] using h
  have hrootlog : 0 < WithZero.log root := by
    have h := (WithZero.log_lt_log
      (one_ne_zero :
        (1 : WithZero (Multiplicative ℤ)) ≠ 0)
      hrootzero).mpr hroot
    simpa only [gt_iff_lt, WithZero.log_one] using h
  have hpowerlog :
      (degree : ℤ) * WithZero.log root <
        -WithZero.log place := by
    have h := (WithZero.log_lt_log
      (pow_ne_zero degree hrootzero)
      (inv_ne_zero hplacezero)).mpr hsmall
    simpa only [gt_iff_lt, WithZero.log_pow, Int.nsmul_eq_mul, WithZero.log_inv] using h
  intro hequal
  have hlog := congrArg WithZero.log hequal
  have hfirst : place ^ firstExponent ≠ 0 :=
    zpow_ne_zero firstExponent hplacezero
  have hsecond : place ^ secondExponent ≠ 0 :=
    zpow_ne_zero secondExponent hplacezero
  have hrooti : root ^ i ≠ 0 := pow_ne_zero i hrootzero
  have hrootj : root ^ j ≠ 0 := pow_ne_zero j hrootzero
  rw [WithZero.log_mul hfirst hrooti,
    WithZero.log_mul hsecond hrootj,
    WithZero.log_zpow, WithZero.log_zpow,
    WithZero.log_pow, WithZero.log_pow] at hlog
  simp only [zsmul_eq_mul, nsmul_eq_mul, Int.cast_id] at hlog
  have hdivides :
      -WithZero.log place ∣
        ((i : ℤ) - (j : ℤ)) * WithZero.log root := by
    refine ⟨firstExponent - secondExponent, ?_⟩
    linear_combination hlog
  have hindexBound :
      |(i : ℤ) - (j : ℤ)| ≤ (degree : ℤ) := by
    apply (abs_le).mpr
    constructor <;> omega
  have habs :
      |((i : ℤ) - (j : ℤ)) * WithZero.log root| <
        -WithZero.log place := by
    calc
      |((i : ℤ) - (j : ℤ)) * WithZero.log root| =
          |(i : ℤ) - (j : ℤ)| * |WithZero.log root| := abs_mul _ _
      _ = |(i : ℤ) - (j : ℤ)| * WithZero.log root := by
        rw [abs_of_pos hrootlog]
      _ ≤ (degree : ℤ) * WithZero.log root :=
        mul_le_mul_of_nonneg_right hindexBound (le_of_lt hrootlog)
      _ < -WithZero.log place := hpowerlog
  have hzero :
      ((i : ℤ) - (j : ℤ)) * WithZero.log root = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdivides habs
  have heq : (i : ℤ) = (j : ℤ) := by
    rcases mul_eq_zero.mp hzero with h | h
    · omega
    · exact False.elim ((ne_of_gt hrootlog) h)
  apply hindex
  exact_mod_cast heq

private theorem valuation_finset_sum_ne_zero_of_distinct
    {L Γ₀ ι : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₀]
    (valuation : Valuation L Γ₀)
    (indices : Finset ι)
    (terms : ι → L)
    (hnonempty : indices.Nonempty)
    (hnonzero : ∀ i ∈ indices, terms i ≠ 0)
    (hdistinct :
      ∀ i ∈ indices, ∀ j ∈ indices,
        i ≠ j → valuation (terms i) ≠ valuation (terms j)) :
    ∑ i ∈ indices, terms i ≠ 0 := by
  classical
  obtain ⟨maxIndex, hmaxIndex, hmax⟩ :=
    Finset.exists_max_image indices
      (fun i => valuation (terms i)) hnonempty
  have hstrict : ∀ i ∈ indices \ {maxIndex},
      valuation (terms i) < valuation (terms maxIndex) := by
    intro i hi
    have himem : i ∈ indices := (Finset.mem_sdiff.mp hi).1
    have hine : i ≠ maxIndex := by
      intro hequal
      subst i
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_singleton_self _)
    exact lt_of_le_of_ne (hmax i himem)
      (hdistinct i himem maxIndex hmaxIndex hine)
  have hvaluation := valuation.map_sum_eq_of_lt hmaxIndex hstrict
  intro hsum
  rw [hsum, valuation.map_zero] at hvaluation
  exact ((Valuation.ne_zero_iff valuation).mpr
    (hnonzero maxIndex hmaxIndex)) hvaluation.symm

private theorem functionFieldExtendedValuation_monic_root_separation
    (a : K) (polynomial : (RatFunc K)[X])
    (hmonic : polynomial.Monic)
    (root : E)
    (hroot :
      polynomial.eval₂ (algebraMap (RatFunc K) E) root = 0)
    (hlarge :
      1 < functionFieldExtendedValuation (K := K) (E := E) a root) :
    (functionFieldExtendedValuation (K := K) (E := E) a
      (algebraMap K[X] E (Polynomial.X - Polynomial.C a)))⁻¹ ≤
      (functionFieldExtendedValuation (K := K) (E := E) a root) ^
        polynomial.natDegree := by
  classical
  let valuation := functionFieldExtendedValuation (K := K) (E := E) a
  let place := algebraMap K[X] E (Polynomial.X - Polynomial.C a)
  have hplace : place ≠ 0 := by
    apply (map_ne_zero_iff (algebraMap K[X] E)
      (functionFieldPolynomial_algebraMap_injective
        (K := K) (E := E))).mpr
    exact Polynomial.X_sub_C_ne_zero a
  have hplacePositive : 0 < valuation place :=
    (Valuation.pos_iff valuation).mpr hplace
  have hplaceLess : valuation place < 1 :=
    functionFieldExtendedValuation_place_lt_one
      (K := K) (E := E) a
  have hrootLarge : 1 < valuation root := hlarge
  have hrootNonzero : root ≠ 0 := by
    intro hzero
    rw [hzero, valuation.map_zero] at hrootLarge
    exact (not_lt_of_ge zero_le) hrootLarge
  change (valuation place)⁻¹ ≤ valuation root ^ polynomial.natDegree
  by_contra hnot
  have hsmall :
      valuation root ^ polynomial.natDegree < (valuation place)⁻¹ :=
    lt_of_not_ge hnot
  let terms : ℕ → E := fun index =>
    algebraMap (RatFunc K) E (polynomial.coeff index) * root ^ index
  have hsupport : polynomial.support.Nonempty :=
    Polynomial.nonempty_support_iff.mpr hmonic.ne_zero
  have hterms :
      ∀ index ∈ polynomial.support, terms index ≠ 0 := by
    intro index hindex
    dsimp [terms]
    apply mul_ne_zero
    · exact
        (map_ne_zero_iff (algebraMap (RatFunc K) E)
          (algebraMap (RatFunc K) E).injective).mpr
          (Polynomial.mem_support_iff.mp hindex)
    · exact pow_ne_zero index hrootNonzero
  have hdistinct :
      ∀ i ∈ polynomial.support, ∀ j ∈ polynomial.support,
        i ≠ j → valuation (terms i) ≠ valuation (terms j) := by
    intro i hi j hj hne
    have hicoeff : polynomial.coeff i ≠ 0 :=
      Polynomial.mem_support_iff.mp hi
    have hjcoeff : polynomial.coeff j ≠ 0 :=
      Polynomial.mem_support_iff.mp hj
    have hile : i ≤ polynomial.natDegree :=
      Polynomial.le_natDegree_of_mem_supp i hi
    have hjle : j ≤ polynomial.natDegree :=
      Polynomial.le_natDegree_of_mem_supp j hj
    dsimp [terms]
    rw [valuation.map_mul, valuation.map_mul,
      valuation.map_pow, valuation.map_pow]
    change
      functionFieldExtendedValuation (K := K) (E := E) a
          (algebraMap (RatFunc K) E (polynomial.coeff i)) *
          valuation root ^ i ≠
        functionFieldExtendedValuation (K := K) (E := E) a
          (algebraMap (RatFunc K) E (polynomial.coeff j)) *
          valuation root ^ j
    rw [functionFieldExtendedValuation_ratFunc_eq_place_zpow
      (E := E) a (polynomial.coeff i) hicoeff]
    rw [functionFieldExtendedValuation_ratFunc_eq_place_zpow
      (E := E) a (polynomial.coeff j) hjcoeff]
    exact discrete_place_root_term_valuations_ne
      (valuation place) (valuation root)
      hplacePositive hplaceLess hrootLarge hile hjle hsmall
      (((polynomial.coeff i).num.rootMultiplicity a : ℤ) -
        ((polynomial.coeff i).denom.rootMultiplicity a : ℤ))
      (((polynomial.coeff j).num.rootMultiplicity a : ℤ) -
        ((polynomial.coeff j).denom.rootMultiplicity a : ℤ))
      hne
  have hsum :
      (∑ index ∈ polynomial.support, terms index) ≠ 0 :=
    valuation_finset_sum_ne_zero_of_distinct
      valuation polynomial.support terms hsupport hterms hdistinct
  apply hsum
  have heval := hroot
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def] at heval
  simpa only using heval

private def normalizedAffineRootPolynomial
    {k : Type*} [Field k]
    (polynomial : k[X]) (place bit : k) : k[X] :=
  (polynomial.comp (Polynomial.X + Polynomial.C bit)).scaleRoots place⁻¹

private theorem normalizedAffineRootPolynomial_monic
    {k : Type*} [Field k]
    (polynomial : k[X]) (hmonic : polynomial.Monic)
    (place bit : k) :
    (normalizedAffineRootPolynomial polynomial place bit).Monic := by
  unfold normalizedAffineRootPolynomial
  apply (Polynomial.monic_scaleRoots_iff place⁻¹).mpr
  apply hmonic.comp (Polynomial.monic_X_add_C bit)
  rw [Polynomial.natDegree_X_add_C]
  exact one_ne_zero

private theorem normalizedAffineRootPolynomial_natDegree
    {k : Type*} [Field k]
    (polynomial : k[X]) (place bit : k) :
    (normalizedAffineRootPolynomial polynomial place bit).natDegree =
      polynomial.natDegree := by
  unfold normalizedAffineRootPolynomial
  rw [Polynomial.natDegree_scaleRoots,
    Polynomial.natDegree_comp,
    Polynomial.natDegree_X_add_C, mul_one]

private theorem normalizedAffineRootPolynomial_eval₂_eq_zero
    {k E : Type*} [Field k] [Field E]
    (polynomial : k[X]) (place bit : k)
    (root : E) (map : k →+* E)
    (hroot : polynomial.eval₂ map root = 0) :
    (normalizedAffineRootPolynomial polynomial place bit).eval₂
        map ((root - map bit) / map place) = 0 := by
  have htranslated :
      (polynomial.comp
        (Polynomial.X + Polynomial.C bit)).eval₂
          map (root - map bit) = 0 := by
    rw [Polynomial.eval₂_comp]
    simpa only [eval₂_add, eval₂_X, eval₂_C, sub_add_cancel] using hroot
  have hscaled :=
    Polynomial.scaleRoots_eval₂_eq_zero
      (p := polynomial.comp (Polynomial.X + Polynomial.C bit))
      map (s := place⁻¹) htranslated
  simpa only [div_eq_inv_mul, normalizedAffineRootPolynomial, map_inv₀] using hscaled

private theorem valuation_highPower_separation_of_place_inverse_le
    {E Γ₀ : Type*} [Field E]
    [LinearOrderedCommGroupWithZero Γ₀]
    (valuation : Valuation E Γ₀)
    (place root : E)
    (rank exponent : ℕ)
    (hlarge : 1 < valuation root)
    (hseparation : (valuation place)⁻¹ ≤ valuation root ^ rank) :
    (valuation place ^ exponent)⁻¹ <
      valuation (root ^ (rank * exponent + 1)) := by
  have hpositive : 0 < valuation root :=
    lt_trans zero_lt_one hlarge
  rw [valuation.map_pow]
  calc
    (valuation place ^ exponent)⁻¹ =
        ((valuation place)⁻¹) ^ exponent := by rw [inv_pow]
    _ ≤ (valuation root ^ rank) ^ exponent :=
      pow_le_pow_left' hseparation exponent
    _ < (valuation root ^ rank) ^ exponent * valuation root := by
      have hpow : 0 < (valuation root ^ rank) ^ exponent :=
        pow_pos (pow_pos hpositive _) _
      simpa only [gt_iff_lt, mul_one] using mul_lt_mul_of_pos_left hlarge hpow
    _ = valuation root ^ (rank * exponent + 1) := by
      rw [pow_succ, pow_mul]

end

section

open scoped BigOperators
open Polynomial Finset Matrix

private theorem genericHankelDenominator_map_eq_vandermonde_det_sq
    {K E : Type*} [Field K] [Field E] [Algebra K[X] E]
    {h : ℕ} (moments : ℕ → K[X]) (roots : Fin h → E)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      algebraMap K[X] E (moments j) = rootMoment roots j) :
    algebraMap K[X] E (genericHankelDenominator h moments) =
      (Matrix.vandermonde roots).det ^ 2 := by
  classical
  calc
    algebraMap K[X] E (genericHankelDenominator h moments) =
        ((polynomialHankel moments h).map (algebraMap K[X] E)).det := by
          simpa only [genericHankelDenominator, leadingHankelDet, RingHom.mapMatrix_apply] using
              ((algebraMap K[X] E).map_det (polynomialHankel moments h))
    _ = (powerSumHankel roots).det := by
          congr 1
          ext i j
          exact hmoments (i.val + j.val) (by omega)
    _ = (Matrix.vandermonde roots).det ^ 2 :=
          powerSumHankel_det_eq_vandermonde_det_sq roots

private theorem vandermonde_shifted_det_mul_place_pow
    {E : Type*} [Field E] {h : ℕ}
    (roots : Fin h → E) (bit place : E) (hplace : place ≠ 0) :
    (Matrix.vandermonde
        (fun i : Fin h => (roots i - bit) / place)).det *
        place ^ (∑ i : Fin h, i.val) =
      (Matrix.vandermonde roots).det := by
  classical
  have hmatrix :
      Matrix.vandermonde (fun i : Fin h => (roots i - bit) / place) *
        Matrix.diagonal (fun i : Fin h => place ^ i.val) =
        Matrix.vandermonde (fun i : Fin h => roots i - bit) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.vandermonde_apply,
      Matrix.vandermonde_apply, div_pow]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hplace)
  have hdet := congrArg Matrix.det hmatrix
  rw [Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_vandermonde_sub] at hdet
  simpa only [prod_pow_eq_pow_sum] using hdet

private theorem vandermonde_shifted_det_sq_mul_place_pow
    {E : Type*} [Field E] {h : ℕ}
    (roots : Fin h → E) (bit place : E) (hplace : place ≠ 0) :
    (Matrix.vandermonde
        (fun i : Fin h => (roots i - bit) / place)).det ^ 2 *
        place ^ (h * (h - 1)) =
      (Matrix.vandermonde roots).det ^ 2 := by
  classical
  have hsum : (∑ i : Fin h, i.val) * 2 = h * (h - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) h]
    exact Finset.sum_range_id_mul_two h
  have hdet := congrArg (fun x : E => x ^ 2)
    (vandermonde_shifted_det_mul_place_pow roots bit place hplace)
  rw [mul_pow, ← pow_mul, hsum] at hdet
  exact hdet

theorem functionFieldExtendedValuation_shiftedVandermonde_det_inv_le_place_inv_pow
    {K E : Type*} [Field K] [Field E]
    [Algebra (RatFunc K) E] [Algebra K[X] E]
    [IsScalarTower K[X] (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E]
    (a : K) (moments : ℕ → K[X]) (d : ℕ) {h : ℕ}
    (roots : Fin h → E) (bit : E)
    (hmoments : ∀ j : ℕ, j < 2 * h →
      algebraMap K[X] E (moments j) = rootMoment roots j)
    (hdegrees : ∀ j : ℕ, (moments j).natDegree ≤ d * j)
    (hdenominator : genericHankelDenominator h moments ≠ 0) :
    (functionFieldExtendedValuation (K := K) (E := E) a
      ((Matrix.vandermonde (fun i : Fin h =>
        (roots i - bit) /
          algebraMap K[X] E (X - C a))).det))⁻¹ ≤
      (functionFieldExtendedValuation (K := K) (E := E) a
        (algebraMap K[X] E (X - C a)) ^ (d * h * h))⁻¹ := by
  classical
  let valuation := functionFieldExtendedValuation (K := K) (E := E) a
  let place : E := algebraMap K[X] E (X - C a)
  have hplace : place ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap K[X] E)
      (functionFieldPolynomial_algebraMap_injective
        (K := K) (E := E))).mpr (Polynomial.X_sub_C_ne_zero a)
  have hplacePositive : 0 < valuation place :=
    (Valuation.pos_iff valuation).mpr hplace
  have hplaceLeOne : valuation place ≤ 1 := by
    exact le_of_lt
      (functionFieldExtendedValuation_place_lt_one
        (K := K) (E := E) a)
  let shiftedRoots : Fin h → E :=
    fun i => (roots i - bit) / place
  have hdetIdentity :
      valuation ((Matrix.vandermonde shiftedRoots).det) ^ 2 *
          valuation place ^ (h * (h - 1)) =
        valuation (algebraMap K[X] E
          (genericHankelDenominator h moments)) := by
    calc
      valuation ((Matrix.vandermonde shiftedRoots).det) ^ 2 *
          valuation place ^ (h * (h - 1)) =
        valuation
          ((Matrix.vandermonde shiftedRoots).det ^ 2 *
            place ^ (h * (h - 1))) := by
              rw [valuation.map_mul, valuation.map_pow,
                valuation.map_pow]
      _ = valuation ((Matrix.vandermonde roots).det ^ 2) := by
            congr 1
            exact vandermonde_shifted_det_sq_mul_place_pow
              roots bit place hplace
      _ = valuation (algebraMap K[X] E
            (genericHankelDenominator h moments)) := by
            congr 1
            exact
              (genericHankelDenominator_map_eq_vandermonde_det_sq
                moments roots hmoments).symm
  have hdenominatorLower :
      valuation place ^ (d * h * (h - 1)) ≤
        valuation (algebraMap K[X] E
          (genericHankelDenominator h moments)) :=
    functionFieldExtendedValuation_genericHankelDenominator_place_pow_le
      (E := E) a moments d h hdegrees hdenominator
  have hdenominatorUpper :
      valuation (algebraMap K[X] E
        (genericHankelDenominator h moments)) ≤
        valuation ((Matrix.vandermonde shiftedRoots).det) ^ 2 := by
    calc
      valuation (algebraMap K[X] E
          (genericHankelDenominator h moments)) =
        valuation ((Matrix.vandermonde shiftedRoots).det) ^ 2 *
          valuation place ^ (h * (h - 1)) := hdetIdentity.symm
      _ ≤ valuation ((Matrix.vandermonde shiftedRoots).det) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left
          (pow_le_one₀ zero_le hplaceLeOne) zero_le
      _ = valuation ((Matrix.vandermonde shiftedRoots).det) ^ 2 :=
        mul_one _
  have hexponents : d * h * (h - 1) ≤ 2 * (d * h * h) := by
    calc
      d * h * (h - 1) ≤ d * h * h :=
        Nat.mul_le_mul_left (d * h) (Nat.sub_le h 1)
      _ ≤ 2 * (d * h * h) := by omega
  have hsquares :
      (valuation place ^ (d * h * h)) ^ 2 ≤
        valuation ((Matrix.vandermonde shiftedRoots).det) ^ 2 := by
    calc
      (valuation place ^ (d * h * h)) ^ 2 =
          valuation place ^ (2 * (d * h * h)) := by
            rw [← pow_mul]
            simp only [Nat.mul_comm]
      _ ≤ valuation place ^ (d * h * (h - 1)) :=
        pow_le_pow_of_le_one zero_le hplaceLeOne hexponents
      _ ≤ valuation (algebraMap K[X] E
            (genericHankelDenominator h moments)) := hdenominatorLower
      _ ≤ valuation ((Matrix.vandermonde shiftedRoots).det) ^ 2 :=
        hdenominatorUpper
  have hdetLower :
      valuation place ^ (d * h * h) ≤
        valuation ((Matrix.vandermonde shiftedRoots).det) :=
    (sq_le_sq₀ zero_le zero_le).mp hsquares
  change (valuation ((Matrix.vandermonde shiftedRoots).det))⁻¹ ≤
    (valuation place ^ (d * h * h))⁻¹
  exact inv_anti₀ (pow_pos hplacePositive _) hdetLower

end

section

variable {E Γ₀ : Type*} [Field E] [LinearOrderedCommMonoidWithZero Γ₀]

/-- GapCVP reduction support. -/
def bitInField (b : Bool) : E := if b then 1 else 0

private theorem valuation_bits_unique (v : Valuation E Γ₀) (a : E)
    {b₁ b₂ : Bool}
    (h₁ : v (a - bitInField (E := E) b₁) < 1)
    (h₂ : v (a - bitInField (E := E) b₂) < 1) : b₁ = b₂ := by
  cases b₁ <;> cases b₂
  · rfl
  · simp only [bitInField, Bool.false_eq_true, ↓reduceIte,
      sub_zero] at h₁ h₂
    have hneg : v (-(a - 1)) < 1 := by
      rw [v.map_neg]
      exact h₂
    have h : v (a - (a - 1)) < 1 := by
      simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, add_neg_cancel_comm_assoc, map_one,
          lt_self_iff_false] using
          v.map_add_lt h₁ hneg
    have hunit : a - (a - 1) = 1 := by ring
    rw [hunit, v.map_one] at h
    exact False.elim ((lt_irrefl _) h)
  · simp only [bitInField, Bool.false_eq_true, ↓reduceIte,
      sub_zero] at h₁ h₂
    have hneg : v (-(a - 1)) < 1 := by
      rw [v.map_neg]
      exact h₁
    have h : v (a - (a - 1)) < 1 := by
      simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, add_neg_cancel_comm_assoc, map_one,
          lt_self_iff_false] using
          v.map_add_lt h₂ hneg
    have hunit : a - (a - 1) = 1 := by ring
    rw [hunit, v.map_one] at h
    exact False.elim ((lt_irrefl _) h)
  · rfl

theorem satisfiable_of_common_valuation_root
    (formula : Formula)
    (valuation : Fin formula.variableCount → Valuation E Γ₀)
    (commonRoot : E)
    (localAssignment :
      Fin formula.clauses.length → Fin formula.variableCount → Bool)
    (local_satisfies : ∀ C : Fin formula.clauses.length,
      (formula.clauses.get C).Satisfied (localAssignment C))
    (local_close : ∀ (C : Fin formula.clauses.length)
      (literal : Literal formula.variableCount),
      literal ∈ (formula.clauses.get C).literals →
      valuation literal.variableIndex
        (commonRoot -
          bitInField (E := E)
            (localAssignment C literal.variableIndex)) < 1) :
    formula.Satisfiable := by
  simp only [GapCVP.Core.Formula.Satisfiable, decide_eq_true_eq] at *
  classical
  let assignment : Fin formula.variableCount → Bool := fun i =>
    if h : ∃ (C : Fin formula.clauses.length)
        (literal : Literal formula.variableCount),
        literal ∈ (formula.clauses.get C).literals ∧
          literal.variableIndex = i then
      localAssignment (Classical.choose h) i
    else false
  refine ⟨assignment, ?_⟩
  simp only [GapCVP.Core.Formula.Satisfied, decide_eq_true_eq]
  intro C
  have clauseSatisfied := local_satisfies C
  simp only [GapCVP.Core.Clause.Satisfied, decide_eq_true_eq] at clauseSatisfied ⊢
  obtain ⟨literal, hliteral, hvalue⟩ := clauseSatisfied
  refine ⟨literal, hliteral, ?_⟩
  have hoccurs : ∃ (D : Fin formula.clauses.length)
      (other : Literal formula.variableCount),
      other ∈ (formula.clauses.get D).literals ∧
        other.variableIndex = literal.variableIndex :=
    ⟨C, literal, hliteral, rfl⟩
  dsimp [assignment]
  split
  next h =>
    obtain ⟨other, hother, hindex⟩ := Classical.choose_spec h
    have hsame :
        localAssignment C literal.variableIndex =
          localAssignment (Classical.choose h) literal.variableIndex :=
      valuation_bits_unique (valuation literal.variableIndex) commonRoot
        (local_close C literal hliteral)
        (by
          have hc := local_close (Classical.choose h) other hother
          simpa only [gt_iff_lt, hindex] using hc)
    exact hsame.symm.trans hvalue
  next h =>
    exact False.elim (h hoccurs)

end

section

open scoped BigOperators
open Polynomial Finset Matrix

private theorem functionFieldExtendedValuation_genericSupportRoot_le_place_inv_pow
    {k E : Type*} [Field k] [Field E]
    [Algebra (RatFunc k) E] [Algebra k[X] E]
    [IsScalarTower k[X] (RatFunc k) E]
    [FiniteDimensional (RatFunc k) E]
    [Algebra.IsSeparable (RatFunc k) E]
    (moments : ℕ → k[X]) (d h : ℕ)
    (hmoments : ∀ j : ℕ, (moments j).natDegree ≤ d * j)
    (hdenominator : genericHankelDenominator h moments ≠ 0)
    (roots : Fin h → E)
    (hroots :
      (genericMomentSupportPolynomial h moments).map
        (algebraMap (RatFunc k) E) = rootSupportPolynomial roots)
    (place : k) (index : Fin h) :
    functionFieldExtendedValuation (K := k) (E := E) place (roots index) ≤
      (functionFieldExtendedValuation (K := k) (E := E) place
         (algebraMap k[X] E (Polynomial.X - Polynomial.C place)) ^
       (d * h * (h - 1)))⁻¹ := by
  classical
  let v := functionFieldExtendedValuation (K := k) (E := E) place
  let q := v (algebraMap k[X] E (Polynomial.X - Polynomial.C place))
  have hq : 0 < q := by
    apply (Valuation.pos_iff v).mpr
    apply (map_ne_zero_iff (algebraMap k[X] E)
      (functionFieldPolynomial_algebraMap_injective
        (K := k) (E := E))).mpr
    exact Polynomial.X_sub_C_ne_zero place
  have hqone : q ≤ 1 :=
    le_of_lt
      (functionFieldExtendedValuation_place_lt_one
        (K := k) (E := E) place)
  have hbound : 1 ≤ (q ^ (d * h * (h - 1)))⁻¹ :=
    (one_le_inv₀ (pow_pos hq _)).mpr
      (pow_le_one₀ zero_le hqone)
  apply valuation_root_le_of_monic_coefficient_bound v
    (fun i : Fin h =>
      algebraMap (RatFunc k) E (genericHankelCoefficient h moments i))
    (roots index) (q ^ (d * h * (h - 1)))⁻¹ hbound
  · intro i
    exact
      functionFieldExtendedValuation_genericHankelCoefficient_le_place_inv_pow
        (E := E) place moments d h hmoments hdenominator i
  · have hroot :
        ((genericMomentSupportPolynomial h moments).map
          (algebraMap (RatFunc k) E)).eval (roots index) = 0 := by
      rw [hroots]
      exact rootSupportPolynomial_eval_root roots index
    simpa only [genericMomentSupportPolynomial, Polynomial.map_add, Polynomial.map_pow, map_X,
        eval_add, eval_pow,
        eval_X, eval_map_algebraMap, map_sum, map_mul, aeval_C, map_pow, aeval_X] using hroot

theorem functionFieldExtendedValuation_shiftedGenericRoot_le_place_inv_pow
    {k E : Type*} [Field k] [Field E]
    [Algebra k E] [Algebra (RatFunc k) E] [Algebra k[X] E]
    [IsScalarTower k k[X] E]
    [IsScalarTower k[X] (RatFunc k) E]
    [FiniteDimensional (RatFunc k) E]
    [Algebra.IsSeparable (RatFunc k) E]
    (moments : ℕ → k[X]) (d h : ℕ)
    (hmoments : ∀ j : ℕ, (moments j).natDegree ≤ d * j)
    (hdenominator : genericHankelDenominator h moments ≠ 0)
    (roots : Fin h → E)
    (hroots :
      (genericMomentSupportPolynomial h moments).map
        (algebraMap (RatFunc k) E) = rootSupportPolynomial roots)
    (place bit : k) (index : Fin h) :
    functionFieldExtendedValuation (K := k) (E := E) place
      ((roots index - algebraMap k E bit) /
        algebraMap k[X] E (Polynomial.X - Polynomial.C place)) ≤
      (functionFieldExtendedValuation (K := k) (E := E) place
        (algebraMap k[X] E (Polynomial.X - Polynomial.C place)) ^
        (d * h * (h - 1) + 1))⁻¹ := by
  classical
  let v := functionFieldExtendedValuation (K := k) (E := E) place
  let q := v (algebraMap k[X] E (Polynomial.X - Polynomial.C place))
  let D := d * h * (h - 1)
  have hq : 0 < q := by
    apply (Valuation.pos_iff v).mpr
    apply (map_ne_zero_iff (algebraMap k[X] E)
      (functionFieldPolynomial_algebraMap_injective
        (K := k) (E := E))).mpr
    exact Polynomial.X_sub_C_ne_zero place
  have hqone : q ≤ 1 :=
    le_of_lt
      (functionFieldExtendedValuation_place_lt_one
        (K := k) (E := E) place)
  have hbound : 1 ≤ (q ^ D)⁻¹ :=
    (one_le_inv₀ (pow_pos hq _)).mpr
      (pow_le_one₀ zero_le hqone)
  have halpha : v (roots index) ≤ (q ^ D)⁻¹ :=
    functionFieldExtendedValuation_genericSupportRoot_le_place_inv_pow
      moments d h hmoments hdenominator roots hroots place index
  have hbitEq :
      algebraMap k E bit = algebraMap k[X] E (Polynomial.C bit) := by
    change algebraMap k E bit =
      algebraMap k[X] E (algebraMap k k[X] bit)
    exact IsScalarTower.algebraMap_apply k k[X] E bit
  have hbit : v (algebraMap k E bit) ≤ 1 := by
    rw [hbitEq]
    exact functionFieldExtendedValuation_polynomial_le_one
      place (Polynomial.C bit)
  have hsub : v (roots index - algebraMap k E bit) ≤ (q ^ D)⁻¹ :=
    (v.map_sub _ _).trans (max_le halpha (hbit.trans hbound))
  calc
    v ((roots index - algebraMap k E bit) /
        algebraMap k[X] E (Polynomial.X - Polynomial.C place)) =
        v (roots index - algebraMap k E bit) / q := v.map_div _ _
    _ = v (roots index - algebraMap k E bit) * q⁻¹ :=
      div_eq_mul_inv _ _
    _ ≤ (q ^ D)⁻¹ * q⁻¹ :=
      mul_le_mul_of_nonneg_right hsub zero_le
    _ = (q ^ (D + 1))⁻¹ := by
      rw [pow_succ, mul_inv]

theorem valuation_inverseTransposeVandermonde_le_place_inv_pow
    {E Γ₀ : Type*} [Field E] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation E Γ₀) {h : ℕ} (roots : Fin h → E)
    (p : Γ₀) (hp : 0 < p) (hpone : p ≤ 1)
    (A B : ℕ)
    (hroots : ∀ i, v (roots i) ≤ (p ^ A)⁻¹)
    (hdet : (v (Matrix.vandermonde roots).det)⁻¹ ≤
      (p ^ B)⁻¹)
    (i j : Fin h) :
    v (inverseTransposeVandermonde roots i j) ≤
      (p ^ (B + A * h * h))⁻¹ := by
  classical
  have hbase : 1 ≤ (p ^ A)⁻¹ :=
    (one_le_inv₀ (pow_pos hp _)).mpr
      (pow_le_one₀ zero_le hpone)
  have hmatrixBound : 1 ≤ (p ^ (A * h))⁻¹ :=
    (one_le_inv₀ (pow_pos hp _)).mpr
      (pow_le_one₀ zero_le hpone)
  have hentries :
      ∀ r c : Fin h,
        v (roots c ^ r.val) ≤ (p ^ (A * h))⁻¹ := by
    intro r c
    calc
      v (roots c ^ r.val) = v (roots c) ^ r.val :=
        v.map_pow (roots c) r.val
      _ ≤ ((p ^ A)⁻¹) ^ r.val :=
        pow_le_pow_left' (hroots c) r.val
      _ ≤ ((p ^ A)⁻¹) ^ h :=
        pow_le_pow_right' hbase (Nat.le_of_lt r.isLt)
      _ = (p ^ (A * h))⁻¹ := by
        rw [inv_pow, ← pow_mul]
  calc
    v (inverseTransposeVandermonde roots i j) ≤
        (v (Matrix.vandermonde roots).det)⁻¹ *
          ((p ^ (A * h))⁻¹) ^ h :=
      valuation_inverseTransposeVandermonde_le_det_inv_mul_pow
        v roots ((p ^ (A * h))⁻¹)
        hmatrixBound hentries i j
    _ ≤ (p ^ B)⁻¹ * ((p ^ (A * h))⁻¹) ^ h :=
      mul_le_mul_of_nonneg_right hdet zero_le
    _ = (p ^ (B + A * h * h))⁻¹ := by
      rw [inv_pow, ← mul_inv, ← pow_mul, ← pow_add]

end

section

open scoped BigOperators
open Matrix

/-- GapCVP reduction support. -/
abbrev BinaryAffineSystem.effectiveGaussianSystem (H : BinaryAffineSystem) :
    EffectiveBinaryGaussian.System H.rowCount H.dimension where
  check := H.check
  rhs := H.rightHandSide

/-- GapCVP reduction support. -/
abbrev BinaryAffineSystem.effectiveGaussianState (H : BinaryAffineSystem) :
    EffectiveBinaryGaussian.State H.rowCount H.dimension :=
  EffectiveBinaryGaussian.eliminate H.effectiveGaussianSystem

theorem BinaryAffineSystem.effectiveGaussian_solves_iff
    (H : BinaryAffineSystem) (z : Fin H.dimension → ℤ) :
    H.effectiveGaussianState.system.Satisfies (binaryResidue z) ↔
      H.Solves z := by
  simpa only [EffectiveBinaryGaussian.System.Satisfies,
      effectiveGaussianState, effectiveGaussianSystem, Solves] using
      EffectiveBinaryGaussian.eliminate_satisfies_iff H.effectiveGaussianSystem (binaryResidue z)

/-- GapCVP reduction support. -/
def BinaryAffineSystem.effectivePivotRowOption
    (H : BinaryAffineSystem) (column : Fin H.dimension) :
    Option (Fin H.rowCount) :=
  (H.effectiveGaussianState.pivots.find?
    (fun pivot => decide (pivot.2 = column))).map Prod.fst

/-- GapCVP reduction support. -/
def BinaryAffineSystem.effectiveAffineBits
    (H : BinaryAffineSystem) : Fin H.dimension → ZMod 2 :=
  fun column =>
    match H.effectivePivotRowOption column with
    | some row => H.effectiveGaussianState.system.rhs row
    | none => 0

/-- GapCVP reduction support. -/
def BinaryAffineSystem.effectiveAffineRepresentative
    (H : BinaryAffineSystem) : Fin H.dimension → ℤ :=
  fun column => ((H.effectiveAffineBits column).val : ℤ)

@[simp] theorem BinaryAffineSystem.effectiveAffineRepresentative_residue
    (H : BinaryAffineSystem) :
    binaryResidue H.effectiveAffineRepresentative =
      H.effectiveAffineBits := by
  funext column
  change (((H.effectiveAffineBits column).val : ℤ) : ZMod 2) =
    H.effectiveAffineBits column
  exact_mod_cast ZMod.natCast_zmod_val (H.effectiveAffineBits column)

theorem effectiveBinary_eq_zero_or_one (bit : ZMod 2) :
    bit = 0 ∨ bit = 1 := by
  by_cases h : bit = 1
  · exact Or.inr h
  · exact Or.inl
      (EffectiveBinaryGaussian.binary_eq_zero_of_ne_one bit h)

theorem BinaryAffineSystem.effectiveAffineRepresentative_eq_zero_or_one
    (H : BinaryAffineSystem) (column : Fin H.dimension) :
    H.effectiveAffineRepresentative column = 0 ∨
      H.effectiveAffineRepresentative column = 1 := by
  rcases effectiveBinary_eq_zero_or_one
    (H.effectiveAffineBits column) with hzero | hone
  · left
    simp only [effectiveAffineRepresentative, hzero, ZMod.val_zero, CharP.cast_eq_zero]
  · right
    change ((H.effectiveAffineBits column).val : ℤ) = 1
    simp only [hone, ZMod.val_one, Nat.cast_one]

/-- GapCVP reduction support. -/
def BinaryAffineSystem.effectiveSquareBasisMatrix
    (H : BinaryAffineSystem) :
    Matrix (Fin H.dimension) (Fin H.dimension) ℤ :=
  fun row column =>
    match H.effectivePivotRowOption row, H.effectivePivotRowOption column with
    | some pivotRow, none =>
        ((H.effectiveGaussianState.system.check pivotRow column).val : ℤ)
    | some _, some _ => if row = column then 2 else 0
    | none, none => if row = column then 1 else 0
    | none, some _ => 0

theorem BinaryAffineSystem.effectiveSquareBasisMatrix_mulVec_free
    (H : BinaryAffineSystem) (coefficients : Fin H.dimension → ℤ)
    (row : Fin H.dimension)
    (hrow : H.effectivePivotRowOption row = none) :
    H.effectiveSquareBasisMatrix.mulVec coefficients row =
      coefficients row := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single row]
  · simp only [effectiveSquareBasisMatrix, hrow, ↓reduceIte, one_mul]
  · intro column _ hne
    cases hcolumn : H.effectivePivotRowOption column with
    | none =>
        simp only [effectiveSquareBasisMatrix, hrow, hcolumn, Ne.symm hne, ↓reduceIte, zero_mul]
    | some pivot =>
        simp only [effectiveSquareBasisMatrix, hrow, hcolumn, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, mul_eq_zero, IsEmpty.forall_iff]

theorem BinaryAffineSystem.effectiveSquareBasisMatrix_mulVec_pivot
    (H : BinaryAffineSystem) (coefficients : Fin H.dimension → ℤ)
    (row : Fin H.dimension) (pivot : Fin H.rowCount)
    (hrow : H.effectivePivotRowOption row = some pivot)
    (hfree : ∀ column : Fin H.dimension,
      H.effectivePivotRowOption column = none → coefficients column = 0) :
    H.effectiveSquareBasisMatrix.mulVec coefficients row =
      2 * coefficients row := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single row]
  · simp only [effectiveSquareBasisMatrix, hrow, ↓reduceIte]
  · intro column _ hne
    cases hcolumn : H.effectivePivotRowOption column with
    | none =>
        simp only [hfree column hcolumn, mul_zero]
    | some other =>
        simp only [effectiveSquareBasisMatrix, hrow, hcolumn, Ne.symm hne, ↓reduceIte, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, mul_eq_zero, IsEmpty.forall_iff]

theorem BinaryAffineSystem.effectiveSquareBasisMatrix_det_ne_zero
    (H : BinaryAffineSystem) :
    H.effectiveSquareBasisMatrix.det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨coefficients, hnonzero, hzero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfree : ∀ column : Fin H.dimension,
      H.effectivePivotRowOption column = none →
        coefficients column = 0 := by
    intro column hcolumn
    have hcoordinate := congrFun hzero column
    rw [H.effectiveSquareBasisMatrix_mulVec_free
      coefficients column hcolumn] at hcoordinate
    simpa only [Pi.zero_apply] using hcoordinate
  apply hnonzero
  funext column
  cases hpivot : H.effectivePivotRowOption column with
  | none =>
      exact hfree column hpivot
  | some pivot =>
      have hcoordinate := congrFun hzero column
      rw [H.effectiveSquareBasisMatrix_mulVec_pivot
        coefficients column pivot hpivot hfree] at hcoordinate
      have hmul : 2 * coefficients column = 0 := by
        simpa only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, Pi.zero_apply] using hcoordinate
      exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)

/-- GapCVP reduction support. -/
def effectiveConstructionAInstance
    (H : BinaryAffineSystem) (hdimension : 0 < H.dimension)
    (radius : ℚ) (hradius : 0 < radius) : GapCVPInstance where
  dimension := H.dimension
  dimension_pos := hdimension
  basis := H.effectiveSquareBasisMatrix
  basis_nonsingular := H.effectiveSquareBasisMatrix_det_ne_zero
  target := fun i => (H.effectiveAffineRepresentative i : ℚ)
  radius := radius
  radius_pos := hradius

namespace EffectiveBinaryGaussian

@[simp] private theorem clearTarget_pivots
    {m n : ℕ} (pivot : Fin m) (column : Fin n)
    (state : State m n) (target : Fin m) :
    (clearTarget pivot column state target).pivots = state.pivots := by
  unfold clearTarget
  split
  · rfl
  · split
    · rfl
    · rfl

@[simp] theorem clearTargets_pivots
    {m n : ℕ} (pivot : Fin m) (column : Fin n)
    (targets : List (Fin m)) (state : State m n) :
    (clearTargets pivot column targets state).pivots =
      state.pivots := by
  induction targets generalizing state with
  | nil => rfl
  | cons target rest ih =>
      change
        (clearTargets pivot column rest
          (clearTarget pivot column state target)).pivots = state.pivots
      rw [ih, clearTarget_pivots]

/-- GapCVP reduction support. -/
noncomputable def PrefixNormal {m n : ℕ}
    (scanned : List (Fin n)) (state : State m n) : Bool :=
  @decide
    (state.nextPivot ≤ m ∧
      (∀ pair ∈ state.pivots,
        pair.1.val < state.nextPivot) ∧
      (∀ row : Fin m,
        row.val < state.nextPivot →
          ∃ column : Fin n, (row, column) ∈ state.pivots) ∧
      (∀ pair ∈ state.pivots,
        ∀ row : Fin m,
          state.system.check row pair.2 =
            if row = pair.1 then 1 else 0) ∧
      (∀ column ∈ scanned,
        ∀ row : Fin m, state.nextPivot ≤ row.val →
          state.system.check row column = 0))
    (Classical.propDecidable _)

theorem PrefixNormal.nextPivot_le {m n : ℕ}
    {scanned : List (Fin n)} {state : State m n}
    (normal : PrefixNormal scanned state) :
    state.nextPivot ≤ m := by
  simp only [PrefixNormal, decide_eq_true_eq] at normal
  exact normal.1

theorem PrefixNormal.pivot_below {m n : ℕ}
    {scanned : List (Fin n)} {state : State m n}
    (normal : PrefixNormal scanned state)
    (pair : Fin m × Fin n) (hpair : pair ∈ state.pivots) :
    pair.1.val < state.nextPivot := by
  simp only [PrefixNormal, decide_eq_true_eq] at normal
  exact normal.2.1 pair hpair

theorem PrefixNormal.pivot_complete {m n : ℕ}
    {scanned : List (Fin n)} {state : State m n}
    (normal : PrefixNormal scanned state)
    (row : Fin m) (hrow : row.val < state.nextPivot) :
    ∃ column : Fin n, (row, column) ∈ state.pivots := by
  simp only [PrefixNormal, decide_eq_true_eq] at normal
  exact normal.2.2.1 row hrow

theorem PrefixNormal.pivot_unit {m n : ℕ}
    {scanned : List (Fin n)} {state : State m n}
    (normal : PrefixNormal scanned state)
    (pair : Fin m × Fin n) (hpair : pair ∈ state.pivots)
    (row : Fin m) :
    state.system.check row pair.2 =
      if row = pair.1 then 1 else 0 := by
  simp only [PrefixNormal, decide_eq_true_eq] at normal
  exact normal.2.2.2.1 pair hpair row

theorem PrefixNormal.scanned_lower_zero {m n : ℕ}
    {scanned : List (Fin n)} {state : State m n}
    (normal : PrefixNormal scanned state)
    (column : Fin n) (hcolumn : column ∈ scanned)
    (row : Fin m) (hrow : state.nextPivot ≤ row.val) :
    state.system.check row column = 0 := by
  simp only [PrefixNormal, decide_eq_true_eq] at normal
  exact normal.2.2.2.2 column hcolumn row hrow

theorem initialState_prefixNormal
    {m n : ℕ} (system : System m n) :
    PrefixNormal [] (initialState system) := by
  simp only [PrefixNormal, decide_eq_true_eq]
  refine ⟨Nat.zero_le m, ?_, ?_, ?_, ?_⟩
  · intro pair hpair
    simp only [initialState, List.not_mem_nil] at hpair
  · intro row hrow
    simp only [initialState, not_lt_zero] at hrow
  · intro pair hpair
    simp only [initialState, List.not_mem_nil] at hpair
  · intro column hcolumn
    simp only [List.not_mem_nil] at hcolumn

end EffectiveBinaryGaussian

end

end Core

namespace Factor400BinarySourceTM

open GapCVP.OutputBoundedDependentRecordFold

theorem boundedFoldStates_of_nonexpansive
    {worker : List Bool → List Bool}
    (hworker : ∀ state : List Bool,
      (worker state).length ≤ state.length) :
    PolynomiallyBoundedFoldStates worker Polynomial.X := by
  simp only [GapCVP.OutputBoundedDependentRecordFold.PolynomiallyBoundedFoldStates,
      decide_eq_true_eq] at *
  intro input count seed hparse stage _
  have hseed : seed.length ≤ input.length := by
    have hword := parseUnaryBoundedFold_eq_word input count seed hparse
    rw [hword, unaryBoundedFoldWord]
    simp only [List.length_append, List.length_replicate,
      List.length_cons]
    omega
  have hiterate : ∀ index : ℕ,
      ((worker^[index]) seed).length ≤ seed.length := by
    intro index
    induction index with
    | zero => simp only [Function.iterate_zero, id_eq, Std.le_refl]
    | succ index ih =>
      rw [Function.iterate_succ_apply']
      exact (hworker _).trans ih
  simpa only [Polynomial.eval_X, ge_iff_le] using (hiterate stage).trans hseed

private noncomputable def boundedWorkerComputable
    {worker : List Bool → List Bool}
    (computer : Turing.TM2ComputableInPolyTime
      GapCVP.bitEncoding GapCVP.bitEncoding worker)
    (bound : Polynomial ℕ)
    (hstates : PolynomiallyBoundedFoldStates worker bound) :
    Turing.TM2ComputableInPolyTime
      GapCVP.bitEncoding GapCVP.bitEncoding
      (boundedRecordFoldOutput worker) :=
  boundedDependentRecordFoldComputable computer bound hstates

/-- GapCVP reduction support. -/
noncomputable def nonexpansiveBoundedWorkerComputable
    {worker : List Bool → List Bool}
    (computer : Turing.TM2ComputableInPolyTime
      GapCVP.bitEncoding GapCVP.bitEncoding worker)
    (hworker : ∀ state : List Bool,
      (worker state).length ≤ state.length) :
    Turing.TM2ComputableInPolyTime
      GapCVP.bitEncoding GapCVP.bitEncoding
      (boundedRecordFoldOutput worker) :=
  boundedWorkerComputable computer Polynomial.X
    (boundedFoldStates_of_nonexpansive hworker)

end Factor400BinarySourceTM

namespace Factor400BinaryPreservingXorWorker

open Turing

private def binaryGaussianXorPreservingWord : List Bool → List Bool
  | first :: second :: remaining =>
      Bool.xor first second :: remaining
  | _ => []

private theorem binaryGaussianXorPreservingWord_nonexpansive
    (input : List Bool) :
    (binaryGaussianXorPreservingWord input).length ≤ input.length := by
  cases input with
  | nil => simp only [binaryGaussianXorPreservingWord, List.length_nil, Std.le_refl]
  | cons first remaining =>
      cases remaining <;>
        simp [binaryGaussianXorPreservingWord]

private def preservingXorPeek (stack : Fin 3)
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .peek stack (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def preservingXorGoto (phase : Fin 4) :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .goto (fun _ => phase)

private def preservingXorFirstStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  preservingXorPeek 0
    (.pop 0 (fun _ symbol => symbol) (preservingXorGoto 1))
    (preservingXorGoto 2)

private def preservingXorSecondStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  .pop 0
    (fun first second =>
      second.map (fun bit => Bool.xor (first.getD false) bit))
    (.branch (fun result => result.isSome)
      (.push 1 (fun result => result.getD false)
        (.load (fun _ => none) (preservingXorGoto 2)))
      (.load (fun _ => none) (preservingXorGoto 2)))

private def preservingXorScanStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  preservingXorPeek 0
    (.pop 0 (fun _ bit => bit)
      (.push 1 (fun bit => bit.getD false)
        (.load (fun _ => none) (preservingXorGoto 2))))
    (.load (fun _ => none) (preservingXorGoto 3))

private def preservingXorRestoreStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 3 => Bool) (Fin 4) (Option Bool) :=
  preservingXorPeek 1
    (.pop 1 (fun _ bit => bit)
      (.push 2 (fun bit => bit.getD false)
        (.load (fun _ => none) (preservingXorGoto 3))))
    (.load (fun _ => none) .halt)

private abbrev preservingXorMachine : Turing.FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Fin 4
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 4) then
      preservingXorFirstStatement
    else if phase = (1 : Fin 4) then
      preservingXorSecondStatement
    else if phase = (2 : Fin 4) then
      preservingXorScanStatement
    else
      preservingXorRestoreStatement

private def preservingXorConfiguration
    (phase : Fin 4) (state : Option Bool)
    (input archive output : List Bool) : preservingXorMachine.Cfg where
  l := some phase
  var := state
  stk := ![input, archive, output]

private theorem preservingXorMachine_init (input : List Bool) :
    Turing.initList preservingXorMachine input =
      preservingXorConfiguration 0 none input [] [] := by
  simp only [preservingXorMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq, dite_eq_ite,
      preservingXorConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `preservingXorStepTac` machine-step simplifier. -/
macro "preservingXorStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [preservingXorMachine, preservingXorConfiguration,
          preservingXorPeek, preservingXorGoto,
          preservingXorFirstStatement, preservingXorSecondStatement,
          preservingXorScanStatement, preservingXorRestoreStatement,
          Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

private theorem preservingXor_first_step
    (first : Bool) (remaining archive output : List Bool) :
    preservingXorMachine.step
      (preservingXorConfiguration 0 none
        (first :: remaining) archive output) =
      some (preservingXorConfiguration 1
        (some first) remaining archive output) := by
  cases first <;> preservingXorStepTac

private theorem preservingXor_first_missing
    (archive output : List Bool) :
    preservingXorMachine.step
      (preservingXorConfiguration 0 none [] archive output) =
      some (preservingXorConfiguration 2 none [] archive output) := by
  preservingXorStepTac

private theorem preservingXor_second_step
    (first second : Bool) (remaining archive output : List Bool) :
    preservingXorMachine.step
      (preservingXorConfiguration 1 (some first)
        (second :: remaining) archive output) =
      some (preservingXorConfiguration 2 none
        remaining (Bool.xor first second :: archive) output) := by
  cases first <;> cases second <;> preservingXorStepTac

private theorem preservingXor_second_missing
    (first : Bool) (archive output : List Bool) :
    preservingXorMachine.step
      (preservingXorConfiguration 1 (some first) [] archive output) =
      some (preservingXorConfiguration 2 none [] archive output) := by
  cases first <;> preservingXorStepTac

private theorem preservingXor_scan_step
    (bit : Bool) (remaining archive output : List Bool) :
    preservingXorMachine.step
      (preservingXorConfiguration 2 none
        (bit :: remaining) archive output) =
      some (preservingXorConfiguration 2 none
        remaining (bit :: archive) output) := by
  cases bit <;> preservingXorStepTac

private theorem preservingXor_scan_finish
    (archive output : List Bool) :
    preservingXorMachine.step
      (preservingXorConfiguration 2 none [] archive output) =
      some (preservingXorConfiguration 3 none [] archive output) := by
  preservingXorStepTac

private theorem preservingXor_restore_step
    (bit : Bool) (archive output : List Bool) :
    preservingXorMachine.step
      (preservingXorConfiguration 3 none []
        (bit :: archive) output) =
      some (preservingXorConfiguration 3 none []
        archive (bit :: output)) := by
  cases bit <;> preservingXorStepTac

private theorem preservingXor_restore_finish
    (output : List Bool) :
    preservingXorMachine.step
      (preservingXorConfiguration 3 none [] [] output) =
      some (Turing.haltList preservingXorMachine output) := by
  preservingXorStepTac

private def preservingXor_scanTrace
    (input archive output : List Bool) :
    EvalsToInTime preservingXorMachine.step (preservingXorConfiguration 2 none input archive
        output)
      (some (preservingXorConfiguration 3 none []
        (input.reverse ++ archive) output))
      (input.length + 1) := by
  induction input generalizing archive with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (preservingXor_scan_finish archive output)
  | cons bit input ih =>
      have first := oneStep _ _ (preservingXor_scan_step bit input archive output)
      have rest := ih (bit :: archive)
      have full := EvalsToInTime.trans preservingXorMachine.step _ _ _ _ _ first rest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using full

private def preservingXor_restoreTrace
    (archive output : List Bool) :
    EvalsToInTime preservingXorMachine.step (preservingXorConfiguration 3 none [] archive output)
      (some (Turing.haltList preservingXorMachine
        (archive.reverse ++ output)))
      (archive.length + 1) := by
  induction archive generalizing output with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          zero_add] using
          oneStep _ _ (preservingXor_restore_finish output)
  | cons bit archive ih =>
      have first := oneStep _ _ (preservingXor_restore_step bit archive output)
      have rest := ih (bit :: output)
      have full := EvalsToInTime.trans preservingXorMachine.step _ _ _ _ _ first rest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, Nat.add_assoc, Nat.reduceAdd] using full

private def preservingXor_totalTrace (input : List Bool) :
    EvalsToInTime preservingXorMachine.step (preservingXorConfiguration 0 none input [] [])
      (some (Turing.haltList preservingXorMachine
        (binaryGaussianXorPreservingWord input)))
      (2 * input.length + 4) := by
  cases input with
  | nil =>
      have first := oneStep _ _ (preservingXor_first_missing [] [])
      have scan := preservingXor_scanTrace [] [] []
      have restore := preservingXor_restoreTrace [] []
      have firstScan := EvalsToInTime.trans preservingXorMachine.step _ _ _ _ _ first scan
      have full := EvalsToInTime.trans preservingXorMachine.step _ _ _ _ _ firstScan restore
      exact rebound full (by simp only [List.length_nil, zero_add, Nat.reduceAdd, mul_zero,
          Nat.reduceLeDiff])
  | cons first remaining =>
      have firstStep := oneStep _ _ (preservingXor_first_step first remaining [] [])
      cases remaining with
      | nil =>
          have secondStep := oneStep _ _ (preservingXor_second_missing first [] [])
          have scan := preservingXor_scanTrace [] [] []
          have restore := preservingXor_restoreTrace [] []
          have firstTwo := EvalsToInTime.trans
            preservingXorMachine.step _ _ _ _ _ firstStep secondStep
          have firstScan := EvalsToInTime.trans preservingXorMachine.step _ _ _ _ _ firstTwo scan
          have full := EvalsToInTime.trans preservingXorMachine.step _ _ _ _ _ firstScan restore
          exact rebound full (by simp only [List.length_nil, zero_add, Nat.reduceAdd,
              List.length_cons, mul_one, Nat.reduceLeDiff])
      | cons second remaining =>
          have secondStep := oneStep _ _ (preservingXor_second_step first second remaining [] [])
          have scan := preservingXor_scanTrace
            remaining [Bool.xor first second] []
          have restore := preservingXor_restoreTrace
            (remaining.reverse ++ [Bool.xor first second]) []
          have firstTwo := EvalsToInTime.trans
            preservingXorMachine.step _ _ _ _ _ firstStep secondStep
          have firstScan := EvalsToInTime.trans preservingXorMachine.step _ _ _ _ _ firstTwo scan
          have full := EvalsToInTime.trans preservingXorMachine.step _ _ _ _ _ firstScan restore
          have houtput :
              (remaining.reverse ++ [Bool.xor first second]).reverse ++
                ([] : List Bool) =
              binaryGaussianXorPreservingWord
                (first :: second :: remaining) := by
            simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
                List.reverse_reverse,
                List.cons_append, List.append_nil, binaryGaussianXorPreservingWord]
          rw [houtput] at full
          exact rebound full (by
            simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil,
                zero_add,
                Nat.reduceAdd]
            omega)

private noncomputable def binaryGaussianXorPreservingComputable :
    Turing.TM2ComputableInPolyTime GapCVP.bitEncoding
      GapCVP.bitEncoding binaryGaussianXorPreservingWord where
  tm := preservingXorMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 4
  outputsFun input := {
    steps := (preservingXor_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, preservingXorMachine_init,
              Option.map_some] using
          (preservingXor_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (preservingXor_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X, ge_iff_le] using hsteps
  }

end Factor400BinaryPreservingXorWorker

namespace Factor400BinaryPhysicalParityTM

open GapCVP.OutputBoundedDependentRecordFold
open GapCVP.Factor400BinarySourceTM GapCVP.Factor400BinaryPreservingXorWorker

/-- GapCVP reduction support. -/
def prefixParityOutput : List Bool → List Bool :=
  boundedRecordFoldOutput binaryGaussianXorPreservingWord

/-- GapCVP reduction support. -/
noncomputable def prefixParityComputable :
    Turing.TM2ComputableInPolyTime
      GapCVP.bitEncoding GapCVP.bitEncoding prefixParityOutput :=
  nonexpansiveBoundedWorkerComputable
    binaryGaussianXorPreservingComputable
    binaryGaussianXorPreservingWord_nonexpansive

private theorem preservingXor_iterate_prefix
    (first : Bool) (remaining suffix : List Bool) :
    ((binaryGaussianXorPreservingWord^[remaining.length])
      (first :: (remaining ++ suffix))) =
        remaining.foldl Bool.xor first :: suffix := by
  induction remaining generalizing first with
  | nil =>
      simp only [List.length_nil, List.nil_append, Function.iterate_zero, id_eq, List.foldl_nil]
  | cons next tail ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change
        ((binaryGaussianXorPreservingWord^[tail.length])
          (Bool.xor first next :: (tail ++ suffix))) =
            tail.foldl Bool.xor (Bool.xor first next) :: suffix
      exact ih (Bool.xor first next)

theorem prefixParityOutput_valid
    (first : Bool) (remaining suffix : List Bool) :
    prefixParityOutput
      (unaryBoundedFoldWord remaining.length
        (first :: (remaining ++ suffix))) =
          remaining.foldl Bool.xor first :: suffix := by
  simp only [prefixParityOutput, boundedRecordFoldOutput,
    parseUnaryBoundedFold_word]
  exact preservingXor_iterate_prefix first remaining suffix

end Factor400BinaryPhysicalParityTM

namespace BinaryCoefficientTM

open Turing GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceMixedRadixOriginalSourceDescriptorRotationTM
open GapCVP.SourceFourFamilyMarkerRotationTM GapCVP.Factor400BinaryPhysicalParityTM

private def convolutionProductMarker : List Bool → List Bool :=
  markerConditionalOutput
    (markerConditionalOutput
      (markerConditionalOutput
        (fun _ : List Bool => [true]) [false])
      [false])
    [false]

private noncomputable def convolutionProductMarkerComputable :
    BitTM
      convolutionProductMarker :=
  markerConditionalComputable
    (markerConditionalComputable
      (markerConditionalComputable
        (sourceFixedWordComputable [true]) [false])
      [false])
    [false]

@[simp] private theorem convolutionProductMarker_valid
    (matched left right : Bool) :
    convolutionProductMarker [matched, left, right] =
      [matched && left && right] := by
  cases matched <;> cases left <;> cases right <;> rfl

private theorem convolutionProductMarker_length
    (input : List Bool) :
    (convolutionProductMarker input).length = 1 := by
  cases input with
  | nil => rfl
  | cons matched remaining =>
      cases matched with
      | false => rfl
      | true =>
          cases remaining with
          | nil => rfl
          | cons left remaining =>
              cases left with
              | false => rfl
              | true =>
                  cases remaining with
                  | nil => rfl
                  | cons right remaining =>
                      cases right <;> rfl

private def convolutionProductRecordFoldOutput : List Bool → List Bool :=
  boundedRecordFoldOutput
    (fourFamilyOriginalMarkerRotationOutput
      convolutionProductMarker)

private noncomputable def convolutionProductRecordFoldComputable :
    BitTM
      convolutionProductRecordFoldOutput := by
  exact fourFamilyOriginalMarkerFoldComputable
    convolutionProductMarkerComputable
    (fun input => (convolutionProductMarker_length input).le)

private def convolutionProductMarkerStream
    (queries : List (List Bool)) : List Bool :=
  fourFamilyOriginalMarkerStream
    convolutionProductMarker queries

private theorem convolutionProductMarkerStream_length
    (queries : List (List Bool)) :
    (convolutionProductMarkerStream queries).length =
      queries.length := by
  induction queries with
  | nil => rfl
  | cons query remaining ih =>
      change
        (convolutionProductMarker query ++
          convolutionProductMarkerStream remaining).length =
            remaining.length + 1
      rw [List.length_append,
        convolutionProductMarker_length, ih]
      omega

/-- GapCVP reduction support. -/
def convolutionCoefficientOutput : List Bool → List Bool :=
  prefixParityOutput ∘ convolutionProductRecordFoldOutput

/-- GapCVP reduction support. -/
noncomputable def convolutionCoefficientComputable :
    BitTM
      convolutionCoefficientOutput :=
  GapCVP.TMComposition.computableInPolyTime
    convolutionProductRecordFoldComputable
    prefixParityComputable

/-- GapCVP reduction support. -/
def convolutionCoefficientQuery
    (queries : List (List Bool)) : List Bool :=
  unaryBoundedFoldWord queries.length
    (sourceMixedRadixOriginalSourceQueryStream queries ++
      unaryBoundedFoldWord queries.length [false])

@[simp] private theorem convolutionCoefficientOutput_queries
    (queries : List (List Bool)) :
    convolutionCoefficientOutput
        (convolutionCoefficientQuery queries) =
      [(convolutionProductMarkerStream queries).foldl
        Bool.xor false] := by
  unfold convolutionCoefficientOutput
    convolutionProductRecordFoldOutput
    convolutionCoefficientQuery
  rw [Function.comp_apply,
    boundedRecordFoldOutput_sourceFourFamilyOriginalMarkerQueries]
  have hlength :
      (fourFamilyOriginalMarkerStream
        convolutionProductMarker queries).length =
          queries.length := by
    simpa only [convolutionProductMarkerStream] using convolutionProductMarkerStream_length queries
  simpa only [unaryBoundedFoldWord, List.append_assoc, List.cons_append, List.nil_append,
      convolutionProductMarkerStream, hlength, List.append_nil] using
      prefixParityOutput_valid false (convolutionProductMarkerStream queries) []

/-- GapCVP reduction support. -/
def wordConvolutionQueries
    {e : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word e)
    (coefficient : Fin (2 * e)) : List (List Bool) :=
  (List.finRange e).flatMap fun i =>
    (List.finRange e).map fun j =>
      [decide (i.val + j.val = coefficient.val), left i, right j]

private def wordConvolutionProductBits
    {e : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word e)
    (coefficient : Fin (2 * e)) : List Bool :=
  (List.finRange e).flatMap fun i =>
    (List.finRange e).map fun j =>
      if i.val + j.val = coefficient.val
      then left i && right j
      else false

theorem wordConvolutionQueries_length
    {e : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word e)
    (coefficient : Fin (2 * e)) :
    (wordConvolutionQueries left right coefficient).length = e * e := by
  simp only [wordConvolutionQueries, List.length_flatMap, List.length_map, List.length_finRange,
      List.map_const', List.sum_replicate, smul_eq_mul]

private theorem convolutionProductMarkerStream_wordQueries
    {e : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word e)
    (coefficient : Fin (2 * e)) :
    convolutionProductMarkerStream
        (wordConvolutionQueries left right coefficient) =
      wordConvolutionProductBits left right coefficient := by
  have hinner (i : Fin e) (items : List (Fin e)) :
      (items.map fun j =>
        [decide (i.val + j.val = coefficient.val),
          left i, right j]).flatMap convolutionProductMarker =
        items.map fun j =>
          if i.val + j.val = coefficient.val
          then left i && right j
          else false := by
    induction items with
    | nil => rfl
    | cons j remaining ih =>
        simp only [List.map_cons, List.flatMap_cons,
          convolutionProductMarker_valid]
        by_cases h : i.val + j.val = coefficient.val
        · simp only [h, decide_true, Bool.true_and, ih, Bool.ite_false_right, List.cons_append,
            List.nil_append,
              ↓reduceIte]
        · simp only [h, decide_false, Bool.false_and, ih, Bool.ite_false_right, List.cons_append,
            List.nil_append,
              ↓reduceIte]
  have houter (items : List (Fin e)) :
      (items.flatMap fun i =>
        (List.finRange e).map fun j =>
          [decide (i.val + j.val = coefficient.val),
            left i, right j]).flatMap convolutionProductMarker =
        items.flatMap fun i =>
          (List.finRange e).map fun j =>
            if i.val + j.val = coefficient.val
            then left i && right j
            else false := by
    induction items with
    | nil => rfl
    | cons i remaining ih =>
        simp only [List.flatMap_cons, List.flatMap_append, hinner i (List.finRange e),
            Bool.ite_false_right, ih]
  exact houter (List.finRange e)

private theorem foldl_xor_flatMap
    {α : Type} (items : List α)
    (bits : α → List Bool) (initial : Bool) :
    (items.flatMap bits).foldl Bool.xor initial =
      items.foldl
        (fun accumulator item =>
          (bits item).foldl Bool.xor accumulator)
        initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons first remaining ih =>
      simp only [List.flatMap_cons, List.foldl_append,
        List.foldl_cons]
      exact ih ((bits first).foldl Bool.xor initial)

private theorem convolutionInnerFold
    {e : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word e)
    (coefficient : Fin (2 * e))
    (i : Fin e) (items : List (Fin e))
    (initial : Bool) :
    (items.map fun j =>
      if i.val + j.val = coefficient.val
      then left i && right j
      else false).foldl Bool.xor initial =
      items.foldl
        (fun accumulator j =>
          if i.val + j.val = coefficient.val then
            Bool.xor accumulator (left i && right j)
          else accumulator)
        initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons first remaining ih =>
      simp only [List.map_cons, List.foldl_cons]
      by_cases h : i.val + first.val = coefficient.val
      · simp only [h, ↓reduceIte]
        exact ih (Bool.xor initial (left i && right first))
      · simp only [h, ↓reduceIte, Bool.xor_false]
        exact ih initial

private theorem wordConvolutionProductBits_foldl
    {e : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word e)
    (coefficient : Fin (2 * e)) :
    (wordConvolutionProductBits left right coefficient).foldl
        Bool.xor false =
      GapCVP.Core.EffectiveBinaryField.multiplyWords
        left right coefficient := by
  unfold wordConvolutionProductBits
  rw [foldl_xor_flatMap]
  unfold GapCVP.Core.EffectiveBinaryField.multiplyWords
  congr 1
  funext accumulator i
  exact convolutionInnerFold left right coefficient i
    (List.finRange e) accumulator

/-- GapCVP reduction support. -/
def wordConvolutionCoefficientQuery
    {e : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word e)
    (coefficient : Fin (2 * e)) : List Bool :=
  convolutionCoefficientQuery
    (wordConvolutionQueries left right coefficient)

@[simp] theorem convolutionCoefficientOutput_word
    {e : ℕ}
    (left right : GapCVP.Core.EffectiveBinaryField.Word e)
    (coefficient : Fin (2 * e)) :
    convolutionCoefficientOutput
        (wordConvolutionCoefficientQuery left right coefficient) =
      [GapCVP.Core.EffectiveBinaryField.multiplyWords
        left right coefficient] := by
  unfold wordConvolutionCoefficientQuery
  rw [convolutionCoefficientOutput_queries,
    convolutionProductMarkerStream_wordQueries,
    wordConvolutionProductBits_foldl]

end BinaryCoefficientTM

namespace GaussianXorWorker

open Turing

/-- GapCVP reduction support. -/
def binaryGaussianXorHeadWord : List Bool → List Bool
  | first :: second :: _ => [Bool.xor first second]
  | _ => []

private def binaryGaussianXorPeek
    (present absent : Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool)) :
    Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) :=
  .peek 0 (fun _ symbol => symbol)
    (.branch (fun symbol => symbol.isSome) present absent)

private def binaryGaussianXorGoto (phase : Fin 3) :
    Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) :=
  .goto (fun _ => phase)

private def binaryGaussianXorFirstStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) :=
  binaryGaussianXorPeek
    (.pop 0 (fun _ symbol => symbol) (binaryGaussianXorGoto 1))
    (binaryGaussianXorGoto 2)

private def binaryGaussianXorSecondStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) :=
  .pop 0
    (fun first second =>
      second.map (fun bit => Bool.xor (first.getD false) bit))
    (.branch (fun result => result.isSome)
      (.push 1 (fun result => result.getD false)
        (.load (fun _ => none) (binaryGaussianXorGoto 2)))
      (.load (fun _ => none) (binaryGaussianXorGoto 2)))

private def binaryGaussianXorDrainStatement :
    Turing.TM2.Stmt
      (fun _ : Fin 2 => Bool) (Fin 3) (Option Bool) :=
  binaryGaussianXorPeek
    (.pop 0 (fun _ _ => none) (binaryGaussianXorGoto 2))
    (.load (fun _ => none) .halt)

private abbrev binaryGaussianXorMachine : Turing.FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := Option Bool
  initialState := none
  m phase :=
    if phase = (0 : Fin 3) then
      binaryGaussianXorFirstStatement
    else if phase = (1 : Fin 3) then
      binaryGaussianXorSecondStatement
    else
      binaryGaussianXorDrainStatement

private def binaryGaussianXorConfiguration
    (phase : Fin 3) (state : Option Bool)
    (input output : List Bool) : binaryGaussianXorMachine.Cfg where
  l := some phase
  var := state
  stk := ![input, output]

private theorem binaryGaussianXorMachine_init (input : List Bool) :
    Turing.initList binaryGaussianXorMachine input =
      binaryGaussianXorConfiguration 0 none input [] := by
  simp only [binaryGaussianXorMachine, Fin.isValue, initList, eq_mpr_eq_cast, cast_eq, dite_eq_ite,
      binaryGaussianXorConfiguration]
  congr 1
  funext stack
  fin_cases stack <;> simp

/-- Executes the `binaryGaussianXorStepTac` machine-step simplifier. -/
macro "binaryGaussianXorStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [binaryGaussianXorMachine, binaryGaussianXorConfiguration,
          binaryGaussianXorPeek, binaryGaussianXorGoto,
          binaryGaussianXorFirstStatement,
          binaryGaussianXorSecondStatement,
          binaryGaussianXorDrainStatement, Turing.haltList,
          Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

private theorem binaryGaussianXor_first_step
    (first : Bool) (remaining output : List Bool) :
    binaryGaussianXorMachine.step
      (binaryGaussianXorConfiguration 0 none
        (first :: remaining) output) =
      some (binaryGaussianXorConfiguration 1
        (some first) remaining output) := by
  cases first <;> binaryGaussianXorStepTac

private theorem binaryGaussianXor_first_missing
    (output : List Bool) :
    binaryGaussianXorMachine.step
      (binaryGaussianXorConfiguration 0 none [] output) =
      some (binaryGaussianXorConfiguration 2 none [] output) := by
  binaryGaussianXorStepTac

private theorem binaryGaussianXor_second_step
    (first second : Bool) (remaining output : List Bool) :
    binaryGaussianXorMachine.step
      (binaryGaussianXorConfiguration 1 (some first)
        (second :: remaining) output) =
      some (binaryGaussianXorConfiguration 2 none
        remaining (Bool.xor first second :: output)) := by
  cases first <;> cases second <;> binaryGaussianXorStepTac

private theorem binaryGaussianXor_second_missing
    (first : Bool) (output : List Bool) :
    binaryGaussianXorMachine.step
      (binaryGaussianXorConfiguration 1 (some first) [] output) =
      some (binaryGaussianXorConfiguration 2 none [] output) := by
  cases first <;> binaryGaussianXorStepTac

private theorem binaryGaussianXor_drain_step
    (bit : Bool) (remaining output : List Bool) :
    binaryGaussianXorMachine.step
      (binaryGaussianXorConfiguration 2 none
        (bit :: remaining) output) =
      some (binaryGaussianXorConfiguration 2 none
        remaining output) := by
  cases bit <;> binaryGaussianXorStepTac

private theorem binaryGaussianXor_drain_finish (output : List Bool) :
    binaryGaussianXorMachine.step
      (binaryGaussianXorConfiguration 2 none [] output) =
      some (Turing.haltList binaryGaussianXorMachine output) := by
  binaryGaussianXorStepTac

private def binaryGaussianXor_drainTrace
    (input output : List Bool) :
    EvalsToInTime binaryGaussianXorMachine.step (binaryGaussianXorConfiguration 2 none input
        output)
      (some (Turing.haltList binaryGaussianXorMachine output))
      (input.length + 1) := by
  induction input with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.length_nil, zero_add] using
          oneStep _ _ (binaryGaussianXor_drain_finish output)
  | cons bit input ih =>
      have first := oneStep _ _ (binaryGaussianXor_drain_step bit input output)
      have full := EvalsToInTime.trans binaryGaussianXorMachine.step _ _ _ _ _ first ih
      simpa only [FinTM2.step, Fin.isValue, List.length_cons, Nat.add_assoc, Nat.reduceAdd]
          using full

private def binaryGaussianXor_totalTrace (input : List Bool) :
    EvalsToInTime binaryGaussianXorMachine.step (binaryGaussianXorConfiguration 0 none input [])
      (some (Turing.haltList binaryGaussianXorMachine
        (binaryGaussianXorHeadWord input)))
      (input.length + 2) := by
  cases input with
  | nil =>
      have first := oneStep _ _ (binaryGaussianXor_first_missing [])
      have rest := binaryGaussianXor_drainTrace [] []
      simpa [binaryGaussianXorHeadWord] using
        EvalsToInTime.trans binaryGaussianXorMachine.step _ _ _ _ _ first rest
  | cons first remaining =>
      have firstStep := oneStep _ _ (binaryGaussianXor_first_step first remaining [])
      cases remaining with
      | nil =>
          have secondStep := oneStep _ _ (binaryGaussianXor_second_missing first [])
          have rest := binaryGaussianXor_drainTrace [] []
          have firstTwo := EvalsToInTime.trans
            binaryGaussianXorMachine.step _ _ _ _ _ firstStep secondStep
          simpa [binaryGaussianXorHeadWord] using
            EvalsToInTime.trans binaryGaussianXorMachine.step _ _ _ _ _ firstTwo rest
      | cons second remaining =>
          have secondStep := oneStep _ _ (binaryGaussianXor_second_step first second remaining [])
          have rest := binaryGaussianXor_drainTrace
            remaining [Bool.xor first second]
          have firstTwo := EvalsToInTime.trans
            binaryGaussianXorMachine.step _ _ _ _ _ firstStep secondStep
          have full := EvalsToInTime.trans binaryGaussianXorMachine.step _ _ _ _ _ firstTwo rest
          exact rebound full (by simp)

/-- GapCVP reduction support. -/
noncomputable def binaryGaussianXorHeadComputable :
    Turing.TM2ComputableInPolyTime GapCVP.bitEncoding
      GapCVP.bitEncoding binaryGaussianXorHeadWord where
  tm := binaryGaussianXorMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun input := {
    steps := (binaryGaussianXor_totalTrace input).steps
    evals_in_steps := by
      simpa only [Option.bind_eq_bind, FinTM2.step, Fin.isValue, Equiv.invFun_as_coe,
          Equiv.refl_symm,
          Equiv.coe_refl, bitEncoding, id_eq, List.map_id_fun, binaryGaussianXorMachine_init,
              Option.map_some] using
          (binaryGaussianXor_totalTrace input).evals_in_steps
    steps_le_m := by
      have hsteps := (binaryGaussianXor_totalTrace input).steps_le_m
      simpa only [FinTM2.step, Fin.isValue, bitEncoding, id_eq, Polynomial.eval_add,
          Polynomial.eval_X,
          Polynomial.eval_ofNat, ge_iff_le] using hsteps
  }

end GaussianXorWorker

namespace GaussianRowWorker

open Turing GapCVP.OutputPolynomialCompositionClosure GapCVP.SourceCanonicalFixedWordTuringTM

/-- GapCVP reduction support. -/
def binaryGaussianFirstCellWord : List Bool → List Bool :=
  markerConditionalOutput (fun _ : List Bool => [true]) [false]

/-- GapCVP reduction support. -/
noncomputable def binaryGaussianFirstCellComputable :
    BitTM
      binaryGaussianFirstCellWord :=
  markerConditionalComputable
    (sourceFixedWordComputable [true]) [false]

@[simp] theorem binaryGaussianFirstCellWord_valid
    (first : Bool) (remaining : List Bool) :
    binaryGaussianFirstCellWord (first :: remaining) = [first] := by
  cases first <;> rfl

end GaussianRowWorker

namespace BinaryModularReductionTM

open Turing GapCVP.OutputPolynomialCompositionClosure GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceFourFamilyMarkerRotationTM GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.GaussianXorWorker GapCVP.GaussianRowWorker

private def modularReductionGatedMaskOutput : List Bool → List Bool :=
  markerConditionalOutput
    (markerConditionalOutput
      (fun _ : List Bool => [true]) [false])
    [false]

private noncomputable def modularReductionGatedMaskComputable :
    BitTM
      modularReductionGatedMaskOutput :=
  markerConditionalComputable
    (markerConditionalComputable
      (sourceFixedWordComputable [true]) [false])
    [false]

private def modularReductionDestinationOutput
    (input : List Bool) : List Bool :=
  binaryGaussianFirstCellWord input.tail.tail

private noncomputable def modularReductionDestinationComputable :
    BitTM
      modularReductionDestinationOutput := by
  have htail := GapCVP.TMComposition.computableInPolyTime
    dropHeadComputable dropHeadComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    htail binaryGaussianFirstCellComputable
  change BitTM
    (fun input => binaryGaussianFirstCellWord input.tail.tail)
  simpa only [Function.comp_def] using hphysical

private def modularReductionPackedXorInput
    (input : List Bool) : List Bool :=
  modularReductionGatedMaskOutput input ++
    modularReductionDestinationOutput input

private noncomputable def modularReductionPackedXorComputable :
    BitTM
      modularReductionPackedXorInput :=
  pointwiseAppendComputable
    modularReductionGatedMaskComputable
    modularReductionDestinationComputable

/-- GapCVP reduction support. -/
def modularReductionCellOutput : List Bool → List Bool :=
  binaryGaussianXorHeadWord ∘ modularReductionPackedXorInput

private noncomputable def modularReductionCellComputable :
    BitTM
      modularReductionCellOutput :=
  GapCVP.TMComposition.computableInPolyTime
    modularReductionPackedXorComputable
    binaryGaussianXorHeadComputable

@[simp] theorem modularReductionCellOutput_valid
    (gate mask destination : Bool) :
    modularReductionCellOutput [gate, mask, destination] =
      [Bool.xor (gate && mask) destination] := by
  cases gate <;> cases mask <;> cases destination <;> rfl

private theorem modularReductionGatedMaskOutput_singleton
    (input : List Bool) :
    ∃ bit : Bool, modularReductionGatedMaskOutput input = [bit] := by
  cases input with
  | nil => exact ⟨false, rfl⟩
  | cons gate remaining =>
      cases gate with
      | false => exact ⟨false, rfl⟩
      | true =>
          cases remaining with
          | nil => exact ⟨false, rfl⟩
          | cons mask remaining =>
              cases mask with
              | false => exact ⟨false, rfl⟩
              | true => exact ⟨true, rfl⟩

private theorem modularReductionDestinationOutput_singleton
    (input : List Bool) :
    ∃ bit : Bool, modularReductionDestinationOutput input = [bit] := by
  unfold modularReductionDestinationOutput
  cases htail : input.tail.tail with
  | nil =>
      refine ⟨false, ?_⟩
      simp only [binaryGaussianFirstCellWord, markerConditionalOutput]
  | cons bit remaining =>
      refine ⟨bit, ?_⟩
      exact binaryGaussianFirstCellWord_valid bit remaining

theorem modularReductionCellOutput_length
    (input : List Bool) :
    (modularReductionCellOutput input).length = 1 := by
  obtain ⟨gate, hgate⟩ :=
    modularReductionGatedMaskOutput_singleton input
  obtain ⟨destination, hdestination⟩ :=
    modularReductionDestinationOutput_singleton input
  simp only [modularReductionCellOutput, Function.comp_apply, binaryGaussianXorHeadWord,
      modularReductionPackedXorInput, hgate, hdestination, List.cons_append, List.nil_append,
          List.length_cons,
      List.length_nil, zero_add]

/-- GapCVP reduction support. -/
def modularReductionWordRowOutput : List Bool → List Bool :=
  boundedRecordFoldOutput
    (fourFamilyOriginalMarkerRotationOutput
      modularReductionCellOutput)

/-- GapCVP reduction support. -/
noncomputable def modularReductionWordRowComputable :
    BitTM
      modularReductionWordRowOutput := by
  exact fourFamilyOriginalMarkerFoldComputable
    modularReductionCellComputable
    (fun input => (modularReductionCellOutput_length input).le)

/-- GapCVP reduction support. -/
def finiteWordBits {d : ℕ}
    (word : GapCVP.Core.EffectiveBinaryField.Word d) : List Bool :=
  (List.finRange d).map word

end BinaryModularReductionTM

namespace BinaryExplicitAffineSystem

open scoped BigOperators

open GapCVP.Core hiding sourceFormulaField
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.BinaryReedSolomonParity

/-- GapCVP reduction support. -/
def explicitMomentBudget
    (encodingLength : ℕ) (formula : Formula) : ℕ :=
  sourceSizeParameter encodingLength formula ^ 30

/-- GapCVP reduction support. -/
abbrev ExplicitConstraintFamily
    (encodingLength : ℕ) (formula : Formula) :=
  sourceSATConstraintFamily formula
    (explicitMomentBudget encodingLength formula)

/-- GapCVP reduction support. -/
abbrev ExplicitGridPoint
    (encodingLength : ℕ) (formula : Formula) :=
  sourceSATGridPoint
    (sourceFormulaGrid encodingLength formula)

/-- GapCVP reduction support. -/
def sourceFormulaExplicitGridOrder
    (encodingLength : ℕ) (formula : Formula) :
    Fin (Fintype.card
      (ExplicitGridPoint encodingLength formula)) ≃
      ExplicitGridPoint encodingLength formula :=
  (finCongr (show
      Fintype.card (ExplicitGridPoint encodingLength formula) =
        (sourceFormulaGrid encodingLength formula).card by simp only [Fintype.card_coe])).trans
    (GapCVP.BinarySourceCoordinateOrder.sourceFormulaGridOrder
      encodingLength formula)

private def explicitFiniteReindexLinearEquiv
    {K : Type*} [Field K]
    {α : Type*} {n : ℕ}
    (order : Fin n ≃ α) :
    (α → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.funCongrLeft K K order

/-- GapCVP reduction support. -/
abbrev explicitFamilyRowCount
    (encodingLength : ℕ) (formula : Formula)
    (family : ExplicitConstraintFamily encodingLength formula) : ℕ :=
  match family with
  | .inl _ =>
      Fintype.card (ExplicitGridPoint encodingLength formula)
  | .inr (.inl _) =>
      Fintype.card
        (ExplicitGridPoint encodingLength formula ×
          sourceFormulaField encodingLength formula)
  | .inr (.inr (.inl _)) =>
      Fintype.card (ExplicitGridPoint encodingLength formula)
  | .inr (.inr (.inr _)) =>
      Fintype.card (ExplicitGridPoint encodingLength formula)

theorem explicitOrdinaryDegree_lt_grid
    (encodingLength : ℕ) (formula : Formula)
    (index : Fin (explicitMomentBudget encodingLength formula + 1)) :
    formula.variableCount * index.val <
      Fintype.card (ExplicitGridPoint encodingLength formula) := by
  let sourceSize := sourceSizeParameter encodingLength formula
  have hvariables : formula.variableCount ≤ sourceSize :=
    source_variableCount_le_size encodingLength formula
  have hindex : index.val ≤ sourceSize ^ 30 := by
    have hlt := index.isLt
    simpa only [explicitMomentBudget, ge_iff_le] using Nat.le_of_lt_succ hlt
  have hgrid := sourceFormulaGrid_max_degree_lt
    encodingLength formula
  have hproduct :
      formula.variableCount * index.val ≤ sourceSize ^ 31 := by
    calc
      formula.variableCount * index.val ≤
          sourceSize * sourceSize ^ 30 :=
        Nat.mul_le_mul hvariables hindex
      _ = sourceSize ^ 31 := by
        calc
          sourceSize * sourceSize ^ 30 =
              sourceSize ^ 30 * sourceSize := Nat.mul_comm _ _
          _ = sourceSize ^ 31 := by
            simpa only [Nat.reduceAdd] using (pow_succ sourceSize 30).symm
  have hcard :
      Fintype.card (ExplicitGridPoint encodingLength formula) =
        (sourceFormulaGrid encodingLength formula).card := by
    simp only [Fintype.card_coe]
  rw [hcard]
  exact lt_of_le_of_lt hproduct hgrid

theorem explicitShiftedDegree_lt_grid
    (encodingLength : ℕ) (formula : Formula)
    (index : Fin (explicitMomentBudget encodingLength formula + 1)) :
    (formula.variableCount - 1) * index.val <
      Fintype.card (ExplicitGridPoint encodingLength formula) := by
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_right index.val
      (Nat.sub_le formula.variableCount 1))
    (explicitOrdinaryDegree_lt_grid
      encodingLength formula index)

/-- GapCVP reduction support. -/
def explicitFamilyLinearMap
    (encodingLength : ℕ) (formula : Formula)
    (family : ExplicitConstraintFamily encodingLength formula) :
    (Fin (sourceFormulaDimension encodingLength formula) →
      sourceFormulaField encodingLength formula) →ₗ[
        sourceFormulaField encodingLength formula]
      (Fin (explicitFamilyRowCount
        encodingLength formula family) →
          sourceFormulaField encodingLength formula) := by
  let grid := sourceFormulaGrid encodingLength formula
  let gridOrder := sourceFormulaExplicitGridOrder
    encodingLength formula
  rcases family with _ | family
  · exact
      (explicitFiniteReindexLinearEquiv gridOrder).toLinearMap.comp
        (sourceGlobalNormalizationMap formula grid)
  · rcases family with clause | family
    · exact
        (sourceFiniteReindexLinearEquiv
          (K := sourceFormulaField encodingLength formula)
          (ExplicitGridPoint encodingLength formula ×
            sourceFormulaField encodingLength formula)).toLinearMap.comp
          (sourceClauseRefinementMap formula grid clause)
    · rcases family with ordinary | shifted
      · obtain ⟨tableType, moment⟩ := ordinary
        exact
          (constructiveParityLinearMap
            (fun position => (gridOrder position).val)
            (explicitOrdinaryDegree_lt_grid
              encodingLength formula moment)).comp
            ((explicitFiniteReindexLinearEquiv
              gridOrder).toLinearMap.comp
                (sourceOrdinaryMomentMap
                  formula grid tableType moment.val))
      · obtain ⟨clause, tuple, localVariable, moment⟩ := shifted
        exact
          (constructiveParityLinearMap
            (fun position => (gridOrder position).val)
            (explicitShiftedDegree_lt_grid
              encodingLength formula moment)).comp
            ((explicitFiniteReindexLinearEquiv
              gridOrder).toLinearMap.comp
                (sourceShiftedMomentMap
                  formula grid
                  (sourceFormulaVariablePlace
                    encodingLength formula)
                  clause tuple localVariable moment.val))

/-- GapCVP reduction support. -/
def explicitFamilyTarget
    (encodingLength : ℕ) (formula : Formula)
    (family : ExplicitConstraintFamily encodingLength formula) :
    Fin (explicitFamilyRowCount
      encodingLength formula family) →
      sourceFormulaField encodingLength formula :=
  fun _ => match family with
    | .inl _ => 1
    | .inr _ => 0

private def explicitFamilyFieldMatrix
    (encodingLength : ℕ) (formula : Formula)
    (family : ExplicitConstraintFamily encodingLength formula) :
    Matrix
      (Fin (explicitFamilyRowCount
        encodingLength formula family))
      (Fin (sourceFormulaDimension encodingLength formula))
      (sourceFormulaField encodingLength formula) :=
  LinearMap.toMatrix'
    (explicitFamilyLinearMap encodingLength formula family)

/-- GapCVP reduction support. -/
abbrev sourceFormulaExplicitBinarySystem
    (encodingLength : ℕ) (formula : Formula) : BinaryAffineSystem :=
  assembledBinaryAffineSystem
    (sourceFormulaFieldBasis encodingLength formula)
    (explicitFamilyRowCount encodingLength formula)
    (explicitFamilyFieldMatrix encodingLength formula)
    (explicitFamilyTarget encodingLength formula)

theorem sourceFormulaExplicitBinarySystem_solves_iff_family
    (encodingLength : ℕ) (formula : Formula)
    (values : Fin (sourceFormulaDimension
      encodingLength formula) → ℤ) :
    (sourceFormulaExplicitBinarySystem
      encodingLength formula).Solves values ↔
      ∀ family : ExplicitConstraintFamily encodingLength formula,
        explicitFamilyLinearMap encodingLength formula family
          (fun position =>
            algebraMap (ZMod 2)
              (sourceFormulaField encodingLength formula)
              (values position : ZMod 2)) =
          explicitFamilyTarget encodingLength formula family := by
  unfold sourceFormulaExplicitBinarySystem
  rw [assembledBinaryAffineSystem_solves_iff]
  simp only [explicitFamilyFieldMatrix,
    LinearMap.toMatrix'_mulVec]

end BinaryExplicitAffineSystem

namespace BinarySourceRowOrder

open scoped BigOperators

open GapCVP.Core GapCVP.BinaryExplicitAffineSystem

attribute [local instance] Classical.propDecidable

/-- GapCVP reduction support. -/
def sourceFormulaExplicitRefinementOrder
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula) :
    Fin (Fintype.card
      (ExplicitGridPoint encodingLength formula ×
        GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength formula)) ≃
      ExplicitGridPoint encodingLength formula ×
        GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength formula := by
  let grid := ExplicitGridPoint encodingLength formula
  let field :=
    GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
      encodingLength formula
  have hcard : Fintype.card (grid × field) =
      Fintype.card grid * Fintype.card field := by
    simp only [Fintype.card_prod]
  refine (finCongr hcard).trans ?_
  exact (finProdFinEquiv
    (m := Fintype.card grid)
    (n := Fintype.card field)).symm.trans
      ((sourceFormulaExplicitGridOrder encodingLength formula).prodCongr
        (GapCVP.BinarySourceCoordinateOrder.sourceFormulaFieldCardOrder
          encodingLength formula))

end BinarySourceRowOrder

namespace BinaryOrderedAssembly

open GapCVP.Core

variable {ι K : Type*} [Field K] [Algebra (ZMod 2) K]
variable {degree dimension rowCount : ℕ}

/-- GapCVP reduction support. -/
abbrev assembledBinaryAffineSystemOrdered
    (basis : Module.Basis (Fin degree) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) →
      Matrix (Fin (rowCounts family)) (Fin dimension) K)
    (targets : (family : ι) → Fin (rowCounts family) → K)
    (rowOrder : Fin rowCount ≃ assembledBinaryRow rowCounts degree) :
    BinaryAffineSystem where
  rowCount := rowCount
  dimension := dimension
  check := fun row column =>
    assembledBinaryParityMatrix basis rowCounts checks
      (rowOrder row) column
  rightHandSide := fun row =>
    assembledBinaryRightHandSide basis rowCounts targets
      (rowOrder row)

@[simp] private theorem assembledBinaryAffineSystemOrdered_rightHandSide_apply
    (basis : Module.Basis (Fin degree) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) →
      Matrix (Fin (rowCounts family)) (Fin dimension) K)
    (targets : (family : ι) → Fin (rowCounts family) → K)
    (rowOrder : Fin rowCount ≃ assembledBinaryRow rowCounts degree)
    (row : Fin rowCount) :
    (assembledBinaryAffineSystemOrdered
      basis rowCounts checks targets rowOrder).rightHandSide row =
      assembledBinaryRightHandSide basis rowCounts targets
        (rowOrder row) := by
  rfl

@[simp] private theorem assembledBinaryAffineSystemOrdered_check_mulVec_apply
    (basis : Module.Basis (Fin degree) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) →
      Matrix (Fin (rowCounts family)) (Fin dimension) K)
    (targets : (family : ι) → Fin (rowCounts family) → K)
    (rowOrder : Fin rowCount ≃ assembledBinaryRow rowCounts degree)
    (bits : Fin dimension → ZMod 2)
    (row : Fin rowCount) :
    (assembledBinaryAffineSystemOrdered
      basis rowCounts checks targets rowOrder).check.mulVec bits row =
      (assembledBinaryParityMatrix
        basis rowCounts checks).mulVec bits (rowOrder row) := by
  rfl

private theorem assembledBinaryAffineSystemOrdered_check_mulVec_eq_iff
    (basis : Module.Basis (Fin degree) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) →
      Matrix (Fin (rowCounts family)) (Fin dimension) K)
    (targets : (family : ι) → Fin (rowCounts family) → K)
    (rowOrder : Fin rowCount ≃ assembledBinaryRow rowCounts degree)
    (bits : Fin dimension → ZMod 2) :
    (assembledBinaryAffineSystemOrdered
      basis rowCounts checks targets rowOrder).check.mulVec bits =
        (assembledBinaryAffineSystemOrdered
          basis rowCounts checks targets rowOrder).rightHandSide ↔
      ∀ family : ι,
        (checks family).mulVec
          (fun position => algebraMap (ZMod 2) K (bits position)) =
            targets family := by
  constructor
  · intro hordered
    apply (assembledBinaryParityMatrix_mulVec_eq_iff
      basis rowCounts checks bits targets).mp
    funext row
    have hrow := congrFun hordered (rowOrder.symm row)
    rw [assembledBinaryAffineSystemOrdered_check_mulVec_apply,
      assembledBinaryAffineSystemOrdered_rightHandSide_apply] at hrow
    simpa only [assembledBinaryParityMatrix_mulVec_apply, Equiv.apply_symm_apply] using hrow
  · intro hfamilies
    have hrows := (assembledBinaryParityMatrix_mulVec_eq_iff
      basis rowCounts checks bits targets).mpr hfamilies
    funext row
    rw [assembledBinaryAffineSystemOrdered_check_mulVec_apply,
      assembledBinaryAffineSystemOrdered_rightHandSide_apply]
    exact congrFun hrows (rowOrder row)

theorem assembledBinaryAffineSystemOrdered_solves_iff
    (basis : Module.Basis (Fin degree) (ZMod 2) K)
    (rowCounts : ι → ℕ)
    (checks : (family : ι) →
      Matrix (Fin (rowCounts family)) (Fin dimension) K)
    (targets : (family : ι) → Fin (rowCounts family) → K)
    (rowOrder : Fin rowCount ≃ assembledBinaryRow rowCounts degree)
    (values : Fin dimension → ℤ) :
    (assembledBinaryAffineSystemOrdered
      basis rowCounts checks targets rowOrder).Solves values ↔
      ∀ family : ι,
        (checks family).mulVec
          (fun position => algebraMap (ZMod 2) K
            (values position : ZMod 2)) =
              targets family := by
  simp only [GapCVP.Core.BinaryAffineSystem.Solves, decide_eq_true_eq]
  exact assembledBinaryAffineSystemOrdered_check_mulVec_eq_iff
    basis rowCounts checks targets rowOrder (binaryResidue values)

end BinaryOrderedAssembly

namespace BinaryOrderedRefinement

open GapCVP.Core GapCVP.BinaryExplicitAffineSystem GapCVP.BinarySourceRowOrder

/-- GapCVP reduction support. -/
def sourceFormulaPhysicalFamilyLinearMap
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (family : ExplicitConstraintFamily encodingLength formula) :
    (Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength formula) →
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength formula) →ₗ[
          GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
            encodingLength formula]
      (Fin (explicitFamilyRowCount
        encodingLength formula family) →
        GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength formula) := by
  rcases family with global | family
  · exact explicitFamilyLinearMap
      encodingLength formula (.inl global)
  · rcases family with clause | family
    · exact
        (explicitFiniteReindexLinearEquiv
          (sourceFormulaExplicitRefinementOrder
            encodingLength formula)).toLinearMap.comp
          (sourceClauseRefinementMap formula
            (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
              encodingLength formula) clause)
    · exact explicitFamilyLinearMap
        encodingLength formula (.inr (.inr family))

/-- GapCVP reduction support. -/
def sourceFormulaPhysicalFamilyFieldMatrix
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (family : ExplicitConstraintFamily encodingLength formula) :
    Matrix
      (Fin (explicitFamilyRowCount
        encodingLength formula family))
      (Fin
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
          encodingLength formula))
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength formula) :=
  LinearMap.toMatrix'
    (sourceFormulaPhysicalFamilyLinearMap
      encodingLength formula family)

theorem sourceFormulaPhysicalFamilyLinearMap_eq_iff_explicit
    (encodingLength : ℕ) (formula : GapCVP.Core.Formula)
    (family : ExplicitConstraintFamily encodingLength formula)
    (values : Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength formula) →
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength formula) :
    sourceFormulaPhysicalFamilyLinearMap
        encodingLength formula family values =
      explicitFamilyTarget encodingLength formula family ↔
    explicitFamilyLinearMap
        encodingLength formula family values =
      explicitFamilyTarget encodingLength formula family := by
  rcases family with global | family
  · rfl
  · rcases family with clause | family
    · let grid :=
        GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
          encodingLength formula
      let field :=
        GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
          encodingLength formula
      let refinement :=
        sourceClauseRefinementMap formula grid clause values
      change
        (explicitFiniteReindexLinearEquiv
          (sourceFormulaExplicitRefinementOrder
            encodingLength formula)) refinement = 0 ↔
        (sourceFiniteReindexLinearEquiv
          (K := field)
          (ExplicitGridPoint encodingLength formula × field))
            refinement = 0
      exact
        (explicitFiniteReindexLinearEquiv
          (sourceFormulaExplicitRefinementOrder
            encodingLength formula)).map_eq_zero_iff.trans
          (sourceFiniteReindexLinearEquiv
            (K := field)
            (ExplicitGridPoint encodingLength formula × field)).map_eq_zero_iff.symm
    · rfl

end BinaryOrderedRefinement

namespace BinaryExplicitFourFamilyKernel

open GapCVP.Core GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryReedSolomonParity
open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K]

private theorem ordinarySystematicParity_iff
    (F : Formula) (points : Finset K)
    {pointCount : ℕ}
    (gridOrder : Fin pointCount ≃ sourceSATGridPoint points)
    (tableType : sourceSATTableType F) (moment : ℕ)
    (hdegree : F.variableCount * moment < pointCount)
    (values : Fin (sourceSATTableDimension F K points) → K) :
    (constructiveParityMatrix
      (fun index => (gridOrder index).val) hdegree).mulVec
        (fun index =>
          sourceOrdinaryMomentMap F points tableType moment values
            (gridOrder index)) = 0 ↔
      sourceOrdinaryMomentMap F points tableType moment values ∈
        sourceReedSolomonCode points (F.variableCount * moment) := by
  rw [constructiveParityMatrix_mulVec_eq_zero_iff_polynomial
    (fun index => (gridOrder index).val) hdegree
    (Subtype.val_injective.comp gridOrder.injective),
    sourceReedSolomonCode_mem_iff]
  refine exists_congr fun polynomial => ?_
  exact and_congr Iff.rfl (gridOrder.forall_congr fun _ => Iff.rfl)

private theorem shiftedSystematicParity_iff
    (F : Formula) (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    {pointCount : ℕ}
    (gridOrder : Fin pointCount ≃ sourceSATGridPoint points)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (moment : ℕ)
    (hdegree : (F.variableCount - 1) * moment < pointCount)
    (values : Fin (sourceSATTableDimension F K points) → K) :
    (constructiveParityMatrix
      (fun index => (gridOrder index).val) hdegree).mulVec
        (fun index =>
          sourceShiftedMomentMap F points variablePlace
            clause tuple localVar moment values
              (gridOrder index)) = 0 ↔
      sourceShiftedMomentMap F points variablePlace
        clause tuple localVar moment values ∈
          sourceReedSolomonCode points
            ((F.variableCount - 1) * moment) := by
  rw [constructiveParityMatrix_mulVec_eq_zero_iff_polynomial
    (fun index => (gridOrder index).val) hdegree
    (Subtype.val_injective.comp gridOrder.injective),
    sourceReedSolomonCode_mem_iff]
  refine exists_congr fun polynomial => ?_
  exact and_congr Iff.rfl (gridOrder.forall_congr fun _ => Iff.rfl)

theorem sourceFormulaExplicitBinarySystem_solves_iff_concreteSATFieldChecks
    (encodingLength : ℕ) (formula : Formula)
    (z : Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength formula) → ℤ) :
    (sourceFormulaExplicitBinarySystem
      encodingLength formula).Solves z ↔
      concreteSATFieldChecks formula
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
          encodingLength formula)
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
          encodingLength formula)
        (sourceSizeParameter encodingLength formula ^ 30)
        (fun position =>
          algebraMap (ZMod 2)
            (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
              encodingLength formula)
            (z position : ZMod 2)) := by
  classical
  rw [sourceFormulaExplicitBinarySystem_solves_iff_family]
  let grid :=
    GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
      encodingLength formula
  let gridOrder := sourceFormulaExplicitGridOrder
    encodingLength formula
  let values : Fin
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength formula) →
      GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength formula :=
    fun position => algebraMap (ZMod 2)
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
        encodingLength formula)
      (z position : ZMod 2)
  change
    (∀ family : ExplicitConstraintFamily encodingLength formula,
      explicitFamilyLinearMap encodingLength formula family values =
        explicitFamilyTarget encodingLength formula family) ↔
      concreteSATFieldChecks formula grid
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
          encodingLength formula)
        (explicitMomentBudget encodingLength formula) values
  simp only [GapCVP.Core.concreteSATFieldChecks, decide_eq_true_eq]
  constructor
  · intro hfamilies
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext point
      have hpoint := congrFun (hfamilies (.inl ()))
        (gridOrder.symm point)
      change
        sourceGlobalNormalizationMap formula grid values
          (gridOrder (gridOrder.symm point)) = 1 at hpoint
      simpa only [Equiv.apply_symm_apply] using hpoint
    · intro clause
      funext position
      let refinementOrder := Fintype.equivFin
        (ExplicitGridPoint encodingLength formula ×
          GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
            encodingLength formula)
      have hposition :=
        congrFun (hfamilies (.inr (.inl clause)))
          (refinementOrder position)
      change
        sourceClauseRefinementMap formula grid clause values
          (refinementOrder.symm (refinementOrder position)) = 0
          at hposition
      simpa only [Pi.zero_apply, Equiv.symm_apply_apply] using hposition
    · intro tableType moment
      apply (ordinarySystematicParity_iff
        formula grid gridOrder tableType moment.val
        (explicitOrdinaryDegree_lt_grid
          encodingLength formula moment) values).mp
      rw [constructiveParityMatrix, LinearMap.toMatrix'_mulVec]
      have hmoment := hfamilies
        (.inr (.inr (.inl (tableType, moment))))
      change
        constructiveParityLinearMap
          (fun position => (gridOrder position).val)
          (explicitOrdinaryDegree_lt_grid
            encodingLength formula moment)
          (fun position =>
            sourceOrdinaryMomentMap formula grid tableType moment.val
              values (gridOrder position)) = 0 at hmoment
      exact hmoment
    · intro clause tuple localVar moment
      apply (shiftedSystematicParity_iff
        formula grid
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
          encodingLength formula)
        gridOrder clause tuple localVar moment.val
        (explicitShiftedDegree_lt_grid
          encodingLength formula moment) values).mp
      rw [constructiveParityMatrix, LinearMap.toMatrix'_mulVec]
      have hmoment := hfamilies
        (.inr (.inr (.inr ⟨clause, tuple, localVar, moment⟩)))
      change
        constructiveParityLinearMap
          (fun position => (gridOrder position).val)
          (explicitShiftedDegree_lt_grid
            encodingLength formula moment)
          (fun position =>
            sourceShiftedMomentMap formula grid
              (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
                encodingLength formula)
              clause tuple localVar moment.val
              values (gridOrder position)) = 0 at hmoment
      exact hmoment
  · rintro ⟨hnormalization, hrefinement, hordinary, hshifted⟩
    intro family
    rcases family with _ | family
    · change
        explicitFiniteReindexLinearEquiv gridOrder
          (sourceGlobalNormalizationMap formula grid values) =
            fun _ => 1
      rw [hnormalization]
      rfl
    · rcases family with clause | family
      · change
          sourceFiniteReindexLinearEquiv
            (K := GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
              encodingLength formula)
            (ExplicitGridPoint encodingLength formula ×
              GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaField
                encodingLength formula)
            (sourceClauseRefinementMap formula grid clause values) = 0
        rw [hrefinement clause]
        exact map_zero _
      · rcases family with ordinary | shifted
        · obtain ⟨tableType, moment⟩ := ordinary
          change
            constructiveParityLinearMap
              (fun position => (gridOrder position).val)
              (explicitOrdinaryDegree_lt_grid
                encodingLength formula moment)
              (fun position =>
                sourceOrdinaryMomentMap formula grid tableType moment.val
                  values (gridOrder position)) = 0
          rw [← LinearMap.toMatrix'_mulVec]
          exact (ordinarySystematicParity_iff
            formula grid gridOrder tableType moment.val
            (explicitOrdinaryDegree_lt_grid
              encodingLength formula moment) values).mpr
              (hordinary tableType moment)
        · obtain ⟨clause, tuple, localVar, moment⟩ := shifted
          change
            constructiveParityLinearMap
              (fun position => (gridOrder position).val)
              (explicitShiftedDegree_lt_grid
                encodingLength formula moment)
              (fun position =>
                sourceShiftedMomentMap formula grid
                  (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
                    encodingLength formula)
                  clause tuple localVar moment.val
                  values (gridOrder position)) = 0
          rw [← LinearMap.toMatrix'_mulVec]
          exact (shiftedSystematicParity_iff
            formula grid
            (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaVariablePlace
              encodingLength formula)
            gridOrder clause tuple localVar moment.val
            (explicitShiftedDegree_lt_grid
              encodingLength formula moment) values).mpr
              (hshifted clause tuple localVar moment)

theorem integerSquaredNorm_wordOrder
    {newDimension oldDimension : ℕ}
    (columnOrder : Fin newDimension ≃ Fin oldDimension)
    (vector : Fin newDimension → ℤ) :
    integerSquaredNorm
        (fun column => vector (columnOrder.symm column)) =
      integerSquaredNorm vector := by
  unfold integerSquaredNorm
  exact Equiv.sum_comp columnOrder.symm
    (fun column : Fin newDimension => (vector column).natAbs ^ 2)

@[simp] private theorem binaryResidue_wordOrder
    {newDimension oldDimension : ℕ}
    (columnOrder : Fin newDimension ≃ Fin oldDimension)
    (vector : Fin newDimension → ℤ) :
    binaryResidue (fun column => vector (columnOrder.symm column)) =
      (fun column => binaryResidue vector (columnOrder.symm column)) := by
  rfl

/-- GapCVP reduction support. -/
abbrev reindexBinaryAffineSystem
    {rowCount dimension : ℕ}
    (system : BinaryAffineSystem)
    (rowOrder : Fin rowCount ≃ Fin system.rowCount)
    (columnOrder : Fin dimension ≃ Fin system.dimension) :
    BinaryAffineSystem where
  rowCount := rowCount
  dimension := dimension
  check := system.check.submatrix rowOrder columnOrder
  rightHandSide := fun row => system.rightHandSide (rowOrder row)

theorem reindexBinaryAffineSystem_solves_iff
    {rowCount dimension : ℕ}
    (system : BinaryAffineSystem)
    (rowOrder : Fin rowCount ≃ Fin system.rowCount)
    (columnOrder : Fin dimension ≃ Fin system.dimension)
    (vector : Fin dimension → ℤ) :
    (reindexBinaryAffineSystem system rowOrder columnOrder).Solves vector ↔
      system.Solves
        (fun column => vector (columnOrder.symm column)) := by
  simp only [GapCVP.Core.BinaryAffineSystem.Solves, decide_eq_true_eq]
  change
    (system.check.submatrix rowOrder columnOrder).mulVec
        (binaryResidue vector) =
      (fun row => system.rightHandSide (rowOrder row)) ↔
      system.check.mulVec
        (binaryResidue
          (fun column => vector (columnOrder.symm column))) =
        system.rightHandSide
  rw [Matrix.submatrix_mulVec_equiv]
  have hresidue :
      (binaryResidue vector) ∘ columnOrder.symm =
        binaryResidue
          (fun column => vector (columnOrder.symm column)) := by
    funext column
    rfl
  rw [hresidue]
  constructor
  · intro hsolve
    funext row
    have hrow := congrFun hsolve (rowOrder.symm row)
    simpa only [binaryResidue_wordOrder, Function.comp_apply, Equiv.apply_symm_apply] using hrow
  · intro hsolve
    funext row
    exact congrFun hsolve (rowOrder row)

end BinaryExplicitFourFamilyKernel

namespace Factor400BinaryConstructiveSourcePlaces

section

open GapCVP.Core
open scoped BigOperators
open Finset Polynomial

private def sourceFormulaSignedTableFiberSupports
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (tableType : sourceSATTableType F) :
    sourceFormulaField encodingLength F →
      Finset (sourceFormulaField encodingLength F) :=
  sourceSignedFiberSupportAt F
    (sourceFormulaGrid encodingLength F) z tableType

/-- GapCVP reduction support. -/
def sourceFormulaSignedTableOrdinaryMomentPolynomials
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (tableType : sourceSATTableType F) :
    ℕ → (sourceFormulaField encodingLength F)[X] := by
  classical
  exact sourceSignedOrdinaryMomentPolynomials F
    (sourceFormulaFieldBasis encodingLength F)
    (sourceFormulaGrid encodingLength F)
    (sourceFormulaVariablePlace encodingLength F)
    (sourceSizeParameter encodingLength F ^ 30)
    z hz tableType

theorem sourceFormulaSignedTableOrdinaryMomentPolynomials_natDegree
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (tableType : sourceSATTableType F)
    (j : ℕ) :
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz tableType j).natDegree ≤
        F.variableCount * j := by
  classical
  exact sourceSignedOrdinaryMomentPolynomials_natDegree F
    (sourceFormulaFieldBasis encodingLength F)
    (sourceFormulaGrid encodingLength F)
    (sourceFormulaVariablePlace encodingLength F)
    (sourceSizeParameter encodingLength F ^ 30)
    z hz tableType j

private theorem sourceFormulaSignedTableOrdinaryMomentPolynomials_eval
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (tableType : sourceSATTableType F)
    (point : sourceFormulaField encodingLength F)
    (hpoint : point ∈ sourceFormulaGrid encodingLength F)
    (j : ℕ) (hj : j ≤ sourceSizeParameter encodingLength F ^ 30) :
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz tableType j).eval point =
        supportMoment
          (sourceFormulaSignedTableFiberSupports
            encodingLength F z tableType point) j := by
  simpa only [sourceFormulaSignedTableOrdinaryMomentPolynomials,
      sourceFormulaSignedTableFiberSupports,
      sourceSignedFiberSupportAt, hpoint, ↓reduceDIte] using
      sourceSignedOrdinaryMomentPolynomials_eval F (sourceFormulaFieldBasis encodingLength F)
        (sourceFormulaGrid encodingLength F) (sourceFormulaVariablePlace encodingLength F)
        (sourceSizeParameter encodingLength F ^ 30) z hz tableType ⟨point, hpoint⟩ j hj

private theorem sourceFormulaSignedTable_globalGenericRank_pos
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z) :
    0 < maximalGenericHankelRank
      (sourceFormulaSignedTableOrdinaryMomentPolynomials
        encodingLength F z hz (.inl ()))
      (sourceSizeParameter encodingLength F ^ 4) := by
  classical
  obtain ⟨point, hpoint⟩ :=
    Finset.card_pos.mp (sourceFormulaGrid_card_pos encodingLength F)
  apply maximalGenericHankelRank_pos_of_normalized_moment
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz (.inl ()))
    (sourceSizeParameter encodingLength F ^ 4) point
  · exact pow_pos
      (lt_of_lt_of_le (by norm_num)
        (sourceSizeParameter_ge_one_hundred encodingLength F)) _
  · rw [sourceFormulaSignedTableOrdinaryMomentPolynomials_eval
      encodingLength F z hz (.inl ()) point hpoint 0 (Nat.zero_le _)]
    simpa only [sourceFormulaSignedTableFiberSupports, sourceSignedFiberSupportAt, hpoint,
        ↓reduceDIte,
        List.get_eq_getElem] using
        sourceSigned_globalSupportMoment_zero F (sourceFormulaFieldBasis encodingLength F)
          (sourceFormulaGrid encodingLength F) (sourceFormulaVariablePlace encodingLength F)
          (sourceSizeParameter encodingLength F ^ 30) z hz ⟨point, hpoint⟩

/-- GapCVP reduction support. -/
def sourceFormulaSignedTableShiftedMomentPolynomials
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable) :
    ℕ → (sourceFormulaField encodingLength F)[X] := by
  classical
  exact sourceSignedShiftedMomentPolynomials F
    (sourceFormulaFieldBasis encodingLength F)
    (sourceFormulaGrid encodingLength F)
    (sourceFormulaVariablePlace encodingLength F)
    (sourceSizeParameter encodingLength F ^ 30)
    z hz clause tuple localVar

private theorem sourceFormula_testedMomentDegree_lt_grid
    (encodingLength : ℕ) (F : Formula)
    (j : ℕ) (hj : j ≤ sourceSizeParameter encodingLength F ^ 30) :
    F.variableCount * j < (sourceFormulaGrid encodingLength F).card := by
  let N := sourceSizeParameter encodingLength F
  calc
    F.variableCount * j ≤ N * N ^ 30 := by
      exact Nat.mul_le_mul (source_variableCount_le_size encodingLength F) hj
    _ = N ^ 31 := by
      rw [show (31 : ℕ) = 1 + 30 by norm_num, pow_add, pow_one]
    _ < (sourceFormulaGrid encodingLength F).card :=
      sourceFormulaGrid_max_degree_lt encodingLength F

private theorem sourceFormulaSignedTable_shiftedMomentPolynomial_identity
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (j : ℕ) (hj : j ≤ sourceSizeParameter encodingLength F ^ 30) :
    (Polynomial.X - Polynomial.C
      (sourceFormulaVariablePlace encodingLength F localVar.val)) ^ j *
        sourceFormulaSignedTableShiftedMomentPolynomials
          encodingLength F z hz clause tuple localVar j =
      shiftedMomentCombination
        (sourceFormulaSignedTableOrdinaryMomentPolynomials
          encodingLength F z hz (.inr ⟨clause, tuple⟩))
        (sourceSATFieldBit
          (K := sourceFormulaField encodingLength F)
          (tuple.val localVar)) j := by
  classical
  apply sourceSigned_shiftedMomentPolynomial_identity F
    (sourceFormulaFieldBasis encodingLength F)
    (sourceFormulaGrid encodingLength F)
    (sourceFormulaVariablePlace encodingLength F)
    (sourceSizeParameter encodingLength F ^ 30)
    z hz clause tuple localVar j hj
  · intro point
    exact sourceSATPuncturedGrid_sub_ne_zero F
      (sourceFormulaVariablePlace encodingLength F) point localVar.val
  · exact sourceFormula_testedMomentDegree_lt_grid encodingLength F j hj

end

section

open GapCVP.Core Finset Polynomial

private theorem scaledSupport_div_ten_mul_le_field
    {N q budget : ℕ}
    (hscaled : 10 * budget ≤ q * N ^ 4) :
    10 * (budget / (N ^ 4 + 1)) ≤ q := by
  have hdiv :
      (budget / (N ^ 4 + 1)) * (N ^ 4 + 1) ≤ budget :=
    Nat.div_mul_le_self budget (N ^ 4 + 1)
  have hproduct :
      (10 * (budget / (N ^ 4 + 1))) * (N ^ 4 + 1) ≤
        q * (N ^ 4 + 1) := by
    calc
      (10 * (budget / (N ^ 4 + 1))) * (N ^ 4 + 1) =
          10 * ((budget / (N ^ 4 + 1)) * (N ^ 4 + 1)) := by ring
      _ ≤ 10 * budget := Nat.mul_le_mul_left 10 hdiv
      _ ≤ q * N ^ 4 := hscaled
      _ ≤ q * (N ^ 4 + 1) := Nat.mul_le_mul_left q (by omega)
  exact Nat.le_of_mul_le_mul_right hproduct
    (Nat.zero_lt_succ (N ^ 4))

private theorem scaledSupport_maximalGenericGoodFiberPoints_card
    {K : Type*} [Field K]
    (N q m d : ℕ)
    (points : Finset K)
    (supports : K → Finset K)
    (moments : ℕ → K[X])
    (hN : 100 ≤ N)
    (hq : N ^ 200 ≤ q)
    (hm : m ≤ N)
    (hd : d ≤ N)
    (hpoints : points.card = q - m)
    (hmoments : ∀ j : ℕ, (moments j).natDegree ≤ d * j)
    (budget : ℕ)
    (hweight : (∑ point ∈ points, (supports point).card) ≤ budget)
    (hscaled : 10 * budget ≤ q * N ^ 4) :
    2 * N ^ 39 <
      (maximalGenericGoodFiberPoints
        points supports moments (N ^ 4)).card := by
  classical
  have hbudget :
      10 * (budget / (N ^ 4 + 1)) ≤ q :=
    scaledSupport_div_ten_mul_le_field hscaled
  have hexceptions :=
    source_variable_and_hankel_exceptions_ten_mul_le_field_size
      hN hq hm
  have hdenominator :
      (genericHankelDenominator
        (maximalGenericHankelRank moments (N ^ 4))
        moments).natDegree ≤ N ^ 9 :=
    source_hankel_denominator_natDegree_le_power moments hd
      (maximalGenericHankelRank_spec moments (N ^ 4)).1
      hmoments
  have hlower := maximalGenericGoodFiberPoints_card_lower_bound
    points supports moments (N ^ 4) budget hweight
  have hclear := source_cleared_moment_degree_lt_half_field_size hN hq
  have hqpositive : 0 < q :=
    (pow_pos (show 0 < N by omega) 200).trans_le hq
  have hhalf : 2 * (q / 2) ≤ q := by omega
  omega

private theorem sourceFormulaSignedTable_maximalGoodFiberPoints_card_of_scaledNorm
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hscaled :
      10 * integerSquaredNorm z ≤
        Fintype.card (sourceFormulaField encodingLength F) *
          sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F) :
    2 * sourceSizeParameter encodingLength F ^ 39 <
      (maximalGenericGoodFiberPoints
        (sourceFormulaGrid encodingLength F)
        (sourceFormulaSignedTableFiberSupports
          encodingLength F z tableType)
        (sourceFormulaSignedTableOrdinaryMomentPolynomials
          encodingLength F z hz tableType)
        (sourceSizeParameter encodingLength F ^ 4)).card := by
  classical
  apply scaledSupport_maximalGenericGoodFiberPoints_card
    (sourceSizeParameter encodingLength F)
    (Fintype.card (sourceFormulaField encodingLength F))
    F.variableCount F.variableCount
    (sourceFormulaGrid encodingLength F)
    (sourceFormulaSignedTableFiberSupports
      encodingLength F z tableType)
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz tableType)
    (sourceSizeParameter_ge_one_hundred encodingLength F)
    (sourceFiniteField_card_lower
      (sourceSizeParameter_ge_one_hundred encodingLength F))
    (source_variableCount_le_size encodingLength F)
    (source_variableCount_le_size encodingLength F)
    (sourceFormulaGrid_card encodingLength F)
    (sourceFormulaSignedTableOrdinaryMomentPolynomials_natDegree
      encodingLength F z hz tableType)
    (integerSquaredNorm z)
  · exact sourceSignedFiberSupportAt_grid_budget F
      (sourceFormulaGrid encodingLength F) z tableType
  · exact hscaled

private theorem sourceFormulaSignedTable_genericMoments_eq_rootMoments_of_scaledNorm
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hscaled :
      10 * integerSquaredNorm z ≤
        Fintype.card (sourceFormulaField encodingLength F) *
          sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F)
    {E : Type*} [Field E]
    [Algebra (sourceFormulaField encodingLength F) E]
    [Algebra (RatFunc (sourceFormulaField encodingLength F)) E]
    [IsScalarTower (sourceFormulaField encodingLength F)
      (RatFunc (sourceFormulaField encodingLength F)) E]
    (roots : Fin (maximalGenericHankelRank
      (sourceFormulaSignedTableOrdinaryMomentPolynomials
        encodingLength F z hz tableType)
      (sourceSizeParameter encodingLength F ^ 4)) → E)
    (hroots :
      (genericMomentSupportPolynomial
        (maximalGenericHankelRank
          (sourceFormulaSignedTableOrdinaryMomentPolynomials
            encodingLength F z hz tableType)
          (sourceSizeParameter encodingLength F ^ 4))
        (sourceFormulaSignedTableOrdinaryMomentPolynomials
          encodingLength F z hz tableType)).map
          (algebraMap (RatFunc (sourceFormulaField encodingLength F)) E) =
        rootSupportPolynomial roots)
    (j : ℕ) (hj : j ≤ sourceSizeParameter encodingLength F ^ 30) :
    algebraMap (RatFunc (sourceFormulaField encodingLength F)) E
      (algebraMap
        (sourceFormulaField encodingLength F)[X]
        (RatFunc (sourceFormulaField encodingLength F))
        (sourceFormulaSignedTableOrdinaryMomentPolynomials
          encodingLength F z hz tableType j)) =
      rootMoment roots j := by
  classical
  apply sourceGenericMoments_eq_rootMoments
    (sourceFormulaGrid encodingLength F)
    (sourceFormulaSignedTableFiberSupports
      encodingLength F z tableType)
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz tableType)
    (sourceSizeParameter encodingLength F) F.variableCount
    (sourceSizeParameter_ge_one_hundred encodingLength F)
    (source_variableCount_le_size encodingLength F)
    (fun point hpoint k hk =>
      sourceFormulaSignedTableOrdinaryMomentPolynomials_eval
        encodingLength F z hz tableType point hpoint k hk)
    (sourceFormulaSignedTableOrdinaryMomentPolynomials_natDegree
      encodingLength F z hz tableType)
    (sourceFormulaSignedTable_maximalGoodFiberPoints_card_of_scaledNorm
      encodingLength F z hz hscaled tableType)
    roots hroots j hj

end

section

open GapCVP.Core

export GapCVP.Core
  (genericMomentSupportPolynomial_natDegree
   rootSupportPolynomial_finiteSupportRoots
   exists_injective_roots_of_monic_separable_splits
   mem_enumeratedRootSupport_iff
   sourceParitySupport_card_le
   genericRoot_mem_subtype_of_characteristicTwo_moments)

open scoped BigOperators symmDiff
open Polynomial Finset

private theorem sourceFormulaSignedTable_globalOrdinaryMoment_eq_clauseSubtypeSum
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (clause : Fin F.clauses.length)
    (j : ℕ) (hj : j ≤ sourceSizeParameter encodingLength F ^ 30) :
    sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz (.inl ()) j =
      ∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
        sourceFormulaSignedTableOrdinaryMomentPolynomials
          encodingLength F z hz (.inr ⟨clause, tuple⟩) j := by
  classical
  apply polynomial_eq_of_agree_on_points (sourceFormulaGrid encodingLength F)
  · refine lt_of_le_of_lt (max_le
      (sourceFormulaSignedTableOrdinaryMomentPolynomials_natDegree
        encodingLength F z hz (.inl ()) j)
      (by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro tuple _
        exact sourceFormulaSignedTableOrdinaryMomentPolynomials_natDegree
          encodingLength F z hz (.inr ⟨clause, tuple⟩) j))
      (sourceFormula_testedMomentDegree_lt_grid encodingLength F j hj)
  · intro point hpoint
    simp_rw [Polynomial.eval_finsetSum,
      sourceFormulaSignedTableOrdinaryMomentPolynomials_eval
        encodingLength F z hz _ point hpoint j hj]
    simpa only [sourceFormulaSignedTableFiberSupports, sourceSignedFiberSupportAt, hpoint,
        ↓reduceDIte,
        List.get_eq_getElem] using
        sourceSigned_globalSupportMoment_eq_clauseSubtypeSum F (sourceFormulaFieldBasis
            encodingLength F)
          (sourceFormulaGrid encodingLength F) (sourceFormulaVariablePlace encodingLength F)
          (sourceSizeParameter encodingLength F ^ 30) z hz clause ⟨point, hpoint⟩ j

/-- GapCVP reduction support. -/
def sourceFormulaGenericRank
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (tableType : sourceSATTableType F) : ℕ :=
  maximalGenericHankelRank
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz tableType)
    (sourceSizeParameter encodingLength F ^ 4)

/-- GapCVP reduction support. -/
def sourceFormulaGenericSupportPolynomial
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (tableType : sourceSATTableType F) :
    (RatFunc (sourceFormulaField encodingLength F))[X] :=
  genericMomentSupportPolynomial
    (sourceFormulaGenericRank encodingLength F z hz tableType)
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz tableType)

theorem sourceFormulaGenericRank_le
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (tableType : sourceSATTableType F) :
    sourceFormulaGenericRank encodingLength F z hz tableType ≤
      sourceSizeParameter encodingLength F ^ 4 :=
  (maximalGenericHankelRank_spec
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz tableType)
    (sourceSizeParameter encodingLength F ^ 4)).1

private theorem sourceFormulaGenericSupportPolynomial_monic
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (tableType : sourceSATTableType F) :
    (sourceFormulaGenericSupportPolynomial
      encodingLength F z hz tableType).Monic :=
  genericMomentSupportPolynomial_monic
    (sourceFormulaGenericRank encodingLength F z hz tableType)
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz tableType)

private theorem sourceFormulaGenericSupportPolynomial_separable
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F) :
    (sourceFormulaGenericSupportPolynomial
      encodingLength F z hz tableType).Separable := by
  classical
  let points := sourceFormulaGrid encodingLength F
  let supports := sourceFormulaSignedTableFiberSupports encodingLength F z tableType
  let moments := sourceFormulaSignedTableOrdinaryMomentPolynomials
    encodingLength F z hz tableType
  let rankBound := sourceSizeParameter encodingLength F ^ 4
  let momentBudget := sourceSizeParameter encodingLength F ^ 30
  obtain ⟨point, hpoint⟩ := Finset.card_pos.mp <|
    (Nat.zero_le _).trans_lt <|
      sourceFormulaSignedTable_maximalGoodFiberPoints_card_of_scaledNorm
        encodingLength F z hz hshort tableType
  have hp := (mem_maximalGenericGoodFiberPoints
    points supports moments rankBound point).mp hpoint
  have budget : 2 * rankBound ≤ momentBudget + 1 := by
    have bound := source_clause_support_lt_moment_budget
      (sourceSizeParameter_ge_one_hundred encodingLength F)
    dsimp [rankBound, momentBudget]
    omega
  have card := maximalGenericGoodFiberPoints_card_eq_rank
    points supports moments rankBound momentBudget budget
    (fun point hp j hj => sourceFormulaSignedTableOrdinaryMomentPolynomials_eval
      encodingLength F z hz tableType point hp j hj) point hpoint
  change (genericMomentSupportPolynomial
    (maximalGenericHankelRank moments rankBound) moments).Separable
  rw [← card]
  apply genericMomentSupportPolynomial_separable
    moments point (finiteSupportRoots (supports point))
    (finiteSupportRoots_injective (supports point))
  intro j hj
  exact (sourceFormulaSignedTableOrdinaryMomentPolynomials_eval
    encodingLength F z hz tableType point hp.1 j (by omega)).trans
    (rootMoment_finiteSupportRoots (supports point) j).symm

/-- GapCVP reduction support. -/
def sourceFormulaGenericSupportFamily
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z) :
    Fin (Fintype.card (sourceSATTableType F)) →
      (RatFunc (sourceFormulaField encodingLength F))[X] :=
  fun index =>
    sourceFormulaGenericSupportPolynomial
      encodingLength F z hz
      ((Fintype.equivFin (sourceSATTableType F)).symm index)

/-- GapCVP reduction support. -/
abbrev SourceFormulaCommonSeparableSplittingField
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z) :=
  CommonSeparableSplittingField
    (sourceFormulaGenericSupportFamily encodingLength F z hz)

private theorem sourceFormulaCommonSeparableSplittingField_splits
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F) :
    ((sourceFormulaGenericSupportPolynomial
      encodingLength F z hz tableType).map
      (algebraMap (RatFunc (sourceFormulaField encodingLength F))
        (SourceFormulaCommonSeparableSplittingField
          encodingLength F z hz))).Splits := by
  let family := sourceFormulaGenericSupportFamily encodingLength F z hz
  let index := Fintype.equivFin (sourceSATTableType F) tableType
  have hnonzero : ∀ i, family i ≠ 0 := by
    intro i
    exact
      (sourceFormulaGenericSupportPolynomial_monic
        encodingLength F z hz
        ((Fintype.equivFin (sourceSATTableType F)).symm i)).ne_zero
  have hseparable : ∀ i, (family i).Separable := by
    intro i
    exact sourceFormulaGenericSupportPolynomial_separable
      encodingLength F z hz hshort
      ((Fintype.equivFin (sourceSATTableType F)).symm i)
  simpa [family, index, sourceFormulaGenericSupportFamily] using
    commonSeparableSplittingField_splits family hnonzero hseparable index

private theorem sourceFormulaCommonRoots_exists
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F) :
    ∃ roots : Fin (sourceFormulaGenericRank
        encodingLength F z hz tableType) →
          SourceFormulaCommonSeparableSplittingField
            encodingLength F z hz,
      Function.Injective roots ∧
      (sourceFormulaGenericSupportPolynomial
        encodingLength F z hz tableType).map
        (algebraMap (RatFunc (sourceFormulaField encodingLength F))
          (SourceFormulaCommonSeparableSplittingField
            encodingLength F z hz)) =
        rootSupportPolynomial roots := by
  let polynomial :=
    (sourceFormulaGenericSupportPolynomial
      encodingLength F z hz tableType).map
      (algebraMap (RatFunc (sourceFormulaField encodingLength F))
        (SourceFormulaCommonSeparableSplittingField
          encodingLength F z hz))
  have hdegree : polynomial.natDegree =
      sourceFormulaGenericRank encodingLength F z hz tableType := by
    simp [polynomial, sourceFormulaGenericSupportPolynomial,
      genericMomentSupportPolynomial_natDegree]
  change ∃ roots : Fin (sourceFormulaGenericRank
    encodingLength F z hz tableType) →
      SourceFormulaCommonSeparableSplittingField encodingLength F z hz,
    Function.Injective roots ∧ polynomial = rootSupportPolynomial roots
  rw [← hdegree]
  exact exists_injective_roots_of_monic_separable_splits polynomial
    ((sourceFormulaGenericSupportPolynomial_monic
      encodingLength F z hz tableType).map _)
    (sourceFormulaGenericSupportPolynomial_separable
      encodingLength F z hz hshort tableType).map
    (sourceFormulaCommonSeparableSplittingField_splits
      encodingLength F z hz hshort tableType)

/-- GapCVP reduction support. -/
def sourceFormulaCommonRoots
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F) :
    Fin (sourceFormulaGenericRank encodingLength F z hz tableType) →
      SourceFormulaCommonSeparableSplittingField
        encodingLength F z hz :=
  Classical.choose
    (sourceFormulaCommonRoots_exists encodingLength F z hz hshort tableType)

theorem sourceFormulaCommonRoots_injective
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F) :
    Function.Injective
      (sourceFormulaCommonRoots
        encodingLength F z hz hshort tableType) :=
  (Classical.choose_spec
    (sourceFormulaCommonRoots_exists
      encodingLength F z hz hshort tableType)).1

theorem sourceFormulaCommonRoots_rootSupport
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F) :
    (sourceFormulaGenericSupportPolynomial
      encodingLength F z hz tableType).map
      (algebraMap (RatFunc (sourceFormulaField encodingLength F))
        (SourceFormulaCommonSeparableSplittingField
          encodingLength F z hz)) =
      rootSupportPolynomial
        (sourceFormulaCommonRoots
          encodingLength F z hz hshort tableType) :=
  (Classical.choose_spec
    (sourceFormulaCommonRoots_exists
      encodingLength F z hz hshort tableType)).2

/-- GapCVP reduction support. -/
def sourceFormulaCommonRootSupport
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F) :
    Finset (SourceFormulaCommonSeparableSplittingField
      encodingLength F z hz) :=
  enumeratedRootSupport
    (sourceFormulaCommonRoots encodingLength F z hz hshort tableType)

private theorem sourceFormulaCommonRootSupport_card
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F) :
    (sourceFormulaCommonRootSupport
      encodingLength F z hz hshort tableType).card =
        sourceFormulaGenericRank encodingLength F z hz tableType :=
  enumeratedRootSupport_card
    (sourceFormulaCommonRoots encodingLength F z hz hshort tableType)
    (sourceFormulaCommonRoots_injective
      encodingLength F z hz hshort tableType)

private theorem sourceFormulaGlobalGenericRank_pos
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z) :
    0 < sourceFormulaGenericRank encodingLength F z hz (.inl ()) :=
  sourceFormulaSignedTable_globalGenericRank_pos encodingLength F z hz

/-- GapCVP reduction support. -/
def sourceFormulaGlobalGenericRoot
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4) :
    SourceFormulaCommonSeparableSplittingField
      encodingLength F z hz :=
  sourceFormulaCommonRoots
    encodingLength F z hz hshort (.inl ())
    ⟨0, sourceFormulaGlobalGenericRank_pos encodingLength F z hz⟩

theorem sourceFormulaCommonRoots_moment
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (tableType : sourceSATTableType F)
    (j : ℕ) (hj : j ≤ sourceSizeParameter encodingLength F ^ 30) :
    algebraMap (RatFunc (sourceFormulaField encodingLength F))
        (SourceFormulaCommonSeparableSplittingField
          encodingLength F z hz)
      (algebraMap
        (sourceFormulaField encodingLength F)[X]
        (RatFunc (sourceFormulaField encodingLength F))
        (sourceFormulaSignedTableOrdinaryMomentPolynomials
          encodingLength F z hz tableType j)) =
      rootMoment
        (sourceFormulaCommonRoots
          encodingLength F z hz hshort tableType) j :=
  sourceFormulaSignedTable_genericMoments_eq_rootMoments_of_scaledNorm
    encodingLength F z hz hshort tableType
    (sourceFormulaCommonRoots encodingLength F z hz hshort tableType)
    (sourceFormulaCommonRoots_rootSupport
      encodingLength F z hz hshort tableType) j hj

private def sourceFormulaClauseRootSupports
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (clause : Fin F.clauses.length) :
    List (Finset (SourceFormulaCommonSeparableSplittingField
      encodingLength F z hz)) :=
  List.ofFn
    (fun index : Fin
        (Fintype.card (F.clauses.get clause).SatisfyingLocalTuple) =>
      sourceFormulaCommonRootSupport
        encodingLength F z hz hshort
        (.inr ⟨clause,
          (Fintype.equivFin
            (F.clauses.get clause).SatisfyingLocalTuple).symm index⟩))

private theorem sourceFormulaClauseRootSupports_sum_card_le
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (clause : Fin F.clauses.length) :
    ((sourceFormulaClauseRootSupports
      encodingLength F z hz hshort clause).map Finset.card).sum ≤
        Fintype.card (F.clauses.get clause).SatisfyingLocalTuple *
          sourceSizeParameter encodingLength F ^ 4 := by
  classical
  unfold sourceFormulaClauseRootSupports
  rw [List.map_ofFn, List.sum_ofFn]
  calc
    (∑ index : Fin
      (Fintype.card (F.clauses.get clause).SatisfyingLocalTuple),
      (sourceFormulaCommonRootSupport
        encodingLength F z hz hshort
        (.inr ⟨clause,
          (Fintype.equivFin
            (F.clauses.get clause).SatisfyingLocalTuple).symm index⟩)).card)
        ≤ ∑ _index : Fin
          (Fintype.card (F.clauses.get clause).SatisfyingLocalTuple),
            sourceSizeParameter encodingLength F ^ 4 := by
      apply Finset.sum_le_sum
      intro index _
      rw [sourceFormulaCommonRootSupport_card]
      exact sourceFormulaGenericRank_le encodingLength F z hz
        (.inr ⟨clause,
          (Fintype.equivFin
            (F.clauses.get clause).SatisfyingLocalTuple).symm index⟩)
    _ = Fintype.card (F.clauses.get clause).SatisfyingLocalTuple *
        sourceSizeParameter encodingLength F ^ 4 := by simp only [List.get_eq_getElem, sum_const,
            card_univ, Fintype.card_fin, smul_eq_mul]

private theorem sourceFormulaCommonGlobalRootMoment_eq_clauseSubtypeSum
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (clause : Fin F.clauses.length)
    (j : ℕ) (hj : j ≤ sourceSizeParameter encodingLength F ^ 30) :
    rootMoment
        (sourceFormulaCommonRoots
          encodingLength F z hz hshort (.inl ())) j =
      ((sourceFormulaClauseRootSupports
        encodingLength F z hz hshort clause).map
        (fun subtype => supportMoment subtype j)).sum := by
  classical
  calc
    rootMoment
        (sourceFormulaCommonRoots encodingLength F z hz hshort (.inl ())) j =
      algebraMap (RatFunc (sourceFormulaField encodingLength F))
        (SourceFormulaCommonSeparableSplittingField encodingLength F z hz)
        (algebraMap (sourceFormulaField encodingLength F)[X]
          (RatFunc (sourceFormulaField encodingLength F))
          (sourceFormulaSignedTableOrdinaryMomentPolynomials
            encodingLength F z hz (.inl ()) j)) :=
      (sourceFormulaCommonRoots_moment
        encodingLength F z hz hshort (.inl ()) j hj).symm
    _ = ∑ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
        rootMoment (sourceFormulaCommonRoots
          encodingLength F z hz hshort (.inr ⟨clause, tuple⟩)) j := by
      rw [sourceFormulaSignedTable_globalOrdinaryMoment_eq_clauseSubtypeSum
        encodingLength F z hz clause j hj]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro tuple _
      exact sourceFormulaCommonRoots_moment
        encodingLength F z hz hshort (.inr ⟨clause, tuple⟩) j hj
    _ = _ := by
      unfold sourceFormulaClauseRootSupports sourceFormulaCommonRootSupport
      rw [List.map_ofFn, List.sum_ofFn]
      rw [← Equiv.sum_comp
        (Fintype.equivFin (F.clauses.get clause).SatisfyingLocalTuple).symm]
      apply Finset.sum_congr rfl
      intro tuple _
      exact (supportMoment_enumeratedRootSupport
        (sourceFormulaCommonRoots encodingLength F z hz hshort
          (.inr ⟨clause, (Fintype.equivFin _).symm tuple⟩))
        (sourceFormulaCommonRoots_injective encodingLength F z hz hshort
          (.inr ⟨clause, (Fintype.equivFin _).symm tuple⟩)) j).symm

private theorem sourceFormulaCommonGlobalRoot_mem_satisfyingSubtype
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (clause : Fin F.clauses.length)
    (index : Fin
      (sourceFormulaGenericRank encodingLength F z hz (.inl ()))) :
    ∃ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
      sourceFormulaCommonRoots
          encodingLength F z hz hshort (.inl ()) index ∈
        sourceFormulaCommonRootSupport
          encodingLength F z hz hshort (.inr ⟨clause, tuple⟩) := by
  classical
  have rank := sourceFormulaGenericRank_le encodingLength F z hz (.inl ())
  have supports := sourceFormulaClauseRootSupports_sum_card_le
    encodingLength F z hz hshort clause
  have tuples := Nat.mul_le_mul_right
    (sourceSizeParameter encodingLength F ^ 4)
    (F.clauses.get clause).satisfyingLocalTuple_card_le_eight
  have budget := source_clause_support_lt_moment_budget
    (sourceSizeParameter_ge_one_hundred encodingLength F)
  have hbudget : sourceFormulaGenericRank encodingLength F z hz (.inl ()) +
      ((sourceFormulaClauseRootSupports
        encodingLength F z hz hshort clause).map Finset.card).sum ≤
      sourceSizeParameter encodingLength F ^ 30 := by
    omega
  obtain ⟨subtype, hsubtype, hroot⟩ :=
    genericRoot_mem_subtype_of_characteristicTwo_moments
      (sourceFormulaCommonRoots encodingLength F z hz hshort (.inl ()))
      (sourceFormulaCommonRoots_injective encodingLength F z hz hshort (.inl ()))
      (sourceFormulaClauseRootSupports encodingLength F z hz hshort clause)
      (sourceSizeParameter encodingLength F ^ 30) hbudget
      (fun j hj => sourceFormulaCommonGlobalRootMoment_eq_clauseSubtypeSum
        encodingLength F z hz hshort clause j (Nat.le_of_lt hj)) index
  change subtype ∈ List.ofFn _ at hsubtype
  obtain ⟨tupleIndex, htuple⟩ := List.mem_ofFn.mp hsubtype
  exact ⟨(Fintype.equivFin
    (F.clauses.get clause).SatisfyingLocalTuple).symm tupleIndex, by
      rw [htuple]
      exact hroot⟩

theorem sourceFormulaGlobalGenericRoot_mem_satisfyingSubtype
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (clause : Fin F.clauses.length) :
    ∃ tuple : (F.clauses.get clause).SatisfyingLocalTuple,
      sourceFormulaGlobalGenericRoot
        encodingLength F z hz hshort ∈
        sourceFormulaCommonRootSupport
          encodingLength F z hz hshort (.inr ⟨clause, tuple⟩) :=
  sourceFormulaCommonGlobalRoot_mem_satisfyingSubtype
    encodingLength F z hz hshort clause
    ⟨0, sourceFormulaGlobalGenericRank_pos encodingLength F z hz⟩

end

section

open GapCVP.Core

export GapCVP.Core
  (functionFieldExtendedValuation_ratFunc_eq_place_zpow
   discrete_place_root_term_valuations_ne
   valuation_finset_sum_ne_zero_of_distinct
   functionFieldExtendedValuation_monic_root_separation
   normalizedAffineRootPolynomial
   normalizedAffineRootPolynomial_monic
   normalizedAffineRootPolynomial_natDegree
   normalizedAffineRootPolynomial_eval₂_eq_zero
   valuation_highPower_separation_of_place_inverse_le)

open scoped BigOperators
open Polynomial Finset

variable {K E : Type*} [Field K] [Field E]
variable [Algebra (RatFunc K) E] [Algebra K[X] E]
variable [IsScalarTower K[X] (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E]
variable [Algebra.IsSeparable (RatFunc K) E]

private theorem sourceFormulaGenericSupportPolynomial_natDegree
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (tableType : sourceSATTableType F) :
    (sourceFormulaGenericSupportPolynomial
      encodingLength F z hz tableType).natDegree =
      sourceFormulaGenericRank encodingLength F z hz tableType := by
  unfold sourceFormulaGenericSupportPolynomial
  exact genericMomentSupportPolynomial_natDegree
    (sourceFormulaGenericRank encodingLength F z hz tableType)
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz tableType)

private def sourceFormulaNormalizedAffineRootPolynomial
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable) :
    (RatFunc (sourceFormulaField encodingLength F))[X] :=
  normalizedAffineRootPolynomial
    (sourceFormulaGenericSupportPolynomial
      encodingLength F z hz (.inr ⟨clause, tuple⟩))
    (algebraMap (sourceFormulaField encodingLength F)[X]
      (RatFunc (sourceFormulaField encodingLength F))
      (Polynomial.X -
        Polynomial.C
          (sourceFormulaVariablePlace encodingLength F localVar.val)))
    (algebraMap (sourceFormulaField encodingLength F)
      (RatFunc (sourceFormulaField encodingLength F))
      (sourceSATFieldBit
        (K := sourceFormulaField encodingLength F)
        (tuple.val localVar)))

private theorem sourceFormulaNormalizedAffineRootPolynomial_monic
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable) :
    (sourceFormulaNormalizedAffineRootPolynomial
      encodingLength F z hz clause tuple localVar).Monic := by
  unfold sourceFormulaNormalizedAffineRootPolynomial
  exact normalizedAffineRootPolynomial_monic
    (sourceFormulaGenericSupportPolynomial
      encodingLength F z hz (.inr ⟨clause, tuple⟩))
    (sourceFormulaGenericSupportPolynomial_monic
      encodingLength F z hz (.inr ⟨clause, tuple⟩)) _ _

private theorem sourceFormulaNormalizedAffineRootPolynomial_natDegree
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable) :
    (sourceFormulaNormalizedAffineRootPolynomial
      encodingLength F z hz clause tuple localVar).natDegree =
      sourceFormulaGenericRank
        encodingLength F z hz (.inr ⟨clause, tuple⟩) := by
  unfold sourceFormulaNormalizedAffineRootPolynomial
  rw [normalizedAffineRootPolynomial_natDegree]
  exact sourceFormulaGenericSupportPolynomial_natDegree
    encodingLength F z hz (.inr ⟨clause, tuple⟩)

private theorem sourceFormulaNormalizedAffineRootPolynomial_eval₂_eq_zero
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (index : Fin (sourceFormulaGenericRank
      encodingLength F z hz (.inr ⟨clause, tuple⟩))) :
    (sourceFormulaNormalizedAffineRootPolynomial
      encodingLength F z hz clause tuple localVar).eval₂
        (algebraMap (RatFunc (sourceFormulaField encodingLength F))
          (SourceFormulaCommonSeparableSplittingField
            encodingLength F z hz))
        ((sourceFormulaCommonRoots
            encodingLength F z hz hshort
            (.inr ⟨clause, tuple⟩) index -
          algebraMap (sourceFormulaField encodingLength F)
            (SourceFormulaCommonSeparableSplittingField
              encodingLength F z hz)
            (sourceSATFieldBit
              (K := sourceFormulaField encodingLength F)
              (tuple.val localVar))) /
          algebraMap (sourceFormulaField encodingLength F)[X]
            (SourceFormulaCommonSeparableSplittingField
              encodingLength F z hz)
            (Polynomial.X -
              Polynomial.C
                (sourceFormulaVariablePlace
                  encodingLength F localVar.val))) = 0 := by
  let k := sourceFormulaField encodingLength F
  let common := SourceFormulaCommonSeparableSplittingField
    encodingLength F z hz
  let polynomial := sourceFormulaGenericSupportPolynomial
    encodingLength F z hz (.inr ⟨clause, tuple⟩)
  let place : RatFunc k := algebraMap (Polynomial k) (RatFunc k)
    (Polynomial.X - Polynomial.C
      (sourceFormulaVariablePlace encodingLength F localVar.val))
  let bit : k := sourceSATFieldBit (K := k) (tuple.val localVar)
  let root : common := sourceFormulaCommonRoots
    encodingLength F z hz hshort (.inr ⟨clause, tuple⟩) index
  have hroot :
      polynomial.eval₂ (algebraMap (RatFunc k) common) root = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, sourceFormulaCommonRoots_rootSupport]
    exact rootSupportPolynomial_eval_root
      (sourceFormulaCommonRoots
        encodingLength F z hz hshort (.inr ⟨clause, tuple⟩)) index
  have hnormalized := normalizedAffineRootPolynomial_eval₂_eq_zero
    polynomial place (algebraMap k (RatFunc k) bit) root
    (algebraMap (RatFunc k) common) hroot
  rw [← IsScalarTower.algebraMap_apply k (RatFunc k) common] at hnormalized
  dsimp [place] at hnormalized
  rw [← IsScalarTower.algebraMap_apply
    (Polynomial k) (RatFunc k) common] at hnormalized
  exact hnormalized

private theorem sourceFormulaShiftedCommonRoot_separation
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (index : Fin (sourceFormulaGenericRank
      encodingLength F z hz (.inr ⟨clause, tuple⟩)))
    (hlarge :
      1 <
        functionFieldExtendedValuation
          (K := sourceFormulaField encodingLength F)
          (E := SourceFormulaCommonSeparableSplittingField
            encodingLength F z hz)
          (sourceFormulaVariablePlace
            encodingLength F localVar.val)
          ((sourceFormulaCommonRoots
              encodingLength F z hz hshort
              (.inr ⟨clause, tuple⟩) index -
            algebraMap (sourceFormulaField encodingLength F)
              (SourceFormulaCommonSeparableSplittingField
                encodingLength F z hz)
              (sourceSATFieldBit
                (K := sourceFormulaField encodingLength F)
                (tuple.val localVar))) /
            algebraMap (sourceFormulaField encodingLength F)[X]
              (SourceFormulaCommonSeparableSplittingField
                encodingLength F z hz)
              (Polynomial.X -
                Polynomial.C
                  (sourceFormulaVariablePlace
                    encodingLength F localVar.val)))) :
    (functionFieldExtendedValuation
      (K := sourceFormulaField encodingLength F)
      (E := SourceFormulaCommonSeparableSplittingField
        encodingLength F z hz)
      (sourceFormulaVariablePlace encodingLength F localVar.val)
      (algebraMap (sourceFormulaField encodingLength F)[X]
        (SourceFormulaCommonSeparableSplittingField
          encodingLength F z hz)
        (Polynomial.X -
          Polynomial.C
            (sourceFormulaVariablePlace
              encodingLength F localVar.val))))⁻¹ ≤
      (functionFieldExtendedValuation
        (K := sourceFormulaField encodingLength F)
        (E := SourceFormulaCommonSeparableSplittingField
          encodingLength F z hz)
        (sourceFormulaVariablePlace
          encodingLength F localVar.val)
        ((sourceFormulaCommonRoots
            encodingLength F z hz hshort
            (.inr ⟨clause, tuple⟩) index -
          algebraMap (sourceFormulaField encodingLength F)
            (SourceFormulaCommonSeparableSplittingField
              encodingLength F z hz)
            (sourceSATFieldBit
              (K := sourceFormulaField encodingLength F)
              (tuple.val localVar))) /
          algebraMap (sourceFormulaField encodingLength F)[X]
            (SourceFormulaCommonSeparableSplittingField
              encodingLength F z hz)
            (Polynomial.X -
              Polynomial.C
                (sourceFormulaVariablePlace
                  encodingLength F localVar.val)))) ^
        sourceFormulaGenericRank
          encodingLength F z hz (.inr ⟨clause, tuple⟩) := by
  simpa only [sourceFormulaNormalizedAffineRootPolynomial_natDegree] using
    functionFieldExtendedValuation_monic_root_separation
      (sourceFormulaVariablePlace encodingLength F localVar.val)
      (sourceFormulaNormalizedAffineRootPolynomial
        encodingLength F z hz clause tuple localVar)
      (sourceFormulaNormalizedAffineRootPolynomial_monic
        encodingLength F z hz clause tuple localVar) _
      (sourceFormulaNormalizedAffineRootPolynomial_eval₂_eq_zero
        encodingLength F z hz hshort clause tuple localVar index)
      hlarge

theorem sourceFormulaShiftedCommonRoot_highPower_separation
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    (exponent : ℕ)
    (index : Fin (sourceFormulaGenericRank
      encodingLength F z hz (.inr ⟨clause, tuple⟩)))
    (hlarge :
      1 <
        functionFieldExtendedValuation
          (K := sourceFormulaField encodingLength F)
          (E := SourceFormulaCommonSeparableSplittingField
            encodingLength F z hz)
          (sourceFormulaVariablePlace encodingLength F localVar.val)
          ((sourceFormulaCommonRoots
              encodingLength F z hz hshort
              (.inr ⟨clause, tuple⟩) index -
            algebraMap (sourceFormulaField encodingLength F)
              (SourceFormulaCommonSeparableSplittingField
                encodingLength F z hz)
              (sourceSATFieldBit
                (K := sourceFormulaField encodingLength F)
                (tuple.val localVar))) /
            algebraMap (sourceFormulaField encodingLength F)[X]
              (SourceFormulaCommonSeparableSplittingField
                encodingLength F z hz)
              (Polynomial.X -
                Polynomial.C
                  (sourceFormulaVariablePlace
                    encodingLength F localVar.val)))) :
    (functionFieldExtendedValuation
      (K := sourceFormulaField encodingLength F)
      (E := SourceFormulaCommonSeparableSplittingField
        encodingLength F z hz)
      (sourceFormulaVariablePlace encodingLength F localVar.val)
      (algebraMap (sourceFormulaField encodingLength F)[X]
        (SourceFormulaCommonSeparableSplittingField
          encodingLength F z hz)
        (Polynomial.X -
          Polynomial.C
            (sourceFormulaVariablePlace
              encodingLength F localVar.val))) ^ exponent)⁻¹ <
      functionFieldExtendedValuation
        (K := sourceFormulaField encodingLength F)
        (E := SourceFormulaCommonSeparableSplittingField
          encodingLength F z hz)
        (sourceFormulaVariablePlace encodingLength F localVar.val)
        (((sourceFormulaCommonRoots
            encodingLength F z hz hshort
            (.inr ⟨clause, tuple⟩) index -
          algebraMap (sourceFormulaField encodingLength F)
            (SourceFormulaCommonSeparableSplittingField
              encodingLength F z hz)
            (sourceSATFieldBit
              (K := sourceFormulaField encodingLength F)
              (tuple.val localVar))) /
          algebraMap (sourceFormulaField encodingLength F)[X]
            (SourceFormulaCommonSeparableSplittingField
              encodingLength F z hz)
            (Polynomial.X -
              Polynomial.C
                (sourceFormulaVariablePlace
                  encodingLength F localVar.val))) ^
          (sourceFormulaGenericRank
            encodingLength F z hz (.inr ⟨clause, tuple⟩) *
              exponent + 1)) := by
  exact valuation_highPower_separation_of_place_inverse_le _ _ _ _
    exponent hlarge
    (sourceFormulaShiftedCommonRoot_separation
      encodingLength F z hz hshort clause tuple localVar index hlarge)

end

section

open GapCVP.Core

/-- GapCVP reduction support. -/
def sourceValuationInverseExponent (d h : ℕ) : ℕ :=
  d * h * h + (d * h * (h - 1) + 1) * h * h

private theorem sourceValuationInverseExponent_le_four
    {N d h : ℕ} (hN : 100 ≤ N)
    (hd : d ≤ N) (hh : h ≤ N ^ 4) :
    sourceValuationInverseExponent d h ≤ 4 * N ^ 17 := by
  have hcore : d * h * h ≤ N ^ 9 := by
    calc
      d * h * h ≤ N * (N ^ 4) * (N ^ 4) := by gcongr
      _ = N ^ 9 := by
        rw [show (9 : ℕ) = 1 + 4 + 4 by norm_num,
          pow_add, pow_add, pow_one]
  have hcoreSeventeen : d * h * h ≤ N ^ 17 := by
    exact hcore.trans
      (Nat.pow_le_pow_right (by omega) (by norm_num : 9 ≤ 17))
  have hfactor : d * h * (h - 1) + 1 ≤ 2 * N ^ 9 := by
    have hsub : d * h * (h - 1) ≤ d * h * h :=
      Nat.mul_le_mul_left (d * h) (Nat.sub_le h 1)
    have hpositive : 1 ≤ N ^ 9 := by
      have : 0 < N ^ 9 := pow_pos (by omega) 9
      omega
    omega
  have hadjugate :
      (d * h * (h - 1) + 1) * h * h ≤ 2 * N ^ 17 := by
    calc
      (d * h * (h - 1) + 1) * h * h ≤
          (2 * N ^ 9) * (N ^ 4) * (N ^ 4) := by gcongr
      _ = 2 * N ^ 17 := by
        rw [show (17 : ℕ) = 9 + 4 + 4 by norm_num,
          pow_add, pow_add]
        ring
  unfold sourceValuationInverseExponent
  omega

private theorem sourceValuationInverseExponent_high_index_lt_budget
    {N d h : ℕ} (hN : 100 ≤ N)
    (hd : d ≤ N) (hh : h ≤ N ^ 4) :
    h * sourceValuationInverseExponent d h + h < N ^ 30 := by
  apply source_valuation_index_lt_moment_budget hN hh
  exact sourceValuationInverseExponent_le_four hN hd hh

private theorem sourceValuationInverseExponent_shifted_index_le_budget
    {N d h : ℕ} (hN : 100 ≤ N)
    (hd : d ≤ N) (hh : h ≤ N ^ 4) (row : Fin h) :
    h * sourceValuationInverseExponent d h + 1 + row.val ≤ N ^ 30 := by
  have hlast :=
    sourceValuationInverseExponent_high_index_lt_budget hN hd hh
  have hrow := row.isLt
  omega

/-- GapCVP reduction support. -/
def sourceFormulaValuationInverseExponent
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (tableType : sourceSATTableType F) : ℕ :=
  sourceValuationInverseExponent F.variableCount
    (sourceFormulaGenericRank encodingLength F z hz tableType)

theorem sourceFormulaValuationInverseExponent_shifted_index_le_budget
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (tableType : sourceSATTableType F)
    (row : Fin (sourceFormulaGenericRank
      encodingLength F z hz tableType)) :
    sourceFormulaGenericRank encodingLength F z hz tableType *
          sourceFormulaValuationInverseExponent
            encodingLength F z hz tableType + 1 + row.val ≤
      sourceSizeParameter encodingLength F ^ 30 :=
  sourceValuationInverseExponent_shifted_index_le_budget
    (sourceSizeParameter_ge_one_hundred encodingLength F)
    (source_variableCount_le_size encodingLength F)
    (sourceFormulaGenericRank_le encodingLength F z hz tableType) row

end

section

open GapCVP.Core

open scoped BigOperators
open Polynomial Finset

theorem sourceFormulaSignedTable_shiftedGenericRootMoment
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4)
    (clause : Fin F.clauses.length)
    (tuple : (F.clauses.get clause).SatisfyingLocalTuple)
    (localVar : (F.clauses.get clause).LocalVariable)
    {E : Type*} [Field E]
    [Algebra (sourceFormulaField encodingLength F) E]
    [Algebra (sourceFormulaField encodingLength F)[X] E]
    [Algebra (RatFunc (sourceFormulaField encodingLength F)) E]
    [IsScalarTower (sourceFormulaField encodingLength F)
      (sourceFormulaField encodingLength F)[X] E]
    [IsScalarTower (sourceFormulaField encodingLength F)
      (RatFunc (sourceFormulaField encodingLength F)) E]
    [IsScalarTower (sourceFormulaField encodingLength F)[X]
      (RatFunc (sourceFormulaField encodingLength F)) E]
    (roots : Fin (maximalGenericHankelRank
      (sourceFormulaSignedTableOrdinaryMomentPolynomials
        encodingLength F z hz (.inr ⟨clause, tuple⟩))
      (sourceSizeParameter encodingLength F ^ 4)) → E)
    (hinjective : Function.Injective roots)
    (hroots :
      (genericMomentSupportPolynomial
        (maximalGenericHankelRank
          (sourceFormulaSignedTableOrdinaryMomentPolynomials
            encodingLength F z hz (.inr ⟨clause, tuple⟩))
          (sourceSizeParameter encodingLength F ^ 4))
        (sourceFormulaSignedTableOrdinaryMomentPolynomials
          encodingLength F z hz (.inr ⟨clause, tuple⟩))).map
          (algebraMap (RatFunc (sourceFormulaField encodingLength F)) E) =
        rootSupportPolynomial roots)
    (j : ℕ) (hj : j ≤ sourceSizeParameter encodingLength F ^ 30) :
    rootMoment
      (fun index =>
        (roots index - algebraMap (sourceFormulaField encodingLength F) E
          (sourceSATFieldBit
            (K := sourceFormulaField encodingLength F)
            (tuple.val localVar))) /
          algebraMap (sourceFormulaField encodingLength F)[X] E
            (Polynomial.X - Polynomial.C
              (sourceFormulaVariablePlace encodingLength F localVar.val))) j =
      algebraMap (sourceFormulaField encodingLength F)[X] E
        (sourceFormulaSignedTableShiftedMomentPolynomials
          encodingLength F z hz clause tuple localVar j) := by
  classical
  let k := sourceFormulaField encodingLength F
  let place := sourceFormulaVariablePlace encodingLength F localVar.val
  apply shiftedGenericRootMoment_eq_mappedShiftedPolynomial
    (sourceFormulaSignedTableOrdinaryMomentPolynomials
      encodingLength F z hz (.inr ⟨clause, tuple⟩))
    (sourceFormulaSignedTableShiftedMomentPolynomials
      encodingLength F z hz clause tuple localVar j)
    place (sourceSATFieldBit (K := k) (tuple.val localVar)) j roots hinjective
    ((map_ne_zero_iff (algebraMap k[X] E)
      (functionFieldPolynomial_algebraMap_injective (K := k) (E := E))).mpr
      (Polynomial.X_sub_C_ne_zero place))
  · intro l hl
    rw [IsScalarTower.algebraMap_apply k[X] (RatFunc k) E]
    exact sourceFormulaSignedTable_genericMoments_eq_rootMoments_of_scaledNorm
      encodingLength F z hz hshort (.inr ⟨clause, tuple⟩)
      roots hroots l (hl.trans hj)
  · exact sourceFormulaSignedTable_shiftedMomentPolynomial_identity
      encodingLength F z hz clause tuple localVar j hj

end

end Factor400BinaryConstructiveSourcePlaces


end GapCVP

end
