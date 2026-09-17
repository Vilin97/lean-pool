/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part09

/-! # GapCVP proof, part 10 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace SourceFactor400BinaryConstructionABounds

open scoped BigOperators

/-- GapCVP reduction support. -/
noncomputable def gapFactor400 (dimension : ℕ) : ℝ :=
  (dimension : ℝ) ^ ((1 : ℝ) / 400)

theorem gapFactor400_sq (dimension : ℕ) :
    gapFactor400 dimension ^ 2 =
      (dimension : ℝ) ^ ((1 : ℝ) / 200) := by
  unfold gapFactor400
  rw [← Real.rpow_mul_natCast (by positivity)]
  norm_num

private theorem source_dimension_le_power402
    {N dimension : ℕ}
    (hN : 100 ≤ N)
    (hdimension : dimension ≤ 40 * N ^ 401) :
    dimension ≤ N ^ 402 := by
  have hforty : 40 ≤ N := by omega
  calc
    dimension ≤ 40 * N ^ 401 := hdimension
    _ ≤ N * N ^ 401 := Nat.mul_le_mul_right _ hforty
    _ = N ^ 402 := by ring

private theorem source_gapFactor400_sq_le_power
    {N dimension : ℕ}
    (hN : 100 ≤ N)
    (hdimension : dimension ≤ 40 * N ^ 401) :
    gapFactor400 dimension ^ 2 ≤
      (N : ℝ) ^ ((201 : ℝ) / 100) := by
  rw [gapFactor400_sq]
  have hpower := source_dimension_le_power402 hN hdimension
  have hcast : (dimension : ℝ) ≤ ((N ^ 402 : ℕ) : ℝ) := by
    exact_mod_cast hpower
  calc
    (dimension : ℝ) ^ ((1 : ℝ) / 200) ≤
        ((N ^ 402 : ℕ) : ℝ) ^ ((1 : ℝ) / 200) := by
      apply Real.rpow_le_rpow (by positivity) hcast
      norm_num
    _ = (N : ℝ) ^ ((201 : ℝ) / 100) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
      norm_num

private theorem eighty_lt_source_power
    {N : ℕ} (hN : 100 ≤ N) :
    (80 : ℝ) < (N : ℝ) ^ ((99 : ℝ) / 100) := by
  have hnumeric : (80 : ℝ) ^ 100 < (100 : ℝ) ^ 99 := by
    norm_num
  have hroot :
      ((80 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) <
        ((100 : ℝ) ^ 99) ^ ((1 : ℝ) / 100) := by
    apply Real.rpow_lt_rpow (by positivity) hnumeric
    norm_num
  have hleft :
      ((80 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 80 := by
    rw [← Real.rpow_natCast_mul (by positivity)]
    norm_num
  have hright :
      ((100 : ℝ) ^ 99) ^ ((1 : ℝ) / 100) =
        (100 : ℝ) ^ ((99 : ℝ) / 100) := by
    rw [← Real.rpow_natCast_mul (by positivity)]
    norm_num
  rw [hleft, hright] at hroot
  have hcast : (100 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  exact hroot.trans_le
    (Real.rpow_le_rpow (by norm_num) hcast (by norm_num))

private theorem source_power_margin
    {N : ℕ} (hN : 100 ≤ N) :
    (80 : ℝ) * (N : ℝ) ^ ((301 : ℝ) / 100) <
      (N : ℝ) ^ 4 := by
  have hNpositive : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  calc
    (80 : ℝ) * (N : ℝ) ^ ((301 : ℝ) / 100) <
        (N : ℝ) ^ ((99 : ℝ) / 100) *
          (N : ℝ) ^ ((301 : ℝ) / 100) := by
      exact mul_lt_mul_of_pos_right
        (eighty_lt_source_power hN)
        (Real.rpow_pos_of_pos hNpositive _)
    _ = (N : ℝ) ^ 4 := by
      rw [← Real.rpow_add hNpositive]
      norm_num

private theorem source_gapFactor400_eighty_mul_size_lt_fourth_power
    {N dimension : ℕ}
    (hN : 100 ≤ N)
    (hdimension : dimension ≤ 40 * N ^ 401) :
    (80 : ℝ) * gapFactor400 dimension ^ 2 * (N : ℝ) <
      (N : ℝ) ^ 4 := by
  have hfactor := source_gapFactor400_sq_le_power hN hdimension
  have hNpositive : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hjoin :
      (N : ℝ) ^ ((201 : ℝ) / 100) * (N : ℝ) =
        (N : ℝ) ^ ((301 : ℝ) / 100) := by
    conv_lhs =>
      rhs
      rw [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hNpositive]
    norm_num
  calc
    (80 : ℝ) * gapFactor400 dimension ^ 2 * (N : ℝ) ≤
        80 * (N : ℝ) ^ ((201 : ℝ) / 100) * (N : ℝ) := by
      gcongr
    _ = 80 * (N : ℝ) ^ ((301 : ℝ) / 100) := by
      rw [← hjoin]
      ring
    _ < (N : ℝ) ^ 4 := source_power_margin hN

end SourceFactor400BinaryConstructionABounds

namespace Factor400BinaryConstructiveSourcePlaces

section

open GapCVP.Core GapCVP.SourceFactor400BinaryConstructionABounds

private theorem sourceFormulaCompletenessRadius_squared_le_eight
    (encodingLength : ℕ) (F : Formula) :
    ((sourceOneHotCompletenessRadius F
      (sourceFormulaGrid encodingLength F) : ℚ) : ℝ) ^ 2 ≤
      ((8 * Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F : ℕ) : ℝ) := by
  refine (sourceOneHotCompletenessRadius_squared_le_four_weight F
    (sourceFormulaGrid encodingLength F)
    (sourceFormulaGrid_card_pos encodingLength F)).trans ?_
  exact_mod_cast source_oneHot_weight_four_mul_le
    (sourceSizeParameter_ge_one_hundred encodingLength F)
    (source_clauseCount_le_size encodingLength F)
    (Finset.card_le_card (Finset.subset_univ
      (sourceFormulaGrid encodingLength F)))

private theorem sourceFormula_radius_squared_le_eight_field_mul_size
    (encodingLength : ℕ) (F : GapCVP.Core.Formula) :
    ((GapCVP.Core.sourceOneHotCompletenessRadius F
      (sourceFormulaGrid encodingLength F) : ℚ) : ℝ) ^ 2 ≤
      ((8 * Fintype.card
        (GapCVP.Core.sourceFormulaField encodingLength F) *
        GapCVP.Core.sourceSizeParameter encodingLength F : ℕ) : ℝ) := by
  exact sourceFormulaCompletenessRadius_squared_le_eight
    encodingLength F

theorem sourceFormula_gapFactor400_eighty_mul_size_lt_fourth_power
    (encodingLength : ℕ) (F : GapCVP.Core.Formula) :
    (80 : ℝ) *
        GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
          (sourceFormulaDimension encodingLength F) ^ 2 *
        (GapCVP.Core.sourceSizeParameter encodingLength F : ℝ) <
      (GapCVP.Core.sourceSizeParameter encodingLength F : ℝ) ^ 4 := by
  exact source_gapFactor400_eighty_mul_size_lt_fourth_power
    (GapCVP.Core.sourceSizeParameter_ge_one_hundred encodingLength F)
    (sourceFormulaDimension_le encodingLength F)

private theorem sourceFormula_ten_mul_integerSquaredNorm_lt_field_mul_fourth_power_of_short
    (encodingLength : ℕ) (F : GapCVP.Core.Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hshort : (GapCVP.Core.integerSquaredNorm z : ℝ) ≤
      (GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
          (sourceFormulaDimension encodingLength F) *
        ((GapCVP.Core.sourceOneHotCompletenessRadius F
          (sourceFormulaGrid encodingLength F) : ℚ) : ℝ)) ^ 2) :
    10 * GapCVP.Core.integerSquaredNorm z <
      Fintype.card (GapCVP.Core.sourceFormulaField encodingLength F) *
        GapCVP.Core.sourceSizeParameter encodingLength F ^ 4 := by
  let N := sourceSizeParameter encodingLength F
  let q := Fintype.card (sourceFormulaField encodingLength F)
  let factor := GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
    (sourceFormulaDimension encodingLength F)
  let radius := ((sourceOneHotCompletenessRadius F
    (sourceFormulaGrid encodingLength F) : ℚ) : ℝ)
  have hnorm : (integerSquaredNorm z : ℝ) ≤
      factor ^ 2 * ((8 * q * N : ℕ) : ℝ) := by
    calc
      (integerSquaredNorm z : ℝ) ≤ (factor * radius) ^ 2 := hshort
      _ = factor ^ 2 * radius ^ 2 := by ring
      _ ≤ factor ^ 2 * ((8 * q * N : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left
          (sourceFormula_radius_squared_le_eight_field_mul_size
            encodingLength F) (sq_nonneg factor)
  have hq : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨(0 : sourceFormulaField encodingLength F)⟩
  have hstrict : ((10 * integerSquaredNorm z : ℕ) : ℝ) <
      ((q * N ^ 4 : ℕ) : ℝ) := by
    calc
      ((10 * integerSquaredNorm z : ℕ) : ℝ) ≤
          (80 * factor ^ 2 * (N : ℝ)) * (q : ℝ) := by
        push_cast at hnorm ⊢
        linarith
      _ < (N : ℝ) ^ 4 * (q : ℝ) :=
        mul_lt_mul_of_pos_right
          (sourceFormula_gapFactor400_eighty_mul_size_lt_fourth_power
            encodingLength F) hq
      _ = ((q * N ^ 4 : ℕ) : ℝ) := by push_cast; ring
  exact_mod_cast hstrict

end

section

open GapCVP.Core
open scoped BigOperators
open Polynomial Finset Matrix

private theorem sourceFormulaShiftedCommonRoot_integral
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
    functionFieldExtendedValuation
      (K := sourceFormulaField encodingLength F)
      (E := SourceFormulaCommonSeparableSplittingField
        encodingLength F z hz)
      (sourceFormulaVariablePlace encodingLength F localVar.val)
      ((sourceFormulaCommonRoots
          encodingLength F z hz hshort (.inr ⟨clause, tuple⟩) index -
        algebraMap (sourceFormulaField encodingLength F)
          (SourceFormulaCommonSeparableSplittingField
            encodingLength F z hz)
          (sourceSATFieldBit
            (K := sourceFormulaField encodingLength F)
            (tuple.val localVar))) /
        algebraMap (sourceFormulaField encodingLength F)[X]
          (SourceFormulaCommonSeparableSplittingField
            encodingLength F z hz)
          (Polynomial.X - Polynomial.C
            (sourceFormulaVariablePlace
              encodingLength F localVar.val))) ≤ 1 := by
  classical
  let k := sourceFormulaField encodingLength F
  let E := SourceFormulaCommonSeparableSplittingField encodingLength F z hz
  let : IsScalarTower k k[X] E := IsScalarTower.of_algebraMap_eq fun x => by
    calc
      algebraMap k E x = algebraMap (RatFunc k) E
          (algebraMap k (RatFunc k) x) :=
        IsScalarTower.algebraMap_apply k (RatFunc k) E x
      _ = algebraMap (RatFunc k) E
          (algebraMap k[X] (RatFunc k) (algebraMap k k[X] x)) := by
        rw [← IsScalarTower.algebraMap_apply k k[X] (RatFunc k) x]
      _ = algebraMap k[X] E (algebraMap k k[X] x) :=
        (IsScalarTower.algebraMap_apply k[X] (RatFunc k) E _).symm
  let type : sourceSATTableType F := .inr ⟨clause, tuple⟩
  let moments := sourceFormulaSignedTableOrdinaryMomentPolynomials
    encodingLength F z hz type
  let h := sourceFormulaGenericRank encodingLength F z hz type
  let roots : Fin h → E := sourceFormulaCommonRoots
    encodingLength F z hz hshort type
  let a := sourceFormulaVariablePlace encodingLength F localVar.val
  let bit := sourceSATFieldBit (K := k) (tuple.val localVar)
  let place : E := algebraMap k[X] E (Polynomial.X - Polynomial.C a)
  let valuation := functionFieldExtendedValuation (K := k) (E := E) a
  let p := valuation place
  let shifted : Fin h → E := fun i => (roots i - algebraMap k E bit) / place
  let U := sourceFormulaValuationInverseExponent encodingLength F z hz type
  have place_ne : place ≠ 0 :=
    (map_ne_zero_iff (algebraMap k[X] E)
      (functionFieldPolynomial_algebraMap_injective
        (K := k) (E := E))).mpr (Polynomial.X_sub_C_ne_zero a)
  have p_pos : 0 < p := (Valuation.pos_iff valuation).mpr place_ne
  have p_le : p ≤ 1 := le_of_lt
    (functionFieldExtendedValuation_place_lt_one (K := k) (E := E) a)
  have roots_inj := sourceFormulaCommonRoots_injective
    encodingLength F z hz hshort type
  have shifted_inj : Function.Injective shifted := fun i j equal =>
    roots_inj (sub_left_injective ((div_left_inj' place_ne).mp equal))
  have denominator := (maximalGenericHankelRank_spec
    moments (sourceSizeParameter encodingLength F ^ 4)).2
  have support := sourceFormulaCommonRoots_rootSupport
    encodingLength F z hz hshort type
  have degrees : ∀ j : ℕ, (moments j).natDegree ≤ F.variableCount * j :=
    sourceFormulaSignedTableOrdinaryMomentPolynomials_natDegree
      encodingLength F z hz type
  have small : ∀ j : ℕ, j < 2 * h →
      algebraMap k[X] E (moments j) = rootMoment roots j := by
    intro j bound
    have rank := sourceFormulaGenericRank_le encodingLength F z hz type
    have support_bound := source_clause_support_lt_moment_budget
      (sourceSizeParameter_ge_one_hundred encodingLength F)
    have budget : j ≤ sourceSizeParameter encodingLength F ^ 30 := by
      dsimp [h] at bound
      omega
    rw [IsScalarTower.algebraMap_apply k[X] (RatFunc k) E]
    exact sourceFormulaCommonRoots_moment
      encodingLength F z hz hshort type j budget
  apply valuation_roots_integral_of_shifted_moments
    valuation shifted shifted_inj (p ^ U)⁻¹ (h * U + 1) _ _ _ index
  · intro i j
    have bound := valuation_inverseTransposeVandermonde_le_place_inv_pow
      valuation shifted p p_pos p_le
      (F.variableCount * h * (h - 1) + 1) (F.variableCount * h * h)
      (fun i => functionFieldExtendedValuation_shiftedGenericRoot_le_place_inv_pow
        moments F.variableCount h degrees denominator roots support a bit i)
      (functionFieldExtendedValuation_shiftedVandermonde_det_inv_le_place_inv_pow
        a moments F.variableCount roots (algebraMap k E bit)
        small degrees denominator) i j
    simpa [U, sourceFormulaValuationInverseExponent,
      sourceValuationInverseExponent, h] using bound
  · intro r
    have budget := sourceFormulaValuationInverseExponent_shifted_index_le_budget
      encodingLength F z hz type r
    have moment := sourceFormulaSignedTable_shiftedGenericRootMoment
      encodingLength F z hz hshort clause tuple localVar roots roots_inj support
      (h * U + 1 + r.val) budget
    change valuation (rootMoment
      (fun i => (roots i - algebraMap k E bit) / place)
      (h * U + 1 + r.val)) ≤ 1
    calc
      valuation (rootMoment
          (fun i => (roots i - algebraMap k E bit) / place)
          (h * U + 1 + r.val)) =
        valuation (algebraMap k[X] E
          (sourceFormulaSignedTableShiftedMomentPolynomials
            encodingLength F z hz clause tuple localVar
            (h * U + 1 + r.val))) := congrArg valuation moment
      _ ≤ 1 := functionFieldExtendedValuation_polynomial_le_one a _
  · intro i large
    exact sourceFormulaShiftedCommonRoot_highPower_separation
      encodingLength F z hz hshort clause tuple localVar U i large

private theorem sourceFormulaCommonRoot_close_to_localBit
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
    functionFieldExtendedValuation
      (K := sourceFormulaField encodingLength F)
      (E := SourceFormulaCommonSeparableSplittingField
        encodingLength F z hz)
      (sourceFormulaVariablePlace encodingLength F localVar.val)
      (sourceFormulaCommonRoots
          encodingLength F z hz hshort (.inr ⟨clause, tuple⟩) index -
        algebraMap (sourceFormulaField encodingLength F)
          (SourceFormulaCommonSeparableSplittingField
            encodingLength F z hz)
          (sourceSATFieldBit
            (K := sourceFormulaField encodingLength F)
            (tuple.val localVar))) < 1 := by
  classical
  let k := sourceFormulaField encodingLength F
  let E := SourceFormulaCommonSeparableSplittingField encodingLength F z hz
  let a := sourceFormulaVariablePlace encodingLength F localVar.val
  let place : E := algebraMap k[X] E (Polynomial.X - Polynomial.C a)
  let v := functionFieldExtendedValuation (K := k) (E := E) a
  let difference : E := sourceFormulaCommonRoots
    encodingLength F z hz hshort (.inr ⟨clause, tuple⟩) index -
    algebraMap k E (sourceSATFieldBit (K := k) (tuple.val localVar))
  have small : v place < 1 :=
    functionFieldExtendedValuation_place_lt_one (K := k) (E := E) a
  change v difference < 1
  calc
    v difference = v (difference / place) * v place := by
      rw [← v.map_mul, div_mul_cancel₀ difference]
      exact (map_ne_zero_iff (algebraMap k[X] E)
        (functionFieldPolynomial_algebraMap_injective (K := k) (E := E))).mpr
        (Polynomial.X_sub_C_ne_zero a)
    _ ≤ 1 * v place := mul_le_mul_of_nonneg_right
      (sourceFormulaShiftedCommonRoot_integral
        encodingLength F z hz hshort clause tuple localVar index) zero_le
    _ < 1 := by simpa only [one_mul] using small

theorem sourceFormula_satisfiable_of_short_signed_solution
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : 10 * integerSquaredNorm z ≤
      Fintype.card (sourceFormulaField encodingLength F) *
        sourceSizeParameter encodingLength F ^ 4) :
    F.Satisfiable := by
  classical
  let k := sourceFormulaField encodingLength F
  let E := SourceFormulaCommonSeparableSplittingField encodingLength F z hz
  let root : E := sourceFormulaGlobalGenericRoot encodingLength F z hz hshort
  let selected : (clause : Fin F.clauses.length) →
      (F.clauses.get clause).SatisfyingLocalTuple := fun clause =>
    Classical.choose (sourceFormulaGlobalGenericRoot_mem_satisfyingSubtype
      encodingLength F z hz hshort clause)
  have hselected : ∀ clause : Fin F.clauses.length,
      root ∈ sourceFormulaCommonRootSupport
        encodingLength F z hz hshort (.inr ⟨clause, selected clause⟩) :=
    fun clause => Classical.choose_spec
      (sourceFormulaGlobalGenericRoot_mem_satisfyingSubtype
        encodingLength F z hz hshort clause)
  let assignment : Fin F.clauses.length → Fin F.variableCount → Bool :=
    fun clause varIndex => if h : varIndex ∈ (F.clauses.get clause).variableSet
      then (selected clause).val ⟨varIndex, h⟩ else false
  let valuation : Fin F.variableCount → Valuation E (WithZero (Multiplicative ℤ)) :=
    fun varIndex => functionFieldExtendedValuation (K := k) (E := E)
      (sourceFormulaVariablePlace encodingLength F varIndex)
  apply satisfiable_of_common_valuation_root F valuation root assignment
  · intro clause
    have satisfied := (selected clause).property
    simp only [GapCVP.Core.Clause.LocalSatisfied, GapCVP.Core.Clause.Satisfied,
      decide_eq_true_eq] at satisfied ⊢
    obtain ⟨literal, hliteral, hvalue⟩ := satisfied
    have hmem : literal.variableIndex ∈ (F.clauses.get clause).variableSet :=
      Finset.mem_image_of_mem (fun l : GapCVP.Core.Literal F.variableCount =>
        l.variableIndex) hliteral
    refine ⟨literal, hliteral, ?_⟩
    dsimp [assignment]
    split
    next => exact hvalue
    next h => exact (h hmem).elim
  · intro clause literal hliteral
    let tuple := selected clause
    have hmem : literal.variableIndex ∈ (F.clauses.get clause).variableSet :=
      Finset.mem_image_of_mem (fun l : GapCVP.Core.Literal F.variableCount =>
        l.variableIndex) hliteral
    let localVar : (F.clauses.get clause).LocalVariable :=
      ⟨literal.variableIndex, hmem⟩
    obtain ⟨index, hindex⟩ :=
      (mem_enumeratedRootSupport_iff
        (sourceFormulaCommonRoots
          encodingLength F z hz hshort (.inr ⟨clause, tuple⟩)) root).mp
        (hselected clause)
    have hclose := sourceFormulaCommonRoot_close_to_localBit
      encodingLength F z hz hshort clause tuple localVar index
    rw [hindex] at hclose
    change functionFieldExtendedValuation (K := k) (E := E)
      (sourceFormulaVariablePlace encodingLength F literal.variableIndex)
      (root - bitInField (E := E) (assignment clause literal.variableIndex)) < 1
    have hlocal : assignment clause literal.variableIndex = tuple.val localVar := by
      dsimp [assignment]
      split
      next => rfl
      next h => exact (h hmem).elim
    rw [hlocal]
    cases hbit : tuple.val localVar <;>
      simpa only [hbit, sourceSATFieldBit, bitInField, localVar,
        Bool.false_eq_true, ↓reduceIte, map_zero, map_one] using hclose

private theorem sourceFormula_satisfiable_of_factor400_short_signed_solution
    (encodingLength : ℕ) (F : Formula)
    (z : Fin (sourceFormulaDimension encodingLength F) → ℤ)
    (hz : (sourceFormulaBinarySystem encodingLength F).Solves z)
    (hshort : (integerSquaredNorm z : ℝ) ≤
      (GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
          (sourceFormulaDimension encodingLength F) *
        ((sourceOneHotCompletenessRadius F
          (sourceFormulaGrid encodingLength F) : ℚ) : ℝ)) ^ 2) :
    F.Satisfiable := by
  apply sourceFormula_satisfiable_of_short_signed_solution
    encodingLength F z hz
  exact Nat.le_of_lt
    (sourceFormula_ten_mul_integerSquaredNorm_lt_field_mul_fourth_power_of_short
      encodingLength F z hshort)

end

section

open GapCVP.Core

private theorem sourceFormula_satisfiable_of_factor400_short_fieldChecks
    (encodingLength : ℕ) (formula : Formula)
    (z : Fin (sourceFormulaDimension encodingLength formula) → ℤ)
    (hchecks :
      concreteSATFieldChecks formula
        (sourceFormulaGrid encodingLength formula)
        (sourceFormulaVariablePlace encodingLength formula)
        (sourceSizeParameter encodingLength formula ^ 30)
        (fun position => algebraMap (ZMod 2)
          (sourceFormulaField encodingLength formula)
          (z position : ZMod 2)))
    (hshort :
      (integerSquaredNorm z : ℝ) ≤
        (GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
          (sourceFormulaDimension encodingLength formula) *
          ((sourceOneHotCompletenessRadius formula
            (sourceFormulaGrid encodingLength formula) : ℚ) : ℝ)) ^ 2) :
    formula.Satisfiable := by
  exact sourceFormula_satisfiable_of_factor400_short_signed_solution
    encodingLength formula z
    ((sourceFormulaBinarySystem_solves_iff
      encodingLength formula z).mpr hchecks)
    hshort

end

section

open GapCVP.Core Polynomial

private theorem sourceFormula_signedSolution_of_satisfiable
    (encodingLength : ℕ) (F : Formula)
    (hsatisfiable : F.Satisfiable) :
    ∃ z : Fin (sourceFormulaDimension encodingLength F) → ℤ,
      (sourceFormulaBinarySystem encodingLength F).Solves z ∧
      (integerSquaredNorm z : ℝ) ≤
        ((sourceOneHotCompletenessRadius F
          (sourceFormulaGrid encodingLength F) : ℚ) : ℝ) ^ 2 := by
  simp only [GapCVP.Core.Formula.Satisfiable, decide_eq_true_eq] at *
  classical
  obtain ⟨assignment, hsatisfies⟩ := hsatisfiable
  obtain ⟨interpolant, hdegree, hinterpolant⟩ :=
    exists_sourceSAT_assignment_interpolant_of_injective
      F (sourceFormulaVariablePlace encodingLength F)
      (sourceFormulaVariablePlace_injective encodingLength F) assignment
  let points := sourceFormulaGrid encodingLength F
  let z := sourceOneHotSignedTable F points assignment hsatisfies interpolant
  refine ⟨z, ?_, ?_⟩
  · change
      (concreteSATBinaryAffineSystem F
        (sourceFormulaFieldBasis encodingLength F)
        points (sourceFormulaVariablePlace encodingLength F)
        (sourceSizeParameter encodingLength F ^ 30)).Solves z
    apply sourceOneHot_solves_concreteSATBinaryAffineSystem
      F (sourceFormulaFieldBasis encodingLength F)
      points (sourceFormulaVariablePlace encodingLength F)
      assignment hsatisfies interpolant hdegree hinterpolant
      _ (sourceSizeParameter encodingLength F ^ 30)
    intro point index
    exact sourceSATPuncturedGrid_sub_ne_zero F
      (sourceFormulaVariablePlace encodingLength F) point index
  · calc
      (integerSquaredNorm z : ℝ) =
          (((F.clauses.length + 1) * points.card : ℕ) : ℝ) := by
        exact_mod_cast
          sourceOneHotSignedTable_squaredNorm
            F points assignment hsatisfies interpolant
      _ ≤ ((sourceOneHotCompletenessRadius F points : ℚ) : ℝ) ^ 2 :=
        sourceOneHotCompletenessRadius_squared_bound F points

end

end Factor400BinaryConstructiveSourcePlaces

namespace BinaryExplicitSourceSoundness

open GapCVP.Core
open GapCVP.BinaryExplicitFourFamilyKernel
open GapCVP.Factor400BinaryConstructiveSourcePlaces

theorem sourceFormulaExplicitBinarySystem_signedSolution_of_satisfiable
    (encodingLength : ℕ) (formula : Formula)
    (hsatisfiable : formula.Satisfiable) :
    ∃ vector :
        Fin (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
          encodingLength formula) → ℤ,
      (GapCVP.BinaryExplicitAffineSystem.sourceFormulaExplicitBinarySystem
          encodingLength formula).Solves vector ∧
      (integerSquaredNorm vector : ℝ) ≤
        ((sourceOneHotCompletenessRadius formula
          (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
            encodingLength formula) : ℚ) : ℝ) ^ 2 := by
  obtain ⟨vector, hsolve, hshort⟩ :=
    GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormula_signedSolution_of_satisfiable
        encodingLength formula hsatisfiable
  refine ⟨vector, ?_, hshort⟩
  apply
    (sourceFormulaExplicitBinarySystem_solves_iff_concreteSATFieldChecks
        encodingLength formula vector).mpr
  exact
    (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaBinarySystem_solves_iff
      encodingLength formula vector).mp hsolve

private theorem sourceFormulaExplicitBinarySystem_satisfiable_of_factor400_short_signed_solution
    (encodingLength : ℕ) (formula : Formula)
    (vector :
      Fin (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength formula) → ℤ)
    (hsolve :
      (GapCVP.BinaryExplicitAffineSystem.sourceFormulaExplicitBinarySystem
          encodingLength formula).Solves vector)
    (hshort :
      (integerSquaredNorm vector : ℝ) ≤
        (GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
          (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
            encodingLength formula) *
          ((sourceOneHotCompletenessRadius formula
            (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
              encodingLength formula) : ℚ) : ℝ)) ^ 2) :
    formula.Satisfiable := by
  exact
    sourceFormula_satisfiable_of_factor400_short_fieldChecks
        encodingLength formula vector
        ((sourceFormulaExplicitBinarySystem_solves_iff_concreteSATFieldChecks
            encodingLength formula vector).mp hsolve)
        hshort

theorem sourceFormulaExplicitBinarySystem_squaredNorm_gt_factor400_of_unsatisfiable
    (encodingLength : ℕ) (formula : Formula)
    (vector :
      Fin (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength formula) → ℤ)
    (hsolve :
      (GapCVP.BinaryExplicitAffineSystem.sourceFormulaExplicitBinarySystem
          encodingLength formula).Solves vector)
    (hunsatisfiable : ¬ formula.Satisfiable) :
    (GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
      (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaDimension
        encodingLength formula) *
      ((sourceOneHotCompletenessRadius formula
        (GapCVP.Factor400BinaryConstructiveSourcePlaces.sourceFormulaGrid
          encodingLength formula) : ℚ) : ℝ)) ^ 2 <
      (integerSquaredNorm vector : ℝ) := by
  apply lt_of_not_ge
  intro hshort
  exact hunsatisfiable
    (sourceFormulaExplicitBinarySystem_satisfiable_of_factor400_short_signed_solution
      encodingLength formula vector hsolve hshort)

end BinaryExplicitSourceSoundness

namespace Factor400BinaryInstanceBridge

/-- GapCVP reduction support. -/
abbrev adaptGapCVPInstance (I : GapCVP.Core.GapCVPInstance) :
    GapCVP.GapCVPInstance where
  dimension := I.dimension
  basis := I.basis
  target := I.target
  radius := I.radius

private theorem adaptGapCVPInstance_wellFormed
    (I : GapCVP.Core.GapCVPInstance) :
    gapCVPWellFormed (adaptGapCVPInstance I) := by
  simp only [GapCVP.gapCVPWellFormed, decide_eq_true_eq] at *
  exact ⟨I.dimension_pos, I.basis_nonsingular, I.radius_pos⟩

private theorem adaptGapCVPInstance_distanceSquared
    (I : GapCVP.Core.GapCVPInstance)
    (z : Fin I.dimension → ℤ) :
    distanceSquared (adaptGapCVPInstance I) z =
      GapCVP.Core.squaredDistance I z := by
  unfold distanceSquared GapCVP.Core.squaredDistance
  change
    (∑ i : Fin I.dimension,
      ((∑ j : Fin I.dimension,
        (I.basis i j : ℝ) * (z j : ℝ)) - (I.target i : ℝ)) ^ 2) =
    ∑ i : Fin I.dimension,
      ((I.target i : ℝ) -
        ∑ j : Fin I.dimension,
          (I.basis i j : ℝ) * (z j : ℝ)) ^ 2
  apply Finset.sum_congr
  · rfl
  · intro i _
    ring

private theorem adaptGapCVPInstance_gapYES400_iff_squaredYes
    (I : GapCVP.Core.GapCVPInstance) :
    gapYES400 (adaptGapCVPInstance I) ↔
      GapCVP.Core.SquaredYes I := by
  simp only [GapCVP.gapYES400, GapCVP.Core.SquaredYes, decide_eq_true_eq]
  constructor
  · rintro ⟨_, z, hz⟩
    refine ⟨z, ?_⟩
    simpa only [adaptGapCVPInstance_distanceSquared,
      adaptGapCVPInstance] using hz
  · rintro ⟨z, hz⟩
    refine ⟨adaptGapCVPInstance_wellFormed I, z, ?_⟩
    simpa only [adaptGapCVPInstance_distanceSquared,
      adaptGapCVPInstance] using hz

theorem adaptGapCVPInstance_gapYES400_iff_metricYes
    (I : GapCVP.Core.GapCVPInstance) :
    gapYES400 (adaptGapCVPInstance I) ↔ I.IsYes := by
  constructor
  · intro hyes
    exact GapCVP.Core.yes_of_squaredYes I
      ((adaptGapCVPInstance_gapYES400_iff_squaredYes I).mp hyes)
  · intro hyes
    simp only [GapCVP.Core.GapCVPInstance.IsYes, decide_eq_true_eq] at hyes
    obtain ⟨z, hnearest⟩ :=
      GapCVP.Core.exists_latticePoint_eq_latticeDistance I
    apply (adaptGapCVPInstance_gapYES400_iff_squaredYes I).mpr
    simp only [GapCVP.Core.SquaredYes, decide_eq_true_eq]
    refine ⟨z, ?_⟩
    rw [GapCVP.Core.squaredDistance_eq_dist_sq]
    have hmetric :
        dist I.targetPoint (I.latticePoint z) ≤ (I.radius : ℝ) := by
      change I.latticeDistance ≤ (I.radius : ℝ) at hyes
      rw [hnearest] at hyes
      exact hyes
    have hradius : 0 ≤ (I.radius : ℝ) := by
      exact_mod_cast (le_of_lt I.radius_pos)
    nlinarith [dist_nonneg (x := I.targetPoint)
      (y := I.latticePoint z)]

theorem adaptGapCVPInstance_gapNO400_iff_metricNo
    (I : GapCVP.Core.GapCVPInstance) :
    gapNO400 (adaptGapCVPInstance I) ↔
      I.IsNo ((1 : ℝ) / 400) := by
  rw [← GapCVP.Core.squaredNoAt_iff_metricNo]
  simp only [GapCVP.gapNO400, GapCVP.Core.SquaredNoAt, decide_eq_true_eq]
  constructor
  · intro hno z
    have h := hno.2 z
    simpa only [gapFactor400, adaptGapCVPInstance,
      adaptGapCVPInstance_distanceSquared] using h
  · intro hno
    refine ⟨adaptGapCVPInstance_wellFormed I, ?_⟩
    intro z
    have h := hno z
    simpa only [gapFactor400, adaptGapCVPInstance,
      adaptGapCVPInstance_distanceSquared] using h

/-- GapCVP reduction support. -/
def effectiveGapCVPInstance
    (H : GapCVP.Core.BinaryAffineSystem)
    (hdimension : 0 < H.dimension)
    (radius : ℚ) (hradius : 0 < radius) : GapCVPInstance :=
  adaptGapCVPInstance
    (GapCVP.Core.effectiveConstructionAInstance
      H hdimension radius hradius)

theorem effectiveGapCVPInstance_wellFormed
    (H : GapCVP.Core.BinaryAffineSystem)
    (hdimension : 0 < H.dimension)
    (radius : ℚ) (hradius : 0 < radius) :
    gapCVPWellFormed
      (effectiveGapCVPInstance H hdimension radius hradius) :=
  adaptGapCVPInstance_wellFormed
    (GapCVP.Core.effectiveConstructionAInstance
      H hdimension radius hradius)

end Factor400BinaryInstanceBridge

namespace Factor400BinaryEffectiveBasisSerializerTM

open Turing GapCVP.BinaryEncoding GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceWholeOutputValidBranchRecordTM GapCVP.CNFFlatPhysicalBinaryAppendTM

/-- GapCVP reduction support. -/
def effectiveBasisPackedAtom : List Bool → List Bool :=
  markerConditionalOutput
    (markerConditionalOutput
      (fun _ : List Bool => encodeAtomic (2 : ℤ))
      (encodeAtomic (1 : ℤ)))
    (encodeAtomic (0 : ℤ))

/-- GapCVP reduction support. -/
noncomputable def effectiveBasisPackedAtomComputable :
    BitTM
      effectiveBasisPackedAtom :=
  markerConditionalComputable
    (markerConditionalComputable
      (sourceFixedWordComputable (encodeAtomic (2 : ℤ)))
      (encodeAtomic (1 : ℤ)))
    (encodeAtomic (0 : ℤ))

@[simp] theorem effectiveBasisPackedAtom_zero
    (suffix : List Bool) :
    effectiveBasisPackedAtom (false :: suffix) =
      encodeAtomic (0 : ℤ) := by
  simp only [effectiveBasisPackedAtom, markerConditionalOutput]

@[simp] theorem effectiveBasisPackedAtom_one
    (suffix : List Bool) :
    effectiveBasisPackedAtom (true :: false :: suffix) =
      encodeAtomic (1 : ℤ) := by
  simp only [effectiveBasisPackedAtom, markerConditionalOutput]

@[simp] theorem effectiveBasisPackedAtom_two
    (suffix : List Bool) :
    effectiveBasisPackedAtom (true :: true :: suffix) =
      encodeAtomic (2 : ℤ) := by
  simp only [effectiveBasisPackedAtom, markerConditionalOutput]

/-- GapCVP reduction support. -/
def effectiveTargetPackedAtom : List Bool → List Bool :=
  markerConditionalOutput
    (fun _ : List Bool => encodeAtomic (1 : ℚ))
    (encodeAtomic (0 : ℚ))

/-- GapCVP reduction support. -/
noncomputable def effectiveTargetPackedAtomComputable :
    BitTM
      effectiveTargetPackedAtom :=
  markerConditionalComputable
    (sourceFixedWordComputable (encodeAtomic (1 : ℚ)))
    (encodeAtomic (0 : ℚ))

@[simp] theorem effectiveTargetPackedAtom_false
    (suffix : List Bool) :
    effectiveTargetPackedAtom (false :: suffix) =
      encodeAtomic (0 : ℚ) := by
  simp only [effectiveTargetPackedAtom, markerConditionalOutput]

@[simp] theorem effectiveTargetPackedAtom_true
    (suffix : List Bool) :
    effectiveTargetPackedAtom (true :: suffix) =
      encodeAtomic (1 : ℚ) := by
  simp only [effectiveTargetPackedAtom, markerConditionalOutput]

private theorem physicalRecordFold_preservesSource
    (records : List (List Bool)) (source : List Bool) :
    boundedRecordFoldOutput sourceFlatAtomicRecordStep
      (unaryBoundedFoldWord records.length
        (sourceFlatAtomicDescriptorStream records ++
          lengthPrefixedWord source)) =
      lengthPrefixedWord source ++ records.flatten := by
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  exact sourceFlatAtomicRecordStep_iterate_descriptors records
    (lengthPrefixedWord source)

private def effectiveSourceSerializerPreparation
    (counter descriptors : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  counter input ++
    false :: (descriptors input ++ lengthPrefixedWord input)

private noncomputable def effectiveSourceSerializerPreparationComputable
    {counter descriptors : List Bool → List Bool}
    (counterComputer : BitTM counter)
    (descriptorComputer : BitTM descriptors) :
    BitTM
      (effectiveSourceSerializerPreparation counter descriptors) := by
  have hphysical := pointwiseAppendComputable counterComputer
    (pointwiseAppendComputable
      (sourceFixedWordComputable [false])
      (pointwiseAppendComputable descriptorComputer
        CLStructuralPrefixWriter.structuralPrefixWriterComputable))
  change
    BitTM
      (fun input : List Bool =>
        counter input ++
          false :: (descriptors input ++ lengthPrefixedWord input))
  exact hphysical

/-- GapCVP reduction support. -/
def effectiveSourceSerializerOutput
    (counter descriptors : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  firstFieldSuffix
    (boundedRecordFoldOutput sourceFlatAtomicRecordStep
      (effectiveSourceSerializerPreparation counter descriptors input))

private noncomputable def effectiveSourceSerializerComputable
    {counter descriptors : List Bool → List Bool}
    (counterComputer : BitTM counter)
    (descriptorComputer : BitTM descriptors) :
    BitTM
      (effectiveSourceSerializerOutput counter descriptors) := by
  have hprepared := GapCVP.TMComposition.computableInPolyTime
    (effectiveSourceSerializerPreparationComputable
      counterComputer descriptorComputer)
    sourceFlatAtomicRecordFoldComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hprepared firstFieldSuffixComputable
  change
    BitTM
      (fun input : List Bool =>
        firstFieldSuffix
          (boundedRecordFoldOutput sourceFlatAtomicRecordStep
            (effectiveSourceSerializerPreparation
              counter descriptors input)))
  exact hphysical

theorem effectiveSourceSerializerOutput_eq_flatten
    (counter descriptors : List Bool → List Bool)
    (records : List Bool → List (List Bool))
    (input : List Bool)
    (hcounter : counter input =
      List.replicate (records input).length true)
    (hdescriptors : descriptors input =
      sourceFlatAtomicDescriptorStream (records input)) :
    effectiveSourceSerializerOutput counter descriptors input =
      (records input).flatten := by
  unfold effectiveSourceSerializerOutput
    effectiveSourceSerializerPreparation
  rw [hcounter, hdescriptors]
  change
    firstFieldSuffix
      (boundedRecordFoldOutput sourceFlatAtomicRecordStep
        (unaryBoundedFoldWord (records input).length
          (sourceFlatAtomicDescriptorStream (records input) ++
            lengthPrefixedWord input))) =
      (records input).flatten
  rw [physicalRecordFold_preservesSource]
  exact firstFieldSuffix_valid input (records input).flatten

end Factor400BinaryEffectiveBasisSerializerTM

namespace SourceAnchoredQaryGridCandidateCatalogueTM

section

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

private def sourceAnchoredQaryGridPaddingPolynomial
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) : Polynomial ℕ :=
  (GapCVP.TMComposition.outputLengthPolynomial computer).comp
    (3 * Polynomial.X + 1)

private def sourceAnchoredQaryGridCompactRankSourcePair
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (firstFieldContents input) ++
    firstFieldContents (firstFieldSuffix input)

private noncomputable def sourceAnchoredQaryGridCompactRankSourcePairComputable :
    BitTM
      sourceAnchoredQaryGridCompactRankSourcePair := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    firstFieldContentsComputable structuralPrefixWriterComputable
  have hbase := GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable
  exact pointwiseAppendComputable hprefix hbase

private def sourceAnchoredQaryGridCompactCandidate
    (candidate : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  candidate (sourceAnchoredQaryGridCompactRankSourcePair input)

private noncomputable def sourceAnchoredQaryGridCompactCandidateComputable
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (sourceAnchoredQaryGridCompactCandidate candidate) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    sourceAnchoredQaryGridCompactRankSourcePairComputable computer
  change BitTM
    (fun input => candidate
      (sourceAnchoredQaryGridCompactRankSourcePair input))
  simpa only [Function.comp_def] using hphysical

private def sourceAnchoredQaryGridRankPayloads
    (count : ℕ) : List (List Bool) :=
  (List.range count).map (fun rank => List.replicate rank true)

end

section

open Turing

@[simp] private theorem sourceAnchoredQaryGridRankPayloads_length
    (count : ℕ) :
    (sourceAnchoredQaryGridRankPayloads count).length = count := by
  unfold sourceAnchoredQaryGridRankPayloads
  simp only [List.length_map, List.length_range]

end

end SourceAnchoredQaryGridCandidateCatalogueTM

namespace SourceMixedRadixMaskSelectedFlatPreparationTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder GapCVP.SourceMachineCert
open GapCVP.OutputBoundedDependentRecordFold GapCVP.SourceCanonicalFixedWordTuringTM
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceAnchoredQaryGridCandidateCatalogueTM GapCVP.SourceAnchoredGridRecordFoldTM
open GapCVP.SourceCanonicalUnaryGridIndexTM GapCVP.CLStructuralPrefixWriter
open GapCVP.CNFPolynomialRowMarkerTM GapCVP.CLStructuralCNFOutputMachinesUnconditional
open GapCVP.CNFFlatPhysicalBinaryAppendTM

/-- GapCVP reduction support. -/
structure SourceQaryMaskDynamicGridWidth where
  /-- GapCVP reduction support. -/
  output : List Bool → List Bool
  /-- GapCVP reduction support. -/
  computer : BitTM output

/-- GapCVP reduction support. -/
def sourceQaryMaskDynamicGridBaseSource
    (width : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord (width.output input) ++ input

/-- GapCVP reduction support. -/
noncomputable def maskDynamicGridBaseSourceComputable
    (width : SourceQaryMaskDynamicGridWidth) :
    BitTM
      (sourceQaryMaskDynamicGridBaseSource width) := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    width.computer structuralPrefixWriterComputable
  exact pointwiseAppendComputable hprefix
    (Turing.idComputableInPolyTime bitEncoding)

private def maskDynamicGridPaddedAnchor
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate)
    (input : List Bool) : List Bool :=
  sourcePreservingPolynomialMarkerWord
    (sourceAnchoredQaryGridPaddingPolynomial computer)
    (sourceQaryMaskDynamicGridBaseSource width input)

private noncomputable def sourceQaryMaskDynamicGridPaddedAnchorComputable
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (maskDynamicGridPaddedAnchor width computer) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (maskDynamicGridBaseSourceComputable width)
    (sourcePreservingPolynomialMarkerComputable
      (sourceAnchoredQaryGridPaddingPolynomial computer))
  change BitTM
    (fun input => sourcePreservingPolynomialMarkerWord
      (sourceAnchoredQaryGridPaddingPolynomial computer)
      (sourceQaryMaskDynamicGridBaseSource width input))
  simpa only [Function.comp_def] using hphysical

private def sourceQaryMaskDynamicGridCounter
    (width : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) : List Bool :=
  width.output input ++ [false]

private noncomputable def sourceQaryMaskDynamicGridCounterComputable
    (width : SourceQaryMaskDynamicGridWidth) :
    BitTM
      (sourceQaryMaskDynamicGridCounter width) :=
  pointwiseAppendComputable width.computer
    (sourceFixedWordComputable [false])

private def maskDynamicGridRankDescriptors
    (width : SourceQaryMaskDynamicGridWidth) :
    List Bool → List Bool :=
  sourceCanonicalUnaryGridIndexOutput ∘
    sourceQaryMaskDynamicGridCounter width

private noncomputable def sourceQaryMaskDynamicGridRankDescriptorsComputable
    (width : SourceQaryMaskDynamicGridWidth) :
    BitTM
      (maskDynamicGridRankDescriptors width) :=
  GapCVP.TMComposition.computableInPolyTime
    (sourceQaryMaskDynamicGridCounterComputable width)
    sourceCanonicalUnaryGridIndexComputable

private def sourceQaryMaskDynamicGridFoldSeed
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate)
    (input : List Bool) : List Bool :=
  lengthPrefixedWord
    (maskDynamicGridPaddedAnchor width computer input) ++
    maskDynamicGridRankDescriptors width input

private noncomputable def sourceQaryMaskDynamicGridFoldSeedComputable
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (sourceQaryMaskDynamicGridFoldSeed width computer) := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    (sourceQaryMaskDynamicGridPaddedAnchorComputable width computer)
    structuralPrefixWriterComputable
  exact pointwiseAppendComputable hprefix
    (sourceQaryMaskDynamicGridRankDescriptorsComputable width)

private def maskDynamicGridFoldPreparation
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate)
    (input : List Bool) : List Bool :=
  sourceQaryMaskDynamicGridCounter width input ++
    sourceQaryMaskDynamicGridFoldSeed width computer input

private noncomputable def sourceQaryMaskDynamicGridFoldPreparationComputable
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (maskDynamicGridFoldPreparation width computer) :=
  pointwiseAppendComputable
    (sourceQaryMaskDynamicGridCounterComputable width)
    (sourceQaryMaskDynamicGridFoldSeedComputable width computer)

/-- GapCVP reduction support. -/
def maskDynamicGridCandidateCatalogueOutput
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate)
    (input : List Bool) : List Bool :=
  firstFieldSuffix
    (boundedRecordFoldOutput
      (sourceAnchoredGridRecordRotationOutput
        (sourceAnchoredQaryGridCompactCandidate candidate))
      (maskDynamicGridFoldPreparation width computer input))

/-- GapCVP reduction support. -/
noncomputable def maskDynamicGridCandidateCatalogueComputable
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate) :
    BitTM
      (maskDynamicGridCandidateCatalogueOutput
        width computer) := by
  have hfold := sourceAnchoredGridRecordFoldComputable
    (sourceAnchoredQaryGridCompactCandidateComputable computer)
  have hprepared := GapCVP.TMComposition.computableInPolyTime
    (sourceQaryMaskDynamicGridFoldPreparationComputable width computer)
    hfold
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hprepared firstFieldSuffixComputable
  change BitTM
    (fun input => firstFieldSuffix
      (boundedRecordFoldOutput
        (sourceAnchoredGridRecordRotationOutput
          (sourceAnchoredQaryGridCompactCandidate candidate))
        (maskDynamicGridFoldPreparation
          width computer input)))
  simpa only [Function.comp_def] using hphysical

private theorem sourceQaryMaskDynamicGridCompactCandidate_paddedAnchor
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate)
    (input : List Bool) (rank : List Bool) :
    sourceAnchoredQaryGridCompactCandidate candidate
        (lengthPrefixedWord rank ++
          maskDynamicGridPaddedAnchor
            width computer input) =
      candidate (lengthPrefixedWord rank ++
        sourceQaryMaskDynamicGridBaseSource width input) := by
  unfold sourceAnchoredQaryGridCompactCandidate
    sourceAnchoredQaryGridCompactRankSourcePair
    maskDynamicGridPaddedAnchor
    sourcePreservingPolynomialMarkerWord
  simp only [firstFieldContents_valid, firstFieldSuffix_valid]

private theorem sourceQaryMaskDynamicGridCandidate_fits
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate)
    (input : List Bool) (count rank : ℕ)
    (hwidth : width.output input = List.replicate count true)
    (hrank : rank < count) :
    (sourceAnchoredQaryGridCompactCandidate candidate
      (lengthPrefixedWord (List.replicate rank true) ++
        maskDynamicGridPaddedAnchor
          width computer input)).length ≤
      (maskDynamicGridPaddedAnchor
        width computer input).length := by
  let base := sourceQaryMaskDynamicGridBaseSource width input
  let polynomial := GapCVP.TMComposition.outputLengthPolynomial
    computer
  let padding := sourceAnchoredQaryGridPaddingPolynomial computer
  have hbase : base.length = 2 * count + 1 + input.length := by
    simp only [sourceQaryMaskDynamicGridBaseSource, hwidth, List.length_append,
        lengthPrefixedWord_length,
      List.length_replicate, base]
  have hrankBase : rank ≤ base.length := by omega
  have hcompact :
      (lengthPrefixedWord (List.replicate rank true) ++ base).length ≤
        3 * base.length + 1 := by
    simp only [List.length_append, lengthPrefixedWord_length,
      List.length_replicate]
    omega
  have houtput := GapCVP.TMComposition.outputLengthPolynomial_bounds
    computer (lengthPrefixedWord (List.replicate rank true) ++ base)
  have hmonotone := GapCVP.TMComposition.natPolynomial_eval_monotone
    polynomial hcompact
  have hpadding : padding.eval base.length =
      polynomial.eval (3 * base.length + 1) := by
    simp only [sourceAnchoredQaryGridPaddingPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one,
            padding, polynomial]
  have hanchor : padding.eval base.length ≤
      (maskDynamicGridPaddedAnchor
        width computer input).length := by
    simp only [maskDynamicGridPaddedAnchor, sourcePreservingPolynomialMarkerWord,
        List.length_append,
        lengthPrefixedWord_length, List.length_replicate, base, padding]
    omega
  rw [sourceQaryMaskDynamicGridCompactCandidate_paddedAnchor
    width computer input (List.replicate rank true)]
  change (candidate
    (lengthPrefixedWord (List.replicate rank true) ++ base)).length ≤ _
  have hpoly :
      (candidate
        (lengthPrefixedWord (List.replicate rank true) ++ base)).length ≤
        padding.eval base.length := by
    rw [hpadding]
    exact houtput.trans hmonotone
  exact hpoly.trans hanchor

private theorem sourceQaryMaskDynamicGridRankDescriptors_valid
    (width : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (count : ℕ)
    (hwidth : width.output input = List.replicate count true) :
    maskDynamicGridRankDescriptors width input =
      (sourceAnchoredQaryGridRankPayloads count).flatMap
        lengthPrefixedWord := by
  unfold maskDynamicGridRankDescriptors
    sourceQaryMaskDynamicGridCounter
  rw [Function.comp_apply, hwidth]
  rw [show List.replicate count true ++ [false] =
    List.replicate count true ++ false :: [] by rfl]
  rw [sourceCanonicalUnaryGridIndexOutput_valid]
  simp only [List.append_nil,
    sourceCanonicalUnaryGridIndexDescriptors,
    sourceAnchoredQaryGridRankPayloads, List.flatMap_map]
  rfl

private theorem sourceQaryMaskDynamicGridFoldPreparation_valid
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate)
    (input : List Bool) (count : ℕ)
    (hwidth : width.output input = List.replicate count true) :
    maskDynamicGridFoldPreparation
        width computer input =
      unaryBoundedFoldWord count
        (lengthPrefixedWord
          (maskDynamicGridPaddedAnchor
            width computer input) ++
          (sourceAnchoredQaryGridRankPayloads count).flatMap
            lengthPrefixedWord) := by
  unfold maskDynamicGridFoldPreparation
    sourceQaryMaskDynamicGridFoldSeed
  rw [sourceQaryMaskDynamicGridRankDescriptors_valid
    width input count hwidth]
  unfold sourceQaryMaskDynamicGridCounter
  rw [hwidth]
  simp only [unaryBoundedFoldWord,
    List.append_assoc, List.cons_append, List.nil_append]

private theorem sourceQaryMaskDynamicGridCandidate_fits_all
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate)
    (input : List Bool) (count : ℕ)
    (hwidth : width.output input = List.replicate count true) :
    ∀ rank ∈ sourceAnchoredQaryGridRankPayloads count,
      (sourceAnchoredQaryGridCompactCandidate candidate
        (lengthPrefixedWord rank ++
          maskDynamicGridPaddedAnchor
            width computer input)).length ≤
        (maskDynamicGridPaddedAnchor
          width computer input).length := by
  intro rank hmember
  obtain ⟨index, hindex, hword⟩ := List.mem_map.mp hmember
  have hlt := List.mem_range.mp hindex
  subst rank
  exact sourceQaryMaskDynamicGridCandidate_fits
    width computer input count index hwidth hlt

theorem maskDynamicGridCandidateCatalogueOutput_valid
    (width : SourceQaryMaskDynamicGridWidth)
    {candidate : List Bool → List Bool}
    (computer : BitTM candidate)
    (input : List Bool) (count : ℕ)
    (hwidth : width.output input = List.replicate count true) :
    maskDynamicGridCandidateCatalogueOutput
        width computer input =
      (List.range count).flatMap
        (fun rank => lengthPrefixedWord
          (candidate (lengthPrefixedWord
            (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource width input))) := by
  have hfit := sourceQaryMaskDynamicGridCandidate_fits_all
    width computer input count hwidth
  have hfold := boundedRecordFoldOutput_sourceAnchoredGridRecordRanks
    (sourceAnchoredQaryGridCompactCandidate candidate)
    (maskDynamicGridPaddedAnchor width computer input)
    (sourceAnchoredQaryGridRankPayloads count) [] hfit
  unfold maskDynamicGridCandidateCatalogueOutput
  rw [sourceQaryMaskDynamicGridFoldPreparation_valid
    width computer input count hwidth]
  have hcounter :
      unaryBoundedFoldWord count
        (lengthPrefixedWord
          (maskDynamicGridPaddedAnchor
            width computer input) ++
          (sourceAnchoredQaryGridRankPayloads count).flatMap
            lengthPrefixedWord) =
        unaryBoundedFoldWord
          (sourceAnchoredQaryGridRankPayloads count).length
          (lengthPrefixedWord
            (maskDynamicGridPaddedAnchor
              width computer input) ++
            (sourceAnchoredQaryGridRankPayloads count).flatMap
              lengthPrefixedWord ++ []) := by
    rw [sourceAnchoredQaryGridRankPayloads_length]
    simp only [List.append_nil]
  rw [hcounter, hfold]
  simp only [List.append_nil, firstFieldSuffix_valid]
  unfold sourceAnchoredQaryGridRankPayloads
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro rank _
  exact congrArg lengthPrefixedWord
    (sourceQaryMaskDynamicGridCompactCandidate_paddedAnchor
      width computer input (List.replicate rank true))

private def sourceQaryMaskDynamicGridRecordFoldPreparation
    (width : SourceQaryMaskDynamicGridWidth)
    {record : List Bool → List Bool}
    (computer : BitTM record)
    (input : List Bool) : List Bool :=
  width.output input ++ false ::
    maskDynamicGridCandidateCatalogueOutput
      width computer input

private noncomputable def sourceQaryMaskDynamicGridRecordFoldPreparationComputable
    (width : SourceQaryMaskDynamicGridWidth)
    {record : List Bool → List Bool}
    (computer : BitTM record) :
    BitTM
      (sourceQaryMaskDynamicGridRecordFoldPreparation
        width computer) := by
  have htail := GapCVP.TMComposition.computableInPolyTime
    (maskDynamicGridCandidateCatalogueComputable
      width computer)
    (prependBitComputable false)
  exact pointwiseAppendComputable width.computer htail

/-- GapCVP reduction support. -/
def maskDynamicGridRecordCatalogueOutput
    (width : SourceQaryMaskDynamicGridWidth)
    {record : List Bool → List Bool}
    (computer : BitTM record) : List Bool → List Bool :=
  boundedRecordFoldOutput sourceFlatAtomicRecordStep ∘
    sourceQaryMaskDynamicGridRecordFoldPreparation width computer

/-- GapCVP reduction support. -/
noncomputable def maskDynamicGridRecordCatalogueComputable
    (width : SourceQaryMaskDynamicGridWidth)
    {record : List Bool → List Bool}
    (computer : BitTM record) :
    BitTM
      (maskDynamicGridRecordCatalogueOutput
        width computer) :=
  GapCVP.TMComposition.computableInPolyTime
    (sourceQaryMaskDynamicGridRecordFoldPreparationComputable
      width computer)
    sourceFlatAtomicRecordFoldComputable

theorem maskDynamicGridRecordCatalogueOutput_valid
    (width : SourceQaryMaskDynamicGridWidth)
    {record : List Bool → List Bool}
    (computer : BitTM record)
    (input : List Bool) (count : ℕ)
    (hwidth : width.output input = List.replicate count true) :
    maskDynamicGridRecordCatalogueOutput
        width computer input =
      (List.range count).flatMap
        (fun rank => record (lengthPrefixedWord
          (List.replicate rank true) ++
          sourceQaryMaskDynamicGridBaseSource width input)) := by
  let records : List (List Bool) :=
    (List.range count).map
      (fun rank => record (lengthPrefixedWord
        (List.replicate rank true) ++
        sourceQaryMaskDynamicGridBaseSource width input))
  have hcatalogue :=
    maskDynamicGridCandidateCatalogueOutput_valid
      width computer input count hwidth
  have hrecords :
      maskDynamicGridCandidateCatalogueOutput
        width computer input =
          sourceFlatAtomicDescriptorStream records := by
    rw [hcatalogue]
    change
      (List.range count).flatMap
        (fun rank => lengthPrefixedWord
          (record (lengthPrefixedWord
            (List.replicate rank true) ++
            sourceQaryMaskDynamicGridBaseSource width input))) =
        records.flatMap sourceFlatAtomicDescriptor
    unfold records
    rw [List.flatMap_map]
    rfl
  have hlength : records.length = count := by
    simp only [List.length_map, List.length_range, records]
  unfold maskDynamicGridRecordCatalogueOutput
    sourceQaryMaskDynamicGridRecordFoldPreparation
  rw [Function.comp_apply, hwidth, hrecords]
  change boundedRecordFoldOutput sourceFlatAtomicRecordStep
    (unaryBoundedFoldWord count
      (sourceFlatAtomicDescriptorStream records)) = _
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  have hresult :
      ((sourceFlatAtomicRecordStep^[count])
        (sourceFlatAtomicDescriptorStream records)) =
          records.flatten := by
    rw [← hlength]
    simpa only [List.append_nil, List.nil_append]
        using sourceFlatAtomicRecordStep_iterate_descriptors records []
  rw [hresult]
  simp only [List.flatten_eq_flatMap, List.flatMap_map, id_eq, records]

end SourceMixedRadixMaskSelectedFlatPreparationTM

namespace BinaryStructuralRecordTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.Factor400BinaryEffectiveBasisSerializerTM

private def constructiveStructuralRecordCountPolynomial : Polynomial ℕ :=
  2 + Polynomial.X + Polynomial.X ^ 2

/-- GapCVP reduction support. -/
def constructiveStructuralRecordCountOutput
    (dimension : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) : List Bool :=
  List.replicate
    (constructiveStructuralRecordCountPolynomial.eval
      (dimension.output input).length)
    true

private noncomputable def constructiveStructuralRecordCountComputable
    (dimension : SourceQaryMaskDynamicGridWidth) :
    BitTM
      (constructiveStructuralRecordCountOutput dimension) := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    dimension.computer
    (polynomialValueUnaryComputable
      constructiveStructuralRecordCountPolynomial)
  change
    BitTM
      (fun input : List Bool =>
        List.replicate
          (constructiveStructuralRecordCountPolynomial.eval
            (dimension.output input).length)
          true)
  exact hphysical

theorem constructiveStructuralRecordCountOutput_valid
    (dimension : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (n : ℕ)
    (hdimension : dimension.output input =
      List.replicate n true) :
    constructiveStructuralRecordCountOutput dimension input =
      List.replicate (2 + n + n * n) true := by
  simp only [constructiveStructuralRecordCountOutput, hdimension, List.length_replicate,
      constructiveStructuralRecordCountPolynomial, pow_two, Polynomial.eval_add,
          Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_mul]

/-- Internal support shared across GapCVP continuation modules. -/
def constructiveStructuralRecordWidth
    (dimension : SourceQaryMaskDynamicGridWidth) :
    SourceQaryMaskDynamicGridWidth where
  output := constructiveStructuralRecordCountOutput dimension
  computer := constructiveStructuralRecordCountComputable dimension

/-- GapCVP reduction support. -/
structure ConstructiveStructuralAtomComputer where
  /-- GapCVP reduction support. -/
  output : List Bool → List Bool
  /-- GapCVP reduction support. -/
  computer : BitTM output

/-- GapCVP reduction support. -/
def constructiveStructuralRankQuery
    (dimension : SourceQaryMaskDynamicGridWidth)
    (input : List Bool) (rank : ℕ) : List Bool :=
  lengthPrefixedWord (List.replicate rank true) ++
    sourceQaryMaskDynamicGridBaseSource
      (constructiveStructuralRecordWidth dimension) input

/-- GapCVP reduction support. -/
def constructiveStructuralDescriptorOutput
    (dimension : SourceQaryMaskDynamicGridWidth)
    (atom : ConstructiveStructuralAtomComputer) :
    List Bool → List Bool :=
  maskDynamicGridCandidateCatalogueOutput
    (constructiveStructuralRecordWidth dimension)
    atom.computer

private noncomputable def constructiveStructuralDescriptorComputable
    (dimension : SourceQaryMaskDynamicGridWidth)
    (atom : ConstructiveStructuralAtomComputer) :
    BitTM
      (constructiveStructuralDescriptorOutput dimension atom) :=
  maskDynamicGridCandidateCatalogueComputable
    (constructiveStructuralRecordWidth dimension)
    atom.computer

private theorem constructiveStructuralDescriptorOutput_valid
    (dimension : SourceQaryMaskDynamicGridWidth)
    (atom : ConstructiveStructuralAtomComputer)
    (input : List Bool) (n : ℕ)
    (hdimension : dimension.output input =
      List.replicate n true) :
    constructiveStructuralDescriptorOutput dimension atom input =
      (List.range (2 + n + n * n)).flatMap
        (fun rank =>
          lengthPrefixedWord
            (atom.output
              (constructiveStructuralRankQuery dimension input rank))) := by
  apply maskDynamicGridCandidateCatalogueOutput_valid
    (constructiveStructuralRecordWidth dimension)
    atom.computer input (2 + n + n * n)
  exact constructiveStructuralRecordCountOutput_valid
    dimension input n hdimension

private theorem constructiveStructuralRecords_indexed
    (records : List (List Bool)) :
    (List.range records.length).map
      (fun index => records.getD index []) = records := by
  apply List.ext_getElem
  · simp only [List.getD_eq_getElem?_getD, List.length_map, List.length_range]
  · intro index hleft hright
    simpa only [List.getD_eq_getElem?_getD, List.getElem_map, List.getElem_range] using
        (List.getElem_eq_getD (l := records) (i := index) (h := hright) ([] : List Bool)).symm

theorem constructiveStructuralDescriptorOutput_eq_records
    (dimension : SourceQaryMaskDynamicGridWidth)
    (atom : ConstructiveStructuralAtomComputer)
    (input : List Bool) (n : ℕ)
    (records : List (List Bool))
    (hdimension : dimension.output input =
      List.replicate n true)
    (hcount : records.length = 2 + n + n * n)
    (hatoms : ∀ rank : ℕ, rank < records.length →
      atom.output
          (constructiveStructuralRankQuery dimension input rank) =
        records.getD rank []) :
    constructiveStructuralDescriptorOutput dimension atom input =
      sourceFlatAtomicDescriptorStream records := by
  rw [constructiveStructuralDescriptorOutput_valid
    dimension atom input n hdimension]
  rw [← hcount]
  calc
    (List.range records.length).flatMap
        (fun rank => lengthPrefixedWord
          (atom.output
            (constructiveStructuralRankQuery dimension input rank))) =
      (List.range records.length).flatMap
        (fun rank => lengthPrefixedWord
          (records.getD rank [])) := by
        apply List.flatMap_congr
        intro rank hmember
        rw [hatoms rank (List.mem_range.mp hmember)]
    _ = ((List.range records.length).map
          (fun index => records.getD index [])).flatMap
          sourceFlatAtomicDescriptor := by
        simp only [List.getD_eq_getElem?_getD, List.flatMap_map, sourceFlatAtomicDescriptor]
    _ = sourceFlatAtomicDescriptorStream records := by
        rw [constructiveStructuralRecords_indexed]
        rfl

/-- GapCVP reduction support. -/
def constructiveStructuralSourceWord
    (dimension : SourceQaryMaskDynamicGridWidth)
    (atom : ConstructiveStructuralAtomComputer) :
    List Bool → List Bool :=
  effectiveSourceSerializerOutput
    (constructiveStructuralRecordCountOutput dimension)
    (constructiveStructuralDescriptorOutput dimension atom)

/-- GapCVP reduction support. -/
noncomputable def constructiveStructuralSourceWordComputable
    (dimension : SourceQaryMaskDynamicGridWidth)
    (atom : ConstructiveStructuralAtomComputer) :
    BitTM
      (constructiveStructuralSourceWord dimension atom) :=
  effectiveSourceSerializerComputable
    (constructiveStructuralRecordCountComputable dimension)
    (constructiveStructuralDescriptorComputable dimension atom)

theorem constructiveStructuralSourceWord_eq_encodeGapCVPInstance
    (dimension : SourceQaryMaskDynamicGridWidth)
    (atom : ConstructiveStructuralAtomComputer)
    (input : List Bool) (lattice : GapCVPInstance)
    (hdimension : dimension.output input =
      List.replicate lattice.dimension true)
    (hatoms : ∀ rank : ℕ,
      rank < (sourceLatticeStructuralRecords lattice).length →
        atom.output
            (constructiveStructuralRankQuery dimension input rank) =
          (sourceLatticeStructuralRecords lattice).getD rank []) :
    constructiveStructuralSourceWord dimension atom input =
      BinaryEncoding.encodeGapCVPInstance lattice := by
  let records := sourceLatticeStructuralRecords lattice
  have hcount : records.length =
      2 + lattice.dimension + lattice.dimension * lattice.dimension := by
    exact sourceLatticeStructuralRecords_length lattice
  have hcounter :
      constructiveStructuralRecordCountOutput dimension input =
        List.replicate records.length true := by
    rw [constructiveStructuralRecordCountOutput_valid
      dimension input lattice.dimension hdimension, hcount]
  have hdescriptors :
      constructiveStructuralDescriptorOutput dimension atom input =
        sourceFlatAtomicDescriptorStream records :=
    constructiveStructuralDescriptorOutput_eq_records
      dimension atom input lattice.dimension records
      hdimension hcount hatoms
  change
    effectiveSourceSerializerOutput
      (constructiveStructuralRecordCountOutput dimension)
      (constructiveStructuralDescriptorOutput dimension atom) input = _
  rw [effectiveSourceSerializerOutput_eq_flatten
    (constructiveStructuralRecordCountOutput dimension)
    (constructiveStructuralDescriptorOutput dimension atom)
    (fun _ => records) input hcounter hdescriptors]
  exact sourceLatticeStructuralRecords_flatten lattice

end BinaryStructuralRecordTM

namespace Core

section

open scoped BigOperators
open Matrix

namespace EffectiveBinaryGaussian

private theorem swapRows_preserves_zero_column
    {m n : ℕ} (system : System m n)
    (left right : Fin m) (column : Fin n)
    (hleft : system.check left column = 0)
    (hright : system.check right column = 0)
    (row : Fin m) :
    (swapRows system left right).check row column =
      system.check row column := by
  by_cases hl : row = left
  · subst row
    simp only [swapRows, Equiv.swap_apply_left, hright, hleft]
  · by_cases hr : row = right
    · subst row
      simp only [swapRows, Equiv.swap_apply_right, hleft, hright]
    · change
        system.check ((Equiv.swap left right) row) column =
          system.check row column
      rw [Equiv.swap_apply_of_ne_of_ne hl hr]

private theorem columnStep_preserves_scanned_column
    {m n : ℕ} (scanned : List (Fin n)) (state : State m n)
    (normal : PrefixNormal scanned state)
    (column : Fin n) (hrow : state.nextPivot < m)
    (candidate : Fin m)
    (hfound : findPivotOption state column = some candidate)
    (oldColumn : Fin n) (hold : oldColumn ∈ scanned)
    (row : Fin m) :
    (columnStep state column).system.check row oldColumn =
      state.system.check row oldColumn := by
  let pivot : Fin m := ⟨state.nextPivot, hrow⟩
  let swapped : State m n :=
    applyOperation state (.swap candidate pivot)
  have hcandidate : state.nextPivot ≤ candidate.val :=
    (findPivotOption_some state column candidate hfound).1
  have hcZero : state.system.check candidate oldColumn = 0 :=
    GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.scanned_lower_zero normal oldColumn hold
        candidate hcandidate
  have hpZero : state.system.check pivot oldColumn = 0 :=
    GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.scanned_lower_zero normal oldColumn hold pivot
        (by simp only [Std.le_refl, pivot])
  have hswap (r : Fin m) :
      swapped.system.check r oldColumn =
        state.system.check r oldColumn := by
    change (swapRows state.system candidate pivot).check r oldColumn =
      state.system.check r oldColumn
    exact swapRows_preserves_zero_column state.system candidate pivot
      oldColumn hcZero hpZero r
  have hswappedZero : swapped.system.check pivot oldColumn = 0 := by
    rw [hswap pivot, hpZero]
  simp only [columnStep, hrow, ↓reduceDIte, hfound]
  change
    (clearTargets pivot column (List.finRange m) swapped).system.check
      row oldColumn = state.system.check row oldColumn
  exact
    (clearTargets_check_of_pivot_zero pivot column oldColumn
      (List.finRange m) swapped hswappedZero row).trans (hswap row)

private theorem columnStep_preserves_old_pivot_column
    {m n : ℕ} (scanned : List (Fin n)) (state : State m n)
    (normal : PrefixNormal scanned state)
    (column : Fin n) (hrow : state.nextPivot < m)
    (candidate : Fin m)
    (hfound : findPivotOption state column = some candidate)
    (pair : Fin m × Fin n) (hpair : pair ∈ state.pivots)
    (row : Fin m) :
    (columnStep state column).system.check row pair.2 =
      state.system.check row pair.2 := by
  let pivot : Fin m := ⟨state.nextPivot, hrow⟩
  let swapped : State m n :=
    applyOperation state (.swap candidate pivot)
  have hcandidate : state.nextPivot ≤ candidate.val :=
    (findPivotOption_some state column candidate hfound).1
  have hbelow : pair.1.val < state.nextPivot :=
    GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_below normal pair hpair
  have hcne : candidate ≠ pair.1 := by
    intro heq
    have hv := congrArg (fun i : Fin m => i.val) heq
    omega
  have hpne : pivot ≠ pair.1 := by
    intro heq
    have hv := congrArg (fun i : Fin m => i.val) heq
    change state.nextPivot = pair.1.val at hv
    omega
  have hcZero : state.system.check candidate pair.2 = 0 := by
    rw [GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_unit normal pair hpair candidate,
        ite_eq_right hcne]
  have hpZero : state.system.check pivot pair.2 = 0 := by
    rw [GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_unit normal pair hpair pivot,
        ite_eq_right
        hpne]
  have hswap (r : Fin m) :
      swapped.system.check r pair.2 =
        state.system.check r pair.2 := by
    change (swapRows state.system candidate pivot).check r pair.2 =
      state.system.check r pair.2
    exact swapRows_preserves_zero_column state.system candidate pivot
      pair.2 hcZero hpZero r
  have hswappedZero : swapped.system.check pivot pair.2 = 0 := by
    rw [hswap pivot, hpZero]
  simp only [columnStep, hrow, ↓reduceDIte, hfound]
  change
    (clearTargets pivot column (List.finRange m) swapped).system.check
      row pair.2 = state.system.check row pair.2
  exact
    (clearTargets_check_of_pivot_zero pivot column pair.2
      (List.finRange m) swapped hswappedZero row).trans (hswap row)

private theorem columnStep_prefixNormal
    {m n : ℕ} (scanned : List (Fin n)) (state : State m n)
    (column : Fin n) (normal : PrefixNormal scanned state) :
    PrefixNormal (column :: scanned) (columnStep state column) := by
  by_cases hrow : state.nextPivot < m
  · cases hfound : findPivotOption state column with
    | none =>
        have hnone :
            ∀ row ∈ List.finRange m,
              ¬ decide
                (state.nextPivot ≤ row.val ∧
                  state.system.check row column = (1 : ZMod 2)) = true := by
          exact List.find?_eq_none.mp hfound
        have hstate : columnStep state column = state := by
          simp only [columnStep, hrow, ↓reduceDIte, hfound]
        rw [hstate]
        simp only [PrefixNormal, decide_eq_true_eq]
        refine ⟨GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.nextPivot_le normal,
            GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_below normal,
          GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_complete normal,
              GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_unit normal, ?_⟩
        intro oldColumn hold row hge
        rcases List.mem_cons.mp hold with hnew | hold
        · subst oldColumn
          apply binary_eq_zero_of_ne_one
          intro hone
          apply hnone row (List.mem_finRange row)
          simp only [hge, hone, and_self, decide_true]
        · exact GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.scanned_lower_zero normal
            oldColumn hold row hge
    | some candidate =>
        let pivot : Fin m := ⟨state.nextPivot, hrow⟩
        have hpivots :
            (columnStep state column).pivots =
              (pivot, column) :: state.pivots := by
          simp only [columnStep, hrow, ↓reduceDIte, hfound, applyOperation, clearTargets_pivots,
              pivot]
        have hnext :
            (columnStep state column).nextPivot =
              state.nextPivot + 1 := by
          simp only [columnStep, hrow, ↓reduceDIte, hfound, clearTargets_pivots]
        simp only [PrefixNormal, decide_eq_true_eq]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hnext]
          omega
        · intro pair hpair
          rw [hpivots] at hpair
          rcases List.mem_cons.mp hpair with hnew | hold
          · subst pair
            rw [hnext]
            change state.nextPivot < state.nextPivot + 1
            omega
          · rw [hnext]
            have hb := GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_below normal pair
                hold
            omega
        · intro row hbelow
          rw [hnext] at hbelow
          by_cases hold : row.val < state.nextPivot
          · obtain ⟨oldColumn, hmem⟩ :=
              GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_complete normal row hold
            refine ⟨oldColumn, ?_⟩
            rw [hpivots]
            exact List.mem_cons_of_mem _ hmem
          · have hval : row.val = state.nextPivot := by omega
            have heq : row = pivot := by
              apply Fin.ext
              simpa only using hval
            refine ⟨column, ?_⟩
            rw [hpivots, heq]
            exact List.mem_cons_self
        · intro pair hpair row
          rw [hpivots] at hpair
          rcases List.mem_cons.mp hpair with hnew | hold
          · subst pair
            exact columnStep_pivot_column
              state column hrow candidate hfound row
          · rw [columnStep_preserves_old_pivot_column
              scanned state normal column hrow candidate hfound
              pair hold row]
            exact GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_unit normal pair hold row
        · intro oldColumn hold row hge
          rw [hnext] at hge
          rcases List.mem_cons.mp hold with hnew | hold
          · subst oldColumn
            have hne : row ≠ (⟨state.nextPivot, hrow⟩ : Fin m) := by
              intro heq
              have hv := congrArg (fun i : Fin m => i.val) heq
              change row.val = state.nextPivot at hv
              omega
            simpa only [hne, ↓reduceIte] using (columnStep_pivot_column state column hrow candidate
                hfound row)
          · rw [columnStep_preserves_scanned_column
              scanned state normal column hrow candidate hfound
              oldColumn hold row]
            apply GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.scanned_lower_zero normal
                oldColumn hold row
            omega
  · have hstate : columnStep state column = state := by
      simp only [columnStep, hrow, ↓reduceDIte]
    rw [hstate]
    simp only [PrefixNormal, decide_eq_true_eq]
    refine ⟨GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.nextPivot_le normal,
        GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_below normal,
      GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_complete normal,
          GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_unit normal, ?_⟩
    intro oldColumn hold row hge
    have hlt := row.isLt
    have hfull : m ≤ state.nextPivot := Nat.le_of_not_gt hrow
    omega

private theorem columnStep_pivots_pairwise
    {m n : ℕ} (scanned : List (Fin n)) (state : State m n)
    (column : Fin n) (normal : PrefixNormal scanned state)
    (hunique : state.pivots.Pairwise (fun p q => p.1 ≠ q.1)) :
    (columnStep state column).pivots.Pairwise
      (fun p q => p.1 ≠ q.1) := by
  by_cases hrow : state.nextPivot < m
  · cases hfound : findPivotOption state column with
    | none =>
        simpa only [ne_eq, columnStep, hrow, ↓reduceDIte, hfound] using hunique
    | some candidate =>
        let pivot : Fin m := ⟨state.nextPivot, hrow⟩
        have hpivots :
            (columnStep state column).pivots =
              (pivot, column) :: state.pivots := by
          simp only [columnStep, hrow, ↓reduceDIte, hfound, applyOperation, clearTargets_pivots,
              pivot]
        rw [hpivots]
        refine List.pairwise_cons.mpr ⟨?_, hunique⟩
        intro pair hpair heq
        have hbelow := GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_below normal pair
            hpair
        have hv := congrArg (fun i : Fin m => i.val) heq
        change state.nextPivot = pair.1.val at hv
        omega
  · simpa only [ne_eq, columnStep, hrow, ↓reduceDIte] using hunique

private theorem runColumns_prefixNormal
    {m n : ℕ} (columns scanned : List (Fin n)) (state : State m n)
    (normal : PrefixNormal scanned state) :
    PrefixNormal (columns.reverse ++ scanned) (runColumns columns state) := by
  induction columns generalizing scanned state with
  | nil => simpa only [List.reverse_nil, List.nil_append, runColumns, List.foldl_nil] using normal
  | cons column rest ih =>
      change
        PrefixNormal ((column :: rest).reverse ++ scanned)
          (runColumns rest (columnStep state column))
      have hrest := ih (column :: scanned) (columnStep state column)
        (columnStep_prefixNormal scanned state column normal)
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
          using hrest

private theorem eliminate_prefixNormal
    {m n : ℕ} (system : System m n) :
    PrefixNormal (List.finRange n).reverse (eliminate system) := by
  simpa only [eliminate, List.append_nil] using
      (runColumns_prefixNormal (List.finRange n) [] (initialState system)
          (initialState_prefixNormal system))

private theorem runColumns_pivots_pairwise
    {m n : ℕ} (columns scanned : List (Fin n)) (state : State m n)
    (normal : PrefixNormal scanned state)
    (hunique : state.pivots.Pairwise (fun p q => p.1 ≠ q.1)) :
    (runColumns columns state).pivots.Pairwise
      (fun p q => p.1 ≠ q.1) := by
  induction columns generalizing scanned state with
  | nil => simpa only [ne_eq, runColumns, List.foldl_nil] using hunique
  | cons column rest ih =>
      change
        (runColumns rest (columnStep state column)).pivots.Pairwise
          (fun p q => p.1 ≠ q.1)
      exact ih (column :: scanned) (columnStep state column)
        (columnStep_prefixNormal scanned state column normal)
        (columnStep_pivots_pairwise scanned state column normal hunique)

private theorem eliminate_pivots_pairwise
    {m n : ℕ} (system : System m n) :
    (eliminate system).pivots.Pairwise (fun p q => p.1 ≠ q.1) := by
  simpa only [ne_eq, eliminate] using
      (runColumns_pivots_pairwise (List.finRange n) [] (initialState system)
          (initialState_prefixNormal system)
        (by simp [initialState]))

/-- GapCVP reduction support. -/
noncomputable def System.InKernel {m n : ℕ}
    (system : System m n) (assignment : Fin n → ZMod 2) : Bool :=
  @decide (
  system.check.mulVec assignment = 0
  ) (Classical.propDecidable _)
theorem RowOperation.inKernel_iff
    {m n : ℕ} (operation : RowOperation m)
    (system : System m n) (assignment : Fin n → ZMod 2) :
    (operation.apply system).InKernel assignment ↔
      system.InKernel assignment := by
  simp only [GapCVP.Core.EffectiveBinaryGaussian.System.InKernel, decide_eq_true_eq]
  cases operation with
  | swap left right =>
      let zeroSystem : System m n :=
        { check := system.check, rhs := 0 }
      have h := swapRows_satisfies_iff
        zeroSystem left right assignment
      simp only [GapCVP.Core.EffectiveBinaryGaussian.System.Satisfies,
        decide_eq_true_eq] at h
      change
        (swapRows zeroSystem left right).check.mulVec assignment =
            (swapRows zeroSystem left right).rhs ↔
          zeroSystem.check.mulVec assignment = zeroSystem.rhs at h
      have hzero : (swapRows zeroSystem left right).rhs =
          (0 : Fin m → ZMod 2) := by
        funext row
        simp only [swapRows, Pi.zero_apply, zeroSystem]
      rw [hzero] at h
      change
        (swapRows system left right).check.mulVec assignment =
            (0 : Fin m → ZMod 2) ↔
          system.check.mulVec assignment = (0 : Fin m → ZMod 2)
      exact h
  | add source target distinct =>
      let zeroSystem : System m n :=
        { check := system.check, rhs := 0 }
      have h := addRow_satisfies_iff
        zeroSystem source target distinct assignment
      simp only [GapCVP.Core.EffectiveBinaryGaussian.System.Satisfies,
        decide_eq_true_eq] at h
      change
        (addRow zeroSystem source target).check.mulVec assignment =
            (addRow zeroSystem source target).rhs ↔
          zeroSystem.check.mulVec assignment = zeroSystem.rhs at h
      have hzero : (addRow zeroSystem source target).rhs =
          (0 : Fin m → ZMod 2) := by
        funext row
        simp only [addRow, Pi.zero_apply, add_zero, ite_self, zeroSystem]
      rw [hzero] at h
      change
        (addRow system source target).check.mulVec assignment =
            (0 : Fin m → ZMod 2) ↔
          system.check.mulVec assignment = (0 : Fin m → ZMod 2)
      exact h

private theorem applyOperation_inKernel_iff
    {m n : ℕ} (state : State m n)
    (operation : RowOperation m)
    (assignment : Fin n → ZMod 2) :
    (applyOperation state operation).system.InKernel assignment ↔
      state.system.InKernel assignment :=
  operation.inKernel_iff state.system assignment

private theorem clearTarget_inKernel_iff
    {m n : ℕ} (pivot : Fin m) (column : Fin n)
    (state : State m n) (target : Fin m)
    (assignment : Fin n → ZMod 2) :
    (clearTarget pivot column state target).system.InKernel assignment ↔
      state.system.InKernel assignment := by
  unfold clearTarget
  split
  · rfl
  · split
    · exact applyOperation_inKernel_iff _ _ _
    · rfl

private theorem clearTargets_inKernel_iff
    {m n : ℕ} (pivot : Fin m) (column : Fin n)
    (targets : List (Fin m)) (state : State m n)
    (assignment : Fin n → ZMod 2) :
    (clearTargets pivot column targets state).system.InKernel assignment ↔
      state.system.InKernel assignment := by
  induction targets generalizing state with
  | nil => rfl
  | cons target rest ih =>
      change
        (clearTargets pivot column rest
          (clearTarget pivot column state target)).system.InKernel
            assignment ↔
          state.system.InKernel assignment
      exact (ih (clearTarget pivot column state target)).trans
        (clearTarget_inKernel_iff pivot column state target assignment)

private theorem columnStep_inKernel_iff
    {m n : ℕ} (state : State m n)
    (column : Fin n) (assignment : Fin n → ZMod 2) :
    (columnStep state column).system.InKernel assignment ↔
      state.system.InKernel assignment := by
  by_cases hactive : state.nextPivot < m
  · cases hfound : findPivotOption state column with
    | none => simp only [columnStep, hactive, ↓reduceDIte, hfound]
    | some candidate =>
        simp only [columnStep, hactive, ↓reduceDIte, hfound]
        exact
          (clearTargets_inKernel_iff
            ⟨state.nextPivot, hactive⟩ column (List.finRange m)
            (applyOperation state
              (.swap candidate ⟨state.nextPivot, hactive⟩))
            assignment).trans
            (applyOperation_inKernel_iff state
              (.swap candidate ⟨state.nextPivot, hactive⟩)
              assignment)
  · simp only [columnStep, hactive, ↓reduceDIte]

private theorem runColumns_inKernel_iff
    {m n : ℕ} (columns : List (Fin n))
    (state : State m n) (assignment : Fin n → ZMod 2) :
    (runColumns columns state).system.InKernel assignment ↔
      state.system.InKernel assignment := by
  induction columns generalizing state with
  | nil => rfl
  | cons column rest ih =>
      change
        (runColumns rest (columnStep state column)).system.InKernel
          assignment ↔ state.system.InKernel assignment
      exact (ih (columnStep state column)).trans
        (columnStep_inKernel_iff state column assignment)

private theorem eliminate_inKernel_iff
    {m n : ℕ} (system : System m n)
    (assignment : Fin n → ZMod 2) :
    (eliminate system).system.InKernel assignment ↔
      system.InKernel assignment :=
  runColumns_inKernel_iff (List.finRange n)
    (initialState system) assignment

end EffectiveBinaryGaussian

theorem BinaryAffineSystem.effectiveGaussian_kernel_iff
    (H : BinaryAffineSystem)
    (assignment : Fin H.dimension → ZMod 2) :
    H.effectiveGaussianState.system.check.mulVec assignment = 0 ↔
      H.check.mulVec assignment = 0 := by
  simpa only [BinaryAffineSystem.effectiveGaussianState,
    BinaryAffineSystem.effectiveGaussianSystem,
    EffectiveBinaryGaussian.System.InKernel, decide_eq_true_eq] using
    EffectiveBinaryGaussian.eliminate_inKernel_iff
      H.effectiveGaussianSystem assignment

theorem BinaryAffineSystem.effectiveGaussian_signedKernel_iff
    (H : BinaryAffineSystem) (z : Fin H.dimension → ℤ) :
    H.effectiveGaussianState.system.check.mulVec (binaryResidue z) = 0 ↔
      H.InLattice z := by
  simp only [GapCVP.Core.BinaryAffineSystem.InLattice, decide_eq_true_eq]
  exact H.effectiveGaussian_kernel_iff (binaryResidue z)

theorem BinaryAffineSystem.effectivePivotRow_some_mem
    (H : BinaryAffineSystem)
    (column : Fin H.dimension) (row : Fin H.rowCount)
    (hrow : H.effectivePivotRowOption column = some row) :
    (row, column) ∈ H.effectiveGaussianState.pivots := by
  unfold BinaryAffineSystem.effectivePivotRowOption at hrow
  obtain ⟨pair, hfind, hfirst⟩ :=
    Option.map_eq_some_iff.mp hrow
  have hsecond : pair.2 = column := by
    have hdecide := List.find?_some hfind
    exact of_decide_eq_true hdecide
  obtain ⟨_, position, hposition, hget, _⟩ :=
    List.find?_eq_some_iff_getElem.mp hfind
  have hmember : pair ∈ H.effectiveGaussianState.pivots :=
    List.mem_of_getElem hget
  have heq : pair = (row, column) :=
    Prod.ext hfirst hsecond
  simpa only [heq] using hmember

theorem BinaryAffineSystem.effectivePivotRow_eq_some_of_mem
    (H : BinaryAffineSystem)
    (hnormal : EffectiveBinaryGaussian.PrefixNormal
      (List.finRange H.dimension).reverse H.effectiveGaussianState)
    (column : Fin H.dimension) (row : Fin H.rowCount)
    (hmember : (row, column) ∈ H.effectiveGaussianState.pivots) :
    H.effectivePivotRowOption column = some row := by
  let predicate : Fin H.rowCount × Fin H.dimension → Bool :=
    fun pair => decide (pair.2 = column)
  cases hfind : H.effectiveGaussianState.pivots.find? predicate with
  | none =>
      have hnone := (List.find?_eq_none.mp hfind)
        (row, column) hmember
      have htrue : predicate (row, column) = true := by
        simp only [decide_true, predicate]
      exact (hnone htrue).elim
  | some pair =>
      have hdecide := List.find?_some hfind
      have hsecond : pair.2 = column := by
        exact of_decide_eq_true hdecide
      obtain ⟨_, position, hposition, hget, _⟩ :=
        List.find?_eq_some_iff_getElem.mp hfind
      have hpair : pair ∈ H.effectiveGaussianState.pivots :=
        List.mem_of_getElem hget
      have hpairUnit := GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_unit hnormal pair
          hpair row
      have hrowUnit := GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_unit hnormal
        (row, column) hmember row
      have hone :
          H.effectiveGaussianState.system.check row column = 1 := by
        simpa only [↓reduceIte] using hrowUnit
      have hequnit :
          H.effectiveGaussianState.system.check row column =
            if row = pair.1 then 1 else 0 := by
        simpa only [hsecond] using hpairUnit
      have heq : pair.1 = row := by
        by_contra hne
        have hother : row ≠ pair.1 := Ne.symm hne
        simp only [hone, hother, ↓reduceIte, one_ne_zero] at hequnit
      unfold BinaryAffineSystem.effectivePivotRowOption
      change
        (H.effectiveGaussianState.pivots.find? predicate).map
          Prod.fst = some row
      rw [hfind]
      simp only [Option.map_some, heq]

private theorem effective_binary_add_eq_zero_iff_eq (left right : ZMod 2) :
    left + right = 0 ↔ left = right := by
  constructor
  · intro hzero
    calc
      left = left + 0 := (add_zero left).symm
      _ = left + (right + right) := by
        rw [EffectiveBinaryGaussian.binary_add_self]
      _ = (left + right) + right := by
        rw [add_assoc]
      _ = 0 + right := by rw [hzero]
      _ = right := zero_add right
  · intro hequal
    rw [hequal]
    exact EffectiveBinaryGaussian.binary_add_self right

theorem BinaryAffineSystem.effectiveReducedRow_mulVec
    (H : BinaryAffineSystem)
    (hnormal : EffectiveBinaryGaussian.PrefixNormal
      (List.finRange H.dimension).reverse H.effectiveGaussianState)
    (hunique : ∀ (first second : Fin H.rowCount × Fin H.dimension),
      first ∈ H.effectiveGaussianState.pivots →
      second ∈ H.effectiveGaussianState.pivots →
      first.1 = second.1 → first.2 = second.2)
    (bits : Fin H.dimension → ZMod 2)
    (pivotColumn : Fin H.dimension) (pivotRow : Fin H.rowCount)
    (hpivot : H.effectivePivotRowOption pivotColumn = some pivotRow) :
    H.effectiveGaussianState.system.check.mulVec bits pivotRow =
      bits pivotColumn +
        ∑ column : Fin H.dimension,
          if H.effectivePivotRowOption column = none then
            H.effectiveGaussianState.system.check pivotRow column *
              bits column
          else 0 := by
  classical
  have hpivotMem := H.effectivePivotRow_some_mem
    pivotColumn pivotRow hpivot
  change
    (∑ column : Fin H.dimension,
      H.effectiveGaussianState.system.check pivotRow column *
        bits column) = _
  calc
    (∑ column : Fin H.dimension,
      H.effectiveGaussianState.system.check pivotRow column *
        bits column) =
        ∑ column : Fin H.dimension,
          ((if column = pivotColumn then bits pivotColumn else 0) +
            (if H.effectivePivotRowOption column = none then
              H.effectiveGaussianState.system.check pivotRow column *
                bits column
            else 0)) := by
      apply Finset.sum_congr rfl
      intro column _
      by_cases hequal : column = pivotColumn
      · subst column
        have hunit := GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_unit hnormal
          (pivotRow, pivotColumn) hpivotMem pivotRow
        simpa only [↓reduceIte, hpivot, reduceCtorEq, add_zero, one_mul] using
            congrArg (fun value : ZMod 2 => value * bits pivotColumn) hunit
      · cases hcolumn : H.effectivePivotRowOption column with
        | none =>
            simp only [hequal, ↓reduceIte, zero_add]
        | some otherRow =>
            have hotherMem := H.effectivePivotRow_some_mem
              column otherRow hcolumn
            have hrowne : pivotRow ≠ otherRow := by
              intro heq
              have hcolumnEq := hunique
                (pivotRow, pivotColumn) (otherRow, column)
                hpivotMem hotherMem heq
              exact hequal hcolumnEq.symm
            have hunit := GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_unit hnormal
              (otherRow, column) hotherMem pivotRow
            simp only [hrowne, ↓reduceIte] at hunit
            simp only [hunit, zero_mul, hequal, ↓reduceIte, reduceCtorEq, add_zero]
    _ = bits pivotColumn +
        ∑ column : Fin H.dimension,
          if H.effectivePivotRowOption column = none then
            H.effectiveGaussianState.system.check pivotRow column *
              bits column
          else 0 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem BinaryAffineSystem.effectiveSquareBasisMatrix_mulVec_pivot_full
    (H : BinaryAffineSystem)
    (coefficients : Fin H.dimension → ℤ)
    (row : Fin H.dimension) (pivot : Fin H.rowCount)
    (hrow : H.effectivePivotRowOption row = some pivot) :
    H.effectiveSquareBasisMatrix.mulVec coefficients row =
      (∑ column : Fin H.dimension,
        if H.effectivePivotRowOption column = none then
          ((H.effectiveGaussianState.system.check pivot column).val : ℤ) *
            coefficients column
        else 0) + 2 * coefficients row := by
  classical
  change
    (∑ column : Fin H.dimension,
      H.effectiveSquareBasisMatrix row column *
        coefficients column) = _
  calc
    (∑ column : Fin H.dimension,
      H.effectiveSquareBasisMatrix row column *
        coefficients column) =
        ∑ column : Fin H.dimension,
          ((if H.effectivePivotRowOption column = none then
              ((H.effectiveGaussianState.system.check
                pivot column).val : ℤ) * coefficients column
            else 0) +
            (if column = row then 2 * coefficients row else 0)) := by
      apply Finset.sum_congr rfl
      intro column _
      cases hcolumn : H.effectivePivotRowOption column with
      | none =>
          have hne : column ≠ row := by
            intro heq
            subst column
            simp only [hrow, reduceCtorEq] at hcolumn
          simp only [effectiveSquareBasisMatrix, hrow, hcolumn, ZMod.natCast_val, ↓reduceIte, hne,
              add_zero]
      | some other =>
          by_cases heq : column = row
          · subst column
            simp only [effectiveSquareBasisMatrix, hrow, ↓reduceIte, reduceCtorEq, zero_add]
          · simp only [effectiveSquareBasisMatrix, hrow, hcolumn, Ne.symm heq, ↓reduceIte,
              zero_mul, reduceCtorEq, heq,
                add_zero]
    _ = (∑ column : Fin H.dimension,
        if H.effectivePivotRowOption column = none then
          ((H.effectiveGaussianState.system.check pivot column).val : ℤ) *
            coefficients column
        else 0) + 2 * coefficients row := by
      rw [Finset.sum_add_distrib]
      simp only [ZMod.natCast_val, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem BinaryAffineSystem.effectiveGaussian_kernel_iff_graph_of_normal
    (H : BinaryAffineSystem)
    (hnormal : EffectiveBinaryGaussian.PrefixNormal
      (List.finRange H.dimension).reverse H.effectiveGaussianState)
    (hunique : ∀ (first second : Fin H.rowCount × Fin H.dimension),
      first ∈ H.effectiveGaussianState.pivots →
      second ∈ H.effectiveGaussianState.pivots →
      first.1 = second.1 → first.2 = second.2)
    (bits : Fin H.dimension → ZMod 2) :
    H.effectiveGaussianState.system.check.mulVec bits = 0 ↔
      ∀ (pivotColumn : Fin H.dimension)
        (pivotRow : Fin H.rowCount),
        H.effectivePivotRowOption pivotColumn = some pivotRow →
          bits pivotColumn =
            ∑ column : Fin H.dimension,
              if H.effectivePivotRowOption column = none then
                H.effectiveGaussianState.system.check
                  pivotRow column * bits column
              else 0 := by
  classical
  constructor
  · intro hkernel pivotColumn pivotRow hpivot
    have hrow := congrFun hkernel pivotRow
    rw [H.effectiveReducedRow_mulVec
      hnormal hunique bits pivotColumn pivotRow hpivot] at hrow
    exact
      (effective_binary_add_eq_zero_iff_eq
        (bits pivotColumn)
        (∑ column : Fin H.dimension,
          if H.effectivePivotRowOption column = none then
            H.effectiveGaussianState.system.check
              pivotRow column * bits column
          else 0)).mp (by simpa only [Pi.zero_apply] using hrow)
  · intro hgraph
    funext row
    by_cases hrow : row.val < H.effectiveGaussianState.nextPivot
    · obtain ⟨pivotColumn, hpivotMem⟩ :=
        GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_complete hnormal row hrow
      have hpivot := H.effectivePivotRow_eq_some_of_mem
        hnormal pivotColumn row hpivotMem
      have hrowFormula := H.effectiveReducedRow_mulVec
        hnormal hunique bits pivotColumn row hpivot
      rw [hrowFormula, hgraph pivotColumn row hpivot]
      exact EffectiveBinaryGaussian.binary_add_self _
    · have hbelow :
          H.effectiveGaussianState.nextPivot ≤ row.val := by omega
      change
        (∑ column : Fin H.dimension,
          H.effectiveGaussianState.system.check row column *
            bits column) = 0
      apply Finset.sum_eq_zero
      intro column _
      have hzero := GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.scanned_lower_zero hnormal
        column (List.mem_reverse.mpr (List.mem_finRange column))
        row hbelow
      simp only [hzero, zero_mul]

/-- GapCVP reduction support. -/
def BinaryAffineSystem.effectiveFreeLiftSum
    (H : BinaryAffineSystem) (row : Fin H.rowCount)
    (z : Fin H.dimension → ℤ) : ℤ :=
  ∑ column : Fin H.dimension,
    if H.effectivePivotRowOption column = none then
      ((H.effectiveGaussianState.system.check row column).val : ℤ) *
        z column
    else 0

theorem BinaryAffineSystem.effectiveFreeLiftSum_cast
    (H : BinaryAffineSystem) (row : Fin H.rowCount)
    (z : Fin H.dimension → ℤ) :
    (H.effectiveFreeLiftSum row z : ZMod 2) =
      ∑ column : Fin H.dimension,
        if H.effectivePivotRowOption column = none then
          H.effectiveGaussianState.system.check row column *
            (z column : ZMod 2)
        else 0 := by
  classical
  unfold BinaryAffineSystem.effectiveFreeLiftSum
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro column _
  by_cases hpivot : H.effectivePivotRowOption column = none
  · simp only [hpivot, ↓reduceIte, Int.cast_mul]
    congr 1
    exact_mod_cast ZMod.natCast_zmod_val
      (H.effectiveGaussianState.system.check row column)
  · simp only [hpivot, ↓reduceIte, Int.cast_zero]

/-- GapCVP reduction support. -/
def BinaryAffineSystem.effectiveBasisCoefficients
    (H : BinaryAffineSystem)
    (z : Fin H.dimension → ℤ) : Fin H.dimension → ℤ :=
  fun column =>
    match H.effectivePivotRowOption column with
    | none => z column
    | some row =>
        (z column - H.effectiveFreeLiftSum row z) / 2

theorem BinaryAffineSystem.effectiveBasis_two_dvd_of_normal
    (H : BinaryAffineSystem)
    (hnormal : EffectiveBinaryGaussian.PrefixNormal
      (List.finRange H.dimension).reverse H.effectiveGaussianState)
    (hunique : ∀ (first second : Fin H.rowCount × Fin H.dimension),
      first ∈ H.effectiveGaussianState.pivots →
      second ∈ H.effectiveGaussianState.pivots →
      first.1 = second.1 → first.2 = second.2)
    (z : Fin H.dimension → ℤ) (hz : H.InLattice z)
    (column : Fin H.dimension) (row : Fin H.rowCount)
    (hpivot : H.effectivePivotRowOption column = some row) :
    (2 : ℤ) ∣ z column - H.effectiveFreeLiftSum row z := by
  have hkernel :=
    (H.effectiveGaussian_signedKernel_iff z).mpr hz
  have hgraph :=
    (H.effectiveGaussian_kernel_iff_graph_of_normal
      hnormal hunique (binaryResidue z)).mp hkernel
  have hbit := hgraph column row hpivot
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd
    (z column - H.effectiveFreeLiftSum row z) 2).mp
  rw [Int.cast_sub, H.effectiveFreeLiftSum_cast]
  apply sub_eq_zero.mpr
  exact hbit

private theorem pairwise_pivot_rows_unique
    {m n : ℕ} (pivots : List (Fin m × Fin n))
    (hpairwise : pivots.Pairwise (fun p q => p.1 ≠ q.1))
    (first second : Fin m × Fin n)
    (hfirst : first ∈ pivots) (hsecond : second ∈ pivots)
    (hrow : first.1 = second.1) :
    first.2 = second.2 := by
  induction pivots generalizing first second with
  | nil => simp only [List.not_mem_nil] at hfirst
  | cons head rest ih =>
      have hp := List.pairwise_cons.mp hpairwise
      rcases List.mem_cons.mp hfirst with hfirst | hfirst
      · subst first
        rcases List.mem_cons.mp hsecond with hsecond | hsecond
        · subst second
          rfl
        · exact (hp.1 second hsecond hrow).elim
      · rcases List.mem_cons.mp hsecond with hsecond | hsecond
        · subst second
          exact (hp.1 first hfirst hrow.symm).elim
        · exact ih hp.2 first second hfirst hsecond hrow

theorem BinaryAffineSystem.effectiveBasis_mulVec_coefficients_of_normal
    (H : BinaryAffineSystem)
    (hnormal : EffectiveBinaryGaussian.PrefixNormal
      (List.finRange H.dimension).reverse H.effectiveGaussianState)
    (hunique : ∀ (first second : Fin H.rowCount × Fin H.dimension),
      first ∈ H.effectiveGaussianState.pivots →
      second ∈ H.effectiveGaussianState.pivots →
      first.1 = second.1 → first.2 = second.2)
    (z : Fin H.dimension → ℤ) (hz : H.InLattice z) :
    H.effectiveSquareBasisMatrix.mulVec
      (H.effectiveBasisCoefficients z) = z := by
  classical
  funext row
  cases hrow : H.effectivePivotRowOption row with
  | none =>
      rw [H.effectiveSquareBasisMatrix_mulVec_free
        (H.effectiveBasisCoefficients z) row hrow]
      simp only [effectiveBasisCoefficients, hrow]
  | some pivot =>
      rw [H.effectiveSquareBasisMatrix_mulVec_pivot_full
        (H.effectiveBasisCoefficients z) row pivot hrow]
      have hsum :
          (∑ column : Fin H.dimension,
            if H.effectivePivotRowOption column = none then
              ((H.effectiveGaussianState.system.check
                pivot column).val : ℤ) *
                H.effectiveBasisCoefficients z column
            else 0) = H.effectiveFreeLiftSum pivot z := by
        unfold BinaryAffineSystem.effectiveFreeLiftSum
        apply Finset.sum_congr rfl
        intro column _
        by_cases hcolumn : H.effectivePivotRowOption column = none
        · simp only [hcolumn, ↓reduceIte, ZMod.natCast_val, effectiveBasisCoefficients]
        · simp only [hcolumn, ↓reduceIte]
      rw [hsum]
      have hcoefficient :
          H.effectiveBasisCoefficients z row =
            (z row - H.effectiveFreeLiftSum pivot z) / 2 := by
        simp only [effectiveBasisCoefficients, hrow]
      rw [hcoefficient]
      have hdvd := H.effectiveBasis_two_dvd_of_normal
        hnormal hunique z hz row pivot hrow
      have hdivision :
          2 * ((z row - H.effectiveFreeLiftSum pivot z) / 2) =
            z row - H.effectiveFreeLiftSum pivot z := by
        simpa only [mul_comm] using Int.ediv_mul_cancel hdvd
      rw [hdivision]
      omega

theorem BinaryAffineSystem.effectiveBasis_mulVec_mem_lattice_of_normal
    (H : BinaryAffineSystem)
    (hnormal : EffectiveBinaryGaussian.PrefixNormal
      (List.finRange H.dimension).reverse H.effectiveGaussianState)
    (hunique : ∀ (first second : Fin H.rowCount × Fin H.dimension),
      first ∈ H.effectiveGaussianState.pivots →
      second ∈ H.effectiveGaussianState.pivots →
      first.1 = second.1 → first.2 = second.2)
    (coefficients : Fin H.dimension → ℤ) :
    H.InLattice (H.effectiveSquareBasisMatrix.mulVec coefficients) := by
  apply
    (H.effectiveGaussian_signedKernel_iff
      (H.effectiveSquareBasisMatrix.mulVec coefficients)).mp
  apply
    (H.effectiveGaussian_kernel_iff_graph_of_normal
      hnormal hunique
      (binaryResidue
        (H.effectiveSquareBasisMatrix.mulVec coefficients))).mpr
  intro pivotColumn pivotRow hpivot
  have hvalue :
      H.effectiveSquareBasisMatrix.mulVec coefficients pivotColumn =
        H.effectiveFreeLiftSum pivotRow coefficients +
          2 * coefficients pivotColumn := by
    simpa only [effectiveFreeLiftSum, ZMod.natCast_val] using
        H.effectiveSquareBasisMatrix_mulVec_pivot_full coefficients pivotColumn pivotRow hpivot
  change
    ((H.effectiveSquareBasisMatrix.mulVec
      coefficients pivotColumn : ℤ) : ZMod 2) = _
  rw [hvalue, Int.cast_add, Int.cast_mul]
  have htwo : ((2 : ℤ) : ZMod 2) = 0 := by decide
  rw [htwo, zero_mul, add_zero,
    H.effectiveFreeLiftSum_cast]
  apply Finset.sum_congr rfl
  intro column _
  by_cases hcolumn : H.effectivePivotRowOption column = none
  · simp only [hcolumn, ↓reduceIte]
    congr 1
    change
      (coefficients column : ZMod 2) =
        ((H.effectiveSquareBasisMatrix.mulVec
          coefficients column : ℤ) : ZMod 2)
    rw [H.effectiveSquareBasisMatrix_mulVec_free
      coefficients column hcolumn]
  · simp only [hcolumn, ↓reduceIte]

theorem BinaryAffineSystem.inLattice_iff_exists_effectiveBasis_of_normal
    (H : BinaryAffineSystem)
    (hnormal : EffectiveBinaryGaussian.PrefixNormal
      (List.finRange H.dimension).reverse H.effectiveGaussianState)
    (hunique : ∀ (first second : Fin H.rowCount × Fin H.dimension),
      first ∈ H.effectiveGaussianState.pivots →
      second ∈ H.effectiveGaussianState.pivots →
      first.1 = second.1 → first.2 = second.2)
    (z : Fin H.dimension → ℤ) :
    H.InLattice z ↔
      ∃ coefficients : Fin H.dimension → ℤ,
        H.effectiveSquareBasisMatrix.mulVec coefficients = z := by
  constructor
  · intro hz
    exact ⟨H.effectiveBasisCoefficients z,
      H.effectiveBasis_mulVec_coefficients_of_normal
        hnormal hunique z hz⟩
  · rintro ⟨coefficients, rfl⟩
    exact H.effectiveBasis_mulVec_mem_lattice_of_normal
      hnormal hunique coefficients

theorem BinaryAffineSystem.effectivePivotRows_unique
    (H : BinaryAffineSystem)
    (first second : Fin H.rowCount × Fin H.dimension)
    (hfirst : first ∈ H.effectiveGaussianState.pivots)
    (hsecond : second ∈ H.effectiveGaussianState.pivots)
    (hrow : first.1 = second.1) : first.2 = second.2 := by
  apply pairwise_pivot_rows_unique
    H.effectiveGaussianState.pivots
    (EffectiveBinaryGaussian.eliminate_pivots_pairwise
      H.effectiveGaussianSystem)
    first second hfirst hsecond hrow

theorem BinaryAffineSystem.inLattice_iff_exists_effectiveSquareBasisMatrix
    (H : BinaryAffineSystem) (z : Fin H.dimension → ℤ) :
    H.InLattice z ↔
      ∃ coefficients : Fin H.dimension → ℤ,
        H.effectiveSquareBasisMatrix.mulVec coefficients = z := by
  exact H.inLattice_iff_exists_effectiveBasis_of_normal
    (EffectiveBinaryGaussian.eliminate_prefixNormal
      H.effectiveGaussianSystem)
    (fun first second hfirst hsecond hrow =>
      H.effectivePivotRows_unique
        first second hfirst hsecond hrow)
    z

/-- GapCVP reduction support. -/
def BinaryAffineSystem.effectiveReducedConsistent
    (H : BinaryAffineSystem) : Bool :=
  decide (∀ row : Fin H.rowCount,
    H.effectiveGaussianState.nextPivot ≤ row.val →
      H.effectiveGaussianState.system.rhs row = 0)

@[simp] theorem BinaryAffineSystem.effectiveReducedConsistent_iff
    (H : BinaryAffineSystem) :
    H.effectiveReducedConsistent = true ↔
      ∀ row : Fin H.rowCount,
        H.effectiveGaussianState.nextPivot ≤ row.val →
          H.effectiveGaussianState.system.rhs row = 0 := by
  simp only [effectiveReducedConsistent, decide_eq_true_eq]

theorem BinaryAffineSystem.effectiveAffineBits_satisfies
    (H : BinaryAffineSystem)
    (hconsistent : H.effectiveReducedConsistent = true) :
    H.effectiveGaussianState.system.Satisfies
      H.effectiveAffineBits := by
  simp only [GapCVP.Core.EffectiveBinaryGaussian.System.Satisfies, decide_eq_true_eq]
  classical
  have hnormal := EffectiveBinaryGaussian.eliminate_prefixNormal
    H.effectiveGaussianSystem
  have hunique :
      ∀ (first second : Fin H.rowCount × Fin H.dimension),
        first ∈ H.effectiveGaussianState.pivots →
        second ∈ H.effectiveGaussianState.pivots →
        first.1 = second.1 → first.2 = second.2 :=
    fun first second hfirst hsecond hrow =>
      H.effectivePivotRows_unique
        first second hfirst hsecond hrow
  have hlower :=
    H.effectiveReducedConsistent_iff.mp hconsistent
  funext row
  by_cases hrow : row.val < H.effectiveGaussianState.nextPivot
  · obtain ⟨pivotColumn, hmember⟩ :=
      GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.pivot_complete hnormal row hrow
    have hpivot := H.effectivePivotRow_eq_some_of_mem
      hnormal pivotColumn row hmember
    rw [H.effectiveReducedRow_mulVec
      hnormal hunique H.effectiveAffineBits pivotColumn row hpivot]
    have hsum :
        (∑ column : Fin H.dimension,
          if H.effectivePivotRowOption column = none then
            H.effectiveGaussianState.system.check row column *
              H.effectiveAffineBits column
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro column _
      by_cases hcolumn : H.effectivePivotRowOption column = none
      · simp only [hcolumn, ↓reduceIte, effectiveAffineBits, mul_zero]
      · simp only [hcolumn, ↓reduceIte]
    rw [hsum, add_zero]
    simp only [effectiveAffineBits, hpivot]
  · have hbelow : H.effectiveGaussianState.nextPivot ≤ row.val := by
      omega
    have hrhs : H.effectiveGaussianState.system.rhs row = 0 :=
      hlower row hbelow
    rw [hrhs]
    change
      (∑ column : Fin H.dimension,
        H.effectiveGaussianState.system.check row column *
          H.effectiveAffineBits column) = 0
    apply Finset.sum_eq_zero
    intro column _
    have hzero := GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.scanned_lower_zero hnormal
      column (List.mem_reverse.mpr (List.mem_finRange column))
      row hbelow
    rw [show H.effectiveGaussianState.system.check row column = 0
      from hzero, zero_mul]

theorem BinaryAffineSystem.effectiveAffineRepresentative_solves
    (H : BinaryAffineSystem)
    (hconsistent : H.effectiveReducedConsistent = true) :
    H.Solves H.effectiveAffineRepresentative := by
  apply
    (H.effectiveGaussian_solves_iff
      H.effectiveAffineRepresentative).mp
  rw [H.effectiveAffineRepresentative_residue]
  exact H.effectiveAffineBits_satisfies hconsistent

theorem BinaryAffineSystem.effectiveReducedConsistent_iff_solvable
    (H : BinaryAffineSystem) :
    H.effectiveReducedConsistent = true ↔
      ∃ z : Fin H.dimension → ℤ, H.Solves z := by
  constructor
  · intro hconsistent
    exact ⟨H.effectiveAffineRepresentative,
      H.effectiveAffineRepresentative_solves hconsistent⟩
  · rintro ⟨z, hz⟩
    apply H.effectiveReducedConsistent_iff.mpr
    intro row hbelow
    have hnormal := EffectiveBinaryGaussian.eliminate_prefixNormal
      H.effectiveGaussianSystem
    have hsolution :=
      (H.effectiveGaussian_solves_iff z).mpr hz
    have solution := hsolution
    simp only [GapCVP.Core.EffectiveBinaryGaussian.System.Satisfies,
      decide_eq_true_eq] at solution
    have hroweq := congrFun solution row
    have hzero :
        H.effectiveGaussianState.system.check.mulVec
          (binaryResidue z) row = 0 := by
      change
        (∑ column : Fin H.dimension,
          H.effectiveGaussianState.system.check row column *
            binaryResidue z column) = 0
      apply Finset.sum_eq_zero
      intro column _
      have hentry := GapCVP.Core.EffectiveBinaryGaussian.PrefixNormal.scanned_lower_zero hnormal
        column (List.mem_reverse.mpr (List.mem_finRange column))
        row hbelow
      rw [show H.effectiveGaussianState.system.check row column = 0
        from hentry, zero_mul]
    exact hroweq.symm.trans hzero

theorem effectiveConstructionAInstance_solution_coset
    (H : BinaryAffineSystem)
    (hconsistent : H.effectiveReducedConsistent = true)
    (z : Fin H.dimension → ℤ) :
    H.Solves (H.effectiveAffineRepresentative - z) ↔
      ∃ coefficients : Fin H.dimension → ℤ,
        H.effectiveSquareBasisMatrix.mulVec coefficients = z := by
  rw [H.solves_sub_iff_inLattice
    (H.effectiveAffineRepresentative_solves hconsistent)]
  exact H.inLattice_iff_exists_effectiveSquareBasisMatrix z

private theorem effectiveConstructionAInstance_squaredDistance_eq_integerSquaredNorm
    (H : BinaryAffineSystem) (hdimension : 0 < H.dimension)
    (v : Fin H.dimension → ℤ)
    (radius : ℚ) (hradius : 0 < radius)
    (coefficients : Fin H.dimension → ℤ)
    (hcoefficients :
      H.effectiveSquareBasisMatrix.mulVec coefficients =
        H.effectiveAffineRepresentative - v) :
    squaredDistance
      (effectiveConstructionAInstance H hdimension radius hradius)
        coefficients = (integerSquaredNorm v : ℝ) := by
  classical
  unfold squaredDistance integerSquaredNorm
  change
    (∑ i : Fin H.dimension,
      (((H.effectiveAffineRepresentative i : ℚ) : ℝ) -
        ∑ j : Fin H.dimension,
          (H.effectiveSquareBasisMatrix i j : ℝ) *
            (coefficients j : ℝ)) ^ 2) =
      ((∑ i : Fin H.dimension, (v i).natAbs ^ 2 : ℕ) : ℝ)
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  have hrow :
      (∑ j : Fin H.dimension,
        (H.effectiveSquareBasisMatrix i j : ℝ) *
          (coefficients j : ℝ)) =
        ((H.effectiveAffineRepresentative i - v i : ℤ) : ℝ) := by
    have hinteger := congrFun hcoefficients i
    change
      (∑ j : Fin H.dimension,
        H.effectiveSquareBasisMatrix i j * coefficients j) =
        H.effectiveAffineRepresentative i - v i at hinteger
    exact_mod_cast hinteger
  rw [hrow]
  have habs : ((v i).natAbs : ℝ) = |(v i : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun value : ℤ => (value : ℝ))
        (Int.natCast_natAbs (v i))
  have hnorm :
      ((v i).natAbs : ℝ) ^ 2 = (v i : ℝ) ^ 2 := by
    rw [habs, sq_abs]
  rw [hnorm, Int.cast_sub]
  ring

private theorem effectiveConstructionAInstance_squaredYes_iff_signedSolution
    (H : BinaryAffineSystem) (hdimension : 0 < H.dimension)
    (hconsistent : H.effectiveReducedConsistent = true)
    (radius : ℚ) (hradius : 0 < radius) :
    SquaredYes (effectiveConstructionAInstance H hdimension radius hradius) ↔
      ∃ v : Fin H.dimension → ℤ, H.Solves v ∧
        (integerSquaredNorm v : ℝ) ≤ (radius : ℝ) ^ 2 := by
  simp only [GapCVP.Core.SquaredYes, decide_eq_true_eq] at *
  constructor
  · rintro ⟨coefficients, hshort⟩
    let v := H.effectiveAffineRepresentative -
      H.effectiveSquareBasisMatrix.mulVec coefficients
    have hv : H.Solves v := by
      apply (effectiveConstructionAInstance_solution_coset
        H hconsistent
        (H.effectiveSquareBasisMatrix.mulVec coefficients)).mpr
      exact ⟨coefficients, rfl⟩
    refine ⟨v, hv, ?_⟩
    have hbasis :
        H.effectiveSquareBasisMatrix.mulVec coefficients =
          H.effectiveAffineRepresentative - v := by
      dsimp [v]
      rw [sub_sub_cancel]
    rw [← effectiveConstructionAInstance_squaredDistance_eq_integerSquaredNorm
      H hdimension v radius hradius coefficients hbasis]
    exact hshort
  · rintro ⟨v, hv, hshort⟩
    have hcoset :
        H.Solves
          (H.effectiveAffineRepresentative -
            (H.effectiveAffineRepresentative - v)) := by
      simpa only [sub_sub_cancel] using hv
    obtain ⟨coefficients, hcoefficients⟩ :=
      (effectiveConstructionAInstance_solution_coset H hconsistent
        (H.effectiveAffineRepresentative - v)).mp hcoset
    refine ⟨coefficients, ?_⟩
    rw [effectiveConstructionAInstance_squaredDistance_eq_integerSquaredNorm
      H hdimension v radius hradius coefficients hcoefficients]
    exact hshort

private theorem squaredYes_of_metricYes
    (I : GapCVPInstance) (hyes : I.IsYes) :
    SquaredYes I := by
  simp only [GapCVP.Core.SquaredYes, GapCVP.Core.GapCVPInstance.IsYes, decide_eq_true_eq] at *
  obtain ⟨coefficients, hnearest⟩ :=
    exists_latticePoint_eq_latticeDistance I
  refine ⟨coefficients, ?_⟩
  rw [squaredDistance_eq_dist_sq]
  change I.latticeDistance ≤ (I.radius : ℝ) at hyes
  rw [hnearest] at hyes
  nlinarith [dist_nonneg (x := I.targetPoint)
    (y := I.latticePoint coefficients)]

theorem effectiveConstructionAInstance_yes_iff_signedSolution
    (H : BinaryAffineSystem) (hdimension : 0 < H.dimension)
    (hconsistent : H.effectiveReducedConsistent = true)
    (radius : ℚ) (hradius : 0 < radius) :
    (effectiveConstructionAInstance H hdimension radius hradius).IsYes ↔
      ∃ v : Fin H.dimension → ℤ, H.Solves v ∧
        (integerSquaredNorm v : ℝ) ≤ (radius : ℝ) ^ 2 := by
  constructor
  · intro hyes
    exact
      (effectiveConstructionAInstance_squaredYes_iff_signedSolution
        H hdimension hconsistent radius hradius).mp
        (squaredYes_of_metricYes _ hyes)
  · intro hsolution
    apply yes_of_squaredYes
    exact
      (effectiveConstructionAInstance_squaredYes_iff_signedSolution
        H hdimension hconsistent radius hradius).mpr hsolution

private theorem effectiveConstructionAInstance_squaredNoAt_iff_signedSolutionNorm
    (H : BinaryAffineSystem) (hdimension : 0 < H.dimension)
    (hconsistent : H.effectiveReducedConsistent = true)
    (radius : ℚ) (hradius : 0 < radius) (exponent : ℝ) :
    SquaredNoAt exponent
        (effectiveConstructionAInstance H hdimension radius hradius) ↔
      ∀ v : Fin H.dimension → ℤ, H.Solves v →
        (((H.dimension : ℝ) ^ exponent) * (radius : ℝ)) ^ 2 <
          (integerSquaredNorm v : ℝ) := by
  simp only [GapCVP.Core.SquaredNoAt, decide_eq_true_eq] at *
  constructor
  · intro hno v hv
    have hcoset :
        H.Solves
          (H.effectiveAffineRepresentative -
            (H.effectiveAffineRepresentative - v)) := by
      simpa only [sub_sub_cancel] using hv
    obtain ⟨coefficients, hcoefficients⟩ :=
      (effectiveConstructionAInstance_solution_coset H hconsistent
        (H.effectiveAffineRepresentative - v)).mp hcoset
    calc
      (((H.dimension : ℝ) ^ exponent) * (radius : ℝ)) ^ 2 <
          squaredDistance
            (effectiveConstructionAInstance H hdimension radius hradius)
              coefficients := hno coefficients
      _ = (integerSquaredNorm v : ℝ) :=
        effectiveConstructionAInstance_squaredDistance_eq_integerSquaredNorm
          H hdimension v radius hradius coefficients hcoefficients
  · intro hno coefficients
    let v := H.effectiveAffineRepresentative -
      H.effectiveSquareBasisMatrix.mulVec coefficients
    have hv : H.Solves v := by
      apply (effectiveConstructionAInstance_solution_coset H hconsistent
        (H.effectiveSquareBasisMatrix.mulVec coefficients)).mpr
      exact ⟨coefficients, rfl⟩
    have hbasis :
        H.effectiveSquareBasisMatrix.mulVec coefficients =
          H.effectiveAffineRepresentative - v := by
      dsimp [v]
      rw [sub_sub_cancel]
    calc
      (((H.dimension : ℝ) ^ exponent) * (radius : ℝ)) ^ 2 <
          (integerSquaredNorm v : ℝ) := hno v hv
      _ = squaredDistance
            (effectiveConstructionAInstance H hdimension radius hradius)
              coefficients :=
        (effectiveConstructionAInstance_squaredDistance_eq_integerSquaredNorm
          H hdimension v radius hradius coefficients hbasis).symm

theorem effectiveConstructionAInstance_no_iff_signedSolutionNorm
    (H : BinaryAffineSystem) (hdimension : 0 < H.dimension)
    (hconsistent : H.effectiveReducedConsistent = true)
    (radius : ℚ) (hradius : 0 < radius) (exponent : ℝ) :
    (effectiveConstructionAInstance H hdimension radius hradius).IsNo exponent ↔
      ∀ v : Fin H.dimension → ℤ, H.Solves v →
        (((H.dimension : ℝ) ^ exponent) * (radius : ℝ)) ^ 2 <
          (integerSquaredNorm v : ℝ) := by
  constructor
  · intro hno
    exact
      (effectiveConstructionAInstance_squaredNoAt_iff_signedSolutionNorm
        H hdimension hconsistent radius hradius exponent).mp
        (squaredNoAt_of_metricNo exponent _ hno)
  · intro hnorm
    apply no_of_squaredNoAt exponent
    exact
      (effectiveConstructionAInstance_squaredNoAt_iff_signedSolutionNorm
        H hdimension hconsistent radius hradius exponent).mpr hnorm

end

end Core

namespace Factor400BinaryPhysicalWorkers

open Turing GapCVP.SourceWholeOutputAssemblyTM GapCVP.CNFGuardedFiveFamilyTagDispatchTM

/-- GapCVP reduction support. -/
def factor400KeepFirstDropSecondWord : List Bool → List Bool
  | [] => []
  | marker :: remaining => marker :: remaining.tail

/-- GapCVP reduction support. -/
noncomputable def factor400KeepFirstDropSecondComputable :
    BitTM
      factor400KeepFirstDropSecondWord :=
  keepFirstDropSecondComputable

end Factor400BinaryPhysicalWorkers

namespace BinaryDimensionTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMachineCert GapCVP.SourceFormulaStructuralDecoder
open GapCVP.SourceVariableFormulaDecoder GapCVP.OutputPolynomialCompositionClosure
open GapCVP.OutputBoundedDependentRecordFold
open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM
open GapCVP.SourceAnchoredGridRecordFoldTM GapCVP.CNFBoundedRecordFoldTM
open GapCVP.CNFFlatPhysicalBinaryAppendTM GapCVP.Factor400BinarySourceTM

/-- GapCVP reduction support. -/
def sourceClauseCountUnary (input : List Bool) : List Bool :=
  ((variableClauseBodyOutput ∘ firstFieldSuffix) input).tail

/-- GapCVP reduction support. -/
noncomputable def sourceClauseCountUnaryComputable :
    BitTM
      sourceClauseCountUnary := by
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    variableFormulaBodyComputable dropHeadComputable
  change
    BitTM
      (fun input : List Bool =>
        ((variableClauseBodyOutput ∘ firstFieldSuffix) input).tail)
  exact hphysical

@[simp] theorem sourceClauseCountUnary_valid
    (formula : ThreeCNF) :
    sourceClauseCountUnary (encodeThreeCNF formula) =
  List.replicate formula.length true := by
  simp only [sourceClauseCountUnary, Function.comp_apply, firstFieldSuffix_encodeThreeCNF,
      variableClauseBodyOutput_valid, List.tail_cons]

/-- GapCVP reduction support. -/
def sourceInputLengthUnary (input : List Bool) : List Bool :=
  List.replicate input.length true

/-- GapCVP reduction support. -/
noncomputable def sourceInputLengthUnaryComputable :
    BitTM
      sourceInputLengthUnary := by
  have hphysical := polynomialValueUnaryComputable Polynomial.X
  change
    BitTM
      (fun input : List Bool => List.replicate input.length true)
  simpa only [Polynomial.eval_X] using hphysical

private def doublingAccumulator (input : List Bool) : List Bool :=
  firstFieldContents input

private noncomputable def doublingAccumulatorComputable :
    BitTM
      doublingAccumulator :=
  firstFieldContentsComputable

private def doublingTarget (input : List Bool) : List Bool :=
  firstFieldContents (firstFieldSuffix input)

private noncomputable def doublingTargetComputable :
    BitTM
      doublingTarget :=
  GapCVP.TMComposition.computableInPolyTime
    firstFieldSuffixComputable firstFieldContentsComputable

private def doublingLessMarker (input : List Bool) : List Bool :=
  fourFamilyComputedUnaryLessBitOutput
    doublingAccumulator doublingTarget input

private noncomputable def doublingLessMarkerComputable :
    BitTM
      doublingLessMarker :=
  fourFamilyComputedUnaryLessBitComputable
    doublingAccumulatorComputable doublingTargetComputable

@[simp] private theorem doublingLessMarker_length (input : List Bool) :
    (doublingLessMarker input).length = 1 :=
  fourFamilyComputedUnaryLessBitOutput_length
    doublingAccumulator doublingTarget input

private def doublingLessBit (input : List Bool) : Bool :=
  (doublingLessMarker input).headD false

private theorem doublingLessMarker_eq (input : List Bool) :
    doublingLessMarker input = [doublingLessBit input] := by
  have hlength := doublingLessMarker_length input
  cases hword : doublingLessMarker input with
  | nil => simp only [hword, List.length_nil, zero_ne_one] at hlength
  | cons bit remaining =>
      cases remaining with
      | nil => simp only [doublingLessBit, hword, List.headD_eq_head?_getD, List.head?_cons,
          Option.getD_some]
      | cons next tail => simp only [hword, List.length_cons, Nat.add_eq_right,
          Nat.add_eq_zero_iff, List.length_eq_zero_iff,
                              one_ne_zero, and_false] at hlength

private noncomputable def doublingLessSelectionComputable :
    BitTM
      (fun input : List Bool => doublingLessBit input :: input) := by
  have hphysical := pointwiseAppendComputable
    doublingLessMarkerComputable
    (Turing.idComputableInPolyTime bitEncoding)
  have heq :
      (fun input : List Bool =>
        doublingLessMarker input ++ input) =
      (fun input : List Bool => doublingLessBit input :: input) := by
    funext input
    simp only [doublingLessMarker_eq, List.cons_append, List.nil_append]
  change
    BitTM
      (fun input : List Bool => doublingLessMarker input ++ input)
    at hphysical
  rwa [heq] at hphysical

private def doublingExtra (input : List Bool) : List Bool :=
  if doublingLessBit input then doublingAccumulator input else []

private noncomputable def doublingExtraComputable :
    BitTM
      doublingExtra :=
  sourcePreservingConditionalComputable
    doublingLessSelectionComputable doublingAccumulatorComputable []

private def guardedDoublingCandidate (input : List Bool) : List Bool :=
  doublingAccumulator input ++ doublingExtra input

private noncomputable def guardedDoublingCandidateComputable :
    BitTM
      guardedDoublingCandidate :=
  pointwiseAppendComputable
    doublingAccumulatorComputable doublingExtraComputable

private def nextPowerStep (target current : ℕ) : ℕ :=
  if current < target then 2 * current else current

private theorem guardedDoublingCandidate_valid
    (current target : ℕ) (padding : List Bool) :
    guardedDoublingCandidate
      (lengthPrefixedWord (List.replicate current true) ++
        lengthPrefixedWord (List.replicate target true) ++ padding) =
      List.replicate (nextPowerStep target current) true := by
  have hacc :
      doublingAccumulator
        (lengthPrefixedWord (List.replicate current true) ++
          lengthPrefixedWord (List.replicate target true) ++ padding) =
        List.replicate current true := by
    simpa only [doublingAccumulator, List.append_assoc] using
      firstFieldContents_valid
        (List.replicate current true)
        (lengthPrefixedWord (List.replicate target true) ++ padding)
  have htarget :
      doublingTarget
        (lengthPrefixedWord (List.replicate current true) ++
          lengthPrefixedWord (List.replicate target true) ++ padding) =
        List.replicate target true := by
    change firstFieldContents
      (firstFieldSuffix
        (lengthPrefixedWord (List.replicate current true) ++
          lengthPrefixedWord (List.replicate target true) ++ padding)) = _
    rw [List.append_assoc, firstFieldSuffix_valid
      (List.replicate current true)
      (lengthPrefixedWord (List.replicate target true) ++ padding)]
    exact firstFieldContents_valid
      (List.replicate target true) padding
  have hmarker :
      doublingLessMarker
        (lengthPrefixedWord (List.replicate current true) ++
          lengthPrefixedWord (List.replicate target true) ++ padding) =
        [decide (current < target)] := by
    exact fourFamilyComputedUnaryLessBitOutput_valid
      doublingAccumulator doublingTarget _ current target hacc htarget
  unfold guardedDoublingCandidate doublingExtra
  rw [hacc]
  have hbit :
      doublingLessBit
        (lengthPrefixedWord (List.replicate current true) ++
          lengthPrefixedWord (List.replicate target true) ++ padding) =
        decide (current < target) := by
    change
      (doublingLessMarker
        (lengthPrefixedWord (List.replicate current true) ++
          lengthPrefixedWord (List.replicate target true) ++
            padding)).headD false = _
    rw [hmarker]
    rfl
  rw [hbit]
  by_cases hlt : current < target
  · have hdouble : current + current = 2 * current := by omega
    simp only [hlt, decide_true, ite_true,
      nextPowerStep, List.replicate_append_replicate, hdouble]
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil, nextPowerStep]

private theorem nextPowerStep_le_two_mul
    (target current : ℕ) (hcurrent : current ≤ 2 * target) :
    nextPowerStep target current ≤ 2 * target := by
  unfold nextPowerStep
  split <;> omega

private def nextPowerAnchor (target : List Bool) : List Bool :=
  lengthPrefixedWord target ++ target ++ target

private noncomputable def nextPowerAnchorComputable
    {target : List Bool → List Bool}
    (computer : BitTM target) :
    BitTM
      (fun input => nextPowerAnchor (target input)) := by
  have hprefix := GapCVP.TMComposition.computableInPolyTime
    computer CLStructuralPrefixWriter.structuralPrefixWriterComputable
  have hphysical := pointwiseAppendComputable hprefix
    (pointwiseAppendComputable computer computer)
  change
    BitTM
      (fun input : List Bool =>
        lengthPrefixedWord (target input) ++
          target input ++ target input)
  simpa only [Function.comp_apply, List.append_assoc] using hphysical

private theorem nextPowerRotation_step
    (target current : ℕ)
    (hcurrent : current ≤ 2 * target) :
    sourceAnchoredGridRecordRotationOutput guardedDoublingCandidate
      (lengthPrefixedWord
          (nextPowerAnchor (List.replicate target true)) ++
        lengthPrefixedWord (List.replicate current true)) =
      lengthPrefixedWord
          (nextPowerAnchor (List.replicate target true)) ++
        lengthPrefixedWord
          (List.replicate (nextPowerStep target current) true) := by
  let anchor := nextPowerAnchor (List.replicate target true)
  let state :=
    lengthPrefixedWord anchor ++
      lengthPrefixedWord (List.replicate current true)
  have hraw :
      sourceAnchoredGridRawCandidate
        guardedDoublingCandidate state =
        List.replicate (nextPowerStep target current) true := by
    change
      guardedDoublingCandidate
        (sourceAnchoredGridRankSourcePair state) = _
    have hrank :
        firstFieldContents
          (lengthPrefixedWord (List.replicate current true)) =
          List.replicate current true := by
      simpa only [List.append_nil] using
        firstFieldContents_valid (List.replicate current true) []
    have hpair :
        sourceAnchoredGridRankSourcePair state =
          lengthPrefixedWord (List.replicate current true) ++ anchor := by
      simp only [state, sourceAnchoredGridRankSourcePair,
        firstFieldContents_valid, firstFieldSuffix_valid,
        hrank]
    rw [hpair]
    simpa only [anchor, nextPowerAnchor, List.append_assoc] using
      guardedDoublingCandidate_valid current target
        (List.replicate target true ++ List.replicate target true)
  have htarget :
      nextPowerStep target current ≤ 2 * target :=
    nextPowerStep_le_two_mul target current hcurrent
  have hfit :
      (List.replicate (nextPowerStep target current) true).length ≤
        anchor.length := by
    simp [anchor, nextPowerAnchor,
      lengthPrefixedWord_length]
    omega
  have hselector :
      sourceAnchoredGridCandidateSelector
        guardedDoublingCandidate state = true := by
    rw [sourceAnchoredGridCandidateSelector_eq, hraw]
    have hcontents : firstFieldContents state = anchor := by
      simp [state]
    rw [hcontents]
    exact decide_eq_true hfit
  have hguard :
      sourceAnchoredGridGuardedCandidate
        guardedDoublingCandidate state =
        List.replicate (nextPowerStep target current) true := by
    simp [sourceAnchoredGridGuardedCandidate,
      hselector, hraw]
  have hrotation :=
    sourceAnchoredGridRecordRotationOutput_records
      guardedDoublingCandidate anchor
      (List.replicate current true) []
  simpa [state, anchor, hguard] using hrotation

private theorem nextPowerRotation_iterate
    (target current stages : ℕ)
    (hcurrent : current ≤ 2 * target) :
    ((sourceAnchoredGridRecordRotationOutput
      guardedDoublingCandidate)^[stages])
        (lengthPrefixedWord
            (nextPowerAnchor (List.replicate target true)) ++
          lengthPrefixedWord (List.replicate current true)) =
      lengthPrefixedWord
          (nextPowerAnchor (List.replicate target true)) ++
        lengthPrefixedWord
          (List.replicate
            (((nextPowerStep target)^[stages]) current) true) := by
  induction stages generalizing current with
  | zero => simp
  | succ stages ih =>
      rw [Function.iterate_succ_apply,
        nextPowerRotation_step target current hcurrent,
        ih (nextPowerStep target current)
          (nextPowerStep_le_two_mul target current hcurrent),
        Function.iterate_succ_apply]

private theorem nextPowerStep_iterate
    (target stages : ℕ) :
    ((nextPowerStep target)^[stages]) 1 =
      2 ^ min stages (Nat.clog 2 target) := by
  induction stages with
  | zero => simp only [Function.iterate_zero, id_eq, zero_le, inf_of_le_left, pow_zero]
  | succ stages ih =>
      rw [Function.iterate_succ_apply', ih]
      by_cases hlt : stages < Nat.clog 2 target
      · have hpow : 2 ^ stages < target :=
          (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < (2 : ℕ))).mp hlt
        have hmin : min stages (Nat.clog 2 target) = stages :=
          Nat.min_eq_left (Nat.le_of_lt hlt)
        have hminnext :
            min (stages + 1) (Nat.clog 2 target) = stages + 1 :=
          Nat.min_eq_left (by omega)
        rw [hmin, hminnext]
        simp only [nextPowerStep, hpow, ↓reduceIte, pow_succ, Nat.mul_comm]
      · have hle : Nat.clog 2 target ≤ stages := by omega
        have hmin :
            min stages (Nat.clog 2 target) = Nat.clog 2 target :=
          Nat.min_eq_right hle
        have hminnext :
            min (stages + 1) (Nat.clog 2 target) =
              Nat.clog 2 target :=
          Nat.min_eq_right (by omega)
        have hbound : target ≤ 2 ^ Nat.clog 2 target :=
          Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) target
        rw [hmin, hminnext]
        simp only [nextPowerStep, Nat.not_lt_of_ge hbound, ↓reduceIte]

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  exact (Nat.lt_two_pow_self (n := n)).le

private theorem nextPowerStep_iterate_target (target : ℕ) :
    ((nextPowerStep target)^[target]) 1 =
      2 ^ Nat.clog 2 target := by
  rw [nextPowerStep_iterate]
  have hclog : Nat.clog 2 target ≤ target :=
    (Nat.clog_le_iff_le_pow
      (by norm_num : 1 < (2 : ℕ))).mpr (nat_le_two_pow target)
  rw [Nat.min_eq_right hclog]

private def nextPowerFoldPreparation
    (target : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  target input ++ false ::
    (lengthPrefixedWord (nextPowerAnchor (target input)) ++
      lengthPrefixedWord [true])

private noncomputable def nextPowerFoldPreparationComputable
    {target : List Bool → List Bool}
    (computer : BitTM target) :
    BitTM
      (nextPowerFoldPreparation target) := by
  have hanchor := GapCVP.TMComposition.computableInPolyTime
    (nextPowerAnchorComputable computer)
    CLStructuralPrefixWriter.structuralPrefixWriterComputable
  have hseed := pointwiseAppendComputable hanchor
    (SourceCanonicalFixedWordTuringTM.sourceFixedWordComputable
      (lengthPrefixedWord [true]))
  have hdelimited := GapCVP.TMComposition.computableInPolyTime
    hseed (prependBitComputable false)
  have hphysical := pointwiseAppendComputable computer hdelimited
  change
    BitTM
      (fun input : List Bool =>
        target input ++ false ::
          (lengthPrefixedWord (nextPowerAnchor (target input)) ++
            lengthPrefixedWord [true]))
  simpa only [Function.comp_apply] using hphysical

/-- GapCVP reduction support. -/
def nextPowerUnaryOutput
    (target : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  firstFieldContents
    (firstFieldSuffix
      (boundedRecordFoldOutput
        (sourceAnchoredGridRecordRotationOutput
          guardedDoublingCandidate)
        (nextPowerFoldPreparation target input)))

/-- GapCVP reduction support. -/
noncomputable def nextPowerUnaryComputable
    {target : List Bool → List Bool}
    (computer : BitTM target) :
    BitTM
      (nextPowerUnaryOutput target) := by
  have hprepared := GapCVP.TMComposition.computableInPolyTime
    (nextPowerFoldPreparationComputable computer)
    (sourceAnchoredGridRecordFoldComputable
      guardedDoublingCandidateComputable)
  have hdrop := GapCVP.TMComposition.computableInPolyTime
    hprepared firstFieldSuffixComputable
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    hdrop firstFieldContentsComputable
  change
    BitTM
      (fun input : List Bool =>
        firstFieldContents
          (firstFieldSuffix
            (boundedRecordFoldOutput
              (sourceAnchoredGridRecordRotationOutput
                guardedDoublingCandidate)
              (nextPowerFoldPreparation target input))))
  exact hphysical

theorem nextPowerUnaryOutput_valid
    (target : List Bool → List Bool)
    (input : List Bool) (n : ℕ)
    (htarget : target input = List.replicate n true)
    (hn : 0 < n) :
    nextPowerUnaryOutput target input =
      List.replicate (2 ^ Nat.clog 2 n) true := by
  unfold nextPowerUnaryOutput nextPowerFoldPreparation
  rw [htarget]
  change
    firstFieldContents
      (firstFieldSuffix
        (boundedRecordFoldOutput
          (sourceAnchoredGridRecordRotationOutput
            guardedDoublingCandidate)
          (unaryBoundedFoldWord n
            (lengthPrefixedWord
              (nextPowerAnchor (List.replicate n true)) ++
                lengthPrefixedWord [true])))) = _
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  have hone : 1 ≤ 2 * n := by omega
  change
    firstFieldContents
      (firstFieldSuffix
        (((sourceAnchoredGridRecordRotationOutput
          guardedDoublingCandidate)^[n])
          (lengthPrefixedWord
            (nextPowerAnchor (List.replicate n true)) ++
              lengthPrefixedWord (List.replicate 1 true)))) = _
  rw [nextPowerRotation_iterate n 1 n hone,
    nextPowerStep_iterate_target]
  rw [firstFieldSuffix_valid
    (nextPowerAnchor (List.replicate n true))
    (lengthPrefixedWord
      (List.replicate (2 ^ Nat.clog 2 n) true))]
  simpa only [List.append_nil] using
    firstFieldContents_valid
      (List.replicate (2 ^ Nat.clog 2 n) true) []

private def unarySubtractionPreparation
    (base subtract : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  subtract input ++ false :: base input

private noncomputable def unarySubtractionPreparationComputable
    {base subtract : List Bool → List Bool}
    (hbase : BitTM base)
    (hsubtract : BitTM subtract) :
    BitTM
      (unarySubtractionPreparation base subtract) := by
  have hdelimited := GapCVP.TMComposition.computableInPolyTime
    hbase (prependBitComputable false)
  have hphysical := pointwiseAppendComputable
    hsubtract hdelimited
  change
    BitTM
      (fun input : List Bool =>
        subtract input ++ false :: base input)
  exact hphysical

/-- GapCVP reduction support. -/
def unarySubtractionOutput
    (base subtract : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  boundedRecordFoldOutput List.tail
    (unarySubtractionPreparation base subtract input)

private theorem dropHead_nonexpansive (state : List Bool) :
    (state.tail).length ≤ state.length := by
  cases state <;> simp

/-- GapCVP reduction support. -/
noncomputable def unarySubtractionComputable
    {base subtract : List Bool → List Bool}
    (hbase : BitTM base)
    (hsubtract : BitTM subtract) :
    BitTM
      (unarySubtractionOutput base subtract) := by
  have hworker :=
    nonexpansiveBoundedWorkerComputable
      dropHeadComputable dropHead_nonexpansive
  have hphysical := GapCVP.TMComposition.computableInPolyTime
    (unarySubtractionPreparationComputable hbase hsubtract)
    hworker
  change
    BitTM
      (fun input : List Bool =>
        boundedRecordFoldOutput List.tail
          (unarySubtractionPreparation base subtract input))
  exact hphysical

private theorem tail_iterate_replicate
    (count length : ℕ) :
    ((List.tail^[count]) (List.replicate length true)) =
      List.replicate (length - count) true := by
  induction count generalizing length with
  | zero => simp only [Function.iterate_zero, id_eq, tsub_zero]
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih]
      cases hremaining : length - count with
      | zero =>
          have hle : length ≤ count :=
            Nat.sub_eq_zero_iff_le.mp hremaining
          have hnext : length - (count + 1) = 0 := by omega
          simp only [List.replicate_zero, List.tail_nil, hnext]
      | succ remaining =>
          have hnext : length - (count + 1) = remaining := by
            omega
          simp only [List.replicate_succ, List.tail_cons, hnext]

theorem unarySubtractionOutput_valid
    (base subtract : List Bool → List Bool)
    (input : List Bool) (first second : ℕ)
    (hbase : base input = List.replicate first true)
    (hsubtract : subtract input = List.replicate second true) :
    unarySubtractionOutput base subtract input =
      List.replicate (first - second) true := by
  unfold unarySubtractionOutput unarySubtractionPreparation
  rw [hbase, hsubtract]
  change
    boundedRecordFoldOutput List.tail
      (unaryBoundedFoldWord second
        (List.replicate first true)) = _
  simp only [boundedRecordFoldOutput, parseUnaryBoundedFold_word]
  exact tail_iterate_replicate second first

end BinaryDimensionTM

namespace SourceMixedRadixMaskSelectedSquareBasisIdentityAtomTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceFormulaStructuralDecoder
open GapCVP.CNFEncodedClauseSort GapCVP.CNFGuardedFiveFamilyTagDispatchTM

private def sourceQaryMaskSquarePairEqualityBit : List Bool → List Bool :=
  encodedOrderingEqualityBitWord ∘
    firstFieldSuffix ∘ sourcePreservingDelimitedPairComparisonWord

private noncomputable def sourceQaryMaskSquarePairEqualityBitComputable :
    BitTM
      sourceQaryMaskSquarePairEqualityBit := by
  have hcomparison := GapCVP.TMComposition.computableInPolyTime
    sourcePreservingDelimitedPairComparisonComputable
    firstFieldSuffixComputable
  exact GapCVP.TMComposition.computableInPolyTime
    hcomparison encodedOrderingEqualityBitComputable

private theorem sourceQaryMaskSquarePairEqualityBit_eq
    (input : List Bool) :
    sourceQaryMaskSquarePairEqualityBit input =
      [decide (delimitedPairWordOrdering input = .equal)] := by
  unfold sourceQaryMaskSquarePairEqualityBit
  simp only [Function.comp_apply, sourcePreservingDelimitedPairComparisonWord,
      firstFieldSuffix_valid,
      encodedOrderingEqualityBitWord_ordering]

private theorem sourceQaryMaskSquarePairEqualityBit_valid
    (first second original : List Bool) :
    sourceQaryMaskSquarePairEqualityBit
        (lengthPrefixedWord first ++
          lengthPrefixedWord second ++ original) =
      [decide (first = second)] := by
  rw [sourceQaryMaskSquarePairEqualityBit_eq,
    delimitedPairWordOrdering_valid]
  simp only [lexicographicEncodedWordOrdering_eq_equal_iff]

end SourceMixedRadixMaskSelectedSquareBasisIdentityAtomTM

namespace SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM

open Turing GapCVP.BinaryEncoding GapCVP.SourceMixedRadixMaskSelectedSquareBasisIdentityAtomTM
open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatPhysicalBinaryAppendTM

/-- GapCVP reduction support. -/
def maskComputedWordEquality
    (first second : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  sourceQaryMaskSquarePairEqualityBit
    (lengthPrefixedWord (first input) ++
      lengthPrefixedWord (second input))

/-- GapCVP reduction support. -/
noncomputable def maskComputedWordEqualityComputable
    {first second : List Bool → List Bool}
    (hfirst : BitTM first)
    (hsecond : BitTM second) :
    BitTM
      (maskComputedWordEquality first second) := by
  have hleft := GapCVP.TMComposition.computableInPolyTime
    hfirst structuralPrefixWriterComputable
  have hright := GapCVP.TMComposition.computableInPolyTime
    hsecond structuralPrefixWriterComputable
  exact GapCVP.TMComposition.computableInPolyTime
    (pointwiseAppendComputable hleft hright)
    sourceQaryMaskSquarePairEqualityBitComputable

@[simp] theorem sourceQaryMaskSquareComputedWordEquality_valid
    (first second : List Bool → List Bool)
    (input : List Bool) :
    maskComputedWordEquality first second input =
      [decide (first input = second input)] := by
  unfold maskComputedWordEquality
  simpa only [List.append_nil] using sourceQaryMaskSquarePairEqualityBit_valid (first input)
      (second input) []

end SourceMixedRadixMaskSelectedRankTaggedSquareBasisPairTM

end GapCVP

end
