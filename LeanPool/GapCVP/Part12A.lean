/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part11

/-! # GapCVP proof, part 12 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace FourFamilySoundness

open scoped BigOperators

open GapCVP.FormulaBridge GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinaryExplicitAffineSystem GapCVP.BinaryExplicitFourFamilyKernel
open GapCVP.BinaryExplicitSourceSoundness GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryDecodingPromiseReduction

/-- GapCVP reduction support. -/
noncomputable def paperVariableArityIntegerRadius
    (encodingLength : ℕ) (formula : ThreeCNF) : ℕ :=
  sourceBinaryDecodingRadius encodingLength
    (srcFormula formula)

theorem paperVariableArityIntegerRadius_pos
    (encodingLength : ℕ) (formula : ThreeCNF) :
    0 < paperVariableArityIntegerRadius encodingLength formula :=
  sourceBinaryDecodingRadius_pos encodingLength
    (srcFormula formula)

/-- Internal support shared across GapCVP continuation modules. -/
theorem paperVariableArityExplicitBinarySystem_oneHot_of_satisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (hsatisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    ∃ vector : Fin
        (sourceFormulaDimension encodingLength
          (srcFormula formula)) → ℤ,
      (paperExplicitBinarySystem
        encodingLength formula).Solves vector ∧
      (∀ index, vector index = 0 ∨ vector index = 1) ∧
      GapCVP.Core.integerSquaredNorm vector =
        paperVariableArityIntegerRadius encodingLength formula := by
  classical
  let F := srcFormula formula
  let points := sourceFormulaGrid encodingLength F
  have hformula : F.Satisfiable :=
    (sourceFormula_satisfiable_iff formula).mpr
      hsatisfiable
  simp only [GapCVP.Core.Formula.Satisfiable, decide_eq_true_eq] at hformula
  obtain ⟨assignment, hsatisfied⟩ := hformula
  obtain ⟨interpolant, hdegree, hinterpolant⟩ :=
    GapCVP.Core.exists_sourceSAT_assignment_interpolant_of_injective
      F (sourceFormulaVariablePlace encodingLength F)
      (sourceFormulaVariablePlace_injective encodingLength F) assignment
  let vector : Fin (sourceFormulaDimension encodingLength F) → ℤ :=
    GapCVP.Core.sourceOneHotSignedTable
      F points assignment hsatisfied interpolant
  have hcanonical :
      (sourceFormulaBinarySystem encodingLength F).Solves vector := by
    change
      (GapCVP.Core.concreteSATBinaryAffineSystem F
        (sourceFormulaFieldBasis encodingLength F)
        points (sourceFormulaVariablePlace encodingLength F)
        (GapCVP.Core.sourceSizeParameter encodingLength F ^ 30)).Solves
        vector
    apply GapCVP.Core.sourceOneHot_solves_concreteSATBinaryAffineSystem
      F (sourceFormulaFieldBasis encodingLength F)
      points (sourceFormulaVariablePlace encodingLength F)
      assignment hsatisfied interpolant hdegree hinterpolant
    intro point index
    exact GapCVP.Core.sourceSATPuncturedGrid_sub_ne_zero
      F (sourceFormulaVariablePlace encodingLength F) point index
  refine ⟨vector, ?_, ?_, ?_⟩
  · change (sourceFormulaExplicitBinarySystem
      encodingLength F).Solves vector
    apply (sourceFormulaExplicitBinarySystem_solves_iff_concreteSATFieldChecks
      encodingLength F vector).mpr
    exact (sourceFormulaBinarySystem_solves_iff
      encodingLength F vector).mp hcanonical
  · intro index
    exact sourceOneHotSignedTable_zero_or_one
      F points assignment hsatisfied interpolant index
  · change GapCVP.Core.integerSquaredNorm vector =
      (F.clauses.length + 1) * points.card
    exact GapCVP.Core.sourceOneHotSignedTable_squaredNorm
      F points assignment hsatisfied interpolant

/-- Internal support shared across GapCVP continuation modules. -/
theorem paperVariableArityExplicitBinarySystem_satisfiable_of_scaled_hamming
    (encodingLength : ℕ) (formula : ThreeCNF)
    (vector : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) → ℤ)
    (hsolve : (paperExplicitBinarySystem
      encodingLength formula).Solves vector)
    (hshort :
      (GapCVP.Core.integerSquaredNorm vector : ℝ) ≤
        2 * binaryCodeGapFactor
          (sourceFormulaDimension encodingLength
            (srcFormula formula)) *
          (paperVariableArityIntegerRadius
            encodingLength formula : ℝ)) :
    ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause := by
  let F := srcFormula formula
  apply (sourceFormula_satisfiable_iff formula).mp
  have hchecks :=
    (sourceFormulaExplicitBinarySystem_solves_iff_concreteSATFieldChecks
      encodingLength F vector).mp hsolve
  have hcanonical :
      (sourceFormulaBinarySystem encodingLength F).Solves vector :=
    (sourceFormulaBinarySystem_solves_iff
      encodingLength F vector).mpr hchecks
  apply sourceFormula_satisfiable_of_short_signed_solution
    encodingLength F vector hcanonical
  apply sourceBinaryDecoding_scaledNorm_support
    encodingLength F vector
  exact hshort

/-- Internal support shared across GapCVP continuation modules. -/
theorem paperVariableArityExplicitBinarySystem_strict_factor400_of_unsatisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (vector : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) → ℤ)
    (hsolve : (paperExplicitBinarySystem
      encodingLength formula).Solves vector)
    (hunsatisfiable :
      ¬ ∃ assignment : ℕ → Bool,
        ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    (GapCVP.SourceFactor400BinaryConstructionABounds.gapFactor400
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) *
      ((GapCVP.Core.sourceOneHotCompletenessRadius
        (srcFormula formula)
        (sourceFormulaGrid encodingLength
          (srcFormula formula)) : ℚ) : ℝ)) ^ 2 <
      (GapCVP.Core.integerSquaredNorm vector : ℝ) := by
  apply
    sourceFormulaExplicitBinarySystem_squaredNorm_gt_factor400_of_unsatisfiable
      encodingLength (srcFormula formula) vector hsolve
  intro hsatisfiable
  exact hunsatisfiable
    ((sourceFormula_satisfiable_iff formula).mp
      hsatisfiable)

end FourFamilySoundness

end GapCVP

end
