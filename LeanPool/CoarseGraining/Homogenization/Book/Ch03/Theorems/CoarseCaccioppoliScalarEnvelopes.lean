/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScaleZeroScalarBounds

/-! # Coarse Caccioppoli Scalar Envelopes -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Scalar envelopes for coarse Caccioppoli

This file contains the final scalar-envelope package used to upgrade
scale-zero explicit constants to the note-facing dimension-only constant.
-/

noncomputable section

open scoped ENNReal

/-- Scalar envelope needed to upgrade the scale-zero explicit bridge constants
to the note-facing dimension-only `C(d)`.  This is deliberately only a scalar
statement: all PDE and geometry work has already been discharged below this
surface. -/
structure CoarseCaccioppoliScaleZeroScalarEnvelope
    (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      (∀ {s t : ℝ}, 0 < s → 0 < t → s + t < 1 →
        boundaryCaccioppoliScaleZeroExplicitConstant d s t ≤ C) ∧
      (∀ {s t : ℝ}, 0 < s → 0 < t → s + t < 1 →
        interiorCaccioppoliScaleZeroExplicitConstant d s t ≤ C)

/-- The scale-zero scalar envelope is fully proved from the explicit split
`s,t` bookkeeping. -/
theorem coarseCaccioppoliScaleZeroScalarEnvelope
    (d : ℕ) [NeZero d] :
    CoarseCaccioppoliScaleZeroScalarEnvelope d where
  exists_constant := by
    refine ⟨caccioppoliScaleZeroScalarBound d, ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    · intro s t hs ht hst
      exact
        (boundaryCaccioppoliScaleZeroExplicitConstant_le_scalarBound
          (d := d) hs ht hst).trans
          ((le_max_left
            (boundaryCaccioppoliScaleZeroScalarBound d)
            (interiorCaccioppoliScaleZeroScalarBound d)).trans
            (le_max_right (1 : ℝ)
              (max (boundaryCaccioppoliScaleZeroScalarBound d)
                (interiorCaccioppoliScaleZeroScalarBound d))))
    · intro s t hs ht hst
      exact
        (interiorCaccioppoliScaleZeroExplicitConstant_le_scalarBound
          (d := d) hs ht hst).trans
          ((le_max_right
            (boundaryCaccioppoliScaleZeroScalarBound d)
            (interiorCaccioppoliScaleZeroScalarBound d)).trans
            (le_max_right (1 : ℝ)
              (max (boundaryCaccioppoliScaleZeroScalarBound d)
                (interiorCaccioppoliScaleZeroScalarBound d))))


end

end Ch03
end Book
end Homogenization
