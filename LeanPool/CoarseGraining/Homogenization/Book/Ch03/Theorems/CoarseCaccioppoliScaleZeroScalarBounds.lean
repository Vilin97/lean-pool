/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScaleZeroBudgetEnvelopes

/-! # Coarse Caccioppoli Scale Zero Scalar Bounds -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Scale-zero Caccioppoli scalar bounds

This file bounds the boundary and interior scale-zero explicit constants by
one dimension-only scalar bound.

## Audit tag

Claim: package the boundary and centered-interior explicit scale-zero constants
under one dimension-only scalar bound.

Downstream target: `CoarseCaccioppoliScaleZero.lean`.  This file should stay as
the scalar-bound endpoint for the scale-zero stack.
-/

noncomputable section

open scoped ENNReal

private noncomputable def caccioppoliScaleZeroEnvelopeBound
    (A X : ℝ) : ℝ :=
  36 * ((6561 : ℝ) * 6561 * X ^ (2 : ℕ)) +
    36 * Real.exp 1 * ((9 : ℝ) * 4 * 81 * X * X * A) + 1

noncomputable def boundaryCaccioppoliScaleZeroScalarBound
    (d : ℕ) [NeZero d] : ℝ :=
  (18 : ℝ) ^ d *
    caccioppoliScaleZeroEnvelopeBound
      (boundaryScaleZeroAlphaInternalEnvelope d)
      (boundaryScaleZeroCrossInternalEnvelope d)

noncomputable def interiorCaccioppoliScaleZeroScalarBound
    (d : ℕ) [NeZero d] : ℝ :=
  (18 : ℝ) ^ d *
    caccioppoliScaleZeroEnvelopeBound
      (interiorScaleZeroAlphaInternalEnvelope d)
      (interiorScaleZeroCrossInternalEnvelope d)

/-- A dimension-only scalar bound dominating both scale-zero bridge constants. -/
noncomputable def caccioppoliScaleZeroScalarBound
    (d : ℕ) [NeZero d] : ℝ :=
  max 1
    (max (boundaryCaccioppoliScaleZeroScalarBound d)
      (interiorCaccioppoliScaleZeroScalarBound d))

private theorem fin_card_real_ge_one (d : ℕ) [NeZero d] :
    (1 : ℝ) ≤ (Fintype.card (Fin d) : ℝ) := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hcard : 1 ≤ Fintype.card (Fin d) := by
    simpa [Fintype.card_fin] using! hd_pos
  exact_mod_cast hcard

private theorem one_le_mul_of_one_le_of_one_le {a b : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have ha_nonneg : 0 ≤ a := by linarith
  have hmul : (1 : ℝ) * 1 ≤ a * b :=
    mul_le_mul ha hb (by norm_num) ha_nonneg
  simpa using hmul

private theorem boundaryScaleZeroAlphaInternalEnvelope_ge_one
    (d : ℕ) [NeZero d] :
    1 ≤ boundaryScaleZeroAlphaInternalEnvelope d := by
  have hcard : (1 : ℝ) ≤ (Fintype.card (Fin d) : ℝ) :=
    fin_card_real_ge_one d
  have henv : 1 ≤ boundaryScaleZeroAlphaBudgetEnvelope d := by
    unfold boundaryScaleZeroAlphaBudgetEnvelope
    dsimp
    exact le_max_left _ _
  unfold boundaryScaleZeroAlphaInternalEnvelope
  exact one_le_mul_of_one_le_of_one_le hcard henv

private theorem interiorScaleZeroAlphaInternalEnvelope_ge_one
    (d : ℕ) [NeZero d] :
    1 ≤ interiorScaleZeroAlphaInternalEnvelope d := by
  have hcard : (1 : ℝ) ≤ (Fintype.card (Fin d) : ℝ) :=
    fin_card_real_ge_one d
  have henv : 1 ≤ interiorScaleZeroAlphaBudgetEnvelope d := by
    unfold interiorScaleZeroAlphaBudgetEnvelope
    dsimp
    exact le_max_left _ _
  unfold interiorScaleZeroAlphaInternalEnvelope
  exact one_le_mul_of_one_le_of_one_le hcard henv

private theorem boundaryScaleZeroCrossInternalEnvelope_ge_one
    (d : ℕ) [NeZero d] :
    1 ≤ boundaryScaleZeroCrossInternalEnvelope d := by
  have hcard : (1 : ℝ) ≤ (Fintype.card (Fin d) : ℝ) :=
    fin_card_real_ge_one d
  have henv : 1 ≤ boundaryScaleZeroCrossBudgetEnvelope d := by
    unfold boundaryScaleZeroCrossBudgetEnvelope
    dsimp
    exact le_max_left _ _
  unfold boundaryScaleZeroCrossInternalEnvelope
  exact one_le_mul_of_one_le_of_one_le hcard henv

private theorem interiorScaleZeroCrossInternalEnvelope_ge_one
    (d : ℕ) [NeZero d] :
    1 ≤ interiorScaleZeroCrossInternalEnvelope d := by
  have hcard : (1 : ℝ) ≤ (Fintype.card (Fin d) : ℝ) :=
    fin_card_real_ge_one d
  have henv : 1 ≤ interiorScaleZeroCrossBudgetEnvelope d := by
    unfold interiorScaleZeroCrossBudgetEnvelope
    dsimp
    exact le_max_left _ _
  unfold interiorScaleZeroCrossInternalEnvelope
  exact one_le_mul_of_one_le_of_one_le hcard henv

theorem boundaryCaccioppoliScaleZeroExplicitConstant_le_scalarBound
    {d : ℕ} [NeZero d] {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    boundaryCaccioppoliScaleZeroExplicitConstant d s t ≤
      boundaryCaccioppoliScaleZeroScalarBound d := by
  let A : ℝ := boundaryScaleZeroAlphaInternalEnvelope d
  let X : ℝ := boundaryScaleZeroCrossInternalEnvelope d
  have hA_ge_one : 1 ≤ A := by
    dsimp [A]
    exact boundaryScaleZeroAlphaInternalEnvelope_ge_one d
  have hX_ge_one : 1 ≤ X := by
    dsimp [X]
    exact boundaryScaleZeroCrossInternalEnvelope_ge_one d
  have hA_nonneg : 0 ≤ A := by linarith
  have hX_nonneg : 0 ≤ X := by linarith
  have hCalpha_nonneg : 0 ≤ A * s⁻¹ :=
    mul_nonneg hA_nonneg (inv_nonneg.mpr hs.le)
  have hnote :
      caccioppoliStandardExplicitNoteBoundSplit s t (A * s⁻¹) X ≤
        caccioppoliScaleZeroEnvelopeBound A X := by
    dsimp [caccioppoliScaleZeroEnvelopeBound]
    exact
      caccioppoliStandardExplicitNoteBoundSplit_le_envelope
        hs ht hst hCalpha_nonneg (le_rfl : A * s⁻¹ ≤ A * s⁻¹)
        hX_nonneg (le_rfl : X ≤ X) hA_ge_one hX_ge_one
  have hfactor_nonneg : 0 ≤ (18 : ℝ) ^ d :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 18) d
  calc
    boundaryCaccioppoliScaleZeroExplicitConstant d s t
        ≤ (18 : ℝ) ^ d *
            caccioppoliStandardExplicitNoteBoundSplit s t (A * s⁻¹) X := by
          dsimp [A, X]
          exact boundaryCaccioppoliScaleZeroExplicitConstant_le_envelopeExplicit
            hs ht hst
    _ ≤ (18 : ℝ) ^ d * caccioppoliScaleZeroEnvelopeBound A X :=
          mul_le_mul_of_nonneg_left hnote hfactor_nonneg
    _ = boundaryCaccioppoliScaleZeroScalarBound d := by
          dsimp [A, X, boundaryCaccioppoliScaleZeroScalarBound]

theorem interiorCaccioppoliScaleZeroExplicitConstant_le_scalarBound
    {d : ℕ} [NeZero d] {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    interiorCaccioppoliScaleZeroExplicitConstant d s t ≤
      interiorCaccioppoliScaleZeroScalarBound d := by
  let A : ℝ := interiorScaleZeroAlphaInternalEnvelope d
  let X : ℝ := interiorScaleZeroCrossInternalEnvelope d
  have hA_ge_one : 1 ≤ A := by
    dsimp [A]
    exact interiorScaleZeroAlphaInternalEnvelope_ge_one d
  have hX_ge_one : 1 ≤ X := by
    dsimp [X]
    exact interiorScaleZeroCrossInternalEnvelope_ge_one d
  have hA_nonneg : 0 ≤ A := by linarith
  have hX_nonneg : 0 ≤ X := by linarith
  have hCalpha_nonneg : 0 ≤ A * s⁻¹ :=
    mul_nonneg hA_nonneg (inv_nonneg.mpr hs.le)
  have hnote :
      caccioppoliStandardExplicitNoteBoundSplit s t (A * s⁻¹) X ≤
        caccioppoliScaleZeroEnvelopeBound A X := by
    dsimp [caccioppoliScaleZeroEnvelopeBound]
    exact
      caccioppoliStandardExplicitNoteBoundSplit_le_envelope
        hs ht hst hCalpha_nonneg (le_rfl : A * s⁻¹ ≤ A * s⁻¹)
        hX_nonneg (le_rfl : X ≤ X) hA_ge_one hX_ge_one
  have hfactor_nonneg : 0 ≤ (18 : ℝ) ^ d :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 18) d
  calc
    interiorCaccioppoliScaleZeroExplicitConstant d s t
        ≤ (18 : ℝ) ^ d *
            caccioppoliStandardExplicitNoteBoundSplit s t (A * s⁻¹) X := by
          dsimp [A, X]
          exact interiorCaccioppoliScaleZeroExplicitConstant_le_envelopeExplicit
            hs ht hst
    _ ≤ (18 : ℝ) ^ d * caccioppoliScaleZeroEnvelopeBound A X :=
          mul_le_mul_of_nonneg_left hnote hfactor_nonneg
    _ = interiorCaccioppoliScaleZeroScalarBound d := by
          dsimp [A, X, interiorCaccioppoliScaleZeroScalarBound]


end

end Ch03
end Book
end Homogenization
