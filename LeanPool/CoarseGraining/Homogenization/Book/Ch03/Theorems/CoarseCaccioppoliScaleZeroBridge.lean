/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScaleZeroRHS.Monotonicity
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScalarEnvelopes

/-! # Coarse Caccioppoli Scale Zero Bridge -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Scale-zero Caccioppoli public bridge estimates

This file assembles the scale-zero core estimates with the RHS bridge helpers
and explicit scalar envelope to produce the public scale-zero Caccioppoli
endpoint used by the dilation transport layer.

## Audit tag

Claim: bridge deterministic scale-zero core estimates and explicit scalar
budgets into the public boundary and centered-interior RHS forms.

Downstream target: `coarseCaccioppoliScaleZeroTheory_of_scalarEnvelope`.
This file is bridge plumbing only; it should not introduce another public
`*Theory` package.
-/

noncomputable section

open scoped ENNReal

private theorem boundary_publicCoreEnergy_le_eighteen_pow_mul_publicRHS_of_scale_zero_standardExplicitBudgetSplit
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hx : x ∈ openCubeSet Q) (hQscale : Q.scale = 0) :
    let CalphaInternal : ℝ :=
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s
    let CcrossInternal : ℝ :=
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s
    let Cnote : ℝ :=
      coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
        Q (pointwiseCoeffFor Q a) s t CalphaInternal CcrossInternal
    0 ≤ Cnote ∧
      boundaryCaccioppoliCoreEnergy u ≤
        (18 : ℝ) ^ d *
          boundaryCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * Cnote) s t u := by
  let CsolQ : ℝ := fullVectorPoincareCubeConstant Q
  let CalphaQ : ℝ := coarseCaccioppoliLocalPatchBufferedAlphaBudget Q s CsolQ
  let CcrossQ : ℝ := coarseCaccioppoliLocalPatchBufferedCrossBudget Q s CsolQ
  let CalphaInternalQ : ℝ := (Fintype.card (Fin d) : ℝ) * CalphaQ
  let CcrossInternalQ : ℝ := (Fintype.card (Fin d) : ℝ) * CcrossQ
  let CnoteQ : ℝ :=
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
      Q (pointwiseCoeffFor Q a) s t CalphaInternalQ CcrossInternalQ
  have hdet_full :=
    boundary_localPatch_deterministic_note_from_public_standardExplicitBudgetSplit
      (Q := Q) (a := a) (x := x) u hs ht hst
  have hdet :
      0 ≤ CnoteQ ∧
        coarseCaccioppoliLocalEnergyRadiusProfile Q x
            (fun y =>
              scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
                u.toPointwiseAHarmonic y) (1 / 3 : ℝ) ≤
          coarseCaccioppoliBoundaryNoteRhs Q (pointwiseCoeffFor Q a) s t CnoteQ
            (coarseCaccioppoliHarmonicL2Sq Q (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic) := by
    simpa [CsolQ, CalphaQ, CcrossQ, CalphaInternalQ, CcrossInternalQ, CnoteQ]
      using hdet_full
  rcases hdet with ⟨hCnote, hdet_bound⟩
  have hgeom :=
    boundaryCaccioppoliCoreEnergy_le_eighteen_pow_mul_localEnergyRadiusProfile
      u hx
  have hfactor_nonneg : 0 ≤ (18 : ℝ) ^ d :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 18) d
  have hconvert :
      coarseCaccioppoliBoundaryNoteRhs Q (pointwiseCoeffFor Q a) s t CnoteQ
          (boundaryCaccioppoliParentL2Sq u) ≤
        boundaryCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * CnoteQ) s t u :=
    deterministic_boundaryNoteRhs_pointwiseCoeffFor_le_publicRHS_dim_sq_mul_of_scale_zero
      (Q := Q) (a := a) (x := x) u (s := s) (t := t) (C := CnoteQ)
      hs ht hst hCnote hQscale
  have hbound :
      boundaryCaccioppoliCoreEnergy u ≤
        (18 : ℝ) ^ d *
          boundaryCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * CnoteQ) s t u := by
    calc
      boundaryCaccioppoliCoreEnergy u ≤
          (18 : ℝ) ^ d *
            coarseCaccioppoliLocalEnergyRadiusProfile Q x
              (fun y =>
                scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
                  u.toPointwiseAHarmonic y) ((3 : ℝ)⁻¹) := hgeom
      _ =
          (18 : ℝ) ^ d *
            coarseCaccioppoliLocalEnergyRadiusProfile Q x
              (fun y =>
                scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
                  u.toPointwiseAHarmonic y) (1 / 3 : ℝ) := by
        simp [one_div]
      _ ≤
          (18 : ℝ) ^ d *
            coarseCaccioppoliBoundaryNoteRhs Q (pointwiseCoeffFor Q a) s t CnoteQ
              (coarseCaccioppoliHarmonicL2Sq Q (pointwiseCoeffFor Q a)
                u.toPointwiseAHarmonic) := by
        exact mul_le_mul_of_nonneg_left hdet_bound hfactor_nonneg
      _ =
          (18 : ℝ) ^ d *
            coarseCaccioppoliBoundaryNoteRhs Q (pointwiseCoeffFor Q a) s t CnoteQ
              (boundaryCaccioppoliParentL2Sq u) := by
        rw [boundaryCaccioppoliParentL2Sq_eq_harmonicL2Sq_pointwise u]
      _ ≤
          (18 : ℝ) ^ d *
            boundaryCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * CnoteQ) s t u := by
        exact mul_le_mul_of_nonneg_left hconvert hfactor_nonneg
  have halpha :
      CalphaQ = coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s := by
    simpa [CalphaQ, CsolQ] using
      coarseCaccioppoliLocalPatchBufferedAlphaBudget_eq_unit_of_scale_eq_zero
        (Q := Q) s hQscale
  have hcross :
      CcrossQ = coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s := by
    simpa [CcrossQ, CsolQ] using
      coarseCaccioppoliLocalPatchBufferedCrossBudget_eq_unit_of_scale_eq_zero
        (Q := Q) s hQscale
  simpa [CalphaQ, CcrossQ, CalphaInternalQ, CcrossInternalQ, CnoteQ, halpha, hcross]
    using And.intro hCnote hbound

private theorem interior_centered_publicCoreEnergy_le_eighteen_pow_mul_publicRHS_of_scale_zero_standardExplicitBudgetSplit
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    (u : CubeSolution Q a) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hQscale : Q.scale = 0) :
    let CalphaInternal : ℝ :=
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedAlphaBudgetUnit d s
    let CcrossInternal : ℝ :=
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedCrossBudgetUnit d s
    let Cnote : ℝ :=
      coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
        Q (pointwiseCoeffFor Q a) s t CalphaInternal CcrossInternal
    0 ≤ Cnote ∧
      interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
        (18 : ℝ) ^ d *
          interiorCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * Cnote) Q a s t u := by
  let CsolQ : ℝ := fullVectorPoincareCubeConstant Q
  let CalphaQ : ℝ := coarseCaccioppoliBufferedAlphaBudget Q s CsolQ
  let CcrossQ : ℝ := coarseCaccioppoliBufferedCrossBudget Q s CsolQ
  let CalphaInternalQ : ℝ := (Fintype.card (Fin d) : ℝ) * CalphaQ
  let CcrossInternalQ : ℝ := (Fintype.card (Fin d) : ℝ) * CcrossQ
  let CnoteQ : ℝ :=
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
      Q (pointwiseCoeffFor Q a) s t CalphaInternalQ CcrossInternalQ
  have hdet_full :=
    interior_centered_deterministic_note_from_public_oscillation_standardExplicitBudgetSplit
      (Q := Q) (a := a) u hs ht hst
  have hdet :
      0 ≤ CnoteQ ∧
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q
            (fun y =>
              scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
                u.toPointwiseAHarmonic y) (1 / 3 : ℝ) ≤
          coarseCaccioppoliInteriorNoteRhs Q (pointwiseCoeffFor Q a) s t CnoteQ
            (interiorCaccioppoliParentOscillationL2Sq Q a u) := by
    simpa [CsolQ, CalphaQ, CcrossQ, CalphaInternalQ, CcrossInternalQ, CnoteQ]
      using hdet_full
  rcases hdet with ⟨hCnote, hdet_bound⟩
  have hgeom :=
    interiorCaccioppoliCoreEnergy_le_eighteen_pow_mul_localEnergyRadiusProfile
      (Q := Q) (a := a) (x := cubeCenter Q) u (cubeCenter_mem_openCubeSet Q)
  let A : CoeffField d := pointwiseCoeffFor Q a
  let uPw : AHarmonicFunction A (openCubeSet Q) := u.toPointwiseAHarmonic
  let energy : Vec d → ℝ := fun y => scalarVariationEnergyIntegrand A uPw y
  have hctrl :
      CoarseCaccioppoliFluxEnergyControls Q A (1 : ℝ)
        (fun y => matVecMul (A y) (uPw.toCubeSet.toH1.grad y))
        (fun y => scalarVariationEnergyIntegrand A uPw.toCubeSet y) :=
    CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
      (Q := Q) (a := A) (s := (1 : ℝ)) (by norm_num)
      (pointwiseCoeffFor_isEllipticFieldOn_cubeSet Q a) uPw.toCubeSet
  have henergy_nonneg : ∀ y ∈ cubeSet Q, 0 ≤ energy y := by
    intro y hy
    simpa [energy, A, uPw, scalarVariationEnergyIntegrand] using hctrl.1 y hy
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume := by
    simpa [energy, A, uPw, scalarVariationEnergyIntegrand] using hctrl.2.1
  have hlocal_le :
      coarseCaccioppoliLocalEnergyRadiusProfile Q (cubeCenter Q)
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) (1 / 3 : ℝ) ≤
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q
          (fun y =>
            scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
              u.toPointwiseAHarmonic y) (1 / 3 : ℝ) := by
    simpa [energy, A, uPw] using
      coarseCaccioppoliLocalEnergyRadiusProfile_cubeCenter_one_third_le_localizedEnergyRadiusProfile
        (Q := Q) henergy_nonneg henergy_int
  have hfactor_nonneg : 0 ≤ (18 : ℝ) ^ d :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 18) d
  have hconvert :
      coarseCaccioppoliInteriorNoteRhs Q (pointwiseCoeffFor Q a) s t CnoteQ
          (interiorCaccioppoliParentOscillationL2Sq Q a u) ≤
        interiorCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * CnoteQ) Q a s t u :=
    deterministic_interiorNoteRhs_pointwiseCoeffFor_le_publicRHS_dim_sq_mul_of_scale_zero
      (Q := Q) (a := a) u (s := s) (t := t) (C := CnoteQ)
      hs ht hst hCnote hQscale
  have hbound :
      interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
        (18 : ℝ) ^ d *
          interiorCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * CnoteQ) Q a s t u := by
    calc
      interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
          (18 : ℝ) ^ d *
            coarseCaccioppoliLocalEnergyRadiusProfile Q (cubeCenter Q)
              (fun y =>
                scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
                  u.toPointwiseAHarmonic y) ((3 : ℝ)⁻¹) := hgeom
      _ =
          (18 : ℝ) ^ d *
            coarseCaccioppoliLocalEnergyRadiusProfile Q (cubeCenter Q)
              (fun y =>
                scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
                  u.toPointwiseAHarmonic y) (1 / 3 : ℝ) := by
        simp [one_div]
      _ ≤
          (18 : ℝ) ^ d *
            coarseCaccioppoliLocalizedEnergyRadiusProfile Q
              (fun y =>
                scalarVariationEnergyIntegrand (pointwiseCoeffFor Q a)
                  u.toPointwiseAHarmonic y) (1 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlocal_le hfactor_nonneg
      _ ≤
          (18 : ℝ) ^ d *
            coarseCaccioppoliInteriorNoteRhs Q (pointwiseCoeffFor Q a) s t CnoteQ
              (interiorCaccioppoliParentOscillationL2Sq Q a u) := by
        exact mul_le_mul_of_nonneg_left hdet_bound hfactor_nonneg
      _ ≤
          (18 : ℝ) ^ d *
            interiorCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * CnoteQ) Q a s t u := by
        exact mul_le_mul_of_nonneg_left hconvert hfactor_nonneg
  have halpha :
      CalphaQ = coarseCaccioppoliBufferedAlphaBudgetUnit d s := by
    simpa [CalphaQ, CsolQ] using
      coarseCaccioppoliBufferedAlphaBudget_eq_unit_of_scale_eq_zero
        (Q := Q) s hQscale
  have hcross :
      CcrossQ = coarseCaccioppoliBufferedCrossBudgetUnit d s := by
    simpa [CcrossQ, CsolQ] using
      coarseCaccioppoliBufferedCrossBudget_eq_unit_of_scale_eq_zero
        (Q := Q) s hQscale
  simpa [CalphaQ, CcrossQ, CalphaInternalQ, CcrossInternalQ, CnoteQ, halpha, hcross]
    using And.intro hCnote hbound

private theorem boundary_publicCoreEnergy_le_publicRHS_of_scale_zero_of_noteConstant_mul_le
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x) {s t Cnote C : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hCnote : 0 ≤ Cnote)
    (hCnote_le : (18 : ℝ) ^ d * (((d : ℝ) ^ (2 : ℕ)) * Cnote) ≤ C)
    (hbound :
      boundaryCaccioppoliCoreEnergy u ≤
        (18 : ℝ) ^ d *
          boundaryCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * Cnote) s t u) :
    boundaryCaccioppoliCoreEnergy u ≤ boundaryCaccioppoliRHS C s t u := by
  have hfactor : (1 : ℝ) ≤ (18 : ℝ) ^ d :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 18)
  have hD_nonneg : 0 ≤ ((d : ℝ) ^ (2 : ℕ)) := by positivity
  have hD_Cnote_nonneg : 0 ≤ ((d : ℝ) ^ (2 : ℕ)) * Cnote :=
    mul_nonneg hD_nonneg hCnote
  exact hbound.trans
    (boundaryCaccioppoliRHS_mul_const_le_of_mul_constant_le
      (Q := Q) (a := a) (x := x) u (s := s) (t := t)
      (M := (18 : ℝ) ^ d)
      (C₁ := ((d : ℝ) ^ (2 : ℕ)) * Cnote) (C₂ := C)
      hfactor hD_Cnote_nonneg hCnote_le hs ht hst)

private theorem interior_centered_publicCoreEnergy_le_publicRHS_of_scale_zero_of_noteConstant_mul_le
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    (u : CubeSolution Q a) {s t Cnote C : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hCnote : 0 ≤ Cnote)
    (hCnote_le : (18 : ℝ) ^ d * (((d : ℝ) ^ (2 : ℕ)) * Cnote) ≤ C)
    (hbound :
      interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
        (18 : ℝ) ^ d *
          interiorCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * Cnote) Q a s t u) :
    interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
      interiorCaccioppoliRHS C Q a s t u := by
  have hfactor : (1 : ℝ) ≤ (18 : ℝ) ^ d :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 18)
  have hD_nonneg : 0 ≤ ((d : ℝ) ^ (2 : ℕ)) := by positivity
  have hD_Cnote_nonneg : 0 ≤ ((d : ℝ) ^ (2 : ℕ)) * Cnote :=
    mul_nonneg hD_nonneg hCnote
  exact hbound.trans
    (interiorCaccioppoliRHS_mul_const_le_of_mul_constant_le
      (Q := Q) (a := a) u (s := s) (t := t)
      (M := (18 : ℝ) ^ d)
      (C₁ := ((d : ℝ) ^ (2 : ℕ)) * Cnote) (C₂ := C)
      hfactor hD_Cnote_nonneg hCnote_le hs ht hst)

theorem boundary_publicCoreEnergy_le_publicRHS_of_scale_zero_of_unitStandardExplicitBoundSplit
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {x : Vec d} (u : BoundaryCaccioppoliDatum Q a x) {s t C : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hx : x ∈ openCubeSet Q) (hQscale : Q.scale = 0)
    (hC :
      let CalphaInternal : ℝ :=
        (Fintype.card (Fin d) : ℝ) *
          coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s
      let CcrossInternal : ℝ :=
        (Fintype.card (Fin d) : ℝ) *
          coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s
      (18 : ℝ) ^ d * (((d : ℝ) ^ (2 : ℕ)) *
          caccioppoliStandardExplicitNoteBoundSplit
            s t CalphaInternal CcrossInternal) ≤ C) :
    boundaryCaccioppoliCoreEnergy u ≤ boundaryCaccioppoliRHS C s t u := by
  let CalphaInternal : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s
  let CcrossInternal : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s
  let Cnote : ℝ :=
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
      Q (pointwiseCoeffFor Q a) s t CalphaInternal CcrossInternal
  have hexact :=
    boundary_publicCoreEnergy_le_eighteen_pow_mul_publicRHS_of_scale_zero_standardExplicitBudgetSplit
      (Q := Q) (a := a) (x := x) u hs ht hst hx hQscale
  have hexact' :
      0 ≤ Cnote ∧
        boundaryCaccioppoliCoreEnergy u ≤
          (18 : ℝ) ^ d *
            boundaryCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * Cnote) s t u := by
    simpa [CalphaInternal, CcrossInternal, Cnote] using hexact
  rcases hexact' with ⟨hCnote, hbound⟩
  have hnote_le :
      Cnote ≤
        caccioppoliStandardExplicitNoteBoundSplit s t
          CalphaInternal CcrossInternal := by
    simpa [CalphaInternal, CcrossInternal, Cnote] using
      boundary_localPatch_standardExplicitNoteConstantSplit_le_unitExplicitBound_of_scale_zero
        Q a hs ht hst hQscale
  have hfactor_nonneg : 0 ≤ (18 : ℝ) ^ d :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 18) d
  have hD_nonneg : 0 ≤ ((d : ℝ) ^ (2 : ℕ)) := by positivity
  have hD_note_le :
      ((d : ℝ) ^ (2 : ℕ)) * Cnote ≤
        ((d : ℝ) ^ (2 : ℕ)) *
          caccioppoliStandardExplicitNoteBoundSplit s t
            CalphaInternal CcrossInternal :=
    mul_le_mul_of_nonneg_left hnote_le hD_nonneg
  have hCnote_le :
      (18 : ℝ) ^ d * (((d : ℝ) ^ (2 : ℕ)) * Cnote) ≤ C := by
    exact
      (mul_le_mul_of_nonneg_left hD_note_le hfactor_nonneg).trans
        (by simpa [CalphaInternal, CcrossInternal] using hC)
  exact
    boundary_publicCoreEnergy_le_publicRHS_of_scale_zero_of_noteConstant_mul_le
      (Q := Q) (a := a) (x := x) u hs ht hst hCnote hCnote_le hbound

theorem interior_centered_publicCoreEnergy_le_publicRHS_of_scale_zero_of_unitStandardExplicitBoundSplit
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    (u : CubeSolution Q a) {s t C : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hQscale : Q.scale = 0)
    (hC :
      let CalphaInternal : ℝ :=
        (Fintype.card (Fin d) : ℝ) *
          coarseCaccioppoliBufferedAlphaBudgetUnit d s
      let CcrossInternal : ℝ :=
        (Fintype.card (Fin d) : ℝ) *
          coarseCaccioppoliBufferedCrossBudgetUnit d s
      (18 : ℝ) ^ d * (((d : ℝ) ^ (2 : ℕ)) *
          caccioppoliStandardExplicitNoteBoundSplit
            s t CalphaInternal CcrossInternal) ≤ C) :
    interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
      interiorCaccioppoliRHS C Q a s t u := by
  let CalphaInternal : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      coarseCaccioppoliBufferedAlphaBudgetUnit d s
  let CcrossInternal : ℝ :=
    (Fintype.card (Fin d) : ℝ) *
      coarseCaccioppoliBufferedCrossBudgetUnit d s
  let Cnote : ℝ :=
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit
      Q (pointwiseCoeffFor Q a) s t CalphaInternal CcrossInternal
  have hexact :=
    interior_centered_publicCoreEnergy_le_eighteen_pow_mul_publicRHS_of_scale_zero_standardExplicitBudgetSplit
      (Q := Q) (a := a) u hs ht hst hQscale
  have hexact' :
      0 ≤ Cnote ∧
        interiorCaccioppoliCoreEnergy Q a (cubeCenter Q) u ≤
          (18 : ℝ) ^ d *
            interiorCaccioppoliRHS (((d : ℝ) ^ (2 : ℕ)) * Cnote) Q a s t u := by
    simpa [CalphaInternal, CcrossInternal, Cnote] using hexact
  rcases hexact' with ⟨hCnote, hbound⟩
  have hnote_le :
      Cnote ≤
        caccioppoliStandardExplicitNoteBoundSplit s t
          CalphaInternal CcrossInternal := by
    simpa [CalphaInternal, CcrossInternal, Cnote] using
      interior_centered_standardExplicitNoteConstantSplit_le_unitExplicitBound_of_scale_zero
        Q a hs ht hst hQscale
  have hfactor_nonneg : 0 ≤ (18 : ℝ) ^ d :=
    pow_nonneg (by norm_num : (0 : ℝ) ≤ 18) d
  have hD_nonneg : 0 ≤ ((d : ℝ) ^ (2 : ℕ)) := by positivity
  have hD_note_le :
      ((d : ℝ) ^ (2 : ℕ)) * Cnote ≤
        ((d : ℝ) ^ (2 : ℕ)) *
          caccioppoliStandardExplicitNoteBoundSplit s t
            CalphaInternal CcrossInternal :=
    mul_le_mul_of_nonneg_left hnote_le hD_nonneg
  have hCnote_le :
      (18 : ℝ) ^ d * (((d : ℝ) ^ (2 : ℕ)) * Cnote) ≤ C := by
    exact
      (mul_le_mul_of_nonneg_left hD_note_le hfactor_nonneg).trans
        (by simpa [CalphaInternal, CcrossInternal] using hC)
  exact
    interior_centered_publicCoreEnergy_le_publicRHS_of_scale_zero_of_noteConstant_mul_le
      (Q := Q) (a := a) u hs ht hst hCnote hCnote_le hbound


end

end Ch03
end Book
end Homogenization
