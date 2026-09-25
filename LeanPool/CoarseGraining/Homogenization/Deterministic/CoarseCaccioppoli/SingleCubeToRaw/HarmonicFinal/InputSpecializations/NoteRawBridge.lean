/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.NoteRawBridge.BoundarySplit
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.CoefficientBounds
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.FaithfulDescendant
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummationFullDual
public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic.Ellipticity.QOneRoot

/-! # Note Raw Bridge -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- Split interior raw bridge for a constant harmonic family using the same
buffered localized-energy summation as the repaired boundary route. -/
theorem
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplit.of_constantFamily_bufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplit_of_closedCubeEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (u0 : AHarmonicFunction a (openCubeSet Q))
    (hClocal : 0 ≤ Clocal) (hCalpha : 0 ≤ Calpha) (hCcross : 0 ≤ Ccross)
    (hCsol_le : fullVectorPoincareCubeConstant Q ≤ Clocal)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplit
        Q a s t Clocal Calpha Ccross) :
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplit
      Q a s t Calpha Ccross (coarseCaccioppoliHarmonicL2Sq Q a u0)
      (fun x => scalarVariationEnergyIntegrand a u0 x) :=
  CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplit.of_boundary
    Q a s t Calpha Ccross (coarseCaccioppoliHarmonicL2Sq Q a u0)
    (fun x => scalarVariationEnergyIntegrand a u0 x)
    (CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplit.of_constantFamily_bufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplit_of_closedCubeEllipticity
      (Q := Q) (a := a) (s := s) (t := t) (Clocal := Clocal)
      (Calpha := Calpha) (Ccross := Ccross) (u0 := u0)
      hClocal hCalpha hCcross hCsol_le hs ht hst hEllCube hrawcoeff)

/-- Boundary note-RHS Caccioppoli from an all-radii split note-faithful raw
bridge, using the standard beta-dependent radius iteration. -/
theorem
    coarseCaccioppoli_boundary_qone_standard_le_noteRhs_explicitSplit_of_profileInputs_of_noteRawBridgeSplitAllRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hProfile :
      CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs Q a baseEnergy w)
    (hBridge :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii
        Q a s t Calpha Ccross uL2Sq baseEnergy) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryNoteRhs Q a s t
        (coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit Q a s t
          ((Fintype.card (Fin d) : ℝ) * Calpha)
          ((Fintype.card (Fin d) : ℝ) * Ccross)) uL2Sq := by
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  have hcard_pos : 0 < (Fintype.card (Fin d) : ℝ) := by
    have hnat : 0 < Fintype.card (Fin d) := by
      simp [Fintype.card_fin, Nat.pos_iff_ne_zero, NeZero.ne d]
    exact_mod_cast hnat
  have hCeffAlpha_pos : 0 < CeffAlpha := by
    exact mul_pos hcard_pos hCalpha
  have hCeffCross_nonneg : 0 ≤ CeffCross := by
    exact mul_nonneg hcard_pos.le hCcross
  exact
    coarseCaccioppoli_boundary_qone_standard_le_noteRhs_of_noteEstimate_of_localizedExplicitHeightOfScaleChoice_split
      (Q := Q) (a := a) (s := s) (t := t)
      (Calpha := CeffAlpha) (Ccross := CeffCross) (uL2Sq := uL2Sq)
      (k := coarseCaccioppoliTriadicGapScale)
      hCeffAlpha_pos hCeffCross_nonneg hs ht hst hu
      (thetaRatio_pos_of_closedCubeHarmonicFamily Q a s t w hs ht hEllCube)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_nonneg
        Q hProfile.base_nonneg)
      (coarseCaccioppoliLocalizedEnergyRadiusProfile_boundedAbove
        Q hProfile.base_nonneg hProfile.base_integrable)
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
        coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂)
      (by
        simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii,
          CeffAlpha, CeffCross] using hBridge)

/-- Interior note-RHS Caccioppoli from an all-radii split note-faithful raw
bridge, using the standard beta-dependent radius iteration. -/
theorem
    coarseCaccioppoli_interior_qone_standard_le_noteRhs_explicitSplit_of_profileInputs_of_noteRawBridgeSplitAllRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hProfile :
      CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs Q a baseEnergy w)
    (hBridge :
      CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii
        Q a s t Calpha Ccross uL2Sq baseEnergy) :
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorNoteRhs Q a s t
        (coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit Q a s t
          ((Fintype.card (Fin d) : ℝ) * Calpha)
          ((Fintype.card (Fin d) : ℝ) * Ccross)) uL2Sq := by
  have hBoundaryBridge :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii
        Q a s t Calpha Ccross uL2Sq baseEnergy := by
    simpa [CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii]
      using hBridge
  simpa [coarseCaccioppoliInteriorNoteRhs] using
    (coarseCaccioppoli_boundary_qone_standard_le_noteRhs_explicitSplit_of_profileInputs_of_noteRawBridgeSplitAllRadii
      (Q := Q) (a := a) (s := s) (t := t) (Calpha := Calpha)
      (Ccross := Ccross) (uL2Sq := uL2Sq)
      (baseEnergy := baseEnergy) (w := w)
      hCalpha hCcross hs ht hst hu hEllCube hProfile hBoundaryBridge)

/-- Boundary note-RHS Caccioppoli from an all-radii split arbitrary-center
local-patch raw bridge, using the standard beta-dependent radius iteration. -/
theorem
    coarseCaccioppoli_boundary_localPatch_qone_standard_le_noteRhs_explicitSplit_of_noteRawBridgeSplitAllRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d)
    (a : CoeffField d) (s t Calpha Ccross uL2Sq : ℝ) {lam Lam : ℝ}
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hbase_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x)
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hBridge :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii
        Q center a s t Calpha Ccross uL2Sq baseEnergy) :
    coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryNoteRhs Q a s t
        (coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit Q a s t
          ((Fintype.card (Fin d) : ℝ) * Calpha)
          ((Fintype.card (Fin d) : ℝ) * Ccross)) uL2Sq := by
  let CeffAlpha : ℝ := (Fintype.card (Fin d) : ℝ) * Calpha
  let CeffCross : ℝ := (Fintype.card (Fin d) : ℝ) * Ccross
  have hcard_pos : 0 < (Fintype.card (Fin d) : ℝ) := by
    have hnat : 0 < Fintype.card (Fin d) := by
      simp [Fintype.card_fin, Nat.pos_iff_ne_zero, NeZero.ne d]
    exact_mod_cast hnat
  have hCeffAlpha_pos : 0 < CeffAlpha := by
    exact mul_pos hcard_pos hCalpha
  have hCeffCross_nonneg : 0 ≤ CeffCross := by
    exact mul_nonneg hcard_pos.le hCcross
  exact
    coarseCaccioppoli_boundary_qone_standard_le_noteRhs_of_noteEstimate_of_localizedExplicitHeightOfScaleChoice_split
      (Q := Q) (a := a) (s := s) (t := t)
      (Calpha := CeffAlpha) (Ccross := CeffCross) (uL2Sq := uL2Sq)
      (k := coarseCaccioppoliTriadicGapScale)
      hCeffAlpha_pos hCeffCross_nonneg hs ht hst hu
      (thetaRatio_pos_of_closedCubeHarmonicFamily Q a s t w hs ht hEllCube)
      (coarseCaccioppoliLocalEnergyRadiusProfile_nonneg
        Q center hbase_nonneg)
      (coarseCaccioppoliLocalEnergyRadiusProfile_boundedAbove
        Q center hbase_nonneg hbase_int)
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
        coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂)
      (by
        simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii,
          CeffAlpha, CeffCross] using hBridge)

/-!
The theorem-facing endpoint aliases that used to live here are now in
`HarmonicFinal/Endpoints.lean`. This file now stops at the internal bridge
constructors and compatibility plumbing that those endpoints consume.
-/

end

end Homogenization
