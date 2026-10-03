/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.LocalPatchNoteRawBridge.BoundarySplit

/-! # Local Patch Note Raw Bridge -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Local-patch note raw bridge

This sidecar ties the arbitrary-center local-patch descendant summation to the
harmonic weak-testing identity.  It covers the interior-contained local patch
case: the translated cutoff support is required to lie inside the parent open
cube, so the compact-support test function is admissible without a boundary
zero-trace argument.
-/

/-- Boundary local-patch split raw bridge for a constant harmonic family, in
the boundary-touching case supplied by a localized scalar zero-trace condition. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplit.of_constantFamily_localPatchBufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplit_of_localizedZeroTrace_of_closedCubeEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ} {V : Set (Vec d)}
    (u0 : AHarmonicFunction a (openCubeSet Q))
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V u0.toH1.toFun)
    (hClocal : 0 ≤ Clocal) (hCcross : 0 ≤ Ccross)
    (hCsol_le : fullVectorPoincareCubeConstant Q ≤ Clocal)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hcutoffWindow : ∀ n : ℕ,
      let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
      let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
      let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
      coarseCaccioppoliLocalClosedCube Q center ρm ⊆ V)
    (hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplit
        Q center a s t Clocal Calpha Ccross) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplit
      Q center a s t Calpha Ccross (coarseCaccioppoliHarmonicL2Sq Q a u0)
      (fun x => scalarVariationEnergyIntegrand a u0 x) := by
  refine
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplit.of_constantFamily_localPatchBufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplit_of_testing_of_closedCubeEllipticity
      (Q := Q) (center := center) (a := a) (s := s) (t := t)
      (Clocal := Clocal) (Calpha := Calpha) (Ccross := Ccross) (u0 := u0)
      hClocal hCcross hCsol_le hs ht hst hEllCube ?_ hrawcoeff
  intro n
  let ρ₁ : ℝ := coarseCaccioppoliRadiusSequence n
  let ρ₂ : ℝ := coarseCaccioppoliRadiusSequence (n + 1)
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a u0 x
  let flux : Vec d → Vec d := fun x => matVecMul (a x) (u0.toH1.grad x)
  let u : Vec d → ℝ := fun x => u0.toH1 x
  let ξ : Vec d → Vec d :=
    scalarCutoffGradientField
      (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEllCube.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hρ₁ : (1 / 3 : ℝ) ≤ ρ₁ := by
    simpa [ρ₁] using (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hρ₁_pos : 0 < ρ₁ := by
    exact (show (0 : ℝ) < 1 / 3 by norm_num).trans_le hρ₁
  have hlt : ρ₁ < ρ₂ := by
    simpa [ρ₁, ρ₂] using
      coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hlt_mid : ρ₁ < ρm := by
    simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hfluxEnergyQ :
      CoarseCaccioppoliFluxEnergyControls Q a s flux energy := by
    have hflux :=
      CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
        (Q := Q) (a := a) (s := s) hs hEllCube u0.toCubeSet
    simpa [flux, energy, scalarVariationEnergyIntegrand] using hflux
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    intro x hx
    have hnonneg :=
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (cubeSet Q) a hEllCube u0.toCubeSet x hx
    simpa [energy, scalarVariationEnergyIntegrand] using hnonneg
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume := hfluxEnergyQ.2.1
  have hlowerρ :
      coarseCaccioppoliLocalEnergyRadiusProfile Q center energy ρ₁ ≤
        cubeAverage Q
          (fun x =>
            coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm x * energy x) := by
    simpa [coarseCaccioppoliLocalEnergyRadiusProfile] using
      coarseCaccioppoliLocalEnergyProfile_le_localCanonicalCutoffEnergy_of_integrable
        Q center energy hρ₁_pos hlt_mid henergy_nonneg henergy_int
  have htestη :=
    le_abs_cubeAverage_vecDot_flux_localCanonicalCutoff_of_aHarmonicFunction_of_localizedZeroTrace_of_le_localCanonicalCutoffEnergy
      Q a center u0 hEllOpen hzero hρ₁_pos hlt_mid
      (by simpa [ρ₁, ρ₂, ρm] using hcutoffWindow n)
      (by simpa [energy] using hlowerρ)
  simpa [ρ₁, ρ₂, ρm, energy, flux, u, ξ] using htestη

/-- All-radii boundary local-patch split raw bridge for a constant harmonic
family, in the boundary-touching case supplied by a localized scalar
zero-trace condition. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii.of_constantFamily_localPatchBufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplitAllRadii_of_localizedZeroTrace_of_closedCubeEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ} {V : Set (Vec d)}
    (u0 : AHarmonicFunction a (openCubeSet Q))
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V u0.toH1.toFun)
    (hClocal : 0 ≤ Clocal) (hCcross : 0 ≤ Ccross)
    (hCsol_le : fullVectorPoincareCubeConstant Q ≤ Clocal)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hcutoffWindow :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
        coarseCaccioppoliLocalClosedCube Q center ρm ⊆ V)
    (hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii
        Q center a s t Clocal Calpha Ccross) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii
      Q center a s t Calpha Ccross (coarseCaccioppoliHarmonicL2Sq Q a u0)
      (fun x => scalarVariationEnergyIntegrand a u0 x) := by
  refine
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii.of_constantFamily_localPatchBufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplitAllRadii_of_testing_of_closedCubeEllipticity
      (Q := Q) (center := center) (a := a) (s := s) (t := t)
      (Clocal := Clocal) (Calpha := Calpha) (Ccross := Ccross) (u0 := u0)
      hClocal hCcross hCsol_le hs ht hst hEllCube ?_ hrawcoeff
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a u0 x
  let flux : Vec d → Vec d := fun x => matVecMul (a x) (u0.toH1.grad x)
  let u : Vec d → ℝ := fun x => u0.toH1 x
  let ξ : Vec d → Vec d :=
    scalarCutoffGradientField
      (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEllCube.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hρ₁_pos : 0 < ρ₁ := by
    exact (show (0 : ℝ) < 1 / 3 by norm_num).trans_le hρ₁
  have hlt_mid : ρ₁ < ρm := by
    simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hfluxEnergyQ :
      CoarseCaccioppoliFluxEnergyControls Q a s flux energy := by
    have hflux :=
      CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
        (Q := Q) (a := a) (s := s) hs hEllCube u0.toCubeSet
    simpa [flux, energy, scalarVariationEnergyIntegrand] using hflux
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    intro x hx
    have hnonneg :=
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (cubeSet Q) a hEllCube u0.toCubeSet x hx
    simpa [energy, scalarVariationEnergyIntegrand] using hnonneg
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume := hfluxEnergyQ.2.1
  have hlowerρ :
      coarseCaccioppoliLocalEnergyRadiusProfile Q center energy ρ₁ ≤
        cubeAverage Q
          (fun x =>
            coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm x * energy x) := by
    simpa [coarseCaccioppoliLocalEnergyRadiusProfile] using
      coarseCaccioppoliLocalEnergyProfile_le_localCanonicalCutoffEnergy_of_integrable
        Q center energy hρ₁_pos hlt_mid henergy_nonneg henergy_int
  have htestη :=
    le_abs_cubeAverage_vecDot_flux_localCanonicalCutoff_of_aHarmonicFunction_of_localizedZeroTrace_of_le_localCanonicalCutoffEnergy
      Q a center u0 hEllOpen hzero hρ₁_pos hlt_mid
      (by simpa [ρm] using hcutoffWindow hρ₁ hlt hρ₂)
      (by simpa [energy] using hlowerρ)
  simpa [ρm, energy, flux, u, ξ] using htestη

/-- Boundary local-patch standard note-RHS endpoint for a constant harmonic
family with zero trace on the full local `cu_{m-1}` window, with split note
coefficients. -/
theorem
    coarseCaccioppoli_boundary_localPatch_qone_standard_le_noteRhs_explicitSplit_of_constantFamily_localPatchBufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplitAllRadii_of_localizedZeroTraceOnLocalOpenCube
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Clocal Calpha Ccross : ℝ) {lam Lam : ℝ}
    (u0 : AHarmonicFunction a (openCubeSet Q))
    (hzero :
      LocalizedZeroTraceFunctionOn (openCubeSet Q)
        (coarseCaccioppoliLocalOpenCube Q center 1) u0.toH1.toFun)
    (hClocal : 0 ≤ Clocal) (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hCsol_le : fullVectorPoincareCubeConstant Q ≤ Clocal)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii
        Q center a s t Clocal Calpha Ccross) :
    coarseCaccioppoliLocalEnergyRadiusProfile Q center
        (fun x => scalarVariationEnergyIntegrand a u0 x) (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryNoteRhs Q a s t
        (coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit Q a s t
          ((Fintype.card (Fin d) : ℝ) * Calpha)
          ((Fintype.card (Fin d) : ℝ) * Ccross))
        (coarseCaccioppoliHarmonicL2Sq Q a u0) := by
  let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand a u0 x
  have hfluxEnergyQ :
      CoarseCaccioppoliFluxEnergyControls Q a s
        (fun x => matVecMul (a x) (u0.toH1.grad x)) energy := by
    have hflux :=
      CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
        (Q := Q) (a := a) (s := s) hs hEllCube u0.toCubeSet
    simpa [energy, scalarVariationEnergyIntegrand] using hflux
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    intro x hx
    have hnonneg :=
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (cubeSet Q) a hEllCube u0.toCubeSet x hx
    simpa [energy, scalarVariationEnergyIntegrand] using hnonneg
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume :=
    hfluxEnergyQ.2.1
  have hcutoffWindow :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
        coarseCaccioppoliLocalClosedCube Q center ρm ⊆
          coarseCaccioppoliLocalOpenCube Q center 1 := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
    have houter : ρm < 1 := by
      have hm_lt : ρm < ρ₂ := by
        simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).2
      exact hm_lt.trans_le hρ₂
    exact
      coarseCaccioppoliLocalClosedCube_subset_localOpenCube_one_of_lt_one
        (Q := Q) (center := center) (rho := ρm) houter
  have hBridge :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii
        Q center a s t Calpha Ccross (coarseCaccioppoliHarmonicL2Sq Q a u0) energy :=
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii.of_constantFamily_localPatchBufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplitAllRadii_of_localizedZeroTrace_of_closedCubeEllipticity
      (Q := Q) (center := center) (a := a) (s := s) (t := t)
      (Clocal := Clocal) (Calpha := Calpha) (Ccross := Ccross) (u0 := u0)
      hzero hClocal hCcross hCsol_le hs ht hst hEllCube hcutoffWindow hrawcoeff
  simpa [energy] using
    coarseCaccioppoli_boundary_localPatch_qone_standard_le_noteRhs_explicitSplit_of_noteRawBridgeSplitAllRadii
      (Q := Q) (center := center) (a := a) (s := s) (t := t)
      (Calpha := Calpha) (Ccross := Ccross)
      (uL2Sq := coarseCaccioppoliHarmonicL2Sq Q a u0)
      (baseEnergy := energy) (w := fun _ _ => u0)
      hCalpha hCcross hs ht hst (coarseCaccioppoliHarmonicL2Sq_nonneg Q a u0)
      hEllCube henergy_nonneg henergy_int hBridge

end

end Homogenization
