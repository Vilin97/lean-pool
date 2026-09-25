/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicCanonicalGradient
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.Setup.CoefficientBounds
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.CutoffSizes

/-! # Solution Inputs -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-- The fixed localized energy profile used by the harmonic-gradient
Caccioppoli endpoints.

This is the solution-side part that genuinely belongs to the chosen localized
energy density: nonnegativity and integrability on the cube, and comparison
with each radius-pair harmonic energy on the inner closed cube.  It does not
assert that a full-cube pair-energy average equals the localized outer-radius
profile; that statement is false for a general solution and must not be hidden
inside the profile package. -/
structure CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) : Prop where
  base_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x
  base_integrable :
    MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume
  inner_energy_le :
    ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      ∀ x ∈ scaledClosedCubeSet Q ρ₁,
        baseEnergy x ≤ scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x

/-- The natural energy density of a single harmonic function supplies the fixed
localized energy profile for the constant radius-pair family. -/
theorem CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs.of_constantFamily
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {lam Lam : ℝ}
    (u : AHarmonicFunction a (openCubeSet Q))
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs Q a
      (fun x => scalarVariationEnergyIntegrand a u x) (fun _ _ => u) where
  base_nonneg := by
    intro x hx
    simpa [scalarVariationEnergyIntegrand] using
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
        (cubeSet Q) a hEllCube u.toCubeSet x hx
  base_integrable := by
    have hflux :
        CoarseCaccioppoliFluxEnergyControls Q a (1 : ℝ)
          (fun x => matVecMul (a x) (u.toCubeSet.toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a u.toCubeSet x) :=
      CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
        (Q := Q) (a := a) (s := (1 : ℝ)) (by norm_num) hEllCube u.toCubeSet
    simpa [scalarVariationEnergyIntegrand] using hflux.2.1
  inner_energy_le := by
    intro ρ₁ ρ₂ _ _ _ x _
    exact le_rfl

/-- Legacy componentwise solution-side assumptions for the harmonic-gradient
Caccioppoli surface.

This groups the fixed localized energy profile, strict positivity of the
canonical gradient factors, and the projected Poincare family for the selected
component.  The projected Poincare field is a compatibility input for older
componentwise endpoints; the corrected note-facing route must use the full-dual
vector Poincare family instead. -/
structure CoarseCaccioppoliBoundaryCanonicalHarmonicSolutionInputs {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (C : ℝ)
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d) : Prop where
  profile :
    CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs Q a baseEnergy w
  positive_factors :
    CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w
  projected_poincare :
    CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i

/-- The actual live compatibility inputs for the repaired vector small-cube
route: fixed localized profile plus projected-vector Poincare.

This package deliberately omits the old strict positive-factor field.  The
faithful small-cube route only needs nonnegative local cutoff sizes and
gradient `circ` bounds, both derived directly in the proof; strict positivity
would incorrectly exclude the zero harmonic solution.  The projected-vector
Poincare field is still a legacy consumer boundary and must be replaced by the
full-dual vector route before this becomes note-facing. -/
structure CoarseCaccioppoliBoundaryCanonicalHarmonicVectorProfilePoincareInputs {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (C : ℝ)
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) : Prop where
  profile :
    CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs Q a baseEnergy w
  projected_vector_poincare :
    CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareVectorFamily Q a C w

/-- Enlarge the projected-vector Poincare constant inside the live
profile/Poincare package. -/
theorem CoarseCaccioppoliBoundaryCanonicalHarmonicVectorProfilePoincareInputs.mono_C
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {C₁ C₂ : ℝ} {baseEnergy : Vec d → ℝ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)}
    (h :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorProfilePoincareInputs
        Q a C₁ baseEnergy w)
    (hC : C₁ ≤ C₂) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorProfilePoincareInputs
      Q a C₂ baseEnergy w where
  profile := h.profile
  projected_vector_poincare := h.projected_vector_poincare.mono_C hC

/-- Note-faithful raw bridge for the vector harmonic Caccioppoli endpoint.

This is the intended landing pad for the local subcube/Besov argument in the
LaTeX proof.  It is stated only on the Chapter-3 radius sequence, which is the
actual recurrence used by the proof and keeps the canonical cutoff away from
the outer-radius endpoint `1`.  Unlike the older canonical coefficient
schedules, this bridge is already after the local `3^{k+h}` against `3^{-h}`
cancellation and therefore targets the note's radius-recursion coefficients
directly. -/
def CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (baseEnergy : Vec d → ℝ) : Prop :=
  ∀ n : ℕ,
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
        (coarseCaccioppoliRadiusSequence n) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t
          ((Fintype.card (Fin d) : ℝ) * C)
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * C) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
          (coarseCaccioppoliRadiusSequence (n + 1)) +
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s
          ((Fintype.card (Fin d) : ℝ) * C) uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * C) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        Real.sqrt
          (coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
            (coarseCaccioppoliRadiusSequence (n + 1)))

/-- Split note-faithful raw bridge for the vector harmonic Caccioppoli
endpoint.  `Calpha` controls the explicit height/absorption coefficient and
`Ccross` controls the cross coefficient. -/
def CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplit {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) (baseEnergy : Vec d → ℝ) : Prop :=
  ∀ n : ℕ,
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
        (coarseCaccioppoliRadiusSequence n) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t
          ((Fintype.card (Fin d) : ℝ) * Calpha)
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * Calpha) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
          (coarseCaccioppoliRadiusSequence (n + 1)) +
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s
          ((Fintype.card (Fin d) : ℝ) * Ccross) uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * Calpha) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        Real.sqrt
          (coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
            (coarseCaccioppoliRadiusSequence (n + 1)))

/-- All-radii split raw bridge for the vector harmonic Caccioppoli endpoint.
This is the bridge shape consumed by the standard beta-dependent hole-filling
iteration. -/
def CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) (baseEnergy : Vec d → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryNoteRawEstimateSplit Q a s t
    ((Fintype.card (Fin d) : ℝ) * Calpha)
    ((Fintype.card (Fin d) : ℝ) * Ccross) uL2Sq
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
      ((Fintype.card (Fin d) : ℝ) * Calpha) coarseCaccioppoliTriadicGapScale)
    (coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)

/-- Interior counterpart of the note-faithful raw bridge.  The current
interior Caccioppoli backbone reuses the same coefficient shape as the boundary
case; the distinction is in how the local estimate is produced. -/
def CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridge {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (baseEnergy : Vec d → ℝ) : Prop :=
  ∀ n : ℕ,
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
        (coarseCaccioppoliRadiusSequence n) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t
          ((Fintype.card (Fin d) : ℝ) * C)
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * C) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
          (coarseCaccioppoliRadiusSequence (n + 1)) +
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s
          ((Fintype.card (Fin d) : ℝ) * C) uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * C) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        Real.sqrt
          (coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
            (coarseCaccioppoliRadiusSequence (n + 1)))

/-- Split interior counterpart of the note-faithful raw bridge.  As in the
boundary bridge, `Calpha` controls the explicit height/absorption coefficient
and `Ccross` controls the cross coefficient. -/
def CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplit {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) (baseEnergy : Vec d → ℝ) : Prop :=
  ∀ n : ℕ,
    coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
        (coarseCaccioppoliRadiusSequence n) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t
          ((Fintype.card (Fin d) : ℝ) * Calpha)
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * Calpha) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
          (coarseCaccioppoliRadiusSequence (n + 1)) +
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s
          ((Fintype.card (Fin d) : ℝ) * Ccross) uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * Calpha) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        Real.sqrt
          (coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy
            (coarseCaccioppoliRadiusSequence (n + 1)))

/-- All-radii split raw bridge for the centered interior endpoint. -/
def CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) (baseEnergy : Vec d → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii
    Q a s t Calpha Ccross uL2Sq baseEnergy

/-- Boundary raw bridge for an arbitrary-center local patch radius profile.

This is the translated/localized counterpart of
`CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge`: the recurrence
uses the same note-facing coefficients, but the energy profile is centered at
the boundary/interior patch center and has base scale `Q.scale - 1`. -/
def CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridge {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) (baseEnergy : Vec d → ℝ) : Prop :=
  ∀ n : ℕ,
    coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy
        (coarseCaccioppoliRadiusSequence n) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t
          ((Fintype.card (Fin d) : ℝ) * C)
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * C) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy
          (coarseCaccioppoliRadiusSequence (n + 1)) +
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s
          ((Fintype.card (Fin d) : ℝ) * C) uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * C) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        Real.sqrt
          (coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy
            (coarseCaccioppoliRadiusSequence (n + 1)))

/-- Split boundary raw bridge for an arbitrary-center local patch radius
profile.  `Calpha` controls the explicit height/absorption coefficient and
`Ccross` controls the cross coefficient. -/
def CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplit {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) (baseEnergy : Vec d → ℝ) : Prop :=
  ∀ n : ℕ,
    coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy
        (coarseCaccioppoliRadiusSequence n) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t
          ((Fintype.card (Fin d) : ℝ) * Calpha)
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * Calpha) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy
          (coarseCaccioppoliRadiusSequence (n + 1)) +
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s
          ((Fintype.card (Fin d) : ℝ) * Ccross) uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * Calpha) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        Real.sqrt
          (coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy
            (coarseCaccioppoliRadiusSequence (n + 1)))

/-- All-radii split raw bridge for an arbitrary-center local patch radius
profile. -/
def
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) (baseEnergy : Vec d → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryNoteRawEstimateSplit Q a s t
    ((Fintype.card (Fin d) : ℝ) * Calpha)
    ((Fintype.card (Fin d) : ℝ) * Ccross) uL2Sq
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
      ((Fintype.card (Fin d) : ℝ) * Calpha) coarseCaccioppoliTriadicGapScale)
    (coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy)

/-- Interior counterpart of the local-patch raw bridge.  The coefficient shape
is again identical to the boundary bridge at the radius-recursion level. -/
def CoarseCaccioppoliInteriorCanonicalHarmonicVectorLocalPatchNoteRawBridge {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) (baseEnergy : Vec d → ℝ) : Prop :=
  ∀ n : ℕ,
    coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy
        (coarseCaccioppoliRadiusSequence n) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t
          ((Fintype.card (Fin d) : ℝ) * C)
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * C) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy
          (coarseCaccioppoliRadiusSequence (n + 1)) +
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s
          ((Fintype.card (Fin d) : ℝ) * C) uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
            ((Fintype.card (Fin d) : ℝ) * C) coarseCaccioppoliTriadicGapScale)
          (coarseCaccioppoliRadiusSequence n)
          (coarseCaccioppoliRadiusSequence (n + 1)) *
        Real.sqrt
          (coarseCaccioppoliLocalEnergyRadiusProfile Q center baseEnergy
            (coarseCaccioppoliRadiusSequence (n + 1)))

/-- The local-patch interior and boundary vector raw bridges have the same
radius-sequence recurrence shape. -/
theorem
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorLocalPatchNoteRawBridge.of_boundary
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) (baseEnergy : Vec d → ℝ)
    (h :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridge
        Q center a s t C uL2Sq baseEnergy) :
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorLocalPatchNoteRawBridge
      Q center a s t C uL2Sq baseEnergy := by
  simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridge,
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorLocalPatchNoteRawBridge] using h

/-- An all-radii boundary raw estimate restricts to the note-faithful
Chapter-3 radius-sequence bridge. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge.of_noteRawEstimate
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) (baseEnergy : Vec d → ℝ)
    (hraw :
      CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t
        ((Fintype.card (Fin d) : ℝ) * C) uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
          ((Fintype.card (Fin d) : ℝ) * C) coarseCaccioppoliTriadicGapScale)
        (coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge
      Q a s t C uL2Sq baseEnergy := by
  intro n
  have hρ₁ : (1 / 3 : ℝ) ≤ coarseCaccioppoliRadiusSequence n :=
    (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hlt :
      coarseCaccioppoliRadiusSequence n <
        coarseCaccioppoliRadiusSequence (n + 1) :=
    coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hρ₂ : coarseCaccioppoliRadiusSequence (n + 1) ≤ 1 :=
    (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
  simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge] using
    hraw hρ₁ hlt hρ₂

/-- An all-radii interior raw estimate restricts to the note-faithful
Chapter-3 radius-sequence bridge. -/
theorem
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridge.of_noteRawEstimate
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) (baseEnergy : Vec d → ℝ)
    (hraw :
      CoarseCaccioppoliInteriorNoteRawEstimate Q a s t
        ((Fintype.card (Fin d) : ℝ) * C) uL2Sq
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t
          ((Fintype.card (Fin d) : ℝ) * C) coarseCaccioppoliTriadicGapScale)
        (coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy)) :
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridge
      Q a s t C uL2Sq baseEnergy := by
  intro n
  have hρ₁ : (1 / 3 : ℝ) ≤ coarseCaccioppoliRadiusSequence n :=
    (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hlt :
      coarseCaccioppoliRadiusSequence n <
        coarseCaccioppoliRadiusSequence (n + 1) :=
    coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hρ₂ : coarseCaccioppoliRadiusSequence (n + 1) ≤ 1 :=
    (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
  simpa [CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridge,
    CoarseCaccioppoliInteriorNoteRawEstimate] using hraw hρ₁ hlt hρ₂

/-- An all-radii split boundary raw bridge restricts to the legacy
radius-sequence split bridge. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplit.of_allRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) (baseEnergy : Vec d → ℝ)
    (hraw :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii
        Q a s t Calpha Ccross uL2Sq baseEnergy) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplit
      Q a s t Calpha Ccross uL2Sq baseEnergy := by
  intro n
  have hρ₁ : (1 / 3 : ℝ) ≤ coarseCaccioppoliRadiusSequence n :=
    (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hlt :
      coarseCaccioppoliRadiusSequence n <
        coarseCaccioppoliRadiusSequence (n + 1) :=
    coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hρ₂ : coarseCaccioppoliRadiusSequence (n + 1) ≤ 1 :=
    (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
  simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplit,
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii]
    using hraw hρ₁ hlt hρ₂

/-- An all-radii split local-patch raw bridge restricts to the legacy
radius-sequence split local-patch bridge. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplit.of_allRadii
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) (baseEnergy : Vec d → ℝ)
    (hraw :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii
        Q center a s t Calpha Ccross uL2Sq baseEnergy) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplit
      Q center a s t Calpha Ccross uL2Sq baseEnergy := by
  intro n
  have hρ₁ : (1 / 3 : ℝ) ≤ coarseCaccioppoliRadiusSequence n :=
    (coarseCaccioppoliRadiusSequence_mem_Icc n).1
  have hlt :
      coarseCaccioppoliRadiusSequence n <
        coarseCaccioppoliRadiusSequence (n + 1) :=
    coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self n)
  have hρ₂ : coarseCaccioppoliRadiusSequence (n + 1) ≤ 1 :=
    (coarseCaccioppoliRadiusSequence_mem_Icc (n + 1)).2
  simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplit,
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorLocalPatchNoteRawBridgeSplitAllRadii]
    using hraw hρ₁ hlt hρ₂

/-- The interior and boundary vector raw bridges have the same radius-sequence
recurrence shape at this level. -/
theorem
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridge.of_boundary
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) (baseEnergy : Vec d → ℝ)
    (h :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge
        Q a s t C uL2Sq baseEnergy) :
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridge
      Q a s t C uL2Sq baseEnergy := by
  simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridge,
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridge] using h

/-- The split interior and boundary vector raw bridges have the same
radius-sequence recurrence shape at this level. -/
theorem
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplit.of_boundary
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) (baseEnergy : Vec d → ℝ)
    (h :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplit
        Q a s t Calpha Ccross uL2Sq baseEnergy) :
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplit
      Q a s t Calpha Ccross uL2Sq baseEnergy := by
  simpa [CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplit,
    CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplit] using h

/-- Build the legacy solution-side package from the existing projected-Poincare
and `circ` package for the canonical gradient component.  The final theorem
only needs the projected-Poincare part; the two `circ` estimates are useful
upstream and are safely forgotten here. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicSolutionInputs.of_projectedPoincareCircBounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hProfile :
      CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs Q a baseEnergy w)
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w)
    (hProjectedCirc :
      CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds Q a s C w
        (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s)) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicSolutionInputs Q a C baseEnergy w i where
  profile := hProfile
  positive_factors := hpositiveFactors
  projected_poincare := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂ N
    exact hProjectedCirc.projectedPoincare hρ₁ hlt hρ₂ N

/-- The remaining analytic/profile hypotheses for the legacy componentwise
harmonic-gradient endpoint at the Chapter-3 radii.

This package deliberately does not hide the coefficient schedule or the
multiscale ellipticity data.  Its role is to name the solution-side inputs:
fixed localized energy profile, flux/gradient energy controls, nonzero energy
factors, the explicit full-cube/localized energy compatibility equality, and
the projected Poincare family for the selected component. -/
structure CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d) : Prop where
  base_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x
  base_integrable :
    MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume
  inner_energy_le :
    ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      ∀ x ∈ scaledClosedCubeSet Q ρ₁,
        baseEnergy x ≤ scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x
  energy_average :
    ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
        coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂
  flux_energy :
    ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      CoarseCaccioppoliFluxEnergyControls Q a s
        (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
        (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
  nonzero_energy_factors :
    CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w
  gradient_energy :
    ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
        (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
  projected_poincare :
    CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i

/-- Extend a fixed localized profile package to the final analytic-input
package by deriving the flux and gradient energy-control fields from
closed-cube ellipticity, while keeping the nondegeneracy and projected
Poincare inputs explicit. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs.of_profileInputs_closedCubeHarmonicEnergyControls
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    {lam Lam : ℝ} (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hs : 0 < s)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂)
    (hProfile :
      CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs Q a baseEnergy w)
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs Q a s C baseEnergy w i where
  base_nonneg := hProfile.base_nonneg
  base_integrable := hProfile.base_integrable
  inner_energy_le := hProfile.inner_energy_le
  energy_average := henergyAvg
  flux_energy := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    have hflux :=
      CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
        (Q := Q) (a := a) (s := s) hs hEllCube ((w ρ₁ ρ₂).toCubeSet)
    simpa [scalarVariationEnergyIntegrand] using hflux
  nonzero_energy_factors := hnonzeroFactors
  gradient_energy := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
      openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
    have hgrad :=
      cubeAverageGradientEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) hEllCube ((w ρ₁ ρ₂).toCubeSet) hOrigin
    simpa [scalarVariationEnergyIntegrand] using hgrad
  projected_poincare := hprojected

/-- Extend the clean solution-side package to the analytic-input package under
closed-cube ellipticity.

The solution package records strict positivity of the canonical gradient
factors.  The analytic package only needs the weaker nonzero-energy part, so
this bridge forgets the extra `Acirc` positivity while deriving the flux and
gradient energy controls from closed-cube ellipticity. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicSolutionInputs.to_analyticInputs_closedCubeHarmonicEnergyControls
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {s C lam Lam : ℝ} {baseEnergy : Vec d → ℝ}
    {w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)} {i : Fin d}
    (hSolution :
      CoarseCaccioppoliBoundaryCanonicalHarmonicSolutionInputs Q a C baseEnergy w i)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂)
    (hs : 0 < s)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs Q a s C baseEnergy w i := by
  have hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    rcases hSolution.positive_factors hρ₁ hlt hρ₂ with ⟨hU, _hA, hEnergy⟩
    exact ⟨hU, hEnergy⟩
  exact
    CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs.of_profileInputs_closedCubeHarmonicEnergyControls
      Q a s C baseEnergy w i hs hEllCube henergyAvg hSolution.profile hnonzeroFactors
      hSolution.projected_poincare

/-- Build the final analytic/profile input package from the remaining profile,
nondegeneracy, and projected-Poincare fields, while deriving the flux and
gradient energy-control fields from closed-cube ellipticity.

This is a compatibility bridge for the current coarse-Poincare API: it uses
`AHarmonicFunction.toCubeSet`, so it requires ellipticity on `cubeSet Q`.
The pure note-facing open-cube version remains the next analytic target. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs.of_closedCubeHarmonicEnergyControls
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    {lam Lam : ℝ} (baseEnergy : Vec d → ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hs : 0 < s)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hbase_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ baseEnergy x)
    (hbase_int :
      MeasureTheory.IntegrableOn baseEnergy (cubeSet Q) MeasureTheory.volume)
    (hinner_energy_le :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∀ x ∈ scaledClosedCubeSet Q ρ₁,
          baseEnergy x ≤ scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x)
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          coarseCaccioppoliLocalizedEnergyRadiusProfile Q baseEnergy ρ₂)
    (hnonzeroFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientNonzeroEnergyFactors Q a w)
    (hprojected :
      CoarseCaccioppoliBoundaryCanonicalGradientProjectedPoincareFamily Q a C w i) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicAnalyticInputs Q a s C baseEnergy w i where
  base_nonneg := hbase_nonneg
  base_integrable := hbase_int
  inner_energy_le := hinner_energy_le
  energy_average := henergyAvg
  flux_energy := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    have hflux :=
      CoarseCaccioppoliFluxEnergyControls.of_aHarmonicFunction_of_isEllipticFieldOn
        (Q := Q) (a := a) (s := s) hs hEllCube ((w ρ₁ ρ₂).toCubeSet)
    simpa [scalarVariationEnergyIntegrand] using hflux
  nonzero_energy_factors := hnonzeroFactors
  gradient_energy := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
      openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
    have hgrad :=
      cubeAverageGradientEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := a) hEllCube ((w ρ₁ ρ₂).toCubeSet) hOrigin
    simpa [scalarVariationEnergyIntegrand] using hgrad
  projected_poincare := hprojected

/-- Localize the canonical harmonic coefficient schedule to the raw
radius-recursion coefficient schedule.  This is the final coefficient-only
composition step: single-cube coefficient bounds plus standard multiscale data
produce the raw `Alpha`/`Bcross` inequalities consumed by the newest wrappers. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalHarmonicRawCoefficientBounds.of_coefficientBounds_of_multiscaleEllipticity
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds Q a s t C uL2Sq w)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ R ∈ descendantsAtScale Q j,
        ∃ sigmaR sigmaStarR kappaR,
          IsCoarseBlockMatrix (openCubeSet R) a
            (deterministicCoarseBlockMatrix (openCubeSet R) a) ∧
          IsSigmaStarCoarse (openCubeSet R) a sigmaStarR ∧
          IsKappaCoarse (openCubeSet R) a sigmaStarR kappaR ∧
          IsSigmaCoarse (openCubeSet R) a sigmaR sigmaStarR kappaR ∧
          IsUnit sigmaStarR.det)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicRawCoefficientBounds Q a s t C uL2Sq w := by
  exact
    CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds.of_coefficientBounds_of_multiscaleEllipticity_of_localizedExplicitHeightOfScaleChoice
      Q a s t C uL2Sq
      coarseCaccioppoliTriadicGapScale
      (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
      (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
      (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
      (coarseCaccioppoliCanonicalGradientAcircOne Q a)
      (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s)
      hC.le hs ht hst
      (fun {ρ₁ ρ₂} hρ₁ hlt hρ₂ =>
        coarseCaccioppoliTriadicGapScale_spec hρ₁ hlt hρ₂)
      hcoeff hEll hData hBsum_s hSigmaSum_t


end

end Homogenization
