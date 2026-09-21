/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicScalarControls

/-! # Harmonic Gradient Controls -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Harmonic gradient scalar-control bridges

This file contains the Phase 2 scalar-control wrappers specialized to the
eventual Chapter 3 auxiliary scalar field `g = partial_i w`.  It keeps the
long generic scalar-control file below the preferred size threshold while
removing routine energy hypotheses from downstream call sites.
-/

/-- Canonical scalar `Acirc` factor used for gradient components at regularity
`r`.  The final harmonic-gradient wrappers specialize this at `r = 1` and
`r = 1 - s`, so the corresponding lower-bound hypotheses become definitional. -/
noncomputable def coarseCaccioppoliCanonicalGradientAcirc {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (r : ℝ) : ℝ :=
  cubeBesovScaleWeight (-r) Q *
    ((geometricDiscount r 1)⁻¹ *
      Real.rpow (lambdaSq Q r (.finite 1) a) (-1 / 2 : ℝ))

/-- Radius-constant canonical `Acirc` factor at regularity `1`. -/
noncomputable def coarseCaccioppoliCanonicalGradientAcircOne {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) : ℝ → ℝ → ℝ :=
  fun _ _ => coarseCaccioppoliCanonicalGradientAcirc Q a (1 : ℝ)

/-- Radius-constant canonical `Acirc` factor at regularity `1 - s`. -/
noncomputable def coarseCaccioppoliCanonicalGradientAcircOneSub {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) : ℝ → ℝ → ℝ :=
  fun _ _ => coarseCaccioppoliCanonicalGradientAcirc Q a (1 - s)

/-- The canonical gradient `Acirc` factor is nonnegative in the nonnegative
regularity range. -/
theorem coarseCaccioppoliCanonicalGradientAcirc_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ coarseCaccioppoliCanonicalGradientAcirc Q a r := by
  unfold coarseCaccioppoliCanonicalGradientAcirc
  have hdisc_nonneg : 0 ≤ (geometricDiscount r 1)⁻¹ := by
    exact inv_nonneg.mpr (geometricDiscount_nonneg (by simpa using hr))
  exact
    mul_nonneg (cubeBesovScaleWeight_nonneg (-r) Q)
      (mul_nonneg hdisc_nonneg
        (Real.rpow_nonneg (multiscale_ellipticity_lambdaSq_one_nonneg Q r a hr) _))

/-- The canonical `r = 1` gradient `Acirc` factor is nonnegative. -/
theorem coarseCaccioppoliCanonicalGradientAcircOne_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (ρ₁ ρ₂ : ℝ) :
    0 ≤ coarseCaccioppoliCanonicalGradientAcircOne Q a ρ₁ ρ₂ := by
  exact
    coarseCaccioppoliCanonicalGradientAcirc_nonneg Q a
      (by norm_num : 0 ≤ (1 : ℝ))

/-- The canonical `r = 1 - s` gradient `Acirc` factor is nonnegative when
`s ≤ 1`. -/
theorem coarseCaccioppoliCanonicalGradientAcircOneSub_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ} (hs1 : s ≤ 1) (ρ₁ ρ₂ : ℝ) :
    0 ≤ coarseCaccioppoliCanonicalGradientAcircOneSub Q a s ρ₁ ρ₂ := by
  exact
    coarseCaccioppoliCanonicalGradientAcirc_nonneg Q a
      (sub_nonneg.mpr hs1)

/-- The strict nondegeneracy inputs still needed for the canonical gradient
`Acirc` specialization.  Nonnegativity of the `1 - s` canonical factor is
derived separately from `s < 1`. -/
def CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    0 < cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ∧
    0 < coarseCaccioppoliCanonicalGradientAcircOne Q a ρ₁ ρ₂ ∧
    0 <
      Real.sqrt (cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))

/-- Build the scalar-positive-factor package for the canonical gradient
`Acirc` factors from the genuinely strict nondegeneracy inputs. -/
theorem CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors.of_canonicalGradientAcirc
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q))
    (hs1 : s < 1)
    (hpos : CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w) :
    CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w
      (coarseCaccioppoliCanonicalGradientAcircOne Q a)
      (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s) := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  obtain ⟨hU, hA1, henergy⟩ := hpos hρ₁ hlt hρ₂
  exact
    ⟨hU, hA1,
      coarseCaccioppoliCanonicalGradientAcircOneSub_nonneg Q a hs1.le ρ₁ ρ₂,
      henergy⟩

/-- A component of the gradient of an open-cube harmonic function is `L²` for
the normalized closed-cube measure. -/
theorem memLp_harmonicGradientComponent_normalizedCubeMeasure {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (w : AHarmonicFunction a (openCubeSet Q)) (i : Fin d) :
    MeasureTheory.MemLp (fun x => w.toH1.grad x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  have hgrad :
      MeasureTheory.MemLp (fun x => w.toH1.grad x) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q w.toH1.grad_memVectorL2
  exact memLp_component_of_memLp (fun x => w.toH1.grad x) i hgrad

/-- Summability of the `sigma_*^{-1}` series improves when the geometric
regularity exponent is increased. -/
theorem summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {t r : ℝ}
    (ht : 0 < t) (htr : t < r)
    (hsum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    Summable (fun n : ℕ =>
      geometricWeight r 1 n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  refine summable_geometricWeight_one_of_lt ?_ ht htr hsum_t
  intro n
  exact
    Real.rpow_nonneg
      (maxDescendantSigmaStarInvNormAtScale_nonneg Q
        (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a)
      _

/-- Concrete harmonic-gradient projected/circ package using the already
available flux-energy controls to supply scalar-energy nonnegativity and
integrability.  The projected mean-zero Poincare estimate for `partial_i w`
remains the genuine analytic input. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_harmonicGradientComponent_of_fluxEnergyControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (Acirc1 AcircS : ℝ → ℝ → ℝ)
    (hs1 : s < 1)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hsum1 :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N)
    (hAcirc1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-1) Q *
            ((geometricDiscount (1 : ℝ) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          Acirc1 ρ₁ ρ₂)
    (hAcircS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-(1 - s)) Q *
            ((geometricDiscount (1 - s) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          AcircS ρ₁ ρ₂) :
    _root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds
      Q a s C w (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i) Acirc1 AcircS := by
  refine
    _root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_harmonicGradientComponent
      Q a s C w i Acirc1 AcircS hs1 ?_ ?_ hgrad hsum1 hsumS hproj hAcirc1 hAcircS
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    exact (hfluxEnergy hρ₁ hlt hρ₂).1
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    exact (hfluxEnergy hρ₁ hlt hρ₂).2.1

/-- Concrete harmonic-gradient projected/circ package with the canonical
gradient `Acirc` factors.  This removes the two explicit `Acirc` lower-bound
hypotheses from the projected/circ handoff. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_harmonicGradientComponent_of_fluxEnergyControls_canonicalGradientAcirc
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hs1 : s < 1)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hsum1 :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N) :
    _root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds
      Q a s C w (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i)
      (coarseCaccioppoliCanonicalGradientAcircOne Q a)
      (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s) := by
  exact
    _root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_harmonicGradientComponent_of_fluxEnergyControls
      Q a s C w i
      (coarseCaccioppoliCanonicalGradientAcircOne Q a)
      (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s)
      hs1 hfluxEnergy hgrad hsum1 hsumS hproj
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)

/-- Full scalar-control factors for `g = partial_i w`, with scalar-energy
nonnegativity/integrability taken from the flux-energy controls already used
by the single-cube Caccioppoli bridge. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_harmonicGradientComponent_of_fluxEnergyControls
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (Acirc1 AcircS : ℝ → ℝ → ℝ)
    (hpos :
      _root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors
        Q a w Acirc1 AcircS)
    (hs1 : s < 1)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hsum1 :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N)
    (hAcirc1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-1) Q *
            ((geometricDiscount (1 : ℝ) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          Acirc1 ρ₁ ρ₂)
    (hAcircS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-(1 - s)) Q *
            ((geometricDiscount (1 - s) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          AcircS ρ₁ ρ₂) :
    _root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalScalarControlFactors
      Q a s C w (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i) Acirc1 AcircS := by
  exact
    _root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_projectedPoincareCircBounds
      Q a s C w (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i) Acirc1 AcircS hpos
      (_root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_harmonicGradientComponent_of_fluxEnergyControls
        Q a s C w i Acirc1 AcircS hs1 hfluxEnergy hgrad hsum1 hsumS hproj hAcirc1
        hAcircS)

/-- Full scalar-control factors for `g = partial_i w` with the canonical
gradient `Acirc` factors. -/
theorem
    CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_harmonicGradientComponent_of_fluxEnergyControls_canonicalGradientAcirc
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s C : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (hpos :
      CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w)
    (hs1 : s < 1)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hsum1 :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hsumS :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N) :
    _root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalScalarControlFactors
      Q a s C w (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i)
      (coarseCaccioppoliCanonicalGradientAcircOne Q a)
      (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s) := by
  exact
    _root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalScalarControlFactors.of_positiveFactors_of_projectedPoincareCircBounds
      Q a s C w (fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i)
      (coarseCaccioppoliCanonicalGradientAcircOne Q a)
      (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s)
      (_root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors.of_canonicalGradientAcirc
        Q a s w hs1 hpos)
      (_root_.Homogenization.CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_harmonicGradientComponent_of_fluxEnergyControls_canonicalGradientAcirc
        Q a s C w i hs1 hfluxEnergy hgrad hsum1 hsumS hproj)

/-- Boundary canonical harmonic Caccioppoli specialized to the concrete scalar
auxiliary field `g = partial_i w`.  The theorem builds the projected/circ
package from flux-energy controls plus gradient-energy controls; projected
mean-zero Poincare for `partial_i w` is still an explicit analytic input. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_harmonicGradientComponent_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        F ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N)
    (hAcirc1_lower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-1) Q *
            ((geometricDiscount (1 : ℝ) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          Acirc1 ρ₁ ρ₂)
    (hAcircS_lower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-(1 - s)) Q *
            ((geometricDiscount (1 - s) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          AcircS ρ₁ ρ₂)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hSigmaSum_one :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hs, hst]) hSigmaSum_t
  have hSigmaSum_one_sub_s :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hst]) hSigmaSum_t
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_projectedPoincareCircBounds_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (w := w)
      (g := fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i)
      (Acirc1 := Acirc1) (AcircS := AcircS) (U := U) (A1 := A1) (AS := AS)
      hC hs ht hst hu hnonneg hbounded hscale hlower henergyAvg
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicGradientComponent_normalizedCubeMeasure Q a (w ρ₁ ρ₂) i)
      hfluxEnergy hpositiveFactors
      (CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_harmonicGradientComponent_of_fluxEnergyControls
        Q a s C w i Acirc1 AcircS hs1 hfluxEnergy hgrad hSigmaSum_one
        hSigmaSum_one_sub_s hproj hAcirc1_lower hAcircS_lower)
      hU hA1 hAS hcoeff hEll hData hSigmaSum_t

/-- Interior canonical harmonic Caccioppoli specialized to
`g = partial_i w`. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_harmonicGradientComponent_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (Acirc1 AcircS U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G₀)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G₀ ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G₀)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        G₀ ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          G₀ ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors Q a w Acirc1 AcircS)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N)
    (hAcirc1_lower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-1) Q *
            ((geometricDiscount (1 : ℝ) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          Acirc1 ρ₁ ρ₂)
    (hAcircS_lower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeBesovScaleWeight (-(1 - s)) Q *
            ((geometricDiscount (1 - s) 1)⁻¹ *
              Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) ≤
          AcircS ρ₁ ρ₂)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        Acirc1 ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        AcircS ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hSigmaSum_one :
      Summable (fun n : ℕ =>
        geometricWeight (1 : ℝ) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hs, hst]) hSigmaSum_t
  have hSigmaSum_one_sub_s :
      Summable (fun n : ℕ =>
        geometricWeight (1 - s) 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_maxDescendantSigmaStarInvNormAtScale_geometricWeight_one_of_lt
      Q a ht (by nlinarith [hst]) hSigmaSum_t
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_projectedPoincareCircBounds_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (G₀ := G₀) (w := w)
      (g := fun ρ₁ ρ₂ x => (w ρ₁ ρ₂).toH1.grad x i)
      (Acirc1 := Acirc1) (AcircS := AcircS) (U := U) (A1 := A1) (AS := AS)
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale hlower henergyAvg
      (by
        intro ρ₁ ρ₂ _ _ _
        exact memLp_harmonicGradientComponent_normalizedCubeMeasure Q a (w ρ₁ ρ₂) i)
      hfluxEnergy hpositiveFactors
      (CoarseCaccioppoliBoundaryCanonicalProjectedPoincareCircBounds.of_harmonicGradientComponent_of_fluxEnergyControls
        Q a s C w i Acirc1 AcircS hs1 hfluxEnergy hgrad hSigmaSum_one
        hSigmaSum_one_sub_s hproj hAcirc1_lower hAcircS_lower)
      hU hA1 hAS hcoeff hEll hData hSigmaSum_t

/-- Boundary canonical harmonic Caccioppoli specialized to the canonical
gradient `Acirc` factors.  Compared with
`...of_harmonicGradientComponent...`, the `Acirc` lower-bound hypotheses are
now definitional. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalGradientAcirc_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        F ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        coarseCaccioppoliCanonicalGradientAcircOne Q a ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        coarseCaccioppoliCanonicalGradientAcircOneSub Q a s ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  have hs1 : s < 1 := by nlinarith [ht, hst]
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_harmonicGradientComponent_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (w := w) (i := i)
      (Acirc1 := coarseCaccioppoliCanonicalGradientAcircOne Q a)
      (AcircS := coarseCaccioppoliCanonicalGradientAcircOneSub Q a s)
      (U := U) (A1 := A1) (AS := AS)
      hC hs ht hst hu hnonneg hbounded hscale hlower henergyAvg
      hfluxEnergy
      (CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors.of_canonicalGradientAcirc
        Q a s w hs1 hpositiveFactors)
      hgrad hproj
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      hU hA1 hAS hcoeff hEll hData hSigmaSum_t

/-- Interior canonical harmonic Caccioppoli specialized to the canonical
gradient `Acirc` factors. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalGradientAcirc_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (U A1 AS : ℝ → ℝ → ℝ)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G₀)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G₀ ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G₀)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        G₀ ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          G₀ ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hA1 :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        coarseCaccioppoliCanonicalGradientAcircOne Q a ρ₁ ρ₂ ≤ A1 ρ₁ ρ₂)
    (hAS :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        coarseCaccioppoliCanonicalGradientAcircOneSub Q a s ρ₁ ρ₂ ≤ AS ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        A1 AS)
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  have hs1 : s < 1 := by nlinarith [ht, hst]
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_harmonicGradientComponent_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (G₀ := G₀) (w := w) (i := i)
      (Acirc1 := coarseCaccioppoliCanonicalGradientAcircOne Q a)
      (AcircS := coarseCaccioppoliCanonicalGradientAcircOneSub Q a s)
      (U := U) (A1 := A1) (AS := AS)
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale hlower henergyAvg
      hfluxEnergy
      (CoarseCaccioppoliBoundaryCanonicalScalarPositiveFactors.of_canonicalGradientAcirc
        Q a s w hs1 hpositiveFactors)
      hgrad hproj
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      hU hA1 hAS hcoeff hEll hData hSigmaSum_t

/-- Boundary canonical harmonic Caccioppoli with the canonical gradient
`Acirc` factors also installed in the coefficient-bound package.  This removes
the caller-facing `hA1` and `hAS` comparison hypotheses from the canonical
gradient endpoint. -/
theorem
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalGradientAcircCoefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (U : ℝ → ℝ → ℝ)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hbounded : CoarseCaccioppoliRadiusBoundedAbove F)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        F ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) = F ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_boundary_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalGradientAcirc_of_coefficientBounds_of_localizationData_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (w := w) (i := i)
      (U := U)
      (A1 := coarseCaccioppoliCanonicalGradientAcircOne Q a)
      (AS := coarseCaccioppoliCanonicalGradientAcircOneSub Q a s)
      hC hs ht hst hu hnonneg hbounded hscale hlower henergyAvg
      hfluxEnergy hpositiveFactors hgrad hproj hU
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      hcoeff hEll hData hSigmaSum_t

/-- Interior canonical harmonic Caccioppoli with the canonical gradient
`Acirc` factors also installed in the coefficient-bound package. -/
theorem
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalGradientAcircCoefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t C uL2Sq : ℝ) {lam Lam : ℝ}
    (k : ℝ → ℝ → ℕ) {F G₀ : ℝ → ℝ}
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) (i : Fin d)
    (U : ℝ → ℝ → ℝ)
    (hC : 0 < C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hagree : CoarseCaccioppoliRadiusAgreement F G₀)
    (hG_nonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ G₀ ρ)
    (hG_bounded : CoarseCaccioppoliRadiusBoundedAbove G₀)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hlower :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) → (hlt : ρ₁ < ρ₂) →
        (hρ₂ : ρ₂ ≤ 1) →
        G₀ ρ₁ ≤
          cubeAverage Q
            (fun x =>
              QuantitativeCubeCutoff.canonicalFun Q ρ₁ ρ₂ x *
                scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (henergyAvg :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeAverage Q (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x) =
          G₀ ρ₂)
    (hfluxEnergy :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliFluxEnergyControls Q a s
          (fun x => matVecMul (a x) ((w ρ₁ ρ₂).toH1.grad x))
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hpositiveFactors :
      CoarseCaccioppoliBoundaryCanonicalGradientPositiveFactors Q a w)
    (hgrad :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CubeAverageGradientEnergyControl Q a (fun x => (w ρ₁ ρ₂).toH1.grad x)
          (fun x => scalarVariationEnergyIntegrand a (w ρ₁ ρ₂) x))
    (hproj :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∀ N : ℕ,
        CubeDescendantProjectedDualMeanZeroPoincareEstimate Q C
          (cubeFluctuation Q (fun x => (w ρ₁ ρ₂).toH1 x))
          (fun x => (w ρ₁ ρ₂).toH1.grad x i) N)
    (hU :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => (w ρ₁ ρ₂).toH1 x) ≤ U ρ₁ ρ₂)
    (hcoeff :
      CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds Q a s C uL2Sq
        (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
        U
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
        (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
        (coarseCaccioppoliCanonicalGradientAcircOne Q a)
        (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s))
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
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ))) :
    F (1 / 3 : ℝ) ≤
      coarseCaccioppoliInteriorExplicitHeightBound Q a s t C uL2Sq := by
  exact
    coarseCaccioppoli_interior_qone_of_canonicalQuantitativeCutoff_of_aHarmonicFamily_of_positiveFactors_of_canonicalGradientAcirc_of_coefficientBounds_of_localizationData_of_radiusAgreement_of_localizedExplicitHeightOfScaleChoice
      (Q := Q) (a := a) (s := s) (t := t) (C := C) (uL2Sq := uL2Sq)
      (k := k) (F := F) (G₀ := G₀) (w := w) (i := i)
      (U := U)
      (A1 := coarseCaccioppoliCanonicalGradientAcircOne Q a)
      (AS := coarseCaccioppoliCanonicalGradientAcircOneSub Q a s)
      hC hs ht hst hu hagree hG_nonneg hG_bounded hscale hlower henergyAvg
      hfluxEnergy hpositiveFactors hgrad hproj hU
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      (by
        intro ρ₁ ρ₂ _ _ _
        exact le_rfl)
      hcoeff hEll hData hSigmaSum_t

end

end Homogenization
