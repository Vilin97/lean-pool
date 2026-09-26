/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicCanonicalGradient
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.CutoffSizes

/-! # Coefficient Bounds -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Final-facing canonical harmonic Caccioppoli endpoints

This file keeps the last public theorem surface readable.  The coefficient
algebra is still a real remaining hypothesis, but it is now exposed as one
named Chapter-3 schedule rather than as the full expanded
`U/Xi/D/A1/AS` expression at every endpoint.
-/

/-- The exact coefficient-schedule hypothesis left for the fully canonical
harmonic-gradient Caccioppoli endpoint.

It specializes the generic canonical coefficient bounds to the Chapter-3
triadic gap scale, the localized explicit height, the harmonic `L²` profile,
the canonical quantitative cutoff bounds, and the canonical gradient `Acirc`
factors. -/
def CoarseCaccioppoliBoundaryCanonicalHarmonicCoefficientBounds {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) : Prop :=
  CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalCoefficientBounds
    Q a s C uL2Sq
    (fun ρ₁ ρ₂ => (coarseCaccioppoliTriadicGapScale ρ₁ ρ₂ : ℝ))
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C
      coarseCaccioppoliTriadicGapScale)
    (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
    (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
    (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
    (coarseCaccioppoliCanonicalGradientAcircOne Q a)
    (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s)

/-- The same fully canonical harmonic coefficient schedule after the
single-cube coefficient bounds have already been localized to the raw radius
recursion coefficients `Alpha` and `Bcross`.

This is the natural handoff point for the concrete cutoff construction: prove
the two raw inequalities once, then invoke the final Caccioppoli wrapper without
also carrying the multiscale localization data. -/
def CoarseCaccioppoliBoundaryCanonicalHarmonicRawCoefficientBounds {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) : Prop :=
  CoarseCaccioppoliBoundaryRadiusEnergyBridgeCanonicalRawCoefficientBounds
    Q a s t C uL2Sq
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C
      coarseCaccioppoliTriadicGapScale)
    (coarseCaccioppoliCanonicalHarmonicL2Profile Q a w)
    (coarseCaccioppoliQuantitativeCutoffGradientBound Q)
    (coarseCaccioppoliQuantitativeCutoffHessianBound Q)
    (coarseCaccioppoliCanonicalGradientAcircOne Q a)
    (coarseCaccioppoliCanonicalGradientAcircOneSub Q a s)

/-- Note-facing `L²` size control for the harmonic family.

The scalar `uL2Sq` is the squared `L²` size appearing in the public RHS. This
package is the honest public replacement for the `U` component hidden inside
the coefficient-schedule hypothesis: every radius-pair harmonic function has
normalized `L²` norm bounded by `sqrt uL2Sq`. -/
def CoarseCaccioppoliBoundaryCanonicalHarmonicL2SizeControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (uL2Sq : ℝ)
    (w : ℝ → ℝ → AHarmonicFunction a (openCubeSet Q)) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    coarseCaccioppoliCanonicalHarmonicL2Profile Q a w ρ₁ ρ₂ ≤ Real.sqrt uL2Sq

/-- The actual squared normalized `L²` size of a single open-cube harmonic
function, in the units used by the public note RHS. -/
noncomputable def coarseCaccioppoliHarmonicL2Sq {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d)
    (u : AHarmonicFunction a (openCubeSet Q)) : ℝ :=
  (cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toH1 x)) ^ (2 : ℕ)

theorem coarseCaccioppoliHarmonicL2Sq_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d)
    (u : AHarmonicFunction a (openCubeSet Q)) :
    0 ≤ coarseCaccioppoliHarmonicL2Sq Q a u := by
  exact sq_nonneg _

/-- The constant harmonic family has the note-facing `L²` size control with
the actual squared normalized `L²` size. -/
theorem CoarseCaccioppoliBoundaryCanonicalHarmonicL2SizeControl.of_constantFamily
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (u : AHarmonicFunction a (openCubeSet Q)) :
    CoarseCaccioppoliBoundaryCanonicalHarmonicL2SizeControl Q a
      (coarseCaccioppoliHarmonicL2Sq Q a u) (fun _ _ => u) := by
  intro ρ₁ ρ₂ _ _ _
  have hnorm_nonneg :
      0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toH1 x) :=
    cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (fun x => u.toH1 x)
  simp [coarseCaccioppoliCanonicalHarmonicL2Profile,
    coarseCaccioppoliHarmonicL2Sq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hnorm_nonneg]

end

end Homogenization
