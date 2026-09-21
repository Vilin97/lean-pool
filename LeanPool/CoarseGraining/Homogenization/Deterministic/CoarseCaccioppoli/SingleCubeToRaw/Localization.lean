/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.TriadicScale
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.SingleCubeRhs

/-! # Localization -/

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# From single-cube Caccioppoli to the radius raw estimate

This sidecar connects the fixed-cube local estimate produced by
`CoarseCaccioppoliEnergyBridge` to the abstract radius-recursion surface in
`CoarseCaccioppoli`.  It keeps the geometric covering/testing step abstract:
callers provide a single-cube raw estimate for each radius pair and the two
coefficient-localization inequalities that compare the local cube coefficients
to the note's radius coefficients.
-/

/-- Radius-indexed version of the note-facing single-cube local estimate. -/
def CoarseCaccioppoliBoundarySingleCubeRawEstimate {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s C uL2Sq : ℝ) (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ) :
    Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    F ρ₁ ≤
      coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂)
        uL2Sq (F ρ₂)

/-- Coefficient-localization controls that turn the fixed-cube single-cube RHS
into the radius-recursion raw RHS. -/
def CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    0 ≤ F ρ₂ ∧
      coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C (k ρ₁ ρ₂) uL2Sq ≤
        coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂ ∧
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂) ≤
        coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂

/-- Pure coefficient localization for the constant single-cube term. -/
def CoarseCaccioppoliBoundarySingleCubeConstantCoefficientLocalization {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C (k ρ₁ ρ₂) uL2Sq ≤
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂

/-- Pure coefficient localization for the centered single-cube term. -/
def CoarseCaccioppoliBoundarySingleCubeCenteredCoefficientLocalization {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (k h : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂

/-- The pure coefficient localization data needed to convert fixed-cube
single-cube coefficients into the radius-recursion coefficients. -/
def CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundarySingleCubeConstantCoefficientLocalization Q a s C uL2Sq k h ∧
    CoarseCaccioppoliBoundarySingleCubeCenteredCoefficientLocalization Q a s t C k h

/-- Base scale/ellipticity inequality behind the constant coefficient
localization, before multiplying by the common `C sqrt(uL2Sq)` factor. -/
def CoarseCaccioppoliBoundarySingleCubeConstantBaseLocalization {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ) (k h : ℝ → ℝ → ℝ) :
    Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    Real.rpow (3 : ℝ) (k ρ₁ ρ₂) *
        Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) ≤
      coarseCaccioppoliGapInv ρ₁ ρ₂ * Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) *
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)

/-- Base scale/ellipticity inequality behind the centered coefficient
localization, before multiplying by the common `C / (s(1-s))` factor. -/
def CoarseCaccioppoliBoundarySingleCubeCenteredBaseLocalization {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t : ℝ) (k h : ℝ → ℝ → ℝ) :
    Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    Real.rpow (3 : ℝ) (k ρ₁ ρ₂ - h ρ₁ ρ₂) *
        (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)) ≤
      coarseCaccioppoliGapInv ρ₁ ρ₂ *
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)

/-- Base coefficient-localization inequalities before the harmless common
positive factors are restored. -/
def CoarseCaccioppoliBoundarySingleCubeBaseLocalization {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t : ℝ) (k h : ℝ → ℝ → ℝ) :
    Prop :=
  CoarseCaccioppoliBoundarySingleCubeConstantBaseLocalization Q a s k h ∧
    CoarseCaccioppoliBoundarySingleCubeCenteredBaseLocalization Q a s t k h

/-- Scale-only part of the single-cube-to-raw localization. -/
def CoarseCaccioppoliBoundarySingleCubeScaleLocalization
    (s t : ℝ) (k h : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    Real.rpow (3 : ℝ) (k ρ₁ ρ₂) ≤
        coarseCaccioppoliGapInv ρ₁ ρ₂ * Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) ∧
      Real.rpow (3 : ℝ) (k ρ₁ ρ₂ - h ρ₁ ρ₂) ≤
        coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂)

theorem CoarseCaccioppoliBoundarySingleCubeScaleLocalization.of_triadicGapScaleChoice_of_height_lower_bounds
    (s t : ℝ) (k : ℝ → ℝ → ℕ) (h : ℝ → ℝ → ℝ)
    (hs : 0 < s) (ht : 0 < t)
    (hchoice :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hheight_const :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (4 : ℝ) / s ≤ h ρ₁ ρ₂)
    (hheight_cent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (4 : ℝ) / (s + t) ≤ h ρ₁ ρ₂) :
    CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t
      (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ)) h := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let H : ℝ := h ρ₁ ρ₂
  have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    coarseCaccioppoliGapInv_nonneg hlt
  have hpow_le :
      Real.rpow (3 : ℝ) ((k ρ₁ ρ₂ : ℕ) : ℝ) ≤
        81 * coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    simpa [Real.rpow_natCast] using
      (coarseCaccioppoli_pow_scale_le_mul_gapInv_of_triadicGapScaleChoice
        (hchoice hρ₁ hlt hρ₂) hlt)
  have h81_le_const : (81 : ℝ) ≤ Real.rpow (3 : ℝ) (s * H) := by
    have h4le : (4 : ℝ) ≤ s * H := by
      have hh := hheight_const hρ₁ hlt hρ₂
      have hscaled : (4 : ℝ) ≤ H * s := (div_le_iff₀ hs).1 hh
      nlinarith
    calc
      (81 : ℝ) = Real.rpow (3 : ℝ) (4 : ℝ) := by norm_num [Real.rpow_natCast]
      _ ≤ Real.rpow (3 : ℝ) (s * H) := by
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) h4le
  have hst_pos : 0 < s + t := by linarith
  have h81_le_cent : (81 : ℝ) ≤ Real.rpow (3 : ℝ) ((s + t) * H) := by
    have h4le : (4 : ℝ) ≤ (s + t) * H := by
      have hh := hheight_cent hρ₁ hlt hρ₂
      have hscaled : (4 : ℝ) ≤ H * (s + t) := (div_le_iff₀ hst_pos).1 hh
      nlinarith
    calc
      (81 : ℝ) = Real.rpow (3 : ℝ) (4 : ℝ) := by norm_num [Real.rpow_natCast]
      _ ≤ Real.rpow (3 : ℝ) ((s + t) * H) := by
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) h4le
  constructor
  · calc
      Real.rpow (3 : ℝ) ((fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ)) ρ₁ ρ₂)
          ≤ 81 * coarseCaccioppoliGapInv ρ₁ ρ₂ := hpow_le
      _ ≤
          coarseCaccioppoliGapInv ρ₁ ρ₂ * Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by
            have hmul :=
              mul_le_mul_of_nonneg_right h81_le_const hgap_nonneg
            simpa [H, mul_comm, mul_left_comm, mul_assoc] using hmul
  · have hsplit :
        Real.rpow (3 : ℝ)
            (((fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ)) ρ₁ ρ₂) - h ρ₁ ρ₂) =
          Real.rpow (3 : ℝ) ((k ρ₁ ρ₂ : ℕ) : ℝ) *
            Real.rpow (3 : ℝ) (-H) := by
      dsimp [H]
      rw [sub_eq_add_neg]
      exact Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _
    have hscaled :
        Real.rpow (3 : ℝ) ((k ρ₁ ρ₂ : ℕ) : ℝ) * Real.rpow (3 : ℝ) (-H) ≤
          (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) * Real.rpow (3 : ℝ) (-H) := by
      exact mul_le_mul_of_nonneg_right hpow_le
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    have hfactor :
        (81 : ℝ) * Real.rpow (3 : ℝ) (-H) ≤
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * H) := by
      calc
        (81 : ℝ) * Real.rpow (3 : ℝ) (-H)
            ≤ Real.rpow (3 : ℝ) ((s + t) * H) * Real.rpow (3 : ℝ) (-H) := by
              exact mul_le_mul_of_nonneg_right h81_le_cent
                (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        _ = Real.rpow (3 : ℝ) (((s + t) * H) + (-H)) := by
              exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ)) ((s + t) * H) (-H)).symm
        _ = Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * H) := by
              congr 1
              unfold coarseCaccioppoliSigma
              ring
    have htail :
        (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) * Real.rpow (3 : ℝ) (-H) ≤
          coarseCaccioppoliGapInv ρ₁ ρ₂ *
            Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * H) := by
      have hmul := mul_le_mul_of_nonneg_left hfactor hgap_nonneg
      calc
        (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) * Real.rpow (3 : ℝ) (-H)
            = coarseCaccioppoliGapInv ρ₁ ρ₂ *
                ((81 : ℝ) * Real.rpow (3 : ℝ) (-H)) := by ring
        _ ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ *
            Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * H) := hmul
    calc
      Real.rpow (3 : ℝ)
          (((fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ)) ρ₁ ρ₂) - h ρ₁ ρ₂)
          =
        Real.rpow (3 : ℝ) ((k ρ₁ ρ₂ : ℕ) : ℝ) *
          Real.rpow (3 : ℝ) (-H) := hsplit
      _ ≤ (81 * coarseCaccioppoliGapInv ρ₁ ρ₂) * Real.rpow (3 : ℝ) (-H) := hscaled
      _ ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * H) := htail
      _ =
          coarseCaccioppoliGapInv ρ₁ ρ₂ *
            Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) := by
            rfl

/-- Ellipticity-only part of the single-cube-to-raw localization. -/
def CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t : ℝ) : Prop :=
  Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) ≤
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) ∧
    Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
        Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ) ≤
      Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)

theorem CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization.of_monotonicity
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hLambda :
      Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) ≤
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ))
    (hlambda :
      Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ) ≤
        Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ)) :
    CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization Q a s t := by
  constructor
  · exact hLambda
  · have hLambda_nonneg :
        0 ≤ Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) := by
      exact Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs) _
    calc
      Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ)
          ≤
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hlambda hLambda_nonneg
      _ = Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
            rw [thetaRatio_rpow_half_eq_mul_rpow_half_rpow_neg_half Q s t a hs ht]

theorem CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization.of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s t lam Lam : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
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
    CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization Q a s t := by
  have hs1 : s < 1 := by
    linarith
  have ht_one_sub : t < 1 - s := by
    linarith
  have hLambda :
      Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) ≤
        Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) :=
    multiscale_ellipticity_LambdaSq_one_rpow_half_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := Q) (a := a) (t := s) (s := (1 : ℝ)) (lam := lam) (Lam := Lam)
      hs hs1 hEll hData hBsum_s
  have hlambda :
      Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ) ≤
        Real.rpow (lambdaSq Q t (.finite 1) a) (-1 / 2 : ℝ) :=
    multiscale_ellipticity_lambdaSq_one_rpow_neg_half_le_of_lt_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := Q) (a := a) (t := t) (s := 1 - s) (lam := lam) (Lam := Lam)
      ht ht_one_sub hEll hData hSigmaSum_t
  exact
    CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization.of_monotonicity
      Q a hs.le ht.le hLambda hlambda

theorem CoarseCaccioppoliBoundarySingleCubeBaseLocalization.of_scale_of_ellipticity
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t : ℝ)
    (k h : ℝ → ℝ → ℝ)
    (hs : 0 < s) (hs1 : s < 1)
    (hscale : CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t k h)
    (helliptic : CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization Q a s t) :
    CoarseCaccioppoliBoundarySingleCubeBaseLocalization Q a s t k h := by
  constructor
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    have hscale_const := (hscale hρ₁ hlt hρ₂).1
    have hright_nonneg :
        0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) := by
      exact mul_nonneg (coarseCaccioppoliGapInv_nonneg hlt)
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    have hleft_ell_nonneg :
        0 ≤ Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ) := by
      exact Real.rpow_nonneg
        (multiscale_ellipticity_LambdaSq_one_nonneg Q 1 a (by norm_num)) _
    exact mul_le_mul hscale_const helliptic.1 hleft_ell_nonneg hright_nonneg
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    have hscale_cent := (hscale hρ₁ hlt hρ₂).2
    have hright_nonneg :
        0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) := by
      exact mul_nonneg (coarseCaccioppoliGapInv_nonneg hlt)
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    have hell_left_nonneg :
        0 ≤ Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ) := by
      exact mul_nonneg
        (Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le) _)
        (Real.rpow_nonneg
          (multiscale_ellipticity_lambdaSq_one_nonneg Q (1 - s) a (sub_nonneg.mpr hs1.le)) _)
    exact mul_le_mul hscale_cent helliptic.2 hell_left_nonneg hright_nonneg

theorem CoarseCaccioppoliBoundarySingleCubeBaseLocalization.of_scale_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) {s t lam Lam : ℝ}
    (k h : ℝ → ℝ → ℝ)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hscale : CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t k h)
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
    CoarseCaccioppoliBoundarySingleCubeBaseLocalization Q a s t k h := by
  exact
    CoarseCaccioppoliBoundarySingleCubeBaseLocalization.of_scale_of_ellipticity
      Q a s t k h hs (by linarith)
      hscale
      (CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization.of_isEllipticFieldOn_of_isSigmaCoarse
        Q a hs ht hst hEll hData hBsum_s hSigmaSum_t)

theorem CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_baseLocalization
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s < 1)
    (hbase : CoarseCaccioppoliBoundarySingleCubeBaseLocalization Q a s t k h) :
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq k h := by
  constructor
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    have hfactor_nonneg : 0 ≤ C * Real.sqrt uL2Sq := by
      exact mul_nonneg hC (Real.sqrt_nonneg _)
    have hscaled :=
      mul_le_mul_of_nonneg_left (hbase.1 hρ₁ hlt hρ₂) hfactor_nonneg
    calc
      coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C (k ρ₁ ρ₂) uL2Sq
          =
        (C * Real.sqrt uL2Sq) *
          (Real.rpow (3 : ℝ) (k ρ₁ ρ₂) *
            Real.rpow (LambdaSq Q 1 (.finite 1) a) (1 / 2 : ℝ)) := by
            unfold coarseCaccioppoliSingleCubeBoundaryConstantCoeff
            ring
      _ ≤
        (C * Real.sqrt uL2Sq) *
          (coarseCaccioppoliGapInv ρ₁ ρ₂ *
            Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) *
            Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ)) := hscaled
      _ =
        coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂ := by
            unfold coarseCaccioppoliBoundaryCrossCoeffOfHeight
            ring
  · intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    have hden_nonneg : 0 ≤ s * (1 - s) := by
      nlinarith
    have hfactor_nonneg : 0 ≤ C / (s * (1 - s)) := by
      exact div_nonneg hC hden_nonneg
    have hscaled :=
      mul_le_mul_of_nonneg_left (hbase.2 hρ₁ hlt hρ₂) hfactor_nonneg
    calc
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂)
          =
        (C / (s * (1 - s))) *
          (Real.rpow (3 : ℝ) (k ρ₁ ρ₂ - h ρ₁ ρ₂) *
            (Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
              Real.rpow (lambdaSq Q (1 - s) (.finite 1) a) (-1 / 2 : ℝ))) := by
            unfold coarseCaccioppoliSingleCubeBoundaryCenteredCoeff
            ring
      _ ≤
        (C / (s * (1 - s))) *
          (coarseCaccioppoliGapInv ρ₁ ρ₂ *
            Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
            Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)) := hscaled
      _ =
        coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂ := by
            unfold coarseCaccioppoliBoundaryAlphaOfHeight
            ring

theorem CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_scale_of_ellipticity
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s < 1)
    (hscale : CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t k h)
    (helliptic : CoarseCaccioppoliBoundarySingleCubeEllipticityLocalization Q a s t) :
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq k h := by
  exact
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_baseLocalization
      Q a s t C uL2Sq k h hC hs hs1
      (CoarseCaccioppoliBoundarySingleCubeBaseLocalization.of_scale_of_ellipticity
        Q a s t k h hs hs1 hscale helliptic)

theorem CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_scale_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {s t lam Lam : ℝ} (C uL2Sq : ℝ) (k h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hscale : CoarseCaccioppoliBoundarySingleCubeScaleLocalization s t k h)
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
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq k h := by
  exact
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_baseLocalization
      Q a s t C uL2Sq k h hC hs (by linarith)
      (CoarseCaccioppoliBoundarySingleCubeBaseLocalization.of_scale_of_isEllipticFieldOn_of_isSigmaCoarse
        Q a k h hs ht hst hscale hEll hData hBsum_s hSigmaSum_t)

theorem CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_triadicGapScaleChoice_of_height_lower_bounds_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {s t lam Lam : ℝ} (C uL2Sq : ℝ) (k : ℝ → ℝ → ℕ) (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hchoice :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
    (hheight_const :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (4 : ℝ) / s ≤ h ρ₁ ρ₂)
    (hheight_cent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (4 : ℝ) / (s + t) ≤ h ρ₁ ρ₂)
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
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq
      (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ)) h := by
  exact
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_scale_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a C uL2Sq (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ)) h
      hC hs ht hst
      (CoarseCaccioppoliBoundarySingleCubeScaleLocalization.of_triadicGapScaleChoice_of_height_lower_bounds
        s t k h hs ht hchoice hheight_const hheight_cent)
      hEll hData hBsum_s hSigmaSum_t

theorem CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_triadicGapScaleChoice_of_localizedExplicitHeightOfScaleChoice_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {s t lam Lam : ℝ} (C uL2Sq : ℝ) (k : ℝ → ℝ → ℕ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hchoice :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
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
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq
      (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) := by
  have hheight_const :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (4 : ℝ) / s ≤
          coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k ρ₁ ρ₂ := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    simpa [coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice] using
      coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_four_div_s
        Q a s t C (k ρ₁ ρ₂)
  have hheight_cent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (4 : ℝ) / (s + t) ≤
          coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k ρ₁ ρ₂ := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    simpa [coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice] using
      coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_four_div_s_add_t
        Q a (k ρ₁ ρ₂) hs ht
  exact
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_triadicGapScaleChoice_of_height_lower_bounds_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a C uL2Sq k
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      hC hs ht hst hchoice hheight_const hheight_cent hEll hData hBsum_s hSigmaSum_t

/-- Integerized variant of
`of_triadicGapScaleChoice_of_localizedExplicitHeightOfScaleChoice_of_isEllipticFieldOn_of_isSigmaCoarse`.
The resulting height is the real cast of a natural depth, which is the form
needed by the small-cube proof. -/
theorem CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_triadicGapScaleChoice_of_integerizedLocalizedExplicitHeightOfScaleChoice_of_isEllipticFieldOn_of_isSigmaCoarse
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    {s t lam Lam : ℝ} (C uL2Sq : ℝ) (k : ℝ → ℝ → ℕ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hchoice :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂)
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
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq
      (fun ρ₁ ρ₂ => (k ρ₁ ρ₂ : ℝ))
      (coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightOfScaleChoice Q a s t C k) := by
  have hheight_const :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (4 : ℝ) / s ≤
          coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightOfScaleChoice
            Q a s t C k ρ₁ ρ₂ := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    simpa [coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightOfScaleChoice,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
      coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightAtScale_ge_four_div_s
        Q a s t C (k ρ₁ ρ₂)
  have hheight_cent :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        (4 : ℝ) / (s + t) ≤
          coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightOfScaleChoice
            Q a s t C k ρ₁ ρ₂ := by
    intro ρ₁ ρ₂ hρ₁ hlt hρ₂
    simpa [coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightOfScaleChoice,
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
      coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightAtScale_ge_four_div_s_add_t
        Q a (k ρ₁ ρ₂) hs ht
  exact
    CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization.of_triadicGapScaleChoice_of_height_lower_bounds_of_isEllipticFieldOn_of_isSigmaCoarse
      Q a C uL2Sq k
      (coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightOfScaleChoice Q a s t C k)
      hC hs ht hst hchoice hheight_const hheight_cent hEll hData hBsum_s hSigmaSum_t

theorem CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl.of_localization
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    (hnonneg : ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ F ρ)
    (hloc :
      CoarseCaccioppoliBoundarySingleCubeCoefficientLocalization Q a s t C uL2Sq k h) :
    CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq k h F := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  have hρ₂_lower : (1 / 3 : ℝ) ≤ ρ₂ := le_trans hρ₁ hlt.le
  exact ⟨hnonneg hρ₂_lower hρ₂, hloc.1 hρ₁ hlt hρ₂, hloc.2 hρ₁ hlt hρ₂⟩

theorem coarseCaccioppoliSingleCubeBoundaryNoteRhs_le_boundaryRawRhs_of_coefficientControl
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) (F : ℝ → ℝ)
    {ρ₁ ρ₂ : ℝ}
    (hctrl :
      CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq
        k h F)
    (hρ₁ : (1 / 3 : ℝ) ≤ ρ₁) (hlt : ρ₁ < ρ₂) (hρ₂ : ρ₂ ≤ 1) :
    coarseCaccioppoliSingleCubeBoundaryNoteRhs Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂)
        uL2Sq (F ρ₂) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂ * F ρ₂ +
        coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂ *
          Real.sqrt (F ρ₂) := by
  rcases hctrl hρ₁ hlt hρ₂ with ⟨hF, hconst, hcent⟩
  rw [coarseCaccioppoliSingleCubeBoundaryNoteRhs_eq_constant_add_centered,
    coarseCaccioppoliSingleCubeBoundaryConstantRhs_eq_coeff_mul,
    coarseCaccioppoliSingleCubeBoundaryCenteredRhs_eq_coeff_mul]
  have hconstTerm :
      coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C (k ρ₁ ρ₂) uL2Sq *
          Real.sqrt (F ρ₂) ≤
        coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂ *
          Real.sqrt (F ρ₂) := by
    exact mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg _)
  have hcentTerm :
      coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂) *
          F ρ₂ ≤
        coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂ * F ρ₂ := by
    exact mul_le_mul_of_nonneg_right hcent hF
  calc
    coarseCaccioppoliSingleCubeBoundaryConstantCoeff Q a C (k ρ₁ ρ₂) uL2Sq *
          Real.sqrt (F ρ₂) +
        coarseCaccioppoliSingleCubeBoundaryCenteredCoeff Q a s C (k ρ₁ ρ₂) (h ρ₁ ρ₂) *
          F ρ₂
        ≤
      coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂ *
          Real.sqrt (F ρ₂) +
        coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂ * F ρ₂ := by
          exact add_le_add hconstTerm hcentTerm
    _ =
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂ * F ρ₂ +
        coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂ *
          Real.sqrt (F ρ₂) := by
          ring

theorem coarseCaccioppoli_boundary_noteRawEstimate_of_singleCubeRawEstimate
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k h : ℝ → ℝ → ℝ) {F : ℝ → ℝ}
    (hsingle : CoarseCaccioppoliBoundarySingleCubeRawEstimate Q a s C uL2Sq k h F)
    (hctrl :
      CoarseCaccioppoliBoundarySingleCubeToRawCoefficientControl Q a s t C uL2Sq
        k h F) :
    CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  exact le_trans
    (hsingle hρ₁ hlt hρ₂)
    (coarseCaccioppoliSingleCubeBoundaryNoteRhs_le_boundaryRawRhs_of_coefficientControl
      Q a s t C uL2Sq k h F hctrl hρ₁ hlt hρ₂)


end

end Homogenization
