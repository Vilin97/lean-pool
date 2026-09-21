/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantitiesBasic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Basic -/

namespace Homogenization

noncomputable section

open scoped BigOperators

/-!
# Deterministic coarse-grained Caccioppoli backbones

This file isolates the radius-iteration backbone of the Chapter-3 coarse
Caccioppoli estimate.

At the current checkpoint the cutoff/Besov argument producing the local
recursive inequality is still upstream work. The theorems here therefore keep
that step as an explicit hypothesis and package the quantitative iteration and
multiscale prefactors that consume it.
-/

/-- Small real-arithmetic helper: `s * (1 - s) ≥ 0` whenever `0 ≤ s ≤ 1`.
Used in several coarse-Caccioppoli non-negativity chains. -/
theorem mul_one_sub_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    0 ≤ s * (1 - s) :=
  mul_nonneg h0 (by linarith)

/-- The Chapter-3 gap parameter `σ = 1 - s - t`. -/
def coarseCaccioppoliSigma (s t : ℝ) : ℝ :=
  1 - s - t

/-- The recursion exponent `β = 2 (1 - t) / (1 - s - t)` appearing in the
radius-iteration step of the coarse Caccioppoli proof. -/
def coarseCaccioppoliBeta (s t : ℝ) : ℝ :=
  2 * (1 - t) / coarseCaccioppoliSigma s t

/-- The note exponent `2s / (1 - s - t)` attached to the recursive error
prefactor. -/
def coarseCaccioppoliPower (s t : ℝ) : ℝ :=
  2 * s / coarseCaccioppoliSigma s t

/-- Upper boundedness on the radius interval used in the Chapter-3
radius-iteration argument. -/
def CoarseCaccioppoliRadiusBoundedAbove (F : ℝ → ℝ) : Prop :=
  ∃ B, ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → F ρ ≤ B

/-- The one-step recursive inequality produced by the local cutoff/Besov part
of the coarse Caccioppoli proof. -/
def CoarseCaccioppoliRadiusRecurrence (F : ℝ → ℝ) (A β : ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    F ρ₁ ≤ (1 / 2 : ℝ) * F ρ₂ + A * Real.rpow (ρ₂ - ρ₁) (-β)

/-- The deterministic radius sequence `ρ_n = 1 - 2 / (3 (n + 1))`,
starting at `1/3` and increasing to `1`. -/
def coarseCaccioppoliRadiusSequence (n : ℕ) : ℝ :=
  1 - 2 / (3 * (n + 1))

/-- The same recursive inequality specialized to the deterministic Chapter-3
radius sequence `ρ_n`. This is the concrete iteration interface needed when a
local cutoff construction only supplies the consecutive pairs
`(ρ_n, ρ_{n+1})`. -/
def CoarseCaccioppoliRadiusSequenceRecurrence (F : ℝ → ℝ) (A β : ℝ) : Prop :=
  ∀ n : ℕ,
    F (coarseCaccioppoliRadiusSequence n) ≤
      (1 / 2 : ℝ) * F (coarseCaccioppoliRadiusSequence (n + 1)) +
        A * Real.rpow
          (coarseCaccioppoliRadiusSequence (n + 1) -
            coarseCaccioppoliRadiusSequence n)
          (-β)

/-- The `n`th weighted error term in the deterministic radius-iteration
argument. -/
def coarseCaccioppoliRadiusIterationTerm (β : ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n *
    Real.rpow
      (coarseCaccioppoliRadiusSequence (n + 1) - coarseCaccioppoliRadiusSequence n)
      (-β)

/-- The deterministic radius-iteration constant obtained by summing the
geometric error terms coming from `coarseCaccioppoliRadiusIterationTerm`. -/
def coarseCaccioppoliRadiusIterationConst (β : ℝ) : ℝ :=
  ∑' n : ℕ, coarseCaccioppoliRadiusIterationTerm β n

/-- Midpoint radius used by the buffered cutoff version of the coarse
Caccioppoli single-step estimate. -/
def coarseCaccioppoliBufferedCutoffRadius (ρ₁ ρ₂ : ℝ) : ℝ :=
  (ρ₁ + ρ₂) / 2

theorem coarseCaccioppoliBufferedCutoffRadius_between {ρ₁ ρ₂ : ℝ}
    (hlt : ρ₁ < ρ₂) :
    ρ₁ < coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂ ∧
      coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂ < ρ₂ := by
  unfold coarseCaccioppoliBufferedCutoffRadius
  constructor <;> linarith

theorem coarseCaccioppoliBufferedCutoffRadius_outer_gap (ρ₁ ρ₂ : ℝ) :
    ρ₂ - coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂ =
      (ρ₂ - ρ₁) / 2 := by
  unfold coarseCaccioppoliBufferedCutoffRadius
  ring

theorem coarseCaccioppoliBufferedCutoffRadius_inner_gap (ρ₁ ρ₂ : ℝ) :
    coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂ - ρ₁ =
      (ρ₂ - ρ₁) / 2 := by
  unfold coarseCaccioppoliBufferedCutoffRadius
  ring

/-- The note-facing recursive right-hand side in the boundary coarse
Caccioppoli proof, after the local cutoff/Besov step has produced the
radius-recursion with exponent `coarseCaccioppoliBeta s t`. -/
def coarseCaccioppoliBoundaryRecursionRhs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) : ℝ :=
  C *
    Real.rpow
      (C / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
      (coarseCaccioppoliPower s t) *
    LambdaSq Q s (.finite 1) a *
    uL2Sq

/-- Split version of the note-facing recursive right-hand side.  `Calpha`
controls the height/absorption branch, while `Ccross` controls the local
cross coefficient.  Keeping these separate prevents a centered-gradient budget
from drifting into the purely local quadratic branch. -/
def coarseCaccioppoliBoundaryRecursionRhsSplit {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t Calpha Ccross uL2Sq : ℝ) : ℝ :=
  Ccross *
    Real.rpow
      (Calpha / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
      (coarseCaccioppoliPower s t) *
    LambdaSq Q s (.finite 1) a *
    uL2Sq

theorem coarseCaccioppoliBoundaryRecursionRhsSplit_self {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ) :
    coarseCaccioppoliBoundaryRecursionRhsSplit Q a s t C C uL2Sq =
      coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq := by
  rfl

/-- The first note-facing boundary coarse Caccioppoli prefactor obtained from
the radius-iteration lemma under an explicit recursive hypothesis. -/
def coarseCaccioppoliBoundaryBound {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) : ℝ :=
  coarseCaccioppoliRadiusIterationConst (coarseCaccioppoliBeta s t) *
    coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq

/-- Literal normalized `m = 0` right-hand side from the note's boundary
coarse Caccioppoli proposition.

Here `C` represents the dimension-dependent constant in the note statement,
not the intermediate projected-Poincare constant used by some lower-level
single-cube wrappers. -/
def coarseCaccioppoliBoundaryNoteRhs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) : ℝ :=
  Real.rpow (C / coarseCaccioppoliSigma s t)
      (2 + 4 * s / coarseCaccioppoliSigma s t) *
    Real.rpow s (-2 * s / coarseCaccioppoliSigma s t) *
    Real.rpow (ThetaRatio Q s t a) (s / coarseCaccioppoliSigma s t) *
    LambdaSq Q s (.finite 1) a *
    uL2Sq

/-- The current interior wrapper reuses the same radius-iteration constant and
recursive prefactor as the boundary version once an interior recursive
estimate has been supplied. -/
def coarseCaccioppoliInteriorBound {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) : ℝ :=
  coarseCaccioppoliBoundaryBound Q a s t C uL2Sq

/-- Literal normalized `m = 0` right-hand side from the note's interior
coarse Caccioppoli corollary. -/
def coarseCaccioppoliInteriorNoteRhs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) : ℝ :=
  coarseCaccioppoliBoundaryNoteRhs Q a s t C uL2Sq

/-- The honest pre-Besov recursive right-hand side obtained from the note's
explicit height choice `h = max {k + 4, ceil(...)}`. The first summand records
the `k + 4` branch; the second records the logarithmic branch. -/
def coarseCaccioppoliBoundaryExplicitHeightRecursionRhs {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) : ℝ :=
  (6561 : ℝ) * 6561 * C ^ (2 : ℕ) * LambdaSq Q s (.finite 1) a * uL2Sq +
    ((9 : ℝ) * Real.rpow (4 : ℝ) (coarseCaccioppoliPower s t) *
      Real.rpow (81 : ℝ) (coarseCaccioppoliPower s t)) *
      C * coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq

/-- Split explicit-height recursive right-hand side.  The left branch only
uses the cross/local constant `Ccross`; the logarithmic-height branch uses
`Calpha` through the height choice and `Ccross` through the cross coefficient. -/
def coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) : ℝ :=
  (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) *
      LambdaSq Q s (.finite 1) a * uL2Sq +
    ((9 : ℝ) * Real.rpow (4 : ℝ) (coarseCaccioppoliPower s t) *
      Real.rpow (81 : ℝ) (coarseCaccioppoliPower s t)) *
      Ccross *
        coarseCaccioppoliBoundaryRecursionRhsSplit Q a s t Calpha Ccross uL2Sq

theorem coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit_self {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ) :
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit Q a s t C C uL2Sq =
      coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq := by
  rfl

/-- The boundary radius-iteration bound driven by the explicit-height recursive
right-hand side above. This is the final pre-Besov boundary surface with no
remaining extra cross-scale hypothesis. -/
def coarseCaccioppoliBoundaryExplicitHeightBound {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) : ℝ :=
  coarseCaccioppoliRadiusIterationConst (coarseCaccioppoliBeta s t) *
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq

/-- Split boundary radius-iteration bound driven by
`coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit`. -/
def coarseCaccioppoliBoundaryExplicitHeightBoundSplit {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t Calpha Ccross uL2Sq : ℝ) : ℝ :=
  coarseCaccioppoliRadiusIterationConst (coarseCaccioppoliBeta s t) *
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
      Q a s t Calpha Ccross uL2Sq

theorem coarseCaccioppoliBoundaryExplicitHeightBoundSplit_self {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ) :
    coarseCaccioppoliBoundaryExplicitHeightBoundSplit Q a s t C C uL2Sq =
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq := by
  rw [coarseCaccioppoliBoundaryExplicitHeightBoundSplit,
    coarseCaccioppoliBoundaryExplicitHeightBound,
    coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit_self]

/-- The interior pre-Besov explicit-height bound reuses the same recursive
prefactor as the boundary version, once the centered local estimate has been
transported into the iteration backbone. -/
def coarseCaccioppoliInteriorExplicitHeightBound {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) : ℝ :=
  coarseCaccioppoliBoundaryExplicitHeightBound Q a s t C uL2Sq

theorem coarseCaccioppoliInteriorExplicitHeightBound_le_noteRhs_of_boundary
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Cinternal Cnote uL2Sq : ℝ)
    (h :
      coarseCaccioppoliBoundaryExplicitHeightBound Q a s t Cinternal uL2Sq ≤
        coarseCaccioppoliBoundaryNoteRhs Q a s t Cnote uL2Sq) :
    coarseCaccioppoliInteriorExplicitHeightBound Q a s t Cinternal uL2Sq ≤
      coarseCaccioppoliInteriorNoteRhs Q a s t Cnote uL2Sq := by
  simpa [coarseCaccioppoliInteriorExplicitHeightBound, coarseCaccioppoliInteriorNoteRhs] using h

/-- Agreement of two radius-dependent quantities on the interval used by the
deterministic iteration. In the interior proof this packages the fact that
centering `v := u - (u)_Q` does not change the gradient quantity being iterated.
-/
def CoarseCaccioppoliRadiusAgreement (F G : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ → ρ ≤ 1 → F ρ = G ρ

/-- Pre-absorption local input for the boundary coarse Caccioppoli proof: after
the cutoff/Besov step and coefficient bookkeeping, the local estimate has an
absorbable `sqrt (F ρ₂)` cross term whose square is controlled by the final
note-facing recursion right-hand side. -/
def CoarseCaccioppoliBoundaryPreRecurrence {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    ∃ α B : ℝ,
      0 ≤ α ∧ α ≤ (1 / 4 : ℝ) ∧ 0 ≤ B ∧
      F ρ₁ ≤ α * F ρ₂ + B * Real.sqrt (F ρ₂) ∧
      B ^ (2 : ℕ) ≤
        coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t)

/-- Pre-recurrence surface with the enlarged explicit-height recursion
prefactor.  This is the natural middle layer for localized height choices,
whose cross term is controlled by `coarseCaccioppoliBoundaryExplicitHeightRecursionRhs`
rather than by the smaller raw note prefactor. -/
def CoarseCaccioppoliBoundaryExplicitHeightPreRecurrence {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    ∃ α B : ℝ,
      0 ≤ α ∧ α ≤ (1 / 4 : ℝ) ∧ 0 ≤ B ∧
      F ρ₁ ≤ α * F ρ₂ + B * Real.sqrt (F ρ₂) ∧
      B ^ (2 : ℕ) ≤
        coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t)

/-- The current interior middle layer reuses the same pre-recurrence surface as
the boundary version; the eventual difference is only in how the local estimate
is produced. -/
def CoarseCaccioppoliInteriorPreRecurrence {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (F : ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryPreRecurrence Q a s t C uL2Sq F

/-- Interior version of the explicit-height pre-recurrence surface. -/
def CoarseCaccioppoliInteriorExplicitHeightPreRecurrence {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (F : ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryExplicitHeightPreRecurrence Q a s t C uL2Sq F

/-- Abstract local single-cube estimate before coefficient bookkeeping and
Young absorption. The note's estimate
`e.cg.Caccioppoli.single.cube.boundary.deterministic.theory`
has exactly this shape. -/
def CoarseCaccioppoliBoundaryRawEstimate (F : ℝ → ℝ) (α B : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    F ρ₁ ≤ α ρ₁ ρ₂ * F ρ₂ + B ρ₁ ρ₂ * Real.sqrt (F ρ₂)

/-- Abstract coefficient bookkeeping for the local single-cube estimate. This
packages the note's choice of `h` and the conversion of localized coefficient
factors into the final note-facing recursion right-hand side. -/
def CoarseCaccioppoliBoundaryCoefficientControl {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (α B : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    0 ≤ α ρ₁ ρ₂ ∧ α ρ₁ ρ₂ ≤ (1 / 4 : ℝ) ∧ 0 ≤ B ρ₁ ρ₂ ∧
      (B ρ₁ ρ₂) ^ (2 : ℕ) ≤
        coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t)

/-- The current interior middle layer uses the same abstract local single-cube
surface as the boundary version. -/
def CoarseCaccioppoliInteriorRawEstimate (F : ℝ → ℝ) (α B : ℝ → ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryRawEstimate F α B

/-- The current interior coefficient bookkeeping surface also matches the
boundary one. -/
def CoarseCaccioppoliInteriorCoefficientControl {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (α B : ℝ → ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryCoefficientControl Q a s t C uL2Sq α B

/-- The inverse gap factor appearing in the radius-recursion estimates. -/
def coarseCaccioppoliGapInv (ρ₁ ρ₂ : ℝ) : ℝ :=
  Real.rpow (ρ₂ - ρ₁) (-1 : ℝ)

/-- The note's triadic scale choice for the gap `ρ₂ - ρ₁`: a natural scale
`k` satisfying `3⁻⁴ (ρ₂ - ρ₁) ≤ 3⁻ᵏ ≤ 3⁻³ (ρ₂ - ρ₁)`. -/
def CoarseCaccioppoliTriadicGapScaleChoice (k : ℕ) (ρ₁ ρ₂ : ℝ) : Prop :=
  (1 / 81 : ℝ) * (ρ₂ - ρ₁) ≤ ((3 : ℝ) ^ k)⁻¹ ∧
    ((3 : ℝ) ^ k)⁻¹ ≤ (1 / 27 : ℝ) * (ρ₂ - ρ₁)

/-- Note-shaped boundary coefficient in front of `F ρ₂` after replacing the
dyadic-scale factor by an inverse gap and keeping the auxiliary height choice
`h`. -/
def coarseCaccioppoliBoundaryAlphaOfHeight {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C : ℝ) (h : ℝ → ℝ → ℝ) (ρ₁ ρ₂ : ℝ) : ℝ :=
  C / (s * (1 - s)) *
    coarseCaccioppoliGapInv ρ₁ ρ₂ *
    Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
    Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)

/-- Note-shaped boundary cross coefficient in front of `sqrt (F ρ₂)` after
replacing the dyadic-scale factor by an inverse gap and keeping the auxiliary
height choice `h`. -/
def coarseCaccioppoliBoundaryCrossCoeffOfHeight {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s C uL2Sq : ℝ) (h : ℝ → ℝ → ℝ) (ρ₁ ρ₂ : ℝ) : ℝ :=
  C *
    coarseCaccioppoliGapInv ρ₁ ρ₂ *
    Real.rpow (3 : ℝ) (s * h ρ₁ ρ₂) *
    Real.rpow (LambdaSq Q s (.finite 1) a) (1 / 2 : ℝ) *
    Real.sqrt uL2Sq

/-- The current note-shaped raw boundary estimate: the local single-cube input
has the note's coefficient structure, parameterized by the auxiliary height
choice `h`. -/
def CoarseCaccioppoliBoundaryNoteRawEstimate {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (h : ℝ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryRawEstimate F
    (coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h)
    (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h)

/-- Split version of the note-shaped raw boundary estimate.  The absorption
coefficient uses `Calpha`, while the cross coefficient uses the independent
local budget `Ccross`. -/
def CoarseCaccioppoliBoundaryNoteRawEstimateSplit {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t Calpha Ccross uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryRawEstimate F
    (coarseCaccioppoliBoundaryAlphaOfHeight Q a s t Calpha h)
    (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq h)

/-- The current note-shaped boundary coefficient-control surface: the remaining
task is to verify the note's explicit height choice implies this property. -/
def CoarseCaccioppoliBoundaryNoteCoefficientControl {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (h : ℝ → ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryCoefficientControl Q a s t C uL2Sq
    (coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h)
    (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h)

/-- The note-specific absorption obligation: the chosen auxiliary height makes
the coefficient in front of `F ρ₂` absorbable by the Young step. -/
def CoarseCaccioppoliBoundaryNoteAbsorptionCondition {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C : ℝ) (h : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    coarseCaccioppoliBoundaryAlphaOfHeight Q a s t C h ρ₁ ρ₂ ≤ (1 / 4 : ℝ)

/-- The note-specific cross-term bookkeeping obligation: after choosing the
auxiliary height, the square of the remaining cross coefficient is controlled
by the final recursion right-hand side. -/
def CoarseCaccioppoliBoundaryNoteCrossTermBound {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (h : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq h ρ₁ ρ₂) ^ (2 : ℕ) ≤
      coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq *
        Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t)

/-- Note-facing explicit height bookkeeping for the boundary proof: for each
gap `ρ₂ - ρ₁`, choose the triadic scale `k` from the note together with an
auxiliary height `h` that is at least `k + 4` and already makes the absorbable
coefficient small. This isolates the first half of the note's `h = max {…}`
construction without yet forcing the later `3^{s h}` estimate. -/
def CoarseCaccioppoliBoundaryHeightChoice {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C : ℝ) (h : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
    ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ ∧
      (k : ℝ) + 4 ≤ h ρ₁ ρ₂ ∧
      C / (s * (1 - s)) * (3 : ℝ) ^ k *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h ρ₁ ρ₂) *
          Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) ≤ (1 / 4 : ℝ)

/-- The logarithmic argument in the note's explicit `h = max {k+4, ceil(...)}` choice. -/
def coarseCaccioppoliBoundaryHeightLogArg {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C : ℝ) (k : ℕ) : ℝ :=
  4 *
    (C / (s * (1 - s)) * (3 : ℝ) ^ k *
      Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))

/-- The explicit height chosen in the note at a fixed triadic scale `k`. This
packages the `max {k + 4, ceil(...)}` formula using a natural ceiling. -/
noncomputable def coarseCaccioppoliBoundaryExplicitHeightAtScale {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) : ℝ :=
  max ((k : ℝ) + 4)
    ((Nat.ceil
      (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k) /
        (coarseCaccioppoliSigma s t * Real.log (3 : ℝ))) : ℕ) : ℝ)

/-- The note's explicit `h`-choice obtained after selecting a triadic scale
`k = k(ρ₁, ρ₂)` for each radius gap. -/
noncomputable def coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (k : ℝ → ℝ → ℕ) : ℝ → ℝ → ℝ :=
  fun ρ₁ ρ₂ => coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C (k ρ₁ ρ₂)

/-- A localized variant of the explicit height which keeps the note's height
choice but also enforces the scale-localization lower bound `h >= 4 / s`.
For `t > 0`, this also implies `h >= 4 / (s + t)`. -/
noncomputable def coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) : ℝ :=
  max (coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k) (4 / s)

/-- Radius-indexed localized explicit height obtained from a scale choice. -/
noncomputable def coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (k : ℝ → ℝ → ℕ) : ℝ → ℝ → ℝ :=
  fun ρ₁ ρ₂ =>
    coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C (k ρ₁ ρ₂)

/-- The interior note-shaped raw estimate currently reuses the same coefficient
structure as the boundary version. -/
def CoarseCaccioppoliInteriorNoteRawEstimate {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (h : ℝ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryNoteRawEstimate Q a s t C uL2Sq h F

/-- Split version of the interior note-shaped raw estimate. -/
def CoarseCaccioppoliInteriorNoteRawEstimateSplit {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t Calpha Ccross uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ) (F : ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryNoteRawEstimateSplit Q a s t Calpha Ccross uL2Sq h F

/-- The interior note-shaped coefficient-control surface currently reuses the
boundary one. -/
def CoarseCaccioppoliInteriorNoteCoefficientControl {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (h : ℝ → ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryNoteCoefficientControl Q a s t C uL2Sq h

/-- The interior note-specific absorption condition currently matches the
boundary one. -/
def CoarseCaccioppoliInteriorNoteAbsorptionCondition {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C : ℝ) (h : ℝ → ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryNoteAbsorptionCondition Q a s t C h

/-- The interior note-specific cross-term bookkeeping condition currently
matches the boundary one. -/
def CoarseCaccioppoliInteriorNoteCrossTermBound {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C uL2Sq : ℝ) (h : ℝ → ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryNoteCrossTermBound Q a s t C uL2Sq h

/-- The interior note-facing explicit height choice currently reuses the
boundary bookkeeping surface; the later distinction is only in how the local
estimate is centered. -/
def CoarseCaccioppoliInteriorHeightChoice {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (s t C : ℝ) (h : ℝ → ℝ → ℝ) : Prop :=
  CoarseCaccioppoliBoundaryHeightChoice Q a s t C h


end

end Homogenization
