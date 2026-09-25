/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ResolventOperator
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Continuation Contour -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Proof-carrying contours for spectral continuation

This module supplies the geometric and spectral data used by the complex
Riesz-projection continuation argument.  A contour is represented by a closed
Mathlib `Path` together with a finite partition of the unit interval on whose
closed subintervals the extended path is continuously differentiable.

The spectral contract is quantitative.  It records a positive common distance
from the contour to the real spectrum, resolvent-set membership at every
contour point, and the normalized winding laws that select exactly the desired
Borel component with positive orientation.

The normalized winding value is written directly as Mathlib's Bochner interval
integral of the scalar resolvent one-form.  The later operator-valued contour
module can use the same parameterization and derivative without introducing a
second contour representation.

**Promoted 2026-07-30 under lane `EXP-PROMOTE-MISC`**, from
`DavisKahan/Experimental/InfiniteDimensional/SinTheta/`.  Its import closure was already
Experimental-free — it needs only `DavisKahan.SpectralTheory.ResolventOperator` and Mathlib —
so it was compiled by nothing but its own aggregate until now.  Nothing is restated.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set
open scoped InnerProductSpace Interval unitInterval

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A closed complex contour with a finite partition into `C1` pieces.

The path itself provides continuity and closedness.  The partition asks for a
continuously differentiable extension on every closed piece, so one-sided
endpoint derivatives are available for later Bochner-integrability arguments.
-/
structure PiecewiseC1ClosedContour where
  /-- The common source and target of the closed path. -/
  basePoint : ℂ
  /-- The closed path parameterized by Mathlib's unit interval. -/
  path : Path basePoint basePoint
  /-- Number of differentiable pieces. -/
  pieceCount : ℕ
  /-- A closed contour has at least one differentiable piece. -/
  pieceCount_pos : 0 < pieceCount
  /-- Ordered partition points, including zero and one. -/
  breakPoint : Fin (pieceCount + 1) → ℝ
  /-- The first partition point is zero. -/
  breakPoint_zero : breakPoint 0 = 0
  /-- The last partition point is one. -/
  breakPoint_last : breakPoint (Fin.last pieceCount) = 1
  /-- Partition points occur in their path order. -/
  breakPoint_strictMono : StrictMono breakPoint
  /-- The extended path is `C1` on every closed partition interval. -/
  contDiffOn_piece : ∀ i : Fin pieceCount,
    ContDiffOn ℝ 1 path.extend
      (Set.Icc (breakPoint i.castSucc) (breakPoint i.succ))

namespace PiecewiseC1ClosedContour

/-- The underlying globally defined parameterization, constant outside the
unit interval. -/
noncomputable def param (Γ : PiecewiseC1ClosedContour) : ℝ → ℂ :=
  Γ.path.extend

/-- The geometric image of the contour. -/
def image (Γ : PiecewiseC1ClosedContour) : Set ℂ :=
  Set.range Γ.path

/-- The contour starts at its recorded base point. -/
theorem path_zero (Γ : PiecewiseC1ClosedContour) :
    Γ.path 0 = Γ.basePoint :=
  Γ.path.source

/-- The contour ends at its recorded base point. -/
theorem path_one (Γ : PiecewiseC1ClosedContour) :
    Γ.path 1 = Γ.basePoint :=
  Γ.path.target

/-- The extended parameterization agrees with the base point at zero. -/
@[simp] theorem param_zero (Γ : PiecewiseC1ClosedContour) :
    Γ.param 0 = Γ.basePoint :=
  Γ.path.extend_zero

/-- The extended parameterization agrees with the base point at one. -/
@[simp] theorem param_one (Γ : PiecewiseC1ClosedContour) :
    Γ.param 1 = Γ.basePoint :=
  Γ.path.extend_one

/-- Normalized scalar resolvent integral around the contour.

For a regular contour avoiding `z`, this is the usual winding number
`(2 * pi * i)^{-1} integral (w - z)^{-1} dw`.  It is kept complex-valued because
that is the form needed by continuous functional calculus.
-/
noncomputable def normalizedWinding (Γ : PiecewiseC1ClosedContour)
    (z : ℂ) : ℂ :=
  (((2 : ℂ) * Real.pi * Complex.I)⁻¹) *
    ∫ t in (0 : ℝ)..1,
      (Γ.param t - z)⁻¹ * derivWithin Γ.param (Set.Icc (0 : ℝ) 1) t

end PiecewiseC1ClosedContour

/-- Complete contour data selecting a real spectral component of a bounded
complex self-adjoint operator.

The `winding_selected` field fixes positive orientation by requiring normalized
winding one on the selected spectrum.  The complementary law requires winding
zero on every spectral point outside the selected component.  Together these
laws say that the contour encloses exactly `s ∩ realSpectrum A`.
-/
structure SpectralSeparatingContour
    (A : H →L[ℂ] H) (s : Set ℝ) where
  /-- Piecewise-`C1` closed geometric contour. -/
  geometric : PiecewiseC1ClosedContour
  /-- Self-adjointness of the operator whose spectrum is separated. -/
  selfAdjoint : A.IsSymmetric
  /-- Measurability required by the Borel spectral projection. -/
  measurable_selected : MeasurableSet s
  /-- Quantitative contour-to-spectrum margin. -/
  spectralMargin : ℝ
  /-- The spectral margin is strictly positive. -/
  spectralMargin_pos : 0 < spectralMargin
  /-- Every contour point stays at least the recorded margin from the spectrum. -/
  spectrum_separated : ∀ t : unitInterval, ∀ lam ∈ realSpectrum A,
    spectralMargin ≤ ‖geometric.path t - (lam : ℂ)‖
  /-- Positive orientation and inclusion of the selected spectral component. -/
  winding_selected : ∀ lam ∈ realSpectrum A, lam ∈ s →
    geometric.normalizedWinding (lam : ℂ) = 1
  /-- Exclusion of the complementary spectral component. -/
  winding_complement : ∀ lam ∈ realSpectrum A, lam ∉ s →
    geometric.normalizedWinding (lam : ℂ) = 0

namespace SpectralSeparatingContour

/-- The underlying closed path. -/
abbrev path {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) :
    Path Γ.geometric.basePoint Γ.geometric.basePoint :=
  Γ.geometric.path

/-- The globally extended contour parameterization. -/
noncomputable def param {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) : ℝ → ℂ :=
  Γ.geometric.param

/-- The geometric contour image. -/
def image {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s) : Set ℂ :=
  Γ.geometric.image

/-- The selected component has normalized winding one at every spectral point. -/
theorem normalizedWinding_eq_one {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s)
    {lam : ℝ} (hlam : lam ∈ realSpectrum A) (hs : lam ∈ s) :
    Γ.geometric.normalizedWinding (lam : ℂ) = 1 :=
  Γ.winding_selected lam hlam hs

/-- The complementary component has normalized winding zero at every spectral
point. -/
theorem normalizedWinding_eq_zero {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s)
    {lam : ℝ} (hlam : lam ∈ realSpectrum A) (hs : lam ∉ s) :
    Γ.geometric.normalizedWinding (lam : ℂ) = 0 :=
  Γ.winding_complement lam hlam hs

/-- Quantitative separation at a contour parameter. -/
theorem spectralMargin_le {A : H →L[ℂ] H} {s : Set ℝ}
    (Γ : SpectralSeparatingContour A s)
    (t : unitInterval) {lam : ℝ} (hlam : lam ∈ realSpectrum A) :
    Γ.spectralMargin ≤ ‖Γ.path t - (lam : ℂ)‖ :=
  Γ.spectrum_separated t lam hlam

/-- Quantitative spectral separation puts every contour point in the
resolvent set. -/
theorem inResolventSet {A : H →L[ℂ] H} {s : Set ℝ}
    [CompleteSpace H] (Γ : SpectralSeparatingContour A s) (t : unitInterval) :
    InResolventSet A (Γ.path t) :=
  complex_inResolventSet_of_distance A Γ.selfAdjoint (Γ.path t)
    Γ.spectralMargin Γ.spectralMargin_pos (Γ.spectrum_separated t)

/-- Uniform resolvent bound supplied by the recorded spectral margin. -/
theorem norm_resolventOperator_le {A : H →L[ℂ] H} {s : Set ℝ}
    [CompleteSpace H] (Γ : SpectralSeparatingContour A s) (t : unitInterval) :
    ‖resolventOperator A (Γ.path t)‖ ≤ Γ.spectralMargin⁻¹ :=
  complex_norm_resolvent_le_inv_distance A Γ.selfAdjoint (Γ.path t)
    Γ.spectralMargin Γ.spectralMargin_pos (Γ.spectrum_separated t)

end SpectralSeparatingContour

end DavisKahanExt
end TauCeti
