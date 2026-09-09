/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact radial stress identities

This file verifies the algebra and radial calculus in equations (6)--(9) of the
candidate manuscript. Parameter derivatives are supplied as independent radial
functions, with their requisite radial derivative identities stated explicitly.
No existence of the candidate profiles or estimates for them is asserted.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.StressAlgebra

open MeasureTheory Set

/-- The axial scaling exponent from the manuscript. -/
def axialExponent (h : ℝ) : ℝ := 1 / 2 - h

/-- The velocity scaling exponent from the manuscript. -/
def velocityExponent (h : ℝ) : ℝ := 1 / 2 + h

/-- The coordinate factor `d = 1 - η²`. -/
def coordinateFactor (η : ℝ) : ℝ := 1 - η ^ 2

/-- `H S_q`, with radial derivatives written explicitly instead of logarithms. -/
def angularSource (h η x W U H Hx Hη : ℝ) : ℝ :=
  -W * x * Hx - h * (1 - 2 * η * U) * H -
    (axialExponent h * η + coordinateFactor η * U) * Hη

/-- `S_n`, with `dot U = x U_x` and `dot P = x P_x`. -/
def axialSource (h η x W U Ux Uη P Px Pη : ℝ) : ℝ :=
  -W * x * Ux - velocityExponent h * (1 - 2 * η * U) * U -
    (axialExponent h * η + coordinateFactor η * U) * Uη -
    coordinateFactor η * Pη + 4 * velocityExponent h * η * P + 2 * η * x * Px

/-- The numerator of the angular integrated identity (9). -/
def angularPrimitive (h η : ℝ) (W H I Iη J Jη : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(x * W x * H x) + (1 - h) * I x - axialExponent h * η * Iη x -
    coordinateFactor η * Jη x + 2 * (h - axialExponent h) * η * J x

/-- The numerator of the axial integrated identity (9). -/
def axialPrimitive (h η : ℝ) (W U M Mη S Sη P Pη : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(x * W x * U x) + axialExponent h * (M x - η * Mη x) +
    4 * h * η * S x - coordinateFactor η * Sη x +
    x * (4 * velocityExponent h * η * P x - coordinateFactor η * Pη x)

/-- The angular integration-by-parts cancellation, as an exact polynomial identity. -/
theorem angular_derivative_algebra
    (h η x W Wx U Uη H Hx Hη : ℝ)
    (hW : W + x * Wx = 1 - 2 * axialExponent h * η * U - coordinateFactor η * Uη) :
    -((W + x * Wx) * H + x * W * Hx) + (1 - h) * H -
      axialExponent h * η * Hη - coordinateFactor η * (Uη * H + U * Hη) +
      2 * (h - axialExponent h) * η * (U * H) =
      angularSource h η x W U H Hx Hη := by
  unfold angularSource
  linear_combination -H * hW

/-- The axial integration-by-parts cancellation, including both pressure identities. -/
theorem axial_derivative_algebra
    (h η x W Wx U Ux Uη E Eη P Px Pη Pηx : ℝ)
    (hW : W + x * Wx = 1 - 2 * axialExponent h * η * U - coordinateFactor η * Uη)
    (hP : x * Px = E ^ 2 / 2)
    (hPη : x * Pηx = E * Eη) :
    -((W + x * Wx) * U + x * W * Ux) + axialExponent h * (U - η * Uη) +
      4 * h * η * (U ^ 2 - E ^ 2 / 2) -
      coordinateFactor η * (2 * U * Uη - E * Eη) +
      (4 * velocityExponent h * η * P - coordinateFactor η * Pη) +
      x * (4 * velocityExponent h * η * Px - coordinateFactor η * Pηx) =
      axialSource h η x W U Ux Uη P Px Pη := by
  unfold axialSource axialExponent velocityExponent coordinateFactor at *
  linear_combination -U * hW + (4 * h * η) * hP - (1 - η ^ 2) * hPη

/-- Genuine radial differentiation of the angular primitive. The moment hypotheses
are precisely `I_x = H`, `(I_η)_x = H_η`, `J_x = UH`, and
`(J_η)_x = U_ηH + UH_η`. -/
theorem angularPrimitive_hasDerivAt
    (h η x : ℝ) (W H I Iη J Jη : ℝ → ℝ) (Wx Hx U Uη Hη : ℝ)
    (hWderiv : HasDerivAt W Wx x) (hH : HasDerivAt H Hx x)
    (hI : HasDerivAt I (H x) x) (hIη : HasDerivAt Iη Hη x)
    (hJ : HasDerivAt J (U * H x) x)
    (hJη : HasDerivAt Jη (Uη * H x + U * Hη) x)
    (hW : W x + x * Wx =
      1 - 2 * axialExponent h * η * U - coordinateFactor η * Uη) :
    HasDerivAt (angularPrimitive h η W H I Iη J Jη)
      (angularSource h η x (W x) U (H x) Hx Hη) x := by
  have hd := (((((hasDerivAt_id x).mul hWderiv).mul hH).neg.add
    (hI.const_mul (1 - h))).sub (hIη.const_mul (axialExponent h * η))).sub
      (hJη.const_mul (coordinateFactor η))
  have hd' := hd.add (hJ.const_mul (2 * (h - axialExponent h) * η))
  apply hd'.congr_deriv
  simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, one_mul] using
    angular_derivative_algebra h η x (W x) Wx U Uη (H x) Hx Hη hW

/-- Genuine radial differentiation of the axial primitive. In addition to the
moment identities this uses `x P_x = E²/2` and its η derivative. -/
theorem axialPrimitive_hasDerivAt
    (h η x : ℝ) (W U M Mη S Sη P Pη : ℝ → ℝ)
    (Wx Ux Uη E Eη Px Pηx : ℝ)
    (hWderiv : HasDerivAt W Wx x) (hU : HasDerivAt U Ux x)
    (hM : HasDerivAt M (U x) x) (hMη : HasDerivAt Mη Uη x)
    (hS : HasDerivAt S ((U x) ^ 2 - E ^ 2 / 2) x)
    (hSη : HasDerivAt Sη (2 * U x * Uη - E * Eη) x)
    (hPderiv : HasDerivAt P Px x) (hPηderiv : HasDerivAt Pη Pηx x)
    (hW : W x + x * Wx =
      1 - 2 * axialExponent h * η * U x - coordinateFactor η * Uη)
    (hP : x * Px = E ^ 2 / 2) (hPη : x * Pηx = E * Eη) :
    HasDerivAt (axialPrimitive h η W U M Mη S Sη P Pη)
      (axialSource h η x (W x) (U x) Ux Uη (P x) Px (Pη x)) x := by
  have hd := (((((hasDerivAt_id x).mul hWderiv).mul hU).neg.add
    ((hM.sub (hMη.const_mul η)).const_mul (axialExponent h))).add
      (hS.const_mul (4 * h * η))).sub (hSη.const_mul (coordinateFactor η))
  have hd' := hd.add ((hasDerivAt_id x).mul
    ((hPderiv.const_mul (4 * velocityExponent h * η)).sub
      (hPηderiv.const_mul (coordinateFactor η))))
  apply hd'.congr_deriv
  simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, one_mul, add_assoc] using
    axial_derivative_algebra h η x (W x) Wx (U x) Ux Uη E Eη
      (P x) Px (Pη x) Pηx hW hP hPη

/-- Data for the angular integrated identity on a specified closed radial interval.
The fields are differential and initial conditions, not an assumed integral identity. -/
structure AngularMomentData (h η X : ℝ) where
  /-- W of `AngularMomentData`, of type `ℝ → ℝ`. -/
  W : ℝ → ℝ
  /-- Wx of `AngularMomentData`, of type `ℝ → ℝ`. -/
  Wx : ℝ → ℝ
  /-- H of `AngularMomentData`, of type `ℝ → ℝ`. -/
  H : ℝ → ℝ
  /-- Hx of `AngularMomentData`, of type `ℝ → ℝ`. -/
  Hx : ℝ → ℝ
  /-- Hη of `AngularMomentData`, of type `ℝ → ℝ`. -/
  Hη : ℝ → ℝ
  /-- U of `AngularMomentData`, of type `ℝ → ℝ`. -/
  U : ℝ → ℝ
  /-- Uη of `AngularMomentData`, of type `ℝ → ℝ`. -/
  Uη : ℝ → ℝ
  /-- I of `AngularMomentData`, of type `ℝ → ℝ`. -/
  I : ℝ → ℝ
  /-- Iη of `AngularMomentData`, of type `ℝ → ℝ`. -/
  Iη : ℝ → ℝ
  /-- J of `AngularMomentData`, of type `ℝ → ℝ`. -/
  J : ℝ → ℝ
  /-- Jη of `AngularMomentData`, of type `ℝ → ℝ`. -/
  Jη : ℝ → ℝ
  W_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt W (Wx x) x
  H_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt H (Hx x) x
  I_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt I (H x) x
  Iη_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt Iη (Hη x) x
  J_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt J (U x * H x) x
  Jη_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt Jη (Uη x * H x + U x * Hη x) x
  W_balance : ∀ x ∈ uIcc 0 X,
    W x + x * Wx x = 1 - 2 * axialExponent h * η * U x - coordinateFactor η * Uη x
  I_zero : I 0 = 0
  Iη_zero : Iη 0 = 0
  J_zero : J 0 = 0
  Jη_zero : Jη 0 = 0

/-- The first integral formula in the proof of Lemma 3.3, derived by the
fundamental theorem of calculus from explicit differential moment conditions. -/
theorem angular_integrated_identity
    {h η X : ℝ} (p : AngularMomentData h η X)
    (hint : IntervalIntegrable
      (fun x => angularSource h η x (p.W x) (p.U x) (p.H x) (p.Hx x) (p.Hη x))
      volume 0 X) :
    intervalIntegral
      (fun x => angularSource h η x (p.W x) (p.U x) (p.H x) (p.Hx x) (p.Hη x))
      0 X volume =
      angularPrimitive h η p.W p.H p.I p.Iη p.J p.Jη X := by
  have hd : ∀ x ∈ uIcc 0 X,
      HasDerivAt (angularPrimitive h η p.W p.H p.I p.Iη p.J p.Jη)
        (angularSource h η x (p.W x) (p.U x) (p.H x) (p.Hx x) (p.Hη x)) x := by
    intro x hx
    exact angularPrimitive_hasDerivAt h η x p.W p.H p.I p.Iη p.J p.Jη
      (p.Wx x) (p.Hx x) (p.U x) (p.Uη x) (p.Hη x)
      (p.W_deriv x hx) (p.H_deriv x hx) (p.I_deriv x hx) (p.Iη_deriv x hx)
      (p.J_deriv x hx) (p.Jη_deriv x hx) (p.W_balance x hx)
  have hzero : angularPrimitive h η p.W p.H p.I p.Iη p.J p.Jη 0 = 0 := by
    simp [angularPrimitive, p.I_zero, p.Iη_zero, p.J_zero, p.Jη_zero]
  simpa only [hzero, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint

/-- Differential and initial data required for the axial integrated identity. -/
structure AxialMomentData (h η X : ℝ) where
  /-- W of `AxialMomentData`, of type `ℝ → ℝ`. -/
  W : ℝ → ℝ
  /-- Wx of `AxialMomentData`, of type `ℝ → ℝ`. -/
  Wx : ℝ → ℝ
  /-- U of `AxialMomentData`, of type `ℝ → ℝ`. -/
  U : ℝ → ℝ
  /-- Ux of `AxialMomentData`, of type `ℝ → ℝ`. -/
  Ux : ℝ → ℝ
  /-- Uη of `AxialMomentData`, of type `ℝ → ℝ`. -/
  Uη : ℝ → ℝ
  /-- E of `AxialMomentData`, of type `ℝ → ℝ`. -/
  E : ℝ → ℝ
  /-- Eη of `AxialMomentData`, of type `ℝ → ℝ`. -/
  Eη : ℝ → ℝ
  /-- P of `AxialMomentData`, of type `ℝ → ℝ`. -/
  P : ℝ → ℝ
  /-- Px of `AxialMomentData`, of type `ℝ → ℝ`. -/
  Px : ℝ → ℝ
  /-- Pη of `AxialMomentData`, of type `ℝ → ℝ`. -/
  Pη : ℝ → ℝ
  /-- Pηx of `AxialMomentData`, of type `ℝ → ℝ`. -/
  Pηx : ℝ → ℝ
  /-- M of `AxialMomentData`, of type `ℝ → ℝ`. -/
  M : ℝ → ℝ
  /-- Mη of `AxialMomentData`, of type `ℝ → ℝ`. -/
  Mη : ℝ → ℝ
  /-- Parameter `S` of `AxialMomentData`, of type `ℝ → ℝ`. -/
  S : ℝ → ℝ
  /-- Sη of `AxialMomentData`, of type `ℝ → ℝ`. -/
  Sη : ℝ → ℝ
  W_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt W (Wx x) x
  U_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt U (Ux x) x
  M_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt M (U x) x
  Mη_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt Mη (Uη x) x
  S_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt S (U x ^ 2 - E x ^ 2 / 2) x
  Sη_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt Sη (2 * U x * Uη x - E x * Eη x) x
  P_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt P (Px x) x
  Pη_deriv : ∀ x ∈ uIcc 0 X, HasDerivAt Pη (Pηx x) x
  W_balance : ∀ x ∈ uIcc 0 X,
    W x + x * Wx x = 1 - 2 * axialExponent h * η * U x - coordinateFactor η * Uη x
  pressure_balance : ∀ x ∈ uIcc 0 X, x * Px x = E x ^ 2 / 2
  pressure_η_balance : ∀ x ∈ uIcc 0 X, x * Pηx x = E x * Eη x
  M_zero : M 0 = 0
  Mη_zero : Mη 0 = 0
  S_zero : S 0 = 0
  Sη_zero : Sη 0 = 0

/-- The second integral formula in Lemma 3.3, including its pressure terms. -/
theorem axial_integrated_identity
    {h η X : ℝ} (p : AxialMomentData h η X)
    (hint : IntervalIntegrable
      (fun x => axialSource h η x (p.W x) (p.U x) (p.Ux x) (p.Uη x)
        (p.P x) (p.Px x) (p.Pη x)) volume 0 X) :
    intervalIntegral
      (fun x => axialSource h η x (p.W x) (p.U x) (p.Ux x) (p.Uη x)
        (p.P x) (p.Px x) (p.Pη x)) 0 X volume =
      axialPrimitive h η p.W p.U p.M p.Mη p.S p.Sη p.P p.Pη X := by
  have hd : ∀ x ∈ uIcc 0 X,
      HasDerivAt (axialPrimitive h η p.W p.U p.M p.Mη p.S p.Sη p.P p.Pη)
        (axialSource h η x (p.W x) (p.U x) (p.Ux x) (p.Uη x)
          (p.P x) (p.Px x) (p.Pη x)) x := by
    intro x hx
    exact axialPrimitive_hasDerivAt h η x p.W p.U p.M p.Mη p.S p.Sη p.P p.Pη
      (p.Wx x) (p.Ux x) (p.Uη x) (p.E x) (p.Eη x) (p.Px x) (p.Pηx x)
      (p.W_deriv x hx) (p.U_deriv x hx) (p.M_deriv x hx) (p.Mη_deriv x hx)
      (p.S_deriv x hx) (p.Sη_deriv x hx) (p.P_deriv x hx) (p.Pη_deriv x hx)
      (p.W_balance x hx) (p.pressure_balance x hx) (p.pressure_η_balance x hx)
  have hzero : axialPrimitive h η p.W p.U p.M p.Mη p.S p.Sη p.P p.Pη 0 = 0 := by
    simp [axialPrimitive, p.M_zero, p.Mη_zero, p.S_zero, p.Sη_zero]
  simpa only [hzero, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint

/-- The angular formula (9) after division by the regular integrating factor.
The left side is the regular primitive definition of `Q_s`. -/
theorem angular_integrated_lag
    {h η X : ℝ} (p : AngularMomentData h η X) (hX : X ≠ 0) (hH : p.H X ≠ 0)
    (hint : IntervalIntegrable
      (fun x => angularSource h η x (p.W x) (p.U x) (p.H x) (p.Hx x) (p.Hη x))
      volume 0 X) :
    intervalIntegral
      (fun x => angularSource h η x (p.W x) (p.U x) (p.H x) (p.Hx x) (p.Hη x))
      0 X volume / (X * p.H X) =
      -p.W X + ((1 - h) * p.I X - axialExponent h * η * p.Iη X -
        coordinateFactor η * p.Jη X + 2 * (h - axialExponent h) * η * p.J X) /
          (X * p.H X) := by
  rw [angular_integrated_identity p hint]
  unfold angularPrimitive
  field_simp; ring

/-- The axial formula (9) after division by its regular integrating factor.
The left side is the regular primitive definition of `N_s`. -/
theorem axial_integrated_lag
    {h η X : ℝ} (p : AxialMomentData h η X) (hX : X ≠ 0)
    (hint : IntervalIntegrable
      (fun x => axialSource h η x (p.W x) (p.U x) (p.Ux x) (p.Uη x)
        (p.P x) (p.Px x) (p.Pη x)) volume 0 X) :
    intervalIntegral
      (fun x => axialSource h η x (p.W x) (p.U x) (p.Ux x) (p.Uη x)
        (p.P x) (p.Px x) (p.Pη x)) 0 X volume / X =
      -p.W X * p.U X + axialExponent h * (p.M X - η * p.Mη X) / X +
        (4 * h * η * p.S X - coordinateFactor η * p.Sη X) / X +
        4 * velocityExponent h * η * p.P X - coordinateFactor η * p.Pη X := by
  rw [axial_integrated_identity p hint]
  unfold axialPrimitive
  field_simp; ring

/-- The source written with logarithmic derivatives agrees with `H S_q`.
Its use for actual logarithms requires the usual nonvanishing profile conditions. -/
theorem angular_source_logarithmic_form
    (h η x W U H Hx Hη : ℝ) (hH : H ≠ 0) :
    H * (-W * (x * Hx / H) - h * (1 - 2 * η * U) -
      (axialExponent h * η + coordinateFactor η * U) * (Hη / H)) =
      angularSource h η x W U H Hx Hη := by
  unfold angularSource
  field_simp

/-- Multiplying (6)'s angular lag equation by its integrating factor gives the
primitive equation. This equivalence uses genuine derivatives of `H` and `Q`. -/
theorem angular_lag_primitive_iff
    (H Q : ℝ → ℝ) (x Hx Qx Sq : ℝ)
    (hH : HasDerivAt H Hx x) (hQ : HasDerivAt Q Qx x) (hHne : H x ≠ 0) :
    HasDerivAt (fun y => y * H y * Q y) (H x * Sq) x ↔
      x * Qx + (1 + x * Hx / H x) * Q x = Sq := by
  have hd := ((hasDerivAt_id x).mul hH).mul hQ
  have hcalc : (1 * H x + x * Hx) * Q x + x * H x * Qx =
      H x * (x * Qx + (1 + x * Hx / H x) * Q x) := by
    field_simp; ring
  constructor
  · intro hp
    have heq := hd.unique hp
    simp only [Pi.mul_apply, id_eq] at heq
    rw [hcalc] at heq
    exact (mul_left_cancel₀ hHne) heq
  · intro hlag
    apply hd.congr_deriv
    simp only [Pi.mul_apply, id_eq]
    rw [hcalc, hlag]

/-- The axial lag equation's integrating factor is `x`. -/
theorem axial_lag_primitive_iff
    (N : ℝ → ℝ) (x Nx Sn : ℝ) (hN : HasDerivAt N Nx x) :
    HasDerivAt (fun y => y * N y) Sn x ↔ x * Nx + N x = Sn := by
  have hd := (hasDerivAt_id x).mul hN
  constructor
  · intro hp
    simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, one_mul, add_comm] using hd.unique hp
  · intro hlag
    apply hd.congr_deriv
    simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, one_mul, add_comm] using hlag

/-- The angular stress-free substitution from (7) yields exactly the radial
second-order expression in (8). Here `φx` and `φxx` denote radial derivatives. -/
theorem stressFree_angular_lag_algebra
    (x L φ φx φxx : ℝ) (hφ : φ ≠ 0) :
    x * (-2 * L * (φxx * φ - φx ^ 2) / φ ^ 2) +
      (2 + x * φx / φ) * (-2 * L * φx / φ) =
      -2 * L * (x * φxx + 2 * φx) / φ := by
  field_simp; ring

/-- The axial stress-free substitution from (7) yields its expression in (8). -/
theorem stressFree_axial_lag_algebra (x L Ux Uxx : ℝ) :
    x * (-2 * L * Uxx) + (-2 * L * Ux) = -2 * L * (x * Uxx + Ux) := by
  ring

/-- The axial coefficient of `F (p_s - s)` in (7), with the positive viscous
primitive `2 x U_x / R` made explicit. Here `R` is the radial factor `sqrt(2x)`. -/
theorem axial_stress_coefficient
    (x R E L Ns Ux : ℝ) (hR : R ≠ 0) (hE : E ≠ 0) (hL : L ≠ 0) :
    (E / R) * (x * Ns / (L * E) + 2 * x * Ux / E) =
      (x / R) * (Ns / L + 2 * Ux) := by
  field_simp

/-- The angular coefficient of (7), with its radial viscous primitive exposed.
This verifies the sign of the subtraction of `a = 1 - 2 dot(E)/E`. -/
theorem angular_stress_coefficient
    (x R E L Qs Ex : ℝ) (hR : R ≠ 0) (hE : E ≠ 0) (hL : L ≠ 0) :
    (E / R) * (x * Qs / L - (1 - 2 * x * Ex / E)) =
      (E / R) * (x * Qs / L) + (2 * x * Ex - E) / R := by
  field_simp; ring

end NavierStokes.StressAlgebra
