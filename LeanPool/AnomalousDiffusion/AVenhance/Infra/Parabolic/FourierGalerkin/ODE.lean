/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Basis
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Energy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Existence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Gronwall
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite real Galerkin systems for the weak form

The coordinates below are real coefficients of a finite orthonormal family of periodic modes.
The coefficient matrix records the weak form exactly: the drift entry is the integral of
`(b · D eⱼ) eᵢ`. In particular, no integration by parts is used to move the drift onto the test
mode, and no divergence-free hypothesis occurs.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance galerkinMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance galerkinMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance galerkinProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Real coefficient vectors with their Euclidean inner product and norm. -/
abbrev Coefficients (n : ℕ) := PiLp 2 (fun _ : Fin n => ℝ)

variable {n : ℕ}

/-- The ordinary dot product on `Vec 2`, written without importing PDE definitions. -/
def vecDot (u v : Fin 2 → ℝ) : ℝ := ∑ k, u k * v k

/-- The weak-form matrix entry for trial mode `j` and test mode `i`.

The drift is kept in the source form `b · D eⱼ`; this definition does not rewrite it by spatial
integration by parts. -/
def weakFormMatrixEntry (b : ℝ → Torus → Fin 2 → ℝ) (κ : ℝ)
    (mode : Fin n → Torus → ℝ) (modeGrad : Fin n → Torus → Fin 2 → ℝ)
    (t : ℝ) (i j : Fin n) : ℝ :=
  -(∫ x, vecDot (b t x) (modeGrad j x) * mode i x) -
    κ * ∫ x, vecDot (modeGrad j x) (modeGrad i x)

/-- The coefficients of an L² projection onto a finite real orthonormal mode family. -/
def modeProjectionCoefficients (n : ℕ) (mode : Fin n → Torus → ℝ)
    (f : Torus → ℝ) : Coefficients n :=
  WithLp.toLp 2 (fun i => ∫ x, f x * mode i x)

/-- The function represented by a finite real coefficient vector. -/
def modeExpansion (n : ℕ) (mode : Fin n → Torus → ℝ)
    (c : Coefficients n) (x : Torus) : ℝ :=
  ∑ i, c i * mode i x

/-- Finite-dimensional weak-form ODE data on a finite real mode family.

`coefficient` is understood as the bounded measurable extension of the Galerkin matrix from the
closed time interval to the line, as required by `LinearODEData`. `matrix_spec` fixes its values on
the physical time interval to the weak-form entries. `mode_orthonormal` makes the coefficient
derivative equal to the tested weak equation without a mass matrix. -/
structure WeakFormGalerkinData (n : ℕ) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- Real orthonormal modes spanning the finite Galerkin approximation. -/
  mode : Fin n → Torus → ℝ
  /-- Spatial gradients of the real Galerkin modes. -/
  modeGrad : Fin n → Torus → Fin 2 → ℝ
  mode_orthonormal : ∀ i j,
    ∫ x, mode i x * mode j x = if i = j then 1 else 0
  /-- Frequency cutoff fixing the finite-dimensional mode expansion. -/
  frequencyCutoff : ℕ
  modeExpansion_fixed_by_projection : ∀ c x,
    realFourierProjection frequencyCutoff (modeExpansion n mode c) x =
      modeExpansion n mode c x
  /-- Initial scalar function on the torus. -/
  initialData : Torus → ℝ
  /-- Time-dependent drift vector on the torus. -/
  drift : ℝ → Torus → Fin 2 → ℝ
  /-- Positive diffusion coefficient of the weak Galerkin equation. -/
  diffusivity : ℝ
  diffusivity_pos : 0 < diffusivity
  /-- Initial coefficients of the finite Galerkin approximation. -/
  initial : Coefficients n
  /-- Time-dependent continuous linear generator on the coefficient space. -/
  coefficient : ℝ → Coefficients n →L[ℝ] Coefficients n
  /-- Uniform operator-norm bound for the coefficient generator. -/
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficient_aestronglyMeasurable : AEStronglyMeasurable coefficient volume
  coefficient_norm_le : ∀ t, ‖coefficient t‖ ≤ coefficientBound
  matrix_spec : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 1)), ∀ c i,
    coefficient t c i =
      ∑ j, weakFormMatrixEntry drift diffusivity mode modeGrad t i j * c j
  initial_is_projection : initial = modeProjectionCoefficients n mode initialData
  projection_eq_modeExpansion : ∀ x,
    modeExpansion n mode initial x =
      realFourierProjection frequencyCutoff initialData x
  /-- Continuous linear gradient of a finite mode expansion. -/
  gradient : Coefficients n →L[ℝ] F
  /-- Constant bounding the quadratic drift contribution to energy. -/
  driftBound : ℝ
  /-- Quadratic drift form occurring in the weak energy identity. -/
  driftForm : ℝ → Coefficients n → ℝ
  weakForm_energy : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 1)), ∀ c,
    2 * inner ℝ c (coefficient t c) =
      -2 * driftForm t c - 2 * diffusivity * ‖gradient c‖ ^ 2
  drift_bound : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 1)), ∀ c,
    |driftForm t c| ≤ driftBound * ‖gradient c‖ * ‖c‖

namespace WeakFormGalerkinData

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The corresponding homogeneous measurable linear ODE on `[0,1]`. -/
def ode (D : WeakFormGalerkinData n F) :
    AVenhance.Infra.ODE.LinearODEData (E := Coefficients n) 0 1 (by norm_num) where
  A := D.coefficient
  f := 0
  y₀ := D.initial
  operatorBound := D.coefficientBound
  operatorBound_nonneg := D.coefficientBound_nonneg
  operator_aestronglyMeasurable := D.coefficient_aestronglyMeasurable
  operator_norm_le := D.coefficient_norm_le
  forcing_intervalIntegrable := IntervalIntegrable.zero

/-- Existence and uniqueness of the finite Galerkin coefficient path.

The path is absolutely continuous and solves the projected weak-form ODE through the
integral-solution characterization supplied by `Infra.ODE.Linear`. -/
theorem existsUnique_solution (D : WeakFormGalerkinData n F) :
    ∃! u : C(Set.Icc (0 : ℝ) 1, Coefficients n),
      AVenhance.Infra.ODE.IsLinearIntegralSolution D.coefficient 0 D.initial 0 1
          (AVenhance.Infra.ODE.extendCurve (by norm_num) u) ∧
        AbsolutelyContinuousOnInterval
          (AVenhance.Infra.ODE.extendCurve (by norm_num) u) 0 1 := by
  exact D.ode.existsUnique_absolutelyContinuous_integralSolution

end WeakFormGalerkinData

end AVenhance.Infra.Parabolic.FourierGalerkin

end
