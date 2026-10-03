/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Energy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.PathCompactness
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Positive-cutoff Galerkin paths for drift data

This module chooses the finite-dimensional ODE solution at every positive real Fourier cutoff
and records the cutoff-independent scalar energy bound.  The next compactness module consumes
these paths together with the uniform gradient estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Filter
open Homogenization
open scoped Topology

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance sequenceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance sequenceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sequenceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open scoped RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

local instance scalarTorusMeasureSeparable : IsSeparable (volume : Measure Torus) :=
  inferInstance

local instance two_ne_top_fact : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

local instance scalarTorusL2SecondCountable : SecondCountableTopology ScalarTorusL2 :=
  inferInstance

/-- The hypotheses needed to instantiate every positive real Fourier Galerkin system. -/
structure FrozenDriftProblem where
  /-- Bounded measurable periodic drift of the frozen parabolic problem. -/
  b : ℝ → Vec 2 → Vec 2
  drift_measurable : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
    (volume.restrict (Icc (0 : ℝ) 1 ×ˢ Set.univ))
  drift_bounded : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ B
  drift_periodic : ∀ t ∈ Icc (0 : ℝ) 1, IsZ2Periodic (b t)
  /-- Positive diffusivity of the frozen parabolic problem. -/
  κ : ℝ
  κ_pos : 0 < κ
  /-- Square-integrable periodic initial datum of the frozen parabolic problem. -/
  θ₀ : Vec 2 → ℝ
  initial_memL2 : MemL2On AVenhance.unitCube θ₀

/-- The concrete finite weak-form ODE at cutoff `N`. -/
def FrozenDriftProblem.galerkinData (P : FrozenDriftProblem) (N : ℕ) :
    WeakFormGalerkinData (RealFourierDimension N) SpatialGradientL2 :=
  positiveCutoffGalerkinData N P.b P.drift_measurable P.drift_bounded P.drift_periodic
    P.κ P.κ_pos P.θ₀ P.initial_memL2

/-- A selected continuous coefficient path solving the finite Galerkin system. -/
noncomputable def FrozenDriftProblem.coefficientPath (P : FrozenDriftProblem) (N : ℕ) :
    C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N)) :=
  Classical.choose ((P.galerkinData N).existsUnique_solution).exists

/-- The selected coefficient path is the unique finite ODE solution. -/
theorem FrozenDriftProblem.coefficientPath_isSolution (P : FrozenDriftProblem) (N : ℕ) :
    (P.galerkinData N).ode.IsSolution (P.coefficientPath N) := by
  apply ((P.galerkinData N).ode.isSolution_iff_integralSolution _).2
  exact (Classical.choose_spec ((P.galerkinData N).existsUnique_solution).exists).1

/-- The continuous scalar `L²` path represented by the finite real Fourier expansion. -/
noncomputable def FrozenDriftProblem.scalarPath (P : FrozenDriftProblem) (N : ℕ) :
    C(Icc (0 : ℝ) 1, ScalarTorusL2) :=
  ⟨fun t => realFourierScalarMap N ((P.coefficientPath N) t),
    (realFourierScalarMap N).continuous.comp (P.coefficientPath N).continuous⟩

/-- The fixed torus `L²` representative of the initial datum. -/
noncomputable def FrozenDriftProblem.initialTorusL2 (P : FrozenDriftProblem) : ScalarTorusL2 :=
  (frozenInitialData_memLp_torus P.initial_memL2).toLp
    (AVenhance.Infra.Torus.periodicToTorus P.θ₀)

/-- A cutoff-independent upper bound for all scalar path norms. -/
def FrozenDriftProblem.scalarBound (P : FrozenDriftProblem) : ℝ :=
  ‖P.initialTorusL2‖ * Real.exp
    ((positiveCutoffDriftConstant P.b P.drift_bounded) ^ 2 / P.κ)

theorem FrozenDriftProblem.scalarBound_nonneg (P : FrozenDriftProblem) :
    0 ≤ P.scalarBound := by
  apply mul_nonneg (norm_nonneg _)
  exact le_of_lt (Real.exp_pos _)

/-- Fourier projection does not increase the `L²` norm of the datum. -/
theorem FrozenDriftProblem.initialProjection_norm_le (P : FrozenDriftProblem) (N : ℕ) :
    ‖(P.galerkinData N).initial‖ ≤ ‖P.initialTorusL2‖ := by
  simpa [FrozenDriftProblem.galerkinData, positiveCutoffGalerkinData,
    FrozenDriftProblem.initialTorusL2] using
    realFourierModeFin_projectionCoefficients_norm_le N
      (frozenInitialData_memLp_torus P.initial_memL2)

/-- Every positive-cutoff path obeys one common-in-time `L²` bound independent of its cutoff. -/
theorem FrozenDriftProblem.scalarPath_norm_le (P : FrozenDriftProblem) (N : ℕ)
    (t : Icc (0 : ℝ) 1) : ‖P.scalarPath N t‖ ≤ P.scalarBound := by
  let D := P.galerkinData N
  let u := P.coefficientPath N
  let y := AVenhance.Infra.ODE.extendCurve (by norm_num) u
  let c : ℝ := (D.driftBound ^ 2 / D.diffusivity)
  have hc : 0 ≤ c := div_nonneg (sq_nonneg D.driftBound) D.diffusivity_pos.le
  have ht : (t : ℝ) ∈ Icc (0 : ℝ) 1 := t.property
  have henergy := WeakFormGalerkinData.IsSolution.energyEstimate D u
    (P.coefficientPath_isSolution N) (t : ℝ) ht
  have hinitial : ‖D.initial‖ ≤ ‖P.initialTorusL2‖ := by
    exact P.initialProjection_norm_le N
  have htime : c * (t : ℝ) ≤ c := by
    exact mul_le_of_le_one_right hc t.property.2
  have hexp : Real.exp (c * (t : ℝ)) ≤ Real.exp c := Real.exp_le_exp.mpr htime
  have hboundSq : ‖y (t : ℝ)‖ ^ 2 ≤ ‖P.initialTorusL2‖ ^ 2 * Real.exp c := by
    calc
      ‖y (t : ℝ)‖ ^ 2 ≤ ‖D.initial‖ ^ 2 * Real.exp (c * (t : ℝ)) := by
        simpa [y, c] using henergy.1
      _ ≤ ‖P.initialTorusL2‖ ^ 2 * Real.exp c := by
        exact mul_le_mul (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hinitial)
          hexp (Real.exp_nonneg _) (sq_nonneg _)
  have hbound : ‖y (t : ℝ)‖ ≤ P.scalarBound := by
    apply (sq_le_sq₀ (norm_nonneg _) P.scalarBound_nonneg).1
    change ‖y (t : ℝ)‖ ^ 2 ≤
      (‖P.initialTorusL2‖ * Real.exp c) ^ 2
    have hexp1 : 1 ≤ Real.exp c := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hc
    have hexp_mul : Real.exp c ≤ Real.exp c * Real.exp c := by
      nlinarith [Real.exp_nonneg c, hexp1]
    calc
      ‖y (t : ℝ)‖ ^ 2 ≤ ‖P.initialTorusL2‖ ^ 2 * Real.exp c := hboundSq
      _ ≤ ‖P.initialTorusL2‖ ^ 2 * (Real.exp c * Real.exp c) :=
        mul_le_mul_of_nonneg_left hexp_mul (sq_nonneg _)
      _ = (‖P.initialTorusL2‖ * Real.exp c) ^ 2 := by ring
  have hy : y (t : ℝ) = u t := by
    exact AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) u ht
  rw [show P.scalarPath N t = realFourierScalarMap N (u t) by rfl,
      realFourierScalarMap_norm, ← hy]
  exact hbound

/-- Uniform space-time gradient energy for the positive-cutoff Galerkin paths. -/
theorem FrozenDriftProblem.gradientEnergy_le (P : FrozenDriftProblem) (N : ℕ) :
    ∫ t in (0 : ℝ)..1,
      ‖(P.galerkinData N).gradient
        (AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N) t)‖ ^ 2 ≤
      ‖P.initialTorusL2‖ ^ 2 *
        (1 + (positiveCutoffDriftConstant P.b P.drift_bounded ^ 2 / P.κ) *
          Real.exp (positiveCutoffDriftConstant P.b P.drift_bounded ^ 2 / P.κ)) / P.κ := by
  let D := P.galerkinData N
  let y := AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N)
  let c : ℝ := D.driftBound ^ 2 / D.diffusivity
  have hc : 0 ≤ c := div_nonneg (sq_nonneg D.driftBound) D.diffusivity_pos.le
  have hinitial : ‖D.initial‖ ≤ ‖P.initialTorusL2‖ := P.initialProjection_norm_le N
  have henergy := WeakFormGalerkinData.IsSolution.energyEstimate D
    (P.coefficientPath N) (P.coefficientPath_isSolution N) 1 (by norm_num)
  have hraw :
      (∫ t in (0 : ℝ)..1, ‖D.gradient (y t)‖ ^ 2) * D.diffusivity ≤
        ‖D.initial‖ ^ 2 * (1 + c * Real.exp c) := by
    have h := henergy.2
    simp only [one_mul, mul_one] at h
    nlinarith [h, sq_nonneg ‖y 1‖]
  have hinitialSq : ‖D.initial‖ ^ 2 ≤ ‖P.initialTorusL2‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hinitial
  have hfac : 0 ≤ 1 + c * Real.exp c := by positivity
  have hreplace : ‖D.initial‖ ^ 2 * (1 + c * Real.exp c) ≤
      ‖P.initialTorusL2‖ ^ 2 * (1 + c * Real.exp c) :=
    mul_le_mul_of_nonneg_right hinitialSq hfac
  have hdiv := (le_div_iff₀ D.diffusivity_pos).2 (hraw.trans hreplace)
  have hresult :
      (∫ t in (0 : ℝ)..1, ‖D.gradient (y t)‖ ^ 2) ≤
        ‖P.initialTorusL2‖ ^ 2 * (1 + c * Real.exp c) / D.diffusivity := by
    exact hdiv
  simpa [D, y, c, FrozenDriftProblem.galerkinData, positiveCutoffGalerkinData] using hresult

end AVenhance.Infra.Parabolic.FourierGalerkin

end
