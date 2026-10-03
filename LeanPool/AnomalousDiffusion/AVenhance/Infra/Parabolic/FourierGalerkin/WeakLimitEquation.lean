/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.FrozenDriftProduct
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.CutoffNesting
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.FiniteWeakForm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.LimitConstruction

/-!
# Product-space weak equation on finite Fourier tests

This module connects the finite Galerkin identities to the synchronized product-space limits.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance weakLimitEquationMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance weakLimitEquationMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weakLimitEquationProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Pairing the initial datum with a cutoff Fourier test is the coefficient pairing with the
Galerkin projection of the datum. -/
theorem FrozenDriftProblem.initialProjection_pairing (P : FrozenDriftProblem) (N : ℕ)
    (d : Coefficients (RealFourierDimension N)) :
    inner ℝ P.initialTorusL2 (realFourierScalarMap N d) =
      inner ℝ (P.galerkinData N).initial d := by
  have hmode (i : Fin (RealFourierDimension N)) :
      inner ℝ P.initialTorusL2 (realFourierModeL2 N i) =
        (P.galerkinData N).initial i := by
    rw [MeasureTheory.L2.inner_def]
    have hinit : (fun x : Torus => P.initialTorusL2 x) =ᵐ[volume]
        AVenhance.Infra.Torus.periodicToTorus P.θ₀ := by
      simpa [FrozenDriftProblem.initialTorusL2] using
        (frozenInitialData_memLp_torus P.initial_memL2).coeFn_toLp
    have hmode : (fun x : Torus => realFourierModeL2 N i x) =ᵐ[volume]
        realFourierModeFin N i := by
      simpa [realFourierModeL2] using (realFourierModeFin_memLp N i).coeFn_toLp
    have hdata : (P.galerkinData N).initial =
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus P.θ₀) := rfl
    rw [hdata, modeProjectionCoefficients]
    apply integral_congr_ae
    filter_upwards [hinit, hmode] with x hx hmx
    rw [hx, hmx]
    simp [mul_comm]
  rw [realFourierScalarMap_apply, inner_sum]
  simp_rw [inner_smul_right, hmode]
  simp [PiLp.inner_apply]

end AVenhance.Infra.Parabolic.FourierGalerkin

end
