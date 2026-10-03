/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.GalerkinSequence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.FourierLimit

/-!
# The projected trace and the real Fourier limit

These lemmas identify the initial value of the concrete Galerkin paths with the real part of the
complex torus Fourier cutoff.  Combined with Parseval convergence, they supply the weak path
compactness theorem with the exact initial trace.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance limitPassageMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance limitPassageMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance limitPassageProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The chosen finite Galerkin coefficient path starts at its orthogonal initial projection. -/
theorem FrozenDriftProblem.coefficientPath_initial (P : FrozenDriftProblem) (N : ℕ) :
    P.coefficientPath N ⟨0, by norm_num, by norm_num⟩ = (P.galerkinData N).initial := by
  let D := P.galerkinData N
  have hsol := (P.coefficientPath_isSolution N).integralSolution D.ode
  have hzero := hsol 0 ⟨le_rfl, by norm_num⟩
  have hext : AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N) 0 =
      P.coefficientPath N ⟨0, by norm_num, by norm_num⟩ := by
    exact AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) _ ⟨le_rfl, by norm_num⟩
  rw [hext] at hzero
  simpa [D, WeakFormGalerkinData.ode, AVenhance.Infra.ODE.linearRhs] using hzero

theorem LimitPassage.mFourierCoeff_congr_ae {f g : Torus → ℂ}
    (hfg : f =ᵐ[volume] g) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff f k = UnitAddTorus.mFourierCoeff g k := by
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  simp [hx]

/-- The complexified initial datum has the canonical real representative a.e. -/
theorem FrozenDriftProblem.initialComplexification_ae (P : FrozenDriftProblem) :
    (fun x => (Complex.ofRealCLM.compLp P.initialTorusL2) x) =ᵐ[volume]
      fun x => ((AVenhance.Infra.Torus.periodicToTorus P.θ₀ : Torus → ℝ) x : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLp P.initialTorusL2,
    (frozenInitialData_memLp_torus P.initial_memL2).coeFn_toLp] with x hmap hinit
  rw [hmap, FrozenDriftProblem.initialTorusL2, hinit]
  rfl

/-- The coefficient path's real scalar initial state is the real Fourier cutoff of the datum. -/
theorem FrozenDriftProblem.initialProjection_eq_realPartFourierSum
    (P : FrozenDriftProblem) (N : ℕ) :
    realFourierScalarMap N (P.galerkinData N).initial =
      Complex.reCLM.compLp
        (complexFourierPartialSumLp N (Complex.ofRealCLM.compLp P.initialTorusL2)) := by
  let f₀ : Torus → ℝ := AVenhance.Infra.Torus.periodicToTorus P.θ₀
  let fC : ComplexScalarTorusL2 := Complex.ofRealCLM.compLp P.initialTorusL2
  have hcoeff (k : Fin 2 → ℤ) :
      UnitAddTorus.mFourierCoeff fC k =
        UnitAddTorus.mFourierCoeff (fun x => (f₀ x : ℂ)) k := by
    exact LimitPassage.mFourierCoeff_congr_ae (P.initialComplexification_ae) k
  have hpartial : ∀ x : Torus,
      complexFourierPartialSumFunction N (fun x => fC x) x =
        complexFourierPartialSum N f₀ x := by
    intro x
    simp [complexFourierPartialSumFunction, complexFourierPartialSum, hcoeff]
  have hclass :
      (fun x => complexFourierPartialSumLp N fC x) =ᵐ[volume]
        complexFourierPartialSum N f₀ := by
    filter_upwards [complexFourierPartialSumLp_coeFn N fC] with x hx
    rw [hx, hpartial]
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp
      (complexFourierPartialSumLp N fC), hclass,
    realFourierScalarMap_coeFn N (P.galerkinData N).initial] with x hreal hsum hexp
  have hproj : modeExpansion (RealFourierDimension N) (realFourierModeFin N)
      (P.galerkinData N).initial x = realFourierProjection N f₀ x := by
    simpa [f₀, FrozenDriftProblem.galerkinData, positiveCutoffGalerkinData] using
      positiveCutoffInitial_projection N P.θ₀ P.initial_memL2 x
  calc
    (realFourierScalarMap N (P.galerkinData N).initial) x =
        modeExpansion (RealFourierDimension N) (realFourierModeFin N)
          (P.galerkinData N).initial x := hexp
    _ = realFourierProjection N f₀ x := hproj
    _ = Complex.reCLM (complexFourierPartialSum N f₀ x) := by
      simp [realFourierProjection, Complex.reCLM]
    _ = Complex.reCLM (complexFourierPartialSumLp N fC x) := by
      rw [← hsum]
    _ = (Complex.reCLM.compLp (complexFourierPartialSumLp N fC)) x := hreal.symm

/-- The concrete Galerkin paths start at the projected initial datum. -/
theorem FrozenDriftProblem.scalarPath_initial (P : FrozenDriftProblem) (N : ℕ) :
    P.scalarPath N ⟨0, by norm_num, by norm_num⟩ =
      realFourierScalarMap N (P.galerkinData N).initial := by
  change realFourierScalarMap N
    (P.coefficientPath N ⟨0, by norm_num, by norm_num⟩) = _
  rw [P.coefficientPath_initial N]

/-- The finite Galerkin initial traces converge weakly to the `L²` datum. -/
theorem FrozenDriftProblem.initialTrace_weak_tendsto (P : FrozenDriftProblem)
    (v : ScalarTorusL2) :
    Tendsto
      (fun N => inner ℝ (P.scalarPath N ⟨0, by norm_num, by norm_num⟩) v) atTop
      (𝓝 (inner ℝ P.initialTorusL2 v)) := by
  let fC : ComplexScalarTorusL2 := Complex.ofRealCLM.compLp P.initialTorusL2
  have hreal : Complex.reCLM.compLp fC = P.initialTorusL2 := by
    apply Lp.ext
    filter_upwards [Complex.reCLM.coeFn_compLp fC,
      Complex.ofRealCLM.coeFn_compLp P.initialTorusL2] with x hre hcast
    simp [fC, hre, hcast]
  have hstrong : Tendsto
      (fun N => P.scalarPath N ⟨0, by norm_num, by norm_num⟩) atTop
      (𝓝 P.initialTorusL2) := by
    have h := tendsto_realPartFourierPartialSumLp fC
    have h' : Tendsto (fun N =>
        Complex.reCLM.compLp (complexFourierPartialSumLp N fC)) atTop
        (𝓝 P.initialTorusL2) := by simpa [hreal] using h
    have hseq : (fun N => P.scalarPath N ⟨0, by norm_num, by norm_num⟩) =
        fun N => Complex.reCLM.compLp (complexFourierPartialSumLp N fC) := by
      funext N
      rw [P.scalarPath_initial N, P.initialProjection_eq_realPartFourierSum N]
    rw [hseq]
    exact h'
  have hcontinuous : Continuous (fun w : ScalarTorusL2 => inner ℝ w v) :=
    continuous_id.inner continuous_const
  exact hcontinuous.continuousAt.tendsto.comp hstrong

end AVenhance.Infra.Parabolic.FourierGalerkin

end
