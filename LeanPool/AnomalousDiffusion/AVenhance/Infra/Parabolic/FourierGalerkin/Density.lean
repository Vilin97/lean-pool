/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.LimitPassage

/-!
# Density of the real symmetric Fourier cutoffs

The union of the finite real Fourier synthesis ranges is dense in scalar torus `L²`.  This is the
test space used by the weak path compactness argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance densityMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance densityMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance densityProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance densityScalarTorusMeasureSeparable : IsSeparable (volume : Measure Torus) :=
  inferInstance
local instance densityTwoNeTopFact : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
local instance densityOneLeTwoFact : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-- The coefficient vector of the orthogonal cutoff projection of a torus `L²` class. -/
@[irreducible]
def realFourierProjectionCoefficients (N : ℕ) (v : ScalarTorusL2) :
    Coefficients (RealFourierDimension N) :=
  modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) (fun x => v x)

theorem Density.mFourierCoeff_congr_ae {f g : Torus → ℂ}
    (hfg : f =ᵐ[volume] g) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff f k = UnitAddTorus.mFourierCoeff g k := by
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  simp [hx]

/-- Real synthesis of the torus orthogonal projection agrees with the real part of the complex
Fourier cutoff in `L²`. -/
theorem realFourierScalarMap_projection_eq_realPartFourierSum (N : ℕ)
    (v : ScalarTorusL2) :
    realFourierScalarMap N (realFourierProjectionCoefficients N v) =
      Complex.reCLM.compLp
        (complexFourierPartialSumLp N (Complex.ofRealCLM.compLp v)) := by
  let fC : ComplexScalarTorusL2 := Complex.ofRealCLM.compLp v
  let fR : Torus → ℝ := fun x => v x
  let c := realFourierProjectionCoefficients N v
  have hcoeff (k : Fin 2 → ℤ) :
      UnitAddTorus.mFourierCoeff fC k =
        UnitAddTorus.mFourierCoeff (fun x => (fR x : ℂ)) k := by
    apply Density.mFourierCoeff_congr_ae
    filter_upwards [Complex.ofRealCLM.coeFn_compLp v] with x hx
    simpa [fC, fR] using hx
  have hpartial : ∀ x : Torus,
      complexFourierPartialSumFunction N (fun x => fC x) x =
        complexFourierPartialSum N fR x := by
    intro x
    simp [complexFourierPartialSumFunction, complexFourierPartialSum, hcoeff]
  have hclass :
      (fun x => complexFourierPartialSumLp N fC x) =ᵐ[volume]
        complexFourierPartialSum N fR := by
    filter_upwards [complexFourierPartialSumLp_coeFn N fC] with x hx
    rw [hx, hpartial]
  have hproj : modeExpansion (RealFourierDimension N) (realFourierModeFin N) c =
      realFourierProjection N fR := by
    simpa [c, realFourierProjectionCoefficients, fR] using
      realFourierModeFin_projectionExpansion_eq_projection N
        ((Lp.memLp v).integrable (by norm_num : 1 ≤ (2 : ENNReal)))
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp
      (complexFourierPartialSumLp N fC), hclass,
    realFourierScalarMap_coeFn N c] with x hreal hsum hexp
  calc
    (realFourierScalarMap N c) x =
        modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x := hexp
    _ = realFourierProjection N fR x := congrFun hproj x
    _ = Complex.reCLM (complexFourierPartialSum N fR x) := by
      rfl
    _ = Complex.reCLM (complexFourierPartialSumLp N fC x) := by rw [← hsum]
    _ = (Complex.reCLM.compLp (complexFourierPartialSumLp N fC)) x := hreal.symm

/-- The concrete real Galerkin synthesis ranges exhaust scalar torus `L²`. -/
theorem tendsto_realFourierProjection (v : ScalarTorusL2) :
    Tendsto (fun N => realFourierScalarMap N (realFourierProjectionCoefficients N v)) atTop
      (𝓝 v) := by
  let fC : ComplexScalarTorusL2 := Complex.ofRealCLM.compLp v
  have hreal : Complex.reCLM.compLp fC = v := by
    apply Lp.ext
    filter_upwards [Complex.reCLM.coeFn_compLp fC,
      Complex.ofRealCLM.coeFn_compLp v] with x hre hcast
    simp [fC, hre, hcast]
  have h := tendsto_realPartFourierPartialSumLp fC
  have h' : Tendsto
      (fun N => Complex.reCLM.compLp (complexFourierPartialSumLp N fC)) atTop
      (𝓝 v) := by simpa [hreal] using h
  apply h'.congr'
  filter_upwards with N
  exact (realFourierScalarMap_projection_eq_realPartFourierSum N v).symm

/-- Union of all finite real symmetric Fourier synthesis ranges. -/
def realFourierSpan : Set ScalarTorusL2 :=
  ⋃ N : ℕ, Set.range (realFourierScalarMap N)

/-- Finite real Fourier synthesis ranges form a dense family in scalar torus `L²`. -/
theorem realFourierSpan_dense : Dense realFourierSpan := by
  rw [Metric.dense_iff]
  intro v ε hε
  have hconv := tendsto_realFourierProjection v
  have hev : ∀ᶠ N in atTop,
      dist (realFourierScalarMap N (realFourierProjectionCoefficients N v)) v < ε :=
    hconv.eventually (Metric.ball_mem_nhds v hε)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨realFourierScalarMap N (realFourierProjectionCoefficients N v), ?_, ?_⟩
  · exact (by simpa [dist_comm] using hN N le_rfl)
  · exact mem_iUnion.mpr ⟨N, Set.mem_range_self _⟩

end AVenhance.Infra.Parabolic.FourierGalerkin

end
