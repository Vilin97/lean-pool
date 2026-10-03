/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothCoefficients
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothLimit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinGenerator

/-! Fourier coefficient equations for the finite classical Galerkin paths. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalSmoothEquationMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalSmoothEquationMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalSmoothEquationProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalSmoothEquationTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

/-- A finite Galerkin Fourier coefficient has the derivative obtained by applying its coefficient
functional to the finite ODE right-hand side. -/
theorem classicalGalerkinFourierCoefficient_hasDerivAt
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N : ℕ) (k : Fin 2 → ℤ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => classicalComplexFourierCoeffCLM k
        (realFourierScalarMap N
          (AVenhance.Infra.ODE.extendCurve (by norm_num)
            (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) s)))
      (classicalComplexFourierCoeffCLM k
        (realFourierScalarMap N
          ((classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient t
            (AVenhance.Infra.ODE.extendCurve (by norm_num)
              (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t) +
            classicalForcingCoefficients N F t))) t := by
  let L : Coefficients (RealFourierDimension N) →L[ℝ] ℂ :=
    (classicalComplexFourierCoeffCLM k).comp (realFourierScalarMap N)
  have hpath := classicalGalerkinCoefficientPath_hasDerivAt
    φ hφ κ hκ F hF θ₀ hθ₀ N ht
  have hL := (hasDerivAt_const t L).clm_apply hpath
  simpa [L, ContinuousLinearMap.comp_apply] using hL

theorem GalerkinSmoothEquation.classicalSmoothModePeriodicity (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    AVenhance.IsZ2Periodic (realFourierModeAmbientExpansion N c) :=
  realFourierModeAmbientExpansion_periodic N c

theorem GalerkinSmoothEquation.classicalSmoothModeLaplacian_contDiff (u : Vec 2 → ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceLap u x) := by
  unfold AVenhance.spaceLap
  apply ContDiff.sum
  intro i hi
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad u x i) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ u x (Homogenization.basisVec i))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ (fun y => AVenhance.spaceGrad u y i) x
      (Homogenization.basisVec i))
  exact (hgrad.fderiv_right (by simp)).clm_apply contDiff_const

theorem GalerkinSmoothEquation.classicalSmoothModeTransport_contDiff
    (b : Vec 2 → Vec 2) (u : Vec 2 → ℝ)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => Homogenization.vecDot (b x) (AVenhance.spaceGrad u x)) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ i : Fin 2, b x i * AVenhance.spaceGrad u x i)
  apply ContDiff.sum
  intro i hi
  have hbcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i) := (contDiff_pi.1 hb) i
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad u x i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ u x (Homogenization.basisVec i))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  exact hbcomp.mul hgrad

end AVenhance.Infra.Classical

end
