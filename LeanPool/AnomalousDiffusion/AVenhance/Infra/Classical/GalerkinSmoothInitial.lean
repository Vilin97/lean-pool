/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothReal
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Density

/-! The strong Galerkin limit retains the prescribed initial trace. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalSmoothInitialMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalSmoothInitialMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalSmoothInitialProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

theorem GalerkinSmoothInitial.classicalGalerkinCoefficientPath_initial
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (N : ℕ) :
    classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N
      ⟨0, by norm_num, by norm_num⟩ =
      (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).initial := by
  let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
  have hsol := (classicalGalerkinCoefficientPath_isSolution
    φ hφ κ hκ F hF θ₀ hθ₀ N).integralSolution D.ode
  have hzero := hsol 0 ⟨le_rfl, by norm_num⟩
  have hext : AVenhance.Infra.ODE.extendCurve (by norm_num)
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) 0 =
      classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N
        ⟨0, by norm_num, by norm_num⟩ := by
    exact AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) _
      ⟨le_rfl, by norm_num⟩
  rw [hext] at hzero
  simpa [D, ForcedGalerkinData.ode, AVenhance.Infra.ODE.linearRhs] using hzero

/-- At time zero, the Cauchy limit of the smooth Galerkin paths is the torus `L²` class of the
initial datum. -/
theorem classicalGalerkinWordScalarPathLimit_initial
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per [] ⟨0, by norm_num, by norm_num⟩ =
      (memLp_periodicToTorus_real hθ₀.continuous hθ₀per).toLp
        (AVenhance.Infra.Torus.periodicToTorus θ₀) := by
  let t₀ : Icc (0 : ℝ) 1 := ⟨0, by norm_num, by norm_num⟩
  let mem := memLp_periodicToTorus_real hθ₀.continuous hθ₀per
  have hpathInitial (N : ℕ) :
      classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [] N t₀ =
        realFourierScalarMap N
          (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
            (AVenhance.Infra.Torus.periodicToTorus θ₀)) := by
    rw [classicalGalerkinWordScalarPath_apply]
    rw [GalerkinSmoothInitial.classicalGalerkinCoefficientPath_initial φ hφ κ hκ F hF θ₀ hθ₀ N]
    change realFourierScalarMap N
        (classicalFrozenDriftProblem φ hφ κ hκ θ₀ hθ₀ |>.galerkinData N).initial = _
    rfl
  have hprojectionCoeff (N : ℕ) :
      realFourierProjectionCoefficients N (mem.toLp
        (AVenhance.Infra.Torus.periodicToTorus θ₀)) =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus θ₀) := by
    ext i
    simp only [realFourierProjectionCoefficients, modeProjectionCoefficients,
      PiLp.toLp_apply]
    apply integral_congr_ae
    filter_upwards [mem.coeFn_toLp] with x hx
    rw [hx]
  have hlimit := classicalGalerkinWordScalarPathLimit_tendsto
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per []
  have heval : Tendsto
      (fun N => classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [] N t₀)
      atTop (𝓝 (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per [] t₀)) := by
    exact ((continuous_eval_const t₀).tendsto _).comp hlimit
  have hprojection : Tendsto
      (fun N => realFourierScalarMap N
        (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus θ₀)))
      atTop (𝓝 (mem.toLp (AVenhance.Infra.Torus.periodicToTorus θ₀))) := by
    have hbase := tendsto_realFourierProjection
      (mem.toLp (AVenhance.Infra.Torus.periodicToTorus θ₀))
    apply hbase.congr'
    filter_upwards with N
    rw [hprojectionCoeff N]
  have hpathProjection : Tendsto
      (fun N => classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ [] N t₀)
      atTop (𝓝 (mem.toLp (AVenhance.Infra.Torus.periodicToTorus θ₀))) := by
    apply hprojection.congr'
    filter_upwards with N
    exact (hpathInitial N).symm
  have heq := tendsto_nhds_unique heval hpathProjection
  simpa [t₀] using heq

end AVenhance.Infra.Classical

end
