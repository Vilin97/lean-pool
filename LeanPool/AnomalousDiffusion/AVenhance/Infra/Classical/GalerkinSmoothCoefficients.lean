/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinProblem
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Continuity of the finite smooth Galerkin operators on the physical time slab. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalSmoothCoefficientsMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalSmoothCoefficientsMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalSmoothCoefficientsProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalSmoothCoefficientsTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def GalerkinSmoothCoefficients.classicalCoefficientClosedCell : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem GalerkinSmoothCoefficients.classicalCoefficientCell_ae_eq_closedCell :
    AVenhance.Infra.Torus.unitCell 2 =ᵐ[volume]
        GalerkinSmoothCoefficients.classicalCoefficientClosedCell := by
  have hopen : AVenhance.unitCube =ᵐ[volume]
      GalerkinSmoothCoefficients.classicalCoefficientClosedCell := by
    simpa [AVenhance.unitCube, GalerkinSmoothCoefficients.classicalCoefficientClosedCell,
        volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc
        (f := fun _ : Fin 2 => (0 : ℝ)) (g := fun _ : Fin 2 => (1 : ℝ)))
  exact AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.trans hopen

theorem GalerkinSmoothCoefficients.classicalCoefficient_driftIntegral_eq_closedCell
    (φ : ℝ → Vec 2 → ℝ)
    (N : ℕ) (t : ℝ) (i j : Fin (RealFourierDimension N)) :
    (∫ x : Torus,
      AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
        (AVenhance.Infra.Torus.periodicToTorus (AVenhance.streamVel φ t) x)
        (realFourierModeGradFin N j x) * realFourierModeFin N i x) =
      ∫ x in GalerkinSmoothCoefficients.classicalCoefficientClosedCell,
        Homogenization.vecDot (AVenhance.streamVel φ t x)
          (realFourierModeAmbientGrad N
            ((realFourierIndexEquivFin N).symm j) x) *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i) x := by
  let g : Vec 2 → ℝ := fun x =>
    Homogenization.vecDot (AVenhance.streamVel φ t x)
      (realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm j) x) *
      realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i) x
  have hgrad := realFourierModeGradFin_eq_periodicToTorus N j
  have hmode := realFourierModeFin_eq_periodicToTorus N i
  have htorus : (fun x : Torus =>
      AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
        (AVenhance.Infra.Torus.periodicToTorus (AVenhance.streamVel φ t) x)
        (realFourierModeGradFin N j x) * realFourierModeFin N i x) =
  AVenhance.Infra.Torus.periodicToTorus g := by
    funext x
    rw [hgrad, hmode]
    simp only [AVenhance.Infra.Parabolic.FourierGalerkin.vecDot]
    rfl
  calc
    _ = ∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus g x := by rw [htorus]
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2, g x :=
      AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell g
    _ = ∫ x in GalerkinSmoothCoefficients.classicalCoefficientClosedCell, g x :=
      setIntegral_congr_set GalerkinSmoothCoefficients.classicalCoefficientCell_ae_eq_closedCell

theorem GalerkinSmoothCoefficients.classicalCoefficient_drift_extension
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ) :
    Continuous (Function.uncurry (AVenhance.streamVel φ)) := by
  exact (streamVel_smoothPeriodic φ hφ).smooth.continuous

theorem GalerkinSmoothCoefficients.classicalCoefficient_entry_continuous
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (N : ℕ) (i j : Fin (RealFourierDimension N)) :
    Continuous (fun t : ℝ => weakFormMatrixEntry
      (fun s x => AVenhance.Infra.Torus.periodicToTorus
        (AVenhance.streamVel φ s) x)
      κ (realFourierModeFin N) (realFourierModeGradFin N) t i j) := by
  let mi := realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)
  let gj := realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm j)
  let cell := GalerkinSmoothCoefficients.classicalCoefficientClosedCell
  have hmi : Continuous mi :=
    (realFourierModeAmbient_contDiff N ((realFourierIndexEquivFin N).symm i)).continuous
  have hgj : Continuous gj := realFourierModeAmbientGrad_continuous N
    ((realFourierIndexEquivFin N).symm j)
  have hbParam : Continuous (fun p : ℝ × Vec 2 => AVenhance.streamVel φ p.1 p.2) :=
    GalerkinSmoothCoefficients.classicalCoefficient_drift_extension φ hφ
  have hdriftIntegrand : Continuous (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (AVenhance.streamVel φ p.1 p.2) (gj p.2) * mi p.2) := by
    change Continuous (fun p : ℝ × Vec 2 =>
      (∑ m : Fin 2, AVenhance.streamVel φ p.1 p.2 m * gj p.2 m) * mi p.2)
    apply (continuous_finsetSum Finset.univ _).mul (hmi.comp continuous_snd)
    intro m hm
    exact (((continuous_apply m).comp hbParam).mul
      (((continuous_apply m).comp hgj).comp continuous_snd))
  have hcompact : IsCompact cell := by
    simpa [cell, GalerkinSmoothCoefficients.classicalCoefficientClosedCell] using
      (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
  have hdriftCell : Continuous (fun t : ℝ =>
      ∫ x in cell, Homogenization.vecDot (AVenhance.streamVel φ t x) (gj x) * mi x) := by
    apply continuous_parametric_integral_of_continuous
    · exact hdriftIntegrand
    · exact hcompact
  have hentry : (fun t : ℝ => weakFormMatrixEntry
      (fun s x => AVenhance.Infra.Torus.periodicToTorus
        (AVenhance.streamVel φ s) x)
      κ (realFourierModeFin N) (realFourierModeGradFin N) t i j) =
      fun t => -(∫ x in cell,
        Homogenization.vecDot (AVenhance.streamVel φ t x) (gj x) * mi x) -
        κ * ∫ x : Torus,
          AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
            (realFourierModeGradFin N j x) (realFourierModeGradFin N i x) := by
    funext t
    simp only [weakFormMatrixEntry]
    rw [GalerkinSmoothCoefficients.classicalCoefficient_driftIntegral_eq_closedCell φ N t i j]
  rw [hentry]
  exact hdriftCell.neg.sub continuous_const

theorem GalerkinSmoothCoefficients.classicalCoefficient_matrix_continuous
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (N : ℕ) :
    Continuous (fun t : ℝ => matrixCoefficientCLM
      (fun i j => weakFormMatrixEntry
        (fun s x => AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.streamVel φ s) x)
        κ (realFourierModeFin N) (realFourierModeGradFin N) t i j)) := by
  classical
  unfold matrixCoefficientCLM
  apply continuous_finsetSum Finset.univ
  intro i hi
  apply continuous_finsetSum Finset.univ
  intro j hj
  exact (GalerkinSmoothCoefficients.classicalCoefficient_entry_continuous φ hφ κ N i j).smul
      continuous_const

/-- The finite Galerkin operator in `classicalForcedGalerkinData` is continuous on `[0,1]`.
This makes its integral ODE classically differentiable at interior times. -/
theorem classicalForcedGalerkinCoefficient_continuousOn
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (N : ℕ) :
    ContinuousOn
      (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient
      (Icc (0 : ℝ) 1) := by
  have hmatrix := GalerkinSmoothCoefficients.classicalCoefficient_matrix_continuous φ hφ κ N
  have hEq : ∀ t ∈ Icc (0 : ℝ) 1,
      (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient t =
        matrixCoefficientCLM
          (fun i j => weakFormMatrixEntry
            (fun s x => AVenhance.Infra.Torus.periodicToTorus
              (AVenhance.streamVel φ s) x)
            κ (realFourierModeFin N) (realFourierModeGradFin N) t i j) := by
    intro t ht
    change frozenWeakFormCoefficient (AVenhance.streamVel φ) κ
      (realFourierModeFin N) (realFourierModeGradFin N) t = _
    simp [frozenWeakFormCoefficient, ht]
  refine hmatrix.continuousOn.congr ?_
  intro t ht
  exact hEq t ht

/-- Interior classical derivative of each forced Galerkin coefficient path. -/
theorem classicalGalerkinCoefficientPath_hasDerivAt
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (AVenhance.Infra.ODE.extendCurve (by norm_num)
        (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N))
      ((classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient t
          (AVenhance.Infra.ODE.extendCurve (by norm_num)
            (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t) +
        classicalForcingCoefficients N F t) t := by
  let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
  have hA : ContinuousOn D.weak.coefficient (Icc (0 : ℝ) 1) := by
    exact classicalForcedGalerkinCoefficient_continuousOn φ hφ κ hκ F hF θ₀ hθ₀ N
  have hf : ContinuousOn D.forcing (Icc (0 : ℝ) 1) := by
    change ContinuousOn (classicalForcingCoefficients N F) (Icc (0 : ℝ) 1)
    exact (classicalForcingCoefficients_continuous N F hF).continuousOn
  exact D.hasDerivAt_on_Ioo_of_continuousOn
    (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N)
    (classicalGalerkinCoefficientPath_isSolution φ hφ κ hκ F hF θ₀ hθ₀ N)
    hA hf ht

end AVenhance.Infra.Classical

end
