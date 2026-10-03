/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinGenerator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Continuity and time integrability of the smooth forcing in each Fourier Galerkin system. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalForcingMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalForcingMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalForcingProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalForcingProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVenhance.Infra.Classical

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def GalerkinForcing.forcingClosedCell : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem GalerkinForcing.unitCell_ae_eq_forcingClosedCell :
    Filter.EventuallyEq (ae (volume : Measure (Vec 2)))
      (AVenhance.Infra.Torus.unitCell 2) GalerkinForcing.forcingClosedCell := by
  have hopen : AVenhance.unitCube =ᵐ[volume] GalerkinForcing.forcingClosedCell := by
    simpa [AVenhance.unitCube, GalerkinForcing.forcingClosedCell, volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc
        (f := fun _ : Fin 2 => (0 : ℝ)) (g := fun _ : Fin 2 => (1 : ℝ)))
  exact AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.trans hopen

theorem GalerkinForcing.forcingContinuousExtension
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    Continuous (Function.uncurry fun t x => F (max t 0) x) := by
  let clamp : ℝ × Vec 2 → ℝ × Vec 2 := fun p => (max p.1 0, p.2)
  have hclamp : Continuous clamp := by
    exact (continuous_fst.max continuous_const).prodMk continuous_snd
  have hmaps : Set.MapsTo clamp Set.univ (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro p hp
    exact ⟨show (0 : ℝ) ≤ max p.1 0 from le_max_right _ _, Set.mem_univ _⟩
  have hcontinuous := hF.continuousOn.comp hclamp.continuousOn hmaps
  have heq : (Function.uncurry fun t x => F (max t 0) x) =
      (Function.uncurry F) ∘ clamp := by
    rfl
  rw [heq]
  exact continuousOn_univ.mp hcontinuous

/-- Fourier projection of a smooth half-line forcing, extended continuously to negative times by
clamping the time coordinate at zero. -/
def classicalForcingCoefficients (N : ℕ) (F : ℝ → Vec 2 → ℝ)
    (t : ℝ) : Coefficients (RealFourierDimension N) :=
  modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
    (AVenhance.Infra.Torus.periodicToTorus (F (max t 0)))

theorem GalerkinForcing.classicalForcingCoefficient_eq_closedCellIntegral
    (N : ℕ) (F : ℝ → Vec 2 → ℝ)
    (t : ℝ) (i : Fin (RealFourierDimension N)) :
    classicalForcingCoefficients N F t i =
      ∫ x in GalerkinForcing.forcingClosedCell,
        F (max t 0) x * realFourierModeAmbient N
          ((realFourierIndexEquivFin N).symm i) x := by
  unfold classicalForcingCoefficients modeProjectionCoefficients
  change (WithLp.toLp 2 (fun j : Fin (RealFourierDimension N) =>
      ∫ x : Torus, AVenhance.Infra.Torus.periodicToTorus (F (max t 0)) x *
        realFourierModeFin N j x)).ofLp i = _
  rw [WithLp.ofLp_toLp]
  have ht : 0 ≤ max t 0 := le_max_right _ _
  have hmode := realFourierModeFin_eq_periodicToTorus N i
  have hproduct :
      (fun x : Torus => AVenhance.Infra.Torus.periodicToTorus (F (max t 0)) x *
        realFourierModeFin N i x) =
      AVenhance.Infra.Torus.periodicToTorus
        (fun x : Vec 2 => F (max t 0) x * realFourierModeAmbient N
          ((realFourierIndexEquivFin N).symm i) x) := by
    funext x
    rw [hmode]
    rfl
  rw [hproduct, AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell]
  exact setIntegral_congr_set GalerkinForcing.unitCell_ae_eq_forcingClosedCell

/-- The coefficient forcing path is continuous, hence interval integrable on every compact time
interval. -/
theorem classicalForcingCoefficients_continuous (N : ℕ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    Continuous (classicalForcingCoefficients N F) := by
  have hFext := GalerkinForcing.forcingContinuousExtension F hF
  let mode (i : Fin (RealFourierDimension N)) :=
    realFourierModeAmbient N ((realFourierIndexEquivFin N).symm i)
  have hcoordinate (i : Fin (RealFourierDimension N)) :
      Continuous (fun t => classicalForcingCoefficients N F t i) := by
    rw [show (fun t => classicalForcingCoefficients N F t i) =
        fun t => ∫ x in GalerkinForcing.forcingClosedCell,
          F (max t 0) x * mode i x from by
            funext t
            simpa [mode] using
              GalerkinForcing.classicalForcingCoefficient_eq_closedCellIntegral N F t i]
    apply continuous_parametric_integral_of_continuous
    · change Continuous (fun p : ℝ × Vec 2 =>
        F (max p.1 0) p.2 * mode i p.2)
      have hmode : Continuous (fun p : ℝ × Vec 2 => mode i p.2) :=
        (realFourierModeAmbient_contDiff N
          ((realFourierIndexEquivFin N).symm i)).continuous.comp continuous_snd
      have hprod : Continuous (fun p : ℝ × Vec 2 =>
          F (max p.1 0) p.2 * mode i p.2) := hFext.mul hmode
      exact hprod
    · simpa [GalerkinForcing.forcingClosedCell] using
        (isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc))
  let e : Coefficients (RealFourierDimension N) ≃L[ℝ]
      (Fin (RealFourierDimension N) → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (RealFourierDimension N) => ℝ)
  have hcomponents : Continuous (fun t : ℝ => fun i =>
      classicalForcingCoefficients N F t i) := by
    exact continuous_pi fun i => hcoordinate i
  have hcoe : (fun t : ℝ => classicalForcingCoefficients N F t) =
      fun t => e.symm (fun i => classicalForcingCoefficients N F t i) := by
    funext t
    apply e.injective
    ext i
    rfl
  change Continuous (fun t : ℝ => classicalForcingCoefficients N F t)
  rw [hcoe]
  exact e.symm.continuous.comp hcomponents

theorem classicalForcingCoefficients_intervalIntegrable (N : ℕ)
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) :
    IntervalIntegrable (classicalForcingCoefficients N F) volume 0 1 :=
  (classicalForcingCoefficients_continuous N F hF).continuousOn
    |>.intervalIntegrable_of_Icc (by norm_num)

end AVenhance.Infra.Classical

end
