/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinForcing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.ForcedGalerkin
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.FamilyEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.PeriodicSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.GalerkinSequence

/-! The forced finite Fourier systems associated with the smooth classical data. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

namespace AVenhance.Infra.Classical

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def GalerkinProblem.classicalProblemClosedCell : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem GalerkinProblem.classicalProblemClosedCell_compact :
    IsCompact GalerkinProblem.classicalProblemClosedCell := by
  simpa [GalerkinProblem.classicalProblemClosedCell] using
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem GalerkinProblem.classicalProblem_cube_subset_closedCell :
    AVenhance.unitCube ⊆ GalerkinProblem.classicalProblemClosedCell := by
  intro x hx
  simp only [AVenhance.unitCube, GalerkinProblem.classicalProblemClosedCell,
    Set.mem_pi, Set.mem_univ, forall_true_left] at hx ⊢
  intro i
  exact ⟨le_of_lt (hx i).1, le_of_lt (hx i).2⟩

theorem GalerkinProblem.classicalProblem_smooth_memL2On {θ₀ : Vec 2 → ℝ}
    (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) : MemL2On AVenhance.unitCube θ₀ := by
  apply (memLp_two_iff_integrable_sq
    hθ₀.continuous.measurable.aestronglyMeasurable).2
  exact (hθ₀.continuous.pow 2).continuousOn.integrableOn_compact
    GalerkinProblem.classicalProblemClosedCell_compact |>.mono_set
        GalerkinProblem.classicalProblem_cube_subset_closedCell

/-- Compact time-space cell used to control the forcing on the unit time interval. -/
def GalerkinProblem.classicalForcingJointCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ GalerkinProblem.classicalProblemClosedCell

theorem GalerkinProblem.classicalForcingJointCell_compact :
    IsCompact GalerkinProblem.classicalForcingJointCell := by
  simpa [GalerkinProblem.classicalForcingJointCell] using
    isCompact_Icc.prod GalerkinProblem.classicalProblemClosedCell_compact

/-- The classical smooth hypotheses instantiate the finite Fourier data. -/
noncomputable def classicalFrozenDriftProblem
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (θ₀ : Vec 2 → ℝ)
    (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) : FrozenDriftProblem where
  b := AVenhance.streamVel φ
  drift_measurable := by
    have hb := (streamVel_smoothPeriodic φ hφ).smooth.continuous
    exact hb.measurable.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  drift_bounded := by
    obtain ⟨B, hB, hbound⟩ := streamVel_global_derivative_bound φ hφ 0
    refine ⟨B, ?_⟩
    intro t ht x
    simpa using hbound (t, x)
  drift_periodic := by
    intro t ht k x
    have h := (streamVel_smoothPeriodic φ hφ).periodic 0 k t x
    simpa [AVenhance.Infra.Flow.jointLatticeShift, AVenhance.latticeShift] using h
  κ := κ
  κ_pos := hκ
  θ₀ := θ₀
  initial_memL2 := GalerkinProblem.classicalProblem_smooth_memL2On hθ₀

/-- The cutoff Galerkin path forced by the Fourier projection of `F`. -/
noncomputable def classicalForcedGalerkinData
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ)
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N : ℕ) : ForcedGalerkinData (Coefficients (RealFourierDimension N))
      SpatialGradientL2 := by
  let P := classicalFrozenDriftProblem φ hφ κ hκ θ₀ hθ₀
  let W := AVenhance.Infra.Classical.WeakFormGalerkinData.toEnergyWeakForm
    (P.galerkinData N)
  exact ForcedGalerkinData.ofWeak W (P.galerkinData N).initial
    (classicalForcingCoefficients N F)
    (classicalForcingCoefficients_intervalIntegrable N F hF)

/-- Every smooth cutoff system has its classical forced coefficient path. -/
noncomputable def classicalGalerkinCoefficientPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ)
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N : ℕ) : C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N)) :=
  Classical.choose
    (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).existsUnique_solution.exists

theorem classicalGalerkinCoefficientPath_isSolution
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ)
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N : ℕ) :
    (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).ode.IsSolution
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) := by
  let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
  change D.ode.IsSolution (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N)
  apply (D.ode.isSolution_iff_integralSolution _).2
  exact (Classical.choose_spec
    (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).existsUnique_solution.exists).1

end AVenhance.Infra.Classical

end
