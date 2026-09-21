/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHS
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.GlobalIteration
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise
import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities
import LeanPool.CoarseGraining.Homogenization.PDE.NeumannRHS
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalCubeBridge

/-! # Energy -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public energy bridges for Chapter 3

This file contains the energy-density and energy-norm identities that convert
public a.e. coefficient data to deterministic pointwise coefficient fields.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

theorem volumeAverage_eq_of_ae_eq {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f = volumeAverage U g := by
  unfold volumeAverage
  congr 1
  exact MeasureTheory.integral_congr_ae hfg

theorem localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity
    {d : ℕ} {U : Ch02.Domain d} (V : Set (Vec d))
    (a : Ch02.CoeffOn U) (u : H1Function (U : Set (Vec d))) :
    localizedCoeffEnergyValue V a u =
      volumeAverage V (coefficientEnergyDensity a.toCoeffField u.grad) := by
  rfl

theorem cubeAverage_coefficientEnergyDensity_publicCoeffField_eq_localizedCoeffEnergyValue
    {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q a) u.grad) =
      localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) u := by
  have henergy_ae :
      coefficientEnergyDensity (publicCoeffField Q a) u.grad
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
      coefficientEnergyDensity (a.coeffOn Q).toCoeffField u.grad := by
    filter_upwards [publicCoeffField_ae_eq_openCubeSet Q a] with x hx
    simp [coefficientEnergyDensity, hx]
  calc
    cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q a) u.grad)
        =
      volumeAverage (openCubeSet Q)
        (coefficientEnergyDensity (publicCoeffField Q a) u.grad) := by
        simp [cubeAverage, volumeAverage, volume_openCubeSet_eq_volume_cubeSet,
          volume_cubeSet_toReal, setIntegral_cubeSet_eq_setIntegral_openCubeSet]
    _ =
      volumeAverage (openCubeSet Q)
        (coefficientEnergyDensity (a.coeffOn Q).toCoeffField u.grad) :=
        volumeAverage_eq_of_ae_eq henergy_ae
    _ =
      localizedCoeffEnergyValue (openCubeSet Q) (a.coeffOn Q) u :=
        (localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity
          (openCubeSet Q) (a.coeffOn Q) u).symm

theorem h1EnergyNormOnCube_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
    {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    h1EnergyNormOnCube Q a u =
      Real.sqrt
        (cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a) u.grad)) := by
  rw [h1EnergyNormOnCube,
    cubeAverage_coefficientEnergyDensity_publicCoeffField_eq_localizedCoeffEnergyValue]

theorem forcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
    {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d)
    {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g) :
    forcedSolutionEnergyNorm Q a u =
      Real.sqrt
        (cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (forcedSolutionGradientField u))) := by
  simpa [forcedSolutionEnergyNorm, forcedSolutionGradientField] using
    h1EnergyNormOnCube_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
      Q a u.toH1

theorem zeroTraceForcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
    {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d)
    {g : Vec d → Vec d} (u : ZeroTraceForcedCubeSolution Q a g) :
    zeroTraceForcedSolutionEnergyNorm Q a u =
      Real.sqrt
        (cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            u.toH10.toH1Function.grad)) := by
  simpa [zeroTraceForcedSolutionEnergyNorm] using
    h1EnergyNormOnCube_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
      Q a u.toH10.toH1Function

theorem dirichletForcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
    {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d)
    {g : Vec d → Vec d} (u : DirichletForcedCubeSolution Q a g) :
    dirichletForcedSolutionEnergyNorm Q a u =
      Real.sqrt
        (cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a) u.toH1.grad)) := by
  simpa [dirichletForcedSolutionEnergyNorm] using
    h1EnergyNormOnCube_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
      Q a u.toH1

theorem neumannForcedSolutionEnergyNorm_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
    {d : ℕ} (Q : TriadicCube d) (a : CoeffFamily d)
    {g : Vec d → Vec d} (u : NeumannForcedCubeSolution Q a g) :
    neumannForcedSolutionEnergyNorm Q a u =
      Real.sqrt
        (cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            u.toH1MeanZero.toH1Function.grad)) := by
  simpa [neumannForcedSolutionEnergyNorm] using
    h1EnergyNormOnCube_eq_sqrt_cubeAverage_coefficientEnergyDensity_publicCoeffField
      Q a u.toH1MeanZero.toH1Function


end

end Ch03
end Book
end Homogenization
