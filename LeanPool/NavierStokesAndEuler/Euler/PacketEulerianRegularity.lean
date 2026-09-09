/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceSmoothField
public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalFieldTower

@[expose] public section

/-! Actual Eulerian reconstructions have every spatial derivative in L²,
continuously in time. Sobolev embedding also supplies bounded smooth
coefficient paths for the velocity and pressure force. -/

noncomputable section

namespace EulerPacketPhysicalField

open Set MeasureTheory EulerSmoothLimit EulerAllOrderCorrectionData
  EulerPacketCorrectionCoefficients EulerGraphPressurePotential EulerGevrey
  EulerLpTranslation EulerMeanCoefficients EulerPacketPiola

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (κ : ℝ) (Z : FieldTower P D.T)

def pressureForceTower : FieldTower P D.T :=
  (Z.multiply ((inverseCoefficient D).adjoint.toCoefficientTower P)).smul κ

theorem pressureForceTower_pointField (t : Icc (0 : ℝ) D.T)
    (x : EulerLiftedGradientSpace.LiftDomain P) :
    (pressureForceTower D P κ Z).pointField t x =
      κ • (D.FInv.field t x.1).adjoint (Z.pointField t x) := by
  rw [pressureForceTower, FieldTower.smul_pointField, FieldTower.multiply_pointField]
  rfl

variable (k : ℝ) (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hY : Continuous (Function.uncurry Y))
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det=1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C*majorant R 0 n)

def eulerianSmoothField (t : Icc (0 : ℝ) D.T) : SmoothL2Field Space :=
  EulerPacketSourceVolumeSobolev.smoothField D (reconstructedTower D P κ Z) k D.m₀
    X Y hX hYX hXY hY R C hR hC hdet hF t

theorem eulerianSmoothField_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (eulerianSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).field x =
      κ • D.F.field t (Y t x) (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) :=
  reconstructedTower_pointField D P κ Z t (cylinderGraph P k D.m₀ (Y t x))

theorem eulerianSmoothField_jetLp_continuous (n : ℕ) :
    Continuous (fun t =>
      (eulerianSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).jetLp n) :=
  EulerPacketSourceVolumeSobolev.smoothField_jetLp_continuous D (reconstructedTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF n

def eulerianCoefficientPath : SmoothCoefficientPath (Icc (0 : ℝ) D.T) Space :=
  EulerPacketSourceVolumeSobolev.smoothCoefficientPath D (reconstructedTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF

theorem eulerianCoefficientPath_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (eulerianCoefficientPath D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF).field t x =
      κ • D.F.field t (Y t x) (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) := by
  rw [eulerianCoefficientPath, EulerPacketSourceVolumeSobolev.smoothCoefficientPath_apply,
    reconstructedTower_pointField]
  rfl

def pressureForceSmoothField (t : Icc (0 : ℝ) D.T) : SmoothL2Field Space :=
  EulerPacketSourceVolumeSobolev.smoothField D (pressureForceTower D P κ Z) k D.m₀
    X Y hX hYX hXY hY R C hR hC hdet hF t

theorem pressureForceSmoothField_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (pressureForceSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).field x =
      κ • (D.FInv.field t (Y t x)).adjoint
        (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) :=
  pressureForceTower_pointField D P κ Z t (cylinderGraph P k D.m₀ (Y t x))

theorem pressureForceSmoothField_jetLp_continuous (n : ℕ) :
    Continuous (fun t =>
      (pressureForceSmoothField D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF t).jetLp n) :=
  EulerPacketSourceVolumeSobolev.smoothField_jetLp_continuous D (pressureForceTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF n

def pressureForceCoefficientPath : SmoothCoefficientPath (Icc (0 : ℝ) D.T) Space :=
  EulerPacketSourceVolumeSobolev.smoothCoefficientPath D (pressureForceTower D P κ Z)
    k D.m₀ X Y hX hYX hXY hY R C hR hC hdet hF

theorem pressureForceCoefficientPath_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (pressureForceCoefficientPath D P κ Z k X Y hX hYX hXY hY R C hR hC hdet hF).field t x =
      κ • (D.FInv.field t (Y t x)).adjoint
        (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) := by
  rw [pressureForceCoefficientPath, EulerPacketSourceVolumeSobolev.smoothCoefficientPath_apply,
    pressureForceTower_pointField]
  rfl

end EulerPacketPhysicalField
