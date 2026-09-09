/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.FlowL2Transport
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCorrectionCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalContinuity

/-! Reconstruction W=κFz is a genuine all-order field tower. Its graph
restriction and its actual inverse-flow pullback are continuous spatial L²
paths, with no independent integrability assumption on the perturbation. -/

@[expose] public section


noncomputable section

namespace EulerPacketPhysicalField

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace
  EulerAllOrderCorrectionData EulerPacketCorrectionCoefficients
  EulerCylinderPhysicalTensor EulerGraphPressurePotential EulerFlowL2Transport

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (κ : ℝ) (Z : FieldTower P D.T)

/-- Reconstructed tower, given by `(Z.multiply ((frameCoefficient D).toCoefficientTower P)).smul
κ`. -/
def reconstructedTower : FieldTower P D.T :=
  (Z.multiply ((frameCoefficient D).toCoefficientTower P)).smul κ

theorem reconstructedTower_pointField (t : Icc (0 : ℝ) D.T) (x : LiftDomain P) :
    (reconstructedTower D P κ Z).pointField t x =
      κ • D.F.field t x.1 (Z.pointField t x) := by
  rw [reconstructedTower,FieldTower.smul_pointField,FieldTower.multiply_pointField]
  rfl

/-- Graph path, given by `(reconstructedTower D P κ Z).canonicalGraphWordPath (physicalPhase P k
D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0`. -/
def graphPath (k : ℝ) : C(Icc (0 : ℝ) D.T,Lp Space 2 (volume : Measure Space)) :=
  (reconstructedTower D P κ Z).canonicalGraphWordPath
    (physicalPhase P k D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0

theorem graphPath_ae (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    (graphPath D P κ Z k t : Space → Space) =ᵐ[volume]
      fun x => κ • D.F.field t x (Z.pointField t (cylinderGraph P k D.m₀ x)) := by
  have h := (reconstructedTower D P κ Z).canonicalGraphWordPath_ae
    (physicalPhase P k D.m₀) (physicalPhase_continuous P k D.m₀) 0 Fin.elim0 t
  simpa only [graphPath,EulerCylinderSobolev.iteratedFieldDerivative_zero,
    reconstructedTower_pointField,physicalPhase,cylinderGraph] using h

/-- Graph tensor path, given by `(reconstructedTower D P κ Z).physicalTensorPath k D.m₀ n`. -/
def graphTensorPath (k : ℝ) (n : ℕ) :
    C(Icc (0 : ℝ) D.T,Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space)) :=
  (reconstructedTower D P κ Z).physicalTensorPath k D.m₀ n

theorem graphTensorPath_ae (k : ℝ) (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    (graphTensorPath D P κ Z k n t : Space → (Space [×n]→L[ℝ] Space)) =ᵐ[volume]
      iteratedFDeriv ℝ n
        (fun x => κ • D.F.field t x (Z.pointField t (cylinderGraph P k D.m₀ x))) := by
  have h := (reconstructedTower D P κ Z).physicalTensorPath_ae k D.m₀ n t
  have he : (reconstructedTower D P κ Z).physicalPointField k D.m₀ t =
      fun x => κ • D.F.field t x (Z.pointField t (cylinderGraph P k D.m₀ x)) :=
    funext (fun x => reconstructedTower_pointField D P κ Z t (cylinderGraph P k D.m₀ x))
  rw [he] at h
  exact h

variable (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hY : Continuous (Function.uncurry Y))
  (hdet : ∀ t x, (D.F.field t x).det = 1)

/-- Eulerian path, given by `transportPath X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet
(graphPath D P κ Z k)`. -/
def eulerianPath (k : ℝ) : C(Icc (0 : ℝ) D.T,Lp Space 2 (volume : Measure Space)) :=
  transportPath X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet (graphPath D P κ Z k)

theorem eulerianPath_ae (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    (eulerianPath D P κ Z X Y hX hYX hXY hY hdet k t : Space → Space) =ᵐ[volume]
      fun x => κ • D.F.field t (Y t x)
        (Z.pointField t (cylinderGraph P k D.m₀ (Y t x))) :=
  transportPath_ae X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet
    (graphPath D P κ Z k) _ (graphPath_ae D P κ Z k) t

theorem eulerianPath_norm (k : ℝ) (t : Icc (0 : ℝ) D.T) :
    ‖eulerianPath D P κ Z X Y hX hYX hXY hY hdet k t‖ = ‖graphPath D P κ Z k t‖ :=
  transportPath_norm X Y (fun t x => D.F.field t x) hX hYX hXY hY hdet (graphPath D P κ Z k) t

end EulerPacketPhysicalField
