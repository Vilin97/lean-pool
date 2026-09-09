/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceVolumeSobolev
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2CoefficientPath

@[expose] public section

/-! The actual source-flow pullback is a smooth spatial L² field at
every time. Its tensor paths also give a bounded smooth coefficient
path, with continuity in the uniform norm at every spatial order. -/

noncomputable section

namespace EulerPacketSourceVolumeSobolev

open Set MeasureTheory EulerSmoothLimit EulerAllOrderCorrectionData
  EulerFlowL2Transport EulerPacketInverseFlowGevrey EulerPacketPiola
  EulerCylinderPhysicalTensor EulerGraphPressurePotential EulerGevrey
  EulerLpTranslation EulerMeanCoefficients
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) {P : ℝ} [Fact (0 < P)]
  (Z : FieldTower P D.T) (k : ℝ) (m : Space)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hYX : ∀ t, Function.LeftInverse (Y t) (X t))
  (hXY : ∀ t, Function.RightInverse (Y t) (X t))
  (hYjoint : Continuous (Function.uncurry Y))
  (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det=1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C*majorant R 0 n)

def smoothField (t : Icc (0 : ℝ) D.T) : SmoothL2Field Space where
  field x := Z.pointField t (cylinderGraph P k m (Y t x))
  smooth := (Z.physicalPointField_smooth k m t).comp
    (continuousInverse_contDiff D X Y hX hXY hYjoint t)
  integrable n :=
    (Lp.memLp (tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t)).ae_eq
      (tensorPath_ae D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t)

theorem smoothField_jetLp (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    (smoothField D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF t).jetLp n =
      tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t := by
  apply Lp.ext
  exact (SmoothL2Field.jetLp_ae _ n).trans
    (tensorPath_ae D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t).symm

theorem smoothField_jetLp_continuous (n : ℕ) :
    Continuous (fun t => (smoothField D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF t).jetLp n)
      := by
  simp only [smoothField_jetLp]
  exact (tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n).continuous

def smoothCoefficientPath : SmoothCoefficientPath (Icc (0 : ℝ) D.T) Space :=
  EulerMeanSobolevBoundedField.coefficientPath
    (smoothField D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF)
    (smoothField_jetLp_continuous D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF)

theorem smoothCoefficientPath_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    (smoothCoefficientPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF).field t x =
      Z.pointField t (cylinderGraph P k m (Y t x)) :=
  EulerMeanSobolevBoundedField.coefficientPath_apply _ _ t x

end EulerPacketSourceVolumeSobolev
