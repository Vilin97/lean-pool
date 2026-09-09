/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerVolumeSobolev
public import LeanPool.NavierStokesAndEuler.Euler.PacketInverseFlowSobolevBound
public import LeanPool.NavierStokesAndEuler.Euler.PacketContinuousInverse
public import LeanPool.NavierStokesAndEuler.Euler.FlowL2Transport
import LeanPool.NavierStokesAndEuler.Euler.PacketVolumeDivergence

/-! Spatial Sobolev paths for the actual inverse parent flow. Its
measure preservation, smoothness, derivative bounds and jet continuity
are all derived from the source deformation and inverse identities. -/

@[expose] public section


noncomputable section

namespace EulerPacketSourceVolumeSobolev

open Set MeasureTheory EulerSmoothLimit EulerAllOrderCorrectionData
  EulerFlowL2Transport EulerPacketInverseFlowGevrey EulerPacketPiola
  EulerCylinderPhysicalTensor EulerGraphPressurePotential EulerGevrey
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
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C * majorant R 0 n)

include hX hYX hXY hYjoint hdet in
theorem inversePath_volume (t : Icc (0 : ℝ) D.T) :
    MeasurePreserving (inversePath Y hYjoint t) volume volume := by
  apply inversePath_measurePreserving X Y (fun s x => D.F.field s x) hX hYX hXY hYjoint
  intro s x
  rw [← EulerPacketVolumeDivergence.operatorMatrix_det]
  exact hdet s x

/-- Tensor path, constructed using `Z.volumeTensorPath`. -/
def tensorPath (n : ℕ) :
    C(Icc (0 : ℝ) D.T,Lp (Space [×n]→L[ℝ] Space) 2 (volume : Measure Space)) :=
  Z.volumeTensorPath k m (inversePath Y hYjoint)
    (inversePath_volume D X Y hX hYX hXY hYjoint hdet) n
    (finiteOrderConstant C R n) (zero_le_one.trans (finiteOrderConstant_one_le C R hR n))
    (fun i _ _ => continuousInverse_jet_continuous D X Y hX hXY hYjoint i)
    (fun i hi hin => inverseFlow_finiteOrderBound D X Y hX
      (continuousInverse_differentiable D X Y hX hXY hYjoint) hXY R C hR hC hdet hF n i hi hin)

theorem tensorPath_ae (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    (tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t :
      Space → (Space [×n]→L[ℝ] Space)) =ᵐ[volume]
      iteratedFDeriv ℝ n (fun x => Z.pointField t (cylinderGraph P k m (Y t x))) :=
  Z.volumeTensorPath_ae k m (inversePath Y hYjoint)
    (inversePath_volume D X Y hX hYX hXY hYjoint hdet) n
    (finiteOrderConstant C R n) (zero_le_one.trans (finiteOrderConstant_one_le C R hR n))
    (fun i _ _ => continuousInverse_jet_continuous D X Y hX hXY hYjoint i)
    (fun i hi hin => inverseFlow_finiteOrderBound D X Y hX
      (continuousInverse_differentiable D X Y hX hXY hYjoint) hXY R C hR hC hdet hF n i hi hin)
    (continuousInverse_contDiff D X Y hX hXY hYjoint) t

theorem tensorPath_norm_le (n : ℕ) (t : Icc (0 : ℝ) D.T) :
    ‖tensorPath D Z k m X Y hX hYX hXY hYjoint R C hR hC hdet hF n t‖ ≤
      ((n.factorial : ℝ)*(finiteOrderConstant C R n)^n)*∑ i : Fin (n+1),
        frequencyFactor k m^i.val*(4 : ℝ)^i.val*Real.sqrt (2/P+2*P)*‖Z.realization (i.val+1) t‖ :=
  Z.volumeTensorPath_norm_le k m (inversePath Y hYjoint)
    (inversePath_volume D X Y hX hYX hXY hYjoint hdet) n
    (finiteOrderConstant C R n) (zero_le_one.trans (finiteOrderConstant_one_le C R hR n))
    (fun i _ _ => continuousInverse_jet_continuous D X Y hX hXY hYjoint i)
    (fun i hi hin => inverseFlow_finiteOrderBound D X Y hX
      (continuousInverse_differentiable D X Y hX hXY hYjoint) hXY R C hR hC hdet hF n i hi hin)
    (continuousInverse_contDiff D X Y hX hXY hYjoint) t

end EulerPacketSourceVolumeSobolev
