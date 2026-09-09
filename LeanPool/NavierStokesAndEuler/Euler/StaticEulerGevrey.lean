/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerRegularity
public import LeanPool.NavierStokesAndEuler.Euler.StaticEulerWeightedBounds
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerGraphGevrey
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeAmplitudeBounds

@[expose] public section

/-! Uniform source-only Gevrey bounds for the actual local Euler solution
and its genuine time derivative. The same spatial radius works for sup
and ordinary L² norms. All constants depend only on P,C,R, not on the
particular solenoidal datum realizing the input bounds. -/

noncomputable section

namespace EulerStaticEuler

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLiftedGradientSpace EulerAllOrderCorrectionData EulerAllOrderDriftCorrection
  EulerCylinderCoordinates EulerCylinderSobolevSpace EulerPacketCylinderField
open scoped ContDiff BoundedContinuousFunction

private local instance : NormedAddCommGroup Space := inferInstance
private local instance : NormedSpace ℝ Space := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (Space [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space [×n]→L[ℝ] Space) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] Space)) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] Space)) := inferInstance

def coverRadius (R : ℝ) : ℝ := ‖coordinateEquiv.symm.toContinuousLinearMap‖*(retainedRadius R)⁻¹

def outputRadius (R : ℝ) : ℝ := 1+4*coverRadius R

theorem coverRadius_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ coverRadius R :=
  mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (retainedRadius_pos R hR).le)

theorem outputRadius_pos (R : ℝ) (hR : 0 ≤ R) : 0 < outputRadius R := by
  have h := coverRadius_nonneg R hR
  unfold outputRadius
  positivity

variable (P : ℝ) [Fact (0 < P)]

def graphCost (R : ℝ) : ℝ :=
  1+sobolevEmbeddingConstant P 3+Real.sqrt (2/P+2*P)*(1+coverRadius R)

def outputVelocitySize (C R : ℝ) : ℝ :=
  graphCost P R*(2*mixedAmplitude P C R+baseErrorFactor)

def outputDerivativeSize (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : ℝ :=
  (amplitude P C R hC hR)⁻¹*graphCost P R*staticTimeCost P R

theorem graphCost_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ graphCost P R := by
  have h₁ := sobolevEmbeddingConstant_nonneg P 3
  have h₂ := coverRadius_nonneg R hR
  unfold graphCost
  positivity

theorem outputVelocitySize_nonneg (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ outputVelocitySize P C R :=
  mul_nonneg (graphCost_nonneg P R hR)
    (add_nonneg (mul_nonneg (by norm_num) (mixedAmplitude_nonneg P C R hC hR))
      baseErrorFactor_nonneg)

theorem outputDerivativeSize_nonneg (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ outputDerivativeSize P C R hC hR := by
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (amplitude_pos P C R hC hR).le)
    (graphCost_nonneg P R hR)) (staticTimeCost_nonneg P R hR)

private theorem graphCost_embedding (R : ℝ) (hR : 0 ≤ R) :
    sobolevEmbeddingConstant P 3 ≤ graphCost P R := by
  have h := mul_nonneg (Real.sqrt_nonneg (2/P+2*P))
    (add_nonneg zero_le_one (coverRadius_nonneg R hR))
  unfold graphCost
  linarith

private theorem graphCost_trace (R : ℝ) :
    Real.sqrt (2/P+2*P)*(1+coverRadius R) ≤ graphCost P R := by
  have h := sobolevEmbeddingConstant_nonneg P 3
  unfold graphCost
  linarith

private theorem jet_mono {a b r s : ℝ} (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hab : a ≤ b) (hrs : r ≤ s) (n : ℕ) :
    a*r^n*(n.factorial : ℝ)^2 ≤ b*s^n*(n.factorial : ℝ)^2 :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul hab (pow_le_pow_left₀ hr hrs n) (pow_nonneg hr n) hb) (sq_nonneg _)

variable (u : SmoothL2Field Space) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
  (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x=0)

theorem unitVelocityCoefficient_graph (t : Icc (0 : ℝ) 1) (x : Space) :
    (unitVelocityCoefficient P u C R hC hR hu hdiv).field t x =
      (exactPacket P u C R hC hR hu hdiv).velocity.zeroGraphCoefficient.field t x := by
  rw [unitVelocityCoefficient_apply,FieldTower.zeroGraphCoefficient_apply,FieldTower.zeroGraphField_apply]
  simp only [EulerConstantEuler.velocity,ExactLiftedPacket.rawVelocity,FieldTower.rawField,
    projIcc_of_mem zero_le_one t.property]

theorem unitDerivativeCoefficient_graph (t : Icc (0 : ℝ) 1) (x : Space) :
    (unitDerivativeCoefficient P u C R hC hR hu hdiv).field t x =
      ((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower P).zeroGraphCoefficient.field t
        x := by
  change ((Field.zero P 1).smul (amplitude P C R hC hR)).toSmoothTimeField.field t (x,0)+_=_
  rw [Field.toSmoothTimeField_apply]
  change amplitude P C R hC hR • (0 : Space)+_=_
  rw [smul_zero,zero_add]
  rfl

def localDerivativeField (t : Icc (0 : ℝ) (amplitude P C R hC hR)) : SmoothL2Field Space :=
  SmoothL2Field.mapField (((amplitude P C R hC hR)⁻¹)^2 • ContinuousLinearMap.id ℝ Space)
    (((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower P).zeroGraphField
      (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t))

theorem localDerivativeField_apply (t : Icc (0 : ℝ) (amplitude P C R hC hR)) (x : Space) :
    (localDerivativeField P u C R hC hR hu hdiv t).field x =
      (derivativeCoefficient P u C R hC hR hu hdiv).field t x := by
  let st := EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t
  change ((amplitude P C R hC hR)⁻¹)^2 •
      (((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower P).zeroGraphField st).field x =
    ((amplitude P C R hC hR)⁻¹)^2 •
      (unitDerivativeCoefficient P u C R hC hR hu hdiv).field st x
  have he := unitDerivativeCoefficient_graph P u C R hC hR hu hdiv st x
  rw [FieldTower.zeroGraphCoefficient_apply] at he
  exact congrArg (fun v : Space => ((amplitude P C R hC hR)⁻¹)^2 • v) he.symm

theorem velocityCoefficient_bound (n : ℕ) :
    ‖(velocityCoefficient P u C R hC hR hu hdiv).jet n‖ ≤
      outputVelocitySize P C R*(outputRadius R)^n*(n.factorial : ℝ)^2 := by
  have hV : 0 ≤ 2*mixedAmplitude P C R+baseErrorFactor :=
    add_nonneg (mul_nonneg (by norm_num) (mixedAmplitude_nonneg P C R hC hR)) baseErrorFactor_nonneg
  have he := (amplitude_pos P C R hC hR).le
  have hunit := (exactPacket P u C R hC hR hu hdiv).velocity.zeroGraphCoefficient_bound
    (retainedRadius R) (amplitude P C R hC hR*(2*mixedAmplitude P C R+baseErrorFactor))
    (retainedRadius_pos R hR) (mul_nonneg he hV) (exact_weighted P u C R hC hR hu hdiv) n
  rw [← SmoothTimeField.jet_eq_of_field_eq _ _ (unitVelocityCoefficient_graph P u C R hC hR hu
    hdiv) n] at hunit
  have h := (EulerTimeRescaling.coefficient_jet_norm (amplitude P C R hC hR)
    (amplitude_pos P C R hC hR) (unitVelocityCoefficient P u C R hC hR hu hdiv) n).trans
    (mul_le_mul_of_nonneg_left hunit (inv_nonneg.mpr he))
  have hi : (amplitude P C R hC hR)⁻¹*amplitude P C R hC hR=1 :=
    inv_mul_cancel₀ (amplitude_pos P C R hC hR).ne'
  apply h.trans
  calc
    _ = (sobolevEmbeddingConstant P 3*(2*mixedAmplitude P C R+baseErrorFactor))*
        (coverRadius R)^n*(n.factorial : ℝ)^2 := by
      unfold coverRadius
      calc
        _ = ((amplitude P C R hC hR)⁻¹*amplitude P C R hC hR)*
          ((sobolevEmbeddingConstant P 3*(2*mixedAmplitude P C R+baseErrorFactor))*
            (‖coordinateEquiv.symm.toContinuousLinearMap‖*(retainedRadius R)⁻¹)^n*(n.factorial :
              ℝ)^2) := by ring
        _ = _ := by rw [hi,one_mul]
    _ ≤ _ := jet_mono (outputVelocitySize_nonneg P C R hC hR) (coverRadius_nonneg R hR)
      (mul_le_mul_of_nonneg_right (graphCost_embedding P R hR) hV)
      (by have hc := coverRadius_nonneg R hR; unfold outputRadius; linarith) n

theorem derivativeCoefficient_bound (n : ℕ) :
    ‖(derivativeCoefficient P u C R hC hR hu hdiv).jet n‖ ≤
      outputDerivativeSize P C R hC hR*(outputRadius R)^n*(n.factorial : ℝ)^2 := by
  have he := (amplitude_pos P C R hC hR).le
  have hT := staticTimeCost_nonneg P R hR
  have hunit := ((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower
    P).zeroGraphCoefficient_bound
    (retainedRadius R) (amplitude P C R hC hR*staticTimeCost P R)
    (retainedRadius_pos R hR) (mul_nonneg he hT) (time_weighted P u C R hC hR hu hdiv) n
  rw [← SmoothTimeField.jet_eq_of_field_eq _ _ (unitDerivativeCoefficient_graph P u C R hC hR hu
    hdiv) n] at hunit
  have h := (EulerTimeRescaling.derivativeCoefficient_jet_norm (amplitude P C R hC hR)
    (amplitude_pos P C R hC hR) (unitDerivativeCoefficient P u C R hC hR hu hdiv) n).trans
    (mul_le_mul_of_nonneg_left hunit (sq_nonneg _))
  have hi : (amplitude P C R hC hR)⁻¹*amplitude P C R hC hR=1 :=
    inv_mul_cancel₀ (amplitude_pos P C R hC hR).ne'
  apply h.trans
  calc
    _ = ((amplitude P C R hC hR)⁻¹*sobolevEmbeddingConstant P 3*staticTimeCost P R)*
        (coverRadius R)^n*(n.factorial : ℝ)^2 := by
      unfold coverRadius
      calc
        _ = ((amplitude P C R hC hR)⁻¹*amplitude P C R hC hR)*
          (((amplitude P C R hC hR)⁻¹*sobolevEmbeddingConstant P 3*staticTimeCost P R)*
            (‖coordinateEquiv.symm.toContinuousLinearMap‖*(retainedRadius R)⁻¹)^n*(n.factorial :
              ℝ)^2) := by ring
        _ = _ := by rw [hi,one_mul]
    _ ≤ _ := jet_mono (outputDerivativeSize_nonneg P C R hC hR) (coverRadius_nonneg R hR)
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (graphCost_embedding P R hR) (inv_nonneg.mpr he)) hT)
      (by have hc := coverRadius_nonneg R hR; unfold outputRadius; linarith) n

theorem localField_bound (t : Icc (0 : ℝ) (amplitude P C R hC hR)) :
    (localField P u C R hC hR hu hdiv t).HasJetBound (outputVelocitySize P C R) (outputRadius R) :=
      by
  have hV : 0 ≤ 2*mixedAmplitude P C R+baseErrorFactor :=
    add_nonneg (mul_nonneg (by norm_num) (mixedAmplitude_nonneg P C R hC hR)) baseErrorFactor_nonneg
  have he := (amplitude_pos P C R hC hR).le
  have hunit := (exactPacket P u C R hC hR hu hdiv).velocity.zeroGraphField_bound
    (retainedRadius R) (amplitude P C R hC hR*(2*mixedAmplitude P C R+baseErrorFactor))
    (retainedRadius_pos R hR) (mul_nonneg he hV) (exact_weighted P u C R hC hR hu hdiv)
    (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t)
  have h := EulerTimeRescaling.mapField_hasJetBound (amplitude P C R hC hR)⁻¹
    (inv_nonneg.mpr he) _ _ _ hunit
  have hi : (amplitude P C R hC hR)⁻¹*amplitude P C R hC hR=1 :=
    inv_mul_cancel₀ (amplitude_pos P C R hC hR).ne'
  have ha : (amplitude P C R hC hR)⁻¹*
      (Real.sqrt (2/P+2*P)*(amplitude P C R hC hR*(2*mixedAmplitude P C
        R+baseErrorFactor))*(1+coverRadius R)) =
      (Real.sqrt (2/P+2*P)*(1+coverRadius R))*(2*mixedAmplitude P C R+baseErrorFactor) := by
    calc
      _ = ((amplitude P C R hC hR)⁻¹*amplitude P C R hC hR)*
        ((Real.sqrt (2/P+2*P)*(1+coverRadius R))*(2*mixedAmplitude P C R+baseErrorFactor)) := by
          ring
      _ = _ := by rw [hi,one_mul]
  change (localField P u C R hC hR hu hdiv t).HasJetBound
    ((amplitude P C R hC hR)⁻¹*(Real.sqrt (2/P+2*P)*
      (amplitude P C R hC hR*(2*mixedAmplitude P C R+baseErrorFactor))*(1+coverRadius R)))
    (4*coverRadius R) at h
  rw [ha] at h
  exact h.mono (by have hc := coverRadius_nonneg R hR; positivity)
    (mul_nonneg (by norm_num) (coverRadius_nonneg R hR))
    (mul_le_mul_of_nonneg_right (graphCost_trace P R) hV)
    (by unfold outputRadius; linarith)

theorem localDerivativeField_bound (t : Icc (0 : ℝ) (amplitude P C R hC hR)) :
    (localDerivativeField P u C R hC hR hu hdiv t).HasJetBound
      (outputDerivativeSize P C R hC hR) (outputRadius R) := by
  have he := (amplitude_pos P C R hC hR).le
  have hT := staticTimeCost_nonneg P R hR
  have hunit := ((correctionBudget P u C R hC hR hu hdiv).timeDerivativeTower
    P).zeroGraphField_bound
    (retainedRadius R) (amplitude P C R hC hR*staticTimeCost P R)
    (retainedRadius_pos R hR) (mul_nonneg he hT) (time_weighted P u C R hC hR hu hdiv)
    (EulerTimeRescaling.timeMap (amplitude P C R hC hR) (amplitude_pos P C R hC hR) t)
  have h := EulerTimeRescaling.mapField_hasJetBound (((amplitude P C R hC hR)⁻¹)^2)
    (sq_nonneg _) _ _ _ hunit
  have hi : (amplitude P C R hC hR)⁻¹*amplitude P C R hC hR=1 :=
    inv_mul_cancel₀ (amplitude_pos P C R hC hR).ne'
  have ha : ((amplitude P C R hC hR)⁻¹)^2*
      (Real.sqrt (2/P+2*P)*(amplitude P C R hC hR*staticTimeCost P R)*(1+coverRadius R)) =
      (amplitude P C R hC hR)⁻¹*(Real.sqrt (2/P+2*P)*(1+coverRadius R))*staticTimeCost P R := by
    calc
      _ = ((amplitude P C R hC hR)⁻¹*amplitude P C R hC hR)*
        ((amplitude P C R hC hR)⁻¹*(Real.sqrt (2/P+2*P)*(1+coverRadius R))*staticTimeCost P R) :=
          by ring
      _ = _ := by rw [hi,one_mul]
  change (localDerivativeField P u C R hC hR hu hdiv t).HasJetBound
    (((amplitude P C R hC hR)⁻¹)^2*(Real.sqrt (2/P+2*P)*
      (amplitude P C R hC hR*staticTimeCost P R)*(1+coverRadius R)))
    (4*coverRadius R) at h
  rw [ha] at h
  exact h.mono (by have hc := coverRadius_nonneg R hR; positivity)
    (mul_nonneg (by norm_num) (coverRadius_nonneg R hR))
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (graphCost_trace P R) (inv_nonneg.mpr he)) hT)
    (by unfold outputRadius; linarith)

end EulerStaticEuler
