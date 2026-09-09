/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.InviscidCorrectionRestriction
public import LeanPool.NavierStokesAndEuler.Euler.InviscidCorrectionUniqueness

@[expose] public section

/-! Actual inviscid corrections agree across compatible Sobolev levels. -/

noncomputable section

namespace EulerInviscidCorrectionCompatibility

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
    EulerCorrectionLowerData
  EulerCorrectionSourceRestriction EulerQuadraticSource EulerVolterraConvolution
  EulerCorrectionStabilityBudget EulerInviscidCorrectionUniqueness

variable (period : ℝ) [Fact (0 < period)]

/-- Actual inviscid corrections constructed at neighboring Sobolev orders coincide after restriction. -/
theorem inviscid_corrections_compatible {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (u : C(Icc (0 : ℝ) T,SobolevSpace period ((q+1)+1)))
    (hu : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT u r))
        (value period ((D.coefficients period (by omega : 6 ≤ q+1)).apply
          ⟨t,ht.1.le,ht.2.le⟩ (u ⟨t,ht.1.le,ht.2.le⟩))) t)
    (B : StabilityBudget period hT (lowerData period D KG KL KQ hG hL hQ))
    (v : C(Icc (0 : ℝ) T,SobolevSpace period (q+1)))
    (hv : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT v r))
        (value period (((lowerData period D KG KL KQ hG hL hQ).coefficients period hq).apply
          ⟨t,ht.1.le,ht.2.le⟩ (v ⟨t,ht.1.le,ht.2.le⟩))) t)
    (hi : truncateOperator period (q+1) (u ⟨0,le_rfl,hT⟩) = v ⟨0,le_rfl,hT⟩)
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hud : ∀ t, value period (u t) ∈ divergenceFreeSpace period D.κ D.direction)
    (hvd : ∀ t, value period (v t) ∈ divergenceFreeSpace period D.κ D.direction) :
    (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u = v := by
  let w := (truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u
  apply inviscid_correction_unique period hq T hT (lowerData period D KG KL KQ hG hL hQ) B w v hi
  · exact EulerInviscidCorrectionRestriction.inviscid_equation_restrict period hq T hT D KG KL KQ
    hG hL hQ u hu
  · exact hv
  · exact hz
  · exact hud
  · exact hvd

end EulerInviscidCorrectionCompatibility
