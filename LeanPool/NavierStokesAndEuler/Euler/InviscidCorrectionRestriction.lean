/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
import LeanPool.NavierStokesAndEuler.Euler.CorrectionSourceRestriction

/-! Actual inviscid corrections agree across compatible Sobolev levels. -/

@[expose] public section


noncomputable section

namespace EulerInviscidCorrectionRestriction

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionSourceRestriction EulerQuadraticSource EulerVolterraConvolution


variable (period : ℝ) [Fact (0 < period)]

/-- The literal inviscid equation is preserved by lowering the actual Sobolev order. -/
theorem inviscid_equation_restrict {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period ((q + 1) + 1)))
    (hu : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => value period (extendPath T hT u r))
        (value period ((D.coefficients period (by omega : 6 ≤ q + 1)).apply
          ⟨t, ht.1.le, ht.2.le⟩ (u ⟨t, ht.1.le, ht.2.le⟩))) t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => value period (extendPath T hT
      ((truncateOperator period (q+1)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u) r))
      (value period (((lowerData period D KG KL KQ hG hL hQ).coefficients period hq).apply
        ⟨t,ht.1.le,ht.2.le⟩ (truncateOperator period (q+1) (u ⟨t,ht.1.le,ht.2.le⟩)))) t := by
  have hs := congrArg (value period (q := q))
    (truncate_source period hq D KG KL KQ hG hL hQ ⟨t,ht.1.le,ht.2.le⟩ (u ⟨t,ht.1.le,ht.2.le⟩))
  rw [value_truncateOperator] at hs
  exact (hu t ht).congr_deriv hs

end EulerInviscidCorrectionRestriction
