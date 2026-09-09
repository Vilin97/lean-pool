/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.StaticCylinderField
public import LeanPool.NavierStokesAndEuler.Euler.SmallCorrectionBudget
public import LeanPool.NavierStokesAndEuler.Euler.SmallCorrectionResidual

@[expose] public section

/-! An actual exact lifted Euler solution is constructed from any genuine
smooth solenoidal L² datum with factorial derivative bounds. The amplitude
is an explicit function of the supplied bounds and does not depend on the
particular datum realizing them. -/

noncomputable section

namespace EulerStaticEuler

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerParameterWordGevrey
  EulerPacketCylinderField EulerAllOrderDriftCorrection EulerSmallCorrection EulerLpTranslation

variable (P : ℝ) [Fact (0 < P)]

def mixedRadius (R : ℝ) : ℝ := sobolevCoefficientRadius (Fin 4) R
def mixedAmplitude (C R : ℝ) : ℝ := Real.sqrt P*sobolevCoefficientAmplitude (Fin 4) 6 R C

theorem mixedRadius_nonneg (R : ℝ) (hR : 0 ≤ R) : 0 ≤ mixedRadius R :=
  sobolevCoefficientRadius_nonneg (ι := Fin 4) R hR

omit [Fact (0 < P)] in
theorem mixedAmplitude_nonneg (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : 0 ≤ mixedAmplitude P C R :=
  mul_nonneg (Real.sqrt_nonneg P) (sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 R C hR hC)

def scales (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    Scale P (mixedAmplitude P C R) (mixedRadius R)
      (residualCost P (mixedAmplitude P C R) (mixedRadius R)) :=
  scale P _ _ _ (mixedAmplitude_nonneg P C R hC hR) (mixedRadius_nonneg R hR)
    (residualCost_pos P _ _ (mixedRadius_nonneg R hR))

def amplitude (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : ℝ := (scales P C R hC hR).value

theorem amplitude_pos (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : 0 < amplitude P C R hC hR :=
  (scales P C R hC hR).positive

theorem amplitude_le_one (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) : amplitude P C R hC hR ≤ 1 :=
  (scales P C R hC hR).one

variable (u : SmoothL2Field Space) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
  (hu : u.HasJetBound C R) (hdiv : ∀ x, divergence u.field x=0)

def inputData := input (EulerStaticCylinder.field P 1 u) (amplitude P C R hC hR)

def correctionBudget :
    Budget P (by norm_num : (0 : ℝ) < 1) (inputData P u C R hC hR) :=
  budget (EulerStaticCylinder.field P 1 u) (EulerStaticCylinder.field_wordBound P 1 u 6 C R hC hR
    hu)
    (mixedAmplitude_nonneg P C R hC hR) (mixedRadius_nonneg R hR) (scales P C R hC hR)
    (EulerStaticCylinder.field_divergence P 1 u 1 0 hdiv)

def exactPacket : ExactLiftedPacket P (by norm_num : (0 : ℝ) < 1)
    (inputData P u C R hC hR) (correctionBudget P u C R hC hR hu hdiv) :=
  exactPacketOfResidual P (correctionBudget P u C R hC hR hu hdiv)
    (approximationResidual (EulerStaticCylinder.field P 1 u) (by norm_num)
      (amplitude P C R hC hR) (EulerStaticCylinder.field_time P 1 u (by norm_num)))

theorem exactPacket_initial (q : ℕ) :
    (exactPacket P u C R hC hR hu hdiv).velocity.realization q ⟨0,le_rfl,by norm_num⟩ =
      ((EulerStaticCylinder.field P 1 u).smul (amplitude P C R hC hR)).toFieldTower.realization q
        ⟨0,le_rfl,by norm_num⟩ :=
  sub_eq_zero.mp ((exactPacket P u C R hC hR hu hdiv).zero_initial_correction q)

end EulerStaticEuler
