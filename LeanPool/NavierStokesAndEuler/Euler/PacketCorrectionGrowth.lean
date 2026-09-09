/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionMetricBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketCorrectionCoefficientBudget
public import LeanPool.NavierStokesAndEuler.Euler.NonlinearEnergyConstants

/-! The exact nonlinear energy constant is a fixed source quantity,
independent of the Sobolev order, truncation and oscillation frequency. -/

@[expose] public section


noncomputable section

namespace EulerPacketCorrectionCoefficients

open EulerPacketCylinderField EulerAllOrderCorrectionData EulerCorrectionEnergyData
  EulerNonlinearEnergyConstants EulerGevreyGrowthCoefficient EulerGevreyMetricEstimate
   EulerLiftedGradientSpace EulerCylinderSobolevSpace

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U) (P : ℝ) [Fact (0 < P)]
  (Kc : CorrectionCoefficientBudget D P)

/-- Growth coefficient as an element of `ℝ`. -/
def growthCoefficient (B0 B1 : ℝ) : ℝ :=
  let c := D.inverseBound⁻¹
  let first := inverseMetricFirstBound D
  energyConstant P
    (growthBudgetBase c (inverseMetricTimeBound D) first +
      growthBudgetSlope c first*sobolevEmbeddingConstant P 6*B0)
    (growthBudgetSlope c first*sobolevEmbeddingConstant P 6*metricAmplification c)
    (inverseMetricBound D/c) Kc.B Kc.M B0 B1 Kc.A0 Kc.A2 c

theorem growthCoefficient_eq (B0 B1 κ : ℝ) (hκ : |κ| ≤ 1)
    (Z G : FieldTower P D.T) (q : ℕ) :
    growthCoefficient D P Kc B0 B1 =
      energyConstant P ((sourceMetricBudget D P κ hκ Z G q).growth0 P B0)
        ((sourceMetricBudget D P κ hκ Z G q).growth1 P)
        ((sourceMetricBudget D P κ hκ Z G q).multiplier P)
        Kc.B Kc.M B0 B1 Kc.A0 Kc.A2 (sourceMetricBudget D P κ hκ Z G q).c := rfl

theorem growthCoefficient_pos (B0 B1 : ℝ) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) :
    0 < growthCoefficient D P Kc B0 B1 := by
  let Z := (Field.zero P D.T).toFieldTower
  let K := sourceMetricBudget D P 0 (by norm_num) Z Z 0
  obtain ⟨h0,h1,hk⟩ := K.constants_nonneg P B0 hB0
  rw [growthCoefficient_eq D P Kc B0 B1 0 (by norm_num) Z Z 0]
  exact energyConstant_pos P _ _ _ _ _ _ _ _ _ _ h0 h1 hk Kc.B_nonneg
    (zero_le_one.trans Kc.M_one_le) hB0 hB1 Kc.A0_nonneg Kc.A2_nonneg K.c_pos

end EulerPacketCorrectionCoefficients
