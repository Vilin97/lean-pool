/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerJetLp
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolev

@[expose] public section

/-! Actual cylinder L² tensor bounds from the finite packet's ordered-word
budgets. The single coordinate conversion affects only the input radius. -/

noncomputable section


namespace EulerPacketCylinderField.Field

open Set MeasureTheory Finset EulerLiftedGradientSpace EulerMetricTransport
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerCylinderJetLp
  EulerCylinderCoordinates EulerJetProductBounds EulerH6Pressure
  EulerPacketProfileRecursion EulerGevrey

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}
  {G : Field P T raw} {q : ℕ} {R A : ℝ}

theorem WordBound.coverTensor_bound (hG : G.WordBound q R A 0)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    (eLpNorm (tensor P (G.toFieldTower.pointField t) n) 2 (liftMeasure P)).toReal ≤
      A * (‖coordinateEquiv.symm.toContinuousLinearMap‖*R)^n * (n.factorial : ℝ)^2 := by
  let J := toJet P (G.toFieldTower.realization (n+q) t)
  have hl : levelNorm P J n ≤ blockNorm P J q n := by
    have h := single_le_sum (s := range (q+1)) (f := fun r => levelNorm P J (n+r))
      (fun r _ => levelNorm_nonneg J) (show 0 ∈ range (q+1) by simp)
    simpa only [blockNorm, Nat.add_zero] using h
  have hb : levelNorm P J n ≤ A*majorant R 0 n :=
    hl.trans ((G.toFieldTower_blockNorm_le (n+q) q n le_rfl t).trans (hG n))
  apply (G.toFieldTower.coverTensor_norm_le_level (n+q) n (by omega) t).trans
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg _) n)).trans_eq
  simp only [majorant, Nat.add_zero, mul_pow]
  ring

end EulerPacketCylinderField.Field
