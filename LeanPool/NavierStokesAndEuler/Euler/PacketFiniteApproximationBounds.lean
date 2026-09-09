/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteProfileFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteProfileBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteSumBounds

/-! Quantitative bounds for the literal finite approximate velocity and its time derivative. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.ProfileRegularity

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerFiniteGrades EulerPacketCoarseMajorant

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0 = 0) (hN : 1 ≤ N) (C : ℝ) (hC : 1 ≤ C)

include hG hR ha hN hC

theorem velocity_bound (κ : ℝ) (hκ : 0 ≤ κ)
    (hsmall : κ * tailBase R S.H0 C N ≤ 1 / 2) :
    (velocityField hT G κ).WordBound 6 (4*R)
      (κ*fixedVelocityGradeCost R S.H0 1+κ^2*fixedVelocityGradeCost R S.H0 2 +
        2*tailBase R S.H0 C N*(κ*tailBase R S.H0 C N)^3) 0 := by
  have hf : (a 0).high+(a 0).mean=0 := by
    rw [ha]
    change (0 : VectorField)+0=0
    exact zero_add 0
  have hz : assembledVelocity N a 0=0 := assemble_zero N _ _ hf
  exact Field.wordBound_evaluate_low_high N hN κ (tailBase R S.H0 C N)
    (fixedVelocityGradeCost R S.H0 1) (fixedVelocityGradeCost R S.H0 2) hκ
    (tailBase_nonneg R S.H0 C (zero_le_one.trans hC) N) hsmall
    (assembledVelocity N a) (velocityGradeField hT G) 6 (4*R) (by linarith)
    (fun _ _ _ => by rw [hz]; rfl)
    ((velocityGrade_bound hT G hG hR ha 1).fixed_velocity_grade (zero_le_one.trans hR) S.H0_pos.le)
    ((velocityGrade_bound hT G hG hR ha 2).fixed_velocity_grade (zero_le_one.trans hR) S.H0_pos.le)
    (fun n _ hn => (velocityGrade_bound hT G hG hR ha n).coarse_velocity_grade
      hR S.H0_one_le C hC N hN (by omega))

theorem velocityDerivative_bound (κ : ℝ) (hκ : 0 ≤ κ)
    (hsmall : κ * tailBase R S.H0 C N ≤ 1 / 2) :
    (velocityDerivativeField hT G κ).WordBound 6 (4*R)
      (κ*fixedVelocityGradeCost R S.H0 1+κ^2*fixedVelocityGradeCost R S.H0 2 +
        2*tailBase R S.H0 C N*(κ*tailBase R S.H0 C N)^3) 0 := by
  have hf : (a 0).high+(a 0).mean=0 := by
    rw [ha]
    change (0 : VectorField)+0=0
    exact zero_add 0
  have hf' : rawTimeDerivative T ((a 0).high+(a 0).mean)=0 := by
    rw [hf,rawTimeDerivative_zero]
  have hz : velocityTimeCoefficients (T := T) (N := N) (a := a) 0=0 := assemble_zero N _ _ hf'
  exact Field.wordBound_evaluate_low_high N hN κ (tailBase R S.H0 C N)
    (fixedVelocityGradeCost R S.H0 1) (fixedVelocityGradeCost R S.H0 2) hκ
    (tailBase_nonneg R S.H0 C (zero_le_one.trans hC) N) hsmall
    (velocityTimeCoefficients (T := T) (N := N) (a := a)) (velocityGradeDerivativeField hT G)
    6 (4*R) (by linarith) (fun _ _ _ => by rw [hz]; rfl)
    ((velocityGradeDerivative_bound hT G hG hR ha 1).fixed_velocity_grade (zero_le_one.trans hR)
        S.H0_pos.le)
    ((velocityGradeDerivative_bound hT G hG hR ha 2).fixed_velocity_grade (zero_le_one.trans hR)
        S.H0_pos.le)
    (fun n _ hn => (velocityGradeDerivative_bound hT G hG hR ha n).coarse_velocity_grade
      hR S.H0_one_le C hC N hN (by omega))

end EulerPacketCylinderField.ProfileRegularity
