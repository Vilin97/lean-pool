/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteRemainderBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderTermBudget
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteProfileFields
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileBudget
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketExponentialTail
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFrequencyBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteProfileBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketTailNormalization
import Mathlib.Algebra.Order.Star.Real

/-! The literal packet differs from its primary wave by a quadratic-frequency remainder. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.ProfileRegularity

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerFiniteGrades EulerPacketCoarseMajorant EulerPacketFiniteFrequency

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))

theorem assembledVelocity_one (hN : 1 ≤ N) (ha : a 0 = 0) (hb : (a 1).mean = 0) :
    assembledVelocity N a 1=(a 1).high := by
  rw [assembledVelocity,assemble_interior N 1 le_rfl hN]
  simp only [Nat.sub_self,hb,ha]
  change (a 1).high+0+0=(a 1).high
  simp only [add_zero]

/-- Primary remainder field as an element of `Field P T (fieldSum (N+1) κ (assembledVelocity N
a)-κ • (a 1).high)`. -/
def primaryRemainderField (hN : 1 ≤ N) (ha : a 0 = 0) (hb : (a 1).mean = 0) (κ : ℝ) :
    Field P T (fieldSum (N+1) κ (assembledVelocity N a)-κ • (a 1).high) :=
  (Field.evaluateRemainder (N+1) (by
      omega) κ (assembledVelocity N a) (velocityGradeField hT G)).congr
    (fun _ _ _ => by rw [assembledVelocity_one hN ha hb])

variable {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0 = 0) (hb : (a 1).mean = 0) (hN : 1 ≤ N)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)

include hG hR

theorem primaryRemainder_bound (k : ℝ) (hk : 4 ≤ k)
    (hbase : tailBase R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    (primaryRemainderField hT G hN ha hb k⁻¹).WordBound 6 (4*R)
      ((fixedVelocityGradeCost R S.H0 2+2)/k^2) 0 := by
  have hk0 : 0 < k := by linarith
  let B := tailBase R S.H0 BC.termCost N
  have hB : 0 ≤ B := tailBase_nonneg R S.H0 BC.termCost BC.termCost_nonneg N
  have hsmall : k⁻¹*B ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using EulerPacketTailBound.grade_ratio_le_half k B hk hbase
  have hf : (a 0).high+(a 0).mean=0 := by
    rw [ha]
    change (0 : VectorField)+0=0
    exact zero_add 0
  have hz : assembledVelocity N a 0=0 := assemble_zero N _ _ hf
  have h := Field.wordBound_evaluateRemainder N hN k⁻¹ B (fixedVelocityGradeCost R S.H0 2)
    (inv_nonneg.mpr hk0.le) hB hsmall (assembledVelocity N a) (velocityGradeField hT G) 6 (4*R)
    (by linarith) (fun _ _ _ => by rw [hz]; rfl)
    ((velocityGrade_bound hT G hG hR ha 2).fixed_velocity_grade (zero_le_one.trans hR) S.H0_pos.le)
    (fun n _ hn => (velocityGrade_bound hT G hG hR ha n).coarse_velocity_grade
      hR S.H0_one_le BC.termCost BC.one_le_termCost N hN (by omega))
  exact (h.mono_amplitude (by linarith)
    (remainder_low_high_le k B (fixedVelocityGradeCost R S.H0 2) hk0
      (fourth_power_le_frequency k B (by linarith) hB hbase))).of_path_eq _ rfl

theorem normalizedRemainder_bound (hRc : EulerParameterWordGevrey.sobolevCoefficientRadius (Fin 4)
    BC.Rc ≤ R)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase R S.H0 BC.termCost N ≤ k ^ (1 / 100 : ℝ)) :
    ((C.inverse.multiply (primaryRemainderField hT G hN ha hb k⁻¹)).smul k).WordBound 6 (4*R)
      (BC.multiplierCost*(fixedVelocityGradeCost R S.H0 2+2)/k) 0 := by
  have hk0 : 0 < k := by linarith
  have hA : 0 ≤ (fixedVelocityGradeCost R S.H0 2+2)/k^2 :=
    div_nonneg (by have := fixedVelocityGradeCost_nonneg R S.H0 (zero_le_one.trans hR) 2; linarith)
      (sq_nonneg k)
  have h := BC.normalized_inverse_bound (primaryRemainderField hT G hN ha hb k⁻¹)
    (primaryRemainder_bound hT G hG hR ha hb hN BC k hk hbase) hA
    (hRc.trans (by linarith)) k hk0.le
  have he : k*BC.multiplierCost*((fixedVelocityGradeCost R S.H0 2+2)/k^2) =
      BC.multiplierCost*(fixedVelocityGradeCost R S.H0 2+2)/k := by field_simp
  simpa only [he] using h

end EulerPacketCylinderField.ProfileRegularity
