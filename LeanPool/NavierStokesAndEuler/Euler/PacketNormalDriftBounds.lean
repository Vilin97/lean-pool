/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketRemainderBounds

@[expose] public section

/-! The transported primary has zero normal component, so the actual normal drift is small. -/

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion EulerPacketTimeProfile
  EulerPacketCoarseMajorant EulerParameterWordGevrey

theorem normalComponentMap_norm_le (m : Space) : ‖normalComponentMap m‖ ≤ ‖m‖ :=
  (normalComponentMap.le_opNorm m).trans
    ((mul_le_mul_of_nonneg_right normalComponentMap_norm (norm_nonneg m)).trans_eq (one_mul _))

namespace ProfileRegularity

variable {P T : ℝ} [Fact (0 < P)] {N : ℕ} {a : ℕ → Profile} {support : Set Space}
  (hT : 0 < T) (G : ∀ i, i ≤ N → ProfileRegularity P T hT.le support (a i))
  {S : Scales (Icc (0 : ℝ) T)} {R : ℝ}
  (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0=0) (hb : (a 1).mean=0) (hN : 1 ≤ N)
  {O : Operators} {C : CoefficientData P T O} (BC : CoefficientBudget C)
  (hRc : sobolevCoefficientRadius (Fin 4) BC.Rc ≤ R)

include hG hR ha hb hN hRc

theorem normalizedNormal_bound (m : Space) (hm : ‖m‖ ≤ 1)
    (htan : ∀ (t : Icc (0 : ℝ) T) x θ,
      inner ℝ m (O.inverseFrame (t,(x,θ)) ((a 1).high (t,(x,θ))))=0)
    (k : ℝ) (hk : 4 ≤ k) (hbase : tailBase R S.H0 BC.termCost N ≤ k^(1/100 : ℝ)) :
    (((C.inverse.multiply (velocityField hT G k⁻¹)).smul k).map (normalComponentMap m)).WordBound
      6 (4*R) (BC.multiplierCost*(fixedVelocityGradeCost R S.H0 2+2)/k) 0 := by
  have hk0 : 0 < k := by linarith
  have hA : 0 ≤ BC.multiplierCost*(fixedVelocityGradeCost R S.H0 2+2)/k :=
    div_nonneg (mul_nonneg BC.multiplierCost_nonneg
      (by have := fixedVelocityGradeCost_nonneg R S.H0 (zero_le_one.trans hR) 2; linarith)) hk0.le
  have hE := (normalizedRemainder_bound hT G hG hR ha hb hN BC hRc k hk hbase).map
    (normalComponentMap m)
  have hE' := hE.mono_amplitude (by linarith : 0 ≤ 4*R)
    ((mul_le_mul_of_nonneg_right ((normalComponentMap_norm_le m).trans hm) hA).trans_eq (one_mul _))
  apply hE'.of_raw_eq (((C.inverse.multiply (velocityField hT G k⁻¹)).smul k).map
    (normalComponentMap m))
  intro t x θ
  have hz : normalComponentMap m (O.inverseFrame (t,(x,θ)) ((a 1).high (t,(x,θ))))=0 := by
    rw [normalComponentMap_apply,htan t x θ]
    exact map_zero _
  change normalComponentMap m (k • O.inverseFrame (t,(x,θ))
      (fieldSum (N+1) k⁻¹ (assembledVelocity N a) (t,(x,θ)))) =
    normalComponentMap m (k • O.inverseFrame (t,(x,θ))
      (fieldSum (N+1) k⁻¹ (assembledVelocity N a) (t,(x,θ))-k⁻¹ • (a 1).high (t,(x,θ))))
  simp only [map_smul,map_sub,hz,smul_zero,sub_zero]

end ProfileRegularity
end EulerPacketCylinderField
