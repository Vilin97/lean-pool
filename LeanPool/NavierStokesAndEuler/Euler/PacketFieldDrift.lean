/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldTower
public import LeanPool.NavierStokesAndEuler.Euler.SobolevDriftNorm
import LeanPool.NavierStokesAndEuler.Euler.LiftedVelocitySplit
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldMap
import LeanPool.NavierStokesAndEuler.Euler.PacketFieldSobolevBudget

/-! The actual small drift budget from the packet's spatial and normal
word bounds, with the same radius and no full-velocity substitution. -/

@[expose] public section


noncomputable section

namespace EulerPacketCylinderField.Field

open Set Finset EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSobolevDriftNorm EulerSobolevTransport EulerFunctionalVelocity
  EulerLiftedVelocitySplit EulerPacketProfileRecursion EulerPacketWeights
  EulerSobolevGevreyOperators EulerJetProductBounds EulerH6Pressure

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField}

theorem toFieldTower_driftLevel_le (G : Field P T raw) (κ : ℝ) (m : Space)
    (s n : ℕ) (hn : n ≤ s) (t : Icc (0 : ℝ) T) :
    driftLevelNorm P n (velocityMap (velocityComponents κ m)) (G.toFieldTower.realization s t) ≤
      3 * |κ| * levelNorm P (toJet P (G.toFieldTower.realization s t)) n +
        levelNorm P (toJet P ((G.map (normalComponentMap m)).toFieldTower.realization s t)) n := by
  rw [levelNorm_eq_words,levelNorm_eq_words,mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro w _
  rw [G.toFieldTower_word_map (normalComponentMap m) s n hn w t]
  exact velocityMap_L2_bound P κ m ((toJet P (G.toFieldTower.realization s t)).word w)

theorem toFieldTower_driftBlock_le (G : Field P T raw) (κ : ℝ) (m : Space)
    (s q n : ℕ) (hn : n + q ≤ s) (t : Icc (0 : ℝ) T) :
    driftBlockNorm P q n (velocityMap (velocityComponents κ m)) (G.toFieldTower.realization s t) ≤
      3 * |κ| * blockNorm P (toJet P (G.toFieldTower.realization s t)) q n +
        blockNorm P (toJet P ((G.map (normalComponentMap m)).toFieldTower.realization s t)) q n :=
            by
  unfold driftBlockNorm blockNorm
  rw [mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro r hr
  exact G.toFieldTower_driftLevel_le κ m s (n+r) (by have := mem_range.mp hr; omega) t

theorem toFieldTower_weightedDrift_le (G : Field P T raw) (κ : ℝ) (m : Space)
    (s q N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (t : Icc (0 : ℝ) T) :
    weightedDriftNorm P q N ρ (velocityMap (velocityComponents κ m))
        (G.toFieldTower.realization s t) ≤
      3 * |κ| * weightedNorm P q N ρ (G.toFieldTower.realization s t) +
        weightedNorm P q N ρ ((G.map (normalComponentMap m)).toFieldTower.realization s t) := by
  unfold weightedDriftNorm weightedNorm
  rw [mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro n hn
  have h := mul_le_mul_of_nonneg_left
    (G.toFieldTower_driftBlock_le κ m s q n (by have := mem_range.mp hn; omega) t)
    (weight_pos hρ n).le
  exact h.trans_eq (by ring)

/-- Separate word estimates for the full normalized vector and its actual
normal component give exactly the small transport budget needed by the
drift-preserving correction theorem. -/
theorem WordBound.toFieldTower_weightedDrift_le_two
    {G : Field P T raw} {q : ℕ} {R A₀ A₁ : ℝ}
    (hG : G.WordBound q R A₀ 0) (κ : ℝ) (m : Space)
    (hNrm : (G.map (normalComponentMap m)).WordBound q R A₁ 0)
    (hR : 0 ≤ R) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (s N : ℕ) (hN : N + q ≤ s) (ρ : ℝ) (hρ : 0 < ρ) (hsmall : ρ * R ≤ 1 / 2)
    (t : Icc (0 : ℝ) T) :
    weightedDriftNorm P q N ρ (velocityMap (velocityComponents κ m))
      (G.toFieldTower.realization s t) ≤ 2 * (3 * |κ| * A₀ + A₁) := by
  have hz := hG.toFieldTower_weightedNorm_le_two hR hA₀ s N hN ρ hρ hsmall t
  have hn := hNrm.toFieldTower_weightedNorm_le_two hR hA₁ s N hN ρ hρ hsmall t
  exact (G.toFieldTower_weightedDrift_le κ m s q N hN ρ hρ t).trans
    ((add_le_add (mul_le_mul_of_nonneg_left hz (by positivity)) hn).trans_eq (by ring))

end EulerPacketCylinderField.Field
