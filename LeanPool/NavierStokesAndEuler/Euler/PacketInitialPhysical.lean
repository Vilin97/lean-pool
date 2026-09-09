/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketFieldPhysicalSobolev
public import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteCoarseBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketInitialFields
import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalL2
import LeanPool.NavierStokesAndEuler.Euler.PacketExponentialTail
import LeanPool.NavierStokesAndEuler.Euler.PacketFiniteFrequencyBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialBounds
import Mathlib.Algebra.Order.Star.Real

/-! The high initial increment retains its small amplitude, while the
mean initial increment is O(k⁻²) without any oscillatory-graph loss. -/

@[expose] public section


noncomputable section


namespace EulerPacketInitial

open Set EulerSmoothLimit EulerPacketProfileRecursion EulerPacketCylinderField
  EulerPacketTimeProfile EulerPacketCoarseMajorant EulerPacketFiniteFrequency
  EulerPacketTailBound EulerPhysicalL2Scaling EulerCylinderPhysicalTensor EulerCylinderCoordinates

/-- High cost, given by `fixedVelocityGradeCost R H 1+fixedVelocityGradeCost R H 2+1`. -/
def highCost (R H : ℝ) : ℝ := fixedVelocityGradeCost R H 1+fixedVelocityGradeCost R H 2+1
/-- Mean cost, given by `fixedVelocityGradeCost R H 2+2`. -/
def meanCost (R H : ℝ) : ℝ := fixedVelocityGradeCost R H 2+2

theorem highCost_nonneg (R H : ℝ) (hR : 0 ≤ R) : 0 ≤ highCost R H := by
  have h1 := fixedVelocityGradeCost_nonneg R H hR 1
  have h2 := fixedVelocityGradeCost_nonneg R H hR 2
  unfold highCost
  positivity

theorem meanCost_nonneg (R H : ℝ) (hR : 0 ≤ R) : 0 ≤ meanCost R H := by
  have h2 := fixedVelocityGradeCost_nonneg R H hR 2
  unfold meanCost
  positivity

variable {P T : ℝ} [Fact (0 < P)] {hT : 0 ≤ T} {N : ℕ}
  {a : ℕ → Profile} {support : Set Space}
  (G : ∀ i, i ≤ N → ProfileRegularity P T hT support (a i))
  (S : Scales (Icc (0 : ℝ) T)) (R : ℝ)
  (hG : ∀ i (hi : i ≤ N), 1 ≤ i → ProfileBudget (G i hi) S R i)
  (hR : 1 ≤ R) (ha : a 0 = 0) (t : Icc (0 : ℝ) T)
  (hN : 1 ≤ N) (C k : ℝ) (hC : 1 ≤ C) (hk : 4 ≤ k)
  (hbase : tailBase R S.H0 C N ≤ k ^ (1 / 100 : ℝ))

include hG hR ha hN hC hk hbase

theorem high_frequency_bound :
    (highField G t k⁻¹).WordBound 6 (4*R) (S.growth t*highCost R S.H0) 0 := by
  have hk0 : 0 < k := by linarith
  have hB0 := tailBase_nonneg R S.H0 C (zero_le_one.trans hC) N
  have hsmall : k⁻¹*tailBase R S.H0 C N ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using grade_ratio_le_half k (tailBase R S.H0 C N) hk hbase
  have h := high_bound G S R hG hR ha t hN C k⁻¹ hC (inv_nonneg.mpr hk0.le) hsmall
  have h4 := fourth_power_le_frequency k _ (by linarith) hB0 hbase
  have hc1 := fixedVelocityGradeCost_nonneg R S.H0 (zero_le_one.trans hR) 1
  have hc2 := fixedVelocityGradeCost_nonneg R S.H0 (zero_le_one.trans hR) 2
  have hn := normalized_low_high_le k (tailBase R S.H0 C N)
    (fixedVelocityGradeCost R S.H0 1) (fixedVelocityGradeCost R S.H0 2) (by linarith) hc2 h4
  apply h.mono_amplitude (by linarith)
  apply mul_le_mul_of_nonneg_left _ (S.growth_pos t).le
  apply le_trans _ hn
  apply le_mul_of_one_le_left
  · positivity
  · linarith

theorem mean_frequency_bound (ha1 : (a 1).mean = 0) :
    (meanField G t k⁻¹).WordBound 6 (4*R) (meanCost R S.H0/k^2) 0 := by
  have hk0 : 0 < k := by linarith
  have hB0 := tailBase_nonneg R S.H0 C (zero_le_one.trans hC) N
  have hsmall : k⁻¹*tailBase R S.H0 C N ≤ 1/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using grade_ratio_le_half k (tailBase R S.H0 C N) hk hbase
  have h := mean_bound G S R hG hR ha t hN ha1 C k⁻¹ hC (inv_nonneg.mpr hk0.le) hsmall
  have h4 := fourth_power_le_frequency k _ (by linarith) hB0 hbase
  exact h.mono_amplitude (by linarith)
    (remainder_low_high_le k _ (fixedVelocityGradeCost R S.H0 2) hk0 h4)

theorem high_physical_bound (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (m : Space) (s : ℕ) :
    derivativeSum s (scale ell (fun x : Space => high N k⁻¹ t a (t,(x,k*inner ℝ m x)))) ≤
      (ell⁻¹)^s*k^s*S.growth t*(highCost R S.H0 *
        physicalDerivativeCost P (4*R) (‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖m‖)) s) :=
            by
  have h := high_frequency_bound G S R hG hR ha t hN C k hC hk hbase
  have hs := h.scaled_graph_derivativeSum_le (by linarith)
    (mul_nonneg (S.growth_pos t).le (highCost_nonneg R S.H0 (zero_le_one.trans hR)))
    t ell hell hell1 k m (‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖m‖)) k
    (by positivity) (by linarith) (frequencyFactor_le_linear k (by linarith) m) s
  exact hs.trans_eq (by ring)

theorem mean_physical_bound (ha1 : (a 1).mean = 0) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (m : Space) (s : ℕ) :
    derivativeSum s (scale ell (fun x : Space => mean N k⁻¹ t a (t,(x,k*inner ℝ m x)))) ≤
      (ell⁻¹)^s/k^2*(meanCost R S.H0 *
        physicalDerivativeCost P (4*R) ‖coordinateEquiv.symm.toContinuousLinearMap‖ s) := by
  have h := mean_frequency_bound G S R hG hR ha t hN C k hC hk hbase ha1
  have hs := h.scaled_graph_derivativeSum_le (by linarith)
    (div_nonneg (meanCost_nonneg R S.H0 (zero_le_one.trans hR)) (sq_nonneg k))
    t ell hell hell1 0 m ‖coordinateEquiv.symm.toContinuousLinearMap‖ 1
    (norm_nonneg _) le_rfl (by simp [frequencyFactor]) s
  have he : (fun x : Space => mean N k⁻¹ t a (t,(x,k*inner ℝ m x))) =
      (fun x : Space => mean N k⁻¹ t a (t,(x,0*inner ℝ m x))) := by
    funext x
    rw [mean_angle G t k⁻¹ t x (k*inner ℝ m x),zero_mul]
  rw [he]
  exact hs.trans_eq (by rw [one_pow]; ring)

end EulerPacketInitial
