/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyTransportCommutator
public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricComparison

@[expose] public section

/-! Fixed-base pointwise and metric-loss control by actual finite Gevrey norms. -/

noncomputable section

namespace EulerGevreyLowNorms

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerJetProductBounds EulerPacketWeights
  EulerSobolevGevreyOperators EulerBaseWordMetric EulerFiniteMetricEnergy
    EulerWeightedCylinderEnergy
  EulerGevreyMetricComparison EulerSobolevTransportCommutator
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Monotonicity in the fixed base Sobolev index. -/
theorem weightedNorm_mono {s p q : ℕ} (hpq : p ≤ q) (N : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (u : SobolevSpace period s) : weightedNorm period p N ρ u ≤ weightedNorm period q N ρ u := by
  apply Finset.sum_le_sum
  intro n _
  apply mul_le_mul_of_nonneg_left _ (weight_pos hρ n).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : p+1 ≤ q+1))
    (fun r _ _ => (levelNorm_nonneg (toJet period u) : 0 ≤ levelNorm period (toJet period u) (n+r)))

/-- The actual base Sobolev norm is contained in every nonempty truncated weighted sum. -/
theorem restrict_norm_le_weighted {s q : ℕ} (N : ℕ) (hq : q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (u : SobolevSpace period s) : ‖restrictOperator period hq u‖ ≤ weightedNorm period q N ρ u := by
  have hbase : ‖restrictOperator period hq u‖ ≤ blockNorm period (toJet period u) q 0 := by
    rw [blockNorm_zero_eq_size (toJet period u) hq]
    have heq : sobolevSize period (directions := standardDirection) q (value period u) =
        sumNorm period (restrictOperator period hq u) := by
      rw [sumNorm_eq_jet, ← sobolevSize_eq period (toJet period (restrictOperator period hq u)),
        value_restrictOperator]
    rw [heq]
    exact norm_le_sumNorm period _
  have hsum := Finset.single_le_sum (s := Finset.range (N+1))
    (fun n _ => mul_nonneg (weight_pos hρ n).le (show 0 ≤ blockNorm period (toJet period u) q n
      from blockNorm_nonneg _))
    (show 0 ∈ Finset.range (N+1) by simp)
  have hsum' : blockNorm period (toJet period u) q 0 ≤ weightedNorm period q N ρ u := by
    simpa [weight, weightedNorm] using hsum
  exact hbase.trans hsum'

/-- The actual pointwise bound has a constant depending only on the fixed base order six, never on the external cutoff. -/
theorem value_ae_weighted {s : ℕ} (N : ℕ) (hs : 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (u : SobolevSpace period s) :
    ∀ᵐ x ∂liftMeasure period, ‖value period u x‖ ≤ sobolevEmbeddingConstant period 6 * weightedNorm
      period 6 N ρ u := by
  have h := value_ae_bound period (by norm_num : 3 ≤ 6) (restrictOperator period hs u)
  filter_upwards [h] with x hx
  rw [value_restrictOperator] at hx
  exact hx.trans (mul_le_mul_of_nonneg_left (restrict_norm_le_weighted period N hs ρ hρ u)
    (sobolevEmbeddingConstant_nonneg period 6))

/-- The exact metric radius-loss sum in fixed-base word notation. -/
theorem metricLoss_eq {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) :
    weightedMetricLoss ρ (fun I : ExternalWord N => I.1.val) K (energyValues period q N hN u) =
      ∑ n : Fin (N+1), (n.val : ℝ)*weight ρ n.val * ∑ w : Fin n.val → Fin 4,
        baseWordMetricNorm period K (EulerH6Pressure.SpatialJet.derivativeJet (q := q) (toJet
          period u) w
          (by have := n.isLt; omega)) := by
  simp only [weightedMetricLoss, Fintype.sum_sigma, Finset.mul_sum, energyValues,
    baseWordMetricNorm]

/-- The actual derivative-loss Sobolev sum is controlled by metric roots with only the fixed base-order constant. -/
theorem weightedLoss_metric_lower {s : ℕ} (q N : ℕ) (hN : N+q ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) (c : ℝ) (hc : 0 < c)
    (hK : ∀ v, c^2*‖v‖^2 ≤ ⟪K v,v⟫_ℝ) :
    weightedLoss period q N ρ u ≤ (Real.sqrt (Fintype.card (BaseWord q) : ℝ)/c) *
      weightedMetricLoss ρ (fun I : ExternalWord N => I.1.val) K (energyValues period q N hN u) :=
        by
  rw [metricLoss_eq, weightedLoss, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have h := mul_le_mul_of_nonneg_left
    (blockNorm_metric_lower period (q := q) (n := n.val) u (by have := n.isLt; omega) K c hc hK)
    (mul_nonneg (Nat.cast_nonneg n.val) (weight_pos hρ n.val).le)
  exact h.trans_eq (by ring)

end EulerGevreyLowNorms
