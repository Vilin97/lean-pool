/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyNonlinearEstimate

@[expose] public section

/-! Actual metric Gevrey energies, fixed norm conversion, and nonlinear scalar growth bounds. -/

noncomputable section

namespace EulerGevreyMetricEstimate

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSobolevGevreyOperators EulerSobolevTransportCommutator EulerGevreyMetricComparison
  EulerWeightedCylinderEnergy EulerFiniteMetricEnergy EulerGevreyLowNorms EulerBaseWordMetric
  EulerPacketWeights

variable (period : ℝ) [Fact (0 < period)]

/-- The actual fixed-base metric Gevrey energy of one complete Sobolev field. -/
def energyNorm {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) : ℝ :=
  weightedMetricSum ρ (fun I : ExternalWord N => I.1.val) K (energyValues period 6 N hN u)

/-- The actual metric radius-loss quantity at the same cutoff. -/
def energyLoss {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) : ℝ :=
  weightedMetricLoss ρ (fun I : ExternalWord N => I.1.val) K (energyValues period 6 N hN u)

/-- A fixed conversion factor, with no external derivative cutoff in its definition. -/
def metricAmplification (c : ℝ) : ℝ := 1+Real.sqrt 5461/c

theorem energyNorm_nonneg {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) : 0 ≤ energyNorm period N
      hN ρ K u :=
  Finset.sum_nonneg (fun I _ => mul_nonneg (weight_pos hρ I.1.val).le (Real.sqrt_nonneg _))

theorem energyLoss_nonneg {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) : 0 ≤ energyLoss period N
      hN ρ K u :=
  Finset.sum_nonneg (fun I _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg I.1.val) (weight_pos hρ
    I.1.val).le) (Real.sqrt_nonneg _))

omit [Fact (0 < period)] in
theorem metricAmplification_one_le {c : ℝ} (hc : 0 < c) : 1 ≤ metricAmplification c := by
  unfold metricAmplification
  exact le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) hc.le)

/-- Every actual retained Sobolev block is bounded by the metric energy with the fixed factor. -/
theorem weightedNorm_le_energy {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) (c : ℝ) (hc : 0 < c)
    (hK : ∀ v, c^2*‖v‖^2 ≤ ⟪K v,v⟫_ℝ) :
    weightedNorm period 6 N ρ u ≤ metricAmplification c*energyNorm period N hN ρ K u := by
  have h := weightedNorm_metric_lower period 6 N hN ρ hρ K u c hc hK
  rw [card_baseWord_six] at h
  have he := energyNorm_nonneg period N hN ρ hρ K u
  change weightedNorm period 6 N ρ u ≤ (Real.sqrt 5461/c)*energyNorm period N hN ρ K u at h
  unfold metricAmplification
  nlinarith only [h,he]

/-- The actual radius-loss sum obeys the identical fixed metric conversion. -/
theorem weightedLoss_le_energy {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period s) (c : ℝ) (hc : 0 < c)
    (hK : ∀ v, c^2*‖v‖^2 ≤ ⟪K v,v⟫_ℝ) :
    weightedLoss period 6 N ρ u ≤ metricAmplification c*energyLoss period N hN ρ K u := by
  have h := weightedLoss_metric_lower period 6 N hN ρ hρ K u c hc hK
  rw [card_baseWord_six] at h
  have he := energyLoss_nonneg period N hN ρ hρ K u
  change weightedLoss period 6 N ρ u ≤ (Real.sqrt 5461/c)*energyLoss period N hN ρ K u at h
  unfold metricAmplification
  nlinarith only [h,he]

/-- Exact scalar conversion of a Sobolev forcing polynomial to metric energy and metric radius loss. -/
theorem metric_polynomial_conversion (S0 S1 S2 D R B a E Y X Z H : ℝ)
    (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) (hD : 0 ≤ D) (hB : 0 ≤ B) (ha : 1 ≤ a)
    (hE0 : 0 ≤ E) (hY0 : 0 ≤ Y) (hX0 : 0 ≤ X)
    (hE : E ≤ a*X) (hY : Y ≤ a*Z)
    (hH : H ≤ S0*R+S1*E+S2*E^2+D*(B+E)*Y) :
    H ≤ S0*R+(S1*a)*X+(S2*a^2)*X^2+(D*a^2)*(B+X)*Z := by
  have ha0 : 0 ≤ a := by linarith
  have hsq : E^2 ≤ a^2*X^2 := by
    simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul hE hE hE0 (mul_nonneg
      ha0 hX0)
  have hBE : B+E ≤ a*(B+X) := by nlinarith only [hE, mul_le_mul_of_nonneg_right ha hB]
  have hBY : (B+E)*Y ≤ a^2*(B+X)*Z := by
    have h := mul_le_mul hBE hY hY0 (mul_nonneg ha0 (add_nonneg hB hX0))
    exact h.trans_eq (by ring)
  have h := add_le_add (add_le_add (add_le_add (le_refl (S0*R))
    (mul_le_mul_of_nonneg_left hE hS1)) (mul_le_mul_of_nonneg_left hsq hS2))
    (mul_le_mul_of_nonneg_left hBY hD)
  calc
    H ≤ S0*R+S1*E+S2*E^2+D*(B+E)*Y := hH
    _ = S0*R+S1*E+S2*E^2+D*((B+E)*Y) := by ring
    _ ≤ S0*R+S1*(a*X)+S2*(a^2*X^2)+D*(a^2*(B+X)*Z) := h
    _ = _ := by ring

/-- A concrete pointwise velocity bound determined by the actual metric energy. -/
def metricVelocityBound (c B X : ℝ) : NNReal :=
  (sobolevEmbeddingConstant period 6*(B+metricAmplification c*X)).toNNReal

/-- The actual background-plus-error velocity satisfies the fixed-order bound used by the metric PDE estimate. -/
theorem velocity_ae_metric {s : ℕ} (N : ℕ) (hN : N+6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (z e : SobolevSpace period s) (c B : ℝ) (hc : 0 < c)
    (hK : ∀ v, c^2*‖v‖^2 ≤ ⟪K v,v⟫_ℝ) (hz : weightedNorm period 6 N ρ z ≤ B) :
    ∀ᵐ x ∂liftMeasure period, ‖value period (z+e) x‖ ≤ metricVelocityBound period c B (energyNorm
      period N hN ρ K e) := by
  have h := value_ae_weighted period N (by omega : 6 ≤ s) ρ hρ (z+e)
  have hn := (weightedNorm_add_le period 6 N hN ρ hρ z e).trans
    (add_le_add hz (weightedNorm_le_energy period N hN ρ hρ K e c hc hK))
  have hp := mul_le_mul_of_nonneg_left hn (sobolevEmbeddingConstant_nonneg period 6)
  filter_upwards [h] with x hx
  exact (hx.trans hp).trans (Real.le_coe_toNNReal _)

end EulerGevreyMetricEstimate
