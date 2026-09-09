/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteMetricEnergy
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialSobolevInverse

/-! Exact identification of the source's base-Sobolev word sum and root metric energy. -/

@[expose] public section


noncomputable section

namespace EulerBaseWordMetric

open EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
    EulerFiniteMetricEnergy
open InnerProductSpace

/-- A base Sobolev word of any length at most s. -/
abbrev BaseWord (s : ℕ) := Σ n : Fin (s + 1), Fin n.val → Fin 4

variable (period : ℝ) [Fact (0 < period)]

/-- The finite family of actual strong derivatives indexed by all base Sobolev words. -/
def baseWordValues {s : ℕ} {f : LiftL2 period} (J : SpatialJet period standardDirection s f) :
    BaseWord s → LiftL2 period := fun w => J.word w.2

/-- The sigma-indexed family gives exactly the previously proved strong Sobolev sum norm. -/
theorem sum_baseWordValues_norm {s : ℕ} {f : LiftL2 period}
    (J : SpatialJet period standardDirection s f) :
    (∑ w : BaseWord s, ‖baseWordValues period J w‖) = J.sobolevNorm := by
  rw [SpatialJet.sobolevNorm_eq_sum_words]
  simp only [baseWordValues, Fintype.sum_sigma]
  exact Fin.sum_univ_eq_sum_range (fun n => ∑ w : Fin n → Fin 4, ‖J.word w‖) (s + 1)

/-- The number of base derivative words depends only on the fixed Sobolev index. -/
theorem card_baseWord (s : ℕ) : Fintype.card (BaseWord s) = ∑ n ∈ Finset.range (s + 1), 4 ^ n := by
  simp only [BaseWord, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun n => 4 ^ n) (s + 1)

/-- The source's root-of-sum metric energy for all base Sobolev words. -/
def baseWordMetricNorm {s : ℕ} {f : LiftL2 period} (K : LiftL2 period →L[ℝ] LiftL2 period)
    (J : SpatialJet period standardDirection s f) : ℝ := familyMetricNorm K (baseWordValues period
        J)

/-- The Sobolev sum is controlled by its metric root with a fixed base-word cardinality constant. -/
theorem sobolevNorm_le_baseWordMetric {s : ℕ} {f : LiftL2 period}
    (K : LiftL2 period →L[ℝ] LiftL2 period) (J : SpatialJet period standardDirection s f)
    (c : ℝ) (hc : 0 < c)
    (hK : ∀ u, c ^ 2 * ‖u‖ ^ 2 ≤ ⟪K u, u⟫_ℝ) :
    J.sobolevNorm ≤ (Real.sqrt (Fintype.card (BaseWord s) : ℝ) / c) * baseWordMetricNorm period K J
        := by
  rw [← sum_baseWordValues_norm period J]
  have hsum := sum_norm_le_card_sqrt_familyNorm (baseWordValues period J)
  have hmet := familyMetricNorm_lower K (baseWordValues period J) c hc.le hK
  have hn : familyNorm (baseWordValues period J) ≤ baseWordMetricNorm period K J / c := by
    apply (le_div_iff₀ hc).mpr
    simpa only [baseWordMetricNorm, mul_comm] using hmet
  have hh := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg (Fintype.card (BaseWord s) : ℝ))
  exact hsum.trans (hh.trans_eq (by ring))

/-- The metric root is controlled by the actual base Sobolev sum with no extra word-count factor. -/
theorem baseWordMetric_le_sobolevNorm {s : ℕ} {f : LiftL2 period}
    (K : LiftL2 period →L[ℝ] LiftL2 period) (J : SpatialJet period standardDirection s f) :
    baseWordMetricNorm period K J ≤ Real.sqrt ‖K‖ * J.sobolevNorm := by
  have h := familyMetricNorm_upper K (baseWordValues period J)
  have hn := familyNorm_le_sum_norm (baseWordValues period J)
  rw [sum_baseWordValues_norm period J] at hn
  exact h.trans (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))

end EulerBaseWordMetric
