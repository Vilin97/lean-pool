/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevSmoothing
public import LeanPool.NavierStokesAndEuler.Euler.GaussianHeatTotal
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDerivatives
import Mathlib.Algebra.Order.Star.Real

/-! The actual Gaussian cylinder heat semigroup on the complete Sobolev scale. -/

@[expose] public section


noncomputable section

namespace EulerSobolevHeat

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevSmoothing
    EulerGaussianCylinderHeat
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine cylinder heat semigroup lifted to the complete Sobolev space. -/
def heatOperator (q : ℕ) (v : ℝ≥0) : SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  liftOperator period q (cylinderHeat period v) (cylinderHeat_translation period v)

/-- Every Sobolev derivative coordinate evolves by the actual L² heat semigroup. -/
@[simp]
theorem heatOperator_apply {q : ℕ} (v : ℝ≥0) (u : SobolevSpace period q) (w : SobolevWord q) :
    (heatOperator period q v u).val w = cylinderHeat period v (u.val w) := rfl

/-- The heat semigroup is contractive in every complete Sobolev norm. -/
theorem heatOperator_bound {q : ℕ} (v : ℝ≥0) (u : SobolevSpace period q) :
    ‖heatOperator period q v u‖ ≤ ‖u‖ := by
  change ‖(heatOperator period q v u).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro w
  exact (cylinderHeat_norm_le period v _).trans (word_norm_le period u w)

/-- The underlying L² field evolves by exactly the original heat operator. -/
@[simp]
theorem heatOperator_value {q : ℕ} (v : ℝ≥0) (u : SobolevSpace period q) :
    value period (heatOperator period q v u) = cylinderHeat period v (value period u) := rfl

/-- Zero variance is the identity on the complete Sobolev space. -/
@[simp]
theorem heatOperator_zero {q : ℕ} (u : SobolevSpace period q) : heatOperator period q 0 u = u := by
  apply value_injective period
  simp only [heatOperator_value, cylinderHeat_zero]

/-- The actual Sobolev heat operators obey the semigroup law. -/
theorem heatOperator_semigroup {q : ℕ} (v w : ℝ≥0) (u : SobolevSpace period q) :
    heatOperator period q v (heatOperator period q w u) = heatOperator period q (v + w) u := by
  apply value_injective period
  simp only [heatOperator_value, cylinderHeat_semigroup]

/-- Strong heat continuity holds in every complete Sobolev norm, including at zero variance. -/
theorem heatOperator_continuous {q : ℕ} (u : SobolevSpace period q) :
    Continuous (fun v : ℝ≥0 => heatOperator period q v u) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  exact cylinderHeat_continuous period (u.val w)

/-- The explicit parabolic derivative constant of the Gaussian heat operator. -/
def heatDerivativeConstant (v : ℝ≥0) : ℝ := gaussianAbsMoment 1 / Real.sqrt (v : ℝ)

/-- The Gaussian derivative constant is nonnegative. -/
theorem heatDerivativeConstant_nonneg (v : ℝ≥0) : 0 ≤ heatDerivativeConstant v :=
  div_nonneg (gaussianAbsMoment_nonneg 1) (Real.sqrt_nonneg _)

/-- Positive-time heat smoothing is a genuine bounded map between successive Sobolev levels. -/
def heatGain (q : ℕ) (v : ℝ≥0) (hv : 0 < v) :
    SobolevSpace period q →L[ℝ] SobolevSpace period (q + 1) :=
  gainOperator period (cylinderHeat period v) (heatDerivativeConstant v)
    (fun i f => cylinderHeat_one_derivative period hv f i) q
    (heatDerivativeConstant_nonneg v) (cylinderHeat_translation period v)

/-- The derivative-gaining map has exactly the actual L² heat output. -/
@[simp]
theorem heatGain_value {q : ℕ} (v : ℝ≥0) (hv : 0 < v) (u : SobolevSpace period q) :
    value period (heatGain period q v hv u) = cylinderHeat period v (value period u) :=
  gain_value period _ _ _ _ u

/-- Actual Gaussian smoothing gains one Sobolev derivative, uniformly in the Sobolev order. -/
theorem heatGain_bound {q : ℕ} (v : ℝ≥0) (hv : 0 < v) (u : SobolevSpace period q) :
    ‖heatGain period q v hv u‖ ≤ max 1 (heatDerivativeConstant v) * ‖u‖ := by
  have h := gain_bound period (cylinderHeat period v) (heatDerivativeConstant v)
    (fun i f => cylinderHeat_one_derivative period hv f i) (heatDerivativeConstant_nonneg v)
    (cylinderHeat_translation period v) u
  have hA : ‖cylinderHeat period v‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
        simpa using cylinderHeat_norm_le period v f)
  exact h.trans (mul_le_mul_of_nonneg_right (max_le_max hA le_rfl) (norm_nonneg u))

/-- Truncating the gained derivative gives the ordinary Sobolev heat action. -/
theorem truncate_heatGain {q : ℕ} (v : ℝ≥0) (hv : 0 < v) (u : SobolevSpace period q) :
    truncateOperator period q (heatGain period q v hv u) = heatOperator period q v u := by
  apply value_injective period
  simp only [value_truncateOperator, heatGain_value, heatOperator_value]

/-- A fixed positive amount of smoothing may be separated from any remaining heat evolution. -/
theorem heatGain_semigroup {q : ℕ} (v w : ℝ≥0) (hv : 0 < v) (u : SobolevSpace period q) :
    heatGain period q v hv (heatOperator period q w u) =
      heatGain period q (v + w) (add_pos_of_pos_of_nonneg hv (show 0 ≤ w from bot_le)) u := by
  apply value_injective period
  simp only [heatGain_value, heatOperator_value, cylinderHeat_semigroup]

/-- The gained-derivative heat orbit is strongly continuous at every positive variance. -/
theorem heatGain_continuous {q : ℕ} (u : SobolevSpace period q) :
    Continuous (fun v : {v : ℝ≥0 // 0 < v} => heatGain period q v.val v.property u) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  let ε : ℝ≥0 := v.val / 2
  have hε : 0 < ε := div_pos v.property (by norm_num)
  have hεv : ε < v.val := by dsimp [ε]; exact half_lt_self v.property
  have hc : Continuous (fun w : {v : ℝ≥0 // 0 < v} =>
      heatGain period q ε hε (heatOperator period q (w.val - ε) u)) :=
    (heatGain period q ε hε).continuous.comp
      ((heatOperator_continuous period u).comp (continuous_subtype_val.sub continuous_const))
  apply hc.continuousAt.congr_of_eventuallyEq
  have he : ∀ᶠ w : {v : ℝ≥0 // 0 < v} in 𝓝 v, ε < w.val :=
    (continuous_subtype_val.tendsto v).eventually (Ioi_mem_nhds hεv)
  filter_upwards [he] with w hw
  apply value_injective period
  simp only [heatGain_value, heatOperator_value, cylinderHeat_semigroup]
  rw [add_tsub_cancel_of_le hw.le]

end EulerSobolevHeat
