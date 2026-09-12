/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.GaussianHeatTotal
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevDerivatives
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevSpace
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureJetIdentities
import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The actual Gaussian cylinder heat semigroup on the complete Sobolev scale. -/

section

/-! Genuine one-derivative L² smoothing lifts to the complete cylinder Sobolev scale. -/

@[expose] public section

noncomputable section

namespace EulerSobolevSmoothing

open EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerSpatialSobolevInverse
  EulerCylinderSobolev EulerCylinderSobolevSpace
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

variable (A : LiftL2 period →L[ℝ] LiftL2 period) (C : ℝ)
variable (hD : ∀ i : Fin 4, ∀ f : LiftL2 period, ∃ g : LiftL2 period,
  HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t) (A f)) g
      0 ∧
    ‖g‖ ≤ C * ‖f‖)

/-- The uniquely determined strong derivative of a genuinely smoothing L² operator. -/
def smoothingDerivative (i : Fin 4) (f : LiftL2 period) : LiftL2 period :=
  Classical.choose (hD i f)

/-- The chosen derivative is the actual strong derivative of the translated output. -/
theorem smoothingDerivative_hasDerivAt (i : Fin 4) (f : LiftL2 period) :
    HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t) (A f))
      (smoothingDerivative period A C hD i f) 0 := (Classical.choose_spec (hD i f)).1

/-- The actual derivative obeys the given L² smoothing estimate. -/
theorem smoothingDerivative_bound (i : Fin 4) (f : LiftL2 period) :
    ‖smoothingDerivative period A C hD i f‖ ≤ C * ‖f‖ := (Classical.choose_spec (hD i f)).2

/-- Uniqueness of strong derivatives proves additivity of the smoothing derivative. -/
theorem smoothingDerivative_add (i : Fin 4) (f g : LiftL2 period) :
    smoothingDerivative period A C hD i (f + g) =
      smoothingDerivative period A C hD i f + smoothingDerivative period A C hD i g := by
  apply (smoothingDerivative_hasDerivAt period A C hD i (f + g)).unique
  simpa only [map_add] using
    (smoothingDerivative_hasDerivAt period A C hD i f).fun_add
      (smoothingDerivative_hasDerivAt period A C hD i g)

/-- Uniqueness of strong derivatives proves homogeneity of the smoothing derivative. -/
theorem smoothingDerivative_smul (i : Fin 4) (r : ℝ) (f : LiftL2 period) :
    smoothingDerivative period A C hD i (r • f) = r • smoothingDerivative period A C hD i f := by
  apply (smoothingDerivative_hasDerivAt period A C hD i (r • f)).unique
  simpa only [map_smul, Pi.smul_def] using
    (smoothingDerivative_hasDerivAt period A C hD i f).const_smul r

/-- Each derivative of the smoothing operator is a bounded linear L² operator. -/
def smoothingDerivativeOperator (i : Fin 4) : LiftL2 period →L[ℝ] LiftL2 period :=
  LinearMap.mkContinuous
    { toFun := smoothingDerivative period A C hD i
      map_add' := smoothingDerivative_add period A C hD i
      map_smul' := smoothingDerivative_smul period A C hD i }
    C (smoothingDerivative_bound period A C hD i)

/-- The bounded derivative operator retains its actual strong-derivative characterization. -/
theorem smoothingDerivativeOperator_hasDerivAt (i : Fin 4) (f : LiftL2 period) :
    HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t) (A f))
      (smoothingDerivativeOperator period A C hD i f) 0 :=
  smoothingDerivative_hasDerivAt period A C hD i f

/-- The bounded derivative operator retains the actual smoothing estimate. -/
theorem smoothingDerivativeOperator_bound (i : Fin 4) (f : LiftL2 period) :
    ‖smoothingDerivativeOperator period A C hD i f‖ ≤ C * ‖f‖ :=
  smoothingDerivative_bound period A C hD i f

/-- Differentiating a translation-commuting smoothing operator preserves translation commutation. -/
theorem smoothingDerivative_translation
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (i : Fin 4) (a : LiftDomain period) (f : LiftL2 period) :
    translation period a (smoothingDerivativeOperator period A C hD i f) =
      smoothingDerivativeOperator period A C hD i (translation period a f) := by
  have hd := (translation period a).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (smoothingDerivative_hasDerivAt period A C hD i f)
  have he : (fun t => translation period a
      (translation period (translationPath period (standardDirection i) t) (A f))) =
      fun t => translation period (translationPath period (standardDirection i) t)
        (A (translation period a f)) := by
    funext t
    rw [hA]
    exact translations_commute period a _ _
  change HasDerivAt (fun t => translation period a
    (translation period (translationPath period (standardDirection i) t) (A f)))
    (translation period a (smoothingDerivative period A C hD i f)) 0 at hd
  rw [he] at hd
  exact hd.unique (smoothingDerivative_hasDerivAt period A C hD i (translation period a f))

/-- A true smoothing operator adds one complete level to any finite strong derivative jet. -/
def gainJet {q : ℕ} {f : LiftL2 period}
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (J : SpatialJet period standardDirection q f) : SpatialJet period standardDirection (q + 1) (A
        f) :=
  .succ (fun i => smoothingDerivativeOperator period A C hD i f)
    (fun i => EulerPressureJetIdentities.SpatialJet.map
      (smoothingDerivativeOperator period A C hD i)
      (smoothingDerivative_translation period A C hD hA i) J)
    (fun i => smoothingDerivativeOperator_hasDerivAt period A C hD i f)

/-- The Sobolev element obtained by actual one-derivative smoothing. -/
def gain {q : ℕ}
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) : SobolevSpace period (q + 1) :=
  ofJet period (gainJet period A C hD hA (toJet period u))

/-- Smoothing on the Sobolev scale has exactly the original L² output. -/
@[simp]
theorem gain_value {q : ℕ}
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) : value period (gain period A C hD hA u) = A (value period u) :=
  value_ofJet period _

/-- The Sobolev derivative gain has an explicit bound independent of the derivative order. -/
theorem gain_bound {q : ℕ} (hC : 0 ≤ C)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f))
    (u : SobolevSpace period q) : ‖gain period A C hD hA u‖ ≤ max ‖A‖ C * ‖u‖ := by
  change ‖(gain period A C hD hA u).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (le_max_of_le_left (norm_nonneg A)) (norm_nonneg
      u))).mpr
  rintro ⟨⟨n, hn⟩, w⟩
  cases n with
  | zero =>
    change ‖(gainJet period A C hD hA (toJet period u)).word w‖ ≤ _
    rw [SpatialJet.word_zero]
    exact (A.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (value_norm_le period u) (norm_nonneg
        A)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg u)))
  | succ n =>
    change ‖(gainJet period A C hD hA (toJet period u)).word w‖ ≤ _
    rw [gainJet, SpatialJet.word_succ, EulerPressureJetIdentities.SpatialJet.map_word]
    have h := smoothingDerivativeOperator_bound period A C hD (w (Fin.last n))
      ((toJet period u).word (Fin.init w))
    rw [toJet_word period u (by omega)] at h
    rw [toJet_word period u (by omega)]
    exact h.trans ((mul_le_mul_of_nonneg_left
      (word_norm_le period u ⟨⟨n, by omega⟩, Fin.init w⟩) hC).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg u)))

/-- The actual Sobolev smoothing construction is linear. -/
def gainLinearMap (q : ℕ)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f)) :
    SobolevSpace period q →ₗ[ℝ] SobolevSpace period (q + 1) where
  toFun := gain period A C hD hA
  map_add' := by
    intro u v
    apply value_injective period
    change value period (gain period A C hD hA (u + v)) =
      value period (gain period A C hD hA u) + value period (gain period A C hD hA v)
    simp only [gain_value]
    exact map_add A _ _
  map_smul' := by
    intro r u
    apply value_injective period
    change value period (gain period A C hD hA (r • u)) = r • value period (gain period A C hD hA u)
    simp only [gain_value]
    exact map_smul A r _

/-- A genuine bounded map H^q to H^(q+1), obtained from actual L² smoothing derivatives. -/
def gainOperator (q : ℕ) (hC : 0 ≤ C)
    (hA : ∀ a f, A (translation period a f) = translation period a (A f)) :
    SobolevSpace period q →L[ℝ] SobolevSpace period (q + 1) :=
  (gainLinearMap period A C hD q hA).mkContinuous (max ‖A‖ C) (gain_bound period A C hD hC hA)

end EulerSobolevSmoothing

end
end

end

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
