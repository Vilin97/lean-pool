/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseFirstPacketScales
public import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalScaleCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureScaleCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleGuards
public import LeanPool.NavierStokesAndEuler.Euler.ParentNormalPacketParameters
import LeanPool.NavierStokesAndEuler.Euler.PacketCommonScaleChoice
import LeanPool.NavierStokesAndEuler.Euler.PacketPressureSeries
import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalPrefix

/-! A single scale choice for the first packet and every normal stage.
The record contains only numerical inequalities and convergent series;
it does not assume the existence of a packet or of a future frame. -/

@[expose] public section


noncomputable section

namespace EulerPacketInductionScales

open Real Filter EulerScale EulerBaseDatum EulerPacketLowConstants
  EulerPacketBaseGuardScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual
  EulerPacketSourceScaleGuards EulerPacketUniformFrequencyScales
  EulerPacketSourceFrequency EulerPacketPressureScale EulerParentRenewalScale
  EulerPacketMovingFrame EulerTransverseActivationSelection EulerMeanHarmonic
open scoped Topology

/-- Geometry constant, given by `neighborStabilityConstant*frameConstant^2`. -/
def geometryConstant : ℝ := neighborStabilityConstant*frameConstant^2

theorem geometryConstant_one : 1 ≤ geometryConstant := by
  have hn : 1 ≤ neighborStabilityConstant := by
    linarith only [neighborStabilityConstant_ge]
  exact one_le_mul_of_one_le_of_one_le hn (one_le_pow₀ frame_properties.1)

/-- Activation margin, given by `1/(32*(activationConstant gradientConstant
hessianConstant+1))`. -/
def activationMargin : ℝ :=
  1/(32*(activationConstant gradientConstant hessianConstant+1))

theorem activationMargin_pos : 0 < activationMargin := by
  unfold activationMargin activationConstant
  positivity [hessian_nonneg]

theorem activationMargin_small :
    16*(activationConstant gradientConstant hessianConstant+1)*activationMargin ≤ 1 := by
  have hp : 0 < activationConstant gradientConstant hessianConstant+1 := by
    unfold activationConstant
    positivity [hessian_nonneg]
  unfold activationMargin
  field_simp
  linarith only [hp]

/-- Correction cost spec, bundling `d`, `B`, `N`, `a` and the required compatibility proofs. -/
def correctionCostSpec : CostSpec where
  d := 1
  B := 3
  N := 2
  a := 2
  b := 1/4
  c := 0
  C := 1
  p := 0
  q := 0
  d_le_two := by norm_num
  a_nonneg := by norm_num
  a_lt_B := by norm_num
  a_le_N := by norm_num
  b_pos := by norm_num
  C_pos := zero_lt_one

theorem correctionCost_eq (J : ℕ) (X : ℝ) (n : ℕ) :
    correctionCostSpec.cost J (scaleSequence J X) n =
      (frequency J X n)^(-(1/4 : ℝ)) := by
  simp only [correctionCostSpec,CostSpec.cost,EulerPacketSourceScaleBounds.monomialCost,
    pow_zero,mul_one,one_mul,zero_mul,add_zero,frequency,← exp_mul,rpow_ofNat]
  congr 1
  ring

/-- Extra cost used in packet induction scales. -/
def extraCost : Sum Unit Bool → CostSpec
  | .inl _ => EulerNormalPacketParameters.frequencySpec 4
  | .inr false => activationCostSpec frameConstant frame_properties.1
  | .inr true => correctionCostSpec

/-- Initial increment, given by `badCost J 4 gradientConstant gradientConstant hessianConstant
80 (scaleSequence J X) n + (frequency J X n)^(-(1/4 : ℝ))`. -/
def initialIncrement (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  badCost J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence J X) n +
    (frequency J X n)^(-(1/4 : ℝ))

/-- Pressure increment, given by
`2*gradientConstant*EulerPacketGeometryLowBounds.goodRatio*goodCost J (scaleSequence J X) n
+ initialIncrement J X n`. -/
def pressureIncrement (J : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  2*gradientConstant*EulerPacketGeometryLowBounds.goodRatio*goodCost J (scaleSequence J X) n +
    initialIncrement J X n

/-- Scales data, collecting `J`, `D`, `X`, `δ`, `stage_large`, `base_power` and their
compatibility conditions. -/
structure Scales (c B : ℝ) where
  /-- J of `Scales`, of type `ℕ`. -/
  J : ℕ
  /-- Domain data of `Scales`, of type `ℕ`. -/
  D : ℕ
  /-- X of `Scales`, of type `ℝ`. -/
  X : ℝ
  /-- Δ of `Scales`, of type `ℝ`. -/
  δ : ℝ
  stage_large : 3 ≤ J
  base_power : 2000 ≤ D
  x_large : 8 ≤ X
  delta_pos : 0 < δ
  delta_small : δ ≤ 1/16
  delta_activation : δ ≤ activationMargin
  delta_geometry : 1000000*geometryConstant*δ ≤ 1
  actual : ActualBounds J D 4 c X δ
  first : FirstScaleGuards J D X
  normal_frequency : ∀ n, UniversalFrequency (frequency J X n)
  previous_floor : ∀ n, B ≤ previousFrequency J D X n
  frequency_series : SmallSeries
    ((EulerNormalPacketParameters.frequencySpec 4).cost J (scaleSequence J X)) δ
  activation_series : SmallSeries
    ((activationCostSpec frameConstant frame_properties.1).cost J (scaleSequence J X)) δ
  correction_series : SmallSeries (fun n => (frequency J X n)^(-(1/4 : ℝ))) δ
  bad_series : SmallSeries
    (badCost J 4 gradientConstant gradientConstant hessianConstant 80 (scaleSequence J X)) δ
  good_series : SmallSeries
    (fun n => 2*gradientConstant*EulerPacketGeometryLowBounds.goodRatio *
      goodCost J (scaleSequence J X) n) δ
  renewal_series : SmallSeries (renewalCost J D 4 c frameConstant X) (1/4)
  time_small : baseHorizon J X ≤ 1
  localized : baseGuardCost J (initialCoefficientCost+1) (initialCoefficientCost+1)
    gradientConstant boundaryLocalizationC2 X ≤ 1/2

theorem exists_base_power : ∃ D : ℕ, 2000 ≤ D ∧
    (firstFrequencyPower : ℝ) < (D : ℝ)*(theta/100) := by
  have ht : 0 < theta/100 := by
    norm_num [theta]
  obtain ⟨d,hd⟩ := exists_nat_gt ((firstFrequencyPower : ℝ)/(theta/100))
  refine ⟨max 2000 d,le_max_left _ _,?_⟩
  apply (div_lt_iff₀ ht).mp
  exact hd.trans_le (by exact_mod_cast (le_max_right 2000 d))

theorem exists_scales (c B : ℝ) (hc : 0 ≤ c) : Nonempty (Scales c B) := by
  obtain ⟨D,hD,hDfreq⟩ := exists_base_power
  obtain ⟨J,hJ,hchoice⟩ := EulerPacketCommonScaleChoice.exists_common_guards extraCost D
    (by omega) 4 c geometryConstant gradientConstant gradientConstant hessianConstant 80
    (by norm_num) hc geometryConstant_one gradient_nonneg gradient_nonneg hessian_nonneg
  let η : ℝ := min (1/16) (min activationMargin
    (min (1/(1000000*geometryConstant)) (1/(8*(1+errorConstant frameConstant)))))
  have hη : 0 < η := by
    dsimp only [η]
    positivity [activationMargin_pos,geometryConstant_one,errorConstant_nonneg frameConstant]
  have hηsmall : η ≤ 1/16 := min_le_left _ _
  have hηactivation : η ≤ activationMargin :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hηgeom : η ≤ 1/(1000000*geometryConstant) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηrenew : η ≤ 1/(8*(1+errorConstant frameConstant)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨X₀,δ,hX₀,hδ,hδη,hδhalf,hall⟩ := hchoice η hη
  have hδgeometry : 1000000*geometryConstant*δ ≤ 1 := by
    have hg : 0 < 1000000*geometryConstant := by positivity [geometryConstant_one]
    have hh := (le_div_iff₀ hg).mp (hδη.trans hηgeom)
    nlinarith only [hh]
  have hδrenew : 2*(1+errorConstant frameConstant)*δ ≤ 1/4 := by
    have hg : 0 < 8*(1+errorConstant frameConstant) := by
      positivity [errorConstant_nonneg frameConstant]
    have hh := (le_div_iff₀ hg).mp (hδη.trans hηrenew)
    nlinarith only [hh]
  have hevent : ∀ᶠ X : ℝ in atTop,
      X₀ ≤ X ∧ 48000 ≤ X ∧ FirstScaleGuards J D X ∧
      (∀ n, UniversalFrequency (frequency J X n)) ∧
      (∀ n, B ≤ previousFrequency J D X n) ∧
      baseHorizon J X ≤ 1 ∧
      baseGuardCost J (initialCoefficientCost+1) (initialCoefficientCost+1)
        gradientConstant boundaryLocalizationC2 X ≤ 1/2 := by
    have hp : Tendsto (fun X : ℝ => X^D) atTop atTop :=
      tendsto_pow_atTop (by omega)
    filter_upwards [eventually_ge_atTop X₀,eventually_ge_atTop (48000 : ℝ),
      eventually_firstScaleGuards J (by omega) D hD hDfreq,
      eventually_all_frequency J (by omega) UniversalFrequency universal_frequency_eventually,
      hp.eventually (eventually_ge_atTop B),
      eventually_all_frequency J (by omega) (fun k => B ≤ k) (eventually_ge_atTop B),
      eventually_base_guards J (by omega) (initialCoefficientCost+1) (initialCoefficientCost+1)
        gradientConstant boundaryLocalizationC2 1 zero_lt_one]
      with X hfloor hlarge hfirst hfrequency hprevious hnormal hb
    refine ⟨hfloor,hlarge,hfirst,hfrequency,?_,hb.2.2.1,hb.2.2.2.2.2⟩
    intro n
    cases n with
    | zero => exact hprevious
    | succ n => exact hnormal n
  obtain ⟨X,hfloor,hlarge,hfirst,hfrequency,hprevious,htime,hlocalized⟩ := hevent.exists
  have hdata := hall X hfloor
  have hX : 8 ≤ X := hX₀.trans hfloor
  have hcorrection : SmallSeries (fun n => (frequency J X n)^(-(1/4 : ℝ))) δ := by
    have hh := hdata.2.1 (Sum.inr true)
    change SmallSeries (correctionCostSpec.cost J (scaleSequence J X)) δ at hh
    convert hh using 1
    funext n
    exact (correctionCost_eq J X n).symm
  refine ⟨{
    J := J, D := D, X := X, δ := δ,
    stage_large := hJ, base_power := hD, x_large := hX, delta_pos := hδ,
    delta_small := hδη.trans hηsmall, delta_activation := hδη.trans hηactivation,
    delta_geometry := hδgeometry, actual := hdata.1, first := hfirst,
    normal_frequency := hfrequency, previous_floor := hprevious,
    frequency_series := hdata.2.1 (Sum.inl ()),
    activation_series := hdata.2.1 (Sum.inr false),
    correction_series := hcorrection, bad_series := hdata.2.2.1,
    good_series := hdata.2.2.2.1,
    renewal_series := renewal_series_small (by omega) (by linarith only [hX]) hδ.le
      (by norm_num) hdata.1 (by norm_num; exact hlarge) hδrenew,
    time_small := htime, localized := hlocalized }⟩

namespace Scales

variable {c B : ℝ} (S : Scales c B)

theorem initial_series : SmallSeries (initialIncrement S.J S.X) (2*S.δ) := by
  have h := add_series S.bad_series S.correction_series
  convert h using 1
  · rfl
  · ring

theorem pressure_series : SmallSeries (pressureIncrement S.J S.X) (3*S.δ) := by
  have h := add_series S.good_series S.initial_series
  convert h using 1
  · rfl
  · ring

theorem stage (a β : ℕ → ℝ) (n : ℕ)
    (ha : 1 / 2 ≤ a n) (ha2 : a n ≤ 2)
    (hβ : 1 / 2 ≤ β n * (scaleSequence S.J S.X n) ^ 2)
    (hβ2 : β n * (scaleSequence S.J S.X n) ^ 2 ≤ 2) :
    StageGuards S.J S.D 4 c S.X geometryConstant a β n :=
  EulerParentRenewalPrefix.stage_guards_at S.J S.D S.stage_large 4 c S.X geometryConstant S.δ
    (by norm_num) S.x_large geometryConstant_one (S.delta_small.trans (by norm_num))
    S.delta_geometry S.actual a β n ha ha2 hβ hβ2

end Scales
end EulerPacketInductionScales
