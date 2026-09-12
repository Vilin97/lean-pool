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
import LeanPool.NavierStokesAndEuler.Euler.PacketPressureSeries
import LeanPool.NavierStokesAndEuler.Euler.ParentRenewalPrefix
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleActual
import Mathlib.Algebra.Order.Ring.Star

/-! A single scale choice for the first packet and every normal stage.
The record contains only numerical inequalities and convergent series;
it does not assume the existence of a packet or of a future frame. -/

section

/-! Reconstruct the numerical source guards from a supplied common
finite cost budget, without making a second choice of the starting stage. -/

@[expose] public section

noncomputable section

namespace EulerPacketSourceScaleChoice

open Real EulerPacketSourceScales EulerPacketSourceTime
  EulerPacketSourceScaleBounds EulerPacketSourceScaleSequence EulerPacketSourceScaleActual

theorem uniformBounds_of_costs (J : ℕ) (hJ : 3 ≤ J) (C c δ : ℝ)
    (hC : 1 ≤ C) (hc : 0 ≤ c) (hδ : 0 ≤ δ) (A : ℕ)
    (x : ℕ → ℝ) (hx1 : ∀ n, 1 ≤ x n)
    (hsmall : ∀ i : SourceCost,
      SmallSeries ((sourceCostSpec C c hC A i).cost J x) (δ/3)) :
    UniformBounds J C c A x δ := by
  have hJ1 : 1 ≤ J := by omega
  have hxp : ∀ n, 0 ≤ x n := fun n => zero_le_one.trans (hx1 n)
  let f := fun i : SourceCost => (sourceCostSpec C c hC A i).cost J x
  have hweak (i : SourceCost) : SmallSeries (f i) δ :=
    (hsmall i).weaken (by linarith only [hδ])
  have hsum : SmallSeries (fun n => f .shear n+f .prior n+f .neighbor n) δ := by
    have hs := ((hsmall .shear).summable.add (hsmall .prior).summable).add (hsmall
        .neighbor).summable
    refine ⟨fun n => add_nonneg (add_nonneg ((hsmall .shear).nonneg n)
      ((hsmall .prior).nonneg n)) ((hsmall .neighbor).nonneg n), hs, ?_⟩
    rw [Summable.tsum_add ((hsmall .shear).summable.add (hsmall .prior).summable)
        (hsmall .neighbor).summable,
      Summable.tsum_add (hsmall .shear).summable (hsmall .prior).summable]
    linarith only [(hsmall .shear).total_le,(hsmall .prior).total_le,(hsmall .neighbor).total_le]
  refine ⟨hsum.mono ?_ ?_, ?_, (hweak .width).mono ?_ ?_,
    (hweak .parent).mono ?_ ?_,(hweak .good).mono ?_ ?_⟩
  · intro n
    have hθ : 0 ≤ sourceTheta J C x n := zero_le_one.trans (sourceTheta_bounds hJ1 hC hx1 n).1
    unfold coefficientCost sourceCoefficientError sourceEpsilon sourceOlderGradient
        sourcePriorError sourceNeighborError
    positivity
  · intro n
    exact sourceCoefficientError_bound J hJ C c hC hc A x hx1 n
  · intro a ha ha₂
    apply (hweak .extra).mono
    · intro n
      have hθ : 0 ≤ sourceTheta J C x n := zero_le_one.trans (sourceTheta_bounds hJ1 hC hx1 n).1
      unfold extraTimeCost sourceNextTimeWidth
      positivity
    · intro n
      exact sourceExtraTime_bound J hJ1 C hC A x hx1 n (a n) (ha n) (ha₂ n)
  · intro n
    unfold sourceTimeRatio
    positivity
  · intro n
    exact sourceTimeRatio_bound J hJ1 x n
  · intro n
    unfold parentSquareRatio
    positivity
  · intro n
    exact (sourceParentSquareRatio_eq J x n).le
  · intro n
    unfold goodCost
    positivity
  · intro n
    exact sourceGoodCost_bound J hJ x n (hxp n)

theorem actualBounds_of_uniform (J D : ℕ) (hJ : 3 ≤ J) (C c X δ : ℝ)
    (hC : 1 ≤ C) (hc : 0 ≤ c) (hX : 1 ≤ X) (hδ : 0 ≤ δ)
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
    (hbase : baseErrorCost J D C X ≤ δ / 2)
    (hn : UniformBounds J C c 60 (scaleSequence J X) (δ / 32)) :
    ActualBounds J D C c X δ := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hw : δ/32 ≤ δ := by linarith only [hδ]
  refine ⟨⟨hn.coefficient.weaken hw,fun a ha ha₂ => (hn.extraTime a ha ha₂).weaken hw,
    hn.width.weaken hw,hn.parent.weaken hw,hn.good.weaken hw⟩,hbaseH,hbaseK,?_⟩
  intro a ha ha₂
  let f : ℕ → ℝ := fun n => 16*coefficientCost J C c 60 (scaleSequence J X) n
  let z : ℕ → ℝ := fun n => if n=0 then baseErrorCost J D C X else 0
  have hf : SmallSeries f (δ/2) := by
    refine ⟨fun n => mul_nonneg (by norm_num) (hn.coefficient.nonneg n),
      hn.coefficient.summable.mul_left 16,?_⟩
    change (∑' n,16*coefficientCost J C c 60 (scaleSequence J X) n) ≤ δ/2
    rw [tsum_mul_left]
    nlinarith only [hn.coefficient.total_le]
  have hz : SmallSeries z (δ/2) := by
    refine ⟨?_,(hasSum_ite_eq 0 (baseErrorCost J D C X)).summable,?_⟩
    · intro n
      exact ite_nonneg (baseErrorCost_nonneg J D C X (zero_le_one.trans hC) hXp.le) le_rfl
    · change (∑' n : ℕ,if n=0 then baseErrorCost J D C X else 0) ≤ δ/2
      rw [tsum_ite_eq]
      exact hbase
  have hsum : SmallSeries (fun n => f n+z n) δ := by
    refine ⟨fun n => add_nonneg (hf.nonneg n) (hz.nonneg n),hf.summable.add hz.summable,?_⟩
    rw [hf.summable.tsum_add hz.summable]
    linarith only [hf.total_le,hz.total_le]
  apply hsum.mono
  · intro n
    unfold geometryErrorCost
    exact mul_nonneg (geometryError_nonneg J D C c X a n (zero_le_one.trans hC) hXp)
      (pow_nonneg (by unfold sourceTheta; positivity) 60)
  · intro n
    exact geometryErrorCost_bound J D hJ C c X hC hX hc a ha ha₂ hbaseH hbaseK n

end EulerPacketSourceScaleChoice

end
end

end

section

/-! One starting index and one final base scale suffice for the actual
geometric guards, pressure series, and any finite list of further packet
frequency comparisons. No independently chosen index is substituted. -/

@[expose] public section

noncomputable section

namespace EulerPacketCommonScaleChoice

open Real Filter EulerScale EulerPacketSourceScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual EulerPacketSourceScaleGuards
  EulerPacketPressureScale EulerPacketGeometryLowBounds
open scoped Topology

theorem exists_common_guards {ι : Type*} [Finite ι] (s : ι → CostSpec)
    (D : ℕ) (hD : 1000 ≤ D) (C c K CM CMn CHn cP : ℝ)
    (hC : 4 ≤ C) (hc : 0 ≤ c) (hK : 1 ≤ K)
    (hCM : 0 ≤ CM) (hCMn : 0 ≤ CMn) (hCHn : 0 ≤ CHn) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ η : ℝ, 0 < η → ∃ X₀ δ : ℝ,
      8 ≤ X₀ ∧ 0 < δ ∧ δ ≤ η ∧ δ ≤ 1/2 ∧
      ∀ X : ℝ, X₀ ≤ X →
        ActualBounds J D C c X δ ∧
        (∀ i, SmallSeries ((s i).cost J (scaleSequence J X)) δ) ∧
        SmallSeries (badCost J C CM CMn CHn cP (scaleSequence J X)) δ ∧
        SmallSeries (fun n => 2*CM*goodRatio*goodCost J (scaleSequence J X) n) δ ∧
        ∀ a β : ℕ → ℝ, (∀ n, 1/2 ≤ a n) → (∀ n, a n ≤ 2) →
          (∀ n, 1/2 ≤ β n*scaleSequence J X n^2) →
          (∀ n, β n*scaleSequence J X n^2 ≤ 2) →
          ∀ n, StageGuards J D C c X K a β n := by
  have hC1 : 1 ≤ C := by linarith only [hC]
  let specs : Sum SourceCost ι → CostSpec
    | .inl i => sourceCostSpec C c hC1 60 i
    | .inr i => s i
  obtain ⟨J,hJ,hchoice⟩ := literal_uniform_choice specs D C CM CMn CHn cP
    (zero_le_one.trans hC1) hCM hCMn hCHn
  refine ⟨J,hJ,?_⟩
  intro η hη
  let δ : ℝ := min η (min (1/2) (1/(1000000*K)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ ≤ η := min_le_left _ _
  have hδhalf : δ ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδK : 1000000*K*δ ≤ 1 := by
    have hh : δ ≤ 1/(1000000*K) := (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (show 0 < 1000000*K by positivity)).mp hh
    nlinarith only [hm]
  obtain ⟨Y,hY,hbounds⟩ := hchoice (δ/96) (by positivity)
  obtain ⟨Z,hZ⟩ := eventually_atTop.mp
    ((baseErrorCost_tendsto_zero J D (by omega) hD C hC1).eventually_le_const
      (by positivity : 0 < δ/2))
  refine ⟨max Y Z,δ,hY.trans (le_max_left _ _),hδ,hδη,hδhalf,?_⟩
  intro X hX
  have hXY : Y ≤ X := (le_max_left _ _).trans hX
  have hXZ : Z ≤ X := (le_max_right _ _).trans hX
  have hX8 : 8 ≤ X := hY.trans hXY
  have hX1 : 1 ≤ X := by linarith only [hX8]
  have hb := hbounds X hXY
  have hx1 : ∀ n, 1 ≤ scaleSequence J X n := quadratic_growth_one_le J (by omega)
    (scaleSequence J X) hX1 (scaleSequence_succ J X)
  have hn : UniformBounds J C c 60 (scaleSequence J X) (δ/32) := by
    apply uniformBounds_of_costs J hJ C c (δ/32) hC1 hc (by positivity) 60
      (scaleSequence J X) hx1
    intro i
    have hi := hb.2.2.1 (Sum.inl i)
    convert hi using 1
    ring
  have ha := actualBounds_of_uniform J D hJ C c X δ hC1 hc hX1 hδ.le
    hb.1 hb.2.1 (hZ X hXZ) hn
  have hweaken : δ/96 ≤ δ := by linarith only [hδ]
  refine ⟨ha,fun i => (hb.2.2.1 (Sum.inr i)).weaken hweaken,
    hb.2.2.2.1.weaken hweaken,hb.2.2.2.2.weaken hweaken,?_⟩
  intro a β ha₁ ha₂ hβ₁ hβ₂ n
  exact stage_guards J D hJ C c X K δ hC hX8 hK hδhalf hδK ha
    a β ha₁ ha₂ hβ₁ hβ₂ n

end EulerPacketCommonScaleChoice

end
end

end

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
