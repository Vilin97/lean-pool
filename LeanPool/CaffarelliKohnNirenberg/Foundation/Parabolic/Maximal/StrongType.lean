/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Maximal.HardyLittlewood
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.LayerCake
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.WeightedKernelIdentity

/-!
# Strong maximal estimates

This file records the direct layer-cake proof of the strong maximal estimate
from the weak estimate in `HardyLittlewood`.  The proof uses truncation at
half the level and Tonelli's theorem, so it does not depend on an abstract
interpolation package.
-/

public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter


noncomputable section

namespace CKN.Foundation.Parabolic

/-- Explicit strong-type coefficient for the parabolic maximal operator. -/
@[expose]
def parabolicMaximalStrongConstant (p : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (10 ^ 5) * ENNReal.ofReal p /
    ENNReal.ofReal (p - 1)

/-- Parabolic ball family used in the strong-type maximal-function proof. -/
abbrev strongMetricBall (z : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r

/-- Part of a nonnegative parabolic source strictly above the truncation level. -/
def highPart (f : ParabolicPoint → ℝ≥0∞) (a : ℝ≥0∞) :
    ParabolicPoint → ℝ≥0∞ := {z | a < f z}.indicator f

/-- Part of a nonnegative parabolic source at or below the truncation level. -/
def lowPart (f : ParabolicPoint → ℝ≥0∞) (a : ℝ≥0∞) :
    ParabolicPoint → ℝ≥0∞ := {z | f z ≤ a}.indicator f

private lemma measurable_highPart {f : ParabolicPoint → ℝ≥0∞} (hf : Measurable f)
    (a : ℝ≥0∞) : Measurable (highPart f a) := by
  exact hf.indicator (measurableSet_Ioi.preimage hf)

private lemma measurable_lowPart {f : ParabolicPoint → ℝ≥0∞} (hf : Measurable f)
    (a : ℝ≥0∞) : Measurable (lowPart f a) := by
  exact hf.indicator (measurableSet_Iic.preimage hf)

private lemma highPart_add_lowPart (f : ParabolicPoint → ℝ≥0∞) (a : ℝ≥0∞) :
    highPart f a + lowPart f a = f := by
  funext z
  by_cases hz : a < f z
  · change {z | a < f z}.indicator f z + {z | f z ≤ a}.indicator f z = f z
    rw [indicator_of_mem (show z ∈ {z | a < f z} from hz),
      indicator_of_notMem (show z ∉ {z | f z ≤ a} from not_le_of_gt hz)]
    simp
  · have hz' : f z ≤ a := le_of_not_gt hz
    change {z | a < f z}.indicator f z + {z | f z ≤ a}.indicator f z = f z
    rw [indicator_of_notMem (show z ∉ {z | a < f z} from hz),
      indicator_of_mem (show z ∈ {z | f z ≤ a} from hz')]
    simp

private lemma parabolicMaximalFunction_add_le
    {f g : ParabolicPoint → ℝ≥0∞} (hf : Measurable f) (_ : Measurable g)
    (z : ParabolicPoint) :
    parabolicMaximalFunction (f + g) z ≤
      parabolicMaximalFunction f z + parabolicMaximalFunction g z := by
  rw [parabolicMaximalFunction, parabolicMaximalFunction]
  refine iSup_le fun c ↦ iSup_le fun r ↦ ?_
  by_cases hz : z ∈ strongMetricBall c r
  · simp only [parabolicMaximalFunction, indicator_of_mem hz]
    calc
      ⨍⁻ y in strongMetricBall c r, (f + g) y ∂volume ≤
      ⨍⁻ y in strongMetricBall c r, f y ∂volume +
            ⨍⁻ y in strongMetricBall c r, g y ∂volume := by
        simp only [Pi.add_apply]
        rw [setLAverage_eq, setLAverage_eq, setLAverage_eq, lintegral_add_left
          (μ := volume.restrict (strongMetricBall c r)) hf, ENNReal.add_div]
      _ ≤ (⨆ c : ParabolicPoint, ⨆ r : ℝ,
          (strongMetricBall c r).indicator
            (fun _ ↦ ⨍⁻ y in strongMetricBall c r, f y ∂volume) z) +
          (⨆ c : ParabolicPoint, ⨆ r : ℝ,
          (strongMetricBall c r).indicator
            (fun _ ↦ ⨍⁻ y in strongMetricBall c r, g y ∂volume) z) := by
        gcongr
        · calc
            ⨍⁻ y in strongMetricBall c r, f y ∂volume =
                (strongMetricBall c r).indicator
                  (fun _ ↦ ⨍⁻ y in strongMetricBall c r, f y ∂volume) z :=
              (indicator_of_mem hz (fun _ ↦ ⨍⁻ y in strongMetricBall c r, f y ∂volume)).symm
            _ ≤ _ := le_iSup₂_of_le c r le_rfl
        · calc
            ⨍⁻ y in strongMetricBall c r, g y ∂volume =
                (strongMetricBall c r).indicator
                  (fun _ ↦ ⨍⁻ y in strongMetricBall c r, g y ∂volume) z :=
              (indicator_of_mem hz (fun _ ↦ ⨍⁻ y in strongMetricBall c r, g y ∂volume)).symm
            _ ≤ _ := le_iSup₂_of_le c r le_rfl
  · simp only [indicator_of_notMem hz, zero_le]

private lemma parabolicMaximalFunction_le_bound
    {f : ParabolicPoint → ℝ≥0∞} {a : ℝ≥0∞} (hf : ∀ z, f z ≤ a)
    (z : ParabolicPoint) : parabolicMaximalFunction f z ≤ a := by
  rw [parabolicMaximalFunction]
  refine iSup_le fun c ↦ iSup_le fun r ↦ ?_
  by_cases hz : z ∈ strongMetricBall c r
  · simp only [indicator_of_mem hz]
    exact (setLAverage_le_essSup (strongMetricBall c r) f).trans
      (essSup_le_of_ae_le a (ae_of_all _ hf))
  · simp only [indicator_of_notMem hz, zero_le]

private lemma parabolicMaximalFunction_high_tail
    {f : ParabolicPoint → ℝ≥0∞} (hf : Measurable f) {l : ℝ} (hl : 0 < l) :
    volume {z | ENNReal.ofReal l < parabolicMaximalFunction f z} ≤
      (ENNReal.ofReal (10 ^ 5) / ENNReal.ofReal (l / 2)) *
        ∫⁻ z in {z | ENNReal.ofReal (l / 2) < f z}, f z := by
  let a : ℝ≥0∞ := ENNReal.ofReal (l / 2)
  let f₁ := highPart f a
  let f₂ := lowPart f a
  have hf₁ : Measurable f₁ := measurable_highPart hf a
  have hf₂ : Measurable f₂ := measurable_lowPart hf a
  have hsplit : f₁ + f₂ = f := highPart_add_lowPart f a
  have hlow : ∀ z, f₂ z ≤ a := by
    intro z
    by_cases hz : f z ≤ a
    · change {z | f z ≤ a}.indicator f z ≤ a
      rw [indicator_of_mem (show z ∈ {z | f z ≤ a} from hz)]
      exact hz
    · change {z | f z ≤ a}.indicator f z ≤ a
      rw [indicator_of_notMem (show z ∉ {z | f z ≤ a} from hz)]
      exact zero_le
  have hM : ∀ z, parabolicMaximalFunction f z ≤
      parabolicMaximalFunction f₁ z + a := by
    intro z
    rw [← hsplit]
    exact (parabolicMaximalFunction_add_le hf₁ hf₂ z).trans
      (add_le_add_right (parabolicMaximalFunction_le_bound hlow z) _)
  have hsubset : {z | ENNReal.ofReal l < parabolicMaximalFunction f z} ⊆
      {z | ENNReal.ofReal (l / 2) < parabolicMaximalFunction f₁ z} := by
    intro z hz
    change ENNReal.ofReal (l / 2) < parabolicMaximalFunction f₁ z
    by_contra hnot
    have hle : parabolicMaximalFunction f₁ z ≤ ENNReal.ofReal (l / 2) :=
      le_of_not_gt hnot
    have hsum : ENNReal.ofReal (l / 2) + ENNReal.ofReal (l / 2) =
        ENNReal.ofReal l := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ l / 2) (by positivity : 0 ≤ l / 2)]
      congr 1
      ring
    exact (not_lt_of_ge ((hM z).trans ((add_le_add hle (by exact le_rfl)).trans_eq hsum))) hz
  have hweak := measure_parabolicMaximalFunction_lt_le f₁
    (l := ENNReal.ofReal (l / 2)) (ENNReal.ofReal_pos.mpr (by positivity))
  calc
    volume {z | ENNReal.ofReal l < parabolicMaximalFunction f z} ≤
        volume {z | ENNReal.ofReal (l / 2) < parabolicMaximalFunction f₁ z} :=
      measure_mono hsubset
    _ ≤ (ENNReal.ofReal (10 ^ 5) / ENNReal.ofReal (l / 2)) * ∫⁻ z, f₁ z := hweak
    _ = (ENNReal.ofReal (10 ^ 5) / ENNReal.ofReal (l / 2)) *
        ∫⁻ z in {z | ENNReal.ofReal (l / 2) < f z}, f z := by
      change (ENNReal.ofReal (10 ^ 5) / ENNReal.ofReal (l / 2)) *
          ∫⁻ z, ({z | ENNReal.ofReal (l / 2) < f z}.indicator f) z = _
      congr 1
      exact lintegral_indicator (measurableSet_Ioi.preimage hf) f


/-- Positive-time power weight for the maximal-function distribution integral. -/
def positiveRpow (p t : ℝ) : ℝ :=
  if 0 < t then Real.exp ((p - 2) * Real.log t) else 0

/-- Weighted upper-tail integrand in the parabolic maximal-function estimate. -/
def weightedTailIntegrand (f : ParabolicPoint → ℝ≥0∞) (p : ℝ)
    (t : ℝ) (z : ParabolicPoint) : ℝ≥0∞ :=
  ENNReal.ofReal (positiveRpow p t) *
    ({z | ENNReal.ofReal (t / 2) < f z}.indicator f) z

private lemma positiveRpow_eq_rpow {p t : ℝ} (ht : 0 < t) :
    positiveRpow p t = t ^ (p - 2) := by
  simp only [positiveRpow, ht, ↓reduceIte]
  rw [Real.rpow_def_of_pos ht]
  ring_nf

private lemma inner_weighted_tail
    {f : ParabolicPoint → ℝ≥0∞} {p : ℝ} (hp : 1 < p)
    {z : ParabolicPoint} (hz : f z < ∞) :
    ∫⁻ t in Ioi (0 : ℝ), weightedTailIntegrand f p t z =
      ENNReal.ofReal ((2 * (f z).toReal) ^ (p - 1) / (p - 1)) * f z := by
  let y : ℝ := (f z).toReal
  have hy : 0 ≤ y := ENNReal.toReal_nonneg
  have hy2 : 0 ≤ 2 * y := by positivity
  have hset : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      weightedTailIntegrand f p t z = (Ioo (0 : ℝ) (2 * y)).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) * f z) t := by
    filter_upwards [self_mem_ae_restrict
      (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
    have htpos : 0 < t := ht
    have hcond : ENNReal.ofReal (t / 2) < f z ↔ t < 2 * y := by
      by_cases hzero : f z = 0
      · simp [hzero, y, htpos.le]
      · have hpos : 0 < (f z).toReal := ENNReal.toReal_pos hzero hz.ne
        rw [← ENNReal.ofReal_toReal hz.ne, ENNReal.ofReal_lt_ofReal_iff hpos]
        constructor <;> intro h <;> linarith only [h]
    simp only [weightedTailIntegrand, positiveRpow_eq_rpow htpos]
    by_cases h : t < 2 * y
    · change ENNReal.ofReal (t ^ (p - 2)) *
        {z | ENNReal.ofReal (t / 2) < f z}.indicator f z = _
      rw [indicator_of_mem (show z ∈ {z | ENNReal.ofReal (t / 2) < f z} from hcond.mpr h),
        indicator_of_mem (show t ∈ Ioo (0 : ℝ) (2 * y) from ⟨htpos, h⟩)]
    · change ENNReal.ofReal (t ^ (p - 2)) *
        {z | ENNReal.ofReal (t / 2) < f z}.indicator f z = _
      rw [indicator_of_notMem (show z ∉ {z | ENNReal.ofReal (t / 2) < f z} from
          fun h' ↦ h (hcond.mp h')),
        indicator_of_notMem (show t ∉ Ioo (0 : ℝ) (2 * y) from fun h' ↦ h h'.2)]
      simp
  rw [lintegral_congr_ae hset]
  have hrestrict :
      (∫⁻ t in Ioi (0 : ℝ), (Ioo (0 : ℝ) (2 * y)).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) * f z) t) =
      ∫⁻ t, (Ioo (0 : ℝ) (2 * y)).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) * f z) t := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    by_cases ht' : t ∈ Ioo (0 : ℝ) (2 * y)
    · simp [ht', Ioo_subset_Ioi_self ht']
    · simp [ht']
  rw [hrestrict]
  have hsets : Ioo (0 : ℝ) (2 * y) =ᵐ[volume] Ioc (0 : ℝ) (2 * y) :=
    Ioo_ae_eq_Ioc' (by simp)
  have hind : (Ioo (0 : ℝ) (2 * y)).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) * f z) =ᵐ[volume]
      (Ioc (0 : ℝ) (2 * y)).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) * f z) := by
    filter_upwards [hsets] with t ht
    by_cases h : t ∈ Ioo (0 : ℝ) (2 * y)
    · have h' : t ∈ Ioc (0 : ℝ) (2 * y) := ht.mp h
      simp [h, h']
    · have h' : t ∉ Ioc (0 : ℝ) (2 * y) := fun h' ↦ h (ht.mpr h')
      simp [h, h']
  rw [lintegral_congr_ae hind]
  rw [lintegral_indicator measurableSet_Ioc]
  calc
    ∫⁻ t in Ioc (0 : ℝ) (2 * y), ENNReal.ofReal (t ^ (p - 2)) * f z =
        (∫⁻ t in Ioc (0 : ℝ) (2 * y), ENNReal.ofReal (t ^ (p - 2))) * f z := by
      exact lintegral_mul_const' (f z)
        (fun t : ℝ ↦ ENNReal.ofReal (t ^ (p - 2)))
        (show f z ≠ ∞ from hz.ne)
    _ = ENNReal.ofReal ((2 * (f z).toReal) ^ (p - 1) / (p - 1)) * f z := by
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · rw [← intervalIntegral.integral_of_le hy2]
        rw [integral_rpow (Or.inl (by linarith only [hp]))]
        have hp1 : 0 < p - 1 := by linarith only [hp]
        have hexp : p - 2 + 1 = p - 1 := by ring
        rw [hexp, Real.zero_rpow hp1.ne']
        congr 2
        ring
      · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith only [hp])).1
      · filter_upwards [self_mem_ae_restrict
          (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) (2 * y)))] with t ht
        exact Real.rpow_nonneg ht.1.le _

private lemma measurable_weightedTailIntegrand
    {f : ParabolicPoint → ℝ≥0∞} (hf : Measurable f) {p : ℝ} :
    AEMeasurable (Function.uncurry (weightedTailIntegrand f p))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hrel : MeasurableSet {q : ℝ × ParabolicPoint |
      ENNReal.ofReal (q.1 / 2) < f q.2} := by
    apply measurableSet_lt
    · exact ENNReal.measurable_ofReal.comp (measurable_fst.div_const 2)
    · exact hf.comp measurable_snd
  have hleft : Measurable (fun q : ℝ × ParabolicPoint ↦
      ENNReal.ofReal (positiveRpow p q.1)) := by
    have hg : Measurable (positiveRpow p) := by
      unfold positiveRpow
      exact Measurable.ite measurableSet_Ioi
        ((measurable_const.mul measurable_id.log).exp) measurable_const
    exact ENNReal.measurable_ofReal.comp (hg.comp measurable_fst)
  have hright : Measurable (fun q : ℝ × ParabolicPoint ↦
      ({z | ENNReal.ofReal (q.1 / 2) < f z}.indicator f) q.2) := by
    have hi : Measurable (fun q : ℝ × ParabolicPoint ↦ f q.2) := hf.comp measurable_snd
    exact hi.indicator hrel
  exact hleft.mul hright |>.aemeasurable

private lemma weighted_tail_integral
    {f : ParabolicPoint → ℝ≥0∞} (hf : Measurable f) {p : ℝ} (hp : 1 < p)
    (hfinite : ∀ᵐ z ∂volume, f z < ∞) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ z in {z | ENNReal.ofReal (t / 2) < f z}, f z =
      ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * ∫⁻ z, f z ^ p := by
  have hFint (t : ℝ) (ht : 0 < t) :
      ∫⁻ z, weightedTailIntegrand f p t z = ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ z in {z | ENNReal.ofReal (t / 2) < f z}, f z := by
    simp only [weightedTailIntegrand, positiveRpow_eq_rpow ht]
    rw [lintegral_const_mul' (ENNReal.ofReal (t ^ (p - 2))) (fun z ↦
      ({z | ENNReal.ofReal (t / 2) < f z}.indicator f) z) ENNReal.ofReal_ne_top]
    change _ * ∫⁻ z, (f ⁻¹' Ioi (ENNReal.ofReal (t / 2))).indicator f z = _
    rw [lintegral_indicator (measurableSet_Ioi.preimage hf) f]
    rfl
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  have hswap := lintegral_lintegral_swap
    (measurable_weightedTailIntegrand hf (p := p))
  calc
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ z in {z | ENNReal.ofReal (t / 2) < f z}, f z =
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ z, weightedTailIntegrand f p t z := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict
        (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
      rw [hFint t ht]
    _ = ∫⁻ z, ∫⁻ t in Ioi (0 : ℝ), weightedTailIntegrand f p t z := hswap
    _ = ∫⁻ z, ENNReal.ofReal ((2 * (f z).toReal) ^ (p - 1) / (p - 1)) * f z := by
      apply lintegral_congr_ae
      filter_upwards [hfinite] with z hz
      exact inner_weighted_tail hp hz
    _ = ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * ∫⁻ z, f z ^ p := by
      have hp1 : 0 < p - 1 := by linarith only [hp]
      have hpoint : ∀ᵐ z ∂volume,
          ENNReal.ofReal ((2 * (f z).toReal) ^ (p - 1) / (p - 1)) * f z =
            ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * f z ^ p := by
        filter_upwards [hfinite] with z hz
        have hy : 0 ≤ (f z).toReal := ENNReal.toReal_nonneg
        have hto : ENNReal.ofReal (f z).toReal = f z :=
          ENNReal.ofReal_toReal hz.ne
        have hpow : f z ^ p = ENNReal.ofReal ((f z).toReal ^ p) := by
          calc
            f z ^ p = (ENNReal.ofReal (f z).toReal) ^ p := by rw [hto]
            _ = ENNReal.ofReal ((f z).toReal ^ p) :=
              ENNReal.ofReal_rpow_of_nonneg hy (by linarith only [hp])
        calc
          ENNReal.ofReal ((2 * (f z).toReal) ^ (p - 1) / (p - 1)) * f z =
              ENNReal.ofReal ((2 * (f z).toReal) ^ (p - 1) / (p - 1)) *
                ENNReal.ofReal (f z).toReal := by rw [hto]
          _ = ENNReal.ofReal
                (((2 * (f z).toReal) ^ (p - 1) / (p - 1)) * (f z).toReal) := by
              rw [ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal ((2 ^ (p - 1) / (p - 1)) * (f z).toReal ^ p) := by
              congr 1
              by_cases hy0 : (f z).toReal = 0
              · simp [hy0, hp1.ne', Real.zero_rpow (by linarith only [hp] : p ≠ 0)]
              · have hypos : 0 < (f z).toReal := lt_of_le_of_ne hy (Ne.symm hy0)
                calc
                  ((2 * (f z).toReal) ^ (p - 1) / (p - 1)) * (f z).toReal =
                      2 ^ (p - 1) / (p - 1) *
                        ((f z).toReal ^ (p - 1) * (f z).toReal) := by
                          rw [Real.mul_rpow (by positivity) hy]
                          ring
                  _ = 2 ^ (p - 1) / (p - 1) * (f z).toReal ^ p := by
                    have hyid : (f z).toReal ^ (p - 1) * (f z).toReal =
                        (f z).toReal ^ p := by
                      calc
                        (f z).toReal ^ (p - 1) * (f z).toReal =
                            (f z).toReal ^ (p - 1) * (f z).toReal ^ 1 := by
                              rw [Real.rpow_one]
                        _ = (f z).toReal ^ ((p - 1) + 1) :=
                          (Real.rpow_add hypos (p - 1) 1).symm
                        _ = (f z).toReal ^ p := by
                          congr 1
                          ring
                    rw [hyid]
          _ = ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) *
                ENNReal.ofReal ((f z).toReal ^ p) := by
              rw [ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * f z ^ p := by rw [hpow]
      rw [lintegral_congr_ae hpoint]
      rw [← lintegral_const_mul' (ENNReal.ofReal (2 ^ (p - 1) / (p - 1)))
        (fun z ↦ f z ^ p) (by exact ENNReal.ofReal_ne_top)]

private lemma highPart_le_rpow
    {f : ParabolicPoint → ℝ≥0∞} {a : ℝ≥0∞} (ha : 0 < a) (ha_top : a ≠ ∞)
    {p : ℝ} (hp : 1 < p) :
    ∀ z, highPart f a z ≤ a ^ (1 - p) * f z ^ p := by
  intro z
  by_cases hz : a < f z
  · unfold highPart
    rw [indicator_of_mem (show z ∈ {z | a < f z} from hz)]
    by_cases htop : f z = ∞
    · have hp0 : 0 < p := lt_trans zero_lt_one hp
      rw [htop, ENNReal.top_rpow_of_pos hp0]
      have hpos : 0 < a ^ (1 - p) := ENNReal.rpow_pos ha ha_top
      simp [hpos.ne']
    · have hzero : f z ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hz.le)
      have hexp : 0 ≤ p - 1 := sub_nonneg.mpr hp.le
      have hpow : a ^ (p - 1) ≤ f z ^ (p - 1) :=
        ENNReal.rpow_le_rpow hz.le hexp
      have hmul : f z * a ^ (p - 1) ≤ f z ^ p := by
        calc
          f z * a ^ (p - 1) ≤ f z * f z ^ (p - 1) := by gcongr
          _ = f z ^ p := by
            calc
              f z * f z ^ (p - 1) = f z ^ 1 * f z ^ (p - 1) := by rw [ENNReal.rpow_one]
              _ = f z ^ (1 + (p - 1)) :=
                (ENNReal.rpow_add 1 (p - 1) hzero htop).symm
              _ = f z ^ p := by
                congr 2
                ring
      have ha_pow_ne_zero : a ^ (p - 1) ≠ 0 :=
        (ENNReal.rpow_pos ha ha_top).ne'
      have ha_pow_ne_top : a ^ (p - 1) ≠ ∞ :=
        (ENNReal.rpow_lt_top_of_nonneg hexp ha_top).ne
      have hdiv : f z ≤ f z ^ p / a ^ (p - 1) :=
        (ENNReal.le_div_iff_mul_le (Or.inl ha_pow_ne_zero)
          (Or.inl ha_pow_ne_top)).2 hmul
      rw [show 1 - p = -(p - 1) by ring, ENNReal.rpow_neg]
      simpa only [ENNReal.div_eq_inv_mul] using hdiv
  · unfold highPart
    rw [indicator_of_notMem (show z ∉ {z | a < f z} from hz)]
    exact bot_le

private lemma highPart_lintegral_le
    {f : ParabolicPoint → ℝ≥0∞} (_ : Measurable f) {a : ℝ≥0∞}
    (ha : 0 < a) (ha_top : a ≠ ∞) {p : ℝ} (hp : 1 < p)
    (_ : ∫⁻ z, f z ^ p ∂volume < ∞) :
    ∫⁻ z, highPart f a z ∂volume ≤ a ^ (1 - p) * ∫⁻ z, f z ^ p ∂volume := by
  calc
    ∫⁻ z, highPart f a z ∂volume ≤ ∫⁻ z, a ^ (1 - p) * f z ^ p := by
      apply lintegral_mono
      exact highPart_le_rpow ha ha_top hp
    _ = a ^ (1 - p) * ∫⁻ z, f z ^ p := by
      apply lintegral_const_mul'
      rw [show 1 - p = -(p - 1) by ring, ENNReal.rpow_neg]
      exact ENNReal.inv_ne_top.mpr (ENNReal.rpow_pos ha ha_top).ne'

private lemma ae_lt_top_parabolicMaximalFunction
    {f : ParabolicPoint → ℝ≥0∞} (hf : Measurable f) {p : ℝ} (hp : 1 < p)
    (hfp : ∫⁻ z, f z ^ p ∂volume < ∞) :
    ∀ᵐ z ∂volume, parabolicMaximalFunction f z < ∞ := by
  have hpow_meas : Measurable (fun z ↦ f z ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hf
  have hf_finite : ∀ᵐ z ∂volume, f z < ∞ := by
    filter_upwards [ae_lt_top hpow_meas hfp.ne] with z hz
    by_cases htop : f z = ∞
    · have hp0 : 0 < p := lt_trans zero_lt_one hp
      simp [htop, ENNReal.top_rpow_of_pos hp0] at hz
    · exact lt_top_iff_ne_top.mpr htop
  let strongC : ℝ≥0∞ := ENNReal.ofReal (10 ^ 5)
  let H : ℝ≥0∞ := ∫⁻ z, f z ^ p ∂volume
  let a : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (((n : ℝ) + 1) / 2)
  let S : ℕ → Set ParabolicPoint :=
    fun n ↦ {z | ENNReal.ofReal ((n : ℝ) + 1) < parabolicMaximalFunction f z}
  let K : ℕ → ℝ≥0∞ := fun n ↦
    strongC / a n * (a n ^ (1 - p) * H)
  have ha_pos (n : ℕ) : 0 < a n := by
    dsimp [a]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have ha_top (n : ℕ) : a n ≠ ∞ := by
    dsimp [a]
    exact ENNReal.ofReal_ne_top
  have hhigh (n : ℕ) :
      ∫⁻ z in {z | a n < f z}, f z < ∞ := by
    have hbound := highPart_lintegral_le hf (ha_pos n) (ha_top n) hp hfp
    have hpow_top : a n ^ (1 - p) < ∞ := by
      rw [show 1 - p = -(p - 1) by ring, ENNReal.rpow_neg]
      exact ENNReal.inv_lt_top.mpr (ENNReal.rpow_pos (ha_pos n) (ha_top n))
    have hprod : a n ^ (1 - p) * H < ∞ :=
      ENNReal.mul_lt_top hpow_top hfp
    have hset : ∫⁻ z in {z | a n < f z}, f z =
        ∫⁻ z, highPart f (a n) z := by
      symm
      exact lintegral_indicator (measurableSet_Ioi.preimage hf) f
    rw [hset]
    exact hbound.trans_lt hprod
  have htail (n : ℕ) : volume (S n) ≤ K n := by
    have h := parabolicMaximalFunction_high_tail hf
      (l := (n : ℝ) + 1) (by positivity)
    have hbound := highPart_lintegral_le hf (ha_pos n) (ha_top n) hp hfp
    have hset : ∫⁻ z in {z | a n < f z}, f z =
        ∫⁻ z, highPart f (a n) z := by
      symm
      exact lintegral_indicator (measurableSet_Ioi.preimage hf) f
    calc
      volume (S n) ≤ strongC / a n * ∫⁻ z in {z | a n < f z}, f z := by
        simpa [S, a, strongC] using h
      _ ≤ K n := by
        dsimp [K]
        gcongr
        rw [hset]
        exact hbound
  have ha_tendsto : Tendsto a atTop (𝓝 ∞) := by
    dsimp [a]
    apply ENNReal.tendsto_ofReal_nhds_top.2
    have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hadd := hnat.atTop_add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1))
    simpa only [Function.comp_apply] using hadd.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hK_tendsto : Tendsto K atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n ↦ strongC / a n) atTop (𝓝 0) := by
      simpa [strongC] using
        ENNReal.Tendsto.const_div ha_tendsto (a := strongC) (by simp [strongC])
    have hpow_top : Tendsto (fun n ↦ a n ^ (p - 1)) atTop (𝓝 ∞) :=
      (ENNReal.tendsto_rpow_at_top (sub_pos.mpr hp)).comp ha_tendsto
    have hpow_zero : Tendsto (fun n ↦ a n ^ (1 - p)) atTop (𝓝 0) := by
      have hinv := tendsto_inv_iff.2 hpow_top
      have hinv' : Tendsto (fun n ↦ (a n ^ (p - 1))⁻¹) atTop (𝓝 0) := by
        simpa only [ENNReal.inv_top] using hinv
      refine hinv'.congr' ?_
      filter_upwards [] with n
      rw [show 1 - p = -(p - 1) by ring, ENNReal.rpow_neg]
    have hprod :
        Tendsto (fun n ↦ (strongC / a n) * a n ^ (1 - p)) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        ENNReal.Tendsto.mul hdiv (by simp) hpow_zero (by simp)
    simpa [K, mul_assoc] using
      ENNReal.Tendsto.mul_const hprod (by right; exact hfp.ne)
  have htopzero : volume {z | parabolicMaximalFunction f z = ∞} = 0 := by
    apply le_antisymm
    · apply ge_of_tendsto hK_tendsto
      filter_upwards [] with n
      calc
        volume {z | parabolicMaximalFunction f z = ∞} ≤ volume (S n) := by
          apply measure_mono
          intro z hz
          change parabolicMaximalFunction f z = ∞ at hz
          change ENNReal.ofReal ((n : ℝ) + 1) < parabolicMaximalFunction f z
          rw [hz]
          exact ENNReal.ofReal_lt_top
        _ ≤ K n := htail n
    · exact bot_le
  simpa only [ae_iff, ENNReal.not_lt_top, not_not] using htopzero

theorem lintegral_rpow_parabolicMaximalFunction_le
    {f : ParabolicPoint → ℝ≥0∞} (hf : Measurable f) {p : ℝ} (hp : 1 < p)
    (hfp : ∫⁻ z, f z ^ p ∂volume < ∞) :
    ∫⁻ z, parabolicMaximalFunction f z ^ p ∂volume ≤
      parabolicMaximalStrongConstant p * ∫⁻ z, f z ^ p ∂volume := by
  have hMfinite := ae_lt_top_parabolicMaximalFunction hf hp hfp
  rw [CKN.Foundation.Measure.lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul volume
    (measurable_parabolicMaximalFunction f) (lt_trans zero_lt_one hp) hMfinite]
  let strongC : ℝ≥0∞ := ENNReal.ofReal (10 ^ 5)
  have hC_top : strongC ≠ ∞ := by
    dsimp [strongC]
    exact ENNReal.ofReal_ne_top
  have hf_finite : ∀ᵐ z ∂volume, f z < ∞ := by
    have hpow_meas : Measurable (fun z ↦ f z ^ p) :=
      ENNReal.continuous_rpow_const.measurable.comp hf
    filter_upwards [ae_lt_top hpow_meas hfp.ne] with z hz
    by_cases htop : f z = ∞
    · have hp0 : 0 < p := lt_trans zero_lt_one hp
      simp [htop, ENNReal.top_rpow_of_pos hp0] at hz
    · exact lt_top_iff_ne_top.mpr htop
  calc
    ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        volume {z | ENNReal.ofReal t < parabolicMaximalFunction f z} *
          ENNReal.ofReal (t ^ (p - 1)) ≤
        ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          (strongC / ENNReal.ofReal (t / 2) *
            ∫⁻ z in {z | ENNReal.ofReal (t / 2) < f z}, f z) *
            ENNReal.ofReal (t ^ (p - 1)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict
        (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
      have htail := parabolicMaximalFunction_high_tail hf
        (l := t) (show 0 < t from ht)
      exact mul_le_mul_of_nonneg_right (by simpa [strongC] using htail)
        (by positivity)
    _ = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          (2 * strongC) *
            (ENNReal.ofReal (t ^ (p - 2)) *
              ∫⁻ z in {z | ENNReal.ofReal (t / 2) < f z}, f z) := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict
        (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
      exact CKN.Foundation.Measure.div_ofReal_half_mul_ofReal_rpow_sub_one ht
    _ = ENNReal.ofReal p *
          ((2 * strongC) * ∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (p - 2)) *
              ∫⁻ z in {z | ENNReal.ofReal (t / 2) < f z}, f z) := by
      congr 1
      rw [lintegral_const_mul' (2 * strongC) _]
      exact ENNReal.mul_ne_top (by norm_num) hC_top
    _ = ENNReal.ofReal p *
          ((2 * strongC) *
            (ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) *
              ∫⁻ z, f z ^ p)) := by
      rw [weighted_tail_integral hf hp hf_finite]
    _ = parabolicMaximalStrongConstant p * ∫⁻ z, f z ^ p := by
      dsimp [parabolicMaximalStrongConstant, strongC]
      have hp0 : 0 < p := lt_trans zero_lt_one hp
      have hp1 : 0 < p - 1 := sub_pos.mpr hp
      rw [ENNReal.ofReal_div_of_pos hp1]
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp1.le]
      have htwo : (2 : ℝ≥0∞) * ENNReal.ofReal 2 ^ (p - 1) = (2 : ℝ≥0∞) ^ p := by
        have h := ENNReal.rpow_add (1 : ℝ) (p - 1)
          (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        rw [ENNReal.rpow_one] at h
        calc
          (2 : ℝ≥0∞) * ENNReal.ofReal 2 ^ (p - 1) =
              ENNReal.ofReal 2 ^ (p - 1) * (2 : ℝ≥0∞) := by ac_rfl
          _ = 2 ^ (1 + (p - 1)) := by
            rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by norm_num]
            simpa [mul_comm] using h.symm
          _ = (2 : ℝ≥0∞) ^ p := by
            congr 2
            ring
      rw [← htwo]
      simp only [ENNReal.div_eq_inv_mul]
      ac_rfl

theorem lintegral_rpow_parabolicMaximalFunction_ofReal_le
    (f : ParabolicPoint → ℝ) (hf : Measurable f) {p : ℝ} (hp : 1 < p)
    (hfp : ∫⁻ z, (ENNReal.ofReal ‖f z‖) ^ p ∂volume < ∞) :
    ∫⁻ z, parabolicMaximalFunction (fun z ↦ ENNReal.ofReal ‖f z‖) z ^ p ∂volume ≤
      parabolicMaximalStrongConstant p * ∫⁻ z, (ENNReal.ofReal ‖f z‖) ^ p ∂volume := by
  exact lintegral_rpow_parabolicMaximalFunction_le
    (hf.norm.ennreal_ofReal) hp hfp

theorem setLIntegral_rpow_parabolicMaximalFunction_indicator_le
    (U : Set ParabolicPoint) (hU : MeasurableSet U) (_ : IsOpen U)
    (_ : Bornology.IsBounded U) {f : ParabolicPoint → ℝ≥0∞}
    (hf : Measurable f) {p : ℝ} (hp : 1 < p)
    (hfp : ∫⁻ z in U, f z ^ p ∂volume < ∞) :
    ∫⁻ z in U, parabolicMaximalFunction (U.indicator f) z ^ p ∂volume ≤
      parabolicMaximalStrongConstant p * ∫⁻ z in U, f z ^ p ∂volume := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpow_indicator : (fun z ↦ (U.indicator f z) ^ p) =
      U.indicator (fun z ↦ f z ^ p) := by
    funext z
    by_cases hz : z ∈ U
    · simp [hz]
    · simp [hz, hp0]
  have hglobal : ∫⁻ z, (U.indicator f z) ^ p ∂volume < ∞ := by
    rw [hpow_indicator, lintegral_indicator hU]
    exact hfp
  have hmain := lintegral_rpow_parabolicMaximalFunction_le
    (hf.indicator hU) hp hglobal
  calc
    ∫⁻ z in U, parabolicMaximalFunction (U.indicator f) z ^ p ∂volume ≤
        ∫⁻ z, parabolicMaximalFunction (U.indicator f) z ^ p ∂volume :=
      setLIntegral_le_lintegral U _
    _ ≤ parabolicMaximalStrongConstant p * ∫⁻ z, (U.indicator f z) ^ p ∂volume := hmain
    _ = parabolicMaximalStrongConstant p * ∫⁻ z in U, f z ^ p ∂volume := by
      rw [hpow_indicator, lintegral_indicator hU]

end CKN.Foundation.Parabolic
