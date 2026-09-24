/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.ENNRealHalfScale

/-!
# Marcinkiewicz interpolation between weak `(1,1)` and strong `(2,2)`

This file develops the analytic ingredients for the Marcinkiewicz interpolation
theorem in the range `1 < p < 2` for a sublinear operator `T` on functions
`Vec3 → ℝ` that is of weak type `(1,1)` with constant `A₁` and of strong type
`(2,2)` with constant `A₂`.  The distribution-function estimate
`|{x | |T f x| > 2λ}| ≤ A₁ ‖f·1_{|f|>λ}‖₁/λ + A₂² ‖f·1_{|f|≤λ}‖₂²/λ²`
and its integral against the layer-cake weight `p t^{p-1}` are proven here; the
interpolation theorem itself, with the explicit constant
`p · 2^p · (A₁/(p-1) + A₂²/(2-p))`, is `interpolation_weak11_strong22` in
`Interpolation.lean`.

The proof works throughout with Lebesgue integrals in `ℝ≥0∞`; measurability of
the input function and of its image under `T` are explicit hypotheses.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Filter


noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- A measurable replacement for the real power `t ^ a`, equal to it for `t > 0`
and vanishing for `t ≤ 0`.  It is used so that the weights occurring in the
layer-cake integrals are globally measurable. -/
def rpowExt (a t : ℝ) : ℝ :=
  if 0 < t then Real.exp (a * Real.log t) else 0

lemma rpowExt_eq {a t : ℝ} (ht : 0 < t) : rpowExt a t = t ^ a := by
  simp only [rpowExt, ht, ↓reduceIte]
  rw [Real.rpow_def_of_pos ht]
  ring_nf

private lemma measurable_rpowExt (a : ℝ) : Measurable (rpowExt a) := by
  unfold rpowExt
  exact Measurable.ite measurableSet_Ioi
    ((measurable_const.mul measurable_id.log).exp) measurable_const

/-! ### The high-frequency contribution -/

/-- Weighted high-amplitude integrand used in the interpolation distribution-function argument. -/
def weightedHighIntegrand (N : Vec3 → ℝ≥0∞) (p : ℝ) (t : ℝ) (x : Vec3) :
    ℝ≥0∞ :=
  ENNReal.ofReal (rpowExt (p - 2) t) *
    (N ⁻¹' Ioi (ENNReal.ofReal (t / 2))).indicator N x

lemma measurable_weightedHighIntegrand {N : Vec3 → ℝ≥0∞} (hN : Measurable N)
    {p : ℝ} :
    AEMeasurable (Function.uncurry (weightedHighIntegrand N p))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hrel : MeasurableSet {q : ℝ × Vec3 |
      ENNReal.ofReal (q.1 / 2) < N q.2} := by
    apply measurableSet_lt
    · exact ENNReal.measurable_ofReal.comp (measurable_fst.div_const 2)
    · exact hN.comp measurable_snd
  have hleft : Measurable (fun q : ℝ × Vec3 ↦
      ENNReal.ofReal (rpowExt (p - 2) q.1)) :=
    ENNReal.measurable_ofReal.comp ((measurable_rpowExt (p - 2)).comp measurable_fst)
  have hright : Measurable (fun q : ℝ × Vec3 ↦
      (N ⁻¹' Ioi (ENNReal.ofReal (q.1 / 2))).indicator N q.2) := by
    have hi : Measurable (fun q : ℝ × Vec3 ↦ N q.2) := hN.comp measurable_snd
    exact hi.indicator hrel
  exact hleft.mul hright |>.aemeasurable

private lemma inner_weightedHigh {N : Vec3 → ℝ≥0∞} {p : ℝ} (hp : 1 < p)
    {x : Vec3} (hx : N x < ∞) :
    ∫⁻ t in Ioi (0 : ℝ), weightedHighIntegrand N p t x =
      ENNReal.ofReal ((2 * (N x).toReal) ^ (p - 1) / (p - 1)) * N x := by
  let y : ℝ := (N x).toReal
  have hy : 0 ≤ y := ENNReal.toReal_nonneg
  have hy2 : 0 ≤ 2 * y := by positivity
  have hset : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      weightedHighIntegrand N p t x = (Ioo (0 : ℝ) (2 * y)).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) * N x) t := by
    filter_upwards [self_mem_ae_restrict
      (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
    have htpos : 0 < t := ht
    have hcond : ENNReal.ofReal (t / 2) < N x ↔ t < 2 * y := by
      by_cases hzero : N x = 0
      · simp [hzero, y, htpos.le]
      · have hpos : 0 < (N x).toReal := ENNReal.toReal_pos hzero hx.ne
        rw [← ENNReal.ofReal_toReal hx.ne, ENNReal.ofReal_lt_ofReal_iff hpos]
        constructor <;> intro h <;> linarith only [h]
    simp only [weightedHighIntegrand, rpowExt_eq htpos, y]
    by_cases h : t < 2 * y
    · change ENNReal.ofReal (t ^ (p - 2)) *
        (N ⁻¹' Ioi (ENNReal.ofReal (t / 2))).indicator N x = _
      rw [indicator_of_mem (show x ∈ N ⁻¹' Ioi (ENNReal.ofReal (t / 2)) from hcond.mpr h),
        indicator_of_mem (show t ∈ Ioo (0 : ℝ) (2 * y) from ⟨htpos, h⟩)]
    · change ENNReal.ofReal (t ^ (p - 2)) *
        (N ⁻¹' Ioi (ENNReal.ofReal (t / 2))).indicator N x = _
      rw [indicator_of_notMem (show x ∉ N ⁻¹' Ioi (ENNReal.ofReal (t / 2)) from
          fun h' ↦ h (hcond.mp h')),
        indicator_of_notMem (show t ∉ Ioo (0 : ℝ) (2 * y) from fun h' ↦ h h'.2)]
      simp
  rw [lintegral_congr_ae hset]
  have hrestrict :
      (∫⁻ t in Ioi (0 : ℝ), (Ioo (0 : ℝ) (2 * y)).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) * N x) t) =
      ∫⁻ t, (Ioo (0 : ℝ) (2 * y)).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) * N x) t := by
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
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) * N x) =ᵐ[volume]
      (Ioc (0 : ℝ) (2 * y)).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) * N x) := by
    filter_upwards [hsets] with t ht
    by_cases h : t ∈ Ioo (0 : ℝ) (2 * y)
    · have h' : t ∈ Ioc (0 : ℝ) (2 * y) := ht.mp h
      simp [h, h']
    · have h' : t ∉ Ioc (0 : ℝ) (2 * y) := fun h' ↦ h (ht.mpr h')
      simp [h, h']
  rw [lintegral_congr_ae hind]
  rw [lintegral_indicator measurableSet_Ioc]
  calc
    ∫⁻ t in Ioc (0 : ℝ) (2 * y), ENNReal.ofReal (t ^ (p - 2)) * N x =
        (∫⁻ t in Ioc (0 : ℝ) (2 * y), ENNReal.ofReal (t ^ (p - 2))) * N x := by
      exact lintegral_mul_const' (N x)
        (fun t : ℝ ↦ ENNReal.ofReal (t ^ (p - 2)))
        (show N x ≠ ∞ from hx.ne)
    _ = ENNReal.ofReal ((2 * (N x).toReal) ^ (p - 1) / (p - 1)) * N x := by
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

lemma inner_High_eq {N : Vec3 → ℝ≥0∞} (hN : Measurable N) {p : ℝ} (t : ℝ) :
    ∫⁻ x, weightedHighIntegrand N p t x =
      ENNReal.ofReal (rpowExt (p - 2) t) *
        ∫⁻ x in N ⁻¹' Ioi (ENNReal.ofReal (t / 2)), N x := by
  simp only [weightedHighIntegrand]
  rw [lintegral_const_mul' (ENNReal.ofReal (rpowExt (p - 2) t))
    (fun x ↦ (N ⁻¹' Ioi (ENNReal.ofReal (t / 2))).indicator N x)
    ENNReal.ofReal_ne_top]
  rw [lintegral_indicator (measurableSet_Ioi.preimage hN) N]

private lemma weighted_high_integral {N : Vec3 → ℝ≥0∞} (hN : Measurable N)
    (hNfin : ∀ x, N x < ∞) {p : ℝ} (hp : 1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (rpowExt (p - 2) t) *
        ∫⁻ x in N ⁻¹' Ioi (ENNReal.ofReal (t / 2)), N x =
      ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * ∫⁻ x, N x ^ p := by
  have hFint (t : ℝ) (ht : 0 < t) :
      ∫⁻ x, weightedHighIntegrand N p t x =
        ENNReal.ofReal (rpowExt (p - 2) t) *
          ∫⁻ x in N ⁻¹' Ioi (ENNReal.ofReal (t / 2)), N x :=
    inner_High_eq hN t
  let _ : SFinite (volume : Measure Vec3) := inferInstance
  have hswap := lintegral_lintegral_swap
    (measurable_weightedHighIntegrand hN (p := p))
  calc
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (rpowExt (p - 2) t) *
        ∫⁻ x in N ⁻¹' Ioi (ENNReal.ofReal (t / 2)), N x =
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, weightedHighIntegrand N p t x := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict
        (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
      rw [hFint t ht]
    _ = ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), weightedHighIntegrand N p t x := hswap
    _ = ∫⁻ x, ENNReal.ofReal ((2 * (N x).toReal) ^ (p - 1) / (p - 1)) * N x := by
      apply lintegral_congr_ae
      filter_upwards [Eventually.of_forall hNfin] with x hx
      exact inner_weightedHigh hp hx
    _ = ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * ∫⁻ x, N x ^ p := by
      have hp1 : 0 < p - 1 := by linarith only [hp]
      have hpoint : ∀ᵐ x ∂volume,
          ENNReal.ofReal ((2 * (N x).toReal) ^ (p - 1) / (p - 1)) * N x =
            ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * N x ^ p := by
        filter_upwards [Eventually.of_forall hNfin] with x hx
        have hy : 0 ≤ (N x).toReal := ENNReal.toReal_nonneg
        have hto : ENNReal.ofReal (N x).toReal = N x :=
          ENNReal.ofReal_toReal hx.ne
        have hpow : N x ^ p = ENNReal.ofReal ((N x).toReal ^ p) := by
          calc
            N x ^ p = (ENNReal.ofReal (N x).toReal) ^ p := by rw [hto]
            _ = ENNReal.ofReal ((N x).toReal ^ p) :=
              ENNReal.ofReal_rpow_of_nonneg hy (by linarith only [hp])
        calc
          ENNReal.ofReal ((2 * (N x).toReal) ^ (p - 1) / (p - 1)) * N x =
              ENNReal.ofReal ((2 * (N x).toReal) ^ (p - 1) / (p - 1)) *
                ENNReal.ofReal (N x).toReal := by rw [hto]
          _ = ENNReal.ofReal
                (((2 * (N x).toReal) ^ (p - 1) / (p - 1)) * (N x).toReal) := by
              rw [ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal ((2 ^ (p - 1) / (p - 1)) * (N x).toReal ^ p) := by
              congr 1
              by_cases hy0 : (N x).toReal = 0
              · simp [hy0, hp1.ne', Real.zero_rpow (by linarith only [hp] : p ≠ 0)]
              · have hypos : 0 < (N x).toReal := lt_of_le_of_ne hy (Ne.symm hy0)
                calc
                  ((2 * (N x).toReal) ^ (p - 1) / (p - 1)) * (N x).toReal =
                      2 ^ (p - 1) / (p - 1) *
                        ((N x).toReal ^ (p - 1) * (N x).toReal) := by
                          rw [Real.mul_rpow (by positivity) hy]
                          ring
                  _ = 2 ^ (p - 1) / (p - 1) * (N x).toReal ^ p := by
                    have hyid : (N x).toReal ^ (p - 1) * (N x).toReal =
                        (N x).toReal ^ p := by
                      calc
                        (N x).toReal ^ (p - 1) * (N x).toReal =
                            (N x).toReal ^ (p - 1) * (N x).toReal ^ 1 := by
                              rw [Real.rpow_one]
                        _ = (N x).toReal ^ ((p - 1) + 1) :=
                          (Real.rpow_add hypos (p - 1) 1).symm
                        _ = (N x).toReal ^ p := by
                          congr 1
                          ring
                    rw [hyid]
          _ = ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) *
                ENNReal.ofReal ((N x).toReal ^ p) := by
              rw [ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * N x ^ p := by rw [hpow]
      rw [lintegral_congr_ae hpoint]
      rw [← lintegral_const_mul' (ENNReal.ofReal (2 ^ (p - 1) / (p - 1)))
        (fun x ↦ N x ^ p) (by exact ENNReal.ofReal_ne_top)]

/-! ### The low-frequency contribution -/

/-- Weighted low-amplitude square integrand used in the interpolation argument. -/
def weightedLowIntegrand (N : Vec3 → ℝ≥0∞) (p : ℝ) (t : ℝ) (x : Vec3) :
    ℝ≥0∞ :=
  ENNReal.ofReal (rpowExt (p - 3) t) *
    (N ⁻¹' Iic (ENNReal.ofReal (t / 2))).indicator (fun x ↦ N x ^ 2) x

private lemma measurable_weightedLowIntegrand {N : Vec3 → ℝ≥0∞} (hN : Measurable N)
    {p : ℝ} :
    AEMeasurable (Function.uncurry (weightedLowIntegrand N p))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hrel : MeasurableSet {q : ℝ × Vec3 |
      N q.2 ≤ ENNReal.ofReal (q.1 / 2)} := by
    apply measurableSet_le
    · exact hN.comp measurable_snd
    · exact ENNReal.measurable_ofReal.comp (measurable_fst.div_const 2)
  have hleft : Measurable (fun q : ℝ × Vec3 ↦
      ENNReal.ofReal (rpowExt (p - 3) q.1)) :=
    ENNReal.measurable_ofReal.comp ((measurable_rpowExt (p - 3)).comp measurable_fst)
  have hright : Measurable (fun q : ℝ × Vec3 ↦
      (N ⁻¹' Iic (ENNReal.ofReal (q.1 / 2))).indicator (fun x ↦ N x ^ 2) q.2) := by
    have hi : Measurable (fun q : ℝ × Vec3 ↦ N q.2 ^ 2) :=
      (hN.comp measurable_snd).pow_const 2
    exact hi.indicator hrel
  exact hleft.mul hright |>.aemeasurable

private lemma inner_weightedLow {N : Vec3 → ℝ≥0∞} {p : ℝ} (hp0 : 0 < p)
    (hp2 : p < 2) {x : Vec3} (hx : N x < ∞) :
    ∫⁻ t in Ioi (0 : ℝ), weightedLowIntegrand N p t x =
      ENNReal.ofReal (2 ^ (p - 2) / (2 - p)) * N x ^ p := by
  by_cases hx0 : N x = 0
  · have hzero : ∀ t : ℝ, weightedLowIntegrand N p t x = 0 := by
      intro t
      rw [weightedLowIntegrand]
      by_cases ht : x ∈ N ⁻¹' Iic (ENNReal.ofReal (t / 2))
      · rw [indicator_of_mem ht, hx0]
        simp
      · rw [indicator_of_notMem ht, mul_zero]
    rw [lintegral_congr (fun t ↦ hzero t), lintegral_zero, hx0,
      ENNReal.zero_rpow_of_pos hp0, mul_zero]
  · let y : ℝ := (N x).toReal
    have hypos : 0 < y := ENNReal.toReal_pos hx0 hx.ne
    have hy : 0 ≤ y := hypos.le
    have hNx : ENNReal.ofReal y = N x := ENNReal.ofReal_toReal hx.ne
    have hcond : ∀ t : ℝ, 0 < t → (N x ≤ ENNReal.ofReal (t / 2) ↔ 2 * y ≤ t) := by
      intro t _
      rw [← hNx, ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ t / 2)]
      constructor <;> intro h <;> linarith only [h]
    have hset : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        weightedLowIntegrand N p t x =
          N x ^ 2 * (Ici (2 * y)).indicator
            (fun t ↦ ENNReal.ofReal (t ^ (p - 3))) t := by
      filter_upwards [self_mem_ae_restrict
        (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
      have htpos : 0 < t := ht
      have hstep : weightedLowIntegrand N p t x =
          ENNReal.ofReal (t ^ (p - 3)) *
            (N ⁻¹' Iic (ENNReal.ofReal (t / 2))).indicator (fun z ↦ N z ^ 2) x := by
        simp only [weightedLowIntegrand, rpowExt_eq htpos]
      rw [hstep]
      by_cases h : 2 * y ≤ t
      · have hxmem : x ∈ N ⁻¹' Iic (ENNReal.ofReal (t / 2)) := (hcond t htpos).mpr h
        rw [indicator_of_mem hxmem,
          indicator_of_mem (show t ∈ Ici (2 * y) from h)]
        ring
      · have hxnot : x ∉ N ⁻¹' Iic (ENNReal.ofReal (t / 2)) :=
          fun hh ↦ h ((hcond t htpos).mp hh)
        rw [indicator_of_notMem hxnot,
          indicator_of_notMem (show t ∉ Ici (2 * y) from h)]
        simp
    rw [lintegral_congr_ae hset]
    rw [lintegral_const_mul' (N x ^ 2)
      (fun t ↦ (Ici (2 * y)).indicator (fun t ↦ ENNReal.ofReal (t ^ (p - 3))) t)
      (ENNReal.pow_lt_top hx).ne]
    have hy2pos : 0 < 2 * y := by positivity
    have hrestrict : (∫⁻ t in Ioi (0 : ℝ), (Ici (2 * y)).indicator
          (fun t ↦ ENNReal.ofReal (t ^ (p - 3))) t) =
        ∫⁻ t in Ioi (2 * y), ENNReal.ofReal (t ^ (p - 3)) := by
      rw [← lintegral_indicator measurableSet_Ioi]
      rw [show (Ioi (0 : ℝ)).indicator
            ((Ici (2 * y)).indicator (fun t ↦ ENNReal.ofReal (t ^ (p - 3)))) =
          (Ici (2 * y)).indicator (fun t ↦ ENNReal.ofReal (t ^ (p - 3))) by
        funext t
        by_cases h : t ∈ Ici (2 * y)
        · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from lt_of_lt_of_le hy2pos h)]
        · rw [indicator_of_notMem h]
          by_cases h0 : t ∈ Ioi (0 : ℝ)
          · rw [indicator_of_mem h0, indicator_of_notMem h]
          · rw [indicator_of_notMem h0]]
      rw [lintegral_indicator measurableSet_Ici]
      rw [← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := 2 * y))]
    rw [hrestrict]
    have hInt : ∫⁻ t in Ioi (2 * y), ENNReal.ofReal (t ^ (p - 3)) =
        ENNReal.ofReal ((2 * y) ^ (p - 2) / (2 - p)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrableOn_Ioi_rpow_of_lt (by linarith only [hp2]) hy2pos)]
      · congr 1
        rw [integral_Ioi_rpow_of_lt (by linarith only [hp2]) hy2pos]
        rw [show p - 3 + 1 = p - 2 by ring]
        rw [show (2 : ℝ) - p = -(p - 2) by ring, div_neg, neg_div]
      · filter_upwards [self_mem_ae_restrict
          (measurableSet_Ioi : MeasurableSet (Ioi (2 * y)))] with t ht
        have ht' : 2 * y < t := ht
        exact Real.rpow_nonneg (by linarith only [hy2pos, ht']) _
    rw [hInt]
    have hNx2 : N x ^ 2 = ENNReal.ofReal (y ^ 2) := by
      rw [← hNx, ENNReal.ofReal_pow hy]
    have hNxp : N x ^ p = ENNReal.ofReal (y ^ p) := by
      rw [← hNx, ENNReal.ofReal_rpow_of_nonneg hy hp0.le]
    rw [hNx2, hNxp]
    have hreal : y ^ 2 * ((2 * y) ^ (p - 2) / (2 - p)) =
        (2 ^ (p - 2) / (2 - p)) * y ^ p := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hy, ← Real.rpow_natCast y 2]
      have hyid : y ^ (2 : ℝ) * y ^ (p - 2) = y ^ p := by
        rw [← Real.rpow_add hypos (2 : ℝ) (p - 2)]
        congr 1
        ring
      calc
        y ^ (2 : ℝ) * (2 ^ (p - 2) * y ^ (p - 2) / (2 - p)) =
            2 ^ (p - 2) / (2 - p) * (y ^ (2 : ℝ) * y ^ (p - 2)) := by ring
        _ = 2 ^ (p - 2) / (2 - p) * y ^ p := by rw [hyid]
    calc
      ENNReal.ofReal (y ^ 2) * ENNReal.ofReal ((2 * y) ^ (p - 2) / (2 - p)) =
          ENNReal.ofReal (y ^ 2 * ((2 * y) ^ (p - 2) / (2 - p))) :=
        (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ y ^ 2)).symm
      _ = ENNReal.ofReal ((2 ^ (p - 2) / (2 - p)) * y ^ p) := by rw [hreal]
      _ = ENNReal.ofReal (2 ^ (p - 2) / (2 - p)) * ENNReal.ofReal (y ^ p) :=
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (p - 2) / (2 - p))

private lemma inner_Low_eq {N : Vec3 → ℝ≥0∞} (hN : Measurable N) {p : ℝ} (t : ℝ) :
    ∫⁻ x, weightedLowIntegrand N p t x =
      ENNReal.ofReal (rpowExt (p - 3) t) *
        ∫⁻ x in N ⁻¹' Iic (ENNReal.ofReal (t / 2)), N x ^ 2 := by
  simp only [weightedLowIntegrand]
  rw [lintegral_const_mul' (ENNReal.ofReal (rpowExt (p - 3) t))
    (fun x ↦ (N ⁻¹' Iic (ENNReal.ofReal (t / 2))).indicator (fun x ↦ N x ^ 2) x)
    ENNReal.ofReal_ne_top]
  rw [lintegral_indicator (measurableSet_Iic.preimage hN) (fun x ↦ N x ^ 2)]

private lemma weighted_low_integral {N : Vec3 → ℝ≥0∞} (hN : Measurable N)
    (hNfin : ∀ x, N x < ∞) {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (rpowExt (p - 3) t) *
        ∫⁻ x in N ⁻¹' Iic (ENNReal.ofReal (t / 2)), N x ^ 2 =
      ENNReal.ofReal (2 ^ (p - 2) / (2 - p)) * ∫⁻ x, N x ^ p := by
  have hFint (t : ℝ) (ht : 0 < t) :
      ∫⁻ x, weightedLowIntegrand N p t x =
        ENNReal.ofReal (rpowExt (p - 3) t) *
          ∫⁻ x in N ⁻¹' Iic (ENNReal.ofReal (t / 2)), N x ^ 2 :=
    inner_Low_eq hN t
  let _ : SFinite (volume : Measure Vec3) := inferInstance
  have hswap := lintegral_lintegral_swap
    (measurable_weightedLowIntegrand hN (p := p))
  calc
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (rpowExt (p - 3) t) *
        ∫⁻ x in N ⁻¹' Iic (ENNReal.ofReal (t / 2)), N x ^ 2 =
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, weightedLowIntegrand N p t x := by
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict
        (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
      rw [hFint t ht]
    _ = ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), weightedLowIntegrand N p t x := hswap
    _ = ∫⁻ x, ENNReal.ofReal (2 ^ (p - 2) / (2 - p)) * N x ^ p := by
      apply lintegral_congr_ae
      filter_upwards [Eventually.of_forall hNfin] with x hx
      exact inner_weightedLow hp0 hp2 hx
    _ = ENNReal.ofReal (2 ^ (p - 2) / (2 - p)) * ∫⁻ x, N x ^ p :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ### The truncation at level `t / 2` and the tail bound -/

/-- The `ℝ≥0∞`-valued modulus of a real function; it converts the real-valued
weak- and strong-type hypotheses into inequalities between Lebesgue integrals. -/
def absE (f : Vec3 → ℝ) : Vec3 → ℝ≥0∞ := fun x ↦ ENNReal.ofReal |f x|

private lemma absE_apply (f : Vec3 → ℝ) (x : Vec3) : absE f x = ENNReal.ofReal |f x| :=
  rfl

lemma measurable_absE {f : Vec3 → ℝ} (hf : Measurable f) : Measurable (absE f) :=
  ENNReal.measurable_ofReal.comp hf.norm

private lemma absE_indicator (s : Set Vec3) (f : Vec3 → ℝ) :
    absE (s.indicator f) = s.indicator (absE f) := by
  funext x
  rw [absE_apply]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

private lemma high_term_eq {A p t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (J : ℝ≥0∞) :
    ENNReal.ofReal (2 * A / t) * J * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (2 * A) * (ENNReal.ofReal (rpowExt (p - 2) t) * J) := by
  have h2A : (0 : ℝ) ≤ 2 * A := mul_nonneg (by norm_num) hA
  have h2At : (0 : ℝ) ≤ 2 * A / t := div_nonneg h2A ht.le
  rw [rpowExt_eq ht, mul_assoc, mul_comm J, ← mul_assoc]
  rw [← ENNReal.ofReal_mul h2At]
  rw [show 2 * A / t * t ^ (p - 1) = 2 * A * t ^ (p - 2) by
    rw [show p - 2 = (p - 1) - 1 by ring, Real.rpow_sub ht (p - 1) 1, Real.rpow_one]
    rw [div_mul_eq_mul_div, mul_div_assoc]]
  rw [ENNReal.ofReal_mul h2A]
  ring

private lemma low_term_eq {A p t : ℝ} (ht : 0 < t) (J : ℝ≥0∞) :
    ENNReal.ofReal (4 * A ^ 2 / t ^ 2) * J * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (4 * A ^ 2) * (ENNReal.ofReal (rpowExt (p - 3) t) * J) := by
  have h4A : (0 : ℝ) ≤ 4 * A ^ 2 := mul_nonneg (by norm_num) (sq_nonneg A)
  have h4At : (0 : ℝ) ≤ 4 * A ^ 2 / t ^ 2 := div_nonneg h4A (by positivity)
  have ht2eq : t ^ (2 : ℝ) = t ^ 2 := Real.rpow_natCast t 2
  have hreal : 4 * A ^ 2 / t ^ 2 * t ^ (p - 1) = 4 * A ^ 2 * t ^ (p - 3) := by
    rw [← ht2eq, show p - 3 = (p - 1) - 2 by ring, Real.rpow_sub ht (p - 1) 2]
    rw [div_mul_eq_mul_div, mul_div_assoc]
  rw [rpowExt_eq ht]
  calc ENNReal.ofReal (4 * A ^ 2 / t ^ 2) * J * ENNReal.ofReal (t ^ (p - 1))
      = (ENNReal.ofReal (4 * A ^ 2 / t ^ 2) * ENNReal.ofReal (t ^ (p - 1))) * J := by
        rw [mul_assoc, mul_comm J, mul_assoc]
    _ = ENNReal.ofReal (4 * A ^ 2 / t ^ 2 * t ^ (p - 1)) * J := by
        rw [← ENNReal.ofReal_mul h4At]
    _ = ENNReal.ofReal (4 * A ^ 2 * t ^ (p - 3)) * J := by rw [hreal]
    _ = (ENNReal.ofReal (4 * A ^ 2) * ENNReal.ofReal (t ^ (p - 3))) * J := by
        rw [ENNReal.ofReal_mul h4A]
    _ = ENNReal.ofReal (4 * A ^ 2) * (ENNReal.ofReal (t ^ (p - 3)) * J) := by
        rw [mul_assoc]

/-- The distribution-function bound obtained by truncating `f` at the level
`t / 2`: the weak `(1,1)` estimate controls the part of `f` above the level and
the strong `(2,2)` estimate (via Chebyshev's inequality) the part below it. -/
lemma tail_bound {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ : ℝ}
    (hTsub : ∀ f g (x : Vec3), |T (f + g) x| ≤ |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → Measurable (T f))
    (hweak : ∀ f, Measurable f → ∀ l : ℝ, 0 < l →
      volume {x | l < |T f x|} ≤
        ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hstrong : ∀ f, Measurable f →
      ∫⁻ x, absE (T f) x ^ 2 ≤ ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    {f : Vec3 → ℝ} (hf : Measurable f) {t : ℝ} (ht : 0 < t) :
    volume {x | t < |T f x|} ≤
      (ENNReal.ofReal (2 * A₁ / t) *
          ∫⁻ x in absE f ⁻¹' Ioi (ENNReal.ofReal (t / 2)), absE f x) +
        (ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) *
          ∫⁻ x in absE f ⁻¹' Iic (ENNReal.ofReal (t / 2)), absE f x ^ 2) := by
  have ht2 : 0 < t / 2 := by linarith only [ht]
  have hNf : Measurable (absE f) := measurable_absE hf
  set s : Set Vec3 := absE f ⁻¹' Ioi (ENNReal.ofReal (t / 2)) with hs
  have hsm : MeasurableSet s := measurableSet_Ioi.preimage hNf
  have hf₁ : Measurable (s.indicator f) := hf.indicator hsm
  have hf₂ : Measurable (sᶜ.indicator f) := hf.indicator hsm.compl
  have hsplit : s.indicator f + sᶜ.indicator f = f := by
    funext x
    rw [Pi.add_apply]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx)]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx)]
      simp
  have hTf : T f = T (s.indicator f + sᶜ.indicator f) := by rw [hsplit]
  have hsub : {x : Vec3 | t < |T f x|} ⊆
      {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x} ∪
        {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    have hx' : t < |T (s.indicator f) x| + |T (sᶜ.indicator f) x| := by
      have hsubx := hTsub (s.indicator f) (sᶜ.indicator f) x
      rw [hTf] at hx
      linarith only [hx, hsubx]
    rcases lt_or_ge (t / 2) (|T (s.indicator f) x|) with ha | ha
    · left
      simp only [Set.mem_ofPred_eq]
      rw [absE_apply, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht2.le]
      exact ha
    · right
      simp only [Set.mem_ofPred_eq]
      rw [absE_apply, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht2.le]
      linarith only [hx', ha]
  have hI1 : ∫⁻ x, absE (s.indicator f) x = ∫⁻ x in s, absE f x := by
    rw [absE_indicator, lintegral_indicator hsm]
  have h1 : volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x} ≤
      ENNReal.ofReal (2 * A₁ / t) * ∫⁻ x in s, absE f x := by
    have hw := hweak (s.indicator f) hf₁ (t / 2) ht2
    have hset : {x : Vec3 | t / 2 < |T (s.indicator f) x|} =
        {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [absE_apply, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht2.le]
    rw [hset] at hw
    calc volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x}
        ≤ ENNReal.ofReal A₁ * (∫⁻ x in s, absE f x) / ENNReal.ofReal (t / 2) := by
          rw [← hI1]
          exact hw
      _ = ENNReal.ofReal (2 * A₁ / t) * ∫⁻ x in s, absE f x :=
          CKN.Foundation.Measure.ofReal_mul_div_ofReal_half ht _
  have hJ2 : ∫⁻ x, absE (sᶜ.indicator f) x ^ 2 = ∫⁻ x in sᶜ, absE f x ^ 2 := by
    have hpow : (fun x ↦ absE (sᶜ.indicator f) x ^ 2) =
        sᶜ.indicator (fun x ↦ absE f x ^ 2) := by
      rw [absE_indicator]
      funext x
      by_cases hx : x ∈ sᶜ
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
        simp
    rw [hpow, lintegral_indicator hsm.compl]
  have h2 : volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} ≤
      ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2 := by
    have hmarkov := mul_meas_ge_le_lintegral (μ := volume)
      ((measurable_absE (hTmeas (sᶜ.indicator f) hf₂)).pow_const 2)
      ((ENNReal.ofReal (t / 2)) ^ 2)
    have hsub2 : {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} ⊆
        {x : Vec3 | (ENNReal.ofReal (t / 2)) ^ 2 ≤ absE (T (sᶜ.indicator f)) x ^ 2} := by
      intro x hx
      exact ENNReal.pow_le_pow_left hx.le
    have hchain : (ENNReal.ofReal (t / 2)) ^ 2 *
        volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} ≤
        ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2 := by
      calc (ENNReal.ofReal (t / 2)) ^ 2 *
            volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x}
          ≤ (ENNReal.ofReal (t / 2)) ^ 2 *
            volume {x : Vec3 | (ENNReal.ofReal (t / 2)) ^ 2 ≤ absE (T (sᶜ.indicator f)) x ^ 2} :=
            mul_le_mul' le_rfl (measure_mono hsub2)
        _ ≤ ∫⁻ x, absE (T (sᶜ.indicator f)) x ^ 2 := hmarkov
        _ ≤ ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2 := by
            rw [← hJ2]
            exact hstrong (sᶜ.indicator f) hf₂
    have hcne : (ENNReal.ofReal (t / 2)) ^ 2 ≠ 0 :=
      ENNReal.pow_ne_zero (by rw [ENNReal.ofReal_ne_zero_iff]; exact ht2) 2
    have hctop : (ENNReal.ofReal (t / 2)) ^ 2 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hvol : volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} ≤
        ENNReal.ofReal (A₂ ^ 2) * (∫⁻ x in sᶜ, absE f x ^ 2) /
          (ENNReal.ofReal (t / 2)) ^ 2 :=
      (ENNReal.le_div_iff_mul_le (Or.inl hcne) (Or.inl hctop)).mpr (by
        rw [mul_comm]
        exact hchain)
    calc volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x}
        ≤ ENNReal.ofReal (A₂ ^ 2) * (∫⁻ x in sᶜ, absE f x ^ 2) /
            (ENNReal.ofReal (t / 2)) ^ 2 := hvol
      _ = ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2 :=
        CKN.Foundation.Measure.ofReal_mul_div_ofReal_half_sq ht _
  have hcalc : volume {x : Vec3 | t < |T f x|} ≤
      (ENNReal.ofReal (2 * A₁ / t) * ∫⁻ x in s, absE f x) +
        (ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2) := by
    calc volume {x : Vec3 | t < |T f x|}
        ≤ volume ({x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x} ∪
            {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x}) :=
          measure_mono hsub
      _ ≤ volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x} +
          volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} :=
          measure_union_le _ _
      _ ≤ (ENNReal.ofReal (2 * A₁ / t) * ∫⁻ x in s, absE f x) +
          (ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2) :=
          add_le_add h1 h2
  have hscompl : absE f ⁻¹' Iic (ENNReal.ofReal (t / 2)) =
      (absE f ⁻¹' Ioi (ENNReal.ofReal (t / 2)))ᶜ := by
    rw [← Set.preimage_compl, Set.compl_Ioi]
  simpa only [hs, hscompl] using hcalc

/-! ### The layer-cake weight and the interpolation constant -/

/-- The weight `p t^{p - 1}` integrates to the power: `∫₀^y p t^{p - 1} = y^p`
for `p > 1`. -/
private lemma integral_pow_weight {p y : ℝ} (hp1 : 1 < p) :
    ∫ t in (0 : ℝ)..y, p * t ^ (p - 1) = y ^ p := by
  have hpm1 : -1 < p - 1 := by linarith only [hp1]
  have hp0 : p ≠ 0 := by linarith only [hp1]
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hpm1)]
  rw [show p - 1 + 1 = p by ring, Real.zero_rpow hp0, sub_zero]
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ _ hp0

/-- The real identity behind the interpolation constant:
`2 A₁ · 2^{p-1}/(p-1) + 4 A₂² · 2^{p-2}/(2-p) = 2^p (A₁/(p-1) + A₂²/(2-p))`. -/
private lemma interp_constant {A₁ A₂ p : ℝ} :
    2 * A₁ * (2 ^ (p - 1) / (p - 1)) + 4 * A₂ ^ 2 * (2 ^ (p - 2) / (2 - p)) =
      2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p)) := by
  have h2a : (2 : ℝ) ^ (p - 1) * 2 = 2 ^ p := by
    have hpow := Real.rpow_add (by norm_num : (0 : ℝ) < 2) (p - 1) 1
    rw [show p - 1 + 1 = p by ring, Real.rpow_one] at hpow
    linarith only [hpow]
  have h2b : (2 : ℝ) ^ (p - 2) * 4 = 2 ^ p := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have hpow := Real.rpow_add (by norm_num : (0 : ℝ) < 2) (p - 2) 2
    rw [show p - 2 + 2 = p by ring, ← h4] at hpow
    linarith only [hpow]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_add]
  nth_rewrite 1 [← h2a]
  nth_rewrite 1 [← h2b]
  ring

/-- Splitting the two `ℝ≥0∞`-coefficients of the tail bound into the single
interpolation constant. -/
private lemma interp_scale {A₁ A₂ p : ℝ} (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2)
    (P : ℝ≥0∞) :
    ENNReal.ofReal (2 * A₁) * (ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * P) +
        ENNReal.ofReal (4 * A₂ ^ 2) * (ENNReal.ofReal (2 ^ (p - 2) / (2 - p)) * P) =
      ENNReal.ofReal (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p))) * P := by
  have hm1 : (0 : ℝ) ≤ 2 * A₁ := by positivity
  have hm2 : (0 : ℝ) ≤ 4 * A₂ ^ 2 := by positivity
  have hb1 : (0 : ℝ) ≤ 2 ^ (p - 1) / (p - 1) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith only [hp1])
  have hb2 : (0 : ℝ) ≤ 2 ^ (p - 2) / (2 - p) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith only [hp2])
  have hc1 : (0 : ℝ) ≤ 2 * A₁ * (2 ^ (p - 1) / (p - 1)) := mul_nonneg hm1 hb1
  have hc2 : (0 : ℝ) ≤ 4 * A₂ ^ 2 * (2 ^ (p - 2) / (2 - p)) := mul_nonneg hm2 hb2
  calc
    ENNReal.ofReal (2 * A₁) * (ENNReal.ofReal (2 ^ (p - 1) / (p - 1)) * P) +
        ENNReal.ofReal (4 * A₂ ^ 2) * (ENNReal.ofReal (2 ^ (p - 2) / (2 - p)) * P)
        = (ENNReal.ofReal (2 * A₁) * ENNReal.ofReal (2 ^ (p - 1) / (p - 1))) * P +
            (ENNReal.ofReal (4 * A₂ ^ 2) * ENNReal.ofReal (2 ^ (p - 2) / (2 - p))) * P := by
          ring
      _ = ENNReal.ofReal (2 * A₁ * (2 ^ (p - 1) / (p - 1))) * P +
            ENNReal.ofReal (4 * A₂ ^ 2 * (2 ^ (p - 2) / (2 - p))) * P := by
          rw [← ENNReal.ofReal_mul hm1, ← ENNReal.ofReal_mul hm2]
      _ = (ENNReal.ofReal (2 * A₁ * (2 ^ (p - 1) / (p - 1))) +
            ENNReal.ofReal (4 * A₂ ^ 2 * (2 ^ (p - 2) / (2 - p)))) * P := by
          rw [← add_mul]
      _ = ENNReal.ofReal (2 * A₁ * (2 ^ (p - 1) / (p - 1)) +
            4 * A₂ ^ 2 * (2 ^ (p - 2) / (2 - p))) * P := by
          rw [← ENNReal.ofReal_add hc1 hc2]
      _ = ENNReal.ofReal (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p))) * P := by
          rw [interp_constant]

/-- The pointwise distribution-function inequality of the tail bound, rewritten
as a product of the two layer-cake weights with the split coefficients. -/
lemma interp_integrand {A₁ A₂ p t : ℝ} (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (ht : 0 < t)
    (H L : ℝ≥0∞) :
    (ENNReal.ofReal (2 * A₁ / t) * H + ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * L) *
        ENNReal.ofReal (p * t ^ (p - 1)) =
      ENNReal.ofReal p *
        (ENNReal.ofReal (2 * A₁) * (ENNReal.ofReal (t ^ (p - 2)) * H) +
          ENNReal.ofReal (4 * A₂ ^ 2) * (ENNReal.ofReal (t ^ (p - 3)) * L)) := by
  have hpnn : (0 : ℝ) ≤ p * t ^ (p - 1) :=
    mul_nonneg (by linarith only [hp1]) (Real.rpow_nonneg ht.le _)
  rw [add_mul, mul_add]
  congr 1
  · calc ENNReal.ofReal (2 * A₁ / t) * H * ENNReal.ofReal (p * t ^ (p - 1))
        = (ENNReal.ofReal (2 * A₁ / t) * H * ENNReal.ofReal (t ^ (p - 1))) *
            ENNReal.ofReal p := by
          rw [ENNReal.ofReal_mul (by linarith only [hp1] : (0 : ℝ) ≤ p)]
          ring
      _ = (ENNReal.ofReal (2 * A₁) * (ENNReal.ofReal (t ^ (p - 2)) * H)) *
            ENNReal.ofReal p := by
          rw [high_term_eq hA₁ ht H, rpowExt_eq ht]
      _ = ENNReal.ofReal p *
            (ENNReal.ofReal (2 * A₁) * (ENNReal.ofReal (t ^ (p - 2)) * H)) := by
          rw [mul_comm]
  · calc ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * L * ENNReal.ofReal (p * t ^ (p - 1))
        = (ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * L * ENNReal.ofReal (t ^ (p - 1))) *
            ENNReal.ofReal p := by
          rw [ENNReal.ofReal_mul (by linarith only [hp1] : (0 : ℝ) ≤ p)]
          ring
      _ = (ENNReal.ofReal (4 * A₂ ^ 2) * (ENNReal.ofReal (t ^ (p - 3)) * L)) *
            ENNReal.ofReal p := by
          rw [low_term_eq ht L, rpowExt_eq ht]
      _ = ENNReal.ofReal p *
            (ENNReal.ofReal (4 * A₂ ^ 2) * (ENNReal.ofReal (t ^ (p - 3)) * L)) := by
          rw [mul_comm]

/-! ### The weighted layer-cake integral -/

/-- The high-frequency tail integral `∫_{N > t/2} N`, viewed as a function of the
level `t`. -/
def highTail (N : Vec3 → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in N ⁻¹' Ioi (ENNReal.ofReal (t / 2)), N x

/-- The low-frequency tail integral `∫_{N ≤ t/2} N ^ 2`, viewed as a function of the
level `t`. -/
def lowTail (N : Vec3 → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in N ⁻¹' Iic (ENNReal.ofReal (t / 2)), N x ^ 2

/-- The layer-cake representation of `∫ |T f| ^ p` as the integral over the level `t`
of the distribution function of `|T f|` against the weight `p t ^ (p - 1)`. -/
lemma layer_cake {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {f : Vec3 → ℝ}
    (hTf : Measurable (T f)) {p : ℝ} (hp1 : 1 < p) :
    ∫⁻ x, absE (T f) x ^ p =
      ∫⁻ t in Ioi (0 : ℝ), volume {x | t < |T f x|} * ENNReal.ofReal (p * t ^ (p - 1)) := by
  have hp0 : (0 : ℝ) ≤ p := by linarith only [hp1]
  have hleft : ∫⁻ x, ENNReal.ofReal (∫ t in (0 : ℝ)..|T f x|, p * t ^ (p - 1)) =
      ∫⁻ x, absE (T f) x ^ p := by
    apply lintegral_congr
    intro x
    rw [integral_pow_weight hp1, absE_apply]
    exact (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (T f x)) hp0).symm
  have h := lintegral_comp_eq_lintegral_meas_lt_mul volume
    (f := fun x : Vec3 => |T f x|) (g := fun t : ℝ => p * t ^ (p - 1))
    (Eventually.of_forall fun x => abs_nonneg (T f x)) hTf.norm.aemeasurable
    (fun _ _ => (intervalIntegral.intervalIntegrable_rpow'
      (by linarith only [hp1] : -1 < p - 1)).const_mul p)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact mul_nonneg hp0 (Real.rpow_nonneg ht.le _))
  exact hleft.symm.trans h

/-- Evaluating the two weighted tail integrals of the distribution-function estimate
against the layer-cake weight and collecting the coefficients into the interpolation
constant. -/
lemma weighted_combined {N : Vec3 → ℝ≥0∞} (hN : Measurable N) (hNfin : ∀ x, N x < ∞)
    {A₁ A₂ p : ℝ} (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * A₁) *
        (ENNReal.ofReal (rpowExt (p - 2) t) * highTail N t)) +
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (4 * A₂ ^ 2) *
        (ENNReal.ofReal (rpowExt (p - 3) t) * lowTail N t)) =
      ENNReal.ofReal (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p))) * ∫⁻ x, N x ^ p := by
  simp only [highTail, lowTail]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, weighted_high_integral hN hNfin hp1,
    weighted_low_integral hN hNfin (by linarith only [hp1]) hp2]
  exact interp_scale hA₁ hp1 hp2 _

end CKN.Foundation.Euclidean
