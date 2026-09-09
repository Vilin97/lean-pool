/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Kinetic action bounds for flow escape

These estimates are independent of Euler and of the Comparator statement.
They expose the flow and energy hypotheses needed to exclude arrival from
spatial infinity. In particular, no global bound on the pointwise velocity
or its derivatives is used in the escape estimate.
-/

@[expose] public section


noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace Euler.ComparatorBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Cauchy--Schwarz for a vector-valued integral against a finite measure. -/
theorem norm_integral_sq_le_action
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (V : α → E) (hV : MemLp V 2 μ) :
    ‖∫ t, V t ∂μ‖ ^ 2 ≤ μ.real univ * (∫ t, ‖V t‖ ^ 2 ∂μ) := by
  have hp : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hn : MemLp (fun t => ‖V t‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hV.norm
  have ho : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := memLp_const 1
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (Eventually.of_forall (fun t => norm_nonneg (V t)))
    (Eventually.of_forall (fun _ => show (0 : ℝ) ≤ 1 by norm_num)) hn ho
  have hi : (∫ t, ‖V t‖ ∂μ) ≤
      Real.sqrt (∫ t, ‖V t‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ) := by
    simpa only [mul_one, Real.rpow_two, Real.one_rpow, integral_const,
      smul_eq_mul, Real.sqrt_eq_rpow, one_pow] using h
  have hs := pow_le_pow_left₀ (norm_nonneg _) ((norm_integral_le_integral_norm V).trans hi) 2
  simpa only [mul_pow,
    Real.sq_sqrt (integral_nonneg (fun t => sq_nonneg ‖V t‖)),
    Real.sq_sqrt (measureReal_nonneg : 0 ≤ μ.real univ), mul_comm] using hs

/-- The displacement of a differentiable curve is bounded by its kinetic action. -/
theorem curve_displacement_sq_le_action
    (a b : ℝ) (hab : a ≤ b) (X V : ℝ → E)
    (hX : ContinuousOn X (Icc a b))
    (hV : ContinuousOn V (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt X (V t) t) :
    ‖X b - X a‖ ^ 2 ≤ (b - a) * (∫ t in Icc a b, ‖V t‖ ^ 2) := by
  have hmem : MemLp V 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq_norm
      (hV.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc)).mpr
      (hV.norm.pow 2).integrableOn_Icc
  have h := norm_integral_sq_le_action
    (volume.restrict (Icc a b)) V hmem
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have hint : (∫ t in Icc a b, V t) = X b - X a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hX hderiv
      (hV.intervalIntegrable_of_Icc hab)
  rwa [hmass, hint] at h

/-- A curve reaching radius `R` from radius at most `K` pays at least
`(R-K)^2 / T` in action over `[0,T]`. -/
theorem curve_escape_sq_le_action
    (T K R s : ℝ) (hT : 0 ≤ T) (hKR : K ≤ R) (hs : s ∈ Icc 0 T)
    (X V : ℝ → E) (hX : ContinuousOn X (Icc 0 T))
    (hV : ContinuousOn V (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt X (V t) t)
    (hstart : ‖X 0‖ ≤ K) (hescape : R ≤ ‖X s‖) :
    (R - K) ^ 2 ≤ T * (∫ t in Icc 0 T, ‖V t‖ ^ 2) := by
  have hsub : Icc (0 : ℝ) s ⊆ Icc 0 T := Icc_subset_Icc le_rfl hs.2
  have hd := curve_displacement_sq_le_action 0 s hs.1 X V (hX.mono hsub)
    (hV.mono hsub) (fun t ht => hderiv t ⟨ht.1, ht.2.trans_le hs.2⟩)
  have hdist : R - K ≤ ‖X s - X 0‖ := by
    have hh := norm_sub_norm_le (X s) (X 0)
    linarith
  have hsq := pow_le_pow_left₀ (sub_nonneg.mpr hKR) hdist 2
  have hi : IntegrableOn (fun t => ‖V t‖ ^ 2) (Icc 0 T) :=
    (hV.norm.pow 2).integrableOn_Icc
  have hi_mono : (∫ t in Icc 0 s, ‖V t‖ ^ 2) ≤
      ∫ t in Icc 0 T, ‖V t‖ ^ 2 :=
    integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (Eventually.of_forall (fun t => sq_nonneg ‖V t‖)) hi
  calc
    (R - K) ^ 2 ≤ ‖X s - X 0‖ ^ 2 := hsq
    _ ≤ s * (∫ t in Icc 0 s, ‖V t‖ ^ 2) := by simpa using hd
    _ ≤ T * (∫ t in Icc 0 T, ‖V t‖ ^ 2) :=
      mul_le_mul hs.2 hi_mono (integral_nonneg (fun t => sq_nonneg ‖V t‖)) hT

omit [CompleteSpace E] [NormedSpace ℝ E] in
/-- A measure-preserving flow converts the Eulerian energy bound into an
integrable action with the same time-integrated bound. -/
theorem flow_action_integrable_and_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure β) [SFinite μ]
    (X : α → β → β) (V : α → β → E)
    (hX : ∀ t, MeasurePreserving (X t) μ μ)
    (hXe : ∀ t, MeasurableEmbedding (X t))
    (hm : AEStronglyMeasurable
      (fun tx : α × β => ‖V tx.1 (X tx.1 tx.2)‖ ^ 2) (ν.prod μ))
    (hV : ∀ t, MemLp (V t) 2 μ)
    (energy : ℝ) (henergy : ∀ t, (∫ x, ‖V t x‖ ^ 2 ∂μ) ≤ energy) :
    Integrable (fun x => ∫ t, ‖V t (X t x)‖ ^ 2 ∂ν) μ ∧
      (∫ x, ∫ t, ‖V t (X t x)‖ ^ 2 ∂ν ∂μ) ≤ ν.real univ * energy := by
  have hinner (t : α) :
      (∫ x, ‖V t (X t x)‖ ^ 2 ∂μ) = ∫ x, ‖V t x‖ ^ 2 ∂μ :=
    (hX t).integral_comp (hXe t) (fun x => ‖V t x‖ ^ 2)
  have hbound (t : α) : (∫ x, ‖V t (X t x)‖ ^ 2 ∂μ) ≤ energy := by
    rw [hinner]
    exact henergy t
  have houter : Integrable (fun t => ∫ x, ‖V t (X t x)‖ ^ 2 ∂μ) ν := by
    apply (integrable_const energy).mono' hm.integral_prod_right'
    exact Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun x => sq_nonneg ‖V t (X t x)‖))]
      exact hbound t)
  have hprod : Integrable
      (fun tx : α × β => ‖V tx.1 (X tx.1 tx.2)‖ ^ 2) (ν.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    constructor
    · exact Eventually.of_forall (fun t =>
        (memLp_two_iff_integrable_sq_norm
          ((hV t).comp_measurePreserving (hX t)).aestronglyMeasurable).mp
            ((hV t).comp_measurePreserving (hX t)))
    · simpa only [norm_pow, norm_norm] using houter
  refine ⟨hprod.integral_prod_right, ?_⟩
  calc
    (∫ x, ∫ t, ‖V t (X t x)‖ ^ 2 ∂ν ∂μ) =
        ∫ t, ∫ x, ‖V t (X t x)‖ ^ 2 ∂μ ∂ν :=
      (integral_integral_swap hprod).symm
    _ ≤ ∫ _ : α, energy ∂ν := integral_mono houter (integrable_const _) hbound
    _ = ν.real univ * energy := by rw [integral_const, smul_eq_mul]

/-- Markov's action estimate for any measurable family of escaping curves.
The hypothesis on the integral of `action` is obtained by volume preservation
and the Eulerian kinetic-energy bound. -/
theorem escape_measure_le_of_action
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S) (hfinite : μ S ≠ ⊤)
    (action : α → ℝ) (ha : Integrable action μ)
    (ha0 : ∀ x, 0 ≤ action x) (T K R energy : ℝ)
    (hT : 0 ≤ T) (hKR : K < R)
    (haenergy : (∫ x, action x ∂μ) ≤ T * energy)
    (hescape : ∀ x ∈ S, (R - K) ^ 2 ≤ T * action x) :
    μ.real S ≤ energy * T ^ 2 / (R - K) ^ 2 := by
  have : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hfinite.lt_top⟩
  have hb : (R - K) ^ 2 * μ.real S ≤ T * (∫ x, action x ∂μ) := by
    calc
      (R - K) ^ 2 * μ.real S = ∫ _ in S, (R - K) ^ 2 ∂μ := by
        simp only [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in S, T * action x ∂μ := by
        apply integral_mono_ae (integrable_const _) ((ha.const_mul T).restrict)
        filter_upwards [ae_restrict_mem hS] with x hx
        exact hescape x hx
      _ ≤ ∫ x, T * action x ∂μ :=
        integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall (fun x => mul_nonneg hT (ha0 x))) (ha.const_mul T)
      _ = T * (∫ x, action x ∂μ) := integral_const_mul _ _
  apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hKR))).mpr
  have hc := mul_le_mul_of_nonneg_left haenergy hT
  nlinarith

/-- A finite-energy measure-preserving flow can carry at most
`energy * T^2 / (R-K)^2` measure of points from radius `K` to radius `R`.
The escaped set need not have a measurable choice of its hitting time. -/
theorem flow_escape_measure_le
    [MeasurableSpace E] (μ : Measure E) [SFinite μ]
    (T K R energy : ℝ) (hT : 0 ≤ T) (hKR : K < R)
    (X V : ℝ → E → E)
    (hX : ∀ t, MeasurePreserving (X t) μ μ)
    (hXe : ∀ t, MeasurableEmbedding (X t))
    (hm : AEStronglyMeasurable
      (fun tx : ℝ × E => ‖V tx.1 (X tx.1 tx.2)‖ ^ 2)
      ((volume.restrict (Icc 0 T)).prod μ))
    (hV : ∀ t, MemLp (V t) 2 μ)
    (henergy : ∀ t, (∫ x, ‖V t x‖ ^ 2 ∂μ) ≤ energy)
    (hcurve : ∀ x, ContinuousOn (fun t => X t x) (Icc 0 T))
    (hspeed : ∀ x, ContinuousOn (fun t => V t (X t x)) (Icc 0 T))
    (hderiv : ∀ x t, t ∈ Ioo 0 T →
      HasDerivAt (fun r => X r x) (V t (X t x)) t)
    (S : Set E) (hS : MeasurableSet S) (hfinite : μ S ≠ ⊤)
    (hstart : ∀ x ∈ S, ‖X 0 x‖ ≤ K)
    (hescape : ∀ x ∈ S, ∃ t ∈ Icc 0 T, R ≤ ‖X t x‖) :
    μ.real S ≤ energy * T ^ 2 / (R - K) ^ 2 := by
  let action : E → ℝ := fun x => ∫ t in Icc 0 T, ‖V t (X t x)‖ ^ 2
  obtain ⟨ha, hbound⟩ := flow_action_integrable_and_bound
    (volume.restrict (Icc 0 T)) μ X V hX hXe hm hV energy henergy
  have hmass : (volume.restrict (Icc 0 T)).real univ = T := by
    simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      sub_zero, ENNReal.toReal_ofReal hT]
  rw [hmass] at hbound
  apply escape_measure_le_of_action μ S hS hfinite action ha
    (fun x => integral_nonneg (fun t => sq_nonneg ‖V t (X t x)‖))
    T K R energy hT hKR hbound
  intro x hx
  obtain ⟨s, hs, hsR⟩ := hescape x hx
  exact curve_escape_sq_le_action T K R s hT hKR.le hs
    (fun t => X t x) (fun t => V t (X t x)) (hcurve x) (hspeed x)
    (hderiv x) (hstart x hx) hsR

end Euler.ComparatorBridge
