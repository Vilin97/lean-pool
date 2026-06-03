/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# L² Bounds for Time Integrals

This file proves L² bounds on time averages and parametric integrals.

## Main Results

1. `sq_setIntegral_le_measure_mul_setIntegral_sq_proved` - Cauchy-Schwarz for set integrals (Hölder)
2. `L2_time_average_bound` - L² bound for time averages (Cauchy-Schwarz + Fubini)
3. `time_average_memLp_two` - Time average is in L² (corollary of 2)
4. `memLp_prod_of_uniform_slicewise_bound` - L² on product from uniform slicewise bounds
5. `gff_time_integral_aestronglyMeasurable_proved` - Parametric time integral is measurable
6. `gff_covariance_norm_integrableOn_slice_proved` - Covariance norm integrable on slices
7. `double_integral_polynomial_decay_bound_proved` - Double integral bound for polynomial decay
kernels
8. `minkowski_weighted_L2_sum_proved` - Minkowski inequality for weighted L² sums

## Mathematical Background

The key tools are:
- Cauchy-Schwarz: ‖∫ f‖² ≤ (b-a) · ∫ ‖f‖²
- Fubini-Tonelli: swap order of integration
- L² is a Hilbert space: Minkowski inequality

## References

- Billingsley "Probability and Measure", Ch. 7
- Folland "Real Analysis", Thm. 2.37 (Fubini-Tonelli)
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace OSforGFF

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## L² Bound for Time Averages

The main result: if A : ℝ → Ω → ℂ has uniform L² bound over [0,T],
then the time average (1/T)∫₀ᵀ A_s ds is in L² with the same bound.

Proof outline:
1. Cauchy-Schwarz pointwise: ‖∫₀ᵀ A_s(ω) ds‖² ≤ T · ∫₀ᵀ ‖A_s(ω)‖² ds
2. Scale by (1/T)²: ‖(1/T)∫...‖² ≤ (1/T) · ∫₀ᵀ ‖A_s(ω)‖² ds
3. Integrate over Ω: ∫_Ω ‖(1/T)∫...‖² dμ ≤ (1/T) · ∫_Ω ∫₀ᵀ ‖A_s‖² ds dμ
4. Fubini: = (1/T) · ∫₀ᵀ (∫_Ω ‖A_s‖² dμ) ds
5. Uniform bound: ≤ (1/T) · ∫₀ᵀ M_sq ds = (1/T) · T · M_sq = M_sq
-/

/-! ## Cauchy-Schwarz for Set Integrals

The L² Cauchy-Schwarz inequality |⟨1, f⟩|² ≤ ‖1‖² · ‖f‖² applied to integrals:
  ‖∫_[a,b] f‖² ≤ (b-a) · ∫_[a,b] ‖f‖²

Proof uses Hölder's inequality with p = q = 2, taking one function to be constant 1.
-/

/-- **Cauchy-Schwarz for set integrals.**

For f : ℝ → ℂ with ‖f‖² integrable on [a,b]:
  ‖∫_[a,b] f(x) dx‖² ≤ (b-a) · ∫_[a,b] ‖f(x)‖² dx

This is |⟨1, f⟩|² ≤ ‖1‖² · ‖f‖² in L².
-/
theorem sq_setIntegral_le_measure_mul_setIntegral_sq_proved
    {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_sq : IntegrableOn (fun x => ‖f x‖ ^ 2) (Icc a b) volume) :
    ‖∫ x in Icc a b, f x‖ ^ 2 ≤ (b - a) * ∫ x in Icc a b, ‖f x‖ ^ 2 := by
  by_cases hf_aesm : AEStronglyMeasurable f (volume.restrict (Icc a b))
  · -- Use Hölder with p = q = 2
    have hpq : (2:ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
    haveI : IsFiniteMeasure (volume.restrict (Icc a b)) := by
      exact Real.isFiniteMeasure_restrict_Icc a b
    have h_memLp1 : MemLp (fun (_ : ℝ) => (1:ℂ)) (ENNReal.ofReal 2)
        (volume.restrict (Icc a b)) := by
      rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num]; exact memLp_const 1
    have h_memLpf : MemLp f (ENNReal.ofReal 2) (volume.restrict (Icc a b)) := by
      rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num]
      exact (memLp_two_iff_integrable_sq_norm hf_aesm).mpr hf_sq
    -- Hölder: ∫ ‖1‖ * ‖f‖ ≤ (∫ ‖1‖²)^(1/2) * (∫ ‖f‖²)^(1/2)
    have h_holder := integral_mul_norm_le_Lp_mul_Lq hpq h_memLp1 h_memLpf
    rw [show (∫ x in Icc a b, ‖(fun _ => (1:ℂ)) x‖ * ‖f x‖) =
        ∫ x in Icc a b, ‖f x‖ from by congr 1; ext x; simp] at h_holder
    rw [show (∫ x in Icc a b, ‖(fun _ => (1:ℂ)) x‖ ^ (2:ℝ)) = b - a from by
      simp; linarith] at h_holder
    -- Chain: ‖∫f‖ ≤ ∫‖f‖ ≤ (b-a)^(1/2) * (∫‖f‖²)^(1/2), then square
    have h_sq := pow_le_pow_left₀ (norm_nonneg _)
      (le_trans (norm_integral_le_integral_norm (f := f)) h_holder) 2
    rw [mul_pow] at h_sq
    -- Simplify (x^(1/2))² = x for both factors
    rw [show ((b - a) ^ ((1:ℝ)/2)) ^ 2 = b - a from by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (sub_nonneg.mpr hab)]; norm_num,
      show ((∫ x in Icc a b, ‖f x‖ ^ (2:ℝ)) ^ ((1:ℝ)/2)) ^ 2 =
          ∫ x in Icc a b, ‖f x‖ ^ (2:ℝ) from by
        rw [← Real.rpow_natCast _ 2,
            ← Real.rpow_mul (integral_nonneg (fun x => by positivity))]; norm_num] at h_sq
    rwa [show (fun x => ‖f x‖ ^ (2:ℝ)) = (fun x => ‖f x‖ ^ 2) from by ext x; simp] at h_sq
  · -- ∫ f = 0 when not AEStronglyMeasurable
    rw [integral_non_aestronglyMeasurable hf_aesm]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (sub_nonneg.mpr hab) (integral_nonneg (fun x => by positivity))

omit [MeasurableSpace Ω] in
/-- Cauchy-Schwarz for the time integral, pointwise in ω. -/
lemma cauchy_schwarz_time_integral_pointwise (A : ℝ → Ω → ℂ) (T : ℝ) (hT : T > 0) (ω : Ω)
    (hf_sq : IntegrableOn (fun s => ‖A s ω‖ ^ 2) (Icc 0 T) volume) :
    ‖∫ s in Icc 0 T, A s ω‖ ^ 2 ≤ T * ∫ s in Icc 0 T, ‖A s ω‖ ^ 2 := by
  have hab : (0 : ℝ) ≤ T := le_of_lt hT
  have h := sq_setIntegral_le_measure_mul_setIntegral_sq_proved hab hf_sq
  simp only [sub_zero] at h
  exact h

omit [MeasurableSpace Ω] in
/-- The scaled time average satisfies a pointwise L² bound. -/
lemma scaled_time_average_pointwise_bound (A : ℝ → Ω → ℂ) (T : ℝ) (hT : T > 0) (ω : Ω)
    (hf_sq : IntegrableOn (fun s => ‖A s ω‖ ^ 2) (Icc 0 T) volume) :
    ‖(1/T : ℂ) * ∫ s in Icc 0 T, A s ω‖ ^ 2 ≤
      (1/T) * ∫ s in Icc 0 T, ‖A s ω‖ ^ 2 := by
  -- Factor out (1/T)²: ‖(1/T) * x‖² = (1/T)² * ‖x‖²
  have h1 : ‖(1/T : ℂ) * ∫ s in Icc 0 T, A s ω‖ ^ 2 =
      (1/T)^2 * ‖∫ s in Icc 0 T, A s ω‖ ^ 2 := by
    rw [norm_mul]
    have h_norm : ‖(1/T : ℂ)‖ = 1/T := by
      rw [show (1/T : ℂ) = ((1/T : ℝ) : ℂ) by simp]
      rw [Complex.norm_real]
      exact abs_of_pos (by positivity)
    rw [h_norm]
    ring
  rw [h1]
  -- Apply Cauchy-Schwarz: ‖∫ f‖² ≤ T * ∫ ‖f‖²
  have h_cs := cauchy_schwarz_time_integral_pointwise A T hT ω hf_sq
  -- Combine: (1/T)² * T * ∫ = (1/T) * ∫
  calc (1/T)^2 * ‖∫ s in Icc 0 T, A s ω‖ ^ 2
    ≤ (1/T)^2 * (T * ∫ s in Icc 0 T, ‖A s ω‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left h_cs
        positivity
    _ = (1/T) * ∫ s in Icc 0 T, ‖A s ω‖^2 := by field_simp

/-! ### Main Theorem: L² Time Average Bound

We now prove the main theorem by integrating the pointwise bound over Ω
and swapping the order of integration via Fubini.
-/

/-- Helper: Fubini swap for ℝ × Ω with restricted measure. -/
lemma integral_swap_Icc (μ : Measure Ω) [SFinite μ]
    (f : ℝ × Ω → ℝ) (T : ℝ)
    (hf : Integrable f ((volume.restrict (Icc 0 T)).prod μ)) :
    (∫ (ω : Ω), (∫ (s : ℝ) in Icc 0 T, f (s, ω)) ∂μ) =
    (∫ (s : ℝ) in Icc 0 T, (∫ (ω : Ω), f (s, ω) ∂μ)) := by
  have h1 : ∫ (p : ℝ × Ω), f p ∂((volume.restrict (Icc 0 T)).prod μ) =
      ∫ (s : ℝ) in Icc 0 T, (∫ (ω : Ω), f (s, ω) ∂μ) := integral_prod f hf
  have h2 : ∫ (p : ℝ × Ω), f p ∂((volume.restrict (Icc 0 T)).prod μ) =
      ∫ (ω : Ω), (∫ (s : ℝ) in Icc 0 T, f (s, ω)) ∂μ := integral_prod_symm f hf
  rw [← h1, h2]

/-- Helper: setIntegral bound using uniform L² bound. -/
lemma setIntegral_L2_bound (μ : Measure Ω) [SFinite μ] (M_sq T : ℝ) (hT : T > 0)
    (A : ℝ → Ω → ℂ)
    (h_L2_bound : ∀ s, s ∈ Icc 0 T → ∫ ω, ‖A s ω‖ ^ 2 ∂μ ≤ M_sq)
    (h_int : IntegrableOn (fun s => ∫ ω, ‖A s ω‖ ^ 2 ∂μ) (Icc 0 T) volume) :
    (∫ (s : ℝ) in Icc 0 T, (∫ ω, ‖A s ω‖ ^ 2 ∂μ)) ≤ T * M_sq := by
  have h_vol : (volume : Measure ℝ) (Icc 0 T) ≠ ⊤ := by
    simp [Real.volume_Icc, ENNReal.ofReal_ne_top]
  calc (∫ (s : ℝ) in Icc 0 T, (∫ ω, ‖A s ω‖ ^ 2 ∂μ))
    ≤ ∫ (s : ℝ) in Icc 0 T, M_sq := by
        apply setIntegral_mono_on h_int (integrableOn_const h_vol) measurableSet_Icc
        intro s hs; exact h_L2_bound s hs
    _ = T * M_sq := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc]
        simp [ENNReal.toReal_ofReal (le_of_lt hT), smul_eq_mul]

/-- **L² bound for time averages.**

For A : ℝ → Ω → ℂ with uniform L² bound ∫_Ω ‖A_s‖² dμ ≤ M_sq for all s ∈ [0,T],
the time average satisfies:
$$\int_\Omega \left\|\frac{1}{T}\int_0^T A_s(\omega)\,ds\right\|^2 d\mu(\omega) \leq M_{sq}$$

**Proof outline:**
1. Cauchy-Schwarz pointwise: ‖(1/T)∫ A_s(ω) ds‖² ≤ (1/T) ∫ ‖A_s(ω)‖² ds
2. Integrate over Ω: ∫_Ω LHS dμ ≤ (1/T) ∫_Ω ∫_[0,T] ‖A_s‖² ds dμ
3. Fubini: = (1/T) ∫_[0,T] (∫_Ω ‖A_s‖² dμ) ds
4. Uniform bound: ≤ (1/T) ∫_[0,T] M_sq ds = (1/T) · T · M_sq = M_sq
-/
theorem L2_time_average_bound (μ : Measure Ω) [SFinite μ]
    (A : ℝ → Ω → ℂ) (M_sq : ℝ) (T : ℝ) (hT : T > 0)
    -- Uniform L² bound
    (h_L2_bound : ∀ s, s ∈ Icc 0 T → ∫ ω, ‖A s ω‖ ^ 2 ∂μ ≤ M_sq)
    -- Joint measurability for Fubini
    (h_joint_meas : AEStronglyMeasurable (Function.uncurry A)
        ((volume.restrict (Icc 0 T)).prod μ))
    -- Integrability of ‖A‖² on product (needed for Fubini)
    (h_prod_int : Integrable (fun p : ℝ × Ω => ‖A p.1 p.2‖ ^ 2)
        ((volume.restrict (Icc 0 T)).prod μ))
    -- Integrability of slice integrals (for Fubini step)
    (h_slice_int : IntegrableOn (fun s => ∫ ω, ‖A s ω‖^2 ∂μ) (Icc 0 T) volume)
    -- Measurability of time average (technical hypothesis)
    (h_avg_meas : AEStronglyMeasurable
        (fun ω => (1/T : ℂ) * ∫ s in Icc 0 T, A s ω) μ) :
    ∫ ω, ‖(1/T : ℂ) * ∫ s in Icc (0 : ℝ) T, A s ω‖^2 ∂μ ≤ M_sq := by
  /-
  The proof uses:
  1. scaled_time_average_pointwise_bound: pointwise Cauchy-Schwarz
  2. integral_mono_ae: integrate the a.e. pointwise inequality
  3. integral_const_mul: factor out (1/T)
  4. integral_swap_Icc: Fubini swap
  5. setIntegral_L2_bound: apply uniform bound
  -/
  -- Setup integrability for integral_mono
  have h_rhs_int : Integrable (fun ω => (1/T : ℝ) * ∫ (s : ℝ) in Icc 0 T, ‖A s ω‖^2) μ := by
    have h_margin := h_prod_int.integral_prod_right
    exact h_margin.const_mul (1/T)
  -- From product integrability, get a.e. slice integrability
  have h_sq_meas : AEStronglyMeasurable (fun p : ℝ × Ω => ‖A p.1 p.2‖^2)
      ((volume.restrict (Icc 0 T)).prod μ) := h_joint_meas.norm.pow 2
  have h_ae_slice_int : ∀ᵐ (ω : Ω) ∂μ, IntegrableOn (fun s => ‖A s ω‖^2) (Icc 0 T) volume := by
    -- Use Integrable.swap to get integrability on the swapped product space
    have h_swap : Integrable ((fun p : ℝ × Ω => ‖A p.1 p.2‖^2) ∘ Prod.swap)
        (μ.prod (volume.restrict (Icc 0 T))) := h_prod_int.swap
    -- The swapped function is (ω, s) ↦ ‖A s ω‖²
    have h_eq : (fun p : ℝ × Ω => ‖A p.1 p.2‖^2) ∘ Prod.swap = fun p : Ω × ℝ => ‖A p.2 p.1‖^2 := rfl
    rw [h_eq] at h_swap
    -- Now apply integrable_prod_iff to get a.e. slice integrability
    -- Note: prod_swap takes AEStronglyMeasurable f (ν.prod μ) to (f ∘ swap) on (μ.prod ν)
    have h_meas_swap : AEStronglyMeasurable (fun p : Ω × ℝ => ‖A p.2 p.1‖^2)
        (μ.prod (volume.restrict (Icc 0 T))) := h_sq_meas.prod_swap
    exact ((integrable_prod_iff h_meas_swap).mp h_swap).1
  have h_lhs_int : Integrable (fun ω => ‖(1/T : ℂ) * ∫ (s : ℝ) in Icc 0 T, A s ω‖^2) μ := by
    have h_meas_sq := h_avg_meas.norm.pow 2
    apply h_rhs_int.mono h_meas_sq
    -- Use a.e. slice integrability to get the pointwise bound a.e.
    filter_upwards [h_ae_slice_int] with ω hω_int
    have h_lhs_nonneg : 0 ≤ ‖(1/T : ℂ) * ∫ (s : ℝ) in Icc 0 T, A s ω‖^2 := sq_nonneg _
    have h_rhs_nonneg : 0 ≤ (1/T : ℝ) * ∫ (s : ℝ) in Icc 0 T, ‖A s ω‖^2 := by
      apply mul_nonneg (by positivity); apply integral_nonneg; intro; positivity
    -- Simplify the power of functions applied to ω
    change ‖((fun x => ‖(1/T : ℂ) * ∫ (s : ℝ) in Icc 0 T, A s x‖) ^ 2) ω‖ ≤ _
    simp only [Pi.pow_apply]
    rw [Real.norm_of_nonneg h_lhs_nonneg, Real.norm_of_nonneg h_rhs_nonneg]
    exact scaled_time_average_pointwise_bound A T hT ω hω_int
  -- Main calculation
  calc ∫ (ω : Ω), ‖(1/T : ℂ) * ∫ (s : ℝ) in Icc (0 : ℝ) T, A s ω‖^2 ∂μ
    -- Step 1-2: Apply pointwise bound and integrate (use a.e. version)
    ≤ ∫ (ω : Ω), (1/T) * (∫ (s : ℝ) in Icc 0 T, ‖A s ω‖^2) ∂μ := by
        apply integral_mono_ae h_lhs_int h_rhs_int
        -- Use a.e. slice integrability to get the bound a.e.
        filter_upwards [h_ae_slice_int] with ω hω_int
        exact scaled_time_average_pointwise_bound A T hT ω hω_int
    -- Step 3: Factor out (1/T)
    _ = (1/T) * (∫ (ω : Ω), (∫ (s : ℝ) in Icc 0 T, ‖A s ω‖^2) ∂μ) := by
        rw [integral_const_mul]
    -- Step 4: Fubini swap
    _ = (1/T) * (∫ (s : ℝ) in Icc 0 T, (∫ (ω : Ω), ‖A s ω‖^2 ∂μ)) := by
        rw [integral_swap_Icc μ (fun p => ‖A p.1 p.2‖^2) T h_prod_int]
    -- Step 5: Apply uniform bound
    _ ≤ (1/T) * (T * M_sq) := by
        apply mul_le_mul_of_nonneg_left
        · exact setIntegral_L2_bound μ M_sq T hT A h_L2_bound h_slice_int
        · positivity
    -- Step 6: Simplify
    _ = M_sq := by field_simp

/-! ## L² on Product from Slicewise Bounds (Theorem 3 - prove first)

Tonelli's theorem: if each slice is in L² with uniform bound,
then the function is in L² on the product.

Key insight: Use `integrable_prod_iff` (Tonelli) to split product integrability into:
1. Slice integrability (from each A_s ∈ L²)
2. Integrability of slice integrals (constant by uniform bound → trivially integrable on [0,T])
-/

/-- **L² on product from uniform slicewise bounds.**

By Tonelli: ∫∫ |A|² = ∫₀ᵀ (∫_Ω |A_s|² dμ) ds = ∫₀ᵀ C ds = TC
-/
theorem memLp_prod_of_uniform_slicewise_bound (μ : Measure Ω) [SFinite μ]
    (A : ℝ → Ω → ℂ) (T : ℝ)
    -- AEStronglyMeasurable on product
    (h_meas : AEStronglyMeasurable (Function.uncurry A)
        ((volume.restrict (Icc 0 T)).prod μ))
    -- Each A_s is in L²
    (h_memLp : ∀ s, MemLp (A s) 2 μ)
    -- Uniform L² norm (constant in s)
    (h_uniform : ∀ s, ∫ ω, ‖A s ω‖ ^ 2 ∂μ = ∫ ω, ‖A 0 ω‖ ^ 2 ∂μ) :
    MemLp (Function.uncurry A) 2 ((volume.restrict (Icc 0 T)).prod μ) := by
  /-
  Proof structure:
  1. MemLp 2 ↔ Integrable (‖·‖²) (for p = 2)
  2. Use integrable_prod_iff to split into slice + integral conditions
  3. Slice integrability: from h_memLp, each A_s ∈ L² means ‖A_s‖² integrable
  4. Integral of slices: by h_uniform, (fun s => ∫ ‖A_s‖²) is constant = C
     A constant function is integrable on bounded [0,T]
  -/
  -- First show ‖A‖² is integrable on product
  have h_sq_int : Integrable (fun p : ℝ × Ω => ‖A p.1 p.2‖ ^ 2)
      ((volume.restrict (Icc 0 T)).prod μ) := by
    have h_sq_meas : AEStronglyMeasurable (fun p : ℝ × Ω => ‖A p.1 p.2‖ ^ 2)
        ((volume.restrict (Icc 0 T)).prod μ) := h_meas.norm.pow 2
    rw [integrable_prod_iff h_sq_meas]
    constructor
    · -- Slice integrability: ∀ᵐ s, Integrable (fun ω => ‖A s ω‖²) μ
      filter_upwards with s
      have h := (h_memLp s).integrable_norm_rpow
        (by simp : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤)
      convert h using 2
      simp [ENNReal.toReal_ofNat]
    · -- Integral of slices is constant, hence integrable on bounded [0,T]
      have h_eq : (fun s => ∫ (ω : Ω), ‖‖A s ω‖ ^ 2‖ ∂μ) =
          fun _ => ∫ ω, ‖A 0 ω‖ ^ 2 ∂μ := by
        ext s
        simp only [Real.norm_of_nonneg (sq_nonneg _)]
        exact h_uniform s
      rw [h_eq]
      have h_vol : (volume : Measure ℝ) (Icc 0 T) ≠ ⊤ := by
        simp [Real.volume_Icc, ENNReal.ofReal_ne_top]
      exact integrableOn_const h_vol
  -- Now use the integrability to get MemLp 2
  rw [memLp_two_iff_integrable_sq_norm h_meas]
  exact h_sq_int

/-! ## Time Average is in L² (Theorem 2)

This is a corollary using Theorem 3 + Integrable.mono.
-/

/-- **Time average is in L²** (Corollary of memLp_prod)

This follows from product integrability + Integrable.mono with the pointwise bound.
-/
theorem time_average_memLp_two (μ : Measure Ω) [SFinite μ]
    (A : ℝ → Ω → ℂ) (T : ℝ) (hT : T > 0)
    -- Each A_s is in L²
    (h_memLp : ∀ s, MemLp (A s) 2 μ)
    -- Uniform L² norm
    (h_uniform : ∀ s, ∫ ω, ‖A s ω‖ ^ 2 ∂μ = ∫ ω, ‖A 0 ω‖ ^ 2 ∂μ)
    -- Joint measurability
    (h_joint_meas : AEStronglyMeasurable (Function.uncurry A)
        ((volume.restrict (Icc 0 T)).prod μ))
    -- Measurability of time average
    (h_avg_meas : AEStronglyMeasurable
        (fun ω => (1 / T : ℂ) * ∫ s in Icc 0 T, A s ω) μ) :
    MemLp (fun ω => (1/T : ℂ) * ∫ s in Icc (0 : ℝ) T, A s ω) 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm h_avg_meas]
  -- 1. Get joint integrability from Theorem 3
  have h_prod := memLp_prod_of_uniform_slicewise_bound μ A T h_joint_meas h_memLp h_uniform
  have h_prod_int : Integrable (fun p : ℝ × Ω => ‖A p.1 p.2‖^2)
      ((volume.restrict (Icc 0 T)).prod μ) :=
    (memLp_two_iff_integrable_sq_norm h_joint_meas).mp h_prod
  -- 2. The RHS bound (1/T) * ∫ ‖A_s ω‖² is integrable (marginal of product)
  have h_rhs_int : Integrable (fun ω => (1/T : ℝ) * ∫ (s : ℝ) in Icc 0 T, ‖A s ω‖^2) μ := by
    have h_margin := h_prod_int.integral_prod_right
    exact h_margin.const_mul (1/T)
  -- 3. Use Integrable.mono with the pointwise bound
  have h_meas_sq : AEStronglyMeasurable (fun ω => ‖(1/T : ℂ) * ∫ (s : ℝ) in Icc 0 T, A s ω‖^2) μ :=
    h_avg_meas.norm.pow 2
  -- From product integrability, get a.e. slice integrability via Fubini (in ω direction)
  have h_sq_meas : AEStronglyMeasurable (fun p : ℝ × Ω => ‖A p.1 p.2‖^2)
      ((volume.restrict (Icc 0 T)).prod μ) := h_joint_meas.norm.pow 2
  have h_ae_slice_int : ∀ᵐ (ω : Ω) ∂μ, IntegrableOn (fun s => ‖A s ω‖^2) (Icc 0 T) volume := by
    -- Use Integrable.swap to get integrability on the swapped product space
    have h_swap : Integrable ((fun p : ℝ × Ω => ‖A p.1 p.2‖^2) ∘ Prod.swap)
        (μ.prod (volume.restrict (Icc 0 T))) := h_prod_int.swap
    have h_eq : (fun p : ℝ × Ω => ‖A p.1 p.2‖^2) ∘ Prod.swap = fun p : Ω × ℝ => ‖A p.2 p.1‖^2 := rfl
    rw [h_eq] at h_swap
    have h_meas_swap : AEStronglyMeasurable (fun p : Ω × ℝ => ‖A p.2 p.1‖^2)
        (μ.prod (volume.restrict (Icc 0 T))) := h_sq_meas.prod_swap
    exact ((integrable_prod_iff h_meas_swap).mp h_swap).1
  apply h_rhs_int.mono h_meas_sq
  -- Use a.e. slice integrability for the pointwise bound
  filter_upwards [h_ae_slice_int] with ω hω_int
  -- The pointwise bound: use that LHS ≥ 0 and apply the Cauchy-Schwarz bound
  have h_lhs_nonneg : 0 ≤ ‖(1/T : ℂ) * ∫ (s : ℝ) in Icc 0 T, A s ω‖^2 := sq_nonneg _
  have h_rhs_nonneg : 0 ≤ (1/T : ℝ) * ∫ (s : ℝ) in Icc 0 T, ‖A s ω‖^2 := by
    apply mul_nonneg (by positivity)
    apply integral_nonneg; intro; positivity
  rw [Real.norm_of_nonneg h_lhs_nonneg, Real.norm_of_nonneg h_rhs_nonneg]
  exact scaled_time_average_pointwise_bound A T hT ω hω_int

/-! ## Measurability of Parametric Time Integrals

For a family A : ℝ → Ω → ℂ that is continuous in s and measurable in ω,
the parametric integral ω ↦ ∫ A s ω ds is AEStronglyMeasurable.

Key tool: `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` gives
joint StronglyMeasurable on ℝ × Ω from continuous-in-s + measurable-in-ω.
Then swap + `integral_prod_right'` gives measurability of the marginal integral.
-/

/-- **Measurability of parametric time integrals.**

For A : ℝ → Ω → ℂ with s ↦ A s ω continuous for each ω and A s measurable for each s,
the time integral ω ↦ (1/T) * ∫ₛ (A s ω - EA) ds is AEStronglyMeasurable.

Proof: continuous-in-s + measurable-in-ω → jointly StronglyMeasurable (Mathlib),
then swap product measure and integrate out s via `integral_prod_right'`.
-/
theorem gff_time_integral_aestronglyMeasurable_proved
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℝ → Ω → ℂ) (EA : ℂ) (T : ℝ)
    (h_cont_s : ∀ ω, Continuous (fun s => A s ω))
    (h_meas : ∀ s, Measurable (A s)) :
    AEStronglyMeasurable
      (fun ω => (1 / T : ℂ) * ∫ s in Icc (0 : ℝ) T, A s ω - EA)
      μ := by
  -- s ↦ A s ω - EA is also continuous in s and measurable in ω
  have h_cont_sub : ∀ ω, Continuous (fun s => A s ω - EA) :=
    fun ω => (h_cont_s ω).sub continuous_const
  have h_meas_sub : ∀ s, Measurable (fun ω => A s ω - EA) :=
    fun s => (h_meas s).sub measurable_const
  -- Joint StronglyMeasurable on ℝ × Ω
  have h_sm_sub : ∀ (s : ℝ), StronglyMeasurable (fun ω => A s ω - EA) :=
    fun s => (h_meas_sub s).stronglyMeasurable
  have h_uncurry : StronglyMeasurable (Function.uncurry (fun s ω => A s ω - EA)) :=
    @stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      Ω ℂ ℝ _ _ _ _ _ _ _ _ (fun s ω => A s ω - EA) h_cont_sub h_sm_sub
  -- AEStronglyMeasurable on product → swap → integrate out s
  have h_ae_prod : AEStronglyMeasurable (Function.uncurry (fun s ω => A s ω - EA))
      ((volume.restrict (Icc 0 T)).prod μ) :=
    h_uncurry.aestronglyMeasurable
  have h_int_meas : AEStronglyMeasurable
      (fun ω => ∫ s in Icc 0 T, (A s ω - EA)) μ :=
    h_ae_prod.prod_swap.integral_prod_right'
  exact h_int_meas.const_mul (1 / T : ℂ)

/-! ## Integrability of Covariance Norm on Slices

For a continuous covariance function, the norm restricted to any compact slice
is integrable. This is immediate from continuity on compact sets.
-/

/-- **Integrability of covariance norm on slices.**

If the covariance (s,u) ↦ ∫ A_s · conj(A_u) - EA·conj(EA) is continuous,
then u ↦ ‖Cov(s,u)‖ is integrable on [0,T] since continuous functions on
compact sets are integrable.
-/
theorem gff_covariance_norm_integrableOn_slice_proved
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℝ → Ω → ℂ) (EA : ℂ) (s T : ℝ)
    (h_cov_cont : Continuous (fun p : ℝ × ℝ =>
      ∫ ω, A p.1 ω * starRingEnd ℂ (A p.2 ω) ∂μ - EA * starRingEnd ℂ EA)) :
    MeasureTheory.IntegrableOn
      (fun u => ‖∫ ω, A s ω * starRingEnd ℂ (A u ω) ∂μ - EA * starRingEnd ℂ EA‖)
      (Icc 0 T) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply ContinuousOn.norm
  exact (h_cov_cont.comp (continuous_const.prodMk continuous_id)).continuousOn

/-! ## Double Integral Bound for Polynomial Decay Kernels

For kernels K(s,u) = (1 + |s-u|)^{-α} with α > 1, the double integral over [0,T]²
is bounded linearly in T. The proof uses:

1. **Integrability on ℝ:** (1+|t|)^{-α} is integrable via `integrableOn_add_rpow_Ioi_of_lt`
   on Ioi 0, transferred to Iio 0 by negation symmetry (g is even, Lebesgue measure
   is negation-invariant via `MeasurePreserving.integrableOn_comp_preimage`).
2. **Translation invariance:** For each s, ∫_{[0,T]} g(s-u) du ≤ ∫_ℝ g = C by
   `setIntegral_le_integral` and `integral_sub_left_eq_self`.
3. **Outer integral:** ∫_{[0,T]} C ds = C·T.
-/

/-- **Double integral bound for polynomial decay kernels.**

For the kernel K(s,u) = (1 + |s-u|)^{-α} with α > 1:
  ∫₀ᵀ ∫₀ᵀ (1 + |s-u|)^{-α} ds du ≤ C · T

where C = ∫_ℝ (1+|t|)^{-α} dt is the integral of the kernel over all of ℝ.

**Key tools:** `integrableOn_add_rpow_Ioi_of_lt` (decay integral), `integral_sub_left_eq_self`
(translation invariance), `setIntegral_le_integral` (set ≤ full for nonneg integrable functions),
`MeasurePreserving.integrableOn_comp_preimage` (negation symmetry for even functions).
-/
theorem double_integral_polynomial_decay_bound_proved (α : ℝ) (hα : α > 1) :
    ∃ C : ℝ, C > 0 ∧ ∀ T : ℝ, T > 0 →
      ∫ s in Icc (0 : ℝ) T, ∫ u in Icc (0 : ℝ) T,
        (1 + |s - u|)^(-α) ≤ C * T := by
  -- The kernel g(t) = (1 + |t|)^(-α)
  set g : ℝ → ℝ := fun t => (1 + |t|) ^ (-α) with hg_def
  -- Integrability on (0, ∞): matches integrableOn_add_rpow_Ioi_of_lt with m=1, c=0
  have h_ioi : IntegrableOn g (Ioi 0) volume :=
    (integrableOn_add_rpow_Ioi_of_lt (by linarith : -α < -1) (by linarith : -(1:ℝ) < 0)).congr_fun
      (fun t ht => by simp [hg_def, abs_of_pos (mem_Ioi.mp ht), add_comm]) measurableSet_Ioi
  -- Integrability on (-∞, 0): by negation symmetry (g is even, Lebesgue measure neg-invariant)
  have h_iio : IntegrableOn g (Iio 0) volume := by
    rw [show Iio (0:ℝ) = Neg.neg ⁻¹' (Ioi 0) from by ext x; simp,
        show g = g ∘ Neg.neg from by ext t; simp [hg_def, abs_neg]]
    exact ((volume : Measure ℝ).measurePreserving_neg.integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding).mpr h_ioi
  -- Integrable on all of ℝ: Iic 0 ∪ Ioi 0 = univ, Iic 0 = Iio 0 ∪ {0}
  have h_integrable : Integrable g volume := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ)),
        show Iic (0:ℝ) = Iio 0 ∪ {0} from Eq.symm Iio_union_right]
    exact (h_iio.union (integrableOn_singleton (hx := by simp))).union h_ioi
  -- g ≥ 0 everywhere
  have h_nonneg : ∀ t : ℝ, 0 ≤ g t := fun t => by positivity
  -- C = ∫_ℝ g(t) dt > 0 (g > 0 on open set (0,1), integrable)
  have hC_pos : 0 < ∫ t : ℝ, g t := by
    calc (0 : ℝ)
      < ∫ t in (0:ℝ)..1, g t := by
          apply intervalIntegral.intervalIntegral_pos_of_pos_on
          · exact (Continuous.rpow_const (by continuity) (fun _ => by left; positivity))
              |>.intervalIntegrable 0 1
          · intro t _; positivity
          · norm_num
      _ = ∫ t in Ioc 0 1, g t :=
          intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)
      _ ≤ ∫ t in Icc 0 1, g t :=
          setIntegral_mono_set h_integrable.integrableOn
            (by
              filter_upwards with t
              exact h_nonneg t)
            Ioc_subset_Icc_self.eventuallyLE
      _ ≤ ∫ t, g t :=
          setIntegral_le_integral h_integrable
            (by
              filter_upwards with t
              exact h_nonneg t)
  refine ⟨∫ t, g t, hC_pos, fun T hT => ?_⟩
  -- For each s: ∫_{[0,T]} g(s-u) du ≤ ∫_ℝ g = C (translation invariance + set ≤ full)
  have h_inner : ∀ s, ∫ u in Icc 0 T, g (s - u) ≤ ∫ t, g t := fun s =>
    calc ∫ u in Icc 0 T, g (s - u)
      ≤ ∫ u, g (s - u) :=
          setIntegral_le_integral (h_integrable.comp_sub_left s)
            (by
              filter_upwards with u
              exact h_nonneg _)
      _ = ∫ t, g t := integral_sub_left_eq_self g volume s
  -- g(s-u) unfolds to (1+|s-u|)^(-α), so goals match definitionally
  change ∫ s in Icc 0 T, ∫ u in Icc 0 T, g (s - u) ≤ (∫ t, g t) * T
  calc ∫ s in Icc 0 T, ∫ u in Icc 0 T, g (s - u)
    ≤ ∫ s in Icc 0 T, (∫ t, g t) := by
        apply integral_mono_of_nonneg
        · filter_upwards with s; exact integral_nonneg (fun u => h_nonneg _)
        · exact integrableOn_const (show volume (Icc (0:ℝ) T) ≠ ⊤ from by
            simp [Real.volume_Icc, ENNReal.ofReal_ne_top])
        · filter_upwards with s; exact h_inner s
    _ = (∫ t, g t) * T := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc, sub_zero,
            ENNReal.toReal_ofReal (by linarith : 0 ≤ T), smul_eq_mul, mul_comm]

/-! ## Minkowski Inequality for Weighted L² Sums

The triangle inequality in L²: √(∫(∑ wⱼfⱼ)²) ≤ ∑ wⱼ√(∫ fⱼ²)
for nonneg weights and functions. Proved by induction using Cauchy-Schwarz.
-/

section Minkowski

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private lemma cauchy_schwarz_integral
    {f g : α → ℝ}
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ x, 0 ≤ g x)
    (hf_int : Integrable (fun x => (f x) ^ 2) μ)
    (hg_int : Integrable (fun x => (g x) ^ 2) μ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hg_meas : AEStronglyMeasurable g μ) :
    ∫ x, f x * g x ∂μ ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 from ⟨by norm_num, by norm_num, by norm_num⟩)
    (Filter.Eventually.of_forall hf_nn) (Filter.Eventually.of_forall hg_nn)
    (show MemLp f (ENNReal.ofReal 2) μ from by
      rw [show ENNReal.ofReal 2 = 2 from by norm_num, memLp_two_iff_integrable_sq_norm hf_meas]
      exact hf_int.congr (by filter_upwards with x; simp [Real.norm_eq_abs, sq_abs]))
    (show MemLp g (ENNReal.ofReal 2) μ from by
      rw [show ENNReal.ofReal 2 = 2 from by norm_num, memLp_two_iff_integrable_sq_norm hg_meas]
      exact hg_int.congr (by filter_upwards with x; simp [Real.norm_eq_abs, sq_abs]))
  have conv : ∀ (φ : α → ℝ), (fun a => φ a ^ (2:ℝ)) = fun a => (φ a)^(2:ℕ) := by
    intro φ; ext a; exact_mod_cast Real.rpow_natCast (φ a) 2
  simp only [conv, Real.sqrt_eq_rpow] at h ⊢; exact h

private lemma integrable_mul_of_sq_integrable
    {f g : α → ℝ}
    (hf_int : Integrable (fun x => (f x) ^ 2) μ)
    (hg_int : Integrable (fun x => (g x) ^ 2) μ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hg_meas : AEStronglyMeasurable g μ) :
    Integrable (fun x => f x * g x) μ := by
  apply Integrable.mono ((hf_int.add hg_int).div_const 2) (hf_meas.mul hg_meas)
  filter_upwards with x
  simp only [Real.norm_eq_abs, Pi.add_apply, Pi.mul_apply]
  calc |f x * g x| ≤ ((f x) ^ 2 + (g x) ^ 2) / 2 := by
        rw [abs_mul]
        nlinarith [sq_abs (f x), sq_abs (g x), sq_nonneg (|f x| - |g x|)]
    _ ≤ |((f x) ^ 2 + (g x) ^ 2) / 2| := le_abs_self _

private lemma sqrt_integral_sq_add_le
    {f g : α → ℝ}
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ x, 0 ≤ g x)
    (hf_int : Integrable (fun x => (f x) ^ 2) μ)
    (hg_int : Integrable (fun x => (g x) ^ 2) μ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hg_meas : AEStronglyMeasurable g μ) :
    Real.sqrt (∫ x, (f x + g x) ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂μ) + Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  set A := Real.sqrt (∫ x, (f x) ^ 2 ∂μ)
  set B := Real.sqrt (∫ x, (g x) ^ 2 ∂μ)
  rw [← Real.sqrt_sq (by positivity : 0 ≤ A + B)]
  apply Real.sqrt_le_sqrt
  have hA_sq : A^2 = ∫ x, (f x)^2 ∂μ :=
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x)))
  have hB_sq : B^2 = ∫ x, (g x)^2 ∂μ :=
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (g x)))
  have hfg_int : Integrable (fun x => f x * g x) μ :=
    integrable_mul_of_sq_integrable hf_int hg_int hf_meas hg_meas
  have h_cs : ∫ x, (f x * g x) ∂μ ≤ A * B :=
    cauchy_schwarz_integral hf_nn hg_nn hf_int hg_int hf_meas hg_meas
  have h_split : ∫ x, (f x + g x) ^ 2 ∂μ =
      ∫ x, (f x) ^ 2 ∂μ + 2 * ∫ x, (f x * g x) ∂μ + ∫ x, (g x) ^ 2 ∂μ := by
    have h1 : ∀ x, (f x + g x) ^ 2 = (f x) ^ 2 + 2 * (f x * g x) + (g x) ^ 2 :=
      fun x => by ring
    simp_rw [h1]
    have i1 : ∫ x, ((f x)^2 + 2 * (f x * g x) + (g x)^2) ∂μ =
        ∫ x, ((f x) ^ 2 + 2 * (f x * g x)) ∂μ + ∫ x, (g x) ^ 2 ∂μ :=
      integral_add (hf_int.add (hfg_int.const_mul 2)) hg_int
    have i2 : ∫ x, ((f x) ^ 2 + 2 * (f x * g x)) ∂μ =
        ∫ x, (f x) ^ 2 ∂μ + ∫ x, 2 * (f x * g x) ∂μ :=
      integral_add hf_int (hfg_int.const_mul 2)
    have i3 : ∫ x, 2 * (f x * g x) ∂μ = 2 * ∫ x, f x * g x ∂μ :=
      integral_const_mul ..
    linarith
  linarith [h_cs, hA_sq, hB_sq]

private lemma sqrt_integral_sq_mul (c : ℝ) (hc : 0 ≤ c) (f : α → ℝ) :
    Real.sqrt (∫ x, (c * f x) ^ 2 ∂μ) = c * Real.sqrt (∫ x, (f x) ^ 2 ∂μ) := by
  simp_rw [show ∀ x, (c * f x)^2 = c^2 * (f x)^2 from fun x => by ring]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

private lemma memLp_two_weighted (w : ℝ) (f : α → ℝ)
    (hf_int : Integrable (fun x => (f x) ^ 2) μ)
    (hf_meas : AEStronglyMeasurable f μ) :
    MemLp (fun x => w * f x) 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm (hf_meas.const_mul w)]
  convert (hf_int.const_mul (w^2)) using 1
  ext x; simp [mul_pow, Real.norm_eq_abs, sq_abs]

private lemma memLp_two_weighted_sum {n : ℕ} (w : Fin n → ℝ) (f : Fin n → α → ℝ)
    (hf_int : ∀ j, Integrable (fun x => (f j x) ^ 2) μ)
    (hf_meas : ∀ j, AEStronglyMeasurable (f j) μ) :
    MemLp (fun x => ∑ j : Fin n, w j * f j x) 2 μ := by
  induction n with
  | zero => simp only [Fin.sum_univ_zero]; exact MemLp.zero
  | succ n ih =>
    simp_rw [Fin.sum_univ_castSucc]
    exact (ih _ _ (fun j => hf_int j.castSucc) (fun j => hf_meas j.castSucc)).add
      (memLp_two_weighted _ _ (hf_int _) (hf_meas _))

private lemma integrable_sq_of_memLp_two {f : α → ℝ} (hf : MemLp f 2 μ) :
    Integrable (fun x => (f x)^2) μ :=
  MemLp.integrable_sq hf

/-- **Minkowski inequality for weighted L² sums** (proved theorem)

    For nonneg weights wⱼ and nonneg functions fⱼ with fⱼ² integrable:
    √(∫ (∑ⱼ wⱼfⱼ)² dμ) ≤ ∑ⱼ wⱼ √(∫ fⱼ² dμ)

    Proof by induction on n, using Cauchy-Schwarz for integrals at each step.
-/
theorem minkowski_weighted_L2_sum_proved {n : ℕ} {w : Fin n → ℝ} {f : Fin n → α → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hf : ∀ j ω, 0 ≤ f j ω)
    (hf_int : ∀ j, Integrable (fun ω => (f j ω) ^ 2) μ)
    (hf_meas : ∀ j, AEStronglyMeasurable (f j) μ) :
    Real.sqrt (∫ ω, (∑ j, w j * f j ω)^2 ∂μ) ≤ ∑ j, w j * Real.sqrt (∫ ω, (f j ω)^2 ∂μ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [Fin.sum_univ_castSucc]
    set S := fun ω => ∑ j : Fin n, w j.castSucc * f j.castSucc ω
    set g := fun ω => w (Fin.last n) * f (Fin.last n) ω
    have hS_nn : ∀ ω, 0 ≤ S ω := fun ω =>
      Finset.sum_nonneg (fun j _ => mul_nonneg (hw j.castSucc) (hf j.castSucc ω))
    have hg_nn : ∀ ω, 0 ≤ g ω := fun ω => mul_nonneg (hw _) (hf _ ω)
    have hS_memLp : MemLp S 2 μ :=
      memLp_two_weighted_sum _ _ (fun j => hf_int j.castSucc) (fun j => hf_meas j.castSucc)
    have hg_memLp : MemLp g 2 μ :=
      memLp_two_weighted _ _ (hf_int _) (hf_meas _)
    have hS_int : Integrable (fun ω => (S ω)^2) μ := integrable_sq_of_memLp_two hS_memLp
    have hg_int : Integrable (fun ω => (g ω)^2) μ := integrable_sq_of_memLp_two hg_memLp
    calc Real.sqrt (∫ ω, (S ω + g ω)^2 ∂μ)
        ≤ Real.sqrt (∫ ω, (S ω)^2 ∂μ) + Real.sqrt (∫ ω, (g ω)^2 ∂μ) :=
          sqrt_integral_sq_add_le hS_nn hg_nn hS_int hg_int
            hS_memLp.aestronglyMeasurable hg_memLp.aestronglyMeasurable
      _ ≤ (∑ j : Fin n, w j.castSucc * Real.sqrt (∫ ω, (f j.castSucc ω)^2 ∂μ)) +
          (w (Fin.last n) * Real.sqrt (∫ ω, (f (Fin.last n) ω)^2 ∂μ)) := by
          gcongr
          · exact ih (fun j => hw j.castSucc) (fun j => hf j.castSucc)
              (fun j => hf_int j.castSucc) (fun j => hf_meas j.castSucc)
          · exact le_of_eq (sqrt_integral_sq_mul _ (hw _) _)

end Minkowski

/-! ## Variance Bound for Time Averages

The variance of the time average is bounded by the double integral of the covariance:
  ‖E[‖T⁻¹∫₀ᵀ A_s ds - EA‖²]‖ ≤ T⁻² · ‖∫₀ᵀ∫₀ᵀ Cov(s,u) ds du‖

The proof establishes an equality (the bound is tight):
1. Center: X_s = A_s - EA, which has zero mean
2. Algebra: T⁻¹ * ∫A_s - EA = T⁻¹ * ∫X_s, factor out T⁻²
3. Cast to ℂ: ‖z‖² = Re(z * conj(z)) [RCLike.mul_conj]
4. Product of integrals = double integral [integral_mul_left/right]
5. Fubini swap ω ↔ (s,u) [integral_integral_swap]
6. Recognize E[X_s · conj(X_u)] = Cov(s,u)
7. Re(z) ≤ ‖z‖ for the final inequality [Complex.re_le_norm]
-/

section VarianceBound

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Variance of time averages bounded by double integral of covariance** (proved theorem)

For an L² stationary process A with constant mean EA:
  ‖E[‖T⁻¹∫₀ᵀ A_s ds - EA‖²]‖ ≤ T⁻² · ‖∫₀ᵀ∫₀ᵀ Cov(s,u) ds du‖

The proof actually gives equality (the bound is tight).
-/
theorem _root_.OSforGFF.L2_variance_time_average_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℝ → Ω → ℂ) (EA : ℂ)
    (T : ℝ) (hT : T > 0)
    (h_mean : ∀ s, ∫ ω, A s ω ∂μ = EA)
    -- Fubini integrability for the covariance triple integral swap
    (h_Fubini : Integrable (fun (x : Ω × (ℝ × ℝ)) =>
        (A x.2.1 x.1 - EA) * starRingEnd ℂ (A x.2.2 x.1 - EA))
        (μ.prod ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T)))))
    -- Each time-slice A_s is L²(Ω) (for bilinear expansion of covariance)
    (h_slice_L2 : ∀ s, MemLp (A s) 2 μ)
    -- Slice integrability: for a.e. ω, s ↦ A_s(ω) is integrable on [0,T]
    (h_slice_int : ∀ᵐ ω ∂μ, Integrable (fun s => A s ω) (volume.restrict (Set.Icc 0 T))) :
    let Cov := fun s u => ∫ ω, A s ω * starRingEnd ℂ (A u ω) ∂μ - EA * starRingEnd ℂ EA
    ‖∫ ω, ‖(T⁻¹ : ℂ) * (∫ s in Set.Icc (0 : ℝ) T, A s ω) - EA‖^2 ∂μ‖ ≤
      T⁻¹^2 * ‖∫ s in Set.Icc (0 : ℝ) T, ∫ u in Set.Icc (0 : ℝ) T, Cov s u‖ := by
  intro Cov
  -- Step 0: Outer ‖·‖ on nonneg real = id
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  -- Step 1: Factor T⁻² out: ‖T⁻¹ * S - EA‖² = T⁻² * ‖S - T*EA‖²
  have hT_ne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hT)
  have h_factor : ∀ ω, ‖(T⁻¹ : ℂ) * (∫ s in Set.Icc 0 T, A s ω) - EA‖ ^ 2 =
      T⁻¹ ^ 2 * ‖(∫ s in Set.Icc 0 T, A s ω) - ↑T * EA‖ ^ 2 := by
    intro ω
    have halg : (T⁻¹ : ℂ) * (∫ s in Set.Icc 0 T, A s ω) - EA =
        (↑T)⁻¹ * ((∫ s in Set.Icc 0 T, A s ω) - ↑T * EA) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hT_ne, one_mul]
    rw [halg, norm_mul, norm_inv, Complex.norm_of_nonneg hT.le, mul_pow]
  simp_rw [h_factor, integral_const_mul]
  -- Goal: T⁻¹^2 * ∫_Ω ‖S - T*EA‖² ≤ T⁻¹^2 * ‖∫∫ Cov‖
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg T⁻¹)
  -- Key inequality: ∫_Ω ‖Z(ω)‖² dμ ≤ ‖∫∫ Cov‖
  -- where Z(ω) = (∫_{[0,T]} A_s(ω) ds) - T * EA
  -- Proof: LHS = Re(∫∫ Cov) ≤ ‖∫∫ Cov‖
  -- The equality ∫_Ω ‖Z‖² = Re(∫∫ Cov) follows from:
  --   ‖z‖² = Re(z * conj z), Re commutes with ∫,
  --   expand Z = ∫A - T·EA, use bilinearity + h_mean + Fubini
  -- Helper: for a.e. ω, factor Z·conj(Z) = ∫∫ (A_s-EA)·conj(A_u-EA)
  -- where Z(ω) = (∫_s A_s ω) - T*EA. Uses integral_prod_mul + integral_conj.
  have h_factor_ae : ∀ᵐ ω ∂μ,
      ((∫ s in Icc 0 T, A s ω) - ↑T * EA) * starRingEnd ℂ ((∫ s in Icc 0 T, A s ω) - ↑T * EA) =
      ∫ su : ℝ × ℝ, (A su.1 ω - EA) * starRingEnd ℂ (A su.2 ω - EA)
        ∂((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) := by
    filter_upwards [h_slice_int] with ω hω
    have h_sum : ∫ s in Icc 0 T, (A s ω - EA) =
        (∫ s in Icc 0 T, A s ω) - ↑T * EA := by
      rw [integral_sub hω (integrable_const EA), integral_const, measureReal_def,
        Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
        sub_zero]; congr 1
    rw [← h_sum]
    have : starRingEnd ℂ (∫ s in Icc 0 T, A s ω - EA) =
        ∫ s in Icc 0 T, starRingEnd ℂ (A s ω - EA) := by
      exact ((@RCLike.conjLIE ℂ _).toLinearIsometry.integral_comp_comm _).symm
    rw [this]
    exact (integral_prod_mul (μ := volume.restrict (Icc 0 T)) (ν := volume.restrict (Icc 0 T))
      (fun s => A s ω - EA) (fun u => starRingEnd ℂ (A u ω - EA))).symm
  -- Step A: Integrability of Z * conj Z (from h_Fubini via Fubini marginal)
  have h_int_Zconj : Integrable
      (fun ω => ((∫ s in Icc 0 T, A s ω) - ↑T * EA) *
        starRingEnd ℂ ((∫ s in Icc 0 T, A s ω) - ↑T * EA)) μ :=
    h_Fubini.integral_prod_left.congr (h_factor_ae.mono fun ω hω => hω.symm)
  -- Step B: Fubini identity ∫_Ω Z·conj(Z) dμ = ∫∫ Cov
  -- Bilinear expansion: ∫_Ω (A_s-EA)·conj(A_u-EA) dμ = Cov(s,u)
  have h_inner : ∀ s u,
      ∫ ω, (A s ω - EA) * starRingEnd ℂ (A u ω - EA) ∂μ = Cov s u := by
    intro s u
    have hs := (h_slice_L2 s).integrable one_le_two
    have hsu : Integrable (fun ω : Ω => A s ω * starRingEnd ℂ (A u ω)) μ :=
      (h_slice_L2 s).integrable_mul (h_slice_L2 u).star (p := 2) (q := 2)
    have hEA_conjA : Integrable (fun ω : Ω => EA * starRingEnd ℂ (A u ω)) μ :=
      ((h_slice_L2 u).star.integrable one_le_two).const_mul _
    -- Distribute: (A-EA)*conj(A-EA) = (A-EA)*conjA - (A-EA)*conjEA
    simp_rw [map_sub, mul_sub]
    have hf : Integrable (fun ω : Ω => (A s ω - EA) * starRingEnd ℂ (A u ω)) μ :=
      (hsu.sub hEA_conjA).congr (ae_of_all _ fun ω => by simp only [Pi.sub_apply]; ring)
    have hg : Integrable (fun ω : Ω => (A s ω - EA) * starRingEnd ℂ EA) μ :=
      (hs.sub (integrable_const _)).mul_const _
    rw [integral_sub hf hg]
    simp_rw [sub_mul]
    rw [integral_sub hsu hEA_conjA,
        integral_sub (hs.mul_const _) (integrable_const _)]
    have h1 : ∫ a, A s a * starRingEnd ℂ EA ∂μ = (∫ a, A s a ∂μ) * starRingEnd ℂ EA :=
      integral_mul_const _ _
    have h2 : ∫ a, EA * starRingEnd ℂ (A u a) ∂μ = EA * ∫ a, starRingEnd ℂ (A u a) ∂μ :=
      integral_const_mul _ _
    have h3 : ∫ a, starRingEnd ℂ (A u a) ∂μ = starRingEnd ℂ (∫ a, A u a ∂μ) :=
      ((@RCLike.conjLIE ℂ _).toLinearIsometry.integral_comp_comm _)
    rw [h1, h2, h3, integral_const,
        h_mean s, h_mean u, show μ.real univ = (1 : ℝ) from probReal_univ,
        one_smul]; ring
  have h_complex_eq :
      ∫ ω, ((∫ s in Icc 0 T, A s ω) - ↑T * EA) *
        starRingEnd ℂ ((∫ s in Icc 0 T, A s ω) - ↑T * EA) ∂μ =
      ∫ (s : ℝ) in Icc 0 T, ∫ (u : ℝ) in Icc 0 T, Cov s u :=
    calc ∫ ω, ((∫ s in Icc 0 T, A s ω) - ↑T * EA) *
          starRingEnd ℂ ((∫ s in Icc 0 T, A s ω) - ↑T * EA) ∂μ
        = ∫ ω, ∫ su : ℝ × ℝ, (A su.1 ω - EA) * starRingEnd ℂ (A su.2 ω - EA)
            ∂((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∂μ :=
          integral_congr_ae h_factor_ae
      _ = ∫ su : ℝ × ℝ, ∫ ω, (A su.1 ω - EA) * starRingEnd ℂ (A su.2 ω - EA) ∂μ
            ∂((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) :=
          integral_integral_swap h_Fubini
      _ = ∫ su : ℝ × ℝ, Cov su.1 su.2
            ∂((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) := by
          congr 1; ext su; exact h_inner su.1 su.2
      _ = ∫ s in Icc 0 T, ∫ u in Icc 0 T, Cov s u :=
          integral_prod (f := fun su => Cov su.1 su.2)
            (h_Fubini.integral_prod_right.congr (ae_of_all _ fun su => h_inner su.1 su.2))
  -- Step C: ‖z‖² = Re(z · conj z), commute Re with ∫
  have h_re : ∀ z : ℂ, ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := by
    intro z; simp [RCLike.mul_conj, sq]
  have h_eq : (∫ ω, ‖(∫ s in Icc 0 T, A s ω) - ↑T * EA‖ ^ 2 ∂μ) =
      (∫ (s : ℝ) in Icc 0 T, ∫ (u : ℝ) in Icc 0 T, Cov s u).re := by
    calc (∫ ω, ‖(∫ s in Icc 0 T, A s ω) - ↑T * EA‖ ^ 2 ∂μ)
        = ∫ ω, RCLike.re (((∫ s in Icc 0 T, A s ω) - ↑T * EA) *
            starRingEnd ℂ ((∫ s in Icc 0 T, A s ω) - ↑T * EA)) ∂μ := by
          congr 1; ext ω; exact h_re _
      _ = (∫ ω, ((∫ s in Icc 0 T, A s ω) - ↑T * EA) *
            starRingEnd ℂ ((∫ s in Icc 0 T, A s ω) - ↑T * EA) ∂μ).re :=
          integral_re h_int_Zconj
      _ = (∫ s in Icc 0 T, ∫ u in Icc 0 T, Cov s u).re := by rw [h_complex_eq]
  -- Final: ∫ ‖Z‖² = Re(∫∫ Cov) ≤ ‖∫∫ Cov‖
  calc ∫ ω, ‖(∫ (s : ℝ) in Icc 0 T, A s ω) - ↑T * EA‖ ^ 2 ∂μ
      = (∫ (s : ℝ) in Icc 0 T, ∫ (u : ℝ) in Icc 0 T, Cov s u).re := h_eq
    _ ≤ ‖∫ (s : ℝ) in Icc 0 T, ∫ (u : ℝ) in Icc 0 T, Cov s u‖ :=
        Complex.re_le_norm _

end VarianceBound

end

/-! ## Fubini Integrability of L² Process Covariance

Proves that (A_s(ω) - c) · conj(A_u(ω) - c) is integrable on the triple product Ω × [0,T] × [0,T],
given that A is jointly L² on [0,T] × Ω, continuous in time, and measurable in ω.

Strategy: bound |f·g| ≤ |f|² + |g|² to decouple the product, then use Tonelli to
factor the triple integral into ν(univ) × double integral, which is finite by L².
-/

open Function ENNReal

private lemma ennreal_mul_le_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
    _ = b ^ 2 := (sq b).symm
    _ ≤ a ^ 2 + b ^ 2 := le_add_left (le_refl _)
  · calc a * b ≤ a * a := by gcongr
    _ = a ^ 2 := (sq a).symm
    _ ≤ a ^ 2 + b ^ 2 := le_add_right (le_refl _)

private lemma memLp_two_lintegral_nnnorm_sq {α ε : Type*} [MeasurableSpace α]
    [NormedAddCommGroup ε] {f : α → ε} {μ : Measure α} (hf : MemLp f 2 μ) :
    ∫⁻ x, ↑‖f x‖₊ ^ (2 : ℕ) ∂μ < ⊤ := by
  have h := hf.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)] at h
  simp only [toReal_ofNat] at h
  rw [rpow_lt_top_iff_of_pos (by positivity : (0:ℝ) < 1/2)] at h
  refine lt_of_eq_of_lt ?_ h
  congr 1; ext x
  rw [enorm_eq_nnnorm, ← rpow_natCast (↑‖f x‖₊) 2]
  norm_cast

/-- Term-by-term finiteness used in `L2_process_covariance_fubini_integrable` (factor out the
last `ℝ`-coordinate via Tonelli).
-/
private lemma l2cov_term_finite {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ} [SFinite μ] [SFinite ν] {A : ℝ → Ω → ℂ} {c : ℂ}
    (hm : Measurable (fun x : Ω × (ℝ × ℝ) => (↑‖A x.2.1 x.1 - c‖₊ : ℝ≥0∞) ^ 2))
    (hF_meas_swap : Measurable (fun p : Ω × ℝ => (↑‖A p.2 p.1 - c‖₊ : ℝ≥0∞) ^ 2))
    (h_both_finite : ν Set.univ * ∫⁻ z : ℝ × Ω, ↑‖A z.1 z.2 - c‖₊ ^ 2 ∂(ν.prod μ) < ⊤)
    (h_inner : ∀ ω, ∫⁻ p : ℝ × ℝ, (↑‖A p.1 ω - c‖₊ : ℝ≥0∞) ^ 2 ∂(ν.prod ν)
        = (∫⁻ s, (↑‖A s ω - c‖₊ : ℝ≥0∞) ^ 2 ∂ν) * ν Set.univ) :
    ∫⁻ x : Ω × (ℝ × ℝ), (↑‖A x.2.1 x.1 - c‖₊ : ℝ≥0∞) ^ 2 ∂(μ.prod (ν.prod ν)) < ⊤ := by
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [h_inner]
  rw [lintegral_mul_const _ hF_meas_swap.lintegral_prod_right', mul_comm]
  conv_lhs => rw [show (fun ω => ∫⁻ s, (↑‖A s ω - c‖₊ : ℝ≥0∞) ^ 2 ∂ν) =
    (fun ω => ∫⁻ s, (fun z : Ω × ℝ => (↑‖A z.2 z.1 - c‖₊ : ℝ≥0∞) ^ 2) (ω, s) ∂ν)
    from rfl]
  rw [lintegral_lintegral hF_meas_swap.aemeasurable, ← lintegral_prod_swap]
  exact h_both_finite

/-- Term-by-term finiteness used in `L2_process_covariance_fubini_integrable` (factor out the
first `ℝ`-coordinate via Tonelli).
-/
private lemma l2cov_term2_finite {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ} [SFinite μ] [SFinite ν] {A : ℝ → Ω → ℂ} {c : ℂ}
    (hm : Measurable (fun x : Ω × (ℝ × ℝ) => (↑‖A x.2.2 x.1 - c‖₊ : ℝ≥0∞) ^ 2))
    (hF_meas_swap : Measurable (fun p : Ω × ℝ => (↑‖A p.2 p.1 - c‖₊ : ℝ≥0∞) ^ 2))
    (h_both_finite : ν Set.univ * ∫⁻ z : ℝ × Ω, ↑‖A z.1 z.2 - c‖₊ ^ 2 ∂(ν.prod μ) < ⊤)
    (h_inner : ∀ ω, ∫⁻ p : ℝ × ℝ, (↑‖A p.2 ω - c‖₊ : ℝ≥0∞) ^ 2 ∂(ν.prod ν)
        = ν Set.univ * ∫⁻ u, (↑‖A u ω - c‖₊ : ℝ≥0∞) ^ 2 ∂ν) :
    ∫⁻ x : Ω × (ℝ × ℝ), (↑‖A x.2.2 x.1 - c‖₊ : ℝ≥0∞) ^ 2 ∂(μ.prod (ν.prod ν)) < ⊤ := by
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [h_inner]
  rw [lintegral_const_mul _ hF_meas_swap.lintegral_prod_right']
  conv_lhs => rw [show (fun ω => ∫⁻ u, (↑‖A u ω - c‖₊ : ℝ≥0∞) ^ 2 ∂ν) =
    (fun ω => ∫⁻ s, (fun z : Ω × ℝ => (↑‖A z.2 z.1 - c‖₊ : ℝ≥0∞) ^ 2) (ω, s) ∂ν)
    from rfl]
  rw [lintegral_lintegral hF_meas_swap.aemeasurable, ← lintegral_prod_swap]
  exact h_both_finite

/-- Inner Tonelli rewrite for `L2_process_covariance_fubini_integrable`,
factoring out the first coordinate. -/
private lemma l2cov_inner_fst {Ω : Type*} {A : ℝ → Ω → ℂ} {c : ℂ} {ν : Measure ℝ} [SFinite ν]
    (hg_meas : ∀ ω, Measurable (fun s : ℝ => (↑‖A s ω - c‖₊ : ℝ≥0∞) ^ 2)) (ω : Ω) :
    ∫⁻ p : ℝ × ℝ, (↑‖A p.1 ω - c‖₊ : ℝ≥0∞) ^ 2 ∂(ν.prod ν)
      = (∫⁻ s, (↑‖A s ω - c‖₊ : ℝ≥0∞) ^ 2 ∂ν) * ν Set.univ := by
  have key := @lintegral_prod_mul ℝ ℝ _ _ ν ν _
    (fun s => (↑‖A s ω - c‖₊ : ℝ≥0∞) ^ 2) (fun _ => 1)
    (hg_meas ω).aemeasurable aemeasurable_const
  simpa only [mul_one, lintegral_one] using key

/-- Inner Tonelli rewrite for `L2_process_covariance_fubini_integrable`,
factoring out the second coordinate. -/
private lemma l2cov_inner_snd {Ω : Type*} {A : ℝ → Ω → ℂ} {c : ℂ} {ν : Measure ℝ} [SFinite ν]
    (hg_meas : ∀ ω, Measurable (fun s : ℝ => (↑‖A s ω - c‖₊ : ℝ≥0∞) ^ 2)) (ω : Ω) :
    ∫⁻ p : ℝ × ℝ, (↑‖A p.2 ω - c‖₊ : ℝ≥0∞) ^ 2 ∂(ν.prod ν)
      = ν Set.univ * ∫⁻ u, (↑‖A u ω - c‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  have key := @lintegral_prod_mul ℝ ℝ _ _ ν ν _
    (fun _ => (1 : ℝ≥0∞)) (fun u => (↑‖A u ω - c‖₊ : ℝ≥0∞) ^ 2)
    aemeasurable_const (hg_meas ω).aemeasurable
  simpa only [one_mul, lintegral_one] using key

theorem _root_.OSforGFF.L2_process_covariance_fubini_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℝ → Ω → ℂ) (c : ℂ) (T : ℝ) (_hT : T > 0)
    (h_L2 : MemLp (uncurry A) 2
      ((volume.restrict (Icc 0 T)).prod μ))
    (h_cont_s : ∀ ω, Continuous (fun s => A s ω))
    (h_sm_slice : ∀ s, StronglyMeasurable (fun ω => A s ω)) :
    Integrable (fun (x : Ω × (ℝ × ℝ)) =>
      (A x.2.1 x.1 - c) * starRingEnd ℂ (A x.2.2 x.1 - c))
      (μ.prod ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T)))) := by
  let ν := volume.restrict (Icc 0 T)
  have hA_sm : StronglyMeasurable (uncurry A) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun ω => h_cont_s ω) h_sm_slice
  have hF_sm : StronglyMeasurable (fun p : ℝ × Ω => A p.1 p.2 - c) :=
    hA_sm.sub stronglyMeasurable_const
  have hm_s : Measurable (fun x : Ω × (ℝ × ℝ) => (x.2.1, x.1)) :=
    Measurable.prodMk (measurable_fst.comp measurable_snd) measurable_fst
  have hm_u : Measurable (fun x : Ω × (ℝ × ℝ) => (x.2.2, x.1)) :=
    Measurable.prodMk (measurable_snd.comp measurable_snd) measurable_fst
  have h1 : StronglyMeasurable (fun x : Ω × (ℝ × ℝ) => A x.2.1 x.1 - c) :=
    hF_sm.comp_measurable hm_s
  have h2 : StronglyMeasurable (fun x : Ω × (ℝ × ℝ) => A x.2.2 x.1 - c) :=
    hF_sm.comp_measurable hm_u
  refine ⟨(h1.mul h2.star).aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, enorm]
  have h_bound : ∀ x : Ω × (ℝ × ℝ),
      (↑‖(A x.2.1 x.1 - c) * starRingEnd ℂ (A x.2.2 x.1 - c)‖₊ : ℝ≥0∞) ≤
      ↑‖A x.2.1 x.1 - c‖₊ ^ 2 + ↑‖A x.2.2 x.1 - c‖₊ ^ 2 := by
    intro x
    rw [nnnorm_mul, coe_mul, show ‖starRingEnd ℂ (A x.2.2 x.1 - c)‖₊ = ‖A x.2.2 x.1 - c‖₊
      from nnnorm_star _]
    exact ennreal_mul_le_add_sq _ _
  have hm1 : Measurable (fun x : Ω × (ℝ × ℝ) => (↑‖A x.2.1 x.1 - c‖₊ : ℝ≥0∞) ^ 2) :=
    (h1.measurable.nnnorm.coe_nnreal_ennreal).pow_const _
  have hm2 : Measurable (fun x : Ω × (ℝ × ℝ) => (↑‖A x.2.2 x.1 - c‖₊ : ℝ≥0∞) ^ 2) :=
    (h2.measurable.nnnorm.coe_nnreal_ennreal).pow_const _
  have hν_fin : ν Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top
  have hF_meas : Measurable (fun z : ℝ × Ω => (↑‖A z.1 z.2 - c‖₊ : ℝ≥0∞) ^ 2) :=
    (hF_sm.measurable.nnnorm.coe_nnreal_ennreal).pow_const _
  have h_lint_base : ∫⁻ z : ℝ × Ω, ↑‖uncurry A z - c‖₊ ^ (2 : ℕ) ∂(ν.prod μ) < ⊤ :=
    memLp_two_lintegral_nnnorm_sq (h_L2.sub (memLp_const c))
  have h_both_finite : ν Set.univ * ∫⁻ z : ℝ × Ω, ↑‖A z.1 z.2 - c‖₊ ^ 2 ∂(ν.prod μ) < ⊤ :=
    mul_lt_top hν_fin h_lint_base
  haveI : SFinite ν := inferInstance
  have hg_meas : ∀ ω, Measurable (fun s : ℝ => (↑‖A s ω - c‖₊ : ℝ≥0∞) ^ 2) := fun ω =>
    ((h_cont_s ω).sub continuous_const).measurable.nnnorm.coe_nnreal_ennreal.pow_const _
  have hF_meas_swap : Measurable (fun p : Ω × ℝ => (↑‖A p.2 p.1 - c‖₊ : ℝ≥0∞) ^ 2) := by
    fun_prop
  calc ∫⁻ x, ↑‖(A x.2.1 x.1 - c) * starRingEnd ℂ (A x.2.2 x.1 - c)‖₊
        ∂(μ.prod (ν.prod ν))
      ≤ ∫⁻ x, (↑‖A x.2.1 x.1 - c‖₊ ^ 2 + ↑‖A x.2.2 x.1 - c‖₊ ^ 2)
        ∂(μ.prod (ν.prod ν)) := lintegral_mono h_bound
    _ = (∫⁻ x, ↑‖A x.2.1 x.1 - c‖₊ ^ 2 ∂(μ.prod (ν.prod ν))) +
        (∫⁻ x, ↑‖A x.2.2 x.1 - c‖₊ ^ 2 ∂(μ.prod (ν.prod ν))) :=
        lintegral_add_left hm1 _
    _ < ⊤ :=
        ENNReal.add_lt_top.mpr ⟨l2cov_term_finite hm1 hF_meas_swap h_both_finite
            (l2cov_inner_fst hg_meas),
          l2cov_term2_finite hm2 hF_meas_swap h_both_finite (l2cov_inner_snd hg_meas)⟩

end OSforGFF
