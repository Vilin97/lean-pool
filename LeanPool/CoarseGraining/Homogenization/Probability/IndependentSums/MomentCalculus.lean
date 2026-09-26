/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite real-exponent moment calculus

This module collects source-neutral real-exponent `L^p` aggregation bounds for
finite families of real random variables.
-/

@[expose] public section

namespace Homogenization.IndependentSums

open MeasureTheory

noncomputable section

private theorem memLp_of_integrable_abs_rpow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : Measurable f)
    (hfp : Integrable (fun ω => |f ω| ^ p) μ) :
    MemLp f (ENNReal.ofReal p) μ := by
  rw [← integrable_norm_rpow_iff hf.aestronglyMeasurable
    (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hp]) ENNReal.ofReal_ne_top]
  simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le] using hfp

private theorem toReal_eLpNorm_eq_integral_abs_rpow_rpow_inv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hfp : MemLp f (ENNReal.ofReal p) μ) :
    ENNReal.toReal (eLpNorm f (ENNReal.ofReal p) μ) =
      (∫ ω, |f ω| ^ p ∂μ) ^ p⁻¹ := by
  have hnonneg :
      0 ≤ (∫ ω, ‖f ω‖ ^ (ENNReal.ofReal p).toReal ∂μ) ^
        (ENNReal.ofReal p).toReal⁻¹ := by
    positivity
  rw [hfp.eLpNorm_eq_integral_rpow_norm
    (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hp]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hnonneg]
  simp [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le]

/-- A finite real `p`-moment on a probability space implies integrability. -/
theorem integrable_of_integrable_abs_rpow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : Measurable f)
    (hfp : Integrable (fun ω => |f ω| ^ p) μ) :
    Integrable f μ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hmem : MemLp f (ENNReal.ofReal p) μ :=
    memLp_of_integrable_abs_rpow hp_pos hf hfp
  exact hmem.integrable (ENNReal.one_le_ofReal.mpr hp)

/-- Centering a real random variable preserves integrability of a finite real
`p`-moment on a probability space. -/
theorem integrable_abs_sub_integral_rpow_of_integrable_abs_rpow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : Measurable f)
    (hfp : Integrable (fun ω => |f ω| ^ p) μ) :
    Integrable (fun ω => |f ω - ∫ z, f z ∂μ| ^ p) μ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_enn_ne_zero : ENNReal.ofReal p ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hp_pos)
  have hmem : MemLp f (ENNReal.ofReal p) μ :=
    memLp_of_integrable_abs_rpow hp_pos hf hfp
  have hcenter : MemLp (fun ω => f ω - ∫ z, f z ∂μ) (ENNReal.ofReal p) μ := by
    show MemLp (f - fun _ => ∫ z, f z ∂μ) (ENNReal.ofReal p) μ
    exact hmem.sub (memLp_const (∫ z, f z ∂μ))
  have hcenter_int :
      Integrable (fun ω => ‖f ω - ∫ z, f z ∂μ‖ ^ (ENNReal.ofReal p).toReal) μ :=
    (integrable_norm_rpow_iff hcenter.aestronglyMeasurable hp_enn_ne_zero ENNReal.ofReal_ne_top).mpr hcenter
  simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le] using hcenter_int

/-- On a probability space, a finite real `p`-moment gives any lower real
moment at exponent at least one. -/
theorem integrable_abs_rpow_of_integrable_abs_rpow_of_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {q p : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p)
    (hf : Measurable f)
    (hfp : Integrable (fun ω => |f ω| ^ p) μ) :
    Integrable (fun ω => |f ω| ^ q) μ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one (hq.trans hqp)
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmem_p : MemLp f (ENNReal.ofReal p) μ :=
    memLp_of_integrable_abs_rpow hp_pos hf hfp
  have hmem_q : MemLp f (ENNReal.ofReal q) μ :=
    hmem_p.mono_exponent (ENNReal.ofReal_le_ofReal hqp)
  have hq_int : Integrable (fun ω => ‖f ω‖ ^ (ENNReal.ofReal q).toReal) μ :=
    hmem_q.integrable_norm_rpow
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq_pos)) ENNReal.ofReal_ne_top
  simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hq_pos.le] using hq_int

/-- On a probability space, normalized real `L^q` moments are monotone in
the exponent. -/
theorem integral_abs_rpow_rpow_inv_le_of_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {q p : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p)
    (hf : Measurable f)
    (hfp : Integrable (fun ω => |f ω| ^ p) μ) :
    (∫ ω, |f ω| ^ q ∂μ) ^ q⁻¹ ≤ (∫ ω, |f ω| ^ p ∂μ) ^ p⁻¹ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one (hq.trans hqp)
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmem_p : MemLp f (ENNReal.ofReal p) μ :=
    memLp_of_integrable_abs_rpow hp_pos hf hfp
  have hmem_q : MemLp f (ENNReal.ofReal q) μ :=
    hmem_p.mono_exponent (ENNReal.ofReal_le_ofReal hqp)
  have hcmp : eLpNorm f (ENNReal.ofReal q) μ ≤ eLpNorm f (ENNReal.ofReal p) μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqp)
  have hcmp_toReal :
      ENNReal.toReal (eLpNorm f (ENNReal.ofReal q) μ) ≤
        ENNReal.toReal (eLpNorm f (ENNReal.ofReal p) μ) :=
    ENNReal.toReal_mono hmem_p.eLpNorm_ne_top hcmp
  calc
    (∫ ω, |f ω| ^ q ∂μ) ^ q⁻¹ =
        ENNReal.toReal (eLpNorm f (ENNReal.ofReal q) μ) := by
          symm
          exact toReal_eLpNorm_eq_integral_abs_rpow_rpow_inv hq_pos hmem_q
    _ ≤ ENNReal.toReal (eLpNorm f (ENNReal.ofReal p) μ) := hcmp_toReal
    _ = (∫ ω, |f ω| ^ p ∂μ) ^ p⁻¹ :=
      toReal_eLpNorm_eq_integral_abs_rpow_rpow_inv hp_pos hmem_p

/-- A finite sum of real random variables with integrable real `p` moments
has an integrable real `p` moment. -/
theorem integrable_abs_finsetSum_rpow
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ι → Ω → ℝ} {s : Finset ι} {p : ℝ}
    (hp : 1 ≤ p)
    (h_meas : ∀ i ∈ s, Measurable (f i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |f i ω| ^ p) μ) :
    Integrable (fun ω => |∑ i ∈ s, f i ω| ^ p) μ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h_memLp : ∀ i ∈ s, MemLp (f i) (ENNReal.ofReal p) μ := by
    intro i hi
    exact memLp_of_integrable_abs_rpow hp_pos (h_meas i hi) (hLp_int i hi)
  have hsum_memLp :
      MemLp (fun ω => ∑ i ∈ s, f i ω) (ENNReal.ofReal p) μ :=
    memLp_finsetSum s h_memLp
  have hsum_int := hsum_memLp.integrable_norm_rpow
    (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hp_pos]) ENNReal.ofReal_ne_top
  simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_pos.le] using hsum_int

/-- The real-exponent `L^p` root of a finite sum is at most the sum of the
individual roots. -/
theorem integral_abs_finsetSum_rpow_rpow_inv_le_sum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ι → Ω → ℝ} {s : Finset ι} {p : ℝ}
    (hp : 1 ≤ p)
    (h_meas : ∀ i ∈ s, Measurable (f i))
    (hLp_int : ∀ i ∈ s, Integrable (fun ω => |f i ω| ^ p) μ) :
    (∫ ω, |∑ i ∈ s, f i ω| ^ p ∂μ) ^ p⁻¹ ≤
      ∑ i ∈ s, (∫ ω, |f i ω| ^ p ∂μ) ^ p⁻¹ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let g : Ω → ℝ := fun ω => ∑ i ∈ s, f i ω
  have h_memLp : ∀ i ∈ s, MemLp (f i) (ENNReal.ofReal p) μ := by
    intro i hi
    exact memLp_of_integrable_abs_rpow hp_pos (h_meas i hi) (hLp_int i hi)
  have hg_memLp : MemLp g (ENNReal.ofReal p) μ := by
    simpa [g] using memLp_finsetSum s h_memLp
  have hg_eq : g = ∑ i ∈ s, f i := by
    funext ω
    simp [g]
  have hg_eLp :
      eLpNorm g (ENNReal.ofReal p) μ ≤
        ∑ i ∈ s, eLpNorm (f i) (ENNReal.ofReal p) μ := by
    rw [hg_eq]
    refine eLpNorm_sum_le ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hg_toReal_le :
      ENNReal.toReal (eLpNorm g (ENNReal.ofReal p) μ) ≤
        ENNReal.toReal (∑ i ∈ s, eLpNorm (f i) (ENNReal.ofReal p) μ) := by
    exact ENNReal.toReal_mono
      (ENNReal.sum_ne_top.2 fun i hi => (h_memLp i hi).eLpNorm_ne_top) hg_eLp
  have hsum_toReal :
      ENNReal.toReal (∑ i ∈ s, eLpNorm (f i) (ENNReal.ofReal p) μ) =
        ∑ i ∈ s, ENNReal.toReal (eLpNorm (f i) (ENNReal.ofReal p) μ) := by
    exact ENNReal.toReal_sum fun i hi => (h_memLp i hi).eLpNorm_ne_top
  calc
    (∫ ω, |∑ i ∈ s, f i ω| ^ p ∂μ) ^ p⁻¹
        = (∫ ω, |g ω| ^ p ∂μ) ^ p⁻¹ := by simp [g]
    _ = ENNReal.toReal (eLpNorm g (ENNReal.ofReal p) μ) := by
      rw [toReal_eLpNorm_eq_integral_abs_rpow_rpow_inv hp_pos hg_memLp]
    _ ≤ ENNReal.toReal (∑ i ∈ s, eLpNorm (f i) (ENNReal.ofReal p) μ) := hg_toReal_le
    _ = ∑ i ∈ s, ENNReal.toReal (eLpNorm (f i) (ENNReal.ofReal p) μ) := hsum_toReal
    _ = ∑ i ∈ s, (∫ ω, |f i ω| ^ p ∂μ) ^ p⁻¹ := by
      refine Finset.sum_congr rfl fun i hi => ?_
      exact toReal_eLpNorm_eq_integral_abs_rpow_rpow_inv hp_pos (h_memLp i hi)

/-- A finite family of nonnegative real numbers satisfies the cardinality
form of Hölder's inequality at a real exponent. -/
theorem sum_rpow_inv_le_card_rpow_mul_rpow_sum
    {ι : Type*} {s : Finset ι} {p : ℝ} {f : ι → ℝ}
    (hp : 1 ≤ p)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ p⁻¹ ≤
      (s.card : ℝ) ^ (1 - p⁻¹) * (∑ i ∈ s, f i) ^ p⁻¹ := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let g : ι → ℝ := fun i => (max (f i) 0) ^ p⁻¹
  have hroot :=
    Real.inner_le_weight_mul_Lp_of_nonneg
      (s := s) (p := p) hp
      (w := fun _ => (1 : ℝ)) (f := g)
      (fun _ => by positivity)
      (fun i => Real.rpow_nonneg (le_max_right _ _) _)
  have hleft :
      ∑ i ∈ s, (fun _ => (1 : ℝ)) i * g i = ∑ i ∈ s, f i ^ p⁻¹ := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [g, max_eq_left (hf i hi)]
  have hright :
      ∑ i ∈ s, (fun _ => (1 : ℝ)) i * g i ^ p = ∑ i ∈ s, f i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [one_mul]
    dsimp [g]
    rw [max_eq_left (hf i hi), ← Real.rpow_mul (hf i hi), inv_mul_cancel₀ hp_pos.ne',
      Real.rpow_one]
  calc
    ∑ i ∈ s, f i ^ p⁻¹ = ∑ i ∈ s, (fun _ => (1 : ℝ)) i * g i := by
      simpa using hleft.symm
    _ ≤ (∑ i ∈ s, (fun _ => (1 : ℝ)) i) ^ (1 - p⁻¹) *
          (∑ i ∈ s, (fun _ => (1 : ℝ)) i * g i ^ p) ^ p⁻¹ := hroot
    _ = (s.card : ℝ) ^ (1 - p⁻¹) * (∑ i ∈ s, f i) ^ p⁻¹ := by
      rw [hright]
      simp

end

end Homogenization.IndependentSums
