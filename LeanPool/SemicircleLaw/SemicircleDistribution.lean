/-
Copyright (c) 2026 FredRaj3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FredRaj3
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Semicircle Distributions over `ℝ`

We define the real-valued Wigner semicircle distribution.

## Main definitions

* `semicirclePDFReal`: the function
  `μ v x ↦ (1 / (2 * π * v)) * √(4 * v - (x - μ) ^ 2)`,
  the probability density function of the semicircle distribution with mean `μ`
  and variance `v` (when `v ≠ 0`).
* `semicirclePDF`: the `ℝ≥0∞`-valued pdf,
  `semicirclePDF μ v x = ENNReal.ofReal (semicirclePDFReal μ v x)`.
* `semicircleReal`: the semicircle measure on `ℝ`, parametrized by mean `μ` and
  variance `v`. If `v = 0`, this is `Measure.dirac μ`; otherwise it is the
  measure with density `semicirclePDF μ v` against the Lebesgue measure.

## Main results

* `semicircleReal_add_const`, `semicircleReal_const_mul`: affine transformations of a semicircular
  random variable stay semicircular, with the mean and variance transformed accordingly.
* `integral_id_semicircleReal`: the mean of `semicircleReal μ v` is its mean parameter `μ`.
* `variance_id_semicircleReal`: the variance of `semicircleReal μ v` is its variance parameter `v`.
* `centralMoment_two_mul_semicircleReal`: the `2 * n`-th central moment of the semicircle
  distribution equals `v ^ n` times the `n`-th Catalan number.
* `centralMoment_odd_semicircleReal`: the odd central moments of the semicircle distribution vanish.
-/

open scoped ENNReal NNReal Real ProbabilityTheory

open MeasureTheory Set

namespace LeanPool.SemicircleLaw

/-- Probability density function of the semicircle distribution with mean `μ` and variance `v`.
Note that the square root of a negative number is defined to be zero. -/
noncomputable
def semicirclePDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2)

lemma semicirclePDFReal_def (μ : ℝ) (v : ℝ≥0) :
    semicirclePDFReal μ v =
      fun x ↦ 1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2) := rfl

@[simp]
lemma semicirclePDFReal_zero_var (m : ℝ) : semicirclePDFReal m 0 = 0 := by
  ext x
  simp [semicirclePDFReal]

/-- The semicircle pdf is nonnegative. -/
lemma semicirclePDFReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ semicirclePDFReal μ v x := by
  rw [semicirclePDFReal]
  positivity

/-- The semicircle pdf is continuous. -/
lemma continuous_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    Continuous (semicirclePDFReal μ v) := by
  rw [semicirclePDFReal_def]
  fun_prop

/-- The semicircle pdf is measurable. -/
@[fun_prop]
lemma measurable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    Measurable (semicirclePDFReal μ v) :=
  (continuous_semicirclePDFReal μ v).measurable

/-- The semicircle pdf is strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    StronglyMeasurable (semicirclePDFReal μ v) :=
  (measurable_semicirclePDFReal μ v).stronglyMeasurable

/-- The support of the semicircle pdf is contained in `[μ - 2√v, μ + 2√v]`. -/
lemma support_semicirclePDFReal_subset (μ : ℝ) (v : ℝ≥0) :
    Function.support (semicirclePDFReal μ v) ⊆ Icc (μ - 2 * √v) (μ + 2 * √v) := by
  intro x hx
  by_contra hxI
  apply hx
  unfold semicirclePDFReal
  have h_abs : 2 * √v ≤ |x - μ| := by
    rcases not_and_or.mp (mt mem_Icc.mpr hxI) with h | h
    · push Not at h
      have : 2 * √v ≤ μ - x := by linarith
      have h2 : 0 ≤ μ - x := by
        have : (0 : ℝ) ≤ √v := Real.sqrt_nonneg _
        linarith
      rw [show |x - μ| = μ - x by rw [abs_sub_comm]; exact abs_of_nonneg h2]
      exact this
    · push Not at h
      have : 2 * √v ≤ x - μ := by linarith
      have h2 : 0 ≤ x - μ := by
        have : (0 : ℝ) ≤ √v := Real.sqrt_nonneg _
        linarith
      rw [abs_of_nonneg h2]
      exact this
  have h_sq : 4 * (v : ℝ) ≤ (x - μ) ^ 2 := by
    have h_sq_abs : (2 * √v) ^ 2 ≤ |x - μ| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h_abs 2
    rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg v), sq_abs] at h_sq_abs
    linarith
  have h_nonpos : 4 * (v : ℝ) - (x - μ) ^ 2 ≤ 0 := by linarith
  rw [Real.sqrt_eq_zero_of_nonpos h_nonpos, mul_zero]

/-- The semicircle pdf is integrable. -/
@[fun_prop]
lemma integrable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (semicirclePDFReal μ v) := by
  have h_cont : Continuous (semicirclePDFReal μ v) := continuous_semicirclePDFReal μ v
  have h_compact : IsCompact (Icc (μ - 2 * √v) (μ + 2 * √v)) := isCompact_Icc
  have h_int_on : IntegrableOn (semicirclePDFReal μ v) (Icc (μ - 2 * √v) (μ + 2 * √v)) :=
    h_cont.continuousOn.integrableOn_compact h_compact
  exact (integrableOn_iff_integrable_of_support_subset
    (support_semicirclePDFReal_subset μ v)).mp h_int_on

lemma sqrt_semicircle_affine (v : ℝ≥0) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    √(4 * (v : ℝ) - (2 * √(v : ℝ) * y) ^ 2) =
      2 * √(v : ℝ) * √(1 - y ^ 2) := by
  have hv_nonneg : 0 ≤ (v : ℝ) := NNReal.coe_nonneg v
  have hy_abs : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hy_sq : y ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one y).2 hy_abs
  calc
    √(4 * (v : ℝ) - (2 * √(v : ℝ) * y) ^ 2)
        = √((4 * (v : ℝ)) * (1 - y ^ 2)) := by
          congr 1
          nlinarith [Real.sq_sqrt hv_nonneg]
    _ = √(4 * (v : ℝ)) * √(1 - y ^ 2) := by
          rw [Real.sqrt_mul (mul_nonneg (by norm_num) hv_nonneg) (1 - y ^ 2)]
    _ = 2 * √(v : ℝ) * √(1 - y ^ 2) := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)) (v : ℝ)]
          have h_sqrt_four : √(4 : ℝ) = 2 := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
            norm_num
          rw [h_sqrt_four]

/-- The unnormalized semicircle kernel has integral `2 * π * v` over its support interval. -/
lemma integral_sqrt_semicircle_interval (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x in μ - 2 * √(v : ℝ)..μ + 2 * √(v : ℝ),
      √(4 * (v : ℝ) - (x - μ) ^ 2) = 2 * π * (v : ℝ) := by
  let c : ℝ := 2 * √(v : ℝ)
  have hv_pos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hv_nonneg : 0 ≤ (v : ℝ) := hv_pos.le
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have h_change :=
    intervalIntegral.smul_integral_comp_mul_add
      (f := fun x ↦ √(4 * (v : ℝ) - (x - μ) ^ 2)) (a := (-1 : ℝ)) (b := 1)
      (c := c) (d := μ)
  calc
    ∫ x in μ - 2 * √(v : ℝ)..μ + 2 * √(v : ℝ),
      √(4 * (v : ℝ) - (x - μ) ^ 2)
        = c * ∫ y in (-1 : ℝ)..1, √(4 * (v : ℝ) - (c * y + μ - μ) ^ 2) := by
          simpa [c, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm]
            using h_change.symm
    _ = c * ∫ y in (-1 : ℝ)..1, c * √(1 - y ^ 2) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro y hy
          have hy' : y ∈ Icc (-1 : ℝ) 1 := by simpa using hy
          simp [c, sqrt_semicircle_affine v hy']
    _ = c * (c * ∫ y in (-1 : ℝ)..1, √(1 - y ^ 2)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = 2 * π * (v : ℝ) := by
          rw [integral_sqrt_one_sub_sq]
          dsimp [c]
          calc
            2 * √(v : ℝ) * (2 * √(v : ℝ) * (π / 2)) =
                2 * π * (√(v : ℝ)) ^ 2 := by ring
            _ = 2 * π * (v : ℝ) := by rw [Real.sq_sqrt hv_nonneg]

/-- The semicircle distribution pdf integrates to 1 when the variance is nonzero. -/
lemma integral_semicirclePDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, semicirclePDFReal μ v x = 1 := by
  have hv_pos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h_support :
      ∫ x in Icc (μ - 2 * √(v : ℝ)) (μ + 2 * √(v : ℝ)), semicirclePDFReal μ v x
        = ∫ x, semicirclePDFReal μ v x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by
        by_contra h
        exact hx (support_semicirclePDFReal_subset μ v h))
  have h_interval :
      ∫ x in Icc (μ - 2 * √(v : ℝ)) (μ + 2 * √(v : ℝ)),
          √(4 * (v : ℝ) - (x - μ) ^ 2)
        = ∫ x in μ - 2 * √(v : ℝ)..μ + 2 * √(v : ℝ),
          √(4 * (v : ℝ) - (x - μ) ^ 2) := by
    have hle : μ - 2 * √(v : ℝ) ≤ μ + 2 * √(v : ℝ) := by
      linarith [Real.sqrt_nonneg (v : ℝ)]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [← h_support]
  simp only [semicirclePDFReal]
  rw [integral_const_mul, h_interval, integral_sqrt_semicircle_interval μ hv]
  field_simp [(show (v : ℝ) ≠ 0 by positivity), Real.pi_ne_zero]

/-- The semicircle distribution pdf has total mass 1 when the variance is nonzero. -/
lemma lintegral_semicirclePDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (semicirclePDFReal μ v x) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_semicirclePDFReal μ v)
    (ae_of_all _ (semicirclePDFReal_nonneg μ v))]
  rw [integral_semicirclePDFReal_eq_one μ hv, ENNReal.ofReal_one]

/-- The `ℝ≥0∞`-valued pdf of a semicircle distribution on `ℝ` with mean `μ` and variance `v`. -/
noncomputable
def semicirclePDF (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (semicirclePDFReal μ v x)

lemma semicirclePDF_def (μ : ℝ) (v : ℝ≥0) :
    semicirclePDF μ v = fun x ↦ ENNReal.ofReal (semicirclePDFReal μ v x) := rfl

@[simp]
lemma semicirclePDF_zero_var (μ : ℝ) : semicirclePDF μ 0 = 0 := by
  ext
  simp [semicirclePDF]

@[simp]
lemma toReal_semicirclePDF {μ : ℝ} {v : ℝ≥0} (x : ℝ) :
    (semicirclePDF μ v x).toReal = semicirclePDFReal μ v x := by
  rw [semicirclePDF, ENNReal.toReal_ofReal (semicirclePDFReal_nonneg μ v x)]

lemma semicirclePDF_lt_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : semicirclePDF μ v x < ∞ := by
  simp [semicirclePDF]

lemma semicirclePDF_ne_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : semicirclePDF μ v x ≠ ∞ :=
  semicirclePDF_lt_top.ne

@[fun_prop]
lemma measurable_semicirclePDF (μ : ℝ) (v : ℝ≥0) : Measurable (semicirclePDF μ v) :=
  (measurable_semicirclePDFReal _ _).ennreal_ofReal

@[simp]
lemma lintegral_semicirclePDF_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ x, semicirclePDF μ v x = 1 :=
  lintegral_semicirclePDFReal_eq_one μ hv

/-- A semicircle distribution on `ℝ` with mean `μ` and variance `v`. -/
noncomputable
def semicircleReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if v = 0 then Measure.dirac μ else volume.withDensity (semicirclePDF μ v)

lemma semicircleReal_of_var_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    semicircleReal μ v = volume.withDensity (semicirclePDF μ v) := if_neg hv

@[simp]
lemma semicircleReal_zero_var (μ : ℝ) : semicircleReal μ 0 = Measure.dirac μ := if_pos rfl

instance instIsProbabilityMeasureSemicircleReal (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (semicircleReal μ v) where
  measure_univ := by by_cases h : v = 0 <;> simp [semicircleReal_of_var_ne_zero, h]

/-- The semicircle pdf vanishes outside the support `[μ - 2√v, μ + 2√v]`. -/
lemma semicirclePDFReal_eq_zero_of_notMem (μ : ℝ) (v : ℝ≥0) {x : ℝ}
    (hx : x ∉ Icc (μ - 2 * √v) (μ + 2 * √v)) :
    semicirclePDFReal μ v x = 0 := by
  by_contra h
  exact hx (support_semicirclePDFReal_subset μ v h)

/-- Translating the input translates the mean in the opposite direction. -/
lemma semicirclePDFReal_sub {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    semicirclePDFReal μ v (x - y) = semicirclePDFReal (μ + y) v x := by
  simp only [semicirclePDFReal]
  rw [sub_add_eq_sub_sub_swap]

/-- Translating the input translates the mean in the opposite direction. -/
lemma semicirclePDFReal_add {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    semicirclePDFReal μ v (x + y) = semicirclePDFReal (μ - y) v x := by
  rw [sub_eq_add_neg, ← semicirclePDFReal_sub, sub_eq_add_neg, neg_neg]

/-- Scaling the input rescales both the mean and variance parameters of the density. -/
lemma semicirclePDFReal_inv_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    semicirclePDFReal μ v (c⁻¹ * x)
      = |c| * semicirclePDFReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) x := by
  rw [semicirclePDFReal, semicirclePDFReal]
  simp only [one_div, NNReal.coe_mul, NNReal.coe_mk]
  have h_arg :
      c⁻¹ * x - μ = c⁻¹ * (x - c * μ) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have h_sqrt₁ :
      √(4 * (v : ℝ) - (c⁻¹ * x - μ) ^ 2)
        = √(4 * (v : ℝ) - (c⁻¹) ^ 2 * (x - c * μ) ^ 2) := by
    rw [h_arg]
    ring_nf
  have h_sqrt₂ :
      √(4 * (v : ℝ) - (c⁻¹) ^ 2 * (x - c * μ) ^ 2)
        = |c⁻¹| * √(4 * (c ^ 2 * v) - (x - c * μ) ^ 2) := by
    have h_factor :
        4 * (v : ℝ) - (c⁻¹) ^ 2 * (x - c * μ) ^ 2
          = (c⁻¹) ^ 2 * (4 * (c ^ 2 * v) - (x - c * μ) ^ 2) := by
      field_simp [hc]
    rw [h_factor, ← sq_abs, Real.sqrt_mul (sq_nonneg _) _, Real.sqrt_sq (abs_nonneg _)]
  rw [h_sqrt₁, h_sqrt₂]
  have h_abs_inv : |c⁻¹| = |c|⁻¹ := abs_inv c
  rw [h_abs_inv]
  field_simp [hc, abs_ne_zero.mpr hc]
  rw [sq_abs]

/-- Scaling the input rescales both the mean and variance parameters of the density. -/
lemma semicirclePDFReal_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    semicirclePDFReal μ v (c * x)
      = |c⁻¹| * semicirclePDFReal (c⁻¹ * μ)
          (.mk ((c ^ 2)⁻¹) (inv_nonneg.mpr (sq_nonneg _)) * v) x := by
  conv_lhs => rw [← inv_inv c, semicirclePDFReal_inv_mul (inv_ne_zero hc)]
  simp

/-- The `ℝ≥0∞`-valued semicircle density is nonnegative. -/
lemma semicirclePDF_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ semicirclePDF μ v x := by
  simp [semicirclePDF]

/-- The support of the `ℝ≥0∞`-valued semicircle density is contained in its support interval. -/
lemma support_semicirclePDF_subset (μ : ℝ) (v : ℝ≥0) :
    Function.support (semicirclePDF μ v) ⊆ Icc (μ - 2 * √v) (μ + 2 * √v) := by
  intro x hx
  exact support_semicirclePDFReal_subset μ v fun hzero ↦ hx (by simp [semicirclePDF, hzero])

/-- The `ℝ≥0∞`-valued semicircle density vanishes outside its support interval. -/
lemma semicirclePDF_eq_zero_of_notMem (μ : ℝ) (v : ℝ≥0) {x : ℝ}
    (hx : x ∉ Icc (μ - 2 * √v) (μ + 2 * √v)) :
    semicirclePDF μ v x = 0 := by
  simp [semicirclePDF, semicirclePDFReal_eq_zero_of_notMem μ v hx]

/-- The semicircle measure has no atoms when the variance is nonzero. -/
lemma noAtoms_semicircleReal {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    NoAtoms (semicircleReal μ v) := by
  rw [semicircleReal_of_var_ne_zero μ hv]; infer_instance

/-- The semicircle measure of a set is the set integral of the density when `v ≠ 0`. -/
lemma semicircleReal_apply (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    semicircleReal μ v s = ∫⁻ x in s, semicirclePDF μ v x := by
  rw [semicircleReal_of_var_ne_zero _ hv, withDensity_apply' _ s]

/-- The semicircle measure of a set as a real integral of the density when `v ≠ 0`. -/
lemma semicircleReal_apply_eq_integral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    semicircleReal μ v s = ENNReal.ofReal (∫ x in s, semicirclePDFReal μ v x) := by
  rw [semicircleReal_apply _ hv s, ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact (integrable_semicirclePDFReal _ _).restrict
  · exact ae_of_all _ (semicirclePDFReal_nonneg _ _)

/-- The semicircle measure is absolutely continuous with respect to the Lebesgue measure
when the variance is nonzero. -/
lemma semicircleReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    semicircleReal μ v ≪ (volume : Measure ℝ) := by
  rw [semicircleReal_of_var_ne_zero μ hv]
  exact withDensity_absolutelyContinuous _ _

/-- The Radon-Nikodym derivative of the semicircle measure with respect to the Lebesgue
measure equals the pdf almost everywhere when the variance is nonzero. -/
lemma rnDeriv_semicircleReal (μ : ℝ) (v : ℝ≥0) :
    (semicircleReal μ v).rnDeriv volume =ᵐ[volume] semicirclePDF μ v := by
  by_cases hv : v = 0
  · simp only [hv, semicircleReal_zero_var, semicirclePDF_zero_var]
    refine (Measure.eq_rnDeriv measurable_zero (mutuallySingular_dirac μ volume) ?_).symm
    rw [withDensity_zero, add_zero]
  · rw [semicircleReal_of_var_ne_zero μ hv]
    exact Measure.rnDeriv_withDensity _ (measurable_semicirclePDF μ v)

/-- Integrating against a non-degenerate semicircle measure is integrating against its density. -/
lemma integral_semicircleReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : ℝ} {v : ℝ≥0} {f : ℝ → E} (hv : v ≠ 0) :
    ∫ x, f x ∂semicircleReal μ v = ∫ x, semicirclePDFReal μ v x • f x := by
  simp [semicircleReal, hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_semicirclePDF _ _)
      (ae_of_all _ fun _ ↦ semicirclePDF_lt_top)]

variable {μ : ℝ} {v : ℝ≥0}

lemma _root_.MeasurableEmbedding.semicircleReal_comap_apply (hv : v ≠ 0)
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f) {f' : ℝ → ℝ}
    (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    (semicircleReal μ v).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * semicirclePDFReal μ v (f x)) := by
  rw [semicircleReal_of_var_ne_zero _ hv, semicirclePDF_def]
  exact hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (semicirclePDFReal_nonneg _ _)) (integrable_semicirclePDFReal _ _)

lemma _root_.MeasurableEquiv.semicircleReal_map_symm_apply (hv : v ≠ 0) (f : ℝ ≃ᵐ ℝ)
    {f' : ℝ → ℝ} (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (semicircleReal μ v).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * semicirclePDFReal μ v (f x)) := by
  rw [semicircleReal_of_var_ne_zero _ hv, semicirclePDF_def]
  exact f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (semicirclePDFReal_nonneg _ _)) (integrable_semicirclePDFReal _ _)

/-- The map of a semicircle distribution by addition of a constant is semicircular. -/
lemma semicircleReal_map_add_const (y : ℝ) :
    (semicircleReal μ v).map (· + y) = semicircleReal (μ + y) v := by
  by_cases hv : v = 0
  · simp [hv, semicircleReal_zero_var]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ 1) x) x := fun _ ↦ (hasDerivAt_id _).sub_const y
  change (semicircleReal μ v).map e.symm = semicircleReal (μ + y) v
  ext s hs
  rw [MeasurableEquiv.semicircleReal_map_symm_apply hv e he' hs]
  simp only [abs_one, one_mul]
  rw [semicircleReal_apply_eq_integral _ hv s]
  simp [e, semicirclePDFReal_sub _ y, Homeomorph.addRight, ← sub_eq_add_neg]

/-- The map of a semicircle distribution by addition of a constant is semicircular. -/
lemma semicircleReal_map_const_add (y : ℝ) :
    (semicircleReal μ v).map (y + ·) = semicircleReal (μ + y) v := by
  simp_rw [add_comm y]
  exact semicircleReal_map_add_const y

/-- The map of a semicircle distribution by multiplication by a constant is semicircular. -/
lemma semicircleReal_map_const_mul (c : ℝ) :
    (semicircleReal μ v).map (c * ·) =
      semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) := by
  by_cases hv : v = 0
  · simp [hv, mul_zero, semicircleReal_zero_var]
  by_cases hc : c = 0
  · simp [hc, zero_mul]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ c⁻¹) x) x := by
    suffices ∀ x, HasDerivAt (fun x ↦ c⁻¹ * x) (c⁻¹ * 1) x by
      rwa [mul_one] at this
    exact fun _ ↦ HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (semicircleReal μ v).map e.symm =
    semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
  ext s hs
  rw [MeasurableEquiv.semicircleReal_map_symm_apply hv e he' hs,
    semicircleReal_apply_eq_integral _ _ s]
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.mulLeft₀, Equiv.mulLeft₀_symm_apply,
    Homeomorph.toMeasurableEquiv_coe, Homeomorph.homeomorph_mk_coe_symm,
    semicirclePDFReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv, inv_mul_cancel₀]
  rwa [ne_eq, abs_eq_zero]

/-- The map of a semicircle distribution by multiplication by a constant is semicircular. -/
lemma semicircleReal_map_mul_const (c : ℝ) :
    (semicircleReal μ v).map (· * c) =
      semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) := by
  simp_rw [mul_comm _ c]
  exact semicircleReal_map_const_mul c

lemma semicircleReal_map_neg :
    (semicircleReal μ v).map (fun x ↦ -x) = semicircleReal (-μ) v := by
  simpa using semicircleReal_map_const_mul (μ := μ) (v := v) (-1)

/-- The map of a semicircle distribution by division by a constant is semicircular. -/
lemma semicircleReal_map_div_const (c : ℝ) :
    (semicircleReal μ v).map (· / c) =
      semicircleReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _)) := by
  simp_rw [div_eq_mul_inv]
  convert semicircleReal_map_mul_const (μ := μ) (v := v) c⁻¹ using 2 <;> rw [mul_comm]
  ext
  simp

lemma semicircleReal_map_sub_const (y : ℝ) :
    (semicircleReal μ v).map (· - y) = semicircleReal (μ - y) v := by
  simp_rw [sub_eq_add_neg, semicircleReal_map_add_const]

lemma semicircleReal_map_const_sub (y : ℝ) :
    (semicircleReal μ v).map (y - ·) = semicircleReal (y - μ) v := by
  simp_rw [sub_eq_add_neg]
  have : (fun x ↦ y + -x) = (fun x ↦ y + x) ∘ fun x ↦ -x := by ext; simp
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), semicircleReal_map_neg,
    semicircleReal_map_const_add, add_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `X + y` has
semicircular law with mean `μ + y` and variance `v`. -/
lemma semicircleReal_add_const (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (y : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ X ω + y) (semicircleReal (μ + y) v) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_add_const y⟩ hX

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `y + X` has
semicircular law with mean `μ + y` and variance `v`. -/
lemma semicircleReal_const_add (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (y : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ y + X ω) (semicircleReal (μ + y) v) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_const_add y⟩ hX

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `X - y` has
semicircular law with mean `μ - y` and variance `v`. -/
lemma semicircleReal_sub_const (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (y : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ X ω - y) (semicircleReal (μ - y) v) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_sub_const y⟩ hX

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `c * X` has
semicircular law with mean `c * μ` and variance `c ^ 2 * v`. -/
lemma semicircleReal_const_mul (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (c : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ c * X ω)
      (semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_const_mul c⟩ hX

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `X * c` has
semicircular law with mean `c * μ` and variance `c ^ 2 * v`. -/
lemma semicircleReal_mul_const (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (c : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ X ω * c)
      (semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_mul_const c⟩ hX

lemma semicircleReal_neg (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P) :
    ProbabilityTheory.HasLaw (-X) (semicircleReal (-μ) v) P := by
  rw [Pi.neg_def, ← Function.comp_def]
  exact ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_neg⟩ hX

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `X / c` has
semicircular law with mean `μ / c` and variance `v / c ^ 2`. -/
lemma semicircleReal_div_const (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (c : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ X ω / c)
      (semicircleReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _))) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_div_const c⟩ hX

lemma semicircleReal_const_sub (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (y : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ y - X ω) (semicircleReal (y - μ) v) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_const_sub y⟩ hX

variable {μ : ℝ} {v : ℝ≥0}

/-- The identity is almost surely bounded under a semicircle distribution. -/
lemma ae_abs_id_le_semicircleReal :
    ∀ᵐ x ∂semicircleReal μ v, |id x| ≤ |μ| + 2 * √(v : ℝ) := by
  by_cases hv : v = 0
  · simp [hv, semicircleReal_zero_var]
  rw [semicircleReal_of_var_ne_zero μ hv]
  rw [ae_withDensity_iff (measurable_semicirclePDF μ v)]
  filter_upwards [] with x hx
  have hxI := support_semicirclePDF_subset μ v hx
  have hx_abs_sub : |x - μ| ≤ 2 * √(v : ℝ) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hxI.1, hxI.2]
  calc
    |id x| = |x| := rfl
    _ = |(x - μ) + μ| := by ring_nf
    _ ≤ |x - μ| + |μ| := abs_add_le _ _
    _ ≤ 2 * √(v : ℝ) + |μ| := by linarith
    _ = |μ| + 2 * √(v : ℝ) := by ring

/-- All finite moments of a real semicircle distribution are finite. -/
lemma memLp_id_semicircleReal (p : ℝ≥0) : MemLp id p (semicircleReal μ v) := by
  have htop : MemLp id ∞ (semicircleReal μ v) :=
    memLp_top_of_bound (by fun_prop) (|μ| + 2 * √(v : ℝ)) ae_abs_id_le_semicircleReal
  exact htop.mono_exponent (by simp)

/-- All finite moments of a real semicircle distribution are finite. -/
lemma memLp_id_semicircleReal' (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp id p (semicircleReal μ v) := by
  lift p to ℝ≥0 using hp
  exact memLp_id_semicircleReal p

/-- The support of the semicircle pdf with mean `μ` and variance `v` is the open interval
`(μ - 2√v, μ + 2√v)`. -/
@[simp]
lemma support_semicirclePDF (hv : v ≠ 0) :
    Function.support (semicirclePDF μ v) = Ioo (μ - 2 * √v) (μ + 2 * √v) := by
  have hv_nonneg : 0 ≤ (v : ℝ) := NNReal.coe_nonneg v
  ext x
  rw [Function.mem_support, semicirclePDF, ne_eq, ENNReal.ofReal_eq_zero, not_le, mem_Ioo]
  constructor
  · intro hpos
    have h_sqrt_pos : 0 < √(4 * (v : ℝ) - (x - μ) ^ 2) := by
      rcases mul_pos_iff.mp hpos with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact h2
      · exact absurd h2 (not_lt.mpr (Real.sqrt_nonneg _))
    have h_arg_pos : 0 < 4 * (v : ℝ) - (x - μ) ^ 2 := by
      by_contra h
      rw [Real.sqrt_eq_zero_of_nonpos (not_lt.mp h)] at h_sqrt_pos
      exact lt_irrefl _ h_sqrt_pos
    have h_lt : (x - μ) ^ 2 < (2 * √(v : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hv_nonneg]; linarith
    have h_abs : |x - μ| < 2 * √(v : ℝ) :=
      abs_lt_of_sq_lt_sq h_lt (by positivity)
    rw [abs_lt] at h_abs
    exact ⟨by linarith [h_abs.1], by linarith [h_abs.2]⟩
  · intro ⟨h1, h2⟩
    have h_abs : |x - μ| < 2 * √(v : ℝ) := by
      rw [abs_lt]; exact ⟨by linarith, by linarith⟩
    have h_sq_lt : (x - μ) ^ 2 < 4 * (v : ℝ) := by
      have := sq_lt_sq' (neg_lt_of_abs_lt h_abs) (lt_of_abs_lt h_abs)
      rw [mul_pow, Real.sq_sqrt hv_nonneg] at this; linarith
    have h_arg_pos : 0 < 4 * (v : ℝ) - (x - μ) ^ 2 := by linarith
    have hden : 0 < 1 / (2 * π * (v : ℝ)) := by
      have : 0 < (v : ℝ) := lt_of_le_of_ne hv_nonneg (Ne.symm (by exact_mod_cast hv))
      positivity
    rw [semicirclePDFReal]
    exact mul_pos hden (Real.sqrt_pos.mpr h_arg_pos)

/-- The real part of the `ℝ≥0∞`-valued semicircle density coincides with the real-valued density,
when the latter is nonnegative. -/
lemma semicirclePDF_toReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) (h₀ : 0 ≤ semicirclePDFReal μ v x) :
    (ENNReal.ofReal (semicirclePDFReal μ v x)).toReal = semicirclePDFReal μ v x :=
  ENNReal.toReal_ofReal h₀

/-- The canonical inclusion of `ℝ≥0` into `ℝ≥0∞` is measurable. -/
lemma measurable_ofNNReal : Measurable (ENNReal.ofNNReal) := by
  have h1 : Measurable fun (x : ℝ≥0) ↦ (x : ℝ) := measurable_subtype_coe
  have h2 : Measurable fun (x : ℝ) ↦ ENNReal.ofReal x := ENNReal.measurable_ofReal
  have h3 : Measurable fun (x : ℝ≥0) ↦ ENNReal.ofReal (x : ℝ) := h2.comp h1
  simpa [ENNReal.ofReal_coe_nnreal] using h3

/-- The integral of an even power of cosine over `[0, π]`, as a Wallis-type product. -/
lemma integral_cos_pow_even (n : ℕ) : (∫ x in (0)..π, Real.cos x ^ (2 * n))
    = π * ∏ k ∈ Finset.range n, ((2 * k + 1) : ℝ) / (2 * (k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have c1 : ∀ (m : ℕ),
        ∫ (x : ℝ) in (0)..π, Real.cos x ^ (m + 2) =
        (Real.cos π ^ (m + 1) * Real.sin π - Real.cos 0 ^ (m + 1) * Real.sin 0 +
        (m + 1) * ∫ (x : ℝ) in (0)..π, Real.cos x ^ m) -
        (m + 1) * ∫ (x : ℝ) in (0)..π, Real.cos x ^ (m + 2) :=
      fun m ↦ integral_cos_pow_aux (n := m) (a := 0) (b := π)
    simp only [Real.cos_pi, Real.sin_pi, Real.cos_zero, Real.sin_zero, mul_zero,
      sub_zero] at c1
    set A := ∫ (x : ℝ) in (0)..π, Real.cos x ^ (2 * n + 2)
    set B := ∫ (x : ℝ) in (0)..π, Real.cos x ^ (2 * n)
    have c2 : A = (2 * n + 1) * B - (2 * n + 1) * A := by
      have c21 := c1 (2 * n)
      simpa [A, B, Nat.cast_mul, Nat.cast_ofNat, two_mul, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using c21
    have c3 : ((2 * n + 2) : ℝ) * A = ((2 * n + 1) : ℝ) * B := by linarith
    have c5 : ∫ (x : ℝ) in (0)..π, Real.cos x ^ (2 * (n + 1))
        = (2 * n + 1) / (2 * n + 2) * ∫ (x : ℝ) in (0)..π, Real.cos x ^ (2 * n) := by
      have hAB : A = (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) * B := by
        rw [div_mul_eq_mul_div, eq_div_iff (by positivity : (2 * (n : ℝ) + 2) ≠ 0)]
        linarith [c3]
      simpa [A, B, show 2 * (n + 1) = 2 * n + 2 from by ring] using hAB
    rw [c5]
    change (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) * B = _
    rw [ih, Finset.prod_range_succ]
    ring

/-- The product `∏_{x < n} 2 * (x + 1)` equals `2 ^ n * n!`. -/
lemma prod_two_mul_factorial (n : ℕ) : ∏ x ∈ Finset.range n, (2 : ℝ) * (↑x + 1)
    = 2 ^ n * (↑n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- The Wallis product ratio equals the central binomial coefficient divided by `4 ^ n`. -/
lemma prod_odd_over_even_central_choose (n : ℕ) :
    (∏ x ∈ Finset.range n, (2 * (x : ℝ) + 1)) /
      (∏ x ∈ Finset.range n, (2 * ((x : ℝ) + 1))) =
      (Nat.choose (2 * n) n : ℝ) / 2 ^ (2 * n) := by
  set P_odd := ∏ x ∈ Finset.range n, (2 * (x : ℝ) + 1) with hP_odd
  set P_even := ∏ x ∈ Finset.range n, (2 * ((x : ℝ) + 1)) with hP_even
  have h_P_even : P_even = (2 : ℝ) ^ n * (Nat.factorial n : ℝ) := by
    rw [hP_even, prod_two_mul_factorial]
  have h_prod_all : P_odd * P_even = (Nat.factorial (2 * n) : ℝ) := by
    have h_nat_prod_id : ∀ k, ∏ i ∈ Finset.range k, ((2 * i + 1) * (2 * i + 2))
        = Nat.factorial (2 * k) := by
      intro k
      induction k with
      | zero => simp
      | succ k IH =>
        rw [Finset.prod_range_succ, IH]
        rw [show Nat.factorial (2 * (k + 1)) = Nat.factorial (2 * k + 2) by ring_nf]
        rw [Nat.factorial_succ, Nat.factorial_succ]
        ring
    rw [hP_odd, hP_even, ← Finset.prod_mul_distrib]
    conv_lhs => arg 2; ext x; rw [show (2 * (x : ℝ) + 1) * (2 * ((x : ℝ) + 1))
      = ((2 * x + 1) * (2 * x + 2) : ℝ) by ring]
    rw [show ∏ x ∈ Finset.range n, ((2 * x + 1) * (2 * x + 2) : ℝ)
      = (∏ x ∈ Finset.range n, (2 * x + 1) * (2 * x + 2) : ℕ) by push_cast; rfl]
    rw [h_nat_prod_id]
  have h_P_even_ne_zero : P_even ≠ 0 := by
    rw [h_P_even]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (by exact_mod_cast Nat.factorial_ne_zero n)
  calc
    P_odd / P_even
    _ = (↑(Nat.factorial (2 * n)) / P_even) / P_even := by
          rw [div_div, ← h_prod_all]; field_simp
    _ = ↑(Nat.factorial (2 * n)) / (P_even * P_even) := by rw [div_div]
    _ = ↑(Nat.factorial (2 * n))
        / (((2 : ℝ) ^ n * ↑(Nat.factorial n)) ^ 2) := by rw [h_P_even]; ring
    _ = ↑(Nat.factorial (2 * n))
        / (2 ^ (2 * n) * (↑(Nat.factorial n)) ^ 2) := by rw [mul_pow, ← pow_mul, mul_comm n 2]
    _ = (↑(Nat.choose (2 * n) n)) / 2 ^ (2 * n) := by
          rw [show (Nat.choose (2 * n) n : ℝ)
            = (2 * n).factorial / (n.factorial * n.factorial) by
            rw [Nat.cast_choose ℝ (by omega : n ≤ 2 * n), show 2 * n - n = n by omega]]
          ring

/-- The Catalan numbers satisfy the recurrence `(n + 2) * C_{n+1} = (4n + 2) * C_n`. -/
lemma catalan_recur (n : ℕ) : (n + 2) * catalan (n + 1) = (4 * n + 2) * (catalan n) := by
  -- Recurrence for the central binomial coefficients.
  have h_central : (n + 1) * Nat.centralBinom (n + 1) = (4 * n + 2) * Nat.centralBinom n := by
    have h := Nat.succ_mul_centralBinom_succ n
    rw [h]; ring
  -- `(n + 2) * catalan (n + 1)` telescopes back to the central binomial coefficient.
  have h_left : (n + 2) * catalan (n + 1) = Nat.centralBinom (n + 1) := by
    rw [catalan_eq_centralBinom_div]
    exact Nat.mul_div_cancel' (by simpa using Nat.succ_dvd_centralBinom (n + 1))
  -- `(4n + 2) * catalan n` does too, using the recurrence above.
  have h_right : (4 * n + 2) * catalan n = Nat.centralBinom (n + 1) := by
    rw [catalan_eq_centralBinom_div, ← Nat.mul_div_assoc _ (Nat.succ_dvd_centralBinom n)]
    refine Nat.div_eq_of_eq_mul_left (Nat.succ_pos n) ?_
    rw [← h_central]; ring
  rw [h_left, h_right]

/-- Reduction of `∫_{-2}^{2} x ^ (2n) √(4 - x ^ 2)` to a difference of even cosine-power
integrals over `[0, π]`. -/
lemma integral_even_pow_mul_sqrt_eq_cos_diff (n : ℕ) :
    ∫ (x : ℝ) in (-2)..2, x ^ (2 * n) * √(4 - x ^ 2) = 2 ^ (2 * n + 2) *
      ((∫ (x : ℝ) in (0)..π, Real.cos x ^ (2 * n))
        - ∫ (x : ℝ) in (0)..π, Real.cos x ^ (2 * n + 2)) := by
  have c50 : ∫ (x : ℝ) in (-2)..2, x ^ (2 * n) * √(4 - x ^ 2)
      = 2 ^ (2 * n + 2) * ∫ (u : ℝ) in (-1)..1, u ^ (2 * n) * √(1 - u ^ 2) := by
    have c5000A : (2 : ℝ) ≠ 0 := by norm_num
    have c5000 := intervalIntegral.integral_comp_mul_left
      (f := fun (x : ℝ) ↦ x ^ (2 * n) * √(4 - x ^ 2)) (c := (2 : ℝ)) (a := -1) (b := 1) c5000A
    simp only [smul_eq_mul, show (2 : ℝ) * (-1) = -2 by norm_num,
      show (2 : ℝ) * 1 = 2 by norm_num] at c5000
    have c5001 : ∫ (x : ℝ) in (-1)..1, (2 * x) ^ (2 * n) * √(4 - (2 * x) ^ 2)
        = ∫ (x : ℝ) in (-1)..1, 2 ^ (2 * n + 1) * x ^ (2 * n) * √(1 - x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      have c500100 : (2 * x) ^ (2 * n) = 2 ^ (2 * n) * x ^ (2 * n) := mul_pow 2 x (2 * n)
      have c500101 : √(4 - (2 * x) ^ 2) = 2 * √(1 - x ^ 2) := by
        rw [show 4 - (2 * x) ^ 2 = 2 ^ 2 * (1 - x ^ 2) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      rw [c500100, c500101]; ring
    have c5002 : ∫ (x : ℝ) in (-1)..1, 2 ^ (2 * n + 1) * x ^ (2 * n) * √(1 - x ^ 2)
        = 2 ^ (2 * n + 1) * ∫ (x : ℝ) in (-1)..1, x ^ (2 * n) * √(1 - x ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _; dsimp only; ring
    have c5003 : ∫ (x : ℝ) in (-2)..2, x ^ (2 * n) * √(4 - x ^ 2)
        = 2 * ∫ (x : ℝ) in (-1)..1, (2 * x) ^ (2 * n) * √(4 - (2 * x) ^ 2) := by
      rw [c5000]; ring
    rw [c5003, c5001, c5002]; ring
  rw [c50]
  have c51 : ∫ (x : ℝ) in (-1)..1, x ^ (2 * n) * √(1 - x ^ 2)
      = (∫ (x : ℝ) in (0)..π, Real.cos x ^ (2 * n))
        - ∫ (x : ℝ) in (0)..π, Real.cos x ^ (2 * n + 2) := by
    have c510 : ∫ (x : ℝ) in (-1)..1, x ^ (2 * n) * √(1 - x ^ 2)
        = ∫ (x : ℝ) in (0)..π, (Real.sin x) ^ 2 * (Real.cos x) ^ (2 * n) := by
      set g := fun (x : ℝ) ↦ x ^ (2 * n) * √(1 - x ^ 2)
      set f := fun (x : ℝ) ↦ Real.cos x
      have c5100A : ∀ x ∈ uIcc 0 π, HasDerivAt f ((deriv f) x) x := by
        intro x _
        have c5100A0 : (deriv f) x = -Real.sin x := Real.deriv_cos
        rw [c5100A0]; exact Real.hasDerivAt_cos x
      have c5100B : ContinuousOn (deriv f) (uIcc 0 π) := by
        have c5100B0 : (deriv f) = fun (x : ℝ) ↦ -Real.sin x := funext fun x ↦ Real.deriv_cos
        rw [c5100B0]; fun_prop
      have c5100C : Continuous g := by unfold g; fun_prop
      have c5100 : ∫ (x : ℝ) in (0)..π, (g ∘ f) x * (deriv f) x = ∫ (x : ℝ) in f 0..f π, g x :=
        intervalIntegral.integral_comp_mul_deriv c5100A c5100B c5100C
      simp only [f, g, Function.comp, Real.deriv_cos, Real.cos_zero, Real.cos_pi] at c5100
      -- `c5100 : ∫_0^π cos^(2n)·√(1-cos²)·(-sin) = ∫_1^{-1} x^(2n)√(1-x²)`.
      rw [intervalIntegral.integral_symm (-1) 1] at c5100
      -- The integrand on `[0, π]` simplifies to `sin²·cos^(2n)` up to sign.
      have c5101A : ∫ (x : ℝ) in (0)..π,
          Real.cos x ^ (2 * n) * √(1 - Real.cos x ^ 2) * -Real.sin x
          = -∫ (x : ℝ) in (0)..π, Real.sin x ^ 2 * Real.cos x ^ (2 * n) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro x hx
        have c51010 : √(1 - Real.cos x ^ 2) = |Real.sin x| :=
          (Real.abs_sin_eq_sqrt_one_sub_cos_sq x).symm
        have hsin : Real.sin x ≥ 0 := by
          refine Real.sin_nonneg_of_mem_Icc ?_
          rwa [← uIcc_of_le Real.pi_nonneg]
        simp only
        rw [c51010, abs_of_nonneg hsin]; ring
      rw [c5101A] at c5100
      simp only [g]
      linarith [c5100]
    have c511 : ∫ (x : ℝ) in (0)..π, (Real.sin x) ^ 2 * (Real.cos x) ^ (2 * n)
        = ∫ (x : ℝ) in (0)..π, (1 - (Real.cos x) ^ 2) * (Real.cos x) ^ (2 * n) := by
      apply intervalIntegral.integral_congr
      intro x _; simp only; rw [Real.sin_sq]
    have c512 : ∫ (x : ℝ) in (0)..π, (1 - (Real.cos x) ^ 2) * (Real.cos x) ^ (2 * n)
        = (∫ (x : ℝ) in (0)..π, Real.cos x ^ (2 * n))
          - ∫ (x : ℝ) in (0)..π, Real.cos x ^ (2 * n + 2) := by
      rw [show (fun (x : ℝ) ↦ (1 - Real.cos x ^ 2) * Real.cos x ^ (2 * n))
        = fun (x : ℝ) ↦ Real.cos x ^ (2 * n) - Real.cos x ^ (2 * n + 2) from
        funext fun x ↦ by rw [pow_add]; ring]
      rw [intervalIntegral.integral_sub
        ((Real.continuous_cos.pow (2 * n)).intervalIntegrable _ _)
        ((Real.continuous_cos.pow (2 * n + 2)).intervalIntegrable _ _)]
    rw [c510, c511, c512]
  rw [c51]

/-- The mean of a real semicircle distribution `semicircleReal μ v` is its mean parameter `μ`. -/
@[simp]
lemma integral_id_semicircleReal : ∫ x, x ∂semicircleReal μ v = μ := by
  by_cases hv : v = 0
  · simp [hv]
  rw [integral_semicircleReal_eq_integral_smul hv]
  have h_integrable : Integrable (fun x => semicirclePDFReal μ v x * (x - μ)) := by
    have h_cont : Continuous (fun x => semicirclePDFReal μ v x * (x - μ)) :=
      (continuous_semicirclePDFReal μ v).mul (continuous_id.sub continuous_const)
    have h_compact : IsCompact (Icc (μ - 2 * √(v : ℝ)) (μ + 2 * √(v : ℝ))) := isCompact_Icc
    have h_int_on : IntegrableOn (fun x => semicirclePDFReal μ v x * (x - μ))
        (Icc (μ - 2 * √(v : ℝ)) (μ + 2 * √(v : ℝ))) :=
      h_cont.continuousOn.integrableOn_compact h_compact
    refine (integrableOn_iff_integrable_of_support_subset ?_).mp h_int_on
    intro x hx
    by_contra hxI
    exact hx (mul_eq_zero_of_left (semicirclePDFReal_eq_zero_of_notMem μ v hxI) _)
  have h_split : (fun x => semicirclePDFReal μ v x • x) =
      (fun x => semicirclePDFReal μ v x * (x - μ) + semicirclePDFReal μ v x * μ) := by
    ext x; simp only [smul_eq_mul]; ring
  rw [h_split, integral_add h_integrable ((integrable_semicirclePDFReal μ v).mul_const μ)]
  have h_symm : ∫ a, semicirclePDFReal μ v a * (a - μ) = 0 := by
    rw [semicirclePDFReal_def]
    have h_shift : ∫ a, 1 / (2 * π * (v : ℝ)) * √(4 * (v : ℝ) - (a - μ) ^ 2) * (a - μ) =
        ∫ y, 1 / (2 * π * (v : ℝ)) * √(4 * (v : ℝ) - y ^ 2) * y := by
      rw [eq_comm, ← integral_sub_right_eq_self _ μ]
    rw [h_shift]
    have h_odd : ∫ y, 1 / (2 * π * (v : ℝ)) * √(4 * (v : ℝ) - y ^ 2) * y =
        ∫ y, -(1 / (2 * π * (v : ℝ)) * √(4 * (v : ℝ) - y ^ 2) * y) := by
      conv_lhs => rw [← integral_neg_eq_self
        (fun y => 1 / (2 * π * (v : ℝ)) * √(4 * (v : ℝ) - y ^ 2) * y)]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [neg_sq]; ring
    rw [integral_neg] at h_odd
    linarith
  rw [h_symm, zero_add]
  simp_rw [show (fun a => semicirclePDFReal μ v a * μ) = (fun a => μ * semicirclePDFReal μ v a)
    from funext fun a => mul_comm _ _]
  rw [integral_const_mul, integral_semicirclePDFReal_eq_one μ hv, mul_one]

/-- The substitution `x ↦ x * √v` rescales the centered semicircle moment integral to the
standard interval `[-2, 2]`. -/
lemma integral_scaled_semicircle_eq (v : ℝ≥0) (n : ℕ) (hv : v ≠ 0) :
    1 / (2 * π * (v : ℝ)) * ∫ (x : ℝ) in (-2 * √v)..(2 * √v), x ^ (2 * n) * √(4 * v - x ^ 2)
      = (v : ℝ) ^ n / (2 * π) * ∫ (x : ℝ) in (-2)..2, x ^ (2 * n) * √(4 - x ^ 2) := by
  have hv_pos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hv_nonneg : 0 ≤ (v : ℝ) := hv_pos.le
  have hsqrt_pos : 0 < √(v : ℝ) := Real.sqrt_pos.mpr hv_pos
  -- Change of variables `x = √v * t` on `[-2, 2]`.
  have hcomp := intervalIntegral.smul_integral_comp_mul_left
    (a := -2) (b := 2) (c := √(v : ℝ))
    (f := fun x ↦ x ^ (2 * n) * √(4 * (v : ℝ) - x ^ 2))
  rw [show √(v : ℝ) * (-2) = -2 * √(v : ℝ) by ring,
    show √(v : ℝ) * 2 = 2 * √(v : ℝ) by ring] at hcomp
  -- Rewrite the right-hand interval integral via the substitution.
  rw [show ∫ (x : ℝ) in (-2 * √(v : ℝ))..(2 * √v), x ^ (2 * n) * √(4 * v - x ^ 2)
    = √(v : ℝ) • ∫ (x : ℝ) in (-2)..2,
        (√(v : ℝ) * x) ^ (2 * n) * √(4 * (v : ℝ) - (√(v : ℝ) * x) ^ 2) from hcomp.symm]
  -- Simplify the substituted integrand.
  have h_integrand : ∀ x : ℝ, (√(v : ℝ) * x) ^ (2 * n) * √(4 * (v : ℝ) - (√(v : ℝ) * x) ^ 2)
      = ((v : ℝ) ^ n * √(v : ℝ)) * (x ^ (2 * n) * √(4 - x ^ 2)) := by
    intro x
    have hpow : (√(v : ℝ) * x) ^ (2 * n) = (v : ℝ) ^ n * x ^ (2 * n) := by
      rw [mul_pow, pow_mul, Real.sq_sqrt hv_nonneg]
    have hsqrt : √(4 * (v : ℝ) - (√(v : ℝ) * x) ^ 2) = √(v : ℝ) * √(4 - x ^ 2) := by
      rw [show (√(v : ℝ) * x) ^ 2 = (v : ℝ) * x ^ 2 by rw [mul_pow, Real.sq_sqrt hv_nonneg],
        show 4 * (v : ℝ) - (v : ℝ) * x ^ 2 = (v : ℝ) * (4 - x ^ 2) by ring,
        Real.sqrt_mul hv_nonneg]
    rw [hpow, hsqrt]; ring
  simp_rw [h_integrand]
  rw [intervalIntegral.integral_const_mul, smul_eq_mul]
  have hv_ne : (v : ℝ) ≠ 0 := ne_of_gt hv_pos
  field_simp
  rw [Real.sq_sqrt hv_nonneg]

/-- The Wallis product telescopes: `2 ^ (2n+1)` times the difference of consecutive Wallis
partial products equals the `n`-th Catalan number. -/
lemma wallis_prod_diff_eq_catalan (n : ℕ) :
    2 ^ (2 * n + 1) * ((∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * (i + 1)))
        - ∏ i ∈ Finset.range (n + 1), (2 * (i : ℝ) + 1) / (2 * (i + 1)))
      = catalan n := by
  have hprod : (∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * (i + 1)))
      = (Nat.choose (2 * n) n : ℝ) / 2 ^ (2 * n) := by
    rw [← prod_odd_over_even_central_choose n, Finset.prod_div_distrib]
  have hsucc : (∏ i ∈ Finset.range (n + 1), (2 * (i : ℝ) + 1) / (2 * (i + 1)))
      = (∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * (i + 1)))
        * ((2 * (n : ℝ) + 1) / (2 * (n + 1))) := Finset.prod_range_succ _ n
  have hne : (2 * ((n : ℝ) + 1)) ≠ 0 := by positivity
  have hdiff : (∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * (i + 1)))
      - ∏ i ∈ Finset.range (n + 1), (2 * (i : ℝ) + 1) / (2 * (i + 1))
      = (Nat.choose (2 * n) n : ℝ) / 2 ^ (2 * n) * (1 / (2 * (n + 1))) := by
    rw [hsucc, hprod]; field_simp; ring
  rw [hdiff]
  -- `catalan n = C(2n,n) / (n+1)` over `ℝ`.
  have hcat : (catalan n : ℝ) = (Nat.choose (2 * n) n : ℝ) / (n + 1) := by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose,
      Nat.cast_div (by simpa [Nat.centralBinom] using Nat.succ_dvd_centralBinom n)
        (by exact_mod_cast Nat.succ_ne_zero n)]
    push_cast; ring
  rw [hcat]
  have h2 : (2 : ℝ) ^ (2 * n) ≠ 0 := by positivity
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

/-- The centered `2 * n`-th power integral against the semicircle measure, rewritten as a
weighted integral of the unnormalized kernel over its centered support interval. -/
lemma integral_centered_pow_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) (hv : v ≠ 0) :
    ∫ (x : ℝ), (x - μ) ^ (2 * n) ∂semicircleReal μ v
      = 1 / (2 * π * (v : ℝ))
        * ∫ (x : ℝ) in (-2 * √v)..(2 * √v), x ^ (2 * n) * √(4 * v - x ^ 2) := by
  rw [integral_semicircleReal_eq_integral_smul hv]
  -- The integrand vanishes outside the support interval, so restrict to it.
  have h_support : Function.support
      (fun x ↦ semicirclePDFReal μ v x • (x - μ) ^ (2 * n)) ⊆ Icc (μ - 2 * √v) (μ + 2 * √v) := by
    intro x hx
    by_contra hxI
    apply hx
    simp only [semicirclePDFReal_eq_zero_of_notMem μ v hxI, smul_eq_mul, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ by
      by_contra hne
      exact hx (h_support hne))]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.sqrt_nonneg (v : ℝ)])]
  -- Center the variable: substitute `x ↦ x + μ`.
  have h_center := intervalIntegral.integral_comp_add_right
    (a := -2 * √(v : ℝ)) (b := 2 * √(v : ℝ)) (d := μ)
    (f := fun x ↦ semicirclePDFReal μ v x • (x - μ) ^ (2 * n))
  rw [show μ - 2 * √(v : ℝ) = -2 * √(v : ℝ) + μ by ring,
    show μ + 2 * √(v : ℝ) = 2 * √(v : ℝ) + μ by ring, ← h_center]
  -- Unfold the kernel and pull out the constant.
  simp only [smul_eq_mul, semicirclePDFReal, add_sub_cancel_right]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  ring

/-- The `2 * n`-th central moment of the semicircle distribution equals `v ^ n` times the `n`-th
Catalan number. -/
lemma centralMoment_fun_two_mul_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    ProbabilityTheory.centralMoment (fun x ↦ x) (2 * n) (semicircleReal μ v)
      = v ^ n * catalan n := by
  rw [ProbabilityTheory.centralMoment]
  simp only [Pi.pow_apply, Pi.sub_apply, integral_id_semicircleReal]
  -- Split off the degenerate `v = 0` case.
  by_cases h1 : v = 0
  · subst h1; rw [semicircleReal_zero_var]; simp; cases n <;> simp [catalan_zero]
  have c0 := integral_centered_pow_semicircleReal μ v n h1
  rw [c0]
  /- Change of variable 2 (trigonometric substitution)-/
  have c2 := integral_scaled_semicircle_eq v n h1
  rw [c2]
  have c3 := integral_cos_pow_even n
  have c4 := integral_cos_pow_even (n + 1)
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring] at c4
  have c5 := integral_even_pow_mul_sqrt_eq_cos_diff n
  rw [c5, c3, c4]
  -- Reduce to the telescoping Wallis identity.
  rw [show (v : ℝ) ^ n / (2 * π) * (2 ^ (2 * n + 2)
      * (π * ∏ k ∈ Finset.range n, (2 * (k : ℝ) + 1) / (2 * (k + 1))
        - π * ∏ k ∈ Finset.range (n + 1), (2 * (k : ℝ) + 1) / (2 * (k + 1))))
    = (v : ℝ) ^ n * (2 ^ (2 * n + 1)
      * ((∏ k ∈ Finset.range n, (2 * (k : ℝ) + 1) / (2 * (k + 1)))
        - ∏ k ∈ Finset.range (n + 1), (2 * (k : ℝ) + 1) / (2 * (k + 1)))) by
    rw [pow_succ]; field_simp]
  rw [wallis_prod_diff_eq_catalan n]

/-- The `2 * n`-th central moment of the identity equals `v ^ n` times the `n`-th Catalan number. -/
lemma centralMoment_two_mul_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    ProbabilityTheory.centralMoment id (2 * n) (semicircleReal μ v) = v ^ n * catalan n := by
  apply centralMoment_fun_two_mul_semicircleReal

variable {μ : ℝ} {v : ℝ≥0}

/-- The variance of a real semicircle distribution `semicircleReal μ v` is its variance
parameter `v`. -/
@[simp]
lemma variance_id_semicircleReal : Var[id; semicircleReal μ v] = v := by
  rw [← ProbabilityTheory.centralMoment_two_eq_variance measurable_id.aemeasurable]
  have := centralMoment_two_mul_semicircleReal μ v 1
  simpa [catalan_one] using this

/-- The variance of a real semicircle distribution `semicircleReal μ v` is its variance
parameter `v`. -/
@[simp]
lemma variance_fun_id_semicircleReal : Var[fun x ↦ x; semicircleReal μ v] = v :=
  variance_id_semicircleReal

/-- The odd central moments of the semicircle distribution vanish. -/
lemma centralMoment_fun_odd_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    ProbabilityTheory.centralMoment (fun x ↦ x) ((2 * n) + 1) (semicircleReal μ v) = 0 := by
  rw [ProbabilityTheory.centralMoment]
  simp only [Pi.pow_apply, Pi.sub_apply, integral_id_semicircleReal]
  by_cases hv : v = 0
  · subst hv; rw [semicircleReal_zero_var]; simp
  rw [integral_semicircleReal_eq_integral_smul hv]
  -- Center the variable: `∫ (semicirclePDF·(x-μ)^(2n+1)) = ∫ u^(2n+1)·semicirclePDF(u+μ)`.
  have h_subst : ∫ x, semicirclePDFReal μ v x • (x - μ) ^ (2 * n + 1)
      = ∫ u, u ^ (2 * n + 1) * semicirclePDFReal μ v (u + μ) := by
    rw [← integral_add_right_eq_self _ μ]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [smul_eq_mul, add_sub_cancel_right]; ring
  rw [h_subst]
  -- The integrand is odd: replacing `u` by `-u` negates it, so the integral is zero.
  have h_odd : ∫ u, u ^ (2 * n + 1) * semicirclePDFReal μ v (u + μ)
      = ∫ u, -(u ^ (2 * n + 1) * semicirclePDFReal μ v (u + μ)) := by
    conv_lhs => rw [← integral_neg_eq_self
      (fun u ↦ u ^ (2 * n + 1) * semicirclePDFReal μ v (u + μ))]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [semicirclePDFReal, semicirclePDFReal,
      show -u + μ - μ = -(u - (μ - μ)) by ring, show u + μ - μ = u - (μ - μ) by ring,
      neg_sq, Odd.neg_pow ⟨n, by ring⟩]
    ring
  rw [integral_neg] at h_odd
  linarith

/-- The odd central moments of the identity vanish. -/
lemma centralMoment_odd_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    ProbabilityTheory.centralMoment id ((2 * n) + 1) (semicircleReal μ v) = 0 := by
  apply centralMoment_fun_odd_semicircleReal

end LeanPool.SemicircleLaw
