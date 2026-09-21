/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundDyadicStopping
import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertFiniteTruncationWeakOneOne
import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertL2Fourier
import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryReductionMaximal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Order.IsLUB

/-!
# The ordinary maximally truncated Hilbert transform

This module begins the uniform `λ = 0` branch by proving the measurable
countable reduction of the genuine supremum over all positive truncation
radii. The reduction uses continuity in the truncation radius, proved
directly from one-sided tail integrals.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace QuadraticCarleson
namespace HilbertMaximalWeakOneOne

open HilbertFiniteTruncationWeakOneOne
open HilbertL2Fourier
open CalderonZygmundDyadicStopping


noncomputable
section

/-- The unmodulated Hilbert-transform integrand `f (x - t) / t`. -/
def zeroHilbertIntegrand (f : ℝ → ℂ) (x t : ℝ) : ℂ :=
  f (x - t) / (t : ℂ)

theorem zeroHilbertTruncation_eq_oneSidedTails {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    quadraticHilbertTrunc 0 ε f x =
      (∫ t in Iio (-ε), zeroHilbertIntegrand f x t) +
        ∫ t in Ioi ε, zeroHilbertIntegrand f x t := by
  have hset : {t : ℝ | ε < |t|} = Iio (-ε) ∪ Ioi ε := by
    ext t
    simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]
    rw [lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hwhole : IntegrableOn (zeroHilbertIntegrand f x) {t : ℝ | ε < |t|} := by
    exact integrableOn_zeroHilbertTail hε hf x
  have hleft : IntegrableOn (zeroHilbertIntegrand f x) (Iio (-ε)) := by
    apply hwhole.mono_set
    intro t ht
    change t < -ε at ht
    change ε < |t|
    have htneg : t < 0 := ht.trans (neg_neg_of_pos hε)
    rw [abs_of_neg htneg]
    linarith
  have hright : IntegrableOn (zeroHilbertIntegrand f x) (Ioi ε) := by
    apply hwhole.mono_set
    intro t ht
    change ε < |t|
    rw [abs_of_pos (hε.trans ht)]
    exact ht
  have hdis : Disjoint (Iio (-ε)) (Ioi ε) := by
    apply Set.disjoint_left.2
    intro t htl htr
    change t < -ε at htl
    change ε < t at htr
    linarith
  unfold quadraticHilbertTrunc zeroHilbertIntegrand
  simp only [zero_mul, phase_zero, mul_one]
  rw [hset]
  simpa only [zeroHilbertIntegrand] using
    setIntegral_union hdis measurableSet_Ioi hleft hright

theorem continuousAt_zeroHilbertTruncation_radius {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    ContinuousAt (fun δ : ℝ ↦ quadraticHilbertTrunc 0 δ f x) ε := by
  let a : ℝ := ε / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hwhole : IntegrableOn (zeroHilbertIntegrand f x) {t : ℝ | a < |t|} := by
    exact integrableOn_zeroHilbertTail ha hf x
  have hright : IntegrableOn (zeroHilbertIntegrand f x) (Ioi a) := by
    apply hwhole.mono_set
    intro t ht
    change a < t at ht
    change a < |t|
    rw [abs_of_pos (ha.trans ht)]
    exact ht
  have hleft : IntegrableOn (zeroHilbertIntegrand f x) (Iio (-a)) := by
    apply hwhole.mono_set
    intro t ht
    change t < -a at ht
    change a < |t|
    have htneg : t < 0 := ht.trans (neg_neg_of_pos ha)
    rw [abs_of_neg htneg]
    linarith
  have hεa : a < ε := by dsimp [a]; linarith
  have hrightAt : ContinuousAt
      (fun δ : ℝ ↦ ∫ t in Ioi δ, zeroHilbertIntegrand f x t) ε := by
    apply (hright.continuousOn_Ici_primitive_Ioi ε hεa.le).continuousAt
    exact Ici_mem_nhds hεa
  have hleftAtBound : ContinuousAt
      (fun b : ℝ ↦ ∫ t in Iio b, zeroHilbertIntegrand f x t) (-ε) := by
    apply (hleft.continuousOn_Iic_primitive_Iio (-ε)
      (by linarith : -ε ≤ -a)).continuousAt
    exact Iic_mem_nhds (by linarith : -ε < -a)
  have hleftAt : ContinuousAt
      (fun δ : ℝ ↦ ∫ t in Iio (-δ), zeroHilbertIntegrand f x t) ε :=
    hleftAtBound.comp continuousAt_neg
  have hsum : ContinuousAt
      (fun δ : ℝ ↦
        (∫ t in Iio (-δ), zeroHilbertIntegrand f x t) +
          ∫ t in Ioi δ, zeroHilbertIntegrand f x t) ε :=
    hleftAt.add hrightAt
  apply ContinuousAt.congr_of_eventuallyEq hsum
  filter_upwards [Ioi_mem_nhds hε] with δ hδ
  exact zeroHilbertTruncation_eq_oneSidedTails hδ hf x

theorem continuous_zeroHilbertTruncation_positiveRadii
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Continuous (fun ε : {ε : ℝ // 0 < ε} ↦
      quadraticHilbertTrunc 0 ε.1 f x) := by
  rw [continuous_iff_continuousAt]
  intro ε
  exact (continuousAt_zeroHilbertTruncation_radius ε.2 hf x).comp
    continuousAt_subtype_val

theorem continuous_enorm_zeroHilbertTruncation_positiveRadii
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Continuous (fun ε : {ε : ℝ // 0 < ε} ↦
      ‖quadraticHilbertTrunc 0 ε.1 f x‖ₑ) :=
  (continuous_zeroHilbertTruncation_positiveRadii hf x).enorm

/-- A fixed countable dense set of positive truncation radii. -/
def densePositiveRadii : Set {ε : ℝ // 0 < ε} :=
  (TopologicalSpace.exists_countable_dense {ε : ℝ // 0 < ε}).choose

theorem countable_densePositiveRadii : densePositiveRadii.Countable :=
  (TopologicalSpace.exists_countable_dense {ε : ℝ // 0 < ε}).choose_spec.1

theorem dense_densePositiveRadii : Dense densePositiveRadii :=
  (TopologicalSpace.exists_countable_dense {ε : ℝ // 0 < ε}).choose_spec.2

/-- A countably indexed representative of the ordinary maximal truncation. -/
def countableZeroHilbertMaximalTruncation (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ ε : densePositiveRadii, ‖quadraticHilbertTrunc 0 ε.1.1 f x‖ₑ

theorem countableZeroHilbertMaximalTruncation_eq
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    countableZeroHilbertMaximalTruncation f x =
      quadraticHilbertMaximalTruncation 0 f x := by
  unfold countableZeroHilbertMaximalTruncation quadraticHilbertMaximalTruncation
  exact dense_densePositiveRadii.ciSup'
    (continuous_enorm_zeroHilbertTruncation_positiveRadii hf x)

theorem measurable_countableZeroHilbertMaximalTruncation
    (f : L0Infinity) : Measurable (countableZeroHilbertMaximalTruncation f) := by
  let _ := countable_densePositiveRadii.toEncodable
  apply Measurable.iSup
  intro ε
  exact (measurable_quadraticHilbertTrunc_l0 0 ε.1.1 f).enorm

/-- Measurability of the genuine supremum over all positive real radii. -/
theorem measurable_zeroHilbertMaximalTruncation (f : L0Infinity) :
    Measurable (quadraticHilbertMaximalTruncation 0 f) := by
  rw [← funext (countableZeroHilbertMaximalTruncation_eq f.integrable)]
  exact measurable_countableZeroHilbertMaximalTruncation f

/-! ## Ordinary Hilbert-kernel cancellation off an interval -/

/-- The ordinary Hilbert kernel in input-variable coordinates. -/
def ordinaryHilbertKernel (x y : ℝ) : ℂ :=
  1 / ((x - y : ℝ) : ℂ)

theorem measurable_ordinaryHilbertKernel :
    Measurable (Function.uncurry ordinaryHilbertKernel) := by
  exact measurable_const.div
    (Complex.measurable_ofReal.comp (measurable_fst.sub measurable_snd))

/-- The ordinary kernel has the Lipschitz regularity required by the existing
one-dimensional bad-atom estimate, with the explicit constant two. -/
theorem ordinaryHilbertKernel_sub_center_norm_le {x z R y : ℝ}
    (hR : 0 < R) (hx : x ∉ tripleCenteredInterval z R)
    (hy : y ∈ centeredInterval z R) :
    ‖ordinaryHilbertKernel x y - ordinaryHilbertKernel x z‖ ≤
      2 * |y - z| / |x - y| ^ 2 := by
  have hyz : |y - z| ≤ R / 2 :=
    abs_sub_center_le_of_mem_centeredInterval hy
  have hxz : 3 * R / 2 < |x - z| :=
    not_mem_tripleCenteredInterval_abs hx
  have hxyLower : |x - z| / 2 ≤ |x - y| :=
    half_center_distance_le_distance hR.le hx hy
  have hxzpos : 0 < |x - z| := by linarith
  have hxypos : 0 < |x - y| := (half_pos hxzpos).trans_le hxyLower
  have hxyUpper : |x - y| ≤ 2 * |x - z| := by
    have htri : |x - y| ≤ |x - z| + |z - y| := by
      calc
        |x - y| = |(x - z) + (z - y)| := by ring_nf
        _ ≤ |x - z| + |z - y| := abs_add_le _ _
    rw [abs_sub_comm z y] at htri
    linarith
  have hxy0 : (x - y : ℂ) ≠ 0 :=
    by simpa using Complex.ofReal_ne_zero.mpr (abs_pos.mp hxypos)
  have hxz0 : (x - z : ℂ) ≠ 0 :=
    by simpa using Complex.ofReal_ne_zero.mpr (abs_pos.mp hxzpos)
  have hid : ordinaryHilbertKernel x y - ordinaryHilbertKernel x z =
      ((y - z : ℝ) : ℂ) / (((x - y : ℝ) : ℂ) * ((x - z : ℝ) : ℂ)) := by
    unfold ordinaryHilbertKernel
    field_simp [hxy0, hxz0]
    push_cast
    ring
  rw [hid, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  apply (div_le_div_iff₀ (mul_pos hxypos hxzpos) (sq_pos_of_pos hxypos)).2
  calc
    |y - z| * |x - y| ^ 2 =
        (|y - z| * |x - y|) * |x - y| := by ring
    _ ≤ (|y - z| * |x - y|) * (2 * |x - z|) := by
      gcongr
    _ ≤ 2 * |y - z| * (|x - y| * |x - z|) := by
      exact le_of_eq (by ring)

/-- Outside the triple interval the ordinary Hilbert kernel times an
integrable interval atom is integrable. -/
theorem integrableOn_ordinaryHilbertKernel_mul_atom
    {b : ℝ → ℂ} {z R x : ℝ} (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R)
    (hb : IntegrableOn b (centeredInterval z R)) :
    IntegrableOn (fun y ↦ ordinaryHilbertKernel x y * b y)
      (centeredInterval z R) := by
  have hxz : 0 < |x - z| := by
    have := not_mem_tripleCenteredInterval_abs hx
    linarith
  have hmeas : AEStronglyMeasurable (ordinaryHilbertKernel x)
      (volume.restrict (centeredInterval z R)) :=
    (measurable_const.div
      (Complex.measurable_ofReal.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂volume.restrict (centeredInterval z R),
      ‖ordinaryHilbertKernel x y‖ ≤ 2 / |x - z| := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    have hdist := half_center_distance_le_distance hR.le hx hy
    have hxy : 0 < |x - y| := (half_pos hxz).trans_le hdist
    unfold ordinaryHilbertKernel
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs]
    calc
      1 / |x - y| ≤ 1 / (|x - z| / 2) :=
        one_div_le_one_div_of_le (half_pos hxz) hdist
      _ = 2 / |x - z| := by field_simp
  exact hb.bdd_mul hmeas hbound

/-- Integrated cancellation estimate for the ordinary Hilbert kernel acting
on a mean-zero atom supported on a finite interval. -/
theorem integral_norm_ordinaryHilbertKernel_atom_le
    (b : ℝ → ℂ) (z R : ℝ) (hR : 0 < R)
    (hb : IntegrableOn b (centeredInterval z R))
    (hbmeas : AEStronglyMeasurable b volume)
    (hmean : ∫ y in centeredInterval z R, b y = 0) :
    ∫ x in (tripleCenteredInterval z R)ᶜ,
        ‖∫ y in centeredInterval z R, ordinaryHilbertKernel x y * b y‖ ≤
      (8 * 2 / 3 : ℝ) * ∫ y in centeredInterval z R, ‖b y‖ := by
  apply integral_norm_setIntegral_kernel_le ordinaryHilbertKernel b z R 2
    hR (by norm_num) hb hmean
  · intro x hx
    exact integrableOn_ordinaryHilbertKernel_mul_atom hR hx hb
  · intro x hx y hy
    exact ordinaryHilbertKernel_sub_center_norm_le hR hx hy
  · have hbI : AEStronglyMeasurable
        ((centeredInterval z R).indicator b) volume :=
      hbmeas.indicator measurableSet_Ico
    have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ ↦ ordinaryHilbertKernel p.1 p.2 *
          (centeredInterval z R).indicator b p.2)
        (volume.prod volume) :=
      measurable_ordinaryHilbertKernel.aestronglyMeasurable.mul
        (hbI.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    have hout := hjoint.integral_prod_right'
    have heq : (fun x ↦ ∫ y, ordinaryHilbertKernel x y *
          (centeredInterval z R).indicator b y) =
        (fun x ↦ ∫ y in centeredInterval z R,
          ordinaryHilbertKernel x y * b y) := by
      funext x
      calc
        (∫ y, ordinaryHilbertKernel x y *
            (centeredInterval z R).indicator b y) =
            ∫ y, (centeredInterval z R).indicator
              (fun u ↦ ordinaryHilbertKernel x u * b u) y := by
          apply integral_congr_ae
          filter_upwards with y
          by_cases hy : y ∈ centeredInterval z R <;> simp [hy]
        _ = ∫ y in centeredInterval z R,
            ordinaryHilbertKernel x y * b y :=
          integral_indicator measurableSet_Ico
    rw [← heq]
    exact hout.restrict

/-- If the sharp truncation radius does not reach an interval, then on an
atom supported in that interval the truncation is exactly the full ordinary
Hilbert-kernel action. This identifies the range already controlled by
cancellation; only radii meeting the interval create boundary pieces. -/
theorem zeroHilbertTruncation_eq_ordinaryKernel_atom_of_radius_lt
    {b : ℝ → ℂ} {z R x ε : ℝ}
    (hsupp : ∀ y ∉ centeredInterval z R, b y = 0)
    (hε : ε < |x - z| - R / 2) :
    quadraticHilbertTrunc 0 ε b x =
      ∫ y in centeredInterval z R, ordinaryHilbertKernel x y * b y := by
  rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc]
  unfold quadraticHilbertConvolutionTrunc
  calc
    (∫ y, sharpQuadraticTailKernel 0 ε (x - y) * b y) =
        ∫ y in centeredInterval z R,
          sharpQuadraticTailKernel 0 ε (x - y) * b y := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [hsupp y hy, mul_zero]
    _ = ∫ y in centeredInterval z R,
        ordinaryHilbertKernel x y * b y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
      have hyz : |y - z| ≤ R / 2 :=
        abs_sub_center_le_of_mem_centeredInterval hy
      have hdist : |x - z| - R / 2 ≤ |x - y| := by
        have htri : |x - z| ≤ |x - y| + |y - z| := by
          calc
            |x - z| = |(x - y) + (y - z)| := by ring_nf
            _ ≤ |x - y| + |y - z| := abs_add_le _ _
        linarith
      have hcut : ε < |x - y| := hε.trans_le hdist
      rw [sharpQuadraticTailKernel, ite_eq_left hcut, zero_mul, phase_zero]
      unfold ordinaryHilbertKernel
      ring

/-- A sharp ordinary truncation has the elementary size bound `1 / ε`
against any integrable input. Unlike the finite-annular estimate, the
constant is independent of an outer radius. -/
theorem norm_zeroHilbertTruncation_le_inv_mul_integral_norm
    {b : ℝ → ℂ} (hb : Integrable b) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ‖quadraticHilbertTrunc 0 ε b x‖ ≤
      (1 / ε) * ∫ y, ‖b y‖ := by
  rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc]
  unfold quadraticHilbertConvolutionTrunc
  have hkernel : AEStronglyMeasurable
      (fun y ↦ sharpQuadraticTailKernel 0 ε (x - y)) volume :=
    (measurable_sharpQuadraticTailKernel 0 ε).comp
      (measurable_const.sub measurable_id) |>.aestronglyMeasurable
  have hintegrable : Integrable
      (fun y ↦ sharpQuadraticTailKernel 0 ε (x - y) * b y) :=
    hb.bdd_mul hkernel (Filter.Eventually.of_forall fun y ↦
      sharpQuadraticTailKernel_norm_le 0 hε)
  calc
    ‖∫ y, sharpQuadraticTailKernel 0 ε (x - y) * b y‖ ≤
        ∫ y, ‖sharpQuadraticTailKernel 0 ε (x - y) * b y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, (1 / ε) * ‖b y‖ := by
      apply integral_mono hintegrable.norm (hb.norm.const_mul (1 / ε))
      intro y
      change ‖sharpQuadraticTailKernel 0 ε (x - y) * b y‖ ≤
        (1 / ε) * ‖b y‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (sharpQuadraticTailKernel_norm_le 0 hε) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem ofReal_inv_mul_eq_four_mul_div_four_mul {ε : ℝ} (hε : 0 < ε)
    (m : ℝ≥0∞) :
    ENNReal.ofReal (1 / ε) * m =
      4 * (m / ENNReal.ofReal (4 * ε)) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos hε]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  calc
    (ENNReal.ofReal ε)⁻¹ * m =
        (4 * 4⁻¹) * ((ENNReal.ofReal ε)⁻¹ * m) := by
      rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ = 4 * (4⁻¹ * (ENNReal.ofReal ε)⁻¹ * m) := by ac_rfl

/-- If an interval of length at most `ε` contains a point within `ε` of
`x`, then the whole interval lies in the centered ball of radius `2ε`. -/
theorem centeredInterval_subset_closedBall_two_mul_of_near
    {z R x ε y₀ : ℝ} (hy₀ : y₀ ∈ centeredInterval z R)
    (hy₀x : |x - y₀| ≤ ε) (hRε : R ≤ ε) :
    centeredInterval z R ⊆ Metric.closedBall x (2 * ε) := by
  intro y hy
  have hyz := abs_sub_center_le_of_mem_centeredInterval hy
  have hy₀z := abs_sub_center_le_of_mem_centeredInterval hy₀
  have hyy₀ : |y - y₀| ≤ R := by
    calc
      |y - y₀| = |(y - z) + (z - y₀)| := by ring_nf
      _ ≤ |y - z| + |z - y₀| := abs_add_le _ _
      _ = |y - z| + |y₀ - z| := by rw [abs_sub_comm z y₀]
      _ ≤ R := by linarith
  change dist y x ≤ 2 * ε
  rw [Real.dist_eq, abs_sub_comm y x]
  calc
    |x - y| = |(x - y₀) + (y₀ - y)| := by ring_nf
    _ ≤ |x - y₀| + |y₀ - y| := abs_add_le _ _
    _ = |x - y₀| + |y - y₀| := by rw [abs_sub_comm y₀ y]
    _ ≤ 2 * ε := by linarith

/-- Pointwise monotonicity of the centered Hardy--Littlewood maximal
operator. -/
theorem centeredHardyLittlewoodMaximal_mono_pointwise
    {u v : ℝ → ℝ≥0∞} (huv : ∀ y, u y ≤ v y) (x : ℝ) :
    centeredHardyLittlewoodMaximal u x ≤
      centeredHardyLittlewoodMaximal v x := by
  unfold centeredHardyLittlewoodMaximal
  apply iSup_mono
  intro q
  unfold centeredAverage
  gcongr with y
  exact huv y

/-- A truncation boundary crosses a set when the deleted ball contains a
point of the set while the retained tail also contains a point. -/
def IsTruncationBoundary (x ε : ℝ) (s : Set ℝ) : Prop :=
  (∃ y ∈ s, |x - y| ≤ ε) ∧ ∃ y ∈ s, ε < |x - y|

/-- For an interval-supported function, a cell not crossed by the sharp
boundary contributes either zero (the interval is wholly deleted) or its
complete ordinary-kernel integral (the interval is wholly retained). -/
theorem zeroHilbertTruncation_eq_zero_or_full_of_not_boundary
    {b : ℝ → ℂ} {z R x ε : ℝ}
    (hsupp : ∀ y ∉ centeredInterval z R, b y = 0)
    (hnot : ¬ IsTruncationBoundary x ε (centeredInterval z R)) :
    quadraticHilbertTrunc 0 ε b x = 0 ∨
      quadraticHilbertTrunc 0 ε b x =
        ∫ y in centeredInterval z R, ordinaryHilbertKernel x y * b y := by
  by_cases hnear : ∃ y ∈ centeredInterval z R, |x - y| ≤ ε
  · left
    have hnfar : ¬ ∃ y ∈ centeredInterval z R, ε < |x - y| :=
      fun hfar ↦ hnot ⟨hnear, hfar⟩
    rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc]
    unfold quadraticHilbertConvolutionTrunc
    apply integral_eq_zero_of_ae
    filter_upwards with y
    change sharpQuadraticTailKernel 0 ε (x - y) * b y = 0
    by_cases hy : y ∈ centeredInterval z R
    · have hcut : ¬ ε < |x - y| := by
        intro hxy
        exact hnfar ⟨y, hy, hxy⟩
      simp [sharpQuadraticTailKernel, hcut]
    · simp [hsupp y hy]
  · right
    rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc]
    unfold quadraticHilbertConvolutionTrunc
    calc
      (∫ y, sharpQuadraticTailKernel 0 ε (x - y) * b y) =
          ∫ y in centeredInterval z R,
            sharpQuadraticTailKernel 0 ε (x - y) * b y := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        rw [hsupp y hy, mul_zero]
      _ = ∫ y in centeredInterval z R,
          ordinaryHilbertKernel x y * b y := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
        have hcut : ε < |x - y| := lt_of_not_ge fun hle ↦
          hnear ⟨y, hy, hle⟩
        rw [sharpQuadraticTailKernel, ite_eq_left hcut, zero_mul, phase_zero]
        unfold ordinaryHilbertKernel
        ring

/-- For an interval lying outside its triple, a sharp radial boundary that
crosses the interval must pass through the interval at one of the two points
`x - ε` or `x + ε`. -/
theorem truncationBoundary_centeredInterval_mem_left_or_right
    {z R x ε : ℝ} (hR : 0 < R)
    (hx : x ∉ tripleCenteredInterval z R)
    (hboundary : IsTruncationBoundary x ε (centeredInterval z R)) :
    x - ε ∈ centeredInterval z R ∨ x + ε ∈ centeredInterval z R := by
  rcases hboundary with ⟨⟨yn, hyn, hnear⟩, ⟨yf, hyf, hfar⟩⟩
  have hxabs : 3 * R / 2 < |x - z| := not_mem_tripleCenteredInterval_abs hx
  rcases le_total z x with hzx | hxz
  · left
    have hsign : 0 ≤ x - z := sub_nonneg.mpr hzx
    rw [abs_of_nonneg hsign] at hxabs
    have hyn' := hyn
    have hyf' := hyf
    simp only [centeredInterval, mem_Ico] at hyn' hyf' ⊢
    have hynx : yn < x := by linarith
    have hyfx : yf < x := by linarith
    rw [abs_of_pos (sub_pos.mpr hynx)] at hnear
    rw [abs_of_pos (sub_pos.mpr hyfx)] at hfar
    constructor <;> linarith
  · right
    have hsign : x - z ≤ 0 := sub_nonpos.mpr hxz
    rw [abs_of_nonpos hsign] at hxabs
    have hyn' := hyn
    have hyf' := hyf
    simp only [centeredInterval, mem_Ico] at hyn' hyf' ⊢
    have hxyn : x < yn := by linarith
    have hxyf : x < yf := by linarith
    rw [abs_of_neg (sub_neg.mpr hxyn)] at hnear
    rw [abs_of_neg (sub_neg.mpr hxyf)] at hfar
    constructor <;> linarith

/-- Outside the tripled interval, if the deleted truncation ball meets the
interval, then the truncation radius is strictly larger than its length. -/
theorem centeredInterval_length_lt_radius_of_notMem_triple_of_near
    {z R x ε y : ℝ} (hy : y ∈ centeredInterval z R)
    (hnear : |x - y| ≤ ε) (hx : x ∉ tripleCenteredInterval z R) :
    R < ε := by
  have hxz : 3 * R / 2 < |x - z| :=
    not_mem_tripleCenteredInterval_abs hx
  have hyz : |y - z| ≤ R / 2 := abs_sub_center_le_of_mem_centeredInterval hy
  have htriangle : |x - z| ≤ |x - y| + |y - z| := by
    calc
      |x - z| = |(x - y) + (y - z)| := by ring_nf
      _ ≤ |x - y| + |y - z| := abs_add_le _ _
  linarith

/-- A large-radius truncation of an interval-supported input is controlled
by the centered Hardy--Littlewood maximal function as soon as the deleted
ball meets the interval. This is the analytic estimate for a boundary
cell; combinatorially there are at most two such cells at a fixed radius. -/
theorem enorm_zeroHilbertTruncation_le_eight_maximal_of_interval_near
    {b : ℝ → ℂ} (hb : Integrable b) {z R x ε y₀ : ℝ}
    (hsupp : ∀ y ∉ centeredInterval z R, b y = 0)
    (hε : 0 < ε) (hRε : R ≤ ε)
    (hy₀ : y₀ ∈ centeredInterval z R) (hy₀x : |x - y₀| ≤ ε) :
    ‖quadraticHilbertTrunc 0 ε b x‖ₑ ≤
      8 * centeredHardyLittlewoodMaximal (fun y ↦ ‖b y‖ₑ) x := by
  have hreal := norm_zeroHilbertTruncation_le_inv_mul_integral_norm hb hε x
  have henorm : ‖quadraticHilbertTrunc 0 ε b x‖ₑ ≤
      ENNReal.ofReal (1 / ε) * ∫⁻ y, ‖b y‖ₑ := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ofReal_norm, ENNReal.ofReal_mul (one_div_nonneg.mpr hε.le),
      ofReal_integral_eq_lintegral_ofReal hb.norm
        (Filter.Eventually.of_forall fun y ↦ norm_nonneg (b y))] at h
    simpa only [ofReal_norm] using h
  have hsubset := centeredInterval_subset_closedBall_two_mul_of_near
    hy₀ hy₀x hRε
  have hmass : (∫⁻ y, ‖b y‖ₑ) ≤
      ∫⁻ y in Metric.closedBall x (2 * ε), ‖b y‖ₑ := by
    rw [← lintegral_indicator measurableSet_closedBall]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ Metric.closedBall x (2 * ε)
    · simp [hy]
    · have hyI : y ∉ centeredInterval z R := fun hy' ↦ hy (hsubset hy')
      change ‖b y‖ₑ ≤
        (Metric.closedBall x (2 * ε)).indicator (fun u ↦ ‖b u‖ₑ) y
      rw [hsupp y hyI]
      simp
  calc
    ‖quadraticHilbertTrunc 0 ε b x‖ₑ ≤
        ENNReal.ofReal (1 / ε) * ∫⁻ y, ‖b y‖ₑ := henorm
    _ ≤ ENNReal.ofReal (1 / ε) *
        ∫⁻ y in Metric.closedBall x (2 * ε), ‖b y‖ₑ :=
      mul_le_mul' le_rfl hmass
    _ = 4 * centeredAverage (2 * ε) (fun y ↦ ‖b y‖ₑ) x := by
      rw [ofReal_inv_mul_eq_four_mul_div_four_mul hε]
      unfold centeredAverage
      rw [show 2 * (2 * ε) = 4 * ε by ring]
    _ ≤ 4 * (2 * centeredHardyLittlewoodMaximal (fun y ↦ ‖b y‖ₑ) x) := by
      exact mul_le_mul' le_rfl
        (centeredAverage_le_two_mul_centeredHardyLittlewoodMaximal
          (by positivity) _ x)
    _ = _ := by ring

/-! ## Specialization to the canonical stopping cells -/

/-- The length of a canonical stopping interval for `f`. -/
def stoppingCellLength (f : ℝ → ℂ) (c : stoppingCell f) : ℝ :=
  dyadicLength (rootLength f) c.1.depth

/-- The midpoint of a canonical stopping interval for `f`. -/
def stoppingCellCenter (f : ℝ → ℂ) (c : stoppingCell f) : ℝ :=
  ((c.1.index : ℝ) + 1 / 2) * stoppingCellLength f c

theorem stoppingCellLength_pos (f : ℝ → ℂ) (c : stoppingCell f) :
    0 < stoppingCellLength f c :=
  dyadicLength_pos rootLength_pos c.1.depth

theorem stoppingCell_interval_eq_centeredInterval (f : ℝ → ℂ)
    (c : stoppingCell f) :
    c.1.interval (rootLength f) =
      centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c) := by
  unfold DyadicCell.interval dyadicInterval centeredInterval stoppingCellCenter
    stoppingCellLength
  congr 1 <;> ring

/-- Union of the triples of all canonical stopping cells. This is the
exceptional set discarded in the usual bad-part argument. -/
def stoppingTripleBadUnion (f : ℝ → ℂ) : Set ℝ :=
  ⋃ c : stoppingCell f,
    tripleCenteredInterval (stoppingCellCenter f c) (stoppingCellLength f c)

/-- The stopping cells cut by the sharp truncation boundary at radius `ε`.
These are the only cells for which the truncated atom is neither zero nor
its complete (untruncated) ordinary-kernel integral. -/
def stoppingBoundaryCells (f : ℝ → ℂ) (x ε : ℝ) : Set (stoppingCell f) :=
  {c | IsTruncationBoundary x ε (c.1.interval (rootLength f))}

/-- Pairwise disjointness implies that at most one stopping cell can contain
a prescribed point. -/
theorem stoppingCells_containing_subsingleton (f : ℝ → ℂ) (y : ℝ) :
    Set.Subsingleton
      {c : stoppingCell f | y ∈ c.1.interval (rootLength f)} := by
  intro c hc d hd
  by_contra hcd
  exact Set.disjoint_left.1 (stoppingCell_pairwiseDisjoint hcd) hc hd

/-- Outside the union of tripled stopping cells, every cell cut by the sharp
truncation boundary contains one of the two boundary points. -/
theorem stoppingBoundaryCells_subset_endpointCells (f : ℝ → ℂ) {x ε : ℝ}
    (hx : x ∉ stoppingTripleBadUnion f) :
    stoppingBoundaryCells f x ε ⊆
      {c : stoppingCell f | x - ε ∈ c.1.interval (rootLength f)} ∪
      {c : stoppingCell f | x + ε ∈ c.1.interval (rootLength f)} := by
  intro c hc
  have hxc : x ∉ tripleCenteredInterval (stoppingCellCenter f c)
      (stoppingCellLength f c) := by
    intro hxmem
    exact hx (Set.mem_iUnion_of_mem c hxmem)
  have hboundary : IsTruncationBoundary x ε
      (centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c)) := by
    rw [← stoppingCell_interval_eq_centeredInterval f c]
    exact hc
  have hend := truncationBoundary_centeredInterval_mem_left_or_right
    (stoppingCellLength_pos f c) hxc hboundary
  rw [← stoppingCell_interval_eq_centeredInterval f c] at hend
  exact hend

/-- Every boundary stopping cell outside the tripled exceptional union is
shorter than the active truncation radius. -/
theorem stoppingBoundaryCell_length_lt_radius (f : ℝ → ℂ) {x ε : ℝ}
    (hx : x ∉ stoppingTripleBadUnion f) {c : stoppingCell f}
    (hc : c ∈ stoppingBoundaryCells f x ε) :
    stoppingCellLength f c < ε := by
  obtain ⟨⟨y, hy, hnear⟩, -⟩ := hc
  rw [stoppingCell_interval_eq_centeredInterval f c] at hy
  have hxc : x ∉ tripleCenteredInterval (stoppingCellCenter f c)
      (stoppingCellLength f c) := by
    intro hxmem
    exact hx (Set.mem_iUnion_of_mem c hxmem)
  apply centeredInterval_length_lt_radius_of_notMem_triple_of_near
    (z := stoppingCellCenter f c) (x := x) (y := y) hy hnear hxc

/-- At a fixed center and radius, outside the enlarged exceptional set there
are at most two boundary cells: one through `x - ε` and one through `x + ε`.
This is the exact one-dimensional boundary combinatorics used in the maximal
bad-part estimate. -/
theorem stoppingBoundaryCells_finite_and_ncard_le_two (f : ℝ → ℂ) {x ε : ℝ}
    (hx : x ∉ stoppingTripleBadUnion f) :
    (stoppingBoundaryCells f x ε).Finite ∧
      (stoppingBoundaryCells f x ε).ncard ≤ 2 := by
  let leftCells : Set (stoppingCell f) :=
    {c | x - ε ∈ c.1.interval (rootLength f)}
  let rightCells : Set (stoppingCell f) :=
    {c | x + ε ∈ c.1.interval (rootLength f)}
  have hleftSub : leftCells.Subsingleton :=
    stoppingCells_containing_subsingleton f (x - ε)
  have hrightSub : rightCells.Subsingleton :=
    stoppingCells_containing_subsingleton f (x + ε)
  have hunionFinite : (leftCells ∪ rightCells).Finite :=
    hleftSub.finite.union hrightSub.finite
  have hsub : stoppingBoundaryCells f x ε ⊆ leftCells ∪ rightCells :=
    stoppingBoundaryCells_subset_endpointCells f hx
  have hfinite := hunionFinite.subset hsub
  refine ⟨hfinite, ?_⟩
  calc
    (stoppingBoundaryCells f x ε).ncard ≤ (leftCells ∪ rightCells).ncard :=
      Set.ncard_le_ncard hsub hunionFinite
    _ ≤ leftCells.ncard + rightCells.ncard := Set.ncard_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      ((Set.ncard_le_one hleftSub.finite).2 hleftSub)
      ((Set.ncard_le_one hrightSub.finite).2 hrightSub)
    _ = 2 := by norm_num

theorem measurableSet_stoppingTripleBadUnion (f : ℝ → ℂ) :
    MeasurableSet (stoppingTripleBadUnion f) := by
  let _ := Encodable.ofCountable (stoppingCell f)
  exact MeasurableSet.iUnion (fun _ ↦ measurableSet_Icc)

theorem volume_triple_stoppingCell (f : ℝ → ℂ) (c : stoppingCell f) :
    volume (tripleCenteredInterval (stoppingCellCenter f c)
      (stoppingCellLength f c)) =
      3 * volume (c.1.interval (rootLength f)) := by
  rw [tripleCenteredInterval, Real.volume_Icc]
  rw [show stoppingCellCenter f c + 3 * stoppingCellLength f c / 2 -
      (stoppingCellCenter f c - 3 * stoppingCellLength f c / 2) =
      3 * stoppingCellLength f c by ring]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
    volume_stoppingCell_interval]
  simp only [stoppingCellLength]
  norm_num

/-- The union of the tripled stopping cells has measure at most three times
the global `L¹` mass. Disjointness is used only before tripling. -/
theorem volume_stoppingTripleBadUnion_le_lintegral_norm {f : ℝ → ℂ}
    (hf : Integrable f) :
    volume (stoppingTripleBadUnion f) ≤
      3 * ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  let _ := Encodable.ofCountable (stoppingCell f)
  calc
    volume (stoppingTripleBadUnion f) ≤
        ∑' c : stoppingCell f,
          volume (tripleCenteredInterval (stoppingCellCenter f c)
            (stoppingCellLength f c)) := by
      exact measure_iUnion_le _
    _ = ∑' c : stoppingCell f,
        3 * volume (c.1.interval (rootLength f)) := by
      congr 1
      funext c
      exact volume_triple_stoppingCell f c
    _ = 3 * ∑' c : stoppingCell f,
        volume (c.1.interval (rootLength f)) := ENNReal.tsum_mul_left
    _ ≤ 3 * ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
      gcongr
      exact tsum_volume_stoppingCell_le_lintegral_norm hf

theorem volume_stoppingTripleBadUnion_lt_top {f : ℝ → ℂ}
    (hf : Integrable f) : volume (stoppingTripleBadUnion f) < ∞ := by
  apply (volume_stoppingTripleBadUnion_le_lintegral_norm hf).trans_lt
  rw [← ofReal_integral_eq_lintegral_ofReal hf.norm
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))]
  exact ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

/-- The bad atom carried by one canonical half-open stopping cell. -/
def stoppingHilbertBadAtom (f : ℝ → ℂ) (c : stoppingCell f) : ℝ → ℂ :=
  (c.1.interval (rootLength f)).indicator
    (fun x ↦ f x - stoppingCellAverage f c)

/-- Pointwise sum of the norms of all canonical stopping atoms. Since their
supports are pairwise disjoint this is morally the norm of the full bad
part, while the `tsum` presentation is convenient for Tonelli. -/
noncomputable def stoppingHilbertBadAtomNormSum (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' c : stoppingCell f, ‖stoppingHilbertBadAtom f c x‖ₑ

/-- Sum of the complete ordinary-kernel actions of all stopping atoms. -/
noncomputable def stoppingFullKernelMajorant (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' c : stoppingCell f,
    ‖∫ y in centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c),
      ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y‖ₑ

/-- The sharp-truncation mass carried by cells crossed by the active
boundary. -/
noncomputable def stoppingBoundaryTruncationMajorant
    (f : ℝ → ℂ) (x ε : ℝ) : ℝ≥0∞ := by
  classical
  exact ∑' c : stoppingCell f,
    if c ∈ stoppingBoundaryCells f x ε then
      ‖quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ₑ else 0

theorem measurable_stoppingHilbertBadAtom {f : ℝ → ℂ} (hf : Measurable f)
    (c : stoppingCell f) : Measurable (stoppingHilbertBadAtom f c) :=
  (hf.sub measurable_const).indicator measurableSet_Ico

theorem integrable_stoppingHilbertBadAtom {f : ℝ → ℂ} (hf : Integrable f)
    (c : stoppingCell f) : Integrable (stoppingHilbertBadAtom f c) := by
  apply IntegrableOn.integrable_indicator
  · exact hf.integrableOn.sub
      (integrableOn_const (volume_stoppingCell_interval_lt_top c).ne)
  · exact measurableSet_stoppingCell_interval c

theorem integral_stoppingHilbertBadAtom_eq_zero {f : ℝ → ℂ}
    (c : stoppingCell f) : ∫ x, stoppingHilbertBadAtom f c x = 0 := by
  rw [stoppingHilbertBadAtom,
    integral_indicator (measurableSet_stoppingCell_interval c)]
  exact setAverage_sub_setAverage
    (volume_stoppingCell_interval_lt_top c).ne f

theorem aestronglyMeasurable_stoppingFullKernelAction {f : ℝ → ℂ}
    (hf : Measurable f) (c : stoppingCell f) :
    AEStronglyMeasurable
      (fun x ↦ ∫ y in centeredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c),
        ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y) volume := by
  have hbI : AEStronglyMeasurable
      ((centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c)).indicator
        (stoppingHilbertBadAtom f c)) volume :=
    (measurable_stoppingHilbertBadAtom hf c).aestronglyMeasurable.indicator
      measurableSet_Ico
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ordinaryHilbertKernel p.1 p.2 *
        (centeredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c)).indicator
            (stoppingHilbertBadAtom f c) p.2) (volume.prod volume) :=
    measurable_ordinaryHilbertKernel.aestronglyMeasurable.mul
      (hbI.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hout := hjoint.integral_prod_right'
  have heq : (fun x ↦ ∫ y, ordinaryHilbertKernel x y *
      (centeredInterval (stoppingCellCenter f c)
        (stoppingCellLength f c)).indicator
          (stoppingHilbertBadAtom f c) y) =
      (fun x ↦ ∫ y in centeredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c),
        ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y) := by
    funext x
    calc
      _ = ∫ y, (centeredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c)).indicator
            (fun u ↦ ordinaryHilbertKernel x u * stoppingHilbertBadAtom f c u) y := by
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : y ∈ centeredInterval (stoppingCellCenter f c)
            (stoppingCellLength f c) <;> simp [hy]
      _ = _ := integral_indicator measurableSet_Ico
  rw [← heq]
  exact hout

theorem integrableOn_stoppingFullKernelAction_compl_triple {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) (c : stoppingCell f) :
    IntegrableOn
      (fun x ↦ ∫ y in centeredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c),
        ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y)
      (tripleCenteredInterval (stoppingCellCenter f c)
        (stoppingCellLength f c))ᶜ := by
  let z := stoppingCellCenter f c
  let R := stoppingCellLength f c
  let b := stoppingHilbertBadAtom f c
  let A := ∫ y in centeredInterval z R, ‖b y‖
  have hb := integrable_stoppingHilbertBadAtom hfi c
  have hbI : IntegrableOn b (centeredInterval z R) := hb.integrableOn
  have hmean : ∫ y in centeredInterval z R, b y = 0 := by
    rw [← stoppingCell_interval_eq_centeredInterval f c]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_stoppingHilbertBadAtom_eq_zero c
    · intro x hx
      simp [b, stoppingHilbertBadAtom, hx]
  have hmaj : IntegrableOn (fun x : ℝ ↦
      (4 * R * A) * (1 / |x - z| ^ 2)) (tripleCenteredInterval z R)ᶜ :=
    (integrableOn_inv_abs_sub_sq_compl_tripleCenteredInterval z R
      (stoppingCellLength_pos f c)).const_mul (4 * R * A)
  apply hmaj.mono'
  · exact (aestronglyMeasurable_stoppingFullKernelAction hf c).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
    have hreg : ∀ y ∈ centeredInterval z R,
        ‖ordinaryHilbertKernel x y - ordinaryHilbertKernel x z‖ ≤
          2 * |y - z| / |x - y| ^ 2 := by
      intro y hy
      simpa only [z, R] using ordinaryHilbertKernel_sub_center_norm_le
        (stoppingCellLength_pos f c)
        (by simpa only [z, R, mem_compl_iff] using hx)
        (by simpa only [z, R] using hy)
    have hbound := norm_setIntegral_kernel_le_decay ordinaryHilbertKernel b x z R 2
      (stoppingCellLength_pos f c) (by norm_num) hx hbI
      (integrableOn_ordinaryHilbertKernel_mul_atom
        (stoppingCellLength_pos f c) hx hbI) hmean
      hreg
    simpa only [z, R, b, A] using hbound.trans_eq (by ring)

theorem integral_norm_stoppingHilbertBadAtom_le {f : ℝ → ℂ}
    (hf : Integrable f) (c : stoppingCell f) :
    (∫ x, ‖stoppingHilbertBadAtom f c x‖) ≤
      2 * ∫ x in c.1.interval (rootLength f), ‖f x‖ := by
  let I := c.1.interval (rootLength f)
  let a := stoppingCellAverage f c
  have hI : MeasurableSet I := measurableSet_stoppingCell_interval c
  have hIfin : volume I ≠ ∞ := (volume_stoppingCell_interval_lt_top c).ne
  have hnormavg : volume.real I * ‖a‖ ≤ ∫ x in I, ‖f x‖ := by
    calc
      volume.real I * ‖a‖ = ‖volume.real I • a‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      _ = ‖∫ x in I, f x‖ := by
        change ‖volume.real I • (⨍ x in I, f x)‖ = ‖∫ x in I, f x‖
        rw [measure_smul_setAverage f hIfin]
      _ ≤ ∫ x in I, ‖f x‖ := norm_integral_le_integral_norm _
  have hconst : IntegrableOn (fun _ : ℝ ↦ a) I := integrableOn_const hIfin
  have htriangle : (∫ x in I, ‖f x - a‖) ≤
      ∫ x in I, ‖f x‖ + ‖a‖ :=
    setIntegral_mono_on (hf.integrableOn.sub hconst).norm
      (hf.norm.integrableOn.add hconst.norm) hI (fun x _ ↦ norm_sub_le _ _)
  have hatom : (∫ x, ‖stoppingHilbertBadAtom f c x‖) =
      ∫ x in I, ‖f x - a‖ := by
    simp only [stoppingHilbertBadAtom, I, a, norm_indicator_eq_indicator_norm]
    exact integral_indicator hI
  rw [hatom]
  calc
    (∫ x in I, ‖f x - a‖) ≤ ∫ x in I, ‖f x‖ + ‖a‖ := htriangle
    _ = (∫ x in I, ‖f x‖) + volume.real I * ‖a‖ := by
      rw [integral_add hf.norm.integrableOn hconst.norm, setIntegral_const,
        smul_eq_mul]
    _ ≤ (∫ x in I, ‖f x‖) + ∫ x in I, ‖f x‖ :=
      add_le_add le_rfl hnormavg
    _ = 2 * ∫ x in I, ‖f x‖ := by ring

theorem measurable_stoppingHilbertBadAtomNormSum {f : ℝ → ℂ}
    (hf : Measurable f) : Measurable (stoppingHilbertBadAtomNormSum f) := by
  let _ := Encodable.ofCountable (stoppingCell f)
  exact Measurable.tsum fun c ↦ (measurable_stoppingHilbertBadAtom hf c).enorm

/-- ENNReal form of the single-atom `L¹` estimate. -/
theorem lintegral_enorm_stoppingHilbertBadAtom_le {f : ℝ → ℂ}
    (hf : Integrable f) (c : stoppingCell f) :
    (∫⁻ x, ‖stoppingHilbertBadAtom f c x‖ₑ) ≤
      2 * ∫⁻ x in c.1.interval (rootLength f), ‖f x‖ₑ := by
  have hb := integrable_stoppingHilbertBadAtom hf c
  have hI := measurableSet_stoppingCell_interval c
  have hfI : Integrable
      ((c.1.interval (rootLength f)).indicator fun x ↦ ‖f x‖) :=
    hf.norm.indicator hI
  have hleft : (∫⁻ x, ‖stoppingHilbertBadAtom f c x‖ₑ) =
      ENNReal.ofReal (∫ x, ‖stoppingHilbertBadAtom f c x‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal hb.norm
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg
        (stoppingHilbertBadAtom f c x))]
    simp only [ofReal_norm]
  have hright : (∫⁻ x in c.1.interval (rootLength f), ‖f x‖ₑ) =
      ENNReal.ofReal (∫ x in c.1.interval (rootLength f), ‖f x‖) := by
    rw [← lintegral_indicator hI, ← integral_indicator hI]
    rw [ofReal_integral_eq_lintegral_ofReal hfI
      (Filter.Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ c.1.interval (rootLength f) <;> simp [hx])]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ c.1.interval (rootLength f) <;> simp [hx]
  rw [hleft, hright, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (integral_norm_stoppingHilbertBadAtom_le hf c)

/-- The complete pointwise norm sum of the canonical bad atoms has `L¹`
mass at most twice that of the original input. -/
theorem lintegral_stoppingHilbertBadAtomNormSum_le {f : ℝ → ℂ}
    (hf : Integrable f) :
    (∫⁻ x, stoppingHilbertBadAtomNormSum f x) ≤
      2 * ∫⁻ x, ‖f x‖ₑ := by
  let _ := Encodable.ofCountable (stoppingCell f)
  change (∫⁻ x, ∑' c : stoppingCell f,
    ‖stoppingHilbertBadAtom f c x‖ₑ) ≤ 2 * ∫⁻ x, ‖f x‖ₑ
  rw [lintegral_tsum (fun c ↦
    (integrable_stoppingHilbertBadAtom hf c).1.enorm)]
  calc
    (∑' c : stoppingCell f, ∫⁻ x, ‖stoppingHilbertBadAtom f c x‖ₑ) ≤
        ∑' c : stoppingCell f,
          2 * ∫⁻ x in c.1.interval (rootLength f), ‖f x‖ₑ :=
      ENNReal.tsum_le_tsum fun c ↦ lintegral_enorm_stoppingHilbertBadAtom_le hf c
    _ = 2 * ∑' c : stoppingCell f,
          ∫⁻ x in c.1.interval (rootLength f), ‖f x‖ₑ :=
      ENNReal.tsum_mul_left
    _ = 2 * ∫⁻ x in stoppingBadUnion f, ‖f x‖ₑ := by
      rw [stoppingBadUnion, lintegral_iUnion
        (fun c : stoppingCell f ↦ measurableSet_stoppingCell_interval c)
        stoppingCell_pairwiseDisjoint]
    _ ≤ 2 * ∫⁻ x, ‖f x‖ₑ :=
      mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- The countable sum of canonical stopping atoms is an honest integrable
function. -/
theorem integrable_tsum_stoppingHilbertBadAtom {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) :
    Integrable (fun x ↦ ∑' c : stoppingCell f, stoppingHilbertBadAtom f c x) := by
  let _ := Encodable.ofCountable (stoppingCell f)
  refine ⟨(Measurable.tsum fun c ↦
    measurable_stoppingHilbertBadAtom hf c).aestronglyMeasurable, ?_⟩
  calc
    (∫⁻ x, ‖∑' c : stoppingCell f, stoppingHilbertBadAtom f c x‖ₑ) ≤
        ∫⁻ x, stoppingHilbertBadAtomNormSum f x := by
      apply lintegral_mono
      intro x
      exact enorm_tsum_le_tsum_enorm
    _ ≤ 2 * ∫⁻ x, ‖f x‖ₑ :=
      lintegral_stoppingHilbertBadAtomNormSum_le hfi
    _ < ∞ := ENNReal.mul_lt_top (by norm_num) hfi.hasFiniteIntegral

/-- Exact pointwise recombination of the canonical stopping atoms with the
ordinary Calderón--Zygmund bad part. Pairwise disjointness makes the series
pointwise finite, so this identity needs no convergence hypothesis. -/
theorem tsum_stoppingHilbertBadAtom_eq_sub_stoppingGoodPart
    (f : ℝ → ℂ) (x : ℝ) :
    (∑' c : stoppingCell f, stoppingHilbertBadAtom f c x) =
      f x - stoppingGoodPart f x := by
  classical
  by_cases hx : x ∈ stoppingBadUnion f
  · obtain ⟨c, hxc⟩ := mem_iUnion.mp hx
    rw [tsum_eq_single c]
    · rw [stoppingGoodPart_eq_average_of_mem c hxc]
      simp [stoppingHilbertBadAtom, hxc]
    · intro d hdc
      have hdis := stoppingCell_pairwiseDisjoint (f := f) hdc.symm
      have hxd : x ∉ d.1.interval (rootLength f) :=
        fun hmem ↦ Set.disjoint_left.1 hdis hxc hmem
      simp [stoppingHilbertBadAtom, hxd]
  · rw [stoppingGoodPart_eq_of_notMem hx, sub_self]
    have hzero : (fun c : stoppingCell f ↦ stoppingHilbertBadAtom f c x) = 0 := by
      funext c
      have hxc : x ∉ c.1.interval (rootLength f) :=
        fun hmem ↦ hx (mem_iUnion.mpr ⟨c, hmem⟩)
      simp [stoppingHilbertBadAtom, hxc]
    rw [hzero]
    exact tsum_zero

/-- The kernel-weighted stopping-atom series is absolutely integrable at
every positive sharp truncation radius. -/
theorem tsum_lintegral_enorm_sharpKernel_mul_stoppingAtom_lt_top
    {f : ℝ → ℂ} (hfi : Integrable f) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (∑' c : stoppingCell f, ∫⁻ y,
      ‖sharpQuadraticTailKernel 0 ε (x - y) *
        stoppingHilbertBadAtom f c y‖ₑ) < ∞ := by
  have hterm (c : stoppingCell f) :
      (∫⁻ y, ‖sharpQuadraticTailKernel 0 ε (x - y) *
        stoppingHilbertBadAtom f c y‖ₑ) ≤
        ENNReal.ofReal (1 / ε) *
          ∫⁻ y, ‖stoppingHilbertBadAtom f c y‖ₑ := by
    calc
      _ ≤ ∫⁻ y, ENNReal.ofReal (1 / ε) *
          ‖stoppingHilbertBadAtom f c y‖ₑ := by
        apply lintegral_mono
        intro y
        change ‖sharpQuadraticTailKernel 0 ε (x - y) *
          stoppingHilbertBadAtom f c y‖ₑ ≤
            ENNReal.ofReal (1 / ε) * ‖stoppingHilbertBadAtom f c y‖ₑ
        rw [enorm_mul]
        apply mul_le_mul' _ le_rfl
        have hk := ENNReal.ofReal_le_ofReal
          (sharpQuadraticTailKernel_norm_le 0 (t := x - y) hε)
        simpa only [ofReal_norm] using hk
      _ = _ := lintegral_const_mul' _ _ (by finiteness)
  have hs := ENNReal.tsum_le_tsum hterm
  rw [ENNReal.tsum_mul_left] at hs
  have hsum : (∑' c : stoppingCell f,
      ∫⁻ y, ‖stoppingHilbertBadAtom f c y‖ₑ) =
      ∫⁻ y, stoppingHilbertBadAtomNormSum f y := by
    change (∑' c : stoppingCell f,
      ∫⁻ y, ‖stoppingHilbertBadAtom f c y‖ₑ) =
      ∫⁻ y, ∑' c : stoppingCell f, ‖stoppingHilbertBadAtom f c y‖ₑ
    rw [lintegral_tsum (fun c ↦
      (integrable_stoppingHilbertBadAtom hfi c).1.enorm)]
  rw [hsum] at hs
  exact hs.trans_lt (ENNReal.mul_lt_top (by finiteness)
    ((lintegral_stoppingHilbertBadAtomNormSum_le hfi).trans_lt
      (ENNReal.mul_lt_top (by norm_num) hfi.hasFiniteIntegral)))

/-- A genuine countable integral/series interchange for sharp ordinary
Hilbert truncations of the complete stopping bad part. -/
theorem zeroHilbertTruncation_tsum_stoppingHilbertBadAtom_eq_tsum
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    quadraticHilbertTrunc 0 ε
        (fun y ↦ ∑' c : stoppingCell f, stoppingHilbertBadAtom f c y) x =
      ∑' c : stoppingCell f,
        quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x := by
  rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc]
  simp_rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc]
  unfold quadraticHilbertConvolutionTrunc
  have hp (y : ℝ) : sharpQuadraticTailKernel 0 ε (x - y) *
      (∑' c : stoppingCell f, stoppingHilbertBadAtom f c y) =
      ∑' c : stoppingCell f,
        sharpQuadraticTailKernel 0 ε (x - y) * stoppingHilbertBadAtom f c y := by
    rw [tsum_mul_left]
  simp_rw [hp]
  have hK : Measurable (fun y : ℝ ↦ sharpQuadraticTailKernel 0 ε (x - y)) :=
    (measurable_sharpQuadraticTailKernel 0 ε).comp
      (measurable_const.sub measurable_id)
  exact integral_tsum
    (fun c ↦ (hK.mul
      (measurable_stoppingHilbertBadAtom hf c)).aestronglyMeasurable)
    (tsum_lintegral_enorm_sharpKernel_mul_stoppingAtom_lt_top hfi hε x).ne

/-- Exact sharp-truncation recombination in the usual `f - good` form of
the Calderón--Zygmund decomposition. -/
theorem zeroHilbertTruncation_sub_stoppingGoodPart_eq_tsum
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    quadraticHilbertTrunc 0 ε (fun y ↦ f y - stoppingGoodPart f y) x =
      ∑' c : stoppingCell f,
        quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x := by
  have heq : (fun y ↦ f y - stoppingGoodPart f y) =
      (fun y ↦ ∑' c : stoppingCell f, stoppingHilbertBadAtom f c y) := by
    funext y
    exact (tsum_stoppingHilbertBadAtom_eq_sub_stoppingGoodPart f y).symm
  rw [heq]
  exact zeroHilbertTruncation_tsum_stoppingHilbertBadAtom_eq_tsum
    hf hfi hε x

/-- Weak `(1,1)` bound for the single maximal function that controls every
boundary-cell sum. The threshold is written in the naturally scaled form
to avoid any finiteness side condition on an arbitrary ENNReal threshold. -/
theorem stoppingHilbertBadAtomNormSum_boundaryMaximal_weak_bound
    {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ≥0∞) :
    (16 * a) * volume {x | 16 * a <
      16 * centeredHardyLittlewoodMaximal
        (stoppingHilbertBadAtomNormSum f) x} ≤
      128 * ∫⁻ x, ‖f x‖ₑ := by
  have hset : {x | 16 * a < 16 * centeredHardyLittlewoodMaximal
      (stoppingHilbertBadAtomNormSum f) x} =
      {x | a < centeredHardyLittlewoodMaximal
        (stoppingHilbertBadAtomNormSum f) x} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    exact (ENNReal.mul_right_strictMono (a := (16 : ℝ≥0∞))
      (by norm_num) (by norm_num)).lt_iff_lt
  rw [hset]
  have hweak := centeredHardyLittlewoodMaximal_weak_bound
    (stoppingHilbertBadAtomNormSum f) a
  calc
    (16 * a) * volume {x | a < centeredHardyLittlewoodMaximal
        (stoppingHilbertBadAtomNormSum f) x} =
        16 * (a * volume {x | a < centeredHardyLittlewoodMaximal
          (stoppingHilbertBadAtomNormSum f) x}) := by ac_rfl
    _ ≤ 16 * (4 * ∫⁻ x, stoppingHilbertBadAtomNormSum f x) :=
      mul_le_mul' le_rfl hweak
    _ ≤ 16 * (4 * (2 * ∫⁻ x, ‖f x‖ₑ)) := by
      gcongr
      exact lintegral_stoppingHilbertBadAtomNormSum_le hf
    _ = 128 * ∫⁻ x, ‖f x‖ₑ := by ring

/-- Large truncation radii acting on one stopping atom are bounded by its
local `L¹` mass divided by the radius. This is the size estimate used for
the at-most-two boundary cells in the maximal bad-part argument. -/
theorem norm_zeroHilbertTruncation_stoppingAtom_le
    {f : ℝ → ℂ} (hf : Integrable f) (c : stoppingCell f)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ‖quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ ≤
      (2 / ε) * ∫ y in c.1.interval (rootLength f), ‖f y‖ := by
  calc
    _ ≤ (1 / ε) * ∫ y, ‖stoppingHilbertBadAtom f c y‖ :=
      norm_zeroHilbertTruncation_le_inv_mul_integral_norm
        (integrable_stoppingHilbertBadAtom hf c) hε x
    _ ≤ (1 / ε) *
        (2 * ∫ y in c.1.interval (rootLength f), ‖f y‖) := by
      apply mul_le_mul_of_nonneg_left
        (integral_norm_stoppingHilbertBadAtom_le hf c)
      exact one_div_nonneg.mpr hε.le
    _ = _ := by ring

/-- Stopping-cell specialization of the boundary-cell maximal estimate. -/
theorem enorm_zeroHilbertTruncation_stoppingAtom_le_eight_maximal
    {f : ℝ → ℂ} (hf : Integrable f) (c : stoppingCell f)
    {x ε y₀ : ℝ} (hε : 0 < ε)
    (hlen : stoppingCellLength f c ≤ ε)
    (hy₀ : y₀ ∈ c.1.interval (rootLength f)) (hy₀x : |x - y₀| ≤ ε) :
    ‖quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ₑ ≤
      8 * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖stoppingHilbertBadAtom f c y‖ₑ) x := by
  apply enorm_zeroHilbertTruncation_le_eight_maximal_of_interval_near
    (integrable_stoppingHilbertBadAtom hf c)
    (z := stoppingCellCenter f c) (R := stoppingCellLength f c)
    (y₀ := y₀)
  · intro y hy
    rw [← stoppingCell_interval_eq_centeredInterval f c] at hy
    simp [stoppingHilbertBadAtom, hy]
  · exact hε
  · exact hlen
  · rwa [← stoppingCell_interval_eq_centeredInterval f c]
  · exact hy₀x

/-- A boundary stopping atom outside the tripled exceptional union obeys
the Hardy--Littlewood maximal estimate with no separate radius assumption:
the geometry forces its cell length to be smaller than the radius. -/
theorem enorm_zeroHilbertTruncation_boundaryStoppingAtom_le_eight_maximal
    {f : ℝ → ℂ} (hf : Integrable f) {x ε : ℝ}
    (hx : x ∉ stoppingTripleBadUnion f) {c : stoppingCell f}
    (hc : c ∈ stoppingBoundaryCells f x ε) :
    ‖quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ₑ ≤
      8 * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖stoppingHilbertBadAtom f c y‖ₑ) x := by
  have hc' := hc
  obtain ⟨⟨y, hy, hnear⟩, -⟩ := hc'
  have hlen := stoppingBoundaryCell_length_lt_radius f hx hc
  exact enorm_zeroHilbertTruncation_stoppingAtom_le_eight_maximal hf c
    ((stoppingCellLength_pos f c).trans hlen) hlen.le hy hnear

/-- The sum of all boundary-cell truncations is controlled by a single
Hardy--Littlewood maximal function. The constant `16` is `8` from the
single-cell size estimate times the sharp count of at most two cells. -/
theorem sum_enorm_zeroHilbertTruncation_boundaryStoppingAtoms_le
    {f : ℝ → ℂ} (hf : Integrable f) {x ε : ℝ}
    (hx : x ∉ stoppingTripleBadUnion f) (s : Finset (stoppingCell f))
    (hs : ∀ c ∈ s, c ∈ stoppingBoundaryCells f x ε) :
    (∑ c ∈ s,
      ‖quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ₑ) ≤
      16 * centeredHardyLittlewoodMaximal
        (stoppingHilbertBadAtomNormSum f) x := by
  let M : ℝ≥0∞ := centeredHardyLittlewoodMaximal
    (stoppingHilbertBadAtomNormSum f) x
  have hterm (c : stoppingCell f) (hc : c ∈ s) :
      ‖quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ₑ ≤ 8 * M := by
    calc
      _ ≤ 8 * centeredHardyLittlewoodMaximal
          (fun y ↦ ‖stoppingHilbertBadAtom f c y‖ₑ) x :=
        enorm_zeroHilbertTruncation_boundaryStoppingAtom_le_eight_maximal
          hf hx (hs c hc)
      _ ≤ 8 * M := mul_le_mul' le_rfl
        (centeredHardyLittlewoodMaximal_mono_pointwise
          (fun y ↦ ENNReal.le_tsum (f := fun c' ↦ ‖stoppingHilbertBadAtom f c' y‖ₑ) c) x)
  have hboundary := stoppingBoundaryCells_finite_and_ncard_le_two f
    (ε := ε) hx
  have hcard : s.card ≤ 2 := by
    have hsub : (s : Set (stoppingCell f)) ⊆
        stoppingBoundaryCells f x ε := by
      intro c hc
      exact hs c hc
    have hn := Set.ncard_le_ncard hsub hboundary.1
    simpa using hn.trans hboundary.2
  calc
    (∑ c ∈ s,
        ‖quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ₑ) ≤
        s.card • (8 * M) := by
      exact s.sum_le_card_nsmul _ _ hterm
    _ ≤ 2 • (8 * M) := by
      have hor : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
      rcases hor with hzero | hone | htwo
      · simp [hzero]
      · rw [hone, one_nsmul]
        calc
          8 * M ≤ 8 * M + 8 * M := le_add_right le_rfl
          _ = 2 • (8 * M) := (two_nsmul (8 * M)).symm
      · simp [htwo]
    _ = 16 * centeredHardyLittlewoodMaximal
        (stoppingHilbertBadAtomNormSum f) x := by
      simp only [M, nsmul_eq_mul]
      ring

/-- Countable formulation of the boundary estimate. The defining `tsum`
is exactly the finite sum over the at-most-two boundary cells. -/
theorem stoppingBoundaryTruncationMajorant_le
    {f : ℝ → ℂ} (hf : Integrable f) {x ε : ℝ}
    (hx : x ∉ stoppingTripleBadUnion f) :
    stoppingBoundaryTruncationMajorant f x ε ≤
      16 * centeredHardyLittlewoodMaximal
        (stoppingHilbertBadAtomNormSum f) x := by
  classical
  let hfinite := (stoppingBoundaryCells_finite_and_ncard_le_two f
    (ε := ε) hx).1
  let s := hfinite.toFinset
  have hs (c : stoppingCell f) :
      c ∈ s ↔ c ∈ stoppingBoundaryCells f x ε := by
    exact hfinite.mem_toFinset
  have heq : stoppingBoundaryTruncationMajorant f x ε =
      ∑ c ∈ s,
        ‖quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ₑ := by
    rw [stoppingBoundaryTruncationMajorant, sum_eq_tsum_indicator]
    apply tsum_congr
    intro c
    by_cases hc : c ∈ stoppingBoundaryCells f x ε <;> simp [hs, hc]
  rw [heq]
  exact sum_enorm_zeroHilbertTruncation_boundaryStoppingAtoms_le hf hx s
    (fun c hc ↦ hs c |>.mp hc)

theorem zeroHilbertTruncation_stoppingAtom_eq_of_radius_lt
    {f : ℝ → ℂ} (c : stoppingCell f) {x ε : ℝ}
    (hε : ε < |x - stoppingCellCenter f c| - stoppingCellLength f c / 2) :
    quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x =
      ∫ y in centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c),
        ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y := by
  apply zeroHilbertTruncation_eq_ordinaryKernel_atom_of_radius_lt
    (z := stoppingCellCenter f c) (R := stoppingCellLength f c)
  · intro y hy
    rw [← stoppingCell_interval_eq_centeredInterval f c] at hy
    simp [stoppingHilbertBadAtom, hy]
  · exact hε

/-- Exact stopping-cell specialization of the nonboundary dichotomy. -/
theorem zeroHilbertTruncation_stoppingAtom_eq_zero_or_full_of_not_boundary
    {f : ℝ → ℂ} (c : stoppingCell f) {x ε : ℝ}
    (hc : c ∉ stoppingBoundaryCells f x ε) :
    quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x = 0 ∨
      quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x =
        ∫ y in centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c),
          ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y := by
  apply zeroHilbertTruncation_eq_zero_or_full_of_not_boundary
    (z := stoppingCellCenter f c) (R := stoppingCellLength f c)
  · intro y hy
    rw [← stoppingCell_interval_eq_centeredInterval f c] at hy
    simp [stoppingHilbertBadAtom, hy]
  · rw [← stoppingCell_interval_eq_centeredInterval f c]
    exact hc

/-- Global pointwise bad-part majorization outside the tripled stopping
exceptional set. Complete nonboundary cells are paid for by the
cancellation majorant, while the at-most-two boundary cells are paid for by
one Hardy--Littlewood maximal function. -/
theorem enorm_zeroHilbertTruncation_badPart_le_fullKernel_add_boundary
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {x ε : ℝ} (hε : 0 < ε) (hx : x ∉ stoppingTripleBadUnion f) :
    ‖quadraticHilbertTrunc 0 ε (fun y ↦ f y - stoppingGoodPart f y) x‖ₑ ≤
      stoppingFullKernelMajorant f x +
        16 * centeredHardyLittlewoodMaximal
          (stoppingHilbertBadAtomNormSum f) x := by
  classical
  rw [zeroHilbertTruncation_sub_stoppingGoodPart_eq_tsum hf hfi hε x]
  calc
    ‖∑' c : stoppingCell f,
        quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ₑ ≤
        ∑' c : stoppingCell f,
          ‖quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ₑ :=
      enorm_tsum_le_tsum_enorm
    _ ≤ ∑' c : stoppingCell f,
        (‖∫ y in centeredInterval (stoppingCellCenter f c)
            (stoppingCellLength f c),
          ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y‖ₑ +
        if c ∈ stoppingBoundaryCells f x ε then
          ‖quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x‖ₑ else 0) := by
      apply ENNReal.tsum_le_tsum
      intro c
      by_cases hc : c ∈ stoppingBoundaryCells f x ε
      · simp [hc]
      · rcases zeroHilbertTruncation_stoppingAtom_eq_zero_or_full_of_not_boundary
          c hc with hzero | hfull
        · simp [hc, hzero]
        · simp [hc, hfull]
    _ = stoppingFullKernelMajorant f x +
        stoppingBoundaryTruncationMajorant f x ε := by
      rw [ENNReal.tsum_add]
      rfl
    _ ≤ stoppingFullKernelMajorant f x +
        16 * centeredHardyLittlewoodMaximal
          (stoppingHilbertBadAtomNormSum f) x :=
      add_le_add le_rfl (stoppingBoundaryTruncationMajorant_le hfi hx)

/-- Off the tripled stopping cell, every truncation radius no larger than the
cell length misses the cell. Thus all such sharp truncations collapse to the
single full-kernel action controlled by cancellation. -/
theorem zeroHilbertTruncation_stoppingAtom_eq_of_le_length_of_notMem_triple
    {f : ℝ → ℂ} (c : stoppingCell f) {x ε : ℝ}
    (hx : x ∉ tripleCenteredInterval (stoppingCellCenter f c)
      (stoppingCellLength f c))
    (hε : ε ≤ stoppingCellLength f c) :
    quadraticHilbertTrunc 0 ε (stoppingHilbertBadAtom f c) x =
      ∫ y in centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c),
        ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y := by
  apply zeroHilbertTruncation_stoppingAtom_eq_of_radius_lt c
  have hxabs : 3 * stoppingCellLength f c / 2 <
      |x - stoppingCellCenter f c| :=
    not_mem_tripleCenteredInterval_abs hx
  linarith

/-- The part of one stopping atom's maximal truncation contributed by radii
no larger than its own cell length. -/
def stoppingAtomSmallRadiusMaximal (f : ℝ → ℂ) (c : stoppingCell f)
    (x : ℝ) : ℝ≥0∞ :=
  ⨆ ε : {ε : ℝ // 0 < ε ∧ ε ≤ stoppingCellLength f c},
    ‖quadraticHilbertTrunc 0 ε.1 (stoppingHilbertBadAtom f c) x‖ₑ

/-- Off the tripled cell, the entire small-radius supremum is exactly one
full-kernel value. In particular, no maximal-operator theorem is needed for
this portion of the bad atom. -/
theorem stoppingAtomSmallRadiusMaximal_eq_of_notMem_triple
    (f : ℝ → ℂ) (c : stoppingCell f) {x : ℝ}
    (hx : x ∉ tripleCenteredInterval (stoppingCellCenter f c)
      (stoppingCellLength f c)) :
    stoppingAtomSmallRadiusMaximal f c x =
      ‖∫ y in centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c),
        ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y‖ₑ := by
  let ε₀ : {ε : ℝ // 0 < ε ∧ ε ≤ stoppingCellLength f c} :=
    ⟨stoppingCellLength f c / 2,
      half_pos (stoppingCellLength_pos f c),
      half_le_self (stoppingCellLength_pos f c).le⟩
  apply le_antisymm
  · apply iSup_le
    intro ε
    rw [zeroHilbertTruncation_stoppingAtom_eq_of_le_length_of_notMem_triple
      c hx ε.2.2]
  · rw [← zeroHilbertTruncation_stoppingAtom_eq_of_le_length_of_notMem_triple
      c hx ε₀.2.2]
    unfold stoppingAtomSmallRadiusMaximal
    exact le_iSup (fun ε : {ε : ℝ // 0 < ε ∧ ε ≤ stoppingCellLength f c} ↦
      ‖quadraticHilbertTrunc 0 ε.1 (stoppingHilbertBadAtom f c) x‖ₑ) ε₀

/-- The canonical stopping atom satisfies the ordinary Hilbert off-support
estimate with a completely explicit constant. -/
theorem integral_norm_ordinaryHilbertKernel_stoppingAtom_le
    {f : ℝ → ℂ} (hf : Integrable f) (c : stoppingCell f) :
    ∫ x in (tripleCenteredInterval (stoppingCellCenter f c)
        (stoppingCellLength f c))ᶜ,
      ‖∫ y in centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c),
        ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y‖ ≤
      (32 / 3 : ℝ) * ∫ y in c.1.interval (rootLength f), ‖f y‖ := by
  have hcenter := stoppingCell_interval_eq_centeredInterval f c
  have hb := integrable_stoppingHilbertBadAtom hf c
  have hmeanGlobal := integral_stoppingHilbertBadAtom_eq_zero c
  have hmean : ∫ y in centeredInterval (stoppingCellCenter f c)
      (stoppingCellLength f c), stoppingHilbertBadAtom f c y = 0 := by
    rw [← hcenter]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hmeanGlobal
    · intro x hx
      simp [stoppingHilbertBadAtom, hx]
  calc
    _ ≤ (8 * 2 / 3 : ℝ) *
        ∫ y in centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c),
          ‖stoppingHilbertBadAtom f c y‖ :=
      integral_norm_ordinaryHilbertKernel_atom_le (stoppingHilbertBadAtom f c)
        (stoppingCellCenter f c) (stoppingCellLength f c)
        (stoppingCellLength_pos f c) (hb.integrableOn)
        hb.1 hmean
    _ ≤ (8 * 2 / 3 : ℝ) *
        (2 * ∫ y in c.1.interval (rootLength f), ‖f y‖) := by
      apply mul_le_mul_of_nonneg_left
      · rw [← hcenter]
        calc
          (∫ y in c.1.interval (rootLength f), ‖stoppingHilbertBadAtom f c y‖) ≤
              ∫ y, ‖stoppingHilbertBadAtom f c y‖ :=
            setIntegral_le_integral hb.norm (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
          _ ≤ _ := integral_norm_stoppingHilbertBadAtom_le hf c
      · norm_num
    _ = _ := by ring

/-- ENNReal version of the off-triple cancellation estimate for one stopping
atom. -/
theorem lintegral_enorm_ordinaryHilbertKernel_stoppingAtom_le
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (c : stoppingCell f) :
    (∫⁻ x in (tripleCenteredInterval (stoppingCellCenter f c)
        (stoppingCellLength f c))ᶜ,
      ‖∫ y in centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c),
        ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y‖ₑ) ≤
      ENNReal.ofReal (32 / 3) *
        ∫⁻ y in c.1.interval (rootLength f), ‖f y‖ₑ := by
  let E := (tripleCenteredInterval (stoppingCellCenter f c)
    (stoppingCellLength f c))ᶜ
  let G : ℝ → ℂ := fun x ↦ ∫ y in centeredInterval (stoppingCellCenter f c)
    (stoppingCellLength f c),
      ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y
  have hE : MeasurableSet E := measurableSet_Icc.compl
  have hG := integrableOn_stoppingFullKernelAction_compl_triple hf hfi c
  have hleft : (∫⁻ x in E, ‖G x‖ₑ) =
      ENNReal.ofReal (∫ x in E, ‖G x‖) := by
    symm
    simpa only [ofReal_norm] using
      ofReal_integral_eq_lintegral_ofReal hG.norm
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (G x))
  have hI := measurableSet_stoppingCell_interval c
  have hright : (∫⁻ y in c.1.interval (rootLength f), ‖f y‖ₑ) =
      ENNReal.ofReal (∫ y in c.1.interval (rootLength f), ‖f y‖) := by
    rw [← lintegral_indicator hI, ← integral_indicator hI]
    rw [ofReal_integral_eq_lintegral_ofReal
      (hfi.norm.indicator hI)
      (Filter.Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ c.1.interval (rootLength f) <;> simp [hx])]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ c.1.interval (rootLength f) <;> simp [hx]
  rw [hleft, hright, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal
    (integral_norm_ordinaryHilbertKernel_stoppingAtom_le hfi c)

theorem aemeasurable_stoppingFullKernelMajorant {f : ℝ → ℂ}
    (hf : Measurable f) : AEMeasurable (stoppingFullKernelMajorant f) := by
  let _ := Encodable.ofCountable (stoppingCell f)
  exact AEMeasurable.tsum fun c ↦
    (aestronglyMeasurable_stoppingFullKernelAction hf c).enorm

/-- The complete full-kernel majorant has the summed cancellation bound on
the complement of the global tripled stopping union. -/
theorem lintegral_stoppingFullKernelMajorant_compl_triple_le
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) :
    (∫⁻ x in (stoppingTripleBadUnion f)ᶜ, stoppingFullKernelMajorant f x) ≤
      ENNReal.ofReal (32 / 3) * ∫⁻ x, ‖f x‖ₑ := by
  let _ := Encodable.ofCountable (stoppingCell f)
  unfold stoppingFullKernelMajorant
  rw [lintegral_tsum (μ := volume.restrict (stoppingTripleBadUnion f)ᶜ)
    (fun c ↦ (aestronglyMeasurable_stoppingFullKernelAction hf c).enorm.restrict)]
  calc
    _ ≤ ∑' c : stoppingCell f,
        ENNReal.ofReal (32 / 3) *
          ∫⁻ y in c.1.interval (rootLength f), ‖f y‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply (lintegral_mono_set ?_).trans
        (lintegral_enorm_ordinaryHilbertKernel_stoppingAtom_le hf hfi c)
      exact compl_subset_compl.mpr (Set.subset_iUnion (fun c : stoppingCell f ↦
        tripleCenteredInterval (stoppingCellCenter f c) (stoppingCellLength f c)) c)
    _ = ENNReal.ofReal (32 / 3) * ∑' c : stoppingCell f,
          ∫⁻ y in c.1.interval (rootLength f), ‖f y‖ₑ := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (32 / 3) *
        ∫⁻ y in stoppingBadUnion f, ‖f y‖ₑ := by
      rw [stoppingBadUnion, lintegral_iUnion
        (fun c : stoppingCell f ↦ measurableSet_stoppingCell_interval c)
        stoppingCell_pairwiseDisjoint]
    _ ≤ ENNReal.ofReal (32 / 3) * ∫⁻ y, ‖f y‖ₑ :=
      mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- Markov's inequality applied to the summed full-kernel cancellation
majorant outside the global exceptional set. -/
theorem stoppingFullKernelMajorant_weak_bound
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (a : ℝ≥0∞) :
    a * volume {x | x ∉ stoppingTripleBadUnion f ∧
      a < stoppingFullKernelMajorant f x} ≤
      ENNReal.ofReal (32 / 3) * ∫⁻ x, ‖f x‖ₑ := by
  let E := (stoppingTripleBadUnion f)ᶜ
  have hE : MeasurableSet E := (measurableSet_stoppingTripleBadUnion f).compl
  let G := E.indicator (stoppingFullKernelMajorant f)
  have hG : AEMeasurable G :=
    (aemeasurable_stoppingFullKernelMajorant hf).indicator hE
  have hsub : {x | x ∉ stoppingTripleBadUnion f ∧
      a < stoppingFullKernelMajorant f x} ⊆ {x | a ≤ G x} := by
    intro x hx
    change a ≤ E.indicator (stoppingFullKernelMajorant f) x
    rw [indicator_of_mem (mem_compl hx.1)]
    exact hx.2.le
  calc
    _ ≤ a * volume {x | a ≤ G x} := mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ ∫⁻ x, G x := mul_meas_ge_le_lintegral₀ hG a
    _ = ∫⁻ x in E, stoppingFullKernelMajorant f x := by
      change (∫⁻ x, E.indicator (stoppingFullKernelMajorant f) x) = _
      rw [lintegral_indicator hE]
    _ ≤ _ := lintegral_stoppingFullKernelMajorant_compl_triple_le hf hfi

/-- Uniform pointwise bad-part estimate after taking the supremum over every
positive sharp truncation radius. -/
theorem quadraticHilbertMaximalTruncation_badPart_le
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) {x : ℝ}
    (hx : x ∉ stoppingTripleBadUnion f) :
    quadraticHilbertMaximalTruncation 0
        (fun y ↦ f y - stoppingGoodPart f y) x ≤
      stoppingFullKernelMajorant f x +
        16 * centeredHardyLittlewoodMaximal
          (stoppingHilbertBadAtomNormSum f) x := by
  unfold quadraticHilbertMaximalTruncation
  apply iSup_le
  intro ε
  exact enorm_zeroHilbertTruncation_badPart_le_fullKernel_add_boundary
    hf hfi ε.2 hx

/-- The complete stopping bad part satisfies a genuine uniform weak
`(1,1)` estimate outside the tripled stopping intervals. The threshold is
scaled as `32a`: `16a` is assigned to each of the full-kernel and boundary
majorants. -/
theorem quadraticHilbertMaximalTruncation_badPart_weak_bound
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (a : ℝ≥0∞) :
    (32 * a) * volume {x | x ∉ stoppingTripleBadUnion f ∧
      32 * a < quadraticHilbertMaximalTruncation 0
      (fun y ↦ f y - stoppingGoodPart f y) x} ≤
      2 * (ENNReal.ofReal (32 / 3) * (∫⁻ x, ‖f x‖ₑ) +
        128 * (∫⁻ x, ‖f x‖ₑ)) := by
  let F := stoppingFullKernelMajorant f
  let B : ℝ → ℝ≥0∞ := fun x ↦ 16 * centeredHardyLittlewoodMaximal
    (stoppingHilbertBadAtomNormSum f) x
  let S := {x | x ∉ stoppingTripleBadUnion f ∧
    32 * a < quadraticHilbertMaximalTruncation 0
      (fun y ↦ f y - stoppingGoodPart f y) x}
  let SF := {x | x ∉ stoppingTripleBadUnion f ∧ 16 * a < F x}
  let SB := {x | 16 * a < B x}
  have hsub : S ⊆ SF ∪ SB := by
    intro x hx
    have hmaj := quadraticHilbertMaximalTruncation_badPart_le hf hfi hx.1
    by_cases hF : 16 * a < F x
    · exact Or.inl ⟨hx.1, hF⟩
    · apply Or.inr
      have hFle : F x ≤ 16 * a := le_of_not_gt hF
      by_contra hB
      have hBle : B x ≤ 16 * a := le_of_not_gt hB
      have : quadraticHilbertMaximalTruncation 0
          (fun y ↦ f y - stoppingGoodPart f y) x ≤ 32 * a := by
        calc
          _ ≤ F x + B x := hmaj
          _ ≤ 16 * a + 16 * a := add_le_add hFle hBle
          _ = 32 * a := by ring
      exact (not_lt_of_ge this) hx.2
  have hfull := stoppingFullKernelMajorant_weak_bound hf hfi (16 * a)
  have hboundary := stoppingHilbertBadAtomNormSum_boundaryMaximal_weak_bound hfi a
  have hfull' : (16 * a) * volume SF ≤
      ENNReal.ofReal (32 / 3) * (∫⁻ x, ‖f x‖ₑ) := by
    simpa only [SF, F] using hfull
  have hboundary' : (16 * a) * volume SB ≤
      128 * (∫⁻ x, ‖f x‖ₑ) := by
    simpa only [SB, B] using hboundary
  calc
    (32 * a) * volume S ≤ (32 * a) * volume (SF ∪ SB) :=
      mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ (32 * a) * (volume SF + volume SB) :=
      mul_le_mul' le_rfl (measure_union_le SF SB)
    _ = 2 * ((16 * a) * volume SF + (16 * a) * volume SB) := by ring
    _ ≤ 2 * (ENNReal.ofReal (32 / 3) * (∫⁻ x, ‖f x‖ₑ) +
        128 * (∫⁻ x, ‖f x‖ₑ)) := by
      apply mul_le_mul' le_rfl
      calc
        (16 * a) * volume SF + (16 * a) * volume SB ≤
            ENNReal.ofReal (32 / 3) * (∫⁻ x, ‖f x‖ₑ) +
              (16 * a) * volume SB := add_le_add_left hfull' ((16 * a) * volume SB)
        _ ≤ ENNReal.ofReal (32 / 3) * (∫⁻ x, ‖f x‖ₑ) +
            128 * (∫⁻ x, ‖f x‖ₑ) :=
          add_le_add_right hboundary'
            (ENNReal.ofReal (32 / 3) * (∫⁻ x, ‖f x‖ₑ))

/-- At the normalization height of the stopping decomposition, the bad-part
weak estimate holds on all of `ℝ`. The first term pays for the tripled
stopping intervals and the second is the off-triple cancellation estimate. -/
theorem quadraticHilbertMaximalTruncation_badPart_weak_bound_one
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) :
    32 * volume {x | 32 < quadraticHilbertMaximalTruncation 0
        (fun y ↦ f y - stoppingGoodPart f y) x} ≤
      96 * (∫⁻ x, ‖f x‖ₑ) +
        2 * (ENNReal.ofReal (32 / 3) * (∫⁻ x, ‖f x‖ₑ) +
          128 * (∫⁻ x, ‖f x‖ₑ)) := by
  let S := {x | 32 < quadraticHilbertMaximalTruncation 0
    (fun y ↦ f y - stoppingGoodPart f y) x}
  let SO := {x | x ∉ stoppingTripleBadUnion f ∧
    32 < quadraticHilbertMaximalTruncation 0
      (fun y ↦ f y - stoppingGoodPart f y) x}
  have hsub : S ⊆ stoppingTripleBadUnion f ∪ SO := by
    intro x hx
    by_cases hU : x ∈ stoppingTripleBadUnion f
    · exact Or.inl hU
    · exact Or.inr ⟨hU, hx⟩
  have htriple : 32 * volume (stoppingTripleBadUnion f) ≤
      96 * (∫⁻ x, ‖f x‖ₑ) := by
    calc
      _ ≤ 32 * (3 * (∫⁻ x, ‖f x‖ₑ)) :=
        mul_le_mul' le_rfl (by
          simpa only [ofReal_norm] using
            volume_stoppingTripleBadUnion_le_lintegral_norm hfi)
      _ = _ := by ring
  have hoff : 32 * volume SO ≤
      2 * (ENNReal.ofReal (32 / 3) * (∫⁻ x, ‖f x‖ₑ) +
        128 * (∫⁻ x, ‖f x‖ₑ)) := by
    simpa only [SO, mul_one] using
      quadraticHilbertMaximalTruncation_badPart_weak_bound hf hfi 1
  calc
    32 * volume S ≤ 32 * volume (stoppingTripleBadUnion f ∪ SO) :=
      mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ 32 * (volume (stoppingTripleBadUnion f) + volume SO) :=
      mul_le_mul' le_rfl (measure_union_le _ _)
    _ = 32 * volume (stoppingTripleBadUnion f) + 32 * volume SO := by ring
    _ ≤ _ := add_le_add htriple hoff

/-! ## Fourier `L²` input for the good-part Cotlar argument -/

/-- The stopping good part belongs to `L²`; this is the exact input space
of the Fourier realization of the ordinary Hilbert transform. -/
theorem memLp_two_stoppingGoodPart {f : ℝ → ℂ} (hf : Integrable f) :
    MemLp (stoppingGoodPart f) 2 :=
  (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_stoppingGoodPart hf)).mpr
      (integrable_sq_norm_stoppingGoodPart hf)

/-- The stopping good part as an element of `L²`. -/
noncomputable def stoppingGoodPartL2 (f : ℝ → ℂ) (hf : Integrable f) :
    Lp (α := ℝ) ℂ 2 volume :=
  MemLp.toLp (stoppingGoodPart f) (memLp_two_stoppingGoodPart hf)

/-- The canonical pointwise representative of the Fourier-side Hilbert
transform of the stopping good part. -/
noncomputable def stoppingGoodHilbertL2Representative
    (f : ℝ → ℂ) (hf : Integrable f) : ℝ → ℂ :=
  ⇑(ordinaryHilbertTransformL2 (stoppingGoodPartL2 f hf))

theorem aestronglyMeasurable_stoppingGoodHilbertL2Representative
    {f : ℝ → ℂ} (hf : Integrable f) :
    AEStronglyMeasurable (stoppingGoodHilbertL2Representative f hf) := by
  change AEStronglyMeasurable
    (⇑(ordinaryHilbertTransformL2 (stoppingGoodPartL2 f hf)) : ℝ → ℂ)
  exact (Lp.memLp (ordinaryHilbertTransformL2 (stoppingGoodPartL2 f hf))).aestronglyMeasurable

/-- The Fourier Hilbert transform of the stopping good part has the sharp
operator-norm bound. A Cotlar inequality relating the sharp truncations to
this representative is the remaining maximal-`L²` bridge. -/
theorem norm_stoppingGoodHilbertL2_le
    {f : ℝ → ℂ} (hf : Integrable f) :
    ‖ordinaryHilbertTransformL2 (stoppingGoodPartL2 f hf)‖ ≤
      Real.pi * ‖stoppingGoodPartL2 f hf‖ :=
  norm_ordinaryHilbertTransformL2_le (stoppingGoodPartL2 f hf)

theorem eLpNorm_stoppingGoodHilbertL2Representative_eq_enorm
    {f : ℝ → ℂ} (hf : Integrable f) :
    eLpNorm (stoppingGoodHilbertL2Representative f hf) 2 =
      ‖ordinaryHilbertTransformL2 (stoppingGoodPartL2 f hf)‖ₑ := by
  change eLpNorm
    (⇑(ordinaryHilbertTransformL2 (stoppingGoodPartL2 f hf)) : ℝ → ℂ) 2 = _
  exact (Lp.enorm_def
    (ordinaryHilbertTransformL2 (stoppingGoodPartL2 f hf))).symm

theorem enorm_stoppingGoodPartL2_sq_eq_lintegral
    {f : ℝ → ℂ} (hf : Integrable f) :
    ‖stoppingGoodPartL2 f hf‖ₑ ^ 2 =
      ∫⁻ x, ‖stoppingGoodPart f x‖ₑ ^ 2 := by
  unfold stoppingGoodPartL2
  rw [Lp.enorm_toLp (memLp_two_stoppingGoodPart hf),
    eLpNorm_two_sq_lintegral _ (memLp_two_stoppingGoodPart hf).aestronglyMeasurable]

theorem enorm_stoppingGoodHilbertL2_le
    {f : ℝ → ℂ} (hf : Integrable f) :
    ‖ordinaryHilbertTransformL2 (stoppingGoodPartL2 f hf)‖ₑ ≤
      ENNReal.ofReal Real.pi * ‖stoppingGoodPartL2 f hf‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul Real.pi_pos.le]
  exact ENNReal.ofReal_le_ofReal (norm_stoppingGoodHilbertL2_le hf)

/-! ## Scalar Poisson-kernel algebra for Cotlar -/

/-- The real sharp Hilbert kernel at radius `r`. -/
def cotlarSharpHilbertKernel (r t : ℝ) : ℝ :=
  if r < |t| then 1 / t else 0

/-- The conjugate Poisson kernel, without its harmless normalization factor. -/
def cotlarConjugatePoissonKernel (r t : ℝ) : ℝ :=
  t / (t ^ 2 + r ^ 2)

theorem cotlarSharpHilbertKernel_eq_zero_of_abs_le {r t : ℝ}
    (ht : |t| ≤ r) : cotlarSharpHilbertKernel r t = 0 := by
  simp [cotlarSharpHilbertKernel, not_lt.mpr ht]

/-- Off the truncation ball the sharp kernel differs from the conjugate
Poisson kernel by the explicit cubic-decay error. -/
theorem cotlarSharp_sub_conjugatePoisson_eq {r t : ℝ}
    (hr : 0 ≤ r) (ht : r < |t|) :
    cotlarSharpHilbertKernel r t - cotlarConjugatePoissonKernel r t =
      r ^ 2 / (t * (t ^ 2 + r ^ 2)) := by
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    simp at ht
    linarith
  simp only [cotlarSharpHilbertKernel, cotlarConjugatePoissonKernel, ht, ↓reduceIte]
  field_simp
  ring

/-- The off-ball Poisson comparison error has cubic decay. -/
theorem abs_cotlarSharp_sub_conjugatePoisson_le {r t : ℝ}
    (hr : 0 ≤ r) (ht : r < |t|) :
    |cotlarSharpHilbertKernel r t - cotlarConjugatePoissonKernel r t| ≤
      r ^ 2 / |t| ^ 3 := by
  have htpos : 0 < |t| := lt_of_le_of_lt hr ht
  rw [cotlarSharp_sub_conjugatePoisson_eq hr ht, abs_div, abs_mul,
    abs_of_nonneg (sq_nonneg r), abs_of_nonneg
      (add_nonneg (sq_nonneg t) (sq_nonneg r))]
  apply div_le_div_of_nonneg_left (sq_nonneg r) (pow_pos htpos 3)
  nlinarith [abs_nonneg t, sq_nonneg r, sq_abs t]

/-- On the deleted ball the conjugate Poisson kernel has the natural
`1/r` size. -/
theorem abs_cotlarConjugatePoissonKernel_le_inv {r t : ℝ}
    (hr : 0 < r) (ht : |t| ≤ r) :
    |cotlarConjugatePoissonKernel r t| ≤ 1 / r := by
  have hden : 0 < t ^ 2 + r ^ 2 := by positivity
  rw [cotlarConjugatePoissonKernel, abs_div,
    abs_of_nonneg hden.le, div_le_div_iff₀ hden hr]
  nlinarith [sq_nonneg t, sq_abs t]

/-- A positive radial majorant for the sharp-to-Poisson comparison error. -/
def cotlarPoissonErrorMajorant (r t : ℝ) : ℝ :=
  if |t| ≤ r then 1 / r else r ^ 2 / |t| ^ 3

theorem abs_cotlarSharp_sub_conjugatePoisson_le_majorant {r t : ℝ}
    (hr : 0 < r) :
    |cotlarSharpHilbertKernel r t - cotlarConjugatePoissonKernel r t| ≤
      cotlarPoissonErrorMajorant r t := by
  by_cases ht : |t| ≤ r
  · rw [cotlarSharpHilbertKernel_eq_zero_of_abs_le ht]
    simp only [zero_sub, abs_neg, cotlarPoissonErrorMajorant, ht, ↓reduceIte]
    exact abs_cotlarConjugatePoissonKernel_le_inv hr ht
  · have htr : r < |t| := lt_of_not_ge ht
    simp only [cotlarPoissonErrorMajorant, ht, ↓reduceIte]
    exact abs_cotlarSharp_sub_conjugatePoisson_le hr.le htr

theorem cotlarPoissonErrorMajorant_nonneg {r t : ℝ} (hr : 0 ≤ r) :
    0 ≤ cotlarPoissonErrorMajorant r t := by
  unfold cotlarPoissonErrorMajorant
  split_ifs
  · positivity
  · positivity

theorem measurable_cotlarPoissonErrorMajorant (r : ℝ) :
    Measurable (cotlarPoissonErrorMajorant r) := by
  unfold cotlarPoissonErrorMajorant
  apply Measurable.ite
  · exact measurableSet_le measurable_norm measurable_const
  · exact measurable_const
  · exact measurable_const.div (measurable_norm.pow_const 3)

theorem measurable_cotlarConjugatePoissonKernel (r : ℝ) :
    Measurable (cotlarConjugatePoissonKernel r) := by
  unfold cotlarConjugatePoissonKernel
  exact measurable_id.div (measurable_id.pow_const 2 |>.add measurable_const)

/-- The positive (unnormalized) Poisson kernel. Its integral is `π`; keeping
this normalization makes the Fourier multiplier comparison with
`ordinaryHilbertTransformL2` transparent. -/
def cotlarPoissonKernel (r t : ℝ) : ℝ :=
  r / (t ^ 2 + r ^ 2)

theorem cotlarPoissonKernel_nonneg {r t : ℝ} (hr : 0 ≤ r) :
    0 ≤ cotlarPoissonKernel r t := by
  unfold cotlarPoissonKernel
  positivity

theorem measurable_cotlarPoissonKernel (r : ℝ) :
    Measurable (cotlarPoissonKernel r) := by
  unfold cotlarPoissonKernel
  exact measurable_const.div (measurable_id.pow_const 2 |>.add measurable_const)

/-- Every point outside the ball of radius `r` lies in a dyadic shell. -/
theorem exists_nat_dyadic_shell {r t : ℝ} (hr : 0 < r) (ht : r < |t|) :
    ∃ n : ℕ, (2 : ℝ) ^ n * r ≤ |t| ∧ |t| < (2 : ℝ) ^ (n + 1) * r := by
  have hratio : 1 ≤ |t| / r := by
    apply (le_div_iff₀ hr).2
    simpa only [one_mul] using ht.le
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, ?_, ?_⟩
  · exact (le_div_iff₀ hr).1 hn
  · exact (div_lt_iff₀ hr).1 hn'

/-- On a dyadic shell the Poisson kernel has the expected quadratic decay. -/
theorem cotlarPoissonKernel_le_dyadic_shell {r t : ℝ} (hr : 0 < r)
    {n : ℕ} (hn : (2 : ℝ) ^ n * r ≤ |t|) :
    cotlarPoissonKernel r t ≤ (1 / 4 : ℝ) ^ n / r := by
  have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have ht0 : 0 < |t| := lt_of_lt_of_le (mul_pos hpow hr) hn
  have hsquare : ((2 : ℝ) ^ n * r) ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]
    exact (sq_le_sq₀ (mul_nonneg hpow.le hr.le) (abs_nonneg t)).2 hn
  have hfour : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    calc
      (4 : ℝ) ^ n = ((2 : ℝ) * 2) ^ n := by norm_num
      _ = (2 : ℝ) ^ n * 2 ^ n := mul_pow 2 2 n
      _ = ((2 : ℝ) ^ n) ^ 2 := by ring
  calc
    cotlarPoissonKernel r t = r / (t ^ 2 + r ^ 2) := rfl
    _ ≤ r / (((2 : ℝ) ^ n * r) ^ 2) := by
      exact div_le_div_of_nonneg_left hr.le (by positivity)
        (by nlinarith [sq_nonneg r])
    _ = 1 / ((4 : ℝ) ^ n * r) := by
      rw [mul_pow, ← hfour]
      field_simp
    _ = (1 / 4 : ℝ) ^ n / r := by
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

/-- On the same shell the sharp-to-conjugate-Poisson error has cubic decay. -/
theorem cotlarPoissonErrorMajorant_le_dyadic_shell {r t : ℝ} (hr : 0 < r)
    (ht : r < |t|) {n : ℕ} (hn : (2 : ℝ) ^ n * r ≤ |t|) :
    cotlarPoissonErrorMajorant r t ≤ (1 / 8 : ℝ) ^ n / r := by
  have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have ht0 : 0 < |t| := lt_of_lt_of_le (mul_pos hpow hr) hn
  rw [cotlarPoissonErrorMajorant, ite_eq_right (not_le.mpr ht)]
  have hcube : ((2 : ℝ) ^ n * r) ^ 3 ≤ |t| ^ 3 := by
    exact pow_le_pow_left₀ (mul_nonneg hpow.le hr.le) hn 3
  have height : (8 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 3 := by
    calc
      (8 : ℝ) ^ n = (((2 : ℝ) * 2) * 2) ^ n := by norm_num
      _ = ((2 : ℝ) * 2) ^ n * 2 ^ n := mul_pow (2 * 2) 2 n
      _ = ((2 : ℝ) ^ n * 2 ^ n) * 2 ^ n := by rw [mul_pow]
      _ = ((2 : ℝ) ^ n) ^ 3 := by ring
  calc
    r ^ 2 / |t| ^ 3 ≤ r ^ 2 / (((2 : ℝ) ^ n * r) ^ 3) := by
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hcube
    _ = 1 / ((8 : ℝ) ^ n * r) := by
      rw [mul_pow, ← height]
      field_simp
    _ = (1 / 8 : ℝ) ^ n / r := by
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

/-- Sum of successively larger dyadic-ball majorants with geometric weights. -/
noncomputable def cotlarDyadicBallSeries (q : ℝ) (r t : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, if |t| ≤ (2 : ℝ) ^ (n + 1) * r
    then ENNReal.ofReal (q ^ n / r) else 0

theorem measurable_cotlarDyadicBallSeries (q r : ℝ) :
    Measurable (cotlarDyadicBallSeries q r) := by
  unfold cotlarDyadicBallSeries
  apply Measurable.tsum
  intro n
  apply Measurable.ite
  · exact measurableSet_le measurable_norm measurable_const
  · exact measurable_const
  · exact measurable_const

/-- Outside its central ball, the Poisson kernel is bounded by the dyadic
ball series with ratio `1/4`. -/
theorem ofReal_cotlarPoissonKernel_le_dyadicBallSeries {r t : ℝ}
    (hr : 0 < r) (ht : r < |t|) :
    ENNReal.ofReal (cotlarPoissonKernel r t) ≤
      cotlarDyadicBallSeries (1 / 4) r t := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_dyadic_shell hr ht
  have hterm : ENNReal.ofReal (cotlarPoissonKernel r t) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ n / r) :=
    ENNReal.ofReal_le_ofReal (cotlarPoissonKernel_le_dyadic_shell hr hn)
  exact hterm.trans (by
    unfold cotlarDyadicBallSeries
    have hone : ENNReal.ofReal ((1 / 4 : ℝ) ^ n / r) =
        (if |t| ≤ (2 : ℝ) ^ (n + 1) * r
          then ENNReal.ofReal ((1 / 4 : ℝ) ^ n / r) else 0) := by
      simp [hn'.le]
    rw [hone]
    exact ENNReal.le_tsum (f := fun k : ℕ ↦ if |t| ≤ (2 : ℝ) ^ (k + 1) * r
      then ENNReal.ofReal ((1 / 4 : ℝ) ^ k / r) else 0) n)

/-- Outside its central ball, the sharp-to-Poisson error is bounded by the
faster dyadic ball series with ratio `1/8`. -/
theorem ofReal_cotlarPoissonErrorMajorant_le_dyadicBallSeries {r t : ℝ}
    (hr : 0 < r) (ht : r < |t|) :
    ENNReal.ofReal (cotlarPoissonErrorMajorant r t) ≤
      cotlarDyadicBallSeries (1 / 8) r t := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_dyadic_shell hr ht
  have hterm : ENNReal.ofReal (cotlarPoissonErrorMajorant r t) ≤
      ENNReal.ofReal ((1 / 8 : ℝ) ^ n / r) :=
    ENNReal.ofReal_le_ofReal
      (cotlarPoissonErrorMajorant_le_dyadic_shell hr ht hn)
  exact hterm.trans (by
    unfold cotlarDyadicBallSeries
    have hone : ENNReal.ofReal ((1 / 8 : ℝ) ^ n / r) =
        (if |t| ≤ (2 : ℝ) ^ (n + 1) * r
          then ENNReal.ofReal ((1 / 8 : ℝ) ^ n / r) else 0) := by
      simp [hn'.le]
    rw [hone]
    exact ENNReal.le_tsum (f := fun k : ℕ ↦ if |t| ≤ (2 : ℝ) ^ (k + 1) * r
      then ENNReal.ofReal ((1 / 8 : ℝ) ^ k / r) else 0) n)

/-- A constant multiple of the mass of a centered ball is controlled by the
centered Hardy--Littlewood maximal function, uniformly in its real radius. -/
theorem ofReal_div_mul_lintegral_closedBall_le_maximal
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ) (G : ℝ → ℝ≥0∞) (x : ℝ) :
    ENNReal.ofReal (C / ρ) * (∫⁻ y in Metric.closedBall x ρ, G y) ≤
      ENNReal.ofReal (4 * C) * centeredHardyLittlewoodMaximal G x := by
  have hden : ENNReal.ofReal (2 * ρ) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hmass : (∫⁻ y in Metric.closedBall x ρ, G y) =
      ENNReal.ofReal (2 * ρ) * centeredAverage ρ G x := by
    unfold centeredAverage
    rw [mul_comm]
    exact (ENNReal.div_mul_cancel hden ENNReal.ofReal_ne_top).symm
  calc
    ENNReal.ofReal (C / ρ) * (∫⁻ y in Metric.closedBall x ρ, G y) =
        ENNReal.ofReal (2 * C) * centeredAverage ρ G x := by
      rw [hmass, ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hC hρ.le)]
      congr 2
      field_simp
    _ ≤ ENNReal.ofReal (2 * C) *
        (2 * centeredHardyLittlewoodMaximal G x) :=
      mul_le_mul' le_rfl
        (centeredAverage_le_two_mul_centeredHardyLittlewoodMaximal hρ G x)
    _ = ENNReal.ofReal (4 * C) * centeredHardyLittlewoodMaximal G x := by
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * C)]
      congr 2
      ring

/-- Integrating the dyadic ball series against a measurable nonnegative
function is controlled by the centered maximal operator. The coefficient
series is displayed explicitly so that the two geometric ratios needed for
Cotlar can be evaluated separately. -/
theorem lintegral_cotlarDyadicBallSeries_mul_le_maximal
    {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) {G : ℝ → ℝ≥0∞}
    (hG : Measurable G) (x : ℝ) :
    (∫⁻ y, cotlarDyadicBallSeries q r (x - y) * G y) ≤
      (∑' n : ℕ, ENNReal.ofReal
        (4 * ((2 : ℝ) ^ (n + 1) * q ^ n))) *
          centeredHardyLittlewoodMaximal G x := by
  rw [show (fun y ↦ cotlarDyadicBallSeries q r (x - y) * G y) =
      (fun y ↦ ∑' n : ℕ,
        (if |x - y| ≤ (2 : ℝ) ^ (n + 1) * r
          then ENNReal.ofReal (q ^ n / r) else 0) * G y) by
    funext y
    unfold cotlarDyadicBallSeries
    exact ENNReal.tsum_mul_right.symm]
  rw [lintegral_tsum]
  · calc
      (∑' n : ℕ, ∫⁻ y,
          (if |x - y| ≤ (2 : ℝ) ^ (n + 1) * r
            then ENNReal.ofReal (q ^ n / r) else 0) * G y) ≤
          ∑' n : ℕ, ENNReal.ofReal
            (4 * ((2 : ℝ) ^ (n + 1) * q ^ n)) *
              centeredHardyLittlewoodMaximal G x := by
        apply ENNReal.tsum_le_tsum
        intro n
        let ρn : ℝ := (2 : ℝ) ^ (n + 1) * r
        let Cn : ℝ := (2 : ℝ) ^ (n + 1) * q ^ n
        have hρn : 0 < ρn := mul_pos (pow_pos (by norm_num) _) hr
        have hCn : 0 ≤ Cn := mul_nonneg (pow_nonneg (by norm_num) _)
          (pow_nonneg hq _)
        have hcoeff : Cn / ρn = q ^ n / r := by
          dsimp only [Cn, ρn]
          field_simp
        calc
          (∫⁻ y, (if |x - y| ≤ (2 : ℝ) ^ (n + 1) * r
              then ENNReal.ofReal (q ^ n / r) else 0) * G y) =
              ENNReal.ofReal (q ^ n / r) *
                (∫⁻ y in Metric.closedBall x ρn, G y) := by
            rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
            have hfun : (fun y : ℝ ↦
                (if |x - y| ≤ (2 : ℝ) ^ (n + 1) * r
                  then ENNReal.ofReal (q ^ n / r) else 0) * G y) =
                (fun y ↦ ENNReal.ofReal (q ^ n / r) *
                  (Metric.closedBall x ρn).indicator G y) := by
              funext y
              by_cases hy : y ∈ Metric.closedBall x ρn
              · have habs : |x - y| ≤ (2 : ℝ) ^ (n + 1) * r := by
                  simpa only [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm, ρn] using hy
                simp [hy, habs]
              · have habs : ¬ |x - y| ≤ (2 : ℝ) ^ (n + 1) * r := by
                  simpa only [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm, ρn] using hy
                simp [hy, habs]
            rw [hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          _ = ENNReal.ofReal (Cn / ρn) *
                (∫⁻ y in Metric.closedBall x ρn, G y) := by rw [hcoeff]
          _ ≤ ENNReal.ofReal (4 * Cn) * centeredHardyLittlewoodMaximal G x :=
            ofReal_div_mul_lintegral_closedBall_le_maximal hCn hρn G x
          _ = ENNReal.ofReal (4 * ((2 : ℝ) ^ (n + 1) * q ^ n)) *
                centeredHardyLittlewoodMaximal G x := rfl
      _ = (∑' n : ℕ, ENNReal.ofReal
          (4 * ((2 : ℝ) ^ (n + 1) * q ^ n))) *
            centeredHardyLittlewoodMaximal G x := ENNReal.tsum_mul_right
  · intro n
    apply AEMeasurable.mul
    · exact (Measurable.ite
        (measurableSet_le
          (by fun_prop) measurable_const)
        measurable_const measurable_const).aemeasurable
    · exact hG.aemeasurable

theorem lintegral_cotlarDyadicBallSeries_quarter_le_maximal
    {r : ℝ} (hr : 0 < r) {G : ℝ → ℝ≥0∞} (hG : Measurable G) (x : ℝ) :
    (∫⁻ y, cotlarDyadicBallSeries (1 / 4) r (x - y) * G y) ≤
      16 * centeredHardyLittlewoodMaximal G x := by
  have h := lintegral_cotlarDyadicBallSeries_mul_le_maximal
    (q := (1 / 4 : ℝ)) (by norm_num) hr hG x
  have hcoef (n : ℕ) :
      4 * ((2 : ℝ) ^ (n + 1) * (1 / 4 : ℝ) ^ n) =
        8 * (1 / 2 : ℝ) ^ n := by
    calc
      4 * ((2 : ℝ) ^ (n + 1) * (1 / 4 : ℝ) ^ n) =
          8 * ((2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := by
            rw [pow_succ]
            ring
      _ = 8 * ((2 : ℝ) * (1 / 4 : ℝ)) ^ n := by rw [mul_pow]
      _ = 8 * (1 / 2 : ℝ) ^ n := by norm_num
  have hsum : (∑' n : ℕ, ENNReal.ofReal
      (4 * ((2 : ℝ) ^ (n + 1) * (1 / 4 : ℝ) ^ n))) = 16 := by
    simp_rw [hcoef]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 8)]
    rw [tsum_mul_left, tsum_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)]
    norm_num
  simpa only [hsum] using h

theorem lintegral_cotlarDyadicBallSeries_eighth_le_maximal
    {r : ℝ} (hr : 0 < r) {G : ℝ → ℝ≥0∞} (hG : Measurable G) (x : ℝ) :
    (∫⁻ y, cotlarDyadicBallSeries (1 / 8) r (x - y) * G y) ≤
      ENNReal.ofReal (32 / 3) * centeredHardyLittlewoodMaximal G x := by
  have h := lintegral_cotlarDyadicBallSeries_mul_le_maximal
    (q := (1 / 8 : ℝ)) (by norm_num) hr hG x
  have hcoef (n : ℕ) :
      4 * ((2 : ℝ) ^ (n + 1) * (1 / 8 : ℝ) ^ n) =
        8 * (1 / 4 : ℝ) ^ n := by
    calc
      4 * ((2 : ℝ) ^ (n + 1) * (1 / 8 : ℝ) ^ n) =
          8 * ((2 : ℝ) ^ n * (1 / 8 : ℝ) ^ n) := by
            rw [pow_succ]
            ring
      _ = 8 * ((2 : ℝ) * (1 / 8 : ℝ)) ^ n := by rw [mul_pow]
      _ = 8 * (1 / 4 : ℝ) ^ n := by norm_num
  have hsum : (∑' n : ℕ, ENNReal.ofReal
      (4 * ((2 : ℝ) ^ (n + 1) * (1 / 8 : ℝ) ^ n))) =
        ENNReal.ofReal (32 / 3) := by
    simp_rw [hcoef]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).mul_left 8)]
    rw [tsum_mul_left, tsum_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)]
    norm_num
  simpa only [hsum] using h

/-- The central `1/r` ball occurring in both radial kernel estimates. -/
def cotlarCentralBallMajorant (r t : ℝ) : ℝ≥0∞ :=
  if |t| ≤ r then ENNReal.ofReal (1 / r) else 0

theorem measurable_cotlarCentralBallMajorant (r : ℝ) :
    Measurable (cotlarCentralBallMajorant r) := by
  unfold cotlarCentralBallMajorant
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
    measurable_const measurable_const

theorem lintegral_cotlarCentralBallMajorant_mul_le_maximal
    {r : ℝ} (hr : 0 < r) {G : ℝ → ℝ≥0∞} (_hG : Measurable G) (x : ℝ) :
    (∫⁻ y, cotlarCentralBallMajorant r (x - y) * G y) ≤
      4 * centeredHardyLittlewoodMaximal G x := by
  have heq : (∫⁻ y, cotlarCentralBallMajorant r (x - y) * G y) =
      ENNReal.ofReal (1 / r) * (∫⁻ y in Metric.closedBall x r, G y) := by
    rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
    have hfun : (fun y : ℝ ↦ cotlarCentralBallMajorant r (x - y) * G y) =
        (fun y ↦ ENNReal.ofReal (1 / r) *
          (Metric.closedBall x r).indicator G y) := by
      funext y
      by_cases hy : y ∈ Metric.closedBall x r
      · have habs : |x - y| ≤ r := by
          simpa only [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using hy
        simp [cotlarCentralBallMajorant, hy, habs]
      · have habs : ¬ |x - y| ≤ r := by
          simpa only [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using hy
        simp [cotlarCentralBallMajorant, hy, habs]
    rw [hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [heq]
  convert ofReal_div_mul_lintegral_closedBall_le_maximal
      (C := (1 : ℝ)) (ρ := r) (by norm_num) hr G x using 1; norm_num

theorem ofReal_cotlarPoissonKernel_le_radialMajorant {r t : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (cotlarPoissonKernel r t) ≤
      cotlarCentralBallMajorant r t + cotlarDyadicBallSeries (1 / 4) r t := by
  by_cases ht : |t| ≤ r
  · have hden : 0 < t ^ 2 + r ^ 2 := by positivity
    have hle : cotlarPoissonKernel r t ≤ 1 / r := by
      rw [cotlarPoissonKernel, div_le_iff₀ hden, div_eq_mul_inv]
      have : 0 ≤ t ^ 2 := sq_nonneg t
      field_simp
      nlinarith
    exact (ENNReal.ofReal_le_ofReal hle).trans (by
      simp [cotlarCentralBallMajorant, ht])
  · have htr : r < |t| := lt_of_not_ge ht
    exact (ofReal_cotlarPoissonKernel_le_dyadicBallSeries hr htr).trans (by
      simp [cotlarCentralBallMajorant, ht])

theorem ofReal_cotlarPoissonErrorMajorant_le_radialMajorant
    {r t : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (cotlarPoissonErrorMajorant r t) ≤
      cotlarCentralBallMajorant r t + cotlarDyadicBallSeries (1 / 8) r t := by
  by_cases ht : |t| ≤ r
  · simp [cotlarPoissonErrorMajorant, cotlarCentralBallMajorant, ht]
  · have htr : r < |t| := lt_of_not_ge ht
    exact (ofReal_cotlarPoissonErrorMajorant_le_dyadicBallSeries hr htr).trans (by
      simp [cotlarCentralBallMajorant, ht])

/-- Radial Poisson kernels are dominated, after convolution, by the centered
Hardy--Littlewood maximal operator. The harmless constant `20` comes from a
central ball and the dyadic quadratic tail. -/
theorem lintegral_ofReal_cotlarPoissonKernel_mul_le_maximal
    {r : ℝ} (hr : 0 < r) {G : ℝ → ℝ≥0∞} (hG : Measurable G) (x : ℝ) :
    (∫⁻ y, ENNReal.ofReal (cotlarPoissonKernel r (x - y)) * G y) ≤
      20 * centeredHardyLittlewoodMaximal G x := by
  calc
    (∫⁻ y, ENNReal.ofReal (cotlarPoissonKernel r (x - y)) * G y) ≤
        ∫⁻ y, (cotlarCentralBallMajorant r (x - y) +
          cotlarDyadicBallSeries (1 / 4) r (x - y)) * G y := by
      apply lintegral_mono
      intro y
      exact mul_le_mul' (ofReal_cotlarPoissonKernel_le_radialMajorant hr) le_rfl
    _ = (∫⁻ y, cotlarCentralBallMajorant r (x - y) * G y) +
        ∫⁻ y, cotlarDyadicBallSeries (1 / 4) r (x - y) * G y := by
      simp_rw [add_mul]
      rw [lintegral_add_left]
      exact ((measurable_cotlarCentralBallMajorant r).comp
        (measurable_const.sub measurable_id)).mul hG
    _ ≤ 4 * centeredHardyLittlewoodMaximal G x +
        16 * centeredHardyLittlewoodMaximal G x :=
      add_le_add (lintegral_cotlarCentralBallMajorant_mul_le_maximal hr hG x)
        (lintegral_cotlarDyadicBallSeries_quarter_le_maximal hr hG x)
    _ = 20 * centeredHardyLittlewoodMaximal G x := by ring

/-- The complete sharp-to-conjugate-Poisson comparison error has the same
radial maximal domination, with the faster cubic-tail constant `44/3`. -/
theorem lintegral_ofReal_cotlarPoissonErrorMajorant_mul_le_maximal
    {r : ℝ} (hr : 0 < r) {G : ℝ → ℝ≥0∞} (hG : Measurable G) (x : ℝ) :
    (∫⁻ y, ENNReal.ofReal (cotlarPoissonErrorMajorant r (x - y)) * G y) ≤
      ENNReal.ofReal (44 / 3) * centeredHardyLittlewoodMaximal G x := by
  calc
    (∫⁻ y, ENNReal.ofReal (cotlarPoissonErrorMajorant r (x - y)) * G y) ≤
        ∫⁻ y, (cotlarCentralBallMajorant r (x - y) +
          cotlarDyadicBallSeries (1 / 8) r (x - y)) * G y := by
      apply lintegral_mono
      intro y
      exact mul_le_mul'
        (ofReal_cotlarPoissonErrorMajorant_le_radialMajorant hr) le_rfl
    _ = (∫⁻ y, cotlarCentralBallMajorant r (x - y) * G y) +
        ∫⁻ y, cotlarDyadicBallSeries (1 / 8) r (x - y) * G y := by
      simp_rw [add_mul]
      rw [lintegral_add_left]
      exact ((measurable_cotlarCentralBallMajorant r).comp
        (measurable_const.sub measurable_id)).mul hG
    _ ≤ 4 * centeredHardyLittlewoodMaximal G x +
        ENNReal.ofReal (32 / 3) * centeredHardyLittlewoodMaximal G x :=
      add_le_add (lintegral_cotlarCentralBallMajorant_mul_le_maximal hr hG x)
        (lintegral_cotlarDyadicBallSeries_eighth_le_maximal hr hG x)
    _ = ENNReal.ofReal (44 / 3) * centeredHardyLittlewoodMaximal G x := by
      rw [← add_mul]
      congr 1
      calc
        (4 : ℝ≥0∞) + ENNReal.ofReal (32 / 3) =
            ENNReal.ofReal 4 + ENNReal.ofReal (32 / 3) := by norm_num
        _ = ENNReal.ofReal (4 + 32 / 3) := by
          rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 4)
            (by norm_num : (0 : ℝ) ≤ 32 / 3)]
        _ = ENNReal.ofReal (44 / 3) := by norm_num

/-- Convolution with the exact error between the sharp Hilbert kernel and
the conjugate Poisson kernel. -/
noncomputable def cotlarSharpPoissonErrorAction
    (r : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, ((cotlarSharpHilbertKernel r (x - y) -
    cotlarConjugatePoissonKernel r (x - y) : ℝ) : ℂ) * g y

/-- The sharp-to-Poisson convolution error is pointwise controlled by the
Hardy--Littlewood maximal function of `‖g‖`. -/
theorem enorm_cotlarSharpPoissonErrorAction_le_maximal
    {r : ℝ} (hr : 0 < r) {g : ℝ → ℂ} (hg : Measurable g) (x : ℝ) :
    ‖cotlarSharpPoissonErrorAction r g x‖ₑ ≤
      ENNReal.ofReal (44 / 3) *
        centeredHardyLittlewoodMaximal (fun y ↦ ‖g y‖ₑ) x := by
  calc
    ‖cotlarSharpPoissonErrorAction r g x‖ₑ ≤
        ∫⁻ y, ‖((cotlarSharpHilbertKernel r (x - y) -
          cotlarConjugatePoissonKernel r (x - y) : ℝ) : ℂ) * g y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ENNReal.ofReal (cotlarPoissonErrorMajorant r (x - y)) *
        ‖g y‖ₑ := by
      apply lintegral_mono
      intro y
      change ‖((cotlarSharpHilbertKernel r (x - y) -
        cotlarConjugatePoissonKernel r (x - y) : ℝ) : ℂ) * g y‖ₑ ≤
          ENNReal.ofReal (cotlarPoissonErrorMajorant r (x - y)) * ‖g y‖ₑ
      rw [enorm_mul]
      apply mul_le_mul' ?_ le_rfl
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (abs_cotlarSharp_sub_conjugatePoisson_le_majorant
          (t := x - y) hr)
    _ ≤ _ := lintegral_ofReal_cotlarPoissonErrorMajorant_mul_le_maximal hr
      hg.enorm x

/-- Convolution with the positive Poisson kernel, in the normalization whose
total mass is `π`. -/
noncomputable def cotlarPoissonAction (r : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, (cotlarPoissonKernel r (x - y) : ℂ) * g y

theorem enorm_cotlarPoissonAction_le_maximal
    {r : ℝ} (hr : 0 < r) {g : ℝ → ℂ} (hg : Measurable g) (x : ℝ) :
    ‖cotlarPoissonAction r g x‖ₑ ≤
      20 * centeredHardyLittlewoodMaximal (fun y ↦ ‖g y‖ₑ) x := by
  calc
    ‖cotlarPoissonAction r g x‖ₑ ≤
        ∫⁻ y, ‖(cotlarPoissonKernel r (x - y) : ℂ) * g y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ENNReal.ofReal (cotlarPoissonKernel r (x - y)) * ‖g y‖ₑ := by
      apply lintegral_congr
      intro y
      rw [enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (cotlarPoissonKernel_nonneg hr.le)]
    _ ≤ _ := lintegral_ofReal_cotlarPoissonKernel_mul_le_maximal hr hg.enorm x

/-- The conjugate Poisson kernel is uniformly bounded at fixed positive
radius. -/
theorem abs_cotlarConjugatePoissonKernel_le_half_inv {r t : ℝ} (hr : 0 < r) :
    |cotlarConjugatePoissonKernel r t| ≤ 1 / (2 * r) := by
  have hden : 0 < t ^ 2 + r ^ 2 := by positivity
  have h2r : 0 < 2 * r := by positivity
  rw [cotlarConjugatePoissonKernel, abs_div, abs_of_pos hden,
    div_le_div_iff₀ hden h2r]
  nlinarith [sq_nonneg (|t| - r), sq_abs t]

theorem sharpQuadraticTailKernel_zero_eq_cotlarSharp
    {r t : ℝ} :
    sharpQuadraticTailKernel 0 r t = (cotlarSharpHilbertKernel r t : ℂ) := by
  by_cases ht : r < |t|
  · simp [sharpQuadraticTailKernel, cotlarSharpHilbertKernel, ht, phase_zero,
      div_eq_mul_inv]
  · simp [sharpQuadraticTailKernel, cotlarSharpHilbertKernel, ht]

/-- Convolution with the conjugate Poisson kernel used in the Cotlar decomposition. -/
noncomputable def cotlarConjugatePoissonAction
    (r : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, (cotlarConjugatePoissonKernel r (x - y) : ℂ) * g y

/-- Exact sharp-kernel decomposition into the conjugate Poisson action and
the controlled radial error. -/
theorem quadraticHilbertTrunc_zero_eq_conjugatePoisson_add_error
    {r : ℝ} (hr : 0 < r) {g : ℝ → ℂ}
    (hgi : Integrable g) (x : ℝ) :
    quadraticHilbertTrunc 0 r g x =
      cotlarConjugatePoissonAction r g x +
        cotlarSharpPoissonErrorAction r g x := by
  have hsharp : Integrable
      (fun y ↦ sharpQuadraticTailKernel 0 r (x - y) * g y) := by
    apply hgi.bdd_mul (c := 1 / r)
    · exact ((measurable_sharpQuadraticTailKernel 0 r).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y ↦
        sharpQuadraticTailKernel_norm_le 0 (t := x - y) hr
  have hQ : Integrable
      (fun y ↦ (cotlarConjugatePoissonKernel r (x - y) : ℂ) * g y) := by
    apply hgi.bdd_mul (c := 1 / (2 * r))
    · exact (Complex.measurable_ofReal.comp
        ((measurable_cotlarConjugatePoissonKernel r).comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y ↦ by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using
          abs_cotlarConjugatePoissonKernel_le_half_inv
            (t := x - y) hr
  have herr : Integrable (fun y ↦
      ((cotlarSharpHilbertKernel r (x - y) -
        cotlarConjugatePoissonKernel r (x - y) : ℝ) : ℂ) * g y) := by
    convert hsharp.sub hQ using 1
    funext y
    change ((cotlarSharpHilbertKernel r (x - y) -
      cotlarConjugatePoissonKernel r (x - y) : ℝ) : ℂ) * g y =
      sharpQuadraticTailKernel 0 r (x - y) * g y -
        (cotlarConjugatePoissonKernel r (x - y) : ℂ) * g y
    rw [sharpQuadraticTailKernel_zero_eq_cotlarSharp]
    push_cast
    ring
  rw [← quadraticHilbertConvolutionTrunc_eq_quadraticHilbertTrunc]
  unfold quadraticHilbertConvolutionTrunc cotlarConjugatePoissonAction
    cotlarSharpPoissonErrorAction
  calc
    (∫ y, sharpQuadraticTailKernel 0 r (x - y) * g y) =
        ∫ y, (cotlarConjugatePoissonKernel r (x - y) : ℂ) * g y +
          ((cotlarSharpHilbertKernel r (x - y) -
            cotlarConjugatePoissonKernel r (x - y) : ℝ) : ℂ) * g y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [sharpQuadraticTailKernel_zero_eq_cotlarSharp]
      push_cast
      ring
    _ = (∫ y, (cotlarConjugatePoissonKernel r (x - y) : ℂ) * g y) +
        ∫ y, ((cotlarSharpHilbertKernel r (x - y) -
          cotlarConjugatePoissonKernel r (x - y) : ℝ) : ℂ) * g y :=
      integral_add hQ herr

/-! ## Linear recombination needed after the Cotlar estimate -/

theorem zeroHilbertTruncation_add {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    quadraticHilbertTrunc 0 ε (f + g) x =
      quadraticHilbertTrunc 0 ε f x + quadraticHilbertTrunc 0 ε g x := by
  have hfi := integrableOn_zeroHilbertTail hε hf x
  have hgi := integrableOn_zeroHilbertTail hε hg x
  unfold quadraticHilbertTrunc
  simp only [zero_mul, phase_zero, mul_one]
  rw [← integral_add hfi hgi]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Pi.add_apply]
  ring

/-- Sublinearity of the genuine supremum over all positive sharp truncation
radii. -/
theorem quadraticHilbertMaximalTruncation_zero_add_le
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    quadraticHilbertMaximalTruncation 0 (f + g) x ≤
      quadraticHilbertMaximalTruncation 0 f x +
        quadraticHilbertMaximalTruncation 0 g x := by
  unfold quadraticHilbertMaximalTruncation
  apply iSup_le
  intro ε
  rw [zeroHilbertTruncation_add hf hg ε.2]
  apply (enorm_add_le _ _).trans
  exact add_le_add
    (le_iSup (fun r : {r : ℝ // 0 < r} ↦
      ‖quadraticHilbertTrunc 0 r f x‖ₑ) ε)
    (le_iSup (fun r : {r : ℝ // 0 < r} ↦
      ‖quadraticHilbertTrunc 0 r g x‖ₑ) ε)

theorem zeroHilbertTruncation_const_mul (c : ℂ) (f : ℝ → ℂ)
    (ε x : ℝ) :
    quadraticHilbertTrunc 0 ε (fun y ↦ c * f y) x =
      c * quadraticHilbertTrunc 0 ε f x := by
  unfold quadraticHilbertTrunc
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [zero_mul, phase_zero, mul_one]
  ring

/-- Exact homogeneity of the genuine zero-modulation maximal truncation. -/
theorem quadraticHilbertMaximalTruncation_zero_const_mul
    (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    quadraticHilbertMaximalTruncation 0 (fun y ↦ c * f y) x =
      ‖c‖ₑ * quadraticHilbertMaximalTruncation 0 f x := by
  unfold quadraticHilbertMaximalTruncation
  simp_rw [zeroHilbertTruncation_const_mul, enorm_mul]
  rw [ENNReal.mul_iSup]

theorem integrable_stoppingBadDifference {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) :
    Integrable (fun x ↦ f x - stoppingGoodPart f x) := by
  apply (integrable_tsum_stoppingHilbertBadAtom hf hfi).congr
  filter_upwards with x
  exact (tsum_stoppingHilbertBadAtom_eq_sub_stoppingGoodPart f x)

theorem integrable_stoppingGoodPart_for_hilbert {f : ℝ → ℂ}
    (hf : Measurable f) (hfi : Integrable f) : Integrable (stoppingGoodPart f) := by
  have hb := integrable_stoppingBadDifference hf hfi
  have hd := hfi.sub hb
  apply hd.congr
  filter_upwards with x
  simp only [Pi.sub_apply]
  ring

theorem measurable_stoppingGoodPart_of_measurable {f : ℝ → ℂ}
    (hf : Measurable f) : Measurable (stoppingGoodPart f) := by
  let _ := Encodable.ofCountable (stoppingCell f)
  unfold stoppingGoodPart
  apply (hf.indicator (measurableSet_stoppingBadUnion f).compl).add
  apply Measurable.tsum
  intro c
  exact measurable_const.indicator
    (measurableSet_stoppingCell_interval (f := f) c)

/-- A genuinely measurable version of the canonical `L²` Hilbert
representative, needed because the centered maximal operator is defined on
pointwise representatives. -/
noncomputable def measurableStoppingGoodHilbertRepresentative
    (f : ℝ → ℂ) (hf : Integrable f) : ℝ → ℂ :=
  (aestronglyMeasurable_stoppingGoodHilbertL2Representative hf).aemeasurable.mk
    (stoppingGoodHilbertL2Representative f hf)

theorem measurable_measurableStoppingGoodHilbertRepresentative
    {f : ℝ → ℂ} (hf : Integrable f) :
    Measurable (measurableStoppingGoodHilbertRepresentative f hf) :=
  (aestronglyMeasurable_stoppingGoodHilbertL2Representative hf).aemeasurable.measurable_mk

theorem ae_eq_measurableStoppingGoodHilbertRepresentative
    {f : ℝ → ℂ} (hf : Integrable f) :
    stoppingGoodHilbertL2Representative f hf =ᵐ[volume]
      measurableStoppingGoodHilbertRepresentative f hf :=
  (aestronglyMeasurable_stoppingGoodHilbertL2Representative hf).aemeasurable.ae_eq_mk

theorem enorm_cotlarPoissonAction_stoppingGoodHilbert_le_maximal
    {f : ℝ → ℂ} (hf : Integrable f) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ‖cotlarPoissonAction r
      (measurableStoppingGoodHilbertRepresentative f hf) x‖ₑ ≤
      20 * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖measurableStoppingGoodHilbertRepresentative f hf y‖ₑ) x :=
  enorm_cotlarPoissonAction_le_maximal hr
    (measurable_measurableStoppingGoodHilbertRepresentative hf) x

/-- Cotlar reduction for the actual stopping good part: only the conjugate
Poisson action remains, while the sharp-kernel error is already controlled
by the centered maximal function. -/
theorem enorm_quadraticHilbertTrunc_stoppingGoodPart_le_conjugatePoisson
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ‖quadraticHilbertTrunc 0 r (stoppingGoodPart f) x‖ₑ ≤
      ‖cotlarConjugatePoissonAction r (stoppingGoodPart f) x‖ₑ +
        ENNReal.ofReal (44 / 3) * centeredHardyLittlewoodMaximal
          (fun y ↦ ‖stoppingGoodPart f y‖ₑ) x := by
  rw [quadraticHilbertTrunc_zero_eq_conjugatePoisson_add_error hr
    (integrable_stoppingGoodPart_for_hilbert hf hfi) x]
  exact (enorm_add_le _ _).trans (add_le_add_right
    (enorm_cotlarSharpPoissonErrorAction_le_maximal hr
      (measurable_stoppingGoodPart_of_measurable hf) x) _)

/-- Exact good/bad maximal recombination for the canonical stopping
decomposition. -/
theorem quadraticHilbertMaximalTruncation_zero_le_good_add_bad
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) (x : ℝ) :
    quadraticHilbertMaximalTruncation 0 f x ≤
      quadraticHilbertMaximalTruncation 0 (stoppingGoodPart f) x +
        quadraticHilbertMaximalTruncation 0
          (fun y ↦ f y - stoppingGoodPart f y) x := by
  have hsum : stoppingGoodPart f +
      (fun y ↦ f y - stoppingGoodPart f y) = f := by
    ext y
    simp only [Pi.add_apply]
    ring
  calc
    quadraticHilbertMaximalTruncation 0 f x =
        quadraticHilbertMaximalTruncation 0
          (stoppingGoodPart f + fun y ↦ f y - stoppingGoodPart f y) x := by
      rw [hsum]
    _ ≤ _ := quadraticHilbertMaximalTruncation_zero_add_le
      (integrable_stoppingGoodPart_for_hilbert hf hfi)
      (integrable_stoppingBadDifference hf hfi) x

/-- The small-radius portion of a stopping atom's maximal truncation obeys
the same integrated off-triple cancellation bound. -/
theorem integral_toReal_stoppingAtomSmallRadiusMaximal_le
    {f : ℝ → ℂ} (hf : Integrable f) (c : stoppingCell f) :
    ∫ x in (tripleCenteredInterval (stoppingCellCenter f c)
        (stoppingCellLength f c))ᶜ,
      (stoppingAtomSmallRadiusMaximal f c x).toReal ≤
      (32 / 3 : ℝ) * ∫ y in c.1.interval (rootLength f), ‖f y‖ := by
  calc
    _ = ∫ x in (tripleCenteredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c))ᶜ,
        ‖∫ y in centeredInterval (stoppingCellCenter f c) (stoppingCellLength f c),
          ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y‖ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
      rw [stoppingAtomSmallRadiusMaximal_eq_of_notMem_triple f c hx]
      simp
    _ ≤ _ := integral_norm_ordinaryHilbertKernel_stoppingAtom_le hf c

/-- The local `L¹` masses on all canonical stopping cells form a summable
family. Their sum is at most the global `L¹` mass because the stopping
cells are pairwise disjoint. -/
theorem summable_stoppingCell_normMass {f : ℝ → ℂ} (hf : Integrable f) :
    Summable (fun c : stoppingCell f ↦
      ∫ x in c.1.interval (rootLength f), ‖f x‖) := by
  exact (hasSum_integral_iUnion
    (fun c : stoppingCell f ↦ measurableSet_stoppingCell_interval c)
    stoppingCell_pairwiseDisjoint hf.norm.integrableOn).summable

/-- Summing the ordinary-kernel cancellation estimate over the complete
canonical stopping family costs only the global `L¹` mass. This is the
global bad-part estimate away from the triple of each atom's own cell. -/
theorem tsum_integral_norm_ordinaryHilbertKernel_stoppingAtom_le
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∑' c : stoppingCell f,
      ∫ x in (tripleCenteredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c))ᶜ,
        ‖∫ y in centeredInterval (stoppingCellCenter f c)
            (stoppingCellLength f c),
          ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y‖) ≤
      (32 / 3 : ℝ) * ∫ x, ‖f x‖ := by
  let localMass : stoppingCell f → ℝ := fun c ↦
    ∫ x in c.1.interval (rootLength f), ‖f x‖
  let offMass : stoppingCell f → ℝ := fun c ↦
    ∫ x in (tripleCenteredInterval (stoppingCellCenter f c)
        (stoppingCellLength f c))ᶜ,
      ‖∫ y in centeredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c),
        ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y‖
  have hlocalSummable : Summable localMass :=
    summable_stoppingCell_normMass hf
  have hmajorantSummable : Summable (fun c ↦ (32 / 3 : ℝ) * localMass c) :=
    hlocalSummable.mul_left (32 / 3 : ℝ)
  have hoff_nonneg : ∀ c, 0 ≤ offMass c := by
    intro c
    exact integral_nonneg fun _ ↦ norm_nonneg _
  have hterm : ∀ c, offMass c ≤ (32 / 3 : ℝ) * localMass c := by
    intro c
    exact integral_norm_ordinaryHilbertKernel_stoppingAtom_le hf c
  have hoffSummable : Summable offMass :=
    Summable.of_nonneg_of_le hoff_nonneg hterm hmajorantSummable
  have hsumLocal : (∑' c : stoppingCell f, localMass c) =
      ∫ x in stoppingBadUnion f, ‖f x‖ := by
    symm
    exact integral_iUnion
      (fun c : stoppingCell f ↦ measurableSet_stoppingCell_interval c)
      stoppingCell_pairwiseDisjoint hf.norm.integrableOn
  have hbad_le : (∫ x in stoppingBadUnion f, ‖f x‖) ≤ ∫ x, ‖f x‖ := by
    exact setIntegral_le_integral hf.norm
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  change (∑' c : stoppingCell f, offMass c) ≤
    (32 / 3 : ℝ) * ∫ x, ‖f x‖
  calc
    (∑' c : stoppingCell f, offMass c) ≤
        ∑' c : stoppingCell f, (32 / 3 : ℝ) * localMass c :=
      hoffSummable.tsum_le_tsum hterm hmajorantSummable
    _ = (32 / 3 : ℝ) * ∑' c : stoppingCell f, localMass c := tsum_mul_left
    _ = (32 / 3 : ℝ) * ∫ x in stoppingBadUnion f, ‖f x‖ := by rw [hsumLocal]
    _ ≤ (32 / 3 : ℝ) * ∫ x, ‖f x‖ := by
      exact mul_le_mul_of_nonneg_left hbad_le (by norm_num)

/-- Globally over all stopping cells, the small-radius maximal pieces retain
the uniform cancellation bound. -/
theorem tsum_integral_toReal_stoppingAtomSmallRadiusMaximal_le
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∑' c : stoppingCell f,
      ∫ x in (tripleCenteredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c))ᶜ,
        (stoppingAtomSmallRadiusMaximal f c x).toReal) ≤
      (32 / 3 : ℝ) * ∫ x, ‖f x‖ := by
  have heq : (fun c : stoppingCell f ↦
      ∫ x in (tripleCenteredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c))ᶜ,
        (stoppingAtomSmallRadiusMaximal f c x).toReal) =
      (fun c : stoppingCell f ↦
      ∫ x in (tripleCenteredInterval (stoppingCellCenter f c)
          (stoppingCellLength f c))ᶜ,
        ‖∫ y in centeredInterval (stoppingCellCenter f c)
            (stoppingCellLength f c),
          ordinaryHilbertKernel x y * stoppingHilbertBadAtom f c y‖) := by
    funext c
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with x hx
    rw [stoppingAtomSmallRadiusMaximal_eq_of_notMem_triple f c hx]
    simp
  rw [heq]
  exact tsum_integral_norm_ordinaryHilbertKernel_stoppingAtom_le hf


end
end HilbertMaximalWeakOneOne
end QuadraticCarleson
