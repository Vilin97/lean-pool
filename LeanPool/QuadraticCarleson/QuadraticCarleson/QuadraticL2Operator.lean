/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticTTStar
import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteSparseMaximal

/-!
# Integral operators for the fixed-height quadratic argument

Finite linearizations of the annular quadratic operators have measurable,
bounded kernels with a finite spatial range. This file develops their actual
integral adjoints and `TT*` representation. The boundedness and finite-range
constants here may depend on the finite family; the oscillatory estimates in
`QuadraticTTStar` will be used to obtain constants independent of that family.
-/

open MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson

/-- The elementary kernel properties enjoyed by every finite linearization of
a family of bounded, compactly supported convolution kernels. -/
structure FiniteRangeKernel where
  /-- The jointly measurable complex kernel in the two spatial variables. -/
  toFun : ℝ → ℝ → ℂ
  measurable_toFun : Measurable (Function.uncurry toFun)
  /-- The positive radius beyond which the kernel vanishes off the diagonal. -/
  radius : ℝ
  radius_pos : 0 < radius
  /-- The nonnegative uniform bound on the kernel norm. -/
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ x t, ‖toFun x t‖ ≤ bound
  eq_zero : ∀ x t, radius < |x - t| → toFun x t = 0

instance : CoeFun FiniteRangeKernel (fun _ ↦ ℝ → ℝ → ℂ) := ⟨FiniteRangeKernel.toFun⟩

namespace FiniteRangeKernel

theorem measurable_row (K : FiniteRangeKernel) (x : ℝ) : Measurable (K x) :=
  K.measurable_toFun.comp (measurable_const.prodMk measurable_id)

theorem measurable_column (K : FiniteRangeKernel) (t : ℝ) : Measurable (fun x ↦ K x t) :=
  K.measurable_toFun.comp (measurable_id.prodMk measurable_const)

/-- Conjugating and exchanging the kernel variables gives the integral adjoint. -/
noncomputable def adjoint (K : FiniteRangeKernel) : FiniteRangeKernel where
  toFun x t := conj (K t x)
  measurable_toFun := Complex.continuous_conj.measurable.comp
    (K.measurable_toFun.comp measurable_swap)
  radius := K.radius
  radius_pos := K.radius_pos
  bound := K.bound
  bound_nonneg := K.bound_nonneg
  norm_le x t := by simpa only [RCLike.norm_conj] using K.norm_le t x
  eq_zero x t h := by
    rw [K.eq_zero t x (by simpa only [abs_sub_comm] using h), map_zero]

@[simp] theorem adjoint_apply (K : FiniteRangeKernel) (x t : ℝ) :
    K.adjoint x t = conj (K t x) := rfl

/-- The genuine integral action of the kernel. -/
noncomputable def applyIntegral (K : FiniteRangeKernel) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t, K x t * f t

/-- The kernel obtained by composing the operator with its adjoint. -/
noncomputable def correlation (K : FiniteRangeKernel) (x y : ℝ) : ℂ :=
  ∫ t, K x t * conj (K y t)

theorem integrable_row (K : FiniteRangeKernel) (x : ℝ) : Integrable (K x) := by
  let s : Set ℝ := Icc (x - K.radius) (x + K.radius)
  have hi : Integrable (s.indicator (fun _ ↦ K.bound)) :=
    (integrableOn_const (by simp [s] : volume s ≠ ⊤)).integrable_indicator measurableSet_Icc
  apply hi.mono' (K.measurable_row x).aestronglyMeasurable
  filter_upwards [] with t
  by_cases ht : t ∈ s
  · rw [indicator_of_mem ht]
    exact K.norm_le x t
  · rw [indicator_of_notMem ht]
    have hdist : K.radius < |x - t| := by
      by_contra hn
      have hh := abs_le.mp (le_of_not_gt hn)
      apply ht
      constructor <;> linarith
    rw [K.eq_zero x t hdist, norm_zero]

theorem integrable_column (K : FiniteRangeKernel) (t : ℝ) : Integrable (fun x ↦ K x t) := by
  apply (K.adjoint.integrable_row t).mono (K.measurable_column t).aestronglyMeasurable
  filter_upwards [] with x
  simp only [adjoint_apply, RCLike.norm_conj, le_refl]

theorem integrable_row_mul (K : FiniteRangeKernel) {f : ℝ → ℂ}
    (hf : Integrable f) (x : ℝ) : Integrable (fun t ↦ K x t * f t) :=
  hf.bdd_mul (K.measurable_row x).aestronglyMeasurable
    (Filter.Eventually.of_forall (K.norm_le x))

theorem measurable_applyIntegral (K : FiniteRangeKernel) {f : ℝ → ℂ}
    (hf : Measurable f) : Measurable (K.applyIntegral f) := by
  have hm : Measurable (fun z : ℝ × ℝ ↦ K z.1 z.2 * f z.2) :=
    K.measurable_toFun.mul (hf.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem norm_applyIntegral_le (K : FiniteRangeKernel) {f : ℝ → ℂ}
    (hf : Integrable f) (x : ℝ) :
    ‖K.applyIntegral f x‖ ≤ K.bound * ∫ t, ‖f t‖ := by
  calc
    _ ≤ ∫ t, ‖K x t * f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, K.bound * ‖f t‖ := by
      apply integral_mono (K.integrable_row_mul hf x).norm (hf.norm.const_mul K.bound)
      intro t
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (K.norm_le x t) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The elementary uniform row-mass estimate. -/
theorem integral_norm_row_le (K : FiniteRangeKernel) (x : ℝ) :
    (∫ t, ‖K x t‖) ≤ 2 * K.radius * K.bound := by
  let s : Set ℝ := Icc (x - K.radius) (x + K.radius)
  have hzero (t : ℝ) (ht : t ∉ s) : K x t = 0 := by
    apply K.eq_zero
    by_contra hn
    have hh := abs_le.mp (le_of_not_gt hn)
    apply ht
    constructor <;> linarith
  calc
    _ = ∫ t in s, ‖K x t‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht ↦ by rw [hzero t ht, norm_zero])).symm
    _ ≤ ∫ _t in s, K.bound := by
      apply setIntegral_mono_on (K.integrable_row x).norm.integrableOn
        (integrableOn_const (by simp [s] : volume s ≠ ⊤)) measurableSet_Icc
      intro t _
      exact K.norm_le x t
    _ = _ := by
      rw [setIntegral_const]
      change (volume (Icc (x - K.radius) (x + K.radius))).toReal * K.bound = _
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [K.radius_pos] :
        0 ≤ x + K.radius - (x - K.radius))]
      ring

theorem integral_norm_column_le (K : FiniteRangeKernel) (t : ℝ) :
    (∫ x, ‖K x t‖) ≤ 2 * K.radius * K.bound := by
  have h := K.adjoint.integral_norm_row_le t
  change (∫ x, ‖conj (K x t)‖) ≤ 2 * K.radius * K.bound at h
  simpa only [RCLike.norm_conj] using h

/-- Fubini integrability for the operator action follows from the finite
spatial range; the input need only be integrable. -/
theorem integrable_action_integrand (K : FiniteRangeKernel)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun z : ℝ × ℝ ↦ K z.1 z.2 * f z.2) (volume.prod volume) := by
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ K z.1 z.2 * f z.2)
      (volume.prod volume) :=
    K.measurable_toFun.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd
  apply (integrable_prod_iff' hm).mpr
  constructor
  · filter_upwards [] with t
    exact (K.integrable_column t).mul_const (f t)
  · apply (hf.norm.const_mul (2 * K.radius * K.bound)).mono'
      hm.norm.prod_swap.integral_prod_right'
    filter_upwards [] with t
    dsimp only [Prod.swap, Prod.fst, Prod.snd]
    have hnonneg : 0 ≤ ∫ x, ‖K x t * f t‖ := integral_nonneg (fun _ ↦ norm_nonneg _)
    rw [Real.norm_of_nonneg hnonneg]
    simp_rw [norm_mul, integral_mul_const]
    exact mul_le_mul_of_nonneg_right (K.integral_norm_column_le t) (norm_nonneg _)

theorem integrable_applyIntegral (K : FiniteRangeKernel)
    {f : ℝ → ℂ} (hf : Integrable f) : Integrable (K.applyIntegral f) :=
  (K.integrable_action_integrand hf).integral_prod_left

/-- Integrability of the Fubini integrand is proved from the kernel bounds and
the integrability of the input; it is not an additional assumption. -/
theorem integrable_correlation_integrand (K : FiniteRangeKernel)
    {g : ℝ → ℂ} (hg : Integrable g) (x : ℝ) :
    Integrable (fun z : ℝ × ℝ ↦ K x z.1 * conj (K z.2 z.1) * g z.2)
      (volume.prod volume) := by
  have hi := (K.integrable_row x).mul_prod hg
  have hm : Measurable (fun z : ℝ × ℝ ↦ conj (K z.2 z.1)) :=
    Complex.continuous_conj.measurable.comp (K.measurable_toFun.comp measurable_swap)
  have hb : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖conj (K z.2 z.1)‖ ≤ K.bound :=
    Filter.Eventually.of_forall (fun z ↦ by simpa only [RCLike.norm_conj] using K.norm_le z.2 z.1)
  convert hi.mul_bdd hm.aestronglyMeasurable hb using 1
  funext z
  ring

/-- The pointwise integral representation of the actual composition `TT*` on
integrable inputs. -/
theorem applyIntegral_adjoint_eq_correlation (K : FiniteRangeKernel)
    {g : ℝ → ℂ} (hg : Integrable g) (x : ℝ) :
    K.applyIntegral (K.adjoint.applyIntegral g) x =
      ∫ y, K.correlation x y * g y := by
  unfold applyIntegral correlation
  simp only [adjoint_apply]
  simp_rw [← integral_const_mul]
  have hswap := integral_integral_swap
    (f := fun t y ↦ K x t * conj (K y t) * g y) (K.integrable_correlation_integrand hg x)
  calc
    _ = ∫ t, ∫ y, K x t * conj (K y t) * g y := by
      apply integral_congr_ae
      filter_upwards [] with t
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = ∫ y, ∫ t, K x t * conj (K y t) * g y := hswap
    _ = _ := by simp_rw [integral_mul_const]

/-- The adjoint identity for the genuine integral action on `L¹` test inputs. -/
theorem integral_pairing_adjoint (K : FiniteRangeKernel)
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x, K.applyIntegral f x * conj (g x)) =
      ∫ t, f t * conj (K.adjoint.applyIntegral g t) := by
  have hgconj : Integrable (fun x ↦ conj (g x)) := by
    apply hg.mono (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    filter_upwards [] with x
    simp only [RCLike.norm_conj, le_refl]
  have hi := hf.mul_prod hgconj
  have hm : Measurable (fun z : ℝ × ℝ ↦ K z.2 z.1) :=
    K.measurable_toFun.comp measurable_swap
  have hb : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, ‖K z.2 z.1‖ ≤ K.bound :=
    Filter.Eventually.of_forall (fun z ↦ K.norm_le z.2 z.1)
  have hint : Integrable (fun z : ℝ × ℝ ↦ K z.2 z.1 * f z.1 * conj (g z.2))
      (volume.prod volume) := by
    convert hi.bdd_mul hm.aestronglyMeasurable hb using 1
    funext z
    ring
  unfold applyIntegral
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (f := fun t x ↦ K x t * f t * conj (g x)) hint]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← integral_conj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [adjoint_apply, map_mul, starRingEnd_self_apply]
  ring

/-- The exact quadratic-form identity underlying the `TT*` method. The left
side is the squared `L²` mass of the adjoint applied to the input; the right
side contains the correlation kernel estimated in `QuadraticTTStar`. -/
theorem adjoint_energy_eq_correlation_pairing (K : FiniteRangeKernel)
    {g : ℝ → ℂ} (hg : Integrable g) :
    (∫ t, ((‖K.adjoint.applyIntegral g t‖ ^ 2 : ℝ) : ℂ)) =
      ∫ x, (∫ y, K.correlation x y * g y) * conj (g x) := by
  have h := K.integral_pairing_adjoint (K.adjoint.integrable_applyIntegral hg) hg
  simp_rw [K.applyIntegral_adjoint_eq_correlation hg] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with t
  simpa only [Complex.ofReal_pow] using (Complex.mul_conj' (K.adjoint.applyIntegral g t)).symm

/-- The adjoint energy is integrable on every integrable input. This avoids
using a total Bochner integral at an unproved integrability point in the
quadratic-form argument. -/
theorem integrable_adjoint_energy (K : FiniteRangeKernel)
    {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun t ↦ ‖K.adjoint.applyIntegral g t‖ ^ 2) := by
  have hi := K.adjoint.integrable_applyIntegral hg
  have hbound (t : ℝ) : ‖K.adjoint.applyIntegral g t‖ ≤
      K.bound * ∫ y, ‖g y‖ := K.adjoint.norm_applyIntegral_le hg t
  apply (hi.norm.const_mul (K.bound * ∫ y, ‖g y‖)).mono'
    (hi.aestronglyMeasurable.norm.pow 2)
  filter_upwards [] with t
  dsimp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hh := mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg (K.adjoint.applyIntegral g t))
  nlinarith

/-- A measurable finite selector produces an actual finite-range integral
kernel. The common bound and radius are elementary finite-family bounds;
they are allowed to depend on that family at this stage. -/
noncomputable def ofFiniteConvolution {N : ℕ} (κ : Fin N → ℝ → ℂ)
    (σκ : ℝ → Fin N) (hσ : Measurable σκ)
    (hκ : ∀ i, Measurable (κ i))
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C)
    (hbound : ∀ i t, ‖κ i t‖ ≤ C)
    (hsupport : ∀ i t, R < |t| → κ i t = 0) : FiniteRangeKernel where
  toFun x t := κ (σκ x) (x - t)
  measurable_toFun := by
    have hm : Measurable (fun z : (ℝ × ℝ) × Fin N ↦ κ z.2 (z.1.1 - z.1.2)) :=
      measurable_from_prod_countable_left
        (fun i ↦ (hκ i).comp (measurable_fst.sub measurable_snd))
    exact hm.comp (measurable_id.prodMk (hσ.comp measurable_fst))
  radius := R
  radius_pos := hR
  bound := C
  bound_nonneg := hC
  norm_le x t := hbound (σκ x) (x - t)
  eq_zero x t h := hsupport (σκ x) (x - t) h

@[simp] theorem ofFiniteConvolution_apply {N : ℕ} (κ : Fin N → ℝ → ℂ)
    (σκ : ℝ → Fin N) (hσ : Measurable σκ)
    (hκ : ∀ i, Measurable (κ i))
    (R C : ℝ) (hR : 0 < R) (hC : 0 ≤ C)
    (hbound : ∀ i t, ‖κ i t‖ ≤ C)
    (hsupport : ∀ i t, R < |t| → κ i t = 0) (x t : ℝ) :
    ofFiniteConvolution κ σκ hσ hκ R C hR hC hbound hsupport x t = κ (σκ x) (x - t) := rfl

/-- Every finite family of continuous compactly supported convolution kernels
has the uniform elementary bounds required by `FiniteRangeKernel`. No common
radius or amplitude bound needs to be supplied by the caller. -/
theorem exists_of_finite_convolution {N : ℕ} (κ : Fin N → ℝ → ℂ)
    (σκ : ℝ → Fin N) (hσ : Measurable σκ)
    (hc : ∀ i, Continuous (κ i)) (hs : ∀ i, HasCompactSupport (κ i)) :
    ∃ K : FiniteRangeKernel, ∀ x t, K x t = κ (σκ x) (x - t) := by
  classical
  choose C hC using fun i ↦ (hc i).bounded_above_of_compact_support (hs i)
  choose R hR hvan using fun i ↦ (hs i).exists_pos_le_norm
  let radius : ℝ := 1 + ∑ i, R i
  let bound : ℝ := ∑ i, max (C i) 0
  have hradius : 0 < radius := by
    dsimp [radius]
    have hh : 0 ≤ ∑ i, R i := Finset.sum_nonneg (fun i _ ↦ (hR i).le)
    linarith
  have hbound : 0 ≤ bound := Finset.sum_nonneg (fun i _ ↦ le_max_right _ _)
  have hRi (i : Fin N) : R i ≤ radius := by
    have hh : R i ≤ ∑ j, R j :=
      Finset.single_le_sum (fun j _ ↦ (hR j).le) (Finset.mem_univ i)
    dsimp [radius]
    linarith
  have hCi (i : Fin N) (t : ℝ) : ‖κ i t‖ ≤ bound := by
    apply (hC i t).trans ((le_max_left (C i) 0).trans _)
    exact Finset.single_le_sum (fun j _ ↦ le_max_right _ _) (Finset.mem_univ i)
  have hsupport (i : Fin N) (t : ℝ) (ht : radius < |t|) : κ i t = 0 := by
    apply hvan i t
    rw [Real.norm_eq_abs]
    exact (hRi i).trans ht.le
  exact ⟨ofFiniteConvolution κ σκ hσ (fun i ↦ (hc i).measurable)
    radius bound hradius hbound hCi hsupport, fun _ _ ↦ rfl⟩

/-- Exact measurable linearization of a finite maximal convolution operator.
The selector is obtained from the measurable maximizing-index theorem, and
the selected operator is represented by a genuine finite-range kernel. -/
theorem exists_finite_maximal_linearization (n : ℕ) (κ : Fin (n + 1) → ℝ → ℂ)
    (hc : ∀ i, Continuous (κ i)) (hs : ∀ i, HasCompactSupport (κ i))
    {f : ℝ → ℂ} (hf : Measurable f) :
    ∃ (σκ : ℝ → Fin (n + 1)) (K : FiniteRangeKernel), Measurable σκ ∧
      (∀ x t, K x t = κ (σκ x) (x - t)) ∧
      ∀ x i, ‖∫ t, κ i (x - t) * f t‖ ≤ ‖K.applyIntegral f x‖ := by
  let F : Fin (n + 1) → ℝ → ℂ := fun i x ↦ ∫ t, κ i (x - t) * f t
  have hF (i : Fin (n + 1)) : Measurable (F i) := by
    have hm : Measurable (fun z : ℝ × ℝ ↦ κ i (z.1 - z.2) * f z.2) :=
      ((hc i).measurable.comp (measurable_fst.sub measurable_snd)).mul (hf.comp measurable_snd)
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  let σκ := measurableMaximizingIndex n F
  have hσ : Measurable σκ := measurable_measurableMaximizingIndex n F hF
  obtain ⟨K, hK⟩ := exists_of_finite_convolution κ σκ hσ hc hs
  refine ⟨σκ, K, hσ, hK, ?_⟩
  intro x i
  have h := measurableMaximizingIndex_isMax n F x i
  simpa only [applyIntegral, hK, F] using h

end FiniteRangeKernel

end QuadraticCarleson
