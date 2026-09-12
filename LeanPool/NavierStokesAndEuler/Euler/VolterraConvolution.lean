/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Star.Real

/-! A genuine singular-kernel Volterra convolution on continuous Banach-valued paths. -/

@[expose] public section


noncomputable section

namespace EulerVolterraConvolution

open MeasureTheory Set
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable (T : ℝ) (hT : 0 ≤ T)

/-- Continuous extension of a compact-interval path by clamping its time argument. -/
def extendPath (f : C(Icc (0 : ℝ) T, Y)) (t : ℝ) : Y := f (projIcc 0 T hT t)

omit [NormedSpace ℝ Y] in
/-- The clamped extension of a continuous path is continuous. -/
theorem extendPath_continuous (f : C(Icc (0 : ℝ) T, Y)) : Continuous (extendPath T hT f) :=
  f.continuous.comp continuous_projIcc

omit [NormedSpace ℝ Y] in
/-- The clamped extension is bounded by the actual uniform path norm. -/
theorem extendPath_norm_le (f : C(Icc (0 : ℝ) T, Y)) (t : ℝ) : ‖extendPath T hT f t‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

/-- The fixed-domain integrand for a causal, possibly singular, time convolution. -/
def causalIntegrand (K : ℝ → Y →L[ℝ] X) (f : C(Icc (0 : ℝ) T, Y))
    (t : Icc (0 : ℝ) T) (r : ℝ) : X :=
  (Iic t.val).indicator (fun r => K r (extendPath T hT f (t.val - r))) r

variable (K : ℝ → Y →L[ℝ] X) (k : ℝ → ℝ)
variable (hK : ContinuousOn (fun p : ℝ × Y => K p.1 p.2) (Ioi 0 ×ˢ (univ : Set Y)))
variable (hk : IntegrableOn k (Ioc 0 T))
variable (hk0 : ∀ r ∈ Ioc 0 T, 0 ≤ k r)
variable (hbound : ∀ r ∈ Ioc 0 T, ∀ y, ‖K r y‖ ≤ k r * ‖y‖)

include hK in
/-- The translated path integrand is measurable despite the possible kernel singularity at zero. -/
theorem causalIntegrand_measurable (f : C(Icc (0 : ℝ) T, Y)) (t : Icc (0 : ℝ) T) :
    AEStronglyMeasurable (causalIntegrand T hT K f t) (volume.restrict (Ioc 0 T)) := by
  have hc : ContinuousOn (fun r : ℝ => K r (extendPath T hT f (t.val - r))) (Ioc 0 T) :=
    hK.comp (continuous_id.prodMk ((extendPath_continuous T hT f).comp
      (continuous_const.sub continuous_id))).continuousOn (fun r hr => ⟨hr.1, mem_univ _⟩)
  exact (hc.aestronglyMeasurable measurableSet_Ioc).indicator measurableSet_Iic

include hk0 hbound in
/-- The causal integrand is bounded by an integrable scalar kernel times the path norm. -/
theorem causalIntegrand_bound (f : C(Icc (0 : ℝ) T, Y)) (t : Icc (0 : ℝ) T)
    (r : ℝ) (hr : r ∈ Ioc 0 T) :
    ‖causalIntegrand T hT K f t r‖ ≤ k r * ‖f‖ := by
  unfold causalIntegrand
  by_cases hrt : r ≤ t.val
  · simp only [indicator, mem_Iic, hrt, ite_true]
    exact (hbound r hr _).trans (mul_le_mul_of_nonneg_left (extendPath_norm_le T hT f _) (hk0 r hr))
  · simp only [indicator, mem_Iic, hrt, ite_false, norm_zero]
    exact mul_nonneg (hk0 r hr) (norm_nonneg f)

include hK hk hk0 hbound in
/-- The actual causal kernel integral is a Bochner-integrable Banach-valued function. -/
theorem causalIntegrand_integrable (f : C(Icc (0 : ℝ) T, Y)) (t : Icc (0 : ℝ) T) :
    Integrable (causalIntegrand T hT K f t) (volume.restrict (Ioc 0 T)) := by
  apply (hk.mul_const ‖f‖).mono' (causalIntegrand_measurable T hT K hK f t)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  exact causalIntegrand_bound T hT K k hk0 hbound f t r hr

/-- Away from the moving upper endpoint, the causal integrand is continuous in time. -/
theorem causalIntegrand_continuousAt (f : C(Icc (0 : ℝ) T, Y)) (t : Icc (0 : ℝ) T)
    (r : ℝ) (hr : r ≠ t.val) :
    ContinuousAt (fun s : Icc (0 : ℝ) T => causalIntegrand T hT K f s r) t := by
  have hc : Continuous (fun s : Icc (0 : ℝ) T => K r (extendPath T hT f (s.val - r))) :=
    (K r).continuous.comp ((extendPath_continuous T hT f).comp
      (continuous_subtype_val.sub continuous_const))
  rcases lt_or_gt_of_ne hr with hrt | htr
  · apply hc.continuousAt.congr_of_eventuallyEq
    have he : ∀ᶠ s : Icc (0 : ℝ) T in 𝓝 t, r < s.val :=
      (continuous_subtype_val.tendsto t).eventually (Ioi_mem_nhds hrt)
    filter_upwards [he] with s hs
    simp only [causalIntegrand, indicator, mem_Iic, hs.le, ite_true]
  · apply (continuousAt_const (y := (0 : X))).congr_of_eventuallyEq
    have he : ∀ᶠ s : Icc (0 : ℝ) T in 𝓝 t, s.val < r :=
      (continuous_subtype_val.tendsto t).eventually (Iio_mem_nhds htr)
    filter_upwards [he] with s hs
    simp only [causalIntegrand, indicator, mem_Iic, not_le.mpr hs, ite_false]

include hK hk hk0 hbound in
/-- Dominated convergence proves continuity of the actual singular causal integral. -/
theorem causalIntegral_continuous (f : C(Icc (0 : ℝ) T, Y)) :
    Continuous (fun t : Icc (0 : ℝ) T => ∫ r in Ioc 0 T, causalIntegrand T hT K f t r) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_of_dominated
    (Filter.Eventually.of_forall (causalIntegrand_measurable T hT K hK f))
    (Filter.Eventually.of_forall fun s => ?_) (hk.mul_const ‖f‖)
  · have hn : ∀ᵐ r : ℝ ∂volume.restrict (Ioc 0 T), r ≠ t.val := by
      exact compl_mem_ae_iff.mpr (measure_singleton _)
    filter_upwards [hn] with r hr
    exact causalIntegrand_continuousAt T hT K f t r hr
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    exact causalIntegrand_bound T hT K k hk0 hbound f s r hr

/-- The actual causal convolution as a continuous path. -/
def convolution (f : C(Icc (0 : ℝ) T, Y)) : C(Icc (0 : ℝ) T, X) where
  toFun t := ∫ r in Ioc 0 T, causalIntegrand T hT K f t r
  continuous_toFun := causalIntegral_continuous T hT K k hK hk hk0 hbound f

/-- The scalar mass of an integrable time-kernel bound on the chosen time interval. -/
def kernelMass : ℝ := ∫ r in Ioc 0 T, k r

include hk0 in
/-- A nonnegative kernel has nonnegative mass. -/
theorem kernelMass_nonneg : 0 ≤ kernelMass T k := by
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
  exact hk0 r hr

include hK hk hk0 hbound in
/-- The actual time convolution has the sharp path-norm estimate by the kernel mass. -/
theorem convolution_bound (f : C(Icc (0 : ℝ) T, Y)) :
    ‖convolution T hT K k hK hk hk0 hbound f‖ ≤ kernelMass T k * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (kernelMass_nonneg T k hk0) (norm_nonneg f))).mpr
  intro t
  change ‖∫ r in Ioc 0 T, causalIntegrand T hT K f t r‖ ≤ _
  calc
    _ ≤ ∫ r in Ioc 0 T, ‖causalIntegrand T hT K f t r‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioc 0 T, k r * ‖f‖ := integral_mono_ae
      (causalIntegrand_integrable T hT K k hK hk hk0 hbound f t).norm (hk.mul_const ‖f‖) (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
        exact causalIntegrand_bound T hT K k hk0 hbound f t r hr)
    _ = kernelMass T k * ‖f‖ := integral_mul_const _ _

include hK hk hk0 hbound in
/-- The fixed-domain causal integral equals the usual shifted Duhamel interval integral. -/
theorem convolution_eq_interval (f : C(Icc (0 : ℝ) T, Y)) (t : Icc (0 : ℝ) T) :
    convolution T hT K k hK hk hk0 hbound f t =
      ∫ r in (0 : ℝ)..t.val, K r (extendPath T hT f (t.val - r)) := by
  change (∫ r in Ioc 0 T, (Iic t.val).indicator
    (fun r => K r (extendPath T hT f (t.val - r))) r) = _
  rw [← intervalIntegral.integral_of_le hT]
  exact intervalIntegral.integral_indicator t.property

end EulerVolterraConvolution
