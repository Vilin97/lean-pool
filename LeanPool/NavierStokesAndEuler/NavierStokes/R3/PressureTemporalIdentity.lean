/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ConservativeDifference
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Compact time tests of the conservative pressure identity

The temporal test has topological support inside the open time interval. The
spatial test is smooth and compactly supported. Consequently all pairings are
ordinary Lebesgue integrals even when the pressure grows at spatial infinity.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.PressureTemporalIdentity

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open ConservativeDifference
open Comparison (tensorDiff)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

/-- A time cutoff supported in an open set turns a continuous function on
that set into a globally continuous product, regardless of its values outside. -/
theorem continuous_cutoff_mul {a F : ℝ → ℝ} {s : Set ℝ}
    (ha : Continuous a) (hF : ContinuousOn F s) (hs : IsOpen s)
    (hsupp : tsupport a ⊆ s) : Continuous (fun t => a t * F t) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t ∈ tsupport a
  · exact ha.continuousAt.mul ((hF t (hsupp ht)).continuousAt (hs.mem_nhds (hsupp ht)))
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds ht] with r hr
    rw [image_eq_zero_of_notMem_tsupport hr, zero_mul]

theorem component_test_continuousOn {T : ℝ} {w : VelocityField} {ψ : Space → ℝ}
    (hw : ContinuousOn w (Comparison.slab 0 T))
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ContinuousOn (fun t => ∫ x, w (t, x) k * ψ x) (Icc 0 T) := by
  have hF : ContinuousOn (fun z : SpaceTime => w z k * ψ z.2) (Icc 0 T ×ˢ univ) :=
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn hw).mul
      (hψ.comp continuous_snd).continuousOn
  apply CompactTimeIntegral.continuousOn_integral hcψ hF
  intro t ht x hx
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem component_time_test_continuousOn {T : ℝ} {w : VelocityField} {ψ : Space → ℝ}
    (hw : ContDiffOn ℝ ∞ w (Comparison.slab 0 T))
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ContinuousOn (fun t => ∫ x, temporalDerivative w t x k * ψ x) (Ioo 0 T) := by
  have htime : ContinuousOn (fun z : SpaceTime => temporalDerivative w z.1 z.2)
      (Ioo 0 T ×ˢ univ) := by
    simpa only [temporalDerivative, deriv] using
      CompactTimeIntegral.continuousOn_timeDeriv_of_contDiffOn (hw.of_le (nat_le_infty 1))
  have hF : ContinuousOn (fun z : SpaceTime => temporalDerivative w z.1 z.2 k * ψ z.2)
      (Ioo 0 T ×ˢ univ) :=
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn htime).mul
      (hψ.comp continuous_snd).continuousOn
  apply CompactTimeIntegral.continuousOn_integral hcψ hF
  intro t ht x hx
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem tensor_test_continuousOn {T : ℝ} {u v : VelocityField} {ψ : Space → ℝ}
    (hu : ContinuousOn u (Comparison.slab 0 T))
    (hv : ContinuousOn v (Comparison.slab 0 T))
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (i j : Fin 3) :
    ContinuousOn (fun t => ∫ x, tensorDiff u v t i j x * ψ x) (Icc 0 T) := by
  have hucomp (k : Fin 3) : ContinuousOn (fun z : SpaceTime => u z k) (Comparison.slab 0 T) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn hu
  have hvcomp (k : Fin 3) : ContinuousOn (fun z : SpaceTime => v z k) (Comparison.slab 0 T) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn hv
  have hF : ContinuousOn (fun z : SpaceTime => tensorDiff u v z.1 i j z.2 * ψ z.2)
      (Icc 0 T ×ˢ univ) :=
    (((hucomp i).mul (hucomp j)).sub ((hvcomp i).mul (hvcomp j))).mul
      (hψ.comp continuous_snd).continuousOn
  apply CompactTimeIntegral.continuousOn_integral hcψ hF
  intro t ht x hx
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- Integration by parts with a temporal test supported away from both
endpoints. Only the cutoff-weighted derivative needs to be integrable. -/
theorem compact_time_integration_by_parts {T : ℝ} {a F D : ℝ → ℝ}
    (hT : 0 < T) (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    (hF : ContinuousOn F (Icc 0 T)) (hD : ContinuousOn D (Ioo 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt F (D t) t) :
    (∫ t in (0 : ℝ)..T, a t * D t) = -(∫ t in (0 : ℝ)..T, deriv a t * F t) := by
  have hda : Continuous (deriv a) := by
    change Continuous (fun t => fderiv ℝ a t 1)
    exact ((ha.fderiv_right infty_add_one_le).clm_apply contDiff_const).continuous
  have hi₁ : IntervalIntegrable (fun t => deriv a t * F t) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT.le (hda.continuousOn.mul hF)
  have hi₂ : IntervalIntegrable (fun t => a t * D t) volume 0 T :=
    (continuous_cutoff_mul ha.continuous hD isOpen_Ioo hsupp).intervalIntegrable _ _
  have hisum : IntervalIntegrable (fun t => deriv a t * F t + a t * D t) volume 0 T :=
    hi₁.add hi₂
  have hprod : ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun r => a r * F r) (deriv a t * F t + a t * D t) t := by
    intro t ht
    exact ((ha.differentiable (by simp) t).hasDerivAt).mul (hderiv t ht)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
    (ha.continuous.continuousOn.mul hF) hprod hisum
  have ha0 : a 0 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h
    exact (lt_irrefl 0) (hsupp h).1)
  have haT : a T = 0 := image_eq_zero_of_notMem_tsupport (by
    intro h
    exact (lt_irrefl T) (hsupp h).2)
  rw [intervalIntegral.integral_add hi₁ hi₂, Pi.mul_apply, Pi.mul_apply, ha0, haT, zero_mul,
    zero_mul, sub_self] at hFTC
  linarith

/-- The compact pressure-gradient identity integrated against a time test.
Both derivatives of the velocity have transferred to the two test functions. -/
theorem pressure_time_identity_interval {T : ℝ} {u v : VelocityField}
    {p q : PressureField} {a : ℝ → ℝ} {ψ : Space → ℝ}
    (hT : 0 < T)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hdivu : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo 0 T, ∀ x,
      navierStokesResidual u p t x = navierStokesResidual v q t x)
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ t in (0 : ℝ)..T, a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x)) =
      (∫ t in (0 : ℝ)..T, a t * (∫ x, (u - v) (t, x) k * scalarLaplacian ψ x)) +
      (∫ t in (0 : ℝ)..T, deriv a t * (∫ x, (u - v) (t, x) k * ψ x)) +
      (∫ t in (0 : ℝ)..T, a t *
        (∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x)) := by
  let W : ℝ → ℝ := fun t => ∫ x, (u - v) (t, x) k * ψ x
  let D : ℝ → ℝ := fun t => ∫ x, temporalDerivative (u - v) t x k * ψ x
  let L : ℝ → ℝ := fun t => ∫ x, (u - v) (t, x) k * scalarLaplacian ψ x
  let G : ℝ → ℝ := fun t => ∑ i : Fin 3,
    ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x
  let P : ℝ → ℝ := fun t => ∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x
  have hW : ContinuousOn W (Icc 0 T) :=
    component_test_continuousOn (hu.sub hv).continuousOn hψ.continuous hcψ k
  have hD : ContinuousOn D (Ioo 0 T) :=
    component_time_test_continuousOn (hu.sub hv) hψ.continuous hcψ k
  have hL : ContinuousOn L (Icc 0 T) :=
    component_test_continuousOn (hu.sub hv).continuousOn
      (scalarLaplacian_contDiff hψ).continuous (compact_scalarLaplacian hcψ) k
  have hG : ContinuousOn G (Icc 0 T) :=
    continuousOn_finsetSum _ (fun i _ => tensor_test_continuousOn hu.continuousOn hv.continuousOn
      (spatial_partial_contDiff hψ i).continuous (CompactEnergy.compact_partial hcψ i) k i)
  have hparts : (∫ t in (0 : ℝ)..T, a t * D t) =
      -(∫ t in (0 : ℝ)..T, deriv a t * W t) :=
    compact_time_integration_by_parts hT ha hsupp hW hD
      (fun t ht => component_test_hasDerivAt (hu.sub hv) ht hψ hcψ k)
  have hiL : IntervalIntegrable (fun t => a t * L t) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT.le (ha.continuous.continuousOn.mul hL)
  have hiD : IntervalIntegrable (fun t => a t * D t) volume 0 T :=
    (continuous_cutoff_mul ha.continuous hD isOpen_Ioo hsupp).intervalIntegrable _ _
  have hiG : IntervalIntegrable (fun t => a t * G t) volume 0 T :=
    ContinuousOn.intervalIntegrable_of_Icc hT.le (ha.continuous.continuousOn.mul hG)
  have hiLD : IntervalIntegrable (fun t => a t * L t - a t * D t) volume 0 T := hiL.sub hiD
  have hpoint : (fun t => a t * P t) = (fun t => a t * L t - a t * D t + a t * G t) := by
    funext t
    by_cases ht : t ∈ Ioo 0 T
    · have h := weak_pressure_gradient_on_slab hu hv hp hq ht (hdivu t ht) (hdivv t ht)
        (hNS t ht) hψ hcψ k
      change P t = L t - D t + G t at h
      rw [h]
      ring
    · have hat : a t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hsupp h))
      simp only [hat, zero_mul, sub_zero, add_zero]
  change (∫ t in (0 : ℝ)..T, a t * P t) =
    (∫ t in (0 : ℝ)..T, a t * L t) + (∫ t in (0 : ℝ)..T, deriv a t * W t) +
      (∫ t in (0 : ℝ)..T, a t * G t)
  rw [hpoint, intervalIntegral.integral_add hiLD hiG, intervalIntegral.integral_sub hiL hiD,
    hparts]
  ring

/-- The same identity as an ordinary set integral over the closed time
interval, convenient for subsequent Fubini and norm estimates. -/
theorem pressure_time_identity {T : ℝ} {u v : VelocityField}
    {p q : PressureField} {a : ℝ → ℝ} {ψ : Space → ℝ}
    (hT : 0 < T)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hdivu : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo 0 T, ∀ x,
      navierStokesResidual u p t x = navierStokesResidual v q t x)
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ t in Icc (0 : ℝ) T, a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x)) =
      (∫ t in Icc (0 : ℝ) T, a t * (∫ x, (u - v) (t, x) k * scalarLaplacian ψ x)) +
      (∫ t in Icc (0 : ℝ) T, deriv a t * (∫ x, (u - v) (t, x) k * ψ x)) +
      (∫ t in Icc (0 : ℝ) T, a t *
        (∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x)) := by
  have h := pressure_time_identity_interval hT hu hv hp hq hdivu hdivv hNS ha hsupp hψ hcψ k
  simpa only [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc] using h

end NavierStokesR3.PressureTemporalIdentity
