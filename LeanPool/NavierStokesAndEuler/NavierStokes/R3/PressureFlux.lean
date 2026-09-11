/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelPairedBound
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelCommutator
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LpNormTools
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszPairing
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszTestOperators
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeightedInterpolation
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WeightedSobolev
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureFunctionals
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LocalizedTransport
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.GradientOperator
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFiniteEnergy
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HarmonicTestFunctionals
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszSymbolRegularity
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactTimeIntegral
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactSchwartz
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierTestDerivatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactEnergy
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ConservativeDifference
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Canonical pressure flux

The pressure is paired with compact smooth tests through its canonical Riesz
functional. Every integral used to split the weighted pairing is shown to be
integrable before its norm is estimated.
-/

section

/-!
# Compact time tests of the conservative pressure identity

The temporal test has topological support inside the open time interval. The
spatial test is smooth and compactly supported. Consequently all pairings are
ordinary Lebesgue integrals even when the pressure grows at spatial infinity.
-/

@[expose] public section

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

end
end

end

section

/-!
# Compact tests used in pressure recovery

Real compact smooth tests are embedded in the actual complex Schwartz space.
The differential operators commute with this embedding. The pressure identities
below continue to pair the physical pressure only with compact spatial tests.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.PressureRecovery

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open Comparison (ComplexTest tensorDiff)
open ConservativeDifference HarmonicTestFunctionals

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

/-- The canonical complex Schwartz test associated to a real compact test. -/
def realTest (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ComplexTest :=
  CompactSchwartz.ofCompactSupport (fun x => (ψ x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hψ)
    (hcψ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))

@[simp] theorem realTest_apply (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (x : Space) : realTest ψ hψ hcψ x = (ψ x : ℂ) := rfl

theorem realTest_compact (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) : HasCompactSupport (realTest ψ hψ hcψ : Space → ℂ) :=
  hcψ.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

theorem partial_ofReal {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (i : Fin 3) (x : Space) :
    spatialPartial i (fun y => (ψ y : ℂ)) x = ((spatialPartial i ψ x : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp x
    (hψ.differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun L : Space →L[ℝ] ℂ => L (coordinateVector i)) h

@[simp] theorem partialCLM_realTest (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin 3) :
    partialCLM i (realTest ψ hψ hcψ) =
      realTest (spatialPartial i ψ) (spatial_partial_contDiff hψ i)
        (CompactEnergy.compact_partial hcψ i) := by
  ext x
  exact partial_ofReal hψ i x

@[simp] theorem laplacianCLM_realTest (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) :
    laplacianCLM (realTest ψ hψ hcψ) =
      realTest (scalarLaplacian ψ) (scalarLaplacian_contDiff hψ) (compact_scalarLaplacian hcψ) := by
  ext x
  rw [laplacianCLM_apply, realTest_apply]
  simp only [scalarLaplacian, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  change spatialPartial i (fun y => spatialPartial i (fun z => (ψ z : ℂ)) y) x = _
  have he : (fun y => spatialPartial i (fun z => (ψ z : ℂ)) y) =
      (fun y => ((spatialPartial i ψ y : ℝ) : ℂ)) := funext (partial_ofReal hψ i)
  rw [he]
  exact partial_ofReal (spatial_partial_contDiff hψ i) i x

theorem partial_laplacian_realTest (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    partialCLM k (laplacianCLM (realTest ψ hψ hcψ)) =
      laplacianCLM (partialCLM k (realTest ψ hψ hcψ)) := by
  rw [laplacianCLM_realTest ψ hψ hcψ,
    partialCLM_realTest (scalarLaplacian ψ) (scalarLaplacian_contDiff hψ)
      (compact_scalarLaplacian hcψ) k,
    partialCLM_realTest ψ hψ hcψ k,
    laplacianCLM_realTest (spatialPartial k ψ) (spatial_partial_contDiff hψ k)
      (CompactEnergy.compact_partial hcψ k)]
  ext x
  exact congrArg Complex.ofReal (partial_scalarLaplacian hψ k x)

/-- A compact complex Schwartz test splits into two compact real tests. -/
theorem compact_test_decomposition (ψ : ComplexTest)
    (hcψ : HasCompactSupport (ψ : Space → ℂ)) :
    ψ = realTest (fun x => (ψ x).re) (Complex.reCLM.contDiff.comp ψ.smooth')
      (hcψ.comp_left (g := Complex.re) (by simp)) +
      Complex.I • realTest (fun x => (ψ x).im) (Complex.imCLM.contDiff.comp ψ.smooth')
        (hcψ.comp_left (g := Complex.im) (by simp)) := by
  ext x
  change ψ x = ((ψ x).re : ℂ) + Complex.I * ((ψ x).im : ℂ)
  apply Complex.ext <;> simp

/-- Compact harmonicity of a complex linear functional can be verified using
real scalar tests alone. -/
theorem compact_harmonic_of_real (F : ComplexTest →ₗ[ℂ] ℂ)
    (hreal : ∀ (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      F (laplacianCLM (realTest ψ hψ hcψ)) = 0) :
    ∀ ψ : ComplexTest, HasCompactSupport (ψ : Space → ℂ) → F (laplacianCLM ψ) = 0 := by
  intro ψ hcψ
  rw [compact_test_decomposition ψ hcψ]
  simp only [map_add, map_smul]
  rw [hreal (fun x => (ψ x).re) (Complex.reCLM.contDiff.comp ψ.smooth')
      (hcψ.comp_left (g := Complex.re) (by simp)),
    hreal (fun x => (ψ x).im) (Complex.imCLM.contDiff.comp ψ.smooth')
      (hcψ.comp_left (g := Complex.im) (by simp))]
  simp only [smul_zero, add_zero]

/-- The differentiated pressure Poisson equation, still tested only against
compact smooth functions. The derivative order agrees with the Riesz symbol. -/
theorem gradient_poisson_test {T t : ℝ} {u v : VelocityField}
    {p q : PressureField} {ψ : Space → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (ht : t ∈ Ioo 0 T)
    (hdivu : ∀ s ∈ Ioo 0 T, ∀ x, spatialDivergence u s x = 0)
    (hdivv : ∀ s ∈ Ioo 0 T, ∀ x, spatialDivergence v s x = 0)
    (hNS : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x, tensorDiff u v t i j x *
          spatialPartial i (spatialPartial j (spatialPartial k ψ)) x := by
  have hπ := (spatial_smooth hp (Ioo_subset_Icc_self ht)).sub
    (spatial_smooth hq (Ioo_subset_Icc_self ht))
  have hibp := CompactEnergy.integral_mul_partial (scalarLaplacian_contDiff hψ) hπ
    (compact_scalarLaplacian hcψ) k
  change (∫ x, scalarLaplacian ψ x * spatialPartial k (fun y => (p - q) (t, y)) x) =
    -(∫ x, (p - q) (t, x) * spatialPartial k (scalarLaplacian ψ) x) at hibp
  have hpoisson := weak_pressure_poisson (ψ := spatialPartial k ψ) hu hv hp hq ht hdivu hdivv hNS
    (spatial_partial_contDiff hψ k) (CompactEnergy.compact_partial hcψ k)
  calc
    _ = -(∫ x, (p - q) (t, x) * spatialPartial k (scalarLaplacian ψ) x) := by
      calc
        _ = ∫ x, scalarLaplacian ψ x * spatialPartial k (fun y => (p - q) (t, y)) x :=
          integral_congr_ae (Eventually.of_forall (fun x => mul_comm _ _))
        _ = _ := hibp
    _ = -(∫ x, (p - q) (t, x) * scalarLaplacian (spatialPartial k ψ) x) := by
      simp only [partial_scalarLaplacian hψ]
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x, tensorDiff u v t i j x *
          spatialPartial j (spatialPartial i (spatialPartial k ψ)) x := by
      rw [hpoisson, neg_neg]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [] with x
      rw [partial_comm (f := spatialPartial k ψ) (spatial_partial_contDiff hψ k) j i x]

/-- The compact physical pressure-gradient pairing is continuous at interior
times. Joint smoothness and the local equation suffice. -/
theorem pressure_gradient_pairing_continuousOn {T : ℝ} {u v : VelocityField}
    {p q : PressureField} {ψ : Space → ℝ}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hdivu : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0)
    (hdivv : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo 0 T, ∀ x,
      navierStokesResidual u p t x = navierStokesResidual v q t x)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ContinuousOn (fun t => ∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x)
      (Ioo 0 T) := by
  have hL := PressureTemporalIdentity.component_test_continuousOn (hu.sub hv).continuousOn
    (scalarLaplacian_contDiff hψ).continuous (compact_scalarLaplacian hcψ) k
  have hD := PressureTemporalIdentity.component_time_test_continuousOn (hu.sub hv)
    hψ.continuous hcψ k
  have hG : ContinuousOn (fun t => ∑ i : Fin 3,
      ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x) (Icc 0 T) :=
    continuousOn_finsetSum _ (fun i _ => PressureTemporalIdentity.tensor_test_continuousOn
      hu.continuousOn hv.continuousOn (spatial_partial_contDiff hψ i).continuous
        (CompactEnergy.compact_partial hcψ i) k i)
  apply ((hL.mono Ioo_subset_Icc_self).sub hD |>.add (hG.mono Ioo_subset_Icc_self)).congr
  intro t ht
  exact weak_pressure_gradient_on_slab hu hv hp hq ht (hdivu t ht) (hdivv t ht) (hNS t ht)
    hψ hcψ k

end NavierStokesR3.PressureRecovery

end
end

end

section

/-!
# Weak time continuity from uniform spatial `L¹` bounds

A jointly continuous scalar field with uniformly bounded spatial `L¹` norm
has continuous pairings with every continuous test vanishing at infinity.
Only the test is approximated by compactly supported functions; no support or
derivative bound is imposed on the field.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ZeroAtInfty

namespace NavierStokesR3.WeakTimeContinuity

open ProblemStatement ComparisonCutoffs

/-- A test function vanishing at infinity is bounded. -/
theorem exists_test_bound {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    ∃ C : ℝ, ∀ x : Space, ‖ψ x‖ ≤ C := by
  let ψ₀ : C₀(Space, ℂ) :=
    { toFun := ψ, continuous_toFun := hψ, zero_at_infty' := hψzero }
  obtain ⟨C, hC⟩ := ψ₀.isBounded_range.exists_norm_le
  exact ⟨C, fun x => hC (ψ x) ⟨x, rfl⟩⟩

/-- Pairing an `L¹` scalar field with a bounded continuous complex test is
integrable. -/
theorem integrable_pairing_of_bounded {f : Space → ℝ} (hf : Integrable f volume)
    {ψ : Space → ℂ} (hψ : Continuous ψ) (hbound : ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C) :
    Integrable (fun x : Space => (f x : ℂ) * ψ x) volume := by
  have hfC : Integrable (fun x : Space => (f x : ℂ)) volume := hf.ofReal
  obtain ⟨C, hC⟩ := hbound
  simpa only [mul_comm] using! hfC.bdd_mul hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- The original, untruncated pairing is a genuine Bochner integral. -/
theorem integrable_pairing {f : Space → ℝ} (hf : Integrable f volume)
    {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    Integrable (fun x : Space => (f x : ℂ) * ψ x) volume :=
  integrable_pairing_of_bounded hf hψ (exists_test_bound hψ hψzero)

/-- The compact approximation to the spatial test. -/
def cutoffTest (R : ℝ) (ψ : Space → ℂ) (x : Space) : ℂ :=
  (cutoff R x : ℂ) * ψ x

theorem cutoffTest_continuous {ψ : Space → ℂ} (hψ : Continuous ψ) (R : ℝ) :
    Continuous (cutoffTest R ψ) :=
  (Complex.continuous_ofReal.comp (cutoff_smooth R).continuous).mul hψ

theorem norm_cutoffTest_le (R : ℝ) (ψ : Space → ℂ) (x : Space) :
    ‖cutoffTest R ψ x‖ ≤ ‖ψ x‖ := by
  simp only [cutoffTest, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cutoff_nonneg R x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one R x)

theorem integrable_cutoff_pairing {f : Space → ℝ} (hf : Integrable f volume)
    {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) (R : ℝ) :
    Integrable (fun x : Space => (f x : ℂ) * cutoffTest R ψ x) volume := by
  obtain ⟨C, hC⟩ := exists_test_bound hψ hψzero
  exact integrable_pairing_of_bounded hf (cutoffTest_continuous hψ R)
    ⟨C, fun x => (norm_cutoffTest_le R ψ x).trans (hC x)⟩

/-- Cutting off the test cannot enlarge its pointwise error beyond its norm. -/
theorem norm_sub_cutoffTest_le (R : ℝ) (ψ : Space → ℂ) (x : Space) :
    ‖ψ x - cutoffTest R ψ x‖ ≤ ‖ψ x‖ := by
  have heq : ψ x - cutoffTest R ψ x = ((1 - cutoff R x : ℝ) : ℂ) * ψ x := by
    simp only [cutoffTest, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (cutoff_le_one R x))]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [cutoff_nonneg R x])

/-- The compact approximations converge uniformly on all of space. -/
theorem tendstoUniformly_cutoffTest {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    TendstoUniformly (fun R : ℝ => cutoffTest R ψ) ψ atTop := by
  let ψ₀ : C₀(Space, ℂ) :=
    { toFun := ψ, continuous_toFun := hψ, zero_at_infty' := hψzero }
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  obtain ⟨A, hA⟩ := ZeroAtInftyContinuousMapClass.norm_le ψ₀ ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop A] with R hR hAR
  intro x
  rw [dist_eq_norm]
  by_cases hx : ‖x‖ ≤ R
  · simp only [cutoffTest, cutoff_eq_one hR hx, Complex.ofReal_one, one_mul,
      sub_self, norm_zero]
    exact hε
  · exact (norm_sub_cutoffTest_le R ψ x).trans_lt
      (hA x (lt_of_le_of_lt hAR (lt_of_not_ge hx)))

/-- Uniform error in the test controls error in its pairing by the `L¹`
norm of the scalar field. -/
theorem norm_pairing_sub_le {f : Space → ℝ} (hf : Integrable f volume)
    {ψ φ : Space → ℂ}
    (hψ : Integrable (fun x : Space => (f x : ℂ) * ψ x) volume)
    (hφ : Integrable (fun x : Space => (f x : ℂ) * φ x) volume)
    {ε : ℝ} (herror : ∀ x : Space, ‖ψ x - φ x‖ ≤ ε) :
    ‖(∫ x : Space, (f x : ℂ) * ψ x) - (∫ x : Space, (f x : ℂ) * φ x)‖ ≤
      ε * ∫ x : Space, ‖f x‖ := by
  rw [← integral_sub hψ hφ]
  calc
    ‖∫ x : Space, (f x : ℂ) * ψ x - (f x : ℂ) * φ x‖
        ≤ ∫ x : Space, ε * ‖f x‖ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul ε)
      apply ae_of_all
      intro x
      rw [← mul_sub, norm_mul, Complex.norm_real]
      exact (mul_le_mul_of_nonneg_left (herror x) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = ε * ∫ x : Space, ‖f x‖ := integral_const_mul _ _

/-- Compactly truncated pairings are continuous on an arbitrary time set. -/
theorem continuousOn_cutoff_pairing {s : Set ℝ} {g : SpaceTime → ℝ}
    (hg : ContinuousOn g (s ×ˢ univ)) {ψ : Space → ℂ} (hψ : Continuous ψ)
    {R : ℝ} (hR : 0 < R) :
    ContinuousOn (fun t => ∫ x : Space, (g (t, x) : ℂ) * cutoffTest R ψ x) s := by
  apply CompactTimeIntegral.continuousOn_integral
    (F := fun z : SpaceTime => (g z : ℂ) * cutoffTest R ψ z.2)
    (isCompact_closedBall (0 : Space) (2 * R))
  · exact (Complex.continuous_ofReal.comp_continuousOn hg).mul
      ((cutoffTest_continuous hψ R).comp continuous_snd).continuousOn
  · intro t _ x hx
    have hxnorm : 2 * R ≤ ‖x‖ := by
      have : ¬ ‖x‖ ≤ 2 * R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      exact (lt_of_not_ge this).le
    simp only [cutoffTest, cutoff_eq_zero hR hxnorm, Complex.ofReal_zero, zero_mul, mul_zero]

/-- Uniform spatial `L¹` bounds upgrade compact-test continuity to continuity
for every continuous test vanishing at infinity. -/
theorem continuousOn_pairing {s : Set ℝ} {g : SpaceTime → ℝ} {M : ℝ}
    (hg : ContinuousOn g (s ×ˢ univ))
    (hints : ∀ t ∈ s, Integrable (fun x : Space => g (t, x)) volume)
    (hbound : ∀ t ∈ s, (∫ x : Space, ‖g (t, x)‖) ≤ M)
    {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    ContinuousOn (fun t => ∫ x : Space, (g (t, x) : ℂ) * ψ x) s := by
  have happrox := tendstoUniformly_cutoffTest hψ hψzero
  have hpair : TendstoUniformlyOn
      (fun R : ℝ => fun t => ∫ x : Space, (g (t, x) : ℂ) * cutoffTest R ψ x)
      (fun t => ∫ x : Space, (g (t, x) : ℂ) * ψ x) atTop s := by
    apply Metric.tendstoUniformlyOn_iff.2
    intro ε hε
    have hden : 0 < max M 0 + 1 := by positivity
    have hδ : 0 < ε / (max M 0 + 1) := div_pos hε hden
    filter_upwards [Metric.tendstoUniformly_iff.1 happrox (ε / (max M 0 + 1)) hδ]
      with R hR
    intro t ht
    have herror := norm_pairing_sub_le (hints t ht)
      (integrable_pairing (hints t ht) hψ hψzero)
      (integrable_cutoff_pairing (hints t ht) hψ hψzero R)
      (fun x => (show ‖ψ x - cutoffTest R ψ x‖ < ε / (max M 0 + 1) by
        simpa only [dist_eq_norm] using hR x).le)
    calc
      dist (∫ x : Space, (g (t, x) : ℂ) * ψ x)
          (∫ x : Space, (g (t, x) : ℂ) * cutoffTest R ψ x)
          ≤ ε / (max M 0 + 1) * ∫ x : Space, ‖g (t, x)‖ := by
        simpa only [dist_eq_norm] using herror
      _ ≤ ε / (max M 0 + 1) * max M 0 :=
        mul_le_mul_of_nonneg_left ((hbound t ht).trans (le_max_left _ _)) hδ.le
      _ < ε / (max M 0 + 1) * (max M 0 + 1) :=
        mul_lt_mul_of_pos_left (lt_add_one _) hδ
      _ = ε := div_mul_cancel₀ ε hden.ne'
  exact hpair.continuousOn ((eventually_gt_atTop (0 : ℝ)).mono
    (fun _ hR => continuousOn_cutoff_pairing hg hψ hR)).frequently

end NavierStokesR3.WeakTimeContinuity

end
end

end

section

/-!
# Pressure recovery for smooth finite-energy comparisons

The physical pressure is tested only against compact smooth functions. Its
canonical representative is recovered from the conservative equation, time
averaging, and the vanishing theorem for harmonic Sobolev-bounded functionals.
-/

section

/-!
# Time averages of finite-energy fields

These averages use the ordinary Bochner integral on a finite closed time
interval. Their spatial integrability follows from joint continuity and the
uniform spatial integral bounds; no time derivative or global spatial
derivative bound is used.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The time average against a scalar weight on the comparison interval. -/
def timeAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (a : ℝ → ℝ) (f : SpaceTime → E) (x : Space) : E :=
  ∫ t in Icc 0 T, a t • f (t, x)

/-- Joint continuity supplies measurability for the product of restricted
time measure and ordinary spatial volume. -/
theorem aestronglyMeasurable_slab {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {f : SpaceTime → E} (hf : ContinuousOn f (slab 0 T)) :
    AEStronglyMeasurable f
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)) := by
  rw [Measure.restrict_prod_eq_prod_univ]
  exact hf.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)

/-- An integrable bound on the spatial norm integrals proves integrability on
the whole slab. -/
theorem integrable_slab_of_integral_norm_le {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {f : SpaceTime → E} {B : ℝ → ℝ}
    (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hB : IntegrableOn B (Icc 0 T))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ B t) :
    Integrable f
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)) := by
  have hmeas := aestronglyMeasurable_slab hf
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hslice t ht
  · apply hB.mono' hmeas.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun x : Space => norm_nonneg (f (t, x))))]
      using hbound t ht

/-- Weighting by a continuous scalar preserves slab continuity. -/
theorem continuousOn_time_weight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T)) :
    ContinuousOn (fun z : SpaceTime => a z.1 • f z) (slab 0 T) :=
  (ha.comp continuous_fst.continuousOn (fun _ hz => hz.1)).smul hf

/-- Each time slice at a fixed spatial point is integrable, including at the
endpoints of the closed time interval. -/
theorem timeAverage_timeSlice_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T)) (x : Space) :
    IntegrableOn (fun t => a t • f (t, x)) (Icc 0 T) :=
  (ha.smul (hf.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ⟨ht, mem_univ x⟩))).integrableOn_Icc

/-- Bounded linear maps commute with these time averages pointwise. -/
theorem timeAverage_continuousLinearMap {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {T : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (L : E →L[ℝ] F) (x : Space) :
    timeAverage T a (fun z => L (f z)) x = L (timeAverage T a f x) := by
  simpa only [timeAverage, map_smul] using
    L.integral_comp_comm (timeAverage_timeSlice_integrable ha hf x)

/-- A field with a uniform spatial `L¹` bound has an integrable weighted
integrand on the time-space slab. -/
theorem timeAverage_integrand_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ M) :
    Integrable (fun z : SpaceTime => a z.1 • f z)
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)) := by
  apply integrable_slab_of_integral_norm_le (continuousOn_time_weight ha hf)
    (fun t ht => (hslice t ht).smul (a t))
    (ha.norm.integrableOn_Icc.mul_const M)
  intro t ht
  simp only [norm_smul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hbound t ht) (norm_nonneg _)

/-- The time average of a uniformly `L¹` field lies in spatial `L¹`. -/
theorem timeAverage_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ M) :
    Integrable (timeAverage T a f) :=
  (timeAverage_integrand_integrable ha hf hslice hbound).integral_prod_right

/-- The spatial `L¹` norm of an average is bounded by the uniform spatial
norm bound times the time integral of the weight's absolute value. -/
theorem timeAverage_norm_integral_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ M) :
    (∫ x : Space, ‖timeAverage T a f x‖) ≤ M * ∫ t in Icc 0 T, ‖a t‖ := by
  have hF := timeAverage_integrand_integrable ha hf hslice hbound
  calc
    (∫ x : Space, ‖timeAverage T a f x‖) ≤
        ∫ x : Space, ∫ t in Icc 0 T, ‖a t • f (t, x)‖ :=
      integral_mono hF.integral_prod_right.norm hF.integral_norm_prod_right
        (fun x => norm_integral_le_integral_norm (fun t => a t • f (t, x)))
    _ = ∫ t in Icc 0 T, ∫ x : Space, ‖a t • f (t, x)‖ :=
      (integral_integral_swap hF.norm).symm
    _ ≤ ∫ t in Icc 0 T, ‖a t‖ * M := by
      apply integral_mono_ae hF.integral_norm_prod_left (ha.norm.integrableOn_Icc.mul_const M)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [norm_smul, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hbound t ht) (norm_nonneg _)
    _ = M * ∫ t in Icc 0 T, ‖a t‖ := by rw [integral_mul_const]; ring

/-- Fubini for a uniformly `L¹` field and a continuous time weight. -/
theorem integral_timeAverage_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ M) :
    (∫ x : Space, timeAverage T a f x) =
      ∫ t in Icc 0 T, a t • (∫ x : Space, f (t, x)) := by
  have hF := timeAverage_integrand_integrable ha hf hslice hbound
  change (∫ x : Space, ∫ t in Icc 0 T, a t • f (t, x)) = _
  rw [← integral_integral_swap hF]
  simp only [integral_smul]

/-- Cauchy--Schwarz for a Bochner integral over a finite measure space. -/
theorem norm_integral_sq_le_measure_mul_integral_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → E} (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ μ.real univ * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hholder : (∫ x, ‖f x‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (f := fun x => ‖f x‖) (g := fun _ : α => (1 : ℝ))
      (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))
      (Filter.Eventually.of_forall (fun _ : α => zero_le_one))
      (by simpa using hf.norm)
      (by simpa using (memLp_const (μ := μ) (p := (2 : ℝ≥0∞)) (1 : ℝ)))
    simpa only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul,
      ← Real.sqrt_eq_rpow] using h
  have hnorm := (norm_integral_le_integral_norm f).trans hholder
  have hsq := mul_self_le_mul_self (norm_nonneg (∫ x, f x ∂μ)) hnorm
  have hsq' : ‖∫ x, f x ∂μ‖ ^ 2 ≤
      (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ)) ^ 2 := by
    simpa only [pow_two] using hsq
  calc
    ‖∫ x, f x ∂μ‖ ^ 2 ≤
        (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ)) ^ 2 := hsq'
    _ = μ.real univ * ∫ x, ‖f x‖ ^ 2 ∂μ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖f x‖)),
        Real.sq_sqrt (show 0 ≤ μ.real univ from ENNReal.toReal_nonneg)]
      ring

/-- Integrating in the finite time variable sends a square-integrable joint
field to a square-integrable spatial field. -/
theorem memLp_two_timeIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} {f : SpaceTime → E}
    (hf : AEStronglyMeasurable f
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)))
    (hsq : Integrable (fun z : SpaceTime => ‖f z‖ ^ 2)
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space))) :
    MemLp (fun x : Space => ∫ t in Icc 0 T, f (t, x)) 2 volume := by
  have havg := hf.prod_swap.integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm havg).2
  apply (hsq.integral_prod_right.const_mul
    (((volume : Measure ℝ).restrict (Icc 0 T)).real univ)).mono' (havg.norm.pow 2)
  filter_upwards [hsq.prod_left_ae, hf.prod_swap.prodMk_left] with x hxint hxmeas
  have hxtwo := (memLp_two_iff_integrable_sq_norm hxmeas).2 hxint
  simpa only [Pi.pow_apply, norm_pow, norm_norm, Prod.swap_prod_mk] using
    norm_integral_sq_le_measure_mul_integral_sq hxtwo

/-- The quantitative estimate behind square-integrability of the time
integral. -/
theorem l2Sq_timeIntegral_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} {f : SpaceTime → E}
    (hf : AEStronglyMeasurable f
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)))
    (hsq : Integrable (fun z : SpaceTime => ‖f z‖ ^ 2)
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space))) :
    l2Sq (fun x : Space => ∫ t in Icc 0 T, f (t, x)) ≤
      ((volume : Measure ℝ).restrict (Icc 0 T)).real univ *
        ∫ t in Icc 0 T, ∫ x : Space, ‖f (t, x)‖ ^ 2 := by
  have hAvg := memLp_two_timeIntegral hf hsq
  have hAvgSq := (memLp_two_iff_integrable_sq_norm hAvg.1).1 hAvg
  calc
    l2Sq (fun x : Space => ∫ t in Icc 0 T, f (t, x)) ≤
        ∫ x : Space, ((volume : Measure ℝ).restrict (Icc 0 T)).real univ *
          ∫ t in Icc 0 T, ‖f (t, x)‖ ^ 2 := by
      apply integral_mono_ae hAvgSq (hsq.integral_prod_right.const_mul _)
      filter_upwards [hsq.prod_left_ae, hf.prod_swap.prodMk_left] with x hxint hxmeas
      have hxtwo := (memLp_two_iff_integrable_sq_norm hxmeas).2 hxint
      simpa only [Prod.swap_prod_mk] using norm_integral_sq_le_measure_mul_integral_sq hxtwo
    _ = ((volume : Measure ℝ).restrict (Icc 0 T)).real univ *
        ∫ t in Icc 0 T, ∫ x : Space, ‖f (t, x)‖ ^ 2 := by
      rw [integral_const_mul, ← integral_integral_swap hsq]

/-- Squared norm integrability of the weighted joint field follows from a
uniform spatial square-integral bound. -/
theorem timeAverage_integrand_integrable_sq_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖ ^ 2) ≤ M) :
    Integrable (fun z : SpaceTime => ‖a z.1 • f z‖ ^ 2)
      (((volume : Measure ℝ).restrict (Icc 0 T)).prod (volume : Measure Space)) := by
  have hslices : ∀ t ∈ Icc 0 T,
      Integrable (fun x : Space => ‖a t • f (t, x)‖ ^ 2) := by
    intro t ht
    simpa only [norm_smul, mul_pow] using (hslice t ht).const_mul (‖a t‖ ^ 2)
  apply integrable_slab_of_integral_norm_le (continuousOn_time_weight ha hf |>.norm.pow 2)
    hslices ((ha.norm.pow 2).integrableOn_Icc.mul_const M)
  intro t ht
  simp only [Pi.pow_apply, norm_pow, norm_norm, norm_smul, mul_pow, norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hbound t ht) (sq_nonneg _)

/-- The time average of a uniformly square-integrable field lies in spatial
`L²`. -/
theorem timeAverage_memLp_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖ ^ 2) ≤ M) :
    MemLp (timeAverage T a f) 2 volume :=
  memLp_two_timeIntegral (aestronglyMeasurable_slab (continuousOn_time_weight ha hf))
    (timeAverage_integrand_integrable_sq_norm ha hf hslice hbound)

/-- A quantitative square-integral estimate using only the time weight and
the uniform spatial square-integral bound. -/
theorem timeAverage_l2Sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T M : ℝ} {a : ℝ → ℝ} {f : SpaceTime → E}
    (hT : 0 ≤ T) (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖ ^ 2) ≤ M) :
    l2Sq (timeAverage T a f) ≤ T * M * ∫ t in Icc 0 T, ‖a t‖ ^ 2 := by
  have hF := aestronglyMeasurable_slab (continuousOn_time_weight ha hf)
  have hFsq := timeAverage_integrand_integrable_sq_norm ha hf hslice hbound
  have hvol : ((volume : Measure ℝ).restrict (Icc 0 T)).real univ = T := by
    simp only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal hT]
  calc
    l2Sq (timeAverage T a f) ≤ T *
        ∫ t in Icc 0 T, ∫ x : Space, ‖a t • f (t, x)‖ ^ 2 := by
      simpa only [hvol, timeAverage] using! l2Sq_timeIntegral_le hF hFsq
    _ ≤ T * ∫ t in Icc 0 T, ‖a t‖ ^ 2 * M := by
      apply mul_le_mul_of_nonneg_left _ hT
      apply integral_mono_ae hFsq.integral_prod_left
        ((ha.norm.pow 2).integrableOn_Icc.mul_const M)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [norm_smul, mul_pow, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hbound t ht) (sq_nonneg _)
    _ = T * M * ∫ t in Icc 0 T, ‖a t‖ ^ 2 := by rw [integral_mul_const]; ring

/-- Uniform finite kinetic energy gives square-integrability of every
continuously weighted time average of a velocity. -/
theorem timeAverage_memLp_two_of_uniformFiniteEnergy {T : ℝ} {a : ℝ → ℝ}
    {u : VelocityField} (ha : ContinuousOn a (Icc 0 T))
    (hu_cont : ContinuousOn u (slab 0 T)) (hu : UniformFiniteEnergy (Icc 0 T) u) :
    MemLp (timeAverage T a u) 2 volume := by
  obtain ⟨M, _, hM⟩ := uniformFiniteEnergy_l2Sq_bound hu
  exact timeAverage_memLp_two ha hu_cont (fun t ht => (hM t ht).1)
    (fun t ht => (hM t ht).2)

/-- In particular, the averaged difference of two finite-energy velocities
belongs to spatial `L²`. The weight can equally be a continuous derivative of
a smooth time test function. -/
theorem timeAverage_difference_memLp_two {T : ℝ} {a : ℝ → ℝ}
    {u v : VelocityField} (ha : ContinuousOn a (Icc 0 T))
    (hu_cont : ContinuousOn u (slab 0 T)) (hv_cont : ContinuousOn v (slab 0 T))
    (hu : UniformFiniteEnergy (Icc 0 T) u) (hv : UniformFiniteEnergy (Icc 0 T) v) :
    MemLp (timeAverage T a (fun z => u z - v z)) 2 volume :=
  timeAverage_memLp_two_of_uniformFiniteEnergy ha (hu_cont.sub hv_cont)
    (uniformFiniteEnergy_sub_of_continuousOn hu_cont hv_cont hu hv)

/-- A uniform finite-energy bound also bounds every scalar coordinate's
ordinary spatial square integral. -/
theorem uniformFiniteEnergy_component_l2Sq_bound {T : ℝ} {u : VelocityField}
    (hu_cont : ContinuousOn u (slab 0 T)) (hu : UniformFiniteEnergy (Icc 0 T) u)
    (k : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T,
      Integrable (fun x : Space => ‖u (t, x) k‖ ^ 2) ∧
        (∫ x : Space, ‖u (t, x) k‖ ^ 2) ≤ M := by
  obtain ⟨M, hM0, hM⟩ := uniformFiniteEnergy_l2Sq_bound hu
  refine ⟨M, hM0, ?_⟩
  intro t ht
  have humeas : AEStronglyMeasurable (fun x : Space => u (t, x)) volume :=
    (continuous_slice_of_continuousOn hu_cont ht).aestronglyMeasurable
  have huLp := (squareIntegrableAtTime_iff_memLp humeas).1 (hM t ht).1
  have hscalarmeas :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable humeas
  have hscalar := huLp.of_le hscalarmeas
    (Filter.Eventually.of_forall (fun x : Space => PiLp.norm_apply_le (u (t, x)) k))
  have hscalarSq := (memLp_two_iff_integrable_sq_norm hscalar.1).1 hscalar
  refine ⟨hscalarSq, ?_⟩
  apply le_trans (integral_mono hscalarSq (hM t ht).1 ?_) (hM t ht).2
  intro x
  simpa only [pow_two, EuclideanSpace.coe_proj] using
    mul_self_le_mul_self (norm_nonneg (u (t, x) k)) (PiLp.norm_apply_le (u (t, x)) k)

/-- Coordinate square-integral bounds for the difference field. -/
theorem uniformFiniteEnergy_difference_component_l2Sq_bound {T : ℝ}
    {u v : VelocityField}
    (hu_cont : ContinuousOn u (slab 0 T)) (hv_cont : ContinuousOn v (slab 0 T))
    (hu : UniformFiniteEnergy (Icc 0 T) u) (hv : UniformFiniteEnergy (Icc 0 T) v)
    (k : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T,
      Integrable (fun x : Space => ‖(u (t, x) - v (t, x)) k‖ ^ 2) ∧
        (∫ x : Space, ‖(u (t, x) - v (t, x)) k‖ ^ 2) ≤ M :=
  uniformFiniteEnergy_component_l2Sq_bound (hu_cont.sub hv_cont)
    (uniformFiniteEnergy_sub_of_continuousOn hu_cont hv_cont hu hv) k

/-- A scalar coordinate of the averaged difference is in `L²`, including
when the continuous weight is a derivative of a time test function. -/
theorem timeAverage_difference_component_memLp_two {T : ℝ} {a : ℝ → ℝ}
    {u v : VelocityField} (ha : ContinuousOn a (Icc 0 T))
    (hu_cont : ContinuousOn u (slab 0 T)) (hv_cont : ContinuousOn v (slab 0 T))
    (hu : UniformFiniteEnergy (Icc 0 T) u) (hv : UniformFiniteEnergy (Icc 0 T) v)
    (k : Fin 3) :
    MemLp (timeAverage T a (fun z : SpaceTime => (u z - v z) k)) 2 volume := by
  obtain ⟨M, _, hM⟩ :=
    uniformFiniteEnergy_difference_component_l2Sq_bound hu_cont hv_cont hu hv k
  exact timeAverage_memLp_two ha
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn (hu_cont.sub hv_cont))
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2)

/-- Each nonlinear tensor component is jointly continuous on the slab. -/
theorem continuousOn_tensorDiff_field {T : ℝ} {u v : VelocityField}
    (hu : ContinuousOn u (slab 0 T)) (hv : ContinuousOn v (slab 0 T))
    (i j : Fin 3) :
    ContinuousOn (fun z : SpaceTime => tensorDiff u v z.1 i j z.2) (slab 0 T) := by
  have hui := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_continuousOn hu
  have huj := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_continuousOn hu
  have hvi := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_continuousOn hv
  have hvj := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_continuousOn hv
  simpa only [tensorDiff, Prod.mk.eta, Pi.sub_apply, Pi.mul_apply, Function.comp_def,
      EuclideanSpace.coe_proj] using! (hui.mul huj).sub (hvi.mul hvj)

/-- Uniform finite kinetic energy gives spatial `L¹` for each averaged
nonlinear tensor component. -/
theorem timeAverage_tensorDiff_integrable {T : ℝ} {a : ℝ → ℝ}
    {u v : VelocityField} (ha : ContinuousOn a (Icc 0 T))
    (hu_cont : ContinuousOn u (slab 0 T)) (hv_cont : ContinuousOn v (slab 0 T))
    (hu : UniformFiniteEnergy (Icc 0 T) u) (hv : UniformFiniteEnergy (Icc 0 T) v)
    (i j : Fin 3) :
    Integrable (timeAverage T a (fun z : SpaceTime => tensorDiff u v z.1 i j z.2)) := by
  obtain ⟨M, _, hM⟩ := uniformFiniteEnergy_tensorDiff_bound
    (fun t ht => (continuous_slice_of_continuousOn hu_cont ht).aestronglyMeasurable)
    (fun t ht => (continuous_slice_of_continuousOn hv_cont ht).aestronglyMeasurable) hu hv
  exact timeAverage_integrable ha (continuousOn_tensorDiff_field hu_cont hv_cont i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)

/-- A deliberately coarse bound for the `L¹` norm of an `L²` pairing. It is
sufficient for the Fubini argument and uses no pointwise bound on either field. -/
theorem l2_inner_integrable_and_norm_integral_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f g : Space → E} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    Integrable (fun x => ⟪f x, g x⟫_ℝ) ∧
      (∫ x : Space, ‖⟪f x, g x⟫_ℝ‖) ≤ l2Sq f + l2Sq g := by
  have hf_sq := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hg_sq := (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  have hpoint (x : Space) : ‖⟪f x, g x⟫_ℝ‖ ≤ ‖f x‖ ^ 2 + ‖g x‖ ^ 2 := by
    apply (norm_inner_le_norm (f x) (g x)).trans
    nlinarith [sq_nonneg (‖f x‖ - ‖g x‖), mul_nonneg (norm_nonneg (f x)) (norm_nonneg (g x))]
  have hint := (hf_sq.add hg_sq).mono' (hf.1.inner hg.1) (Filter.Eventually.of_forall hpoint)
  refine ⟨hint, ?_⟩
  calc
    (∫ x : Space, ‖⟪f x, g x⟫_ℝ‖) ≤ ∫ x : Space, ‖f x‖ ^ 2 + ‖g x‖ ^ 2 :=
      integral_mono hint.norm (hf_sq.add hg_sq) hpoint
    _ = l2Sq f + l2Sq g := integral_add hf_sq hg_sq

/-- The spatial `L²` pairing commutes with time averaging. Compact smooth
spatial tests are covered as a special case of a continuous `L²` test. -/
theorem timeAverage_inner_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {T M : ℝ} {a : ℝ → ℝ}
    {f : SpaceTime → E} {ψ : Space → E}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖ ^ 2) ≤ M)
    (hψcont : Continuous ψ) (hψ : MemLp ψ 2 volume) :
    (∫ x : Space, ⟪ψ x, timeAverage T a f x⟫_ℝ) =
      ∫ t in Icc 0 T, a t * (∫ x : Space, ⟪ψ x, f (t, x)⟫_ℝ) := by
  have hflp (t : ℝ) (ht : t ∈ Icc 0 T) : MemLp (fun x : Space => f (t, x)) 2 volume := by
    have hfc : ContinuousOn (fun x : Space => f (t, x)) univ :=
      hf.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x _ => ⟨ht, mem_univ x⟩)
    have hfm : AEStronglyMeasurable (fun x : Space => f (t, x)) volume := by
      simpa only [Measure.restrict_univ] using hfc.aestronglyMeasurable MeasurableSet.univ
    exact (memLp_two_iff_integrable_sq_norm hfm).2 (hslice t ht)
  have hpaircont : ContinuousOn (fun z : SpaceTime => ⟪ψ z.2, f z⟫_ℝ) (slab 0 T) :=
    (hψcont.comp continuous_snd).continuousOn.inner hf
  have hpair (t : ℝ) (ht : t ∈ Icc 0 T) :=
    l2_inner_integrable_and_norm_integral_le hψ (hflp t ht)
  have hpairbound (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ x : Space, ‖⟪ψ x, f (t, x)⟫_ℝ‖) ≤ l2Sq ψ + M :=
    (hpair t ht).2.trans (add_le_add_right (hbound t ht) (l2Sq ψ))
  have havg (x : Space) :
      timeAverage T a (fun z : SpaceTime => ⟪ψ z.2, f z⟫_ℝ) x =
        ⟪ψ x, timeAverage T a f x⟫_ℝ := by
    simpa only [timeAverage, inner_smul_right, smul_eq_mul] using
      integral_inner (𝕜 := ℝ) (timeAverage_timeSlice_integrable ha hf x) (ψ x)
  calc
    (∫ x : Space, ⟪ψ x, timeAverage T a f x⟫_ℝ) =
        ∫ x : Space, timeAverage T a (fun z : SpaceTime => ⟪ψ z.2, f z⟫_ℝ) x :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => (havg x).symm))
    _ = ∫ t in Icc 0 T, a t * (∫ x : Space, ⟪ψ x, f (t, x)⟫_ℝ) := by
      simpa only [smul_eq_mul] using
        integral_timeAverage_eq ha hpaircont (fun t ht => (hpair t ht).1) hpairbound

/-- A complex scalar spatial test factors out of the time integral. -/
theorem timeAverage_complex_mul (T : ℝ) (a : ℝ → ℝ) (f : SpaceTime → ℝ)
    (ψ : Space → ℂ) (x : Space) :
    timeAverage T a (fun z : SpaceTime => (f z : ℂ) * ψ z.2) x =
      ((timeAverage T a f x : ℝ) : ℂ) * ψ x := by
  change (∫ t in Icc 0 T, a t • ((f (t, x) : ℂ) * ψ x)) = _
  calc
    (∫ t in Icc 0 T, a t • ((f (t, x) : ℂ) * ψ x)) =
        ∫ t in Icc 0 T, ((a t * f (t, x) : ℝ) : ℂ) * ψ x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        simp only [Complex.real_smul, Complex.ofReal_mul, mul_assoc])
    _ = (∫ t in Icc 0 T, ((a t * f (t, x) : ℝ) : ℂ)) * ψ x := integral_mul_const _ _
    _ = ((timeAverage T a f x : ℝ) : ℂ) * ψ x := by rw [integral_complex_ofReal]; rfl

/-- Fubini for a complex spatial test once the tested field has a uniform
spatial `L¹` bound. -/
theorem timeAverage_complex_pairing_of_integrable {T M : ℝ} {a : ℝ → ℝ}
    {f : SpaceTime → ℝ} {ψ : Space → ℂ}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hψ : Continuous ψ)
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => (f (t, x) : ℂ) * ψ x))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖(f (t, x) : ℂ) * ψ x‖) ≤ M) :
    (∫ x : Space, ((timeAverage T a f x : ℝ) : ℂ) * ψ x) =
      ∫ t in Icc 0 T, (a t : ℂ) * (∫ x : Space, (f (t, x) : ℂ) * ψ x) := by
  have hpaircont : ContinuousOn (fun z : SpaceTime => (f z : ℂ) * ψ z.2) (slab 0 T) :=
    (Complex.continuous_ofReal.comp_continuousOn hf).mul
      (hψ.comp continuous_snd).continuousOn
  simpa only [timeAverage_complex_mul, Complex.real_smul] using
    integral_timeAverage_eq ha hpaircont hslice hbound

/-- Uniformly `L¹` real fields may be tested against every bounded continuous
complex function before interchanging the time and spatial integrals. -/
theorem timeAverage_complex_pairing_of_bounded {T M : ℝ} {a : ℝ → ℝ}
    {f : SpaceTime → ℝ} {ψ : Space → ℂ}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => f (t, x)))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖) ≤ M)
    (hψ : Continuous ψ) (hψbound : ∃ C : ℝ, ∀ x : Space, ‖ψ x‖ ≤ C) :
    (∫ x : Space, ((timeAverage T a f x : ℝ) : ℂ) * ψ x) =
      ∫ t in Icc 0 T, (a t : ℂ) * (∫ x : Space, (f (t, x) : ℂ) * ψ x) := by
  obtain ⟨C, hC⟩ := hψbound
  have hC0 : 0 ≤ C := (norm_nonneg (ψ 0)).trans (hC 0)
  have hpair (t : ℝ) (ht : t ∈ Icc 0 T) :
      Integrable (fun x : Space => (f (t, x) : ℂ) * ψ x) := by
    simpa only [mul_comm] using!
      (hslice t ht).ofReal.bdd_mul hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  apply timeAverage_complex_pairing_of_integrable ha hf hψ hpair
    (M := C * M)
  intro t ht
  calc
    (∫ x : Space, ‖(f (t, x) : ℂ) * ψ x‖) ≤
        ∫ x : Space, C * ‖f (t, x)‖ := by
      apply integral_mono (hpair t ht).norm ((hslice t ht).norm.const_mul C)
      intro x
      change ‖(f (t, x) : ℂ) * ψ x‖ ≤ C * ‖f (t, x)‖
      rw [norm_mul, Complex.norm_real]
      exact (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = C * ∫ x : Space, ‖f (t, x)‖ := integral_const_mul _ _
    _ ≤ C * M := mul_le_mul_of_nonneg_left (hbound t ht) hC0

/-- Spatial `L²` control makes a scalar field times a complex `L²` test
integrable, with a coarse bound sufficient for Fubini. -/
theorem l2_complex_mul_integrable_and_norm_integral_le {f : Space → ℝ} {ψ : Space → ℂ}
    (hf : MemLp f 2 volume) (hψ : MemLp ψ 2 volume) :
    Integrable (fun x : Space => (f x : ℂ) * ψ x) ∧
      (∫ x : Space, ‖(f x : ℂ) * ψ x‖) ≤ l2Sq f + l2Sq ψ := by
  have hf_sq := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hψ_sq := (memLp_two_iff_integrable_sq_norm hψ.1).1 hψ
  have hpoint (x : Space) : ‖(f x : ℂ) * ψ x‖ ≤ ‖f x‖ ^ 2 + ‖ψ x‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real]
    nlinarith [sq_nonneg (‖f x‖ - ‖ψ x‖), mul_nonneg (norm_nonneg (f x)) (norm_nonneg (ψ x))]
  have hmeas := (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1).mul hψ.1
  have hint := (hf_sq.add hψ_sq).mono' hmeas (Filter.Eventually.of_forall hpoint)
  refine ⟨hint, ?_⟩
  calc
    (∫ x : Space, ‖(f x : ℂ) * ψ x‖) ≤ ∫ x : Space, ‖f x‖ ^ 2 + ‖ψ x‖ ^ 2 :=
      integral_mono hint.norm (hf_sq.add hψ_sq) hpoint
    _ = l2Sq f + l2Sq ψ := integral_add hf_sq hψ_sq

/-- A uniformly square-integrable real field can be paired with a continuous
complex `L²` spatial test before interchanging time and space. -/
theorem timeAverage_complex_pairing_of_memLp_two {T M : ℝ} {a : ℝ → ℝ}
    {f : SpaceTime → ℝ} {ψ : Space → ℂ}
    (ha : ContinuousOn a (Icc 0 T)) (hf : ContinuousOn f (slab 0 T))
    (hslice : ∀ t ∈ Icc 0 T, Integrable (fun x : Space => ‖f (t, x)‖ ^ 2))
    (hbound : ∀ t ∈ Icc 0 T, (∫ x : Space, ‖f (t, x)‖ ^ 2) ≤ M)
    (hψcont : Continuous ψ) (hψ : MemLp ψ 2 volume) :
    (∫ x : Space, ((timeAverage T a f x : ℝ) : ℂ) * ψ x) =
      ∫ t in Icc 0 T, (a t : ℂ) * (∫ x : Space, (f (t, x) : ℂ) * ψ x) := by
  have hflp (t : ℝ) (ht : t ∈ Icc 0 T) : MemLp (fun x : Space => f (t, x)) 2 volume := by
    have hfc : ContinuousOn (fun x : Space => f (t, x)) univ :=
      hf.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x _ => ⟨ht, mem_univ x⟩)
    have hfm : AEStronglyMeasurable (fun x : Space => f (t, x)) volume := by
      simpa only [Measure.restrict_univ] using hfc.aestronglyMeasurable MeasurableSet.univ
    exact (memLp_two_iff_integrable_sq_norm hfm).2 (hslice t ht)
  have hpair (t : ℝ) (ht : t ∈ Icc 0 T) :=
    l2_complex_mul_integrable_and_norm_integral_le (hflp t ht) hψ
  apply timeAverage_complex_pairing_of_integrable ha hf hψcont (fun t ht => (hpair t ht).1)
    (M := M + l2Sq ψ)
  intro t ht
  exact (hpair t ht).2.trans (add_le_add_left (hbound t ht) (l2Sq ψ))

end NavierStokesR3.Comparison

end
end

end

section

/-! # Pointwise recovery from compact temporal tests -/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokesR3.TemporalTestUniqueness

/-- Continuity turns the distributional fundamental lemma into equality at
every time of the open interval. The tests are real, and values may be complex. -/
theorem eq_zero_on_open_of_tests {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℂ}
    (hf : ContinuousOn f U)
    (htest : ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ U →
      (∫ t : ℝ, a t • f t) = 0) :
    ∀ t ∈ U, f t = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hf.locallyIntegrableOn hU.measurableSet) htest
  have hrestr : f =ᵐ[volume.restrict U] (fun _ => (0 : ℂ)) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hU.measurableSet] with t ht htU
    exact ht htU
  exact Measure.eqOn_open_of_ae_eq hrestr hU hf continuousOn_const

/-- A compact temporal test supported in `(0,T)` has the same integral over
`[0,T]` as over the line. No integrability of the untested function is needed. -/
theorem integral_eq_setIntegral {T : ℝ} {a : ℝ → ℝ} {f : ℝ → ℂ}
    (hs : tsupport a ⊆ Ioo (0 : ℝ) T) :
    (∫ t : ℝ, a t • f t) = ∫ t in Icc (0 : ℝ) T, a t • f t := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  have ha : a t = 0 := image_eq_zero_of_notMem_tsupport fun h =>
    ht (Ioo_subset_Icc_self (hs h))
  simp only [ha, zero_smul]

theorem eq_zero_on_Ioo_of_setIntegral_tests {T : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo (0 : ℝ) T))
    (htest : ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a →
      tsupport a ⊆ Ioo (0 : ℝ) T →
      (∫ t in Icc (0 : ℝ) T, a t • f t) = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, f t = 0 := by
  apply eq_zero_on_open_of_tests isOpen_Ioo hf
  intro a ha hc hs
  rw [integral_eq_setIntegral hs]
  exact htest a ha hc hs

end NavierStokesR3.TemporalTestUniqueness

end
end

end

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.PressureRecovery

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open Comparison ConservativeDifference HarmonicTestFunctionals PressureFunctionals

/-- These are exactly the local smooth equation and uniform finite-energy
hypotheses of the comparison argument. -/
structure Hypotheses (T : ℝ) (u v : VelocityField) (p q : PressureField) : Prop where
  positive : 0 < T
  smooth_u : ContDiffOn ℝ ∞ u (Comparison.slab 0 T)
  smooth_v : ContDiffOn ℝ ∞ v (Comparison.slab 0 T)
  smooth_p : ContDiffOn ℝ ∞ p (Comparison.slab 0 T)
  smooth_q : ContDiffOn ℝ ∞ q (Comparison.slab 0 T)
  div_u : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence u t x = 0
  div_v : ∀ t ∈ Ioo 0 T, ∀ x, spatialDivergence v t x = 0
  equation : ∀ t ∈ Ioo 0 T, ∀ x,
    navierStokesResidual u p t x = navierStokesResidual v q t x
  energy_u : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) u
  energy_v : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v

/-- Velocity average, given by `timeAverage T a (fun z => (u - v) z k)`. -/
def velocityAverage (T : ℝ) (a : ℝ → ℝ) (u v : VelocityField) (k : Fin 3) : Space → ℝ :=
  timeAverage T a (fun z => (u - v) z k)

/-- Tensor average, given by `timeAverage T a (fun z => tensorDiff u v z.1 i j z.2)`. -/
def tensorAverage (T : ℝ) (a : ℝ → ℝ) (u v : VelocityField)
    (i j : Fin 3) : Space → ℝ :=
  timeAverage T a (fun z => tensorDiff u v z.1 i j z.2)

theorem continuous_deriv_of_smooth {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) :
    Continuous (deriv a) := by
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)
  change Continuous (fun t => fderiv ℝ a t 1)
  exact ((ha.fderiv_right hinf).clm_apply contDiff_const).continuous

theorem Hypotheses.velocityAverage_memLp {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T)) (k : Fin 3) :
    MemLp (velocityAverage T a u v k) 2 :=
  timeAverage_difference_component_memLp_two ha H.smooth_u.continuousOn H.smooth_v.continuousOn
    H.energy_u H.energy_v k

theorem Hypotheses.tensorAverage_integrable {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T)) (i j : Fin 3) :
    Integrable (tensorAverage T a u v i j) :=
  timeAverage_tensorDiff_integrable ha H.smooth_u.continuousOn H.smooth_v.continuousOn
    H.energy_u H.energy_v i j

theorem Hypotheses.tensor_bound {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) ∧ (∫ x, ‖tensorDiff u v t i j x‖) ≤ M :=
  uniformFiniteEnergy_tensorDiff_bound
    (fun _t ht => (spatial_smooth H.smooth_u ht).continuous.aestronglyMeasurable)
    (fun _t ht => (spatial_smooth H.smooth_v ht).continuous.aestronglyMeasurable)
    H.energy_u H.energy_v

theorem velocityAverage_pairing {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, velocityAverage T a u v k x * ψ x) =
      ∫ t in Icc 0 T, a t * (∫ x, (u - v) (t, x) k * ψ x) := by
  obtain ⟨M, _, hM⟩ := uniformFiniteEnergy_difference_component_l2Sq_bound
    H.smooth_u.continuousOn H.smooth_v.continuousOn H.energy_u H.energy_v k
  have hf : ContinuousOn (fun z => (u - v) z k) (Comparison.slab 0 T) :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_continuousOn
      (H.smooth_u.continuousOn.sub H.smooth_v.continuousOn)
  have h := timeAverage_complex_pairing_of_memLp_two
    (f := fun z => (u - v) z k) (ψ := (realTest ψ hψ hcψ : Space → ℂ)) ha hf
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2)
    (realTest ψ hψ hcψ).continuous ((realTest ψ hψ hcψ).memLp 2)
  apply Complex.ofReal_injective
  simpa only [velocityAverage, realTest_apply, ← Complex.ofReal_mul, integral_complex_ofReal] using
      h

theorem tensorAverage_pairing {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (i j : Fin 3) :
    (∫ x, tensorAverage T a u v i j x * ψ x) =
      ∫ t in Icc 0 T, a t * (∫ x, tensorDiff u v t i j x * ψ x) := by
  obtain ⟨M, _, hM⟩ := H.tensor_bound
  obtain ⟨C, hC⟩ := hcψ.exists_bound_of_continuous hψ.continuous
  have h := timeAverage_complex_pairing_of_bounded
    (f := fun z => tensorDiff u v z.1 i j z.2)
    (ψ := (realTest ψ hψ hcψ : Space → ℂ)) ha
    (continuousOn_tensorDiff_field H.smooth_u.continuousOn H.smooth_v.continuousOn i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)
    (realTest ψ hψ hcψ).continuous ⟨C, fun x => by simpa using hC x⟩
  apply Complex.ofReal_injective
  simpa only [tensorAverage, realTest_apply, ← Complex.ofReal_mul, integral_complex_ofReal] using h

/-- Fubini for the actual canonical pressure pairing. The Riesz test is
bounded, so the uniform tensor `L¹` bound controls the whole product. -/
theorem pressurePair_tensorAverage {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    (i j : Fin 3) (ψ : ComplexTest) :
    pressurePair i j (tensorAverage T a u v i j) ψ =
      ∫ t in Icc 0 T, (a t : ℂ) * pressurePair i j (tensorDiff u v t i j) ψ := by
  obtain ⟨M, _, hM⟩ := H.tensor_bound
  obtain ⟨C, _, hC⟩ := RieszTestOperators.exists_bound_rieszTest i j ψ
  exact timeAverage_complex_pairing_of_bounded ha
    (continuousOn_tensorDiff_field H.smooth_u.continuousOn H.smooth_v.continuousOn i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)
    (RieszTestOperators.continuous_rieszTest i j ψ)
    ⟨C, hC⟩

theorem noncanonical_average_identity {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, (velocityAverage T a u v k x : ℂ) * laplacianCLM (realTest ψ hψ hcψ) x) +
      (∫ x, (velocityAverage T (deriv a) u v k x : ℂ) * realTest ψ hψ hcψ x) +
      (∑ i : Fin 3, ∫ x, (tensorAverage T a u v k i x : ℂ) *
        partialCLM i (realTest ψ hψ hcψ) x) =
      ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) : ℝ) : ℂ) := by
  have hsum : (∑ i : Fin 3, ∫ x, tensorAverage T a u v k i x * spatialPartial i ψ x) =
      ∫ t in Icc 0 T, a t * (∑ i : Fin 3, ∫ x, tensorDiff u v t k i x * spatialPartial i ψ x) := by
    have hpair : (∑ i : Fin 3, ∫ x, tensorAverage T a u v k i x * spatialPartial i ψ x) =
        ∑ i : Fin 3, ∫ t in Icc 0 T, a t * (∫ x, tensorDiff u v t k i x * spatialPartial i ψ x) :=
            by
      apply Finset.sum_congr rfl
      intro i _
      exact tensorAverage_pairing (ψ := spatialPartial i ψ) H ha.continuous.continuousOn
        (spatial_partial_contDiff hψ i) (CompactEnergy.compact_partial hcψ i) k i
    rw [hpair]
    simp only [Finset.mul_sum]
    exact (integral_finsetSum _ (fun i _ =>
      (ha.continuous.continuousOn.mul
        (PressureTemporalIdentity.tensor_test_continuousOn H.smooth_u.continuousOn
          H.smooth_v.continuousOn (spatial_partial_contDiff hψ i).continuous
            (CompactEnergy.compact_partial hcψ i) k i)).integrableOn_Icc)).symm
  have hreal : (∫ x, velocityAverage T a u v k x * scalarLaplacian ψ x) +
      (∫ x, velocityAverage T (deriv a) u v k x * ψ x) +
      (∑ i : Fin 3, ∫ x, tensorAverage T a u v k i x * spatialPartial i ψ x) =
      ∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) := by
    rw [velocityAverage_pairing H ha.continuous.continuousOn (scalarLaplacian_contDiff hψ)
        (compact_scalarLaplacian hcψ) k,
      velocityAverage_pairing H (continuous_deriv_of_smooth ha).continuousOn hψ hcψ k, hsum]
    exact (PressureTemporalIdentity.pressure_time_identity H.positive H.smooth_u H.smooth_v
      H.smooth_p H.smooth_q H.div_u H.div_v H.equation ha hsupp hψ hcψ k).symm
  simp only [laplacianCLM_realTest, partialCLM_realTest, realTest_apply,
    ← Complex.ofReal_mul, integral_complex_ofReal]
  change ((∫ x, velocityAverage T a u v k x * scalarLaplacian ψ x : ℝ) : ℂ) +
      ((∫ x, velocityAverage T (deriv a) u v k x * ψ x : ℝ) : ℂ) +
      (∑ i : Fin 3, ∫ x, (tensorAverage T a u v k i x : ℂ) *
        ((spatialPartial i ψ x : ℝ) : ℂ)) = _
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_add,
    Complex.ofReal_sum] using congrArg Complex.ofReal hreal

theorem averaged_value_realTest {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    averagedPressureDifferenceValue (velocityAverage T a u v k)
      (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) k (realTest ψ hψ hcψ) =
      ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) : ℝ) : ℂ) +
      ∑ i : Fin 3, ∑ j : Fin 3,
        pressurePair i j (tensorAverage T a u v i j) (partialCLM k (realTest ψ hψ hcψ)) := by
  unfold averagedPressureDifferenceValue
  rw [noncanonical_average_identity H ha hsupp hψ hcψ k]

/-- Averaging the differentiated Poisson equation commutes with each compact
tensor pairing. All derivatives remain on the compact test. -/
theorem averaged_gradient_poisson {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ t in Icc 0 T, a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, tensorAverage T a u v i j x *
        spatialPartial i (spatialPartial j (spatialPartial k ψ)) x := by
  have hD (i j : Fin 3) :
      ContDiff ℝ ∞ (spatialPartial i (spatialPartial j (spatialPartial k ψ))) :=
    spatial_partial_contDiff (spatial_partial_contDiff (spatial_partial_contDiff hψ k) j) i
  have hC (i j : Fin 3) :
      HasCompactSupport (spatialPartial i (spatialPartial j (spatialPartial k ψ))) :=
    CompactEnergy.compact_partial
      (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcψ k) j) i
  have hi (i j : Fin 3) : IntegrableOn (fun t => a t * (∫ x, tensorDiff u v t i j x *
      spatialPartial i (spatialPartial j (spatialPartial k ψ)) x)) (Icc 0 T) :=
    (ha.continuous.continuousOn.mul
      (PressureTemporalIdentity.tensor_test_continuousOn H.smooth_u.continuousOn
        H.smooth_v.continuousOn (hD i j).continuous (hC i j) i j)).integrableOn_Icc
  have hpoint : (fun t => a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x)) =
      (fun t => a t * (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, tensorDiff u v t i j x *
        spatialPartial i (spatialPartial j (spatialPartial k ψ)) x)) := by
    funext t
    by_cases ht : t ∈ Ioo 0 T
    · rw [gradient_poisson_test H.smooth_u H.smooth_v H.smooth_p H.smooth_q ht
        H.div_u H.div_v (H.equation t ht) hψ hcψ k]
    · have hat : a t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hsupp h))
      simp only [hat, zero_mul]
  rw [hpoint]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact (tensorAverage_pairing (ψ := spatialPartial i (spatialPartial j (spatialPartial k ψ)))
    H ha.continuous.continuousOn (hD i j) (hC i j) i j).symm

theorem averaged_gradient_poisson_complex {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ((∫ t in Icc 0 T, a t *
      (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) : ℝ) : ℂ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (tensorAverage T a u v i j x : ℂ) *
        partialCLM i (partialCLM j (partialCLM k (realTest ψ hψ hcψ))) x := by
  have htest (i j : Fin 3) :
      partialCLM i (partialCLM j (partialCLM k (realTest ψ hψ hcψ))) =
        realTest (spatialPartial i (spatialPartial j (spatialPartial k ψ)))
          (spatial_partial_contDiff (spatial_partial_contDiff
            (spatial_partial_contDiff hψ k) j) i)
          (CompactEnergy.compact_partial (CompactEnergy.compact_partial
            (CompactEnergy.compact_partial hcψ k) j) i) :=
    (congrArg (fun t => partialCLM i (partialCLM j t))
      (partialCLM_realTest ψ hψ hcψ k)).trans
      ((congrArg (partialCLM i) (partialCLM_realTest (spatialPartial k ψ)
        (spatial_partial_contDiff hψ k) (CompactEnergy.compact_partial hcψ k) j)).trans
        (partialCLM_realTest (spatialPartial j (spatialPartial k ψ))
          (spatial_partial_contDiff (spatial_partial_contDiff hψ k) j)
          (CompactEnergy.compact_partial (CompactEnergy.compact_partial hcψ k) j) i))
  simp only [htest]
  change _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (tensorAverage T a u v i j x : ℂ) *
    ((spatialPartial i (spatialPartial j (spatialPartial k ψ)) x : ℝ) : ℂ)
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_sum] using
    congrArg Complex.ofReal (averaged_gradient_poisson H ha hsupp hψ hcψ k)

/-- The averaged physical-minus-canonical pressure-gradient functional is
harmonic on every compact real test, by the two actual Poisson identities. -/
theorem averaged_value_real_harmonic {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    averagedPressureDifferenceValue (velocityAverage T a u v k)
      (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) k
        (laplacianCLM (realTest ψ hψ hcψ)) = 0 := by
  calc
    _ = ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) : ℝ) : ℂ) +
        ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j)
          (partialCLM k (laplacianCLM (realTest ψ hψ hcψ))) := by
      simpa only [laplacianCLM_realTest] using
        averaged_value_realTest H ha hsupp (scalarLaplacian_contDiff hψ)
          (compact_scalarLaplacian hcψ) k
    _ = ((∫ t in Icc 0 T, a t *
        (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * scalarLaplacian ψ x) : ℝ) : ℂ) -
        (∑ i : Fin 3, ∑ j : Fin 3, ∫ x, (tensorAverage T a u v i j x : ℂ) *
          partialCLM i (partialCLM j (partialCLM k (realTest ψ hψ hcψ))) x) := by
      simp only [partial_laplacian_realTest, RieszTestOperators.pressurePair_laplacianCLM,
        Finset.sum_neg_distrib, sub_eq_add_neg]
    _ = 0 := by
      rw [averaged_gradient_poisson_complex H ha hsupp hψ hcψ k, sub_self]

/-- The genuine `H³` bound and compact harmonicity force the whole averaged
functional to vanish. No representative of the physical pressure on Schwartz
tests has been introduced. -/
theorem averaged_value_zero {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T) (k : Fin 3) (ψ : ComplexTest) :
    averagedPressureDifferenceValue (velocityAverage T a u v k)
      (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) k ψ = 0 := by
  have hW0 := H.velocityAverage_memLp ha.continuous.continuousOn k
  have hW1 := H.velocityAverage_memLp (continuous_deriv_of_smooth ha).continuousOn k
  have hG := H.tensorAverage_integrable ha.continuous.continuousOn
  let F : ComplexTest →ₗ[ℂ] ℂ := averagedPressureDifference (velocityAverage T a u v k)
    (velocityAverage T (deriv a) u v k) (tensorAverage T a u v) hW0 hW1 hG k
  obtain ⟨C, hC, hbound⟩ := averagedPressureDifference_bound hW0 hW1 hG k
  have hharmonic : ∀ φ : ComplexTest, HasCompactSupport (φ : Space → ℂ) →
      F (laplacianCLM φ) = 0 := by
    apply compact_harmonic_of_real F
    intro φ hφ hcφ
    simpa only [F, averagedPressureDifference_apply] using
      averaged_value_real_harmonic H ha hsupp hφ hcφ k
  have hz : F = 0 := eq_zero_of_compact_harmonic F hC hbound hharmonic
  have hvalue : F ψ = 0 := by rw [hz]; rfl
  simpa only [F, averagedPressureDifference_apply] using hvalue

/-- The uniform tensor bound and spatial decay of a Riesz test give
continuity of its canonical pairing in time, including the slab endpoints. -/
theorem pressurePair_continuousOn {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (i j : Fin 3) (ψ : ComplexTest) :
    ContinuousOn (fun t => pressurePair i j (tensorDiff u v t i j) ψ) (Icc 0 T) := by
  obtain ⟨M, _, hM⟩ := H.tensor_bound
  exact WeakTimeContinuity.continuousOn_pairing
    (continuousOn_tensorDiff_field H.smooth_u.continuousOn H.smooth_v.continuousOn i j)
    (fun t ht => (hM t ht i j).1) (fun t ht => (hM t ht i j).2)
    (RieszTestOperators.continuous_rieszTest i j ψ)
    (RieszTestOperators.rieszTest_tendsto_zero i j ψ)

theorem canonical_sum_continuousOn {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ψ : ComplexTest) :
    ContinuousOn (fun t => ∑ i : Fin 3, ∑ j : Fin 3,
      pressurePair i j (tensorDiff u v t i j) ψ) (Icc 0 T) :=
  continuousOn_finsetSum _ (fun i _ =>
    continuousOn_finsetSum _ (fun j _ => pressurePair_continuousOn H i j ψ))

theorem canonical_sum_timeAverage {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    (ψ : ComplexTest) :
    (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j) ψ) =
      ∫ t in Icc 0 T, (a t : ℂ) *
        (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j) ψ) := by
  have hi (i j : Fin 3) : IntegrableOn (fun t =>
      (a t : ℂ) * pressurePair i j (tensorDiff u v t i j) ψ) (Icc 0 T) :=
    ((Complex.continuous_ofReal.comp_continuousOn ha).mul
      (pressurePair_continuousOn H i j ψ)).integrableOn_Icc
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j) ψ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ t in Icc 0 T,
        (a t : ℂ) * pressurePair i j (tensorDiff u v t i j) ψ := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact pressurePair_tensorAverage H ha i j ψ
  rw [hsum]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_finsetSum _ (fun j _ => hi i j)).symm

/-- Every compact temporal test annihilates the difference between the
physical and canonical pressure gradients, at a fixed compact spatial test. -/
theorem time_test_gradient_difference_zero {T : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) {a : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hsupp : tsupport a ⊆ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ t in Icc 0 T, a t •
      (((∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x : ℝ) : ℂ) +
        ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
          (partialCLM k (realTest ψ hψ hcψ)))) = 0 := by
  let P : ℝ → ℝ := fun t => ∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x
  let Ψ := partialCLM k (realTest ψ hψ hcψ)
  let Q : ℝ → ℂ := fun t => ∑ i : Fin 3, ∑ j : Fin 3,
    pressurePair i j (tensorDiff u v t i j) Ψ
  have hP : ContinuousOn P (Ioo 0 T) :=
    pressure_gradient_pairing_continuousOn H.smooth_u H.smooth_v H.smooth_p H.smooth_q
      H.div_u H.div_v H.equation hψ hcψ k
  have hPweight : Continuous (fun t => a t * P t) :=
    PressureTemporalIdentity.continuous_cutoff_mul ha.continuous hP isOpen_Ioo hsupp
  have hiP : IntegrableOn (fun t => (a t : ℂ) * (P t : ℂ)) (Icc 0 T) := by
    have hi : IntegrableOn (fun t => ((a t * P t : ℝ) : ℂ)) (Icc 0 T) :=
      (Complex.continuous_ofReal.comp hPweight).continuousOn.integrableOn_Icc
    simpa only [Complex.ofReal_mul] using hi
  have hQ : ContinuousOn Q (Icc 0 T) := canonical_sum_continuousOn H Ψ
  have hiQ : IntegrableOn (fun t => (a t : ℂ) * Q t) (Icc 0 T) :=
    ((Complex.continuous_ofReal.comp_continuousOn ha.continuous.continuousOn).mul
        hQ).integrableOn_Icc
  have hz := averaged_value_zero H ha hsupp k (realTest ψ hψ hcψ)
  rw [averaged_value_realTest H ha hsupp hψ hcψ k] at hz
  change (((∫ t in Icc 0 T, a t * P t : ℝ) : ℂ) +
    ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorAverage T a u v i j) Ψ) = 0 at hz
  rw [canonical_sum_timeAverage H ha.continuous.continuousOn Ψ] at hz
  change (∫ t in Icc 0 T, a t • ((P t : ℂ) + Q t)) = 0
  simp only [Complex.real_smul, mul_add]
  rw [integral_add hiP hiQ]
  simp only [← Complex.ofReal_mul, integral_complex_ofReal]
  exact hz

/-- Actual pressure-gradient recovery at every interior time. This equality
is obtained from the equation and uniform finite energy, rather than assumed
as a pressure normalization. -/
theorem gradient_recovery_complex {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ((∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x : ℝ) : ℂ) =
      -(∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (partialCLM k (realTest ψ hψ hcψ))) := by
  have hP := pressure_gradient_pairing_continuousOn
    H.smooth_u H.smooth_v H.smooth_p H.smooth_q H.div_u H.div_v H.equation hψ hcψ k
  have hQ := canonical_sum_continuousOn H (partialCLM k (realTest ψ hψ hcψ))
  have hcontinuous := (Complex.continuous_ofReal.comp_continuousOn hP).add
    (hQ.mono Ioo_subset_Icc_self)
  have hzero := TemporalTestUniqueness.eq_zero_on_Ioo_of_setIntegral_tests hcontinuous (by
    intro a ha _hca hsupp
    exact time_test_gradient_difference_zero H ha hsupp hψ hcψ k)
  exact eq_neg_of_add_eq_zero_left (hzero t ht)

theorem gradient_recovery {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T)
    {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      -(∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (partialCLM k (realTest ψ hψ hcψ))).re := by
  simpa only [Complex.ofReal_re, Complex.neg_re] using
    congrArg Complex.re (gradient_recovery_complex H ht hψ hcψ k)

/-- The explicit comparison-hypothesis form of pressure recovery. Only the
spatial test is compactly supported; both velocities and both pressures are
allowed on all of Euclidean space. -/
theorem pressure_gradient_recovery {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (hT : 0 < T)
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hdivu : ∀ s ∈ Ioo 0 T, ∀ x, spatialDivergence u s x = 0)
    (hdivv : ∀ s ∈ Ioo 0 T, ∀ x, spatialDivergence v s x = 0)
    (hNS : ∀ s ∈ Ioo 0 T, ∀ x,
      navierStokesResidual u p s x = navierStokesResidual v q s x)
    (heu : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) u)
    (hev : NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v)
    (ht : t ∈ Ioo 0 T) {ψ : Space → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, spatialPartial k (fun y => (p - q) (t, y)) x * ψ x) =
      -(∑ i : Fin 3, ∑ j : Fin 3, (pressurePair i j (tensorDiff u v t i j)
        (partialCLM k (realTest ψ hψ hcψ))).re) := by
  let H : Hypotheses T u v p q := ⟨hT, hu, hv, hp, hq, hdivu, hdivv, hNS, heu, hev⟩
  have h := congrArg (fun z : ℂ => Complex.reCLM z) (gradient_recovery_complex H ht hψ hcψ k)
  simpa only [map_neg, map_sum, Complex.reCLM_apply, Complex.ofReal_re] using h

end NavierStokesR3.PressureRecovery

end
end

end

section

/-!
# The compact test function in the pressure flux

The identity `φ² r = D(φ⁸)[w]` places the localized pressure flux in the
commutator form.  Its estimates use only the unweighted velocity energy and
the weighted velocity and gradient norms.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.PressureFluxTest

open ProblemStatement Comparison

/-- The scalar test function for the pressure commutator. -/
noncomputable def r (φ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  8 * φ x ^ 5 * (fderiv ℝ φ x (w x))

theorem multiplier_r_eq_weight_deriv {φ : Space → ℝ} (w : Space → Space)
    {x : Space} (hφ : DifferentiableAt ℝ φ x) :
    φ x ^ 2 * r φ w x = fderiv ℝ (fun y => φ y ^ 8) x (w x) := by
  have hd : fderiv ℝ (fun y => φ y ^ 8) x = (8 * φ x ^ 7) • fderiv ℝ φ x := by
    simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
      ((hasDerivAt_pow 8 (φ x)).comp_hasFDerivAt x hφ.hasFDerivAt).fderiv
  rw [hd]
  simp only [r, _root_.smul_apply, smul_eq_mul]
  ring

theorem r_smooth {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (r φ w) :=
  (contDiff_const.mul (hφ.pow 5)).mul
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply hw)

theorem r_hasCompactSupport {φ : Space → ℝ} (hs : HasCompactSupport φ)
    (w : Space → Space) : HasCompactSupport (r φ w) := by
  apply hs.mono
  intro x hx
  change φ x ≠ 0
  intro hzero
  apply hx
  simp [r, hzero]

theorem memLp_r {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (p : ℝ≥0∞) : MemLp (r φ w) p volume :=
  (r_smooth hφ hw).continuous.memLp_of_hasCompactSupport (r_hasCompactSupport hs w)

theorem memLp_fderiv_r {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (p : ℝ≥0∞) : MemLp (fderiv ℝ (r φ w)) p volume :=
  ((r_smooth hφ hw).fderiv_right (m := ∞) (by simp)).continuous.memLp_of_hasCompactSupport
    ((r_hasCompactSupport hs w).fderiv ℝ)

theorem norm_r_le {φ : Space → ℝ} {w : Space → Space} {x : Space}
    (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ‖fderiv ℝ φ x‖ ≤ L) :
    ‖r φ w x‖ ≤ (8 * L) * ‖(φ x ^ 3) • w x‖ := by
  have hp2 : φ x ^ 2 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hp : φ x ^ 5 ≤ φ x ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hp2 (pow_nonneg hφ0 3)]
  have happly : ‖fderiv ℝ φ x (w x)‖ ≤ L * ‖w x‖ :=
    ((fderiv ℝ φ x).le_opNorm (w x)).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    ‖r φ w x‖ = 8 * φ x ^ 5 * ‖fderiv ℝ φ x (w x)‖ := by
      simp [r, norm_mul, Real.norm_eq_abs, abs_of_nonneg hφ0]
    _ ≤ 8 * φ x ^ 5 * (L * ‖w x‖) :=
      mul_le_mul_of_nonneg_left happly (by positivity)
    _ ≤ (8 * L) * (φ x ^ 3 * ‖w x‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg hL0 (norm_nonneg (w x)))]
    _ = (8 * L) * ‖(φ x ^ 3) • w x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hφ0 3)]

/-- The test belongs to `L⁴`, with the exact endpoint interpolation exponents. -/
theorem memLp_and_lpNorm_r_four_le {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L) :
    MemLp (r φ w) 4 volume ∧
      comparisonLpNorm 4 (r φ w) ≤ 8 * L * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  have hw6 := WeightedSobolev.memLp_cutoff_pow_smul hφ.continuous hs hw.continuous
    (by norm_num : (4 : ℕ) ≠ 0) 6
  obtain ⟨hw4, hbound⟩ := WeightedInterpolation.cutoff_interpolation_four
    hφ.continuous.aestronglyMeasurable hφ0 hw2 hw6
  refine ⟨memLp_r hφ hs hw 4, ?_⟩
  calc
    comparisonLpNorm 4 (r φ w) ≤ comparisonLpNorm 4 (fun x => (8 * L) • (φ x ^ 3 • w x)) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (hw4.const_smul (8 * L))
      intro x
      change ‖r φ w x‖ ≤ ‖(8 * L) • (φ x ^ 3 • w x)‖
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 8 * L)]
      exact norm_r_le (hφ0 x) (hφ1 x) hL0 (hL x)
    _ = (8 * L) * comparisonLpNorm 4 (fun x => φ x ^ 3 • w x) := by
      rw [LpNormTools.lpNorm_const_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 8 * L)]
    _ ≤ (8 * L) * (comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 8 * L * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (3 / 4 : ℝ) := by ring

private theorem norm_fderiv_product_le {f g : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => f y * g y) x‖ ≤
      ‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖ := by
  rw [fderiv_fun_mul hf hg]
  exact (norm_add_le _ _).trans (add_le_add
    (ContinuousLinearMap.opNorm_smul_le _ _) (ContinuousLinearMap.opNorm_smul_le _ _))

private theorem norm_fderiv_apply_le {φ : Space → ℝ} {w : Space → Space} {x : Space}
    (hφ : DifferentiableAt ℝ (fderiv ℝ φ) x) (hw : DifferentiableAt ℝ w x) :
    ‖fderiv ℝ (fun y => fderiv ℝ φ y (w y)) x‖ ≤
      ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ + ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ := by
  have hflip : ‖(fderiv ℝ (fderiv ℝ φ) x).flip (w x)‖ ≤
      ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    change ‖fderiv ℝ (fderiv ℝ φ) x z (w x)‖ ≤ _
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ φ) x z‖ * ‖w x‖ :=
        (fderiv ℝ (fderiv ℝ φ) x z).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖z‖) * ‖w x‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ φ) x).le_opNorm z)
          (norm_nonneg _)
      _ = _ := by ring
  rw [fderiv_clm_apply hφ hw]
  exact (norm_add_le _ _).trans
    (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) hflip)

/-- Product differentiation before replacing the cutoff derivative norms by constants. -/
theorem norm_fderiv_r_le_raw {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (x : Space) (hφ0 : 0 ≤ φ x) :
    ‖fderiv ℝ (r φ w) x‖ ≤ 8 *
      (φ x ^ 5 * ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ +
        φ x ^ 5 * ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ +
        5 * φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2 * ‖w x‖) := by
  have hdφ : DifferentiableAt ℝ φ x := (contDiff_infty.1 hφ 1).differentiable (by simp) x
  have hdw : DifferentiableAt ℝ w x := (contDiff_infty.1 hw 1).differentiable (by simp) x
  have hdDφ : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  let q : Space → ℝ := fun y => fderiv ℝ φ y (w y)
  have hdq : DifferentiableAt ℝ q x := hdDφ.clm_apply hdw
  have hr : r φ w = fun y => 8 * (φ y ^ 5 * q y) := by
    funext y
    simp only [r, q]
    ring
  have hpow : ‖fderiv ℝ (fun y => φ y ^ 5) x‖ ≤
      5 * φ x ^ 4 * ‖fderiv ℝ φ x‖ := by
    have heq : fderiv ℝ (fun y => φ y ^ 5) x = (5 * φ x ^ 4) • fderiv ℝ φ x := by
      simpa only [Function.comp_def, Nat.cast_ofNat, Nat.reduceSub] using
        ((hasDerivAt_pow 5 (φ x)).comp_hasFDerivAt x hdφ.hasFDerivAt).fderiv
    rw [heq]
    calc
      _ ≤ ‖(5 : ℝ) * φ x ^ 4‖ * ‖fderiv ℝ φ x‖ :=
        ContinuousLinearMap.opNorm_smul_le (5 * φ x ^ 4) (fderiv ℝ φ x)
      _ = _ := by rw [Real.norm_of_nonneg (by positivity : 0 ≤ 5 * φ x ^ 4)]
  have hq : ‖q x‖ ≤ ‖fderiv ℝ φ x‖ * ‖w x‖ := (fderiv ℝ φ x).le_opNorm _
  have hDq : ‖fderiv ℝ q x‖ ≤ ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ +
      ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ := norm_fderiv_apply_le hdDφ hdw
  calc
    ‖fderiv ℝ (r φ w) x‖ ≤ 8 * ‖fderiv ℝ (fun y => φ y ^ 5 * q y) x‖ := by
      rw [hr, fderiv_const_mul (a := fun y => φ y ^ 5 * q y) ((hdφ.pow 5).mul hdq) 8]
      simpa using ContinuousLinearMap.opNorm_smul_le (8 : ℝ)
        (fderiv ℝ (fun y => φ y ^ 5 * q y) x)
    _ ≤ 8 * (φ x ^ 5 * ‖fderiv ℝ q x‖ +
        ‖q x‖ * ‖fderiv ℝ (fun y => φ y ^ 5) x‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hφ0 5)] using!
        norm_fderiv_product_le (hdφ.pow 5) hdq
    _ ≤ 8 * (φ x ^ 5 * (‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ +
        ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖) +
        (‖fderiv ℝ φ x‖ * ‖w x‖) * (5 * φ x ^ 4 * ‖fderiv ℝ φ x‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add (mul_le_mul_of_nonneg_left hDq (pow_nonneg hφ0 5))
      exact mul_le_mul hq hpow (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Only the weighted velocity derivative occurs in the pointwise bound. -/
theorem norm_fderiv_r_le_amplitude {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hw : ContDiff ℝ ∞ w) (x : Space)
    (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1) {L J : ℝ} (hL0 : 0 ≤ L)
    (hL : ‖fderiv ℝ φ x‖ ≤ L) (hJ : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ J) :
    ‖fderiv ℝ (r φ w) x‖ ≤
      (24 * L) * WeightedSobolev.cutoffGradientAmplitude φ w x +
        (40 * L ^ 2 + 8 * J) * ‖w x‖ := by
  have hp4 : φ x ^ 4 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hp5 : φ x ^ 5 ≤ 1 := pow_le_one₀ hφ0 hφ1
  have hp54 : φ x ^ 5 ≤ φ x ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hφ1 (pow_nonneg hφ0 4)]
  have hgrad := GradientOperator.norm_fderiv_le_three_mul_sqrt_gradientSq w x
  have h1 : φ x ^ 5 * ‖fderiv ℝ φ x‖ * ‖fderiv ℝ w x‖ ≤
      3 * L * WeightedSobolev.cutoffGradientAmplitude φ w x := by
    calc
      _ ≤ (φ x ^ 4 * L) * (3 * Real.sqrt (gradientSq w x)) :=
        mul_le_mul (mul_le_mul hp54 hL (norm_nonneg _) (pow_nonneg hφ0 4)) hgrad
          (norm_nonneg _) (mul_nonneg (pow_nonneg hφ0 4) hL0)
      _ = _ := by unfold WeightedSobolev.cutoffGradientAmplitude; ring
  have h2 : φ x ^ 5 * ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖w x‖ ≤ J * ‖w x‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [one_mul] using
      mul_le_mul hp5 hJ (norm_nonneg (fderiv ℝ (fderiv ℝ φ) x)) zero_le_one
  have hsquare : ‖fderiv ℝ φ x‖ ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hL 2
  have h3 : 5 * φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2 * ‖w x‖ ≤
      5 * L ^ 2 * ‖w x‖ := by
    have hh : φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2 ≤ L ^ 2 := by
      simpa only [one_mul] using mul_le_mul hp4 hsquare (sq_nonneg _) zero_le_one
    calc
      _ = 5 * (φ x ^ 4 * ‖fderiv ℝ φ x‖ ^ 2) * ‖w x‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (by norm_num)) (norm_nonneg _)
  calc
    ‖fderiv ℝ (r φ w) x‖ ≤ _ := norm_fderiv_r_le_raw hφ hw x hφ0
    _ ≤ 8 * (3 * L * WeightedSobolev.cutoffGradientAmplitude φ w x +
        J * ‖w x‖ + 5 * L ^ 2 * ‖w x‖) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) (by norm_num)
    _ = _ := by ring

/-- The derivative is square integrable and controlled by weighted dissipation. -/
theorem memLp_and_lpNorm_fderiv_r_two_le {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L J : ℝ} (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J)
    (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L)
    (hJ : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ J) :
    MemLp (fderiv ℝ (r φ w)) 2 volume ∧
      comparisonLpNorm 2 (fderiv ℝ (r φ w)) ≤
        (24 * L) * Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) +
          (40 * L ^ 2 + 8 * J) * comparisonLpNorm 2 w := by
  let G := WeightedSobolev.cutoffGradientAmplitude φ w
  have hw1 := contDiff_infty.1 hw 1
  have hG : MemLp G 2 volume :=
    WeightedSobolev.memLp_cutoffGradientAmplitude hφ.continuous hs hw1 2
  have hG24 : MemLp (fun x => (24 * L) • G x) 2 volume := hG.const_smul (24 * L)
  have hw40 : MemLp (fun x => (40 * L ^ 2 + 8 * J) • ‖w x‖) 2 volume :=
    hw2.norm.const_smul (40 * L ^ 2 + 8 * J)
  have hc : 0 ≤ 40 * L ^ 2 + 8 * J := by positivity
  refine ⟨memLp_fderiv_r hφ hs hw 2, ?_⟩
  calc
    comparisonLpNorm 2 (fderiv ℝ (r φ w)) ≤
        comparisonLpNorm 2 (fun x => (24 * L) • G x + (40 * L ^ 2 + 8 * J) • ‖w x‖) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (hG24.add hw40)
      intro x
      have hp := norm_fderiv_r_le_amplitude hφ hw x (hφ0 x) (hφ1 x) hL0 (hL x) (hJ x)
      simpa only [Pi.add_apply, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ (24 * L) * G x + (40 * L ^ 2 + 8 * J) * ‖w x‖ by
          have := WeightedSobolev.cutoffGradientAmplitude_nonneg φ w x
          dsimp [G] at *
          positivity)] using hp
    _ ≤ comparisonLpNorm 2 (fun x => (24 * L) • G x) +
        comparisonLpNorm 2 (fun x => (40 * L ^ 2 + 8 * J) • ‖w x‖) :=
      LpNormTools.lpNorm_add_le (by norm_num) hG24 hw40
    _ = (24 * L) * Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) +
        (40 * L ^ 2 + 8 * J) * comparisonLpNorm 2 w := by
      rw [LpNormTools.lpNorm_const_smul, LpNormTools.lpNorm_const_smul]
      have hGeq := WeightedSobolev.lpNorm_cutoffGradientAmplitude hφ.continuous hs hw1
      change comparisonLpNorm 2 G = _ at hGeq
      rw [hGeq]
      simp [comparisonLpNorm, eLpNorm_norm, Real.norm_eq_abs, abs_of_nonneg hL0, abs_of_nonneg hc]

theorem lpNorm_fderiv_r_two_le {φ : Space → ℝ} {w : Space → Space}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hw : ContDiff ℝ ∞ w)
    (hw2 : MemLp w 2 volume) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    {L J : ℝ} (hL0 : 0 ≤ L) (hJ0 : 0 ≤ J)
    (hL : ∀ x, ‖fderiv ℝ φ x‖ ≤ L)
    (hJ : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ J) :
    comparisonLpNorm 2 (fderiv ℝ (r φ w)) ≤
      40 * (L * Real.sqrt (∫ x, φ x ^ 8 * gradientSq w x) +
        (L ^ 2 + J) * comparisonLpNorm 2 w) := by
  have h := (memLp_and_lpNorm_fderiv_r_two_le hφ hs hw hw2 hφ0 hφ1 hL0 hJ0 hL hJ).2
  have hA := Real.sqrt_nonneg (∫ x, φ x ^ 8 * gradientSq w x)
  have hM := LpNormTools.lpNorm_nonneg 2 w
  nlinarith [mul_nonneg hL0 hA, mul_nonneg hJ0 hM]

/-- The actual test at radius `R` in the fixed cutoff family. -/
def cutoffTest (R : ℝ) (w : Space → Space) : Space → ℝ :=
  r (ComparisonCutoffs.cutoff R) w

theorem cutoffTest_flux_identity (R : ℝ) (w : Space → Space) (x : Space) :
    ComparisonCutoffs.multiplier R x * cutoffTest R w x =
      fderiv ℝ (ComparisonCutoffs.weight R) x (w x) :=
  multiplier_r_eq_weight_deriv w
    ((contDiff_infty.1 (ComparisonCutoffs.cutoff_smooth R) 1).differentiable (by simp) x)

theorem cutoffTest_smooth (R : ℝ) {w : Space → Space} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (cutoffTest R w) := r_smooth (ComparisonCutoffs.cutoff_smooth R) hw

theorem cutoffTest_hasCompactSupport {R : ℝ} (hR : 0 < R) (w : Space → Space) :
    HasCompactSupport (cutoffTest R w) :=
  r_hasCompactSupport (ComparisonCutoffs.cutoff_hasCompactSupport hR) w

theorem memLp_cutoffTest {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (p : ℝ≥0∞) : MemLp (cutoffTest R w) p volume :=
  memLp_r (ComparisonCutoffs.cutoff_smooth R) (ComparisonCutoffs.cutoff_hasCompactSupport hR) hw p

theorem memLp_fderiv_cutoffTest {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (p : ℝ≥0∞) : MemLp (fderiv ℝ (cutoffTest R w)) p volume :=
  memLp_fderiv_r (ComparisonCutoffs.cutoff_smooth R)
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hw p

theorem cutoffTest_four_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) :
    MemLp (cutoffTest R w) 4 volume ∧
      comparisonLpNorm 4 (cutoffTest R w) ≤ (8 * ComparisonCutoffs.derivativeConstant 1 / R) *
        comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
          comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  have h := memLp_and_lpNorm_r_four_le (ComparisonCutoffs.cutoff_smooth R)
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hw hw2
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R)
    (div_nonneg (ComparisonCutoffs.derivativeConstant_pos 1).le hR.le)
    (ComparisonCutoffs.cutoff_fderiv_le hR)
  simpa only [cutoffTest, mul_div_assoc] using h

/-- A fixed constant for the derivative bound of the pressure test. -/
def cutoffDerivativeConstant : ℝ :=
  max (24 * ComparisonCutoffs.derivativeConstant 1)
    (40 * ComparisonCutoffs.derivativeConstant 1 ^ 2 + 8 * ComparisonCutoffs.derivativeConstant 2)

theorem cutoffDerivativeConstant_pos : 0 < cutoffDerivativeConstant :=
  lt_of_lt_of_le (mul_pos (by norm_num) (ComparisonCutoffs.derivativeConstant_pos 1))
    (le_max_left _ _)

theorem cutoffTest_derivative_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) :
    MemLp (fderiv ℝ (cutoffTest R w)) 2 volume ∧
      comparisonLpNorm 2 (fderiv ℝ (cutoffTest R w)) ≤
        (cutoffDerivativeConstant / R) *
          Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) +
        (cutoffDerivativeConstant / R ^ 2) * comparisonLpNorm 2 w := by
  have h := memLp_and_lpNorm_fderiv_r_two_le (ComparisonCutoffs.cutoff_smooth R)
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hw hw2
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R)
    (div_nonneg (ComparisonCutoffs.derivativeConstant_pos 1).le hR.le)
    (div_nonneg (ComparisonCutoffs.derivativeConstant_pos 2).le (sq_nonneg R))
    (ComparisonCutoffs.cutoff_fderiv_le hR) (ComparisonCutoffs.cutoff_second_fderiv_le hR)
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ = ((24 * ComparisonCutoffs.derivativeConstant 1) / R) *
          Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) +
        ((40 * ComparisonCutoffs.derivativeConstant 1 ^ 2 +
          8 * ComparisonCutoffs.derivativeConstant 2) / R ^ 2) * comparisonLpNorm 2 w := by
      field_simp [hR.ne']
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right hR).2 (le_max_left _ _)) (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_right
        ((div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2 (le_max_right _ _))
        (LpNormTools.lpNorm_nonneg 2 w))

end NavierStokesR3.PressureFluxTest

end
end

end

section

/-!
# The actual pressure flux equals the canonical pressure flux

The scalar gradient identification is supplied by the proved pressure recovery
theorem. The only compact support in this identity is that of the cutoff.
-/

section

/-!
# From scalar pressure-gradient identification to the cutoff pressure flux

This module is an integration-by-parts bridge. Its input is an explicit
identification of every compact scalar pressure-gradient pairing. It does not
assume a pressure-flux formula or any bound on the pressure at infinity.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff BigOperators

namespace NavierStokesR3.PressureFluxIdentity

open ProblemStatement Comparison PressureRecovery HarmonicTestFunctionals
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness

theorem fluxFunction_smooth {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x : Space => fderiv ℝ χ x (w x)) :=
  (hχ.fderiv_right (m := ∞) (by simp)).clm_apply hw

theorem fluxFunction_hasCompactSupport {χ : Space → ℝ}
    (hcχ : HasCompactSupport χ) (w : Space → Space) :
    HasCompactSupport (fun x : Space => fderiv ℝ χ x (w x)) := by
  apply (hcχ.fderiv ℝ).mono
  intro x hx
  change fderiv ℝ χ x ≠ 0
  intro hzero
  apply hx
  simp only [hzero, _root_.zero_apply]

theorem integrable_pressure_flux {χ π : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hπ : ContDiff ℝ ∞ π) (hw : ContDiff ℝ ∞ w)
    (hcχ : HasCompactSupport χ) :
    Integrable (fun x : Space => π x * fderiv ℝ χ x (w x)) :=
  ConservativeDifference.integrable_mul_test hπ.continuous
    (fluxFunction_smooth hχ hw).continuous (fluxFunction_hasCompactSupport hcχ w)

/-- The scalar compact test associated to one component of the weighted velocity. -/
def weightedComponent (χ : Space → ℝ) (w : Space → Space) (k : Fin 3) : Space → ℝ :=
  fun x => χ x * w x k

theorem weightedComponent_smooth {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (k : Fin 3) :
    ContDiff ℝ ∞ (weightedComponent χ w k) :=
  hχ.mul (component_contDiff hw k)

theorem weightedComponent_hasCompactSupport {χ : Space → ℝ}
    (hcχ : HasCompactSupport χ) (w : Space → Space) (k : Fin 3) :
    HasCompactSupport (weightedComponent χ w k) := hcχ.mul_right

theorem sum_partial_weightedComponent {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ x : Space, (∑ k : Fin 3, partialD k w x k) = 0) (x : Space) :
    (∑ k : Fin 3, partialD k (weightedComponent χ w k) x) = fderiv ℝ χ x (w x) := by
  calc
    (∑ k : Fin 3, partialD k (weightedComponent χ w k) x) =
        ∑ k : Fin 3, spatialPartial k (fun y => χ y • w y) x k := by
      apply Finset.sum_congr rfl
      intro k _
      change spatialPartial k (fun y => (χ y • w y) k) x = _
      exact ConservativeDifference.partial_component (hχ.smul hw) k k x
    _ = fderiv ℝ χ x (w x) := by
      simpa only [hdiv x, mul_zero, add_zero] using
        LocalizedDifferenceEnergy.divergence_weighted hχ hw x

/-- The compact flux test is the sum of the differentiated component tests. -/
theorem sum_partial_realTest_weightedComponent {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ)
    (hdiv : ∀ x : Space, (∑ k : Fin 3, partialD k w x k) = 0) :
    (∑ k : Fin 3, partialCLM k (realTest (weightedComponent χ w k)
      (weightedComponent_smooth hχ hw k) (weightedComponent_hasCompactSupport hcχ w k))) =
    realTest (fun x : Space => fderiv ℝ χ x (w x))
      (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w) := by
  ext x
  simp only [sum_apply, partialCLM_realTest, realTest_apply]
  calc
    (∑ k : Fin 3, ((spatialPartial k (weightedComponent χ w k) x : ℝ) : ℂ)) =
        ((∑ k : Fin 3, partialD k (weightedComponent χ w k) x : ℝ) : ℂ) :=
      (map_sum Complex.ofRealCLM _ _).symm
    _ = (fderiv ℝ χ x (w x) : ℂ) :=
      congrArg Complex.ofReal (sum_partial_weightedComponent hχ hw hdiv x)

/-- The sum of all canonical pressure pairings is a complex-linear functional. -/
def canonicalPressureLinear (g : Fin 3 → Fin 3 → Space → ℝ)
    (hg : ∀ i j : Fin 3, Integrable (g i j)) : ComplexTest →ₗ[ℂ] ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, PressureFunctionals.pressurePairLinear i j (g i j) (hg i j)

@[simp] theorem canonicalPressureLinear_apply (g : Fin 3 → Fin 3 → Space → ℝ)
    (hg : ∀ i j : Fin 3, Integrable (g i j)) (ψ : ComplexTest) :
    canonicalPressureLinear g hg ψ = ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (g i j) ψ := by
  simp only [canonicalPressureLinear, LinearMap.sum_apply,
      PressureFunctionals.pressurePairLinear_apply]

theorem integrable_canonical_flux_terms {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (hcχ : HasCompactSupport χ)
    {g : Fin 3 → Fin 3 → Space → ℝ} (hg : ∀ i j : Fin 3, Integrable (g i j))
    (i j : Fin 3) :
    Integrable (fun x : Space => (g i j x : ℂ) * rieszTest i j
      (realTest (fun y : Space => fderiv ℝ χ y (w y))
        (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w)) x) :=
  PressureFunctionals.integrable_l1_riesz_pair (hg i j) i j _

/-- Compact integration by parts turns the given scalar pressure-gradient
identification into the actual cutoff pressure flux. -/
theorem pressure_flux_eq_of_gradient_identification
    {π χ : Space → ℝ} {w : Space → Space} {g : Fin 3 → Fin 3 → Space → ℝ}
    (hπ : ContDiff ℝ ∞ π) (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w)
    (hcχ : HasCompactSupport χ) (hg : ∀ i j : Fin 3, Integrable (g i j))
    (hdiv : ∀ x : Space, (∑ k : Fin 3, partialD k w x k) = 0)
    (hgrad : ∀ (k : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
      (hcψ : HasCompactSupport ψ),
      (∫ x : Space, partialD k π x * ψ x) =
        -(∑ i : Fin 3, ∑ j : Fin 3,
          pressurePair i j (g i j) (partialCLM k (realTest ψ hψ hcψ))).re) :
    (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
      (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (g i j)
        (realTest (fun x : Space => fderiv ℝ χ x (w x))
          (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w))).re := by
  let η : Fin 3 → ComplexTest := fun k =>
    partialCLM k (realTest (weightedComponent χ w k)
      (weightedComponent_smooth hχ hw k) (weightedComponent_hasCompactSupport hcχ w k))
  let Q : ComplexTest →ₗ[ℂ] ℂ := canonicalPressureLinear g hg
  have hsum : (∑ k : Fin 3, η k) =
      realTest (fun x : Space => fderiv ℝ χ x (w x))
        (fluxFunction_smooth hχ hw) (fluxFunction_hasCompactSupport hcχ w) :=
    sum_partial_realTest_weightedComponent hχ hw hcχ hdiv
  have hint (k : Fin 3) :
      Integrable (fun x : Space => π x * partialD k (weightedComponent χ w k) x) :=
    ConservativeDifference.integrable_mul_test hπ.continuous
      (spatial_partial_contDiff (weightedComponent_smooth hχ hw k) k).continuous
      (CompactEnergy.compact_partial (weightedComponent_hasCompactSupport hcχ w k) k)
  have hscalar (k : Fin 3) :
      (∫ x : Space, π x * partialD k (weightedComponent χ w k) x) = (Q (η k)).re := by
    have hibp :
        (∫ x : Space, partialD k π x * weightedComponent χ w k x) =
          -(∫ x : Space, π x * partialD k (weightedComponent χ w k) x) := by
      simpa only [partialD, mul_comm] using
        CompactEnergy.integral_mul_partial (weightedComponent_smooth hχ hw k) hπ
          (weightedComponent_hasCompactSupport hcχ w k) k
    have h := neg_injective (hibp.symm.trans (hgrad k (weightedComponent χ w k)
      (weightedComponent_smooth hχ hw k) (weightedComponent_hasCompactSupport hcχ w k)))
    simpa only [Q, η, canonicalPressureLinear_apply] using h
  have hfluxsum :
      (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
        ∑ k : Fin 3, ∫ x : Space, π x * partialD k (weightedComponent χ w k) x := by
    calc
      (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
          ∫ x : Space, ∑ k : Fin 3, π x * partialD k (weightedComponent χ w k) x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change π x * fderiv ℝ χ x (w x) =
            ∑ k : Fin 3, π x * partialD k (weightedComponent χ w k) x
          rw [← sum_partial_weightedComponent hχ hw hdiv x, Finset.mul_sum]
      _ = _ := integral_finsetSum _ (fun k _ => hint k)
  calc
    (∫ x : Space, π x * fderiv ℝ χ x (w x)) =
        ∑ k : Fin 3, ∫ x : Space, π x * partialD k (weightedComponent χ w k) x := hfluxsum
    _ = ∑ k : Fin 3, (Q (η k)).re := Finset.sum_congr rfl (fun k _ => hscalar k)
    _ = (∑ k : Fin 3, Q (η k)).re :=
      (map_sum Complex.reCLM (fun k => Q (η k)) Finset.univ).symm
    _ = (Q (∑ k : Fin 3, η k)).re :=
      congrArg Complex.re (map_sum Q η Finset.univ).symm
    _ = _ := by
      rw [hsum]
      exact congrArg Complex.re (canonicalPressureLinear_apply g hg _)

end NavierStokesR3.PressureFluxIdentity

end
end

end

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NavierStokesR3.ActualPressureFlux

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicUniqueness
open Comparison PressureRecovery PressureFluxIdentity

theorem difference_slice_smooth {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T) :
    ContDiff ℝ ∞ (fun x : Space => (u - v) (t, x)) :=
  spatial_smooth (H.smooth_u.sub H.smooth_v) (Ioo_subset_Icc_self ht)

theorem actual_pressure_flux_integrable {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T) {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    Integrable (fun x : Space => (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) :=
  integrable_pressure_flux hχ
    (spatial_smooth (H.smooth_p.sub H.smooth_q) (Ioo_subset_Icc_self ht))
    (difference_slice_smooth H ht) hcχ

/-- The pressure flux of the actual difference equation has the canonical
Riesz-pairing representation, with no additional pressure hypothesis. -/
theorem pressure_flux_eq_canonical {T t : ℝ} {u v : VelocityField} {p q : PressureField}
    (H : Hypotheses T u v p q) (ht : t ∈ Ioo 0 T) {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    (∫ x : Space, (p - q) (t, x) * fderiv ℝ χ x ((u - v) (t, x))) =
      (∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (realTest (fun x : Space => fderiv ℝ χ x ((u - v) (t, x)))
          (fluxFunction_smooth hχ (difference_slice_smooth H ht))
          (fluxFunction_hasCompactSupport hcχ (fun x : Space => (u - v) (t, x))))).re := by
  obtain ⟨_M, _hM, hg⟩ := H.tensor_bound
  have hdiv : ∀ x : Space,
      (∑ k : Fin 3, partialD k (fun y => (u - v) (t, y)) x k) = 0 := by
    intro x
    change spatialDivergence (u - v) t x = 0
    rw [spatialDivergence_sub (spatial_smooth H.smooth_u (Ioo_subset_Icc_self ht))
      (spatial_smooth H.smooth_v (Ioo_subset_Icc_self ht)),
      H.div_u t ht, H.div_v t ht, sub_self]
  exact pressure_flux_eq_of_gradient_identification
    (spatial_smooth (H.smooth_p.sub H.smooth_q) (Ioo_subset_Icc_self ht))
    hχ (difference_slice_smooth H ht) hcχ
    (fun i j => (hg t (Ioo_subset_Icc_self ht) i j).1) hdiv
    (fun k ψ hψ hcψ => gradient_recovery H ht hψ hcψ k)

end NavierStokesR3.ActualPressureFlux

end
end

end

section

/-!
# Weighted tensor bounds for the localized pressure

The tensor difference is expanded around the reference velocity. Its two
cross terms use `L³` of that velocity and `L²` of the difference; the quadratic
term uses the cutoff interpolation estimate. All norms remain finite explicitly.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace NavierStokesR3.LocalizedTensorBounds

open ProblemStatement Comparison

private theorem six_fifths_ne_zero : (6 / 5 : ℝ≥0∞) ≠ 0 :=
  (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (6 / 5 : ℝ≥0∞).toReal)).1.ne'

private theorem six_fifths_ne_top : (6 / 5 : ℝ≥0∞) ≠ ⊤ :=
  (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (6 / 5 : ℝ≥0∞).toReal)).2.ne

private theorem twelve_fifths_ne_zero : (12 / 5 : ℝ≥0∞) ≠ 0 :=
  (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (12 / 5 : ℝ≥0∞).toReal)).1.ne'

/-- Scalar Hölder with finite real-valued norms. -/
theorem scalar_product_bound {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {f g : Space → ℝ} (hf : MemLp f p volume) (hg : MemLp g q volume) :
    MemLp (fun x => f x * g x) r volume ∧
      comparisonLpNorm r (fun x => f x * g x) ≤ comparisonLpNorm p f * comparisonLpNorm q g := by
  have hprod : MemLp (fun x => f x * g x) r volume := hg.mul' hf
  have hb : eLpNorm (fun x => f x * g x) r volume ≤
      eLpNorm f p volume * eLpNorm g q volume := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hf.1 hg.1
      (fun a b : ℝ => a * b) 1
      (Eventually.of_forall fun x => by simp [norm_mul])
  refine ⟨hprod, ?_⟩
  simpa only [comparisonLpNorm, ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) hb

/-- The scalar product of the two vector magnitudes belongs to `L^(6/5)`. -/
theorem cross_norm_bound {u w : Space → Space}
    (hu : MemLp u 3 volume) (hw : MemLp w 2 volume) :
    MemLp (fun x => ‖u x‖ * ‖w x‖) (6 / 5) volume ∧
      comparisonLpNorm (6 / 5) (fun x => ‖u x‖ * ‖w x‖) ≤ comparisonLpNorm 3 u * comparisonLpNorm 2
          w := by
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 2 (6 / 5) := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
      (ENNReal.inv_ne_top.mpr six_fifths_ne_zero)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num⟩
  simpa only [comparisonLpNorm, eLpNorm_norm] using scalar_product_bound (r := 6 / 5) hu.norm
      hw.norm

/-- The quadratic weighted difference has the endpoint interpolation bound. -/
theorem quadratic_cutoff_bound {φ : Space → ℝ} {w : Space → Space}
    (hφm : AEStronglyMeasurable φ volume) (hφ0 : ∀ x, 0 ≤ φ x)
    (hw : MemLp w 2 volume)
    (hweighted : MemLp (fun x => φ x ^ 4 • w x) 6 volume) :
    MemLp (fun x => ‖φ x • w x‖ ^ 2) (6 / 5) volume ∧
      comparisonLpNorm (6 / 5) (fun x => ‖φ x • w x‖ ^ 2) ≤
        comparisonLpNorm 2 w ^ (3 / 2 : ℝ) *
          comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (1 / 2 : ℝ) := by
  obtain ⟨hmem, hb⟩ := WeightedInterpolation.cutoff_interpolation_twelve_fifths
    hφm hφ0 hw hweighted
  let : ENNReal.HolderTriple (12 / 5 : ℝ≥0∞) (12 / 5) (6 / 5) := ⟨by
    have h12 := ENNReal.inv_ne_top.mpr twelve_fifths_ne_zero
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨h12, h12⟩)
      (ENNReal.inv_ne_top.mpr six_fifths_ne_zero)).mp
    rw [ENNReal.toReal_add h12 h12]
    norm_num⟩
  obtain ⟨hprod, hprodb⟩ := scalar_product_bound (r := 6 / 5) hmem.norm hmem.norm
  have hQ : MemLp (fun x => ‖φ x • w x‖ ^ 2) (6 / 5) volume := by
    simpa only [pow_two] using hprod
  have hQb : comparisonLpNorm (6 / 5) (fun x => ‖φ x • w x‖ ^ 2) ≤
      comparisonLpNorm (12 / 5) (fun x => φ x • w x) ^ 2 := by
    simpa only [pow_two, comparisonLpNorm, eLpNorm_norm] using hprodb
  have hA := LpNormTools.lpNorm_nonneg (12 / 5) (fun x => φ x • w x)
  have hM := LpNormTools.lpNorm_nonneg 2 w
  have hB := LpNormTools.lpNorm_nonneg 6 (fun x => φ x ^ 4 • w x)
  refine ⟨hQ, hQb.trans ?_⟩
  calc
    comparisonLpNorm (12 / 5) (fun x => φ x • w x) ^ 2 ≤
        (comparisonLpNorm 2 w ^ (3 / 4 : ℝ) *
          comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (1 / 4 : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ hA hb 2
    _ = comparisonLpNorm 2 w ^ (3 / 2 : ℝ) *
        comparisonLpNorm 6 (fun x => φ x ^ 4 • w x) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast _ 2,
        Real.mul_rpow (Real.rpow_nonneg hM _) (Real.rpow_nonneg hB _),
        ← Real.rpow_mul hM, ← Real.rpow_mul hB]
      norm_num

/-- The tensor identity uses the actual difference of the two velocities. -/
theorem tensorDiff_eq (u v : VelocityField) (t : ℝ) (i j : Fin 3) (x : Space) :
    tensorDiff u v t i j x =
      u (t, x) i * (u - v) (t, x) j +
        (u - v) (t, x) i * u (t, x) j -
        (u - v) (t, x) i * (u - v) (t, x) j := by
  change u (t, x) i * u (t, x) j - v (t, x) i * v (t, x) j =
    u (t, x) i * (u (t, x) j - v (t, x) j) +
      (u (t, x) i - v (t, x) i) * u (t, x) j -
      (u (t, x) i - v (t, x) i) * (u (t, x) j - v (t, x) j)
  ring

theorem continuous_component {f : Space → Space} (hf : Continuous f) (i : Fin 3) :
    Continuous (fun x => f x i) :=
  (continuous_apply i).comp ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp hf)

theorem continuous_tensorDiff {u v : VelocityField} {t : ℝ}
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (i j : Fin 3) : Continuous (tensorDiff u v t i j) :=
  ((continuous_component hu i).mul (continuous_component hu j)).sub
    ((continuous_component hv i).mul (continuous_component hv j))

/-- Pointwise domination is uniform in both tensor indices. -/
theorem norm_weighted_tensorDiff_le (u v : VelocityField) (t : ℝ) (i j : Fin 3)
    (x : Space) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖s ^ 2 * tensorDiff u v t i j x‖ ≤
      2 * (‖u (t, x)‖ * ‖(u - v) (t, x)‖) + ‖s • (u - v) (t, x)‖ ^ 2 := by
  let a := u (t, x)
  let w := (u - v) (t, x)
  have hcross1 : ‖a i * w j‖ ≤ ‖a‖ * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le a i) (PiLp.norm_apply_le w j)
      (norm_nonneg _) (norm_nonneg _)
  have hcross2 : ‖w i * a j‖ ≤ ‖w‖ * ‖a‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le w i) (PiLp.norm_apply_le a j)
      (norm_nonneg _) (norm_nonneg _)
  have hquad : ‖w i * w j‖ ≤ ‖w‖ * ‖w‖ := by
    rw [norm_mul]
    exact mul_le_mul (PiLp.norm_apply_le w i) (PiLp.norm_apply_le w j)
      (norm_nonneg _) (norm_nonneg _)
  have ht : ‖tensorDiff u v t i j x‖ ≤ 2 * (‖a‖ * ‖w‖) + ‖w‖ ^ 2 := by
    rw [tensorDiff_eq]
    calc
      ‖a i * w j + w i * a j - w i * w j‖ ≤
          ‖a i * w j + w i * a j‖ + ‖w i * w j‖ := norm_sub_le _ _
      _ ≤ (‖a i * w j‖ + ‖w i * a j‖) + ‖w i * w j‖ :=
        add_le_add_left (norm_add_le _ _) _
      _ ≤ (‖a‖ * ‖w‖ + ‖w‖ * ‖a‖) + ‖w‖ * ‖w‖ :=
        add_le_add (add_le_add hcross1 hcross2) hquad
      _ = _ := by ring
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs0 hs1
  calc
    ‖s ^ 2 * tensorDiff u v t i j x‖ = s ^ 2 * ‖tensorDiff u v t i j x‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]
    _ ≤ s ^ 2 * (2 * (‖a‖ * ‖w‖) + ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg s)
    _ ≤ 2 * (‖a‖ * ‖w‖) + ‖s • w‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs2) (mul_nonneg (norm_nonneg a) (norm_nonneg w))]

/-- Compactness supplies finite weighted tensor norms without any growth
assumption on either velocity. -/
theorem weighted_tensorDiff_memLp {φ : Space → ℝ} {u v : VelocityField} {t : ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (i j : Fin 3) (p : ℝ≥0∞) :
    MemLp (fun x => φ x ^ 2 * tensorDiff u v t i j x) p volume := by
  have hp : HasCompactSupport (fun x => φ x ^ 2) :=
    hs.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  exact ((hφ.pow 2).mul (continuous_tensorDiff hu hv i j)).memLp_of_hasCompactSupport hp.mul_right

/-- The weighted tensor estimate used by the localized pressure argument.
It has the same constant for every pair of indices. -/
theorem weighted_tensorDiff_bound {φ : Space → ℝ} {u v : VelocityField} {t : ℝ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hu : Continuous (fun x => u (t, x))) (hv : Continuous (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) (i j : Fin 3) :
    MemLp (fun x => φ x ^ 2 * tensorDiff u v t i j x) (6 / 5) volume ∧
      comparisonLpNorm (6 / 5) (fun x => φ x ^ 2 * tensorDiff u v t i j x) ≤
        comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
          cutoffL6 φ (u - v) t ^ (1 / 2 : ℝ) +
        2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x))
            := by
  let P : Space → ℝ := fun x => ‖u (t, x)‖ * ‖(u - v) (t, x)‖
  let Q : Space → ℝ := fun x => ‖φ x • (u - v) (t, x)‖ ^ 2
  obtain ⟨hP, hPb⟩ := cross_norm_bound hu3 hw2
  have hweighted := WeightedSobolev.memLp_cutoff_pow_smul hφ hs (hu.sub hv)
    (by norm_num : (4 : ℕ) ≠ 0) 6
  obtain ⟨hQ, hQb⟩ := quadratic_cutoff_bound hφ.aestronglyMeasurable hφ0 hw2 hweighted
  change MemLp P (6 / 5) volume at hP
  change comparisonLpNorm (6 / 5) P ≤ _ at hPb
  change MemLp Q (6 / 5) volume at hQ
  change comparisonLpNorm (6 / 5) Q ≤ _ at hQb
  have h2P : MemLp (fun x => (2 : ℝ) • P x) (6 / 5) volume := hP.const_smul (2 : ℝ)
  refine ⟨weighted_tensorDiff_memLp hφ hs hu hv i j (6 / 5), ?_⟩
  calc
    comparisonLpNorm (6 / 5) (fun x => φ x ^ 2 * tensorDiff u v t i j x) ≤
        comparisonLpNorm (6 / 5) (fun x => (2 : ℝ) • P x + Q x) := by
      apply LpNormTools.lpNorm_mono_of_norm_le (h2P.add hQ)
      intro x
      change ‖φ x ^ 2 * tensorDiff u v t i j x‖ ≤ ‖2 * P x + Q x‖
      have hn : ‖2 * P x + Q x‖ = 2 * P x + Q x := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        dsimp [P, Q]
        positivity
      rw [hn]
      exact norm_weighted_tensorDiff_le u v t i j x (hφ0 x) (hφ1 x)
    _ ≤ comparisonLpNorm (6 / 5) (fun x => (2 : ℝ) • P x) + comparisonLpNorm (6 / 5) Q :=
      LpNormTools.lpNorm_add_le (by
        apply (ENNReal.toReal_le_toReal ENNReal.one_ne_top six_fifths_ne_top).mp
        norm_num) h2P hQ
    _ = 2 * comparisonLpNorm (6 / 5) P + comparisonLpNorm (6 / 5) Q := by
      rw [LpNormTools.lpNorm_const_smul]
      norm_num
    _ ≤ _ := by
      change 2 * comparisonLpNorm (6 / 5) P + comparisonLpNorm (6 / 5) Q ≤
        comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
          comparisonLpNorm 6 (fun x => φ x ^ 4 • (u - v) (t, x)) ^ (1 / 2 : ℝ) +
        2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t, x))
      nlinarith

end NavierStokesR3.LocalizedTensorBounds

end
end

end

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology BigOperators

namespace NavierStokesR3.PressureFlux

open ProblemStatement Comparison

theorem lpNorm_ofReal (p : ℝ≥0∞) (f : Space → ℝ) :
    comparisonLpNorm p (fun x => (f x : ℂ)) = comparisonLpNorm p f := by
  apply congrArg ENNReal.toReal
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => Complex.norm_real (f x))

theorem norm_fderiv_ofReal {f : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (fun y => (f y : ℂ)) x‖ = ‖fderiv ℝ f x‖ := by
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at hd
  rw [hd]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    change ‖(fderiv ℝ f x y : ℂ)‖ ≤ ‖fderiv ℝ f x‖ * ‖y‖
    simpa only [Complex.norm_real] using (fderiv ℝ f x).le_opNorm y
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    have h := (Complex.ofRealCLM.comp (fderiv ℝ f x)).le_opNorm y
    change ‖(fderiv ℝ f x y : ℂ)‖ ≤ _ at h
    simpa only [Complex.norm_real] using h

theorem lpNorm_fderiv_realTest (p : ℝ≥0∞) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    comparisonLpNorm p (fderiv ℝ (fun x => PressureRecovery.realTest f hf hc x)) =
      comparisonLpNorm p (fderiv ℝ f) := by
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_norm_ae
  exact Eventually.of_forall fun x =>
    norm_fderiv_ofReal ((contDiff_infty.1 hf 1).differentiable (by simp) x)

theorem cutoff_lipschitz {R : ℝ} (hR : 0 < R) (x y : Space) :
    |ComparisonCutoffs.cutoff R x - ComparisonCutoffs.cutoff R y| ≤
      (ComparisonCutoffs.derivativeConstant 1 / R) * ‖x - y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (univ : Set Space)) =>
      (contDiff_infty.1 (ComparisonCutoffs.cutoff_smooth R) 1).differentiable (by simp) z)
    (fun z (_ : z ∈ (univ : Set Space)) => ComparisonCutoffs.cutoff_fderiv_le hR z)
    (convex_univ : Convex ℝ (univ : Set Space)) (mem_univ y) (mem_univ x)
  exact h

private instance holder_six_fifths_six :
    ENNReal.HolderTriple (6 / 5) 6 1 := ⟨by
  have hz : (6 / 5 : ℝ≥0∞) ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (6 / 5 : ℝ≥0∞).toReal)).1.ne'
  have hn := ENNReal.inv_ne_top.mpr hz
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨hn, by norm_num⟩)
    (by norm_num)).mp
  rw [ENNReal.toReal_add hn (by norm_num)]
  norm_num⟩

theorem integrable_holder_pair {f : Space → ℝ} {g : Space → ℂ}
    (hf : MemLp f (6 / 5) volume) (hg : MemLp g 6 volume) :
    Integrable (fun x => (f x : ℂ) * g x) volume :=
  hf.ofReal.integrable_mul hg

theorem norm_holder_pair_le {f : Space → ℝ} {g : Space → ℂ}
    (hf : MemLp f (6 / 5) volume) (hg : MemLp g 6 volume) :
    ‖∫ x, (f x : ℂ) * g x‖ ≤ comparisonLpNorm (6 / 5) f * comparisonLpNorm 6 g := by
  have hfc : MemLp (fun x => (f x : ℂ)) (6 / 5) volume := hf.ofReal
  have he : eLpNorm (fun x => (f x : ℂ) * g x) 1 volume ≤
      eLpNorm (fun x => (f x : ℂ)) (6 / 5) volume * eLpNorm g 6 volume := by
    simpa only [ENNReal.coe_one, one_mul] using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hfc.1 hg.1
        (fun a b : ℂ => a * b) 1
        (Eventually.of_forall fun x => by simp [nnnorm_mul])
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hfc.eLpNorm_ne_top hg.eLpNorm_ne_top) he
  change comparisonLpNorm 1 (fun x => (f x : ℂ) * g x) ≤
    (eLpNorm (fun x => (f x : ℂ)) (6 / 5) volume * eLpNorm g 6 volume).toReal at ht
  rw [ENNReal.toReal_mul] at ht
  change comparisonLpNorm 1 (fun x => (f x : ℂ) * g x) ≤
    comparisonLpNorm (6 / 5) (fun x => (f x : ℂ)) * comparisonLpNorm 6 g at ht
  rw [lpNorm_ofReal] at ht
  calc
    ‖∫ x, (f x : ℂ) * g x‖ ≤ ∫ x, ‖(f x : ℂ) * g x‖ := norm_integral_le_integral_norm _
    _ = comparisonLpNorm 1 (fun x => (f x : ℂ) * g x) :=
      (LpNormTools.lpNorm_one_eq_integral_norm (integrable_holder_pair hf hg)).symm
    _ ≤ _ := ht

/-- The scalar test in the localized pressure flux. -/
noncomputable def fluxFunction (χ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  fderiv ℝ χ x (w x)

theorem fluxFunction_smooth {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fluxFunction χ w) :=
  (hχ.fderiv_right (m := ∞) (by simp)).clm_apply hw

theorem fluxFunction_compact {χ : Space → ℝ} (hc : HasCompactSupport χ)
    (w : Space → Space) : HasCompactSupport (fluxFunction χ w) := by
  apply (hc.fderiv ℝ).mono
  intro x hx
  change fderiv ℝ χ x ≠ 0
  intro hz
  apply hx
  simp [fluxFunction, hz]

/-- The raw complex canonical pairing, with no pressure function selected. -/
def canonicalFlux (g : Fin 3 → Fin 3 → Space → ℝ) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)

theorem canonical_pair_integrable (g : Fin 3 → Fin 3 → Space → ℝ) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hg : ∀ i j, Integrable (g i j) volume) (i j : Fin 3) :
    Integrable (fun x => (g i j x : ℂ) *
      rieszTest i j (PressureRecovery.realTest f hf hc) x) volume := by
  apply RieszTestOperators.integrable_mul_rieszTest
  simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp (hg i j)

theorem norm_canonicalFlux_le {g : Fin 3 → Fin 3 → Space → ℝ} {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {C : ℝ}
    (hbound : ∀ i j : Fin 3,
      ‖pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)‖ ≤ C) :
    ‖canonicalFlux g f hf hc‖ ≤ 9 * C := by
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
        pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        ‖pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hbound i j))
    _ = 9 * C := by simp; ring

/-- The compact Schwartz test used on the uncommuted side of the Riesz operator. -/
def rTest (R : ℝ) (hR : 0 < R) (w : Space → Space) (hw : ContDiff ℝ ∞ w) :
    ComplexTest :=
  PressureRecovery.realTest (PressureFluxTest.cutoffTest R w)
    (PressureFluxTest.cutoffTest_smooth R hw) (PressureFluxTest.cutoffTest_hasCompactSupport hR w)

/-- The actual flux test `Dχ_R[w]`, represented in the Schwartz space. -/
def fluxTest (R : ℝ) (hR : 0 < R) (w : Space → Space) (hw : ContDiff ℝ ∞ w) :
    ComplexTest :=
  PressureRecovery.realTest (fluxFunction (ComparisonCutoffs.weight R) w)
    (fluxFunction_smooth (ComparisonCutoffs.weight_smooth R) hw)
    (fluxFunction_compact (ComparisonCutoffs.weight_hasCompactSupport hR) w)

@[simp] theorem rTest_apply (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (x : Space) :
    rTest R hR w hw x = (PressureFluxTest.cutoffTest R w x : ℂ) := rfl

@[simp] theorem fluxTest_apply (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (x : Space) :
    fluxTest R hR w hw x = (fderiv ℝ (ComparisonCutoffs.weight R) x (w x) : ℂ) := rfl

theorem fluxTest_eq_multiplier_rTest (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (x : Space) :
    fluxTest R hR w hw x = ComparisonCutoffs.cutoff R x ^ 2 • rTest R hR w hw x := by
  rw [fluxTest_apply, rTest_apply, ← PressureFluxTest.cutoffTest_flux_identity]
  simp [ComparisonCutoffs.multiplier, Complex.real_smul]

theorem lpNorm_rTest (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (p : ℝ≥0∞) :
    comparisonLpNorm p (rTest R hR w hw : Space → ℂ) = comparisonLpNorm p
        (PressureFluxTest.cutoffTest R w) :=
  lpNorm_ofReal _ _

theorem lpNorm_fderiv_rTest (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) :
    comparisonLpNorm 2 (fderiv ℝ (fun x => rTest R hR w hw x)) =
      comparisonLpNorm 2 (fderiv ℝ (PressureFluxTest.cutoffTest R w)) :=
  lpNorm_fderiv_realTest _ _ _ _

/-- Canonical flux for a time slice of the difference of two velocities. -/
def canonicalCutoffFlux (R : ℝ) (hR : 0 < R) (u v : VelocityField) (t : ℝ)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) : ℂ :=
  canonicalFlux (tensorDiff u v t)
    (fluxFunction (ComparisonCutoffs.weight R) (fun x => (u - v) (t, x)))
    (fluxFunction_smooth (ComparisonCutoffs.weight_smooth R) (hu.sub hv))
    (fluxFunction_compact (ComparisonCutoffs.weight_hasCompactSupport hR) _)

theorem canonicalCutoffFlux_eq_sum (R : ℝ) (hR : 0 < R) (u v : VelocityField) (t : ℝ)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) :
    canonicalCutoffFlux R hR u v t hu hv =
      ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv)) := rfl

theorem norm_canonicalCutoffFlux_le (R : ℝ) (hR : 0 < R) (u v : VelocityField) (t : ℝ)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    {C : ℝ} (hbound : ∀ i j : Fin 3, ‖pressurePair i j (tensorDiff u v t i j)
      (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ ≤ C) :
    ‖canonicalCutoffFlux R hR u v t hu hv‖ ≤ 9 * C :=
  norm_canonicalFlux_le _ _ hbound

theorem actual_flux_eq_canonicalCutoffFlux {T t R : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (ht : t ∈ Ioo 0 T) (hR : 0 < R)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) :
    (∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))) =
      (canonicalCutoffFlux R hR u v t hu hv).re := by
  simpa only [canonicalCutoffFlux, canonicalFlux, fluxFunction] using!
    ActualPressureFlux.pressure_flux_eq_canonical H ht
      (ComparisonCutoffs.weight_smooth R) (ComparisonCutoffs.weight_hasCompactSupport hR)

theorem actual_flux_integrable_and_le_canonicalNorm {T t R : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (ht : t ∈ Ioo 0 T) (hR : 0 < R)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) :
    Integrable (fun x => (p - q) (t, x) *
      fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))) volume ∧
    |∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))| ≤
      ‖canonicalCutoffFlux R hR u v t hu hv‖ := by
  refine ⟨ActualPressureFlux.actual_pressure_flux_integrable H ht
    (ComparisonCutoffs.weight_smooth R) (ComparisonCutoffs.weight_hasCompactSupport hR), ?_⟩
  rw [actual_flux_eq_canonicalCutoffFlux H ht hR hu hv]
  exact Complex.abs_re_le_norm _

/-- The commutator integral in the heat-kernel estimate. -/
def commutatorPair (i j : Fin 3) (h g : Space → ℝ) (ψ ψh : ComplexTest) : ℂ :=
  ∫ x, g x • (rieszTest i j ψh x - h x • rieszTest i j ψ x)

theorem integrable_commutator_pair (i j : Fin 3) {h g : Space → ℝ}
    (hg : Integrable g volume) (hhg : MemLp (fun x => h x * g x) (6 / 5) volume)
    (ψ ψh : ComplexTest) :
    Integrable (fun x => g x • (rieszTest i j ψh x - h x • rieszTest i j ψ x)) volume := by
  have hgc : Integrable (fun x => (g x : ℂ)) volume := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hg
  have hq := RieszTestOperators.integrable_mul_rieszTest i j ψh hgc
  have hl := integrable_holder_pair hhg (RieszTestOperators.memLp_rieszTest_six i j ψ)
  convert! hq.sub hl using 1
  funext x
  simp only [Pi.sub_apply, Complex.real_smul, Complex.ofReal_mul]
  ring

theorem pressurePair_decomposition (i j : Fin 3) {h g : Space → ℝ}
    (hg : Integrable g volume) (hhg : MemLp (fun x => h x * g x) (6 / 5) volume)
    (ψ ψh : ComplexTest) :
    pressurePair i j g ψh =
      (∫ x, (h x * g x : ℝ) * rieszTest i j ψ x) + commutatorPair i j h g ψ ψh := by
  have hgc : Integrable (fun x => (g x : ℂ)) volume := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hg
  have hq := RieszTestOperators.integrable_mul_rieszTest i j ψh hgc
  have hl := integrable_holder_pair hhg (RieszTestOperators.memLp_rieszTest_six i j ψ)
  have he : commutatorPair i j h g ψ ψh = pressurePair i j g ψh -
      (∫ x, (h x * g x : ℝ) * rieszTest i j ψ x) := by
    rw [commutatorPair, pressurePair, ← integral_sub hq hl]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
  simpa only [add_comm] using (eq_sub_iff_add_eq.mp he).symm

theorem norm_pressurePair_le_local_commutator (i j : Fin 3) {h g : Space → ℝ}
    (hg : Integrable g volume) (hhg : MemLp (fun x => h x * g x) (6 / 5) volume)
    (ψ ψh : ComplexTest) :
    ‖pressurePair i j g ψh‖ ≤ comparisonLpNorm (6 / 5) (fun x => h x * g x) *
      comparisonLpNorm 6 (rieszTest i j ψ) + ‖commutatorPair i j h g ψ ψh‖ := by
  rw [pressurePair_decomposition i j hg hhg]
  exact (norm_add_le _ _).trans (add_le_add_left
    (norm_holder_pair_le hhg (RieszTestOperators.memLp_rieszTest_six i j ψ)) _)

/-- The fixed constant in the actual Riesz-test Sobolev inequality. -/
def rieszSobolevConstant : ℝ := 3 * WeightedSobolev.sobolevConstant

theorem rieszSobolevConstant_nonneg : 0 ≤ rieszSobolevConstant :=
  mul_nonneg (by norm_num) WeightedSobolev.sobolevConstant_nonneg

/-- Local pair constant, given by `rieszSobolevConstant *
PressureFluxTest.cutoffDerivativeConstant`. -/
def localPairConstant : ℝ := rieszSobolevConstant * PressureFluxTest.cutoffDerivativeConstant

theorem localPairConstant_nonneg : 0 ≤ localPairConstant :=
  mul_nonneg rieszSobolevConstant_nonneg PressureFluxTest.cutoffDerivativeConstant_pos.le

theorem riesz_rTest_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) (i j : Fin 3) :
    comparisonLpNorm 6 (rieszTest i j (rTest R hR w hw)) ≤ localPairConstant *
      (Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) / R +
        comparisonLpNorm 2 w / R ^ 2) := by
  calc
    _ ≤ rieszSobolevConstant * comparisonLpNorm 2 (fderiv ℝ (fun x => rTest R hR w hw x)) := by
      simpa only [rieszSobolevConstant, WeightedSobolev.sobolevConstant] using
        RieszTestOperators.lpNorm_six_rieszTest_le i j (rTest R hR w hw)
    _ = rieszSobolevConstant * comparisonLpNorm 2 (fderiv ℝ (PressureFluxTest.cutoffTest R w)) := by
      rw [lpNorm_fderiv_rTest]
    _ ≤ rieszSobolevConstant * ((PressureFluxTest.cutoffDerivativeConstant / R) *
        Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) +
          (PressureFluxTest.cutoffDerivativeConstant / R ^ 2) * comparisonLpNorm 2 w) :=
      mul_le_mul_of_nonneg_left (PressureFluxTest.cutoffTest_derivative_bound hR hw hw2).2
        rieszSobolevConstant_nonneg
    _ = _ := by unfold localPairConstant; ring

theorem rTest_four_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) :
    comparisonLpNorm 4 (rTest R hR w hw : Space → ℂ) ≤
      (8 * ComparisonCutoffs.derivativeConstant 1 / R) * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  rw [lpNorm_rTest]
  exact (PressureFluxTest.cutoffTest_four_bound hR hw hw2).2

/-- The local part of one canonical pressure component is an actual integrable pairing. -/
theorem localized_pair_bound {R : ℝ} (hR : 0 < R) {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume) (i j : Fin 3) :
    Integrable (fun x => (ComparisonCutoffs.multiplier R x * tensorDiff u v t i j x : ℝ) *
      rieszTest i j (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv)) x) volume ∧
    ‖∫ x, (ComparisonCutoffs.multiplier R x * tensorDiff u v t i j x : ℝ) *
      rieszTest i j (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv)) x‖ ≤
      localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t,
              x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) := by
  have ht := LocalizedTensorBounds.weighted_tensorDiff_bound
    (ComparisonCutoffs.cutoff_smooth R).continuous
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hu.continuous hv.continuous hw2 hu3
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R) i j
  have hr := RieszTestOperators.memLp_rieszTest_six i j
    (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))
  refine ⟨integrable_holder_pair ht.1 hr, ?_⟩
  have hM := LpNormTools.lpNorm_nonneg 2 (fun x => (u - v) (t, x))
  have hU := LpNormTools.lpNorm_nonneg 3 (fun x => u (t, x))
  have hB := LpNormTools.lpNorm_nonneg 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • (u - v) (t,
      x))
  calc
    _ ≤ comparisonLpNorm (6 / 5) (fun x => ComparisonCutoffs.cutoff R x ^ 2 * tensorDiff u v t i j
        x) *
        comparisonLpNorm 6 (rieszTest i j (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))) :=
      norm_holder_pair_le ht.1 hr
    _ ≤ (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t,
              x))) *
        (localPairConstant * (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2)) := by
      apply mul_le_mul ht.2 (riesz_rTest_bound hR (hu.sub hv) hw2 i j)
        (LpNormTools.lpNorm_nonneg _ _)
      unfold cutoffL6
      positivity
    _ = _ := by ring

theorem norm_cutoff_pressurePair_le_local_commutator {R : ℝ} (hR : 0 < R)
    {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume) (i j : Fin 3)
    (hg : Integrable (tensorDiff u v t i j) volume) :
    ‖pressurePair i j (tensorDiff u v t i j)
      (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ ≤
      localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t,
              x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) +
      ‖commutatorPair i j (ComparisonCutoffs.multiplier R) (tensorDiff u v t i j)
        (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))
        (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ := by
  have ht := LocalizedTensorBounds.weighted_tensorDiff_bound
    (ComparisonCutoffs.cutoff_smooth R).continuous
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hu.continuous hv.continuous hw2 hu3
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R) i j
  rw [pressurePair_decomposition i j hg ht.1]
  exact (norm_add_le _ _).trans (add_le_add_left (localized_pair_bound hR hu hv hw2 hu3 i j).2 _)

/-- The coefficient after fixing uniform bounds for the three data norms. -/
def uniformCoefficient (C₁ C₂ M₀ U₀ G₀ : ℝ) : ℝ :=
  C₁ * (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (M₀ + 1) +
    C₂ * G₀ * M₀ ^ (1 / 4 : ℝ)

theorem uniformCoefficient_nonneg {C₁ C₂ M₀ U₀ G₀ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀) :
    0 ≤ uniformCoefficient C₁ C₂ M₀ U₀ G₀ := by
  unfold uniformCoefficient
  positivity

/-- Collecting constants uses only the fixed data-norm bounds, not the radius. -/
theorem uniform_expression_bound {C₁ C₂ M₀ U₀ G₀ M U G A B R : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (_hG : 0 ≤ G) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hMM : M ≤ M₀) (hUU : U ≤ U₀) (hGG : G ≤ G₀) (hR : 0 < R) :
    C₁ * (M ^ (3 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + 2 * M * U) *
        (A / R + M / R ^ 2) +
      C₂ * G * M ^ (1 / 4 : ℝ) * R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) ≤
    uniformCoefficient C₁ C₂ M₀ U₀ G₀ *
      ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
        R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ)) := by
  have hMp := Real.rpow_le_rpow hM hMM (by norm_num : 0 ≤ (3 / 2 : ℝ))
  have hMp₄ := Real.rpow_le_rpow hM hMM (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hB₁ := Real.rpow_nonneg hB (1 / 2 : ℝ)
  have hB₃ := Real.rpow_nonneg hB (3 / 4 : ℝ)
  have hM₀p := Real.rpow_nonneg hM₀ (3 / 2 : ℝ)
  have hM₀p₄ := Real.rpow_nonneg hM₀ (1 / 4 : ℝ)
  have hRp := Real.rpow_nonneg hR.le (-(7 / 4 : ℝ))
  have hMU : 2 * M * U ≤ 2 * M₀ * U₀ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hMM (by norm_num)) hUU hU (by positivity)
  have hT : M ^ (3 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + 2 * M * U ≤
      (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (B ^ (1 / 2 : ℝ) + 1) := by
    have h := add_le_add (mul_le_mul_of_nonneg_right hMp hB₁) hMU
    have hm0u0 : 0 ≤ 2 * M₀ * U₀ := by positivity
    exact h.trans (by nlinarith only [hM₀p, mul_nonneg hm0u0 hB₁])
  have hAR : 0 ≤ A / R := div_nonneg hA hR.le
  have hInv : 0 ≤ 1 / R ^ 2 := by positivity
  have hD : A / R + M / R ^ 2 ≤ (M₀ + 1) * (A / R + 1 / R ^ 2) := by
    have hdiv := (div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2 hMM
    have hdiv' : M / R ^ 2 ≤ M₀ * (1 / R ^ 2) := by simpa only [mul_one_div] using hdiv
    nlinarith only [hdiv', mul_nonneg hM₀ hAR, hInv]
  have hlocal :
      C₁ * (M ^ (3 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + 2 * M * U) * (A / R + M / R ^ 2) ≤
      (C₁ * (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (M₀ + 1)) *
        ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2)) := by
    calc
      _ ≤ (C₁ * ((M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (B ^ (1 / 2 : ℝ) + 1))) *
          ((M₀ + 1) * (A / R + 1 / R ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hT hC₁) hD (by positivity) (by positivity)
      _ = _ := by ring
  have hcoeff : C₂ * G * M ^ (1 / 4 : ℝ) ≤ C₂ * G₀ * M₀ ^ (1 / 4 : ℝ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hGG hC₂) hMp₄
      (Real.rpow_nonneg hM _) (mul_nonneg hC₂ hG₀)
  have hcomm : C₂ * G * M ^ (1 / 4 : ℝ) * R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) ≤
      (C₂ * G₀ * M₀ ^ (1 / 4 : ℝ)) * (R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ)) := by
    calc
      _ = (C₂ * G * M ^ (1 / 4 : ℝ)) * (R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hRp hB₃)
  have hK₁ : 0 ≤ C₁ * (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (M₀ + 1) := by positivity
  have hK₂ : 0 ≤ C₂ * G₀ * M₀ ^ (1 / 4 : ℝ) := by positivity
  have hE₁ : 0 ≤ (B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) := by positivity
  have hE₂ : 0 ≤ R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) := mul_nonneg hRp hB₃
  unfold uniformCoefficient
  nlinarith only [add_le_add hlocal hcomm, mul_nonneg hK₁ hE₂, mul_nonneg hK₂ hE₁]

theorem rpow_three_fourths_div {R : ℝ} (hR : 0 < R) :
    R ^ (-(3 / 4 : ℝ)) / R = R ^ (-(7 / 4 : ℝ)) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one R, ← Real.rpow_add hR]
  norm_num

/-- The fixed coefficient after combining the commutator and test-function bounds. -/
def commutatorConstant : ℝ :=
  (Comparison.rieszCommutatorConstant * max (2 * ComparisonCutoffs.derivativeConstant 1) 1) *
    (8 * ComparisonCutoffs.derivativeConstant 1)

theorem commutatorConstant_nonneg : 0 ≤ commutatorConstant := by
  have hH := Comparison.rieszCommutatorConstant_pos.le
  have hD := (ComparisonCutoffs.derivativeConstant_pos 1).le
  have hm : 0 ≤ max (2 * ComparisonCutoffs.derivativeConstant 1) 1 :=
    zero_le_one.trans (le_max_right _ _)
  unfold commutatorConstant
  positivity

theorem cutoff_commutator_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) {g : Space → ℝ}
    (hg : Integrable g volume) (i j : Fin 3) :
    ‖commutatorPair i j (ComparisonCutoffs.multiplier R) g
      (rTest R hR w hw) (fluxTest R hR w hw)‖ ≤
      commutatorConstant * comparisonLpNorm 1 g * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        R ^ (-(7 / 4 : ℝ)) *
          comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  have h := Comparison.riesz_commutator_pair_bound i j hR
    (ComparisonCutoffs.cutoff_smooth R).continuous.measurable
    (ComparisonCutoffs.cutoff_mem_Icc R) (cutoff_lipschitz hR) hg
    (rTest R hR w hw) (fluxTest R hR w hw)
    (fluxTest_eq_multiplier_rTest R hR w hw) ((rTest R hR w hw).memLp 4)
  have hH := Comparison.rieszCommutatorConstant_pos.le
  have hD := (ComparisonCutoffs.derivativeConstant_pos 1).le
  have hm : 0 ≤ max (2 * ComparisonCutoffs.derivativeConstant 1) 1 :=
    zero_le_one.trans (le_max_right _ _)
  have hG := LpNormTools.lpNorm_nonneg 1 g
  have hRp := Real.rpow_nonneg hR.le (-(3 / 4 : ℝ))
  calc
    _ ≤ (Comparison.rieszCommutatorConstant * max (2 * ComparisonCutoffs.derivativeConstant 1) 1) *
        R ^ (-(3 / 4 : ℝ)) * comparisonLpNorm 1 g * comparisonLpNorm 4 (rTest R hR w hw : Space →
            ℂ) := h
    _ ≤ (Comparison.rieszCommutatorConstant * max (2 * ComparisonCutoffs.derivativeConstant 1) 1) *
        R ^ (-(3 / 4 : ℝ)) * comparisonLpNorm 1 g *
          ((8 * ComparisonCutoffs.derivativeConstant 1 / R) * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
            comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (rTest_four_bound hR hw hw2) (by positivity)
    _ = _ := by
      rw [← rpow_three_fourths_div hR]
      unfold commutatorConstant
      ring

/-- One actual canonical pressure component, with the three data norms explicit. -/
theorem cutoff_pressurePair_bound {R : ℝ} (hR : 0 < R) {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume) (i j : Fin 3)
    (hg : Integrable (tensorDiff u v t i j) volume) :
    ‖pressurePair i j (tensorDiff u v t i j)
      (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ ≤
      localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t,
              x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) +
      commutatorConstant * comparisonLpNorm 1 (tensorDiff u v t i j) *
        comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (1 / 4 : ℝ) * R ^ (-(7 / 4 : ℝ)) *
          cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ) :=
  (norm_cutoff_pressurePair_le_local_commutator hR hu hv hw2 hu3 i j hg).trans
    (add_le_add_right (cutoff_commutator_bound hR (hu.sub hv) hw2 hg i j) _)

/-- The full canonical flux with an explicit bound on each tensor component's `L¹` norm. -/
theorem canonicalCutoffFlux_bound {R : ℝ} (hR : 0 < R) {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume)
    (hg : ∀ i j : Fin 3, Integrable (tensorDiff u v t i j) volume)
    {G : ℝ} (hG : ∀ i j : Fin 3, comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G) :
    ‖canonicalCutoffFlux R hR u v t hu hv‖ ≤ 9 *
      (localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t,
              x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) +
      commutatorConstant * G * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (1 / 4 : ℝ) *
        R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ)) := by
  apply norm_canonicalCutoffFlux_le
  intro i j
  refine (cutoff_pressurePair_bound hR hu hv hw2 hu3 i j (hg i j)).trans (add_le_add_right ?_ _)
  have hM := Real.rpow_nonneg
    (LpNormTools.lpNorm_nonneg 2 (fun x => (u - v) (t, x))) (1 / 4 : ℝ)
  have hB := Real.rpow_nonneg
    (LpNormTools.lpNorm_nonneg 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • (u - v) (t, x)))
    (3 / 4 : ℝ)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hG i j) commutatorConstant_nonneg) hM)
      (Real.rpow_nonneg hR.le _)) hB

/-- One constant works for all radii and all smooth slices satisfying the fixed norm bounds. -/
theorem exists_uniform_canonicalCutoffFlux_bound (M₀ U₀ G₀ : ℝ)
    (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ (R : ℝ) (hR : 1 ≤ R) (u v : VelocityField) (t : ℝ)
      (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))),
      MemLp (fun x => (u - v) (t, x)) 2 volume →
      MemLp (fun x => u (t, x)) 3 volume →
      (∀ i j : Fin 3, Integrable (tensorDiff u v t i j) volume) →
      comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M₀ →
      comparisonLpNorm 3 (fun x => u (t, x)) ≤ U₀ →
      (∀ i j : Fin 3, comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G₀) →
      ‖canonicalCutoffFlux R (zero_lt_one.trans_le hR) u v t hu hv‖ ≤ CP *
        ((cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) + 1) *
          (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R + 1 / R ^ 2) +
          R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ)) := by
  refine ⟨9 * uniformCoefficient localPairConstant commutatorConstant M₀ U₀ G₀,
    mul_nonneg (by norm_num)
      (uniformCoefficient_nonneg localPairConstant_nonneg commutatorConstant_nonneg hM₀ hU₀ hG₀),
          ?_⟩
  intro R hR u v t hu hv hw2 hu3 hg hM hU hG
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hA : 0 ≤ dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t := Real.sqrt_nonneg _
  have hB : 0 ≤ cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t :=
    LpNormTools.lpNorm_nonneg _ _
  have hn := uniform_expression_bound localPairConstant_nonneg commutatorConstant_nonneg
    hM₀ hU₀ hG₀ (LpNormTools.lpNorm_nonneg 2 (fun x => (u - v) (t, x)))
    (LpNormTools.lpNorm_nonneg 3 (fun x => u (t, x))) hG₀ hA hB hM hU (le_refl G₀) hR0
  have hp := canonicalCutoffFlux_bound hR0 hu hv hw2 hu3 hg hG
  simpa only [mul_assoc] using hp.trans (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 9))

/-- The physical pressure flux has a single bound uniform in time and cutoff radius.
All hypotheses on the pressure are exactly those already present in pressure recovery. -/
theorem exists_uniform_actual_pressure_flux_bound {T : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (M₀ U₀ G₀ : ℝ) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀)
    (hM : ∀ t ∈ Icc 0 T, MemLp (fun x => (u - v) (t, x)) 2 volume ∧
      comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M₀)
    (hU : ∀ t ∈ Icc 0 T, MemLp (fun x => u (t, x)) 3 volume ∧
      comparisonLpNorm 3 (fun x => u (t, x)) ≤ U₀)
    (hG : ∀ t ∈ Icc 0 T, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) volume ∧ comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G₀) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo 0 T,
      |∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))| ≤ CP *
        ((cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) + 1) *
          (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R + 1 / R ^ 2) +
          R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ)) := by
  obtain ⟨CP, hCP, hbound⟩ := exists_uniform_canonicalCutoffFlux_bound M₀ U₀ G₀ hM₀ hU₀ hG₀
  refine ⟨CP, hCP, ?_⟩
  intro R hR t ht
  have ht' : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hu := NavierStokes.PeriodicUniqueness.spatial_smooth H.smooth_u ht'
  have hv := NavierStokes.PeriodicUniqueness.spatial_smooth H.smooth_v ht'
  exact (actual_flux_integrable_and_le_canonicalNorm H ht (zero_lt_one.trans_le hR) hu hv).2.trans
    (hbound R hR u v t hu hv (hM t ht').1 (hU t ht').1 (fun i j => (hG t ht' i j).1)
      (hM t ht').2 (hU t ht').2 (fun i j => (hG t ht' i j).2))

end NavierStokesR3.PressureFlux
