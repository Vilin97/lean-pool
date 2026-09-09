/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureTemporalIdentity
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactSchwartz
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierTestDerivatives
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Compact tests used in pressure recovery

Real compact smooth tests are embedded in the actual complex Schwartz space.
The differential operators commute with this embedding. The pressure identities
below continue to pair the physical pressure only with compact spatial tests.
-/


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
