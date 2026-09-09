/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelCancellation
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PairedKernelBound
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RadialKernelBounds

@[expose] public section

/-!
# Fubini after insertion of the cutoff difference

The time kernel is multiplied by the cutoff difference before estimating its
absolute integral. The resulting radial majorant belongs to `L^(4/3)`, so
Hölder with the `L^4` test function proves integrability on space times time.
-/


noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The complex pairing integrand, with cancellation already inserted. -/
def cancelledComplexTimeIntegrand (K : ℝ → Space → ℝ) (φ : Space → ℝ)
    (r : Space → ℂ) (x : Space) (ys : Space × ℝ) : ℂ :=
  (K ys.2 (x - ys.1) * cutoffSquareDifference φ x ys.1) • r ys.1

theorem cancelledComplexTimeIntegrand_measurable {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} {r : Space → ℂ}
    (hK : Measurable (Function.uncurry K)) (hφ : Measurable φ)
    (hr : Measurable r) (x : Space) :
    Measurable (cancelledComplexTimeIntegrand K φ r x) := by
  have hmap : Measurable (fun p : Space × ℝ => ((x, p.1), p.2)) := by fun_prop
  exact ((cancelledTimeIntegrand_measurable hK hφ).comp hmap).smul
    (hr.comp measurable_fst)

private theorem cancelledComplexTimeIntegrand_norm_timeIntegral
    (K : ℝ → Space → ℝ) (φ : Space → ℝ) (r : Space → ℂ) (x y : Space) :
    (∫ s in Ioi (0 : ℝ), ‖cancelledComplexTimeIntegrand K φ r x (y, s)‖) =
      absoluteCancelledTimeKernel K φ x y * ‖r y‖ := by
  simp only [cancelledComplexTimeIntegrand, norm_smul, Real.norm_eq_abs,
    absoluteCancelledTimeKernel, integral_mul_const]

/-- The cancelled integrand is absolutely integrable on the product space.
The time-section hypothesis is needed only away from the origin; cancellation
makes the diagonal section identically zero. -/
theorem cancelledTimeKernel_product_integrable {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} {r : Space → ℂ} {C L R : ℝ}
    (hKmeas : Measurable (Function.uncurry K)) (hφmeas : Measurable φ)
    (hrmeas : Measurable r)
    (hKint : ∀ z ≠ 0, IntegrableOn (fun s => K s z) (Ioi (0 : ℝ)) volume)
    (hC : 0 ≤ C) (hR : 0 < R)
    (hKbound : ∀ z ≠ 0, (∫ s in Ioi (0 : ℝ), |K s z|) ≤ C * ‖z‖ ^ (-3 : ℝ))
    (hφrange : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hr : MemLp r 4 volume) (x : Space) :
    Integrable (cancelledComplexTimeIntegrand K φ r x)
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
  have hD : 0 ≤ C * max (2 * L) 1 :=
    mul_nonneg hC (zero_le_one.trans (le_max_right _ _))
  have hm : AEStronglyMeasurable
      (fun y : Space => absoluteCancelledTimeKernel K φ x y) volume :=
    ((absoluteCancelledTimeKernel_measurable hKmeas hφmeas).comp
      measurable_prodMk_left).aestronglyMeasurable
  have hb : ∀ᵐ y ∂volume, ‖absoluteCancelledTimeKernel K φ x y‖ ≤
      (C * max (2 * L) 1) * radialCommutatorKernel R (x - y) := by
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (absoluteCancelledTimeKernel_nonneg K φ x y)]
    exact absoluteCancelledTimeKernel_le hC hR hKbound hφrange hLip x y
  have hmarginal :=
    PairedKernelBound.dominated_section_integrable_and_integral_norm_le_scaled
      x hm (radialCommutatorKernel_memLp hR) hr.norm hD hb
  have hmeas : AEStronglyMeasurable (cancelledComplexTimeIntegrand K φ r x)
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioi 0))) :=
    (cancelledComplexTimeIntegrand_measurable hKmeas hφmeas hrmeas x).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (cancelledTimeKernel_integrable_time hKint φ x y).smul_const (r y)
  · simpa only [cancelledComplexTimeIntegrand_norm_timeIntegral, smul_eq_mul] using
      hmarginal.1

/-- Cancellation justifies exchanging the heat-time and spatial integrals. -/
theorem cancelledTimeKernel_integral_swap {K : ℝ → Space → ℝ}
    {φ : Space → ℝ} {r : Space → ℂ} {C L R : ℝ}
    (hKmeas : Measurable (Function.uncurry K)) (hφmeas : Measurable φ)
    (hrmeas : Measurable r)
    (hKint : ∀ z ≠ 0, IntegrableOn (fun s => K s z) (Ioi (0 : ℝ)) volume)
    (hC : 0 ≤ C) (hR : 0 < R)
    (hKbound : ∀ z ≠ 0, (∫ s in Ioi (0 : ℝ), |K s z|) ≤ C * ‖z‖ ^ (-3 : ℝ))
    (hφrange : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hr : MemLp r 4 volume) (x : Space) :
    (∫ s in Ioi (0 : ℝ), ∫ y : Space,
      (K s (x - y) * cutoffSquareDifference φ x y) • r y) =
      ∫ y : Space, cancelledTimeKernel K φ x y • r y := by
  have hprod := cancelledTimeKernel_product_integrable hKmeas hφmeas hrmeas
    hKint hC hR hKbound hφrange hLip hr x
  calc
    (∫ s in Ioi (0 : ℝ), ∫ y : Space,
        (K s (x - y) * cutoffSquareDifference φ x y) • r y) =
        ∫ y : Space, ∫ s in Ioi (0 : ℝ),
          (K s (x - y) * cutoffSquareDifference φ x y) • r y := by
      exact (integral_integral_swap
        (f := fun (y : Space) (s : ℝ) =>
          (K s (x - y) * cutoffSquareDifference φ x y) • r y) hprod).symm
    _ = _ := by simp only [cancelledTimeKernel, integral_smul_const]

end NavierStokesR3.Comparison
