/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelCancellation
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelFourier
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierConvolution
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelFubini
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelPairedBound

@[expose] public section

/-!
# The pressure commutator

The Fourier-defined double Riesz operator has the actual heat representation.
We first subtract the two time-integrable heat evolutions, insert the cutoff
difference, and only then use the absolute-integrability theorem to interchange
time and space. The resulting kernel has the proved radial `L^(4/3)` majorant.
-/


noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

private theorem real_smul_as_complex_mul (a : ℝ) (z : ℂ) :
    a • z = (a : ℂ) * z := by
  rw [Algebra.smul_def]
  rfl

private theorem integrable_real_smul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ) (a : ℝ) :
    Integrable (fun x => a • f x) μ := by
  simpa only [real_smul_as_complex_mul] using hf.const_mul (a : ℂ)

/-- Each positive-time Fourier multiplier is convolution with the actual heat Hessian. -/
theorem heatSecondTest_eq_convolution {s : ℝ} (hs : 0 < s) (i j : Fin 3)
    (ψ : ComplexTest) (x : Space) :
    heatSecondTest s i j ψ x =
      ∫ y : Space, heatKernelSecond s i j (x - y) • ψ y := by
  change FourierTransform.fourierInv (fun ξ : Space =>
    (heatSecondSymbol s i j ξ : ℂ) * FourierTransform.fourier (fun y => ψ y) ξ) x = _
  rw [fourierIntegralInv_mul_fourier (integrable_heatSecondSymbol_space hs i j)
    ψ.integrable x]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [fourierIntegralInv_heatSecondSymbol hs i j (x - y), real_smul_as_complex_mul]

/-- The spatial heat-Hessian convolution is integrable at each positive time. -/
theorem heatSecondTest_convolution_integrable {s : ℝ} (hs : 0 < s) (i j : Fin 3)
    (ψ : ComplexTest) (x : Space) :
    Integrable (fun y : Space => heatKernelSecond s i j (x - y) • ψ y) := by
  apply (integrable_fourierIntegralInv_convolution
    (integrable_heatSecondSymbol_space hs i j) ψ.integrable x).congr
  filter_upwards [] with y
  rw [fourierIntegralInv_heatSecondSymbol hs i j (x - y), real_smul_as_complex_mul]

/-- The pointwise Riesz commutator equals the absolutely convergent cancelled
heat kernel. The cutoff difference is inserted before spatial/time Fubini. -/
theorem riesz_commutator_eq_heatKernel (i j : Fin 3)
    {φ : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (ψ ψh : ComplexTest) (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψ4 : MemLp (fun x => ψ x) 4 volume) (x : Space) :
    rieszTest i j ψh x - φ x ^ 2 • rieszTest i j ψ x =
      ∫ y : Space, heatCommutatorKernel i j φ x y • ψ y := by
  have htime1 := integrableOn_heatSecondTest i j ψh x
  have htime2 := integrable_real_smul (integrableOn_heatSecondTest i j ψ x) (φ x ^ 2)
  rw [rieszTest_eq_integral_heatSecondTest i j ψh x,
    rieszTest_eq_integral_heatSecondTest i j ψ x, ← integral_smul,
    ← integral_sub htime1 htime2]
  calc
    (∫ s : ℝ in Ioi 0,
        (heatSecondTest s i j ψh x - φ x ^ 2 • heatSecondTest s i j ψ x)) =
        ∫ s : ℝ in Ioi 0, ∫ y : Space,
          (heatKernelSecond s i j (x - y) * cutoffSquareDifference φ x y) • ψ y := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [heatSecondTest_eq_convolution hs i j ψh x,
        heatSecondTest_eq_convolution hs i j ψ x, ← integral_smul,
        ← integral_sub (heatSecondTest_convolution_integrable hs i j ψh x)
          (integrable_real_smul (heatSecondTest_convolution_integrable hs i j ψ x) (φ x ^ 2))]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hψh y]
      exact cutoffSquareDifference_smul (heatKernelSecond s i j (x - y)) φ (ψ y) x y
    _ = ∫ y : Space, heatCommutatorKernel i j φ x y • ψ y := by
      exact cancelledTimeKernel_integral_swap
        (heatKernelSecond_joint_measurable i j) hφm ψ.continuous.measurable
        (fun z hz => heatKernelSecond_integrable_time i j hz)
        heatKernelTimeConstant_pos.le hR
        (fun z hz => heatKernelSecond_integral_abs_le i j hz)
        hφ hLip hψ4 x

/-- The paired pressure commutator bound for the actual Fourier-defined Riesz operator. -/
theorem riesz_commutator_pair_bound (i j : Fin 3)
    {φ g : Space → ℝ} {L R : ℝ}
    (hR : 0 < R) (hφm : Measurable φ) (hφ : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hLip : ∀ x y, |φ x - φ y| ≤ (L / R) * ‖x - y‖)
    (hg : Integrable g volume)
    (ψ ψh : ComplexTest) (hψh : ∀ x, ψh x = φ x ^ 2 • ψ x)
    (hψ4 : MemLp (fun x => ψ x) 4 volume) :
    ‖∫ x : Space, g x • (rieszTest i j ψh x - φ x ^ 2 • rieszTest i j ψ x)‖ ≤
      (rieszCommutatorConstant * max (2 * L) 1) * R ^ (-(3 / 4) : ℝ) *
        comparisonLpNorm 1 g * comparisonLpNorm 4 (fun x => ψ x) := by
  have heq : (fun x : Space => g x •
      (rieszTest i j ψh x - φ x ^ 2 • rieszTest i j ψ x)) =
      (fun x : Space => g x • ∫ y : Space, heatCommutatorKernel i j φ x y • ψ y) := by
    funext x
    rw [riesz_commutator_eq_heatKernel i j hR hφm hφ hLip ψ ψh hψh hψ4 x]
  rw [heq]
  exact heatKernel_paired_commutator_bound i j hR hφm hφ hLip hg hψ4

end NavierStokesR3.Comparison
