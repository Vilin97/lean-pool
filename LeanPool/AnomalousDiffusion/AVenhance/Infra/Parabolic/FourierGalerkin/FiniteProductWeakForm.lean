/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.WeakLimitEquation

/-!
# Finite Galerkin weak form in product-space pairings

The finite ODE identity is expressed using the product-space Hilbert classes so that it can be
passed directly through weak convergence.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The finite Galerkin equation tested by a separated smooth time/Fourier test, written as
three pairings in the common product-space `L²` spaces. -/
theorem FrozenDriftProblem.finite_product_fourier_test_weak_identity
    (P : FrozenDriftProblem) (N : ℕ)
    (d : Coefficients (RealFourierDimension N))
    (η : ℝ → ℝ) (hη : ContDiff ℝ 1 η) (hη₁ : η 1 = 0)
    (hηMem : MemLp η ⊤ GalerkinTimeMeasure)
    (hηDerivMem : MemLp (deriv η) ⊤ GalerkinTimeMeasure) :
    -inner ℝ (P.scalarProductLp N)
        (scalarProductTestLp (deriv η) (realFourierScalarMap N d) hηDerivMem) +
      inner ℝ (P.gradientProductLp N)
        (P.weightedDriftProductTestLp η N d hηMem) +
      P.κ * inner ℝ (P.gradientProductLp N)
        (gradientProductTestLp η (realFourierGradientMap N d) hηMem) =
      η 0 * inner ℝ P.initialTorusL2 (realFourierScalarMap N d) := by
  let ψ := realFourierScalarMap N d
  let g := realFourierGradientMap N d
  let f₀ : ℝ → ℝ := fun t => deriv η t * inner ℝ (P.scalarTimeFunction N t) ψ
  let f₁ : ℝ → ℝ := fun t => η t * realFourierDriftBilinearForm N
    (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) t
    (productExtendedCoefficients P N t) d
  let f₂ : ℝ → ℝ := fun t => η t * inner ℝ (P.gradientTimeFunction N t) g
  have hscalarPair := P.scalarProductLp_pairing_time N (deriv η) hηDerivMem ψ
  have hdriftPair := P.gradientProductLp_weightedDrift_pairing_time N η hηMem d
  have hgradientPair := P.gradientProductLp_pairing_time N η hηMem g
  have hscalarCont' : Continuous (fun t => inner ℝ ψ (P.scalarTimeFunction N t)) :=
    (innerSL ℝ ψ).continuous.comp (scalarTimeFunction_continuous P N)
  have hscalarCont : Continuous (fun t => inner ℝ (P.scalarTimeFunction N t) ψ) :=
    hscalarCont'.congr fun t => by simp [real_inner_comm]
  have hgradientCont' : Continuous (fun t => inner ℝ g (P.gradientTimeFunction N t)) :=
    (innerSL ℝ g).continuous.comp (gradientTimeFunction_continuous P N)
  have hgradientCont : Continuous (fun t => inner ℝ (P.gradientTimeFunction N t) g) :=
    hgradientCont'.congr fun t => by simp [real_inner_comm]
  have hf₀Cont : Continuous f₀ := hη.continuous_deriv_one.mul hscalarCont
  have hf₂Cont : Continuous f₂ := hη.continuous.mul hgradientCont
  have hf₀Int : Integrable f₀ GalerkinTimeMeasure := by
    have htop := continuous_time_memLp_top hf₀Cont
    exact (htop.mono_exponent (by norm_num : (1 : ENNReal) ≤ ⊤)).integrable (by norm_num)
  have hf₁Int : Integrable f₁ GalerkinTimeMeasure :=
    P.weightedDriftProduct_time_integrable N η hηMem d
  have hf₂Int : Integrable f₂ GalerkinTimeMeasure := by
    have htop := continuous_time_memLp_top hf₂Cont
    exact (htop.mono_exponent (by norm_num : (1 : ENNReal) ≤ ⊤)).integrable (by norm_num)
  let y : ℝ → Coefficients (RealFourierDimension N) :=
    AVenhance.Infra.ODE.extendCurve (by norm_num) (P.coefficientPath N)
  let F : ℝ → ℝ := fun t =>
    -(inner ℝ (realFourierScalarMap N (y t)) (realFourierScalarMap N d)) * deriv η t +
      η t * (realFourierDriftBilinearForm N
        (fun s => AVenhance.Infra.Torus.periodicToTorus (P.b s)) t (y t) d +
        P.κ * inner ℝ (realFourierGradientMap N (y t)) (realFourierGradientMap N d))
  have hscalarState (t : ℝ) :
      P.scalarTimeFunction N t = realFourierScalarMap N (y t) := rfl
  have hgradientState (t : ℝ) :
      P.gradientTimeFunction N t = realFourierGradientMap N (y t) := by
    change (P.galerkinData N).gradient (y t) = realFourierGradientMap N (y t)
    rw [FrozenDriftProblem.galerkinData, positiveCutoffGalerkinData]
    change positiveCutoffGradientMap N (y t) = _
    rw [positiveCutoffGradientMap]
  have hfinite := P.finite_fourier_test_weak_identity N d η hη hη₁
  dsimp only at hfinite
  have hFint : ∫ t, F t ∂GalerkinTimeMeasure =
      η 0 * inner ℝ (P.galerkinData N).initial d := by
    have hfinite' := hfinite
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hfinite'
    simpa only [F, y, GalerkinTimeMeasure] using hfinite'
  have hsumPoint (t : ℝ) : F t = -f₀ t + (f₁ t + P.κ * f₂ t) := by
    simp only [F, f₀, f₁, f₂, ψ, g, productExtendedCoefficients, y]
    rw [← hscalarState t, ← hgradientState t]
    ring
  have hsumInt : ∫ t, F t ∂GalerkinTimeMeasure =
      -(∫ t, f₀ t ∂GalerkinTimeMeasure) +
        (∫ t, f₁ t ∂GalerkinTimeMeasure +
          P.κ * ∫ t, f₂ t ∂GalerkinTimeMeasure) := by
    calc
      ∫ t, F t ∂GalerkinTimeMeasure =
          ∫ t, (-f₀ t + (f₁ t + P.κ * f₂ t)) ∂GalerkinTimeMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hsumPoint
      _ = (∫ t, -f₀ t ∂GalerkinTimeMeasure) +
          ∫ t, (f₁ t + P.κ * f₂ t) ∂GalerkinTimeMeasure :=
        integral_add hf₀Int.neg (hf₁Int.add (hf₂Int.const_mul P.κ))
      _ = _ := by
        rw [integral_neg]
        rw [integral_add hf₁Int (hf₂Int.const_mul P.κ)]
        rw [integral_const_mul]
  have hpairs :
      -inner ℝ (P.scalarProductLp N)
          (scalarProductTestLp (deriv η) (realFourierScalarMap N d) hηDerivMem) +
        inner ℝ (P.gradientProductLp N)
          (P.weightedDriftProductTestLp η N d hηMem) +
        P.κ * inner ℝ (P.gradientProductLp N)
          (gradientProductTestLp η (realFourierGradientMap N d) hηMem) =
      -(∫ t, f₀ t ∂GalerkinTimeMeasure) +
        (∫ t, f₁ t ∂GalerkinTimeMeasure + P.κ * ∫ t, f₂ t ∂GalerkinTimeMeasure) := by
    rw [hscalarPair, hdriftPair, hgradientPair]
    simp only [f₀, f₁, f₂]
    ring
  calc
    _ = -(∫ t, f₀ t ∂GalerkinTimeMeasure) +
        (∫ t, f₁ t ∂GalerkinTimeMeasure + P.κ * ∫ t, f₂ t ∂GalerkinTimeMeasure) := hpairs
    _ = ∫ t, F t ∂GalerkinTimeMeasure := by rw [hsumInt]
    _ = η 0 * inner ℝ (P.galerkinData N).initial d := hFint
    _ = η 0 * inner ℝ P.initialTorusL2 (realFourierScalarMap N d) := by
      rw [← P.initialProjection_pairing]

end AVenhance.Infra.Parabolic.FourierGalerkin

end
