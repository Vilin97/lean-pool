/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszSymbolRegularity

/-!
# Heat multipliers for the double Riesz transform

The Fourier convention has a factor `2 * π` in the character.  Consequently the
heat semigroup has multiplier `exp (-4 * π² * s * ‖ξ‖²)`.  Integrating its second
spatial derivative over positive time recovers the double Riesz multiplier.
-/

@[expose] public section



noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace NavierStokesR3.Comparison

open ProblemStatement

private theorem realAlgebraMap_apply (r : ℝ) : (algebraMap ℝ ℂ) r = (r : ℂ) := rfl

/-- The Fourier multiplier of a second derivative of the heat semigroup. -/
def heatSecondSymbol (s : ℝ) (i j : Fin 3) (ξ : Space) : ℝ :=
  -(4 * Real.pi ^ 2 * (ξ i * ξ j)) *
    Real.exp (-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * s)

@[simp] theorem heatSecondSymbol_zero (s : ℝ) (i j : Fin 3) :
    heatSecondSymbol s i j 0 = 0 := by
  simp [heatSecondSymbol]

/-- Positive-time integrability holds also at the zero frequency. -/
theorem integrableOn_heatSecondSymbol (i j : Fin 3) (ξ : Space) :
    IntegrableOn (fun s => heatSecondSymbol s i j ξ) (Ioi 0) := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [heatSecondSymbol_zero]
    exact integrableOn_zero
  · have hpos : 0 < 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
      positivity
    exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hpos) 0).const_mul _

/-- Integrating the heat second-derivative multiplier gives the double Riesz symbol. -/
theorem integral_heatSecondSymbol (i j : Fin 3) (ξ : Space) :
    (∫ s : ℝ in Ioi 0, heatSecondSymbol s i j ξ) = rieszSymbol i j ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [rieszSymbol]
  · have hpos : 0 < 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
      positivity
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hnorm : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
    simp only [heatSecondSymbol]
    rw [integral_const_mul,
      integral_exp_mul_Ioi (neg_neg_of_pos hpos)]
    simp only [mul_zero, Real.exp_zero]
    unfold rieszSymbol
    field_simp

/-- The absolute time integral is the absolute value of the Riesz symbol. -/
theorem integral_norm_heatSecondSymbol (i j : Fin 3) (ξ : Space) :
    (∫ s : ℝ in Ioi 0, ‖heatSecondSymbol s i j ξ‖) = ‖rieszSymbol i j ξ‖ := by
  rw [← integral_heatSecondSymbol i j ξ]
  simp only [heatSecondSymbol, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), integral_const_mul]
  rw [abs_of_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)]

/-- A second derivative of the heat evolution, expressed in frequency space. -/
def heatSecondTest (s : ℝ) (i j : Fin 3) (ψ : ComplexTest) : Space → ℂ :=
  FourierTransform.fourierInv (fun ξ : Space =>
    (heatSecondSymbol s i j ξ : ℂ) * (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ)

private theorem heatSecondTest_eq_integral (s : ℝ) (i j : Fin 3)
    (ψ : ComplexTest) (x : Space) :
    heatSecondTest s i j ψ x =
      ∫ ξ : Space, heatSecondSymbol s i j ξ •
        (Real.fourierChar ⟪ξ, x⟫ • (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ) := by
  rw [heatSecondTest, Real.fourierInv_eq]
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [Circle.smul_def, smul_eq_mul, Algebra.smul_def, realAlgebraMap_apply]
  ring

private theorem integrable_heatFourierProduct (i j : Fin 3) (ψ : ComplexTest)
    (x : Space) :
    Integrable (fun p : Space × ℝ => heatSecondSymbol p.2 i j p.1 •
      (Real.fourierChar ⟪p.1, x⟫ • (FourierTransform.fourierCLE ℂ ComplexTest ψ) p.1))
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
  let ψhat : ComplexTest := FourierTransform.fourierCLE ℂ ComplexTest ψ
  have hs : Continuous (fun p : Space × ℝ => heatSecondSymbol p.2 i j p.1) := by
    unfold heatSecondSymbol
    fun_prop
  have hc : Continuous (fun p : Space × ℝ => heatSecondSymbol p.2 i j p.1 •
      (Real.fourierChar ⟪p.1, x⟫ • ψhat p.1)) :=
    hs.smul ((Real.continuous_fourierChar.comp
      (continuous_fst.inner continuous_const)).smul (ψhat.continuous.comp continuous_fst))
  have hm : AEStronglyMeasurable (fun p : Space × ℝ =>
      heatSecondSymbol p.2 i j p.1 • (Real.fourierChar ⟪p.1, x⟫ • ψhat p.1))
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Ioi 0))) :=
    hc.aestronglyMeasurable
  refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
  · have hslice (ξ : Space) : Integrable
        (fun s : ℝ => heatSecondSymbol s i j ξ •
          (Real.fourierChar ⟪ξ, x⟫ • ψhat ξ))
        ((volume : Measure ℝ).restrict (Ioi 0)) :=
      (integrableOn_heatSecondSymbol i j ξ).smul_const
        (Real.fourierChar ⟪ξ, x⟫ • ψhat ξ)
    exact Filter.Eventually.of_forall hslice
  · refine ψhat.integrable.norm.mono' hm.norm.integral_prod_right' ?_
    filter_upwards [] with ξ
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [norm_smul, Circle.norm_smul, integral_mul_const,
      integral_norm_heatSecondSymbol]
    exact mul_le_of_le_one_left (norm_nonneg _) (RieszTestOperators.norm_rieszSymbol_le i j ξ)

/-- The positive-time representation converges absolutely at each spatial point. -/
theorem integrableOn_heatSecondTest (i j : Fin 3) (ψ : ComplexTest) (x : Space) :
    IntegrableOn (fun s => heatSecondTest s i j ψ x) (Ioi 0) := by
  apply (integrable_heatFourierProduct i j ψ x).integral_prod_right.congr
  exact Filter.Eventually.of_forall fun s => (heatSecondTest_eq_integral s i j ψ x).symm

/-- The actual double Riesz test operator is the positive-time heat integral. -/
theorem rieszTest_eq_integral_heatSecondTest (i j : Fin 3) (ψ : ComplexTest) (x : Space) :
    rieszTest i j ψ x = ∫ s : ℝ in Ioi 0, heatSecondTest s i j ψ x := by
  calc
    rieszTest i j ψ x = ∫ ξ : Space, ∫ s : ℝ in Ioi 0,
        heatSecondSymbol s i j ξ •
          (Real.fourierChar ⟪ξ, x⟫ • (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ) := by
      rw [rieszTest, Real.fourierInv_eq]
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [integral_smul_const, integral_heatSecondSymbol]
      simp only [Circle.smul_def, smul_eq_mul, Algebra.smul_def, realAlgebraMap_apply]
      ring
    _ = ∫ s : ℝ in Ioi 0, ∫ ξ : Space, heatSecondSymbol s i j ξ •
        (Real.fourierChar ⟪ξ, x⟫ • (FourierTransform.fourierCLE ℂ ComplexTest ψ) ξ) :=
      integral_integral_swap (integrable_heatFourierProduct i j ψ x)
    _ = ∫ s : ℝ in Ioi 0, heatSecondTest s i j ψ x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => (heatSecondTest_eq_integral s i j ψ x).symm

end NavierStokesR3.Comparison
