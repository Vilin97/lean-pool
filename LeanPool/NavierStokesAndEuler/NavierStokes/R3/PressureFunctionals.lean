/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszLinearityDecay
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierTestDerivatives
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszPairing
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierSobolevWeights
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszSymbolRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.SchwartzParseval

/-!
# The pressure-difference functional on Schwartz tests

The coefficients of the velocity terms belong to ordinary `L²`, and the
tensor coefficients belong to `L¹`. All pairings below are actual Lebesgue
integrals. The final functional uses the spatial Laplacian and coordinate
derivatives from the equation, and the double Riesz test operator.
-/

section

/-! # Fourier bounds for pressure test functionals -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace NavierStokesR3.PressureTestBounds

open ProblemStatement Comparison HarmonicTestFunctionals

/-- The dimension-three integrable weight used in the Fourier Cauchy--Schwarz bound. -/
theorem integrable_inverse_weight_sq :
    Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2)⁻¹ ^ 2) := by
  have h := integrable_rpow_neg_one_add_norm_sq
    (μ := (volume : Measure Space)) (r := 4) (by norm_num [Space,
      NavierStokes.ProblemStatement.Space])
  convert! h using 1
  ext ξ
  norm_num

/-- A finite numerical constant depending only on three-dimensional Lebesgue measure. -/
def fourierMomentConstant : ℝ :=
  Real.sqrt (∫ ξ : Space, (1 + ‖ξ‖ ^ 2)⁻¹ ^ 2)

theorem fourierMomentConstant_nonneg : 0 ≤ fourierMomentConstant :=
  Real.sqrt_nonneg _

/-- The elementary weighted Cauchy--Schwarz estimate behind the `H³` bounds. -/
theorem integral_first_moment_le {f : Space → ℂ}
    (hf : AEStronglyMeasurable f)
    (hw : Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 3 * ‖f ξ‖ ^ 2)) :
    (∫ ξ : Space, ‖ξ‖ * ‖f ξ‖) ≤ fourierMomentConstant *
      Real.sqrt (∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ 3 * ‖f ξ‖ ^ 2) := by
  let a : Space → ℝ := fun ξ => (1 + ‖ξ‖ ^ 2)⁻¹
  let b : Space → ℝ := fun ξ => (1 + ‖ξ‖ ^ 2) * ‖ξ‖ * ‖f ξ‖
  have ha : AEStronglyMeasurable a := by
    exact ((continuous_const.add (continuous_norm.pow 2)).inv₀
      (fun ξ : Space => ne_of_gt (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2))).aestronglyMeasurable
  have hb : AEStronglyMeasurable b := by
    exact (by fun_prop : Continuous
      (fun ξ : Space => (1 + ‖ξ‖ ^ 2) * ‖ξ‖)).aestronglyMeasurable.mul hf.norm
  have hb_le (ξ : Space) : b ξ ^ 2 ≤ (1 + ‖ξ‖ ^ 2) ^ 3 * ‖f ξ‖ ^ 2 := by
    dsimp [b]
    calc
      ((1 + ‖ξ‖ ^ 2) * ‖ξ‖ * ‖f ξ‖) ^ 2 =
          (1 + ‖ξ‖ ^ 2) ^ 2 * ‖ξ‖ ^ 2 * ‖f ξ‖ ^ 2 := by ring
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ 2 * (1 + ‖ξ‖ ^ 2) * ‖f ξ‖ ^ 2 := by
        gcongr
        linarith
      _ = (1 + ‖ξ‖ ^ 2) ^ 3 * ‖f ξ‖ ^ 2 := by ring
  have hb_int : Integrable (fun ξ => b ξ ^ 2) :=
    hw.mono' (hb.pow 2) (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hb_le ξ)
  have ha_lp : MemLp a 2 :=
    (memLp_two_iff_integrable_sq ha).mpr integrable_inverse_weight_sq
  have hb_lp : MemLp b 2 := (memLp_two_iff_integrable_sq hb).mpr hb_int
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (volume : Measure Space)) (f := a) (g := b) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun ξ => by dsimp [a]; positivity))
    (Filter.Eventually.of_forall (fun ξ => by dsimp [b]; positivity))
    (by simpa using ha_lp) (by simpa using hb_lp)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  have hprod : (fun ξ : Space => a ξ * b ξ) = fun ξ => ‖ξ‖ * ‖f ξ‖ := by
    funext ξ
    dsimp [a, b]
    have hq : (1 + ‖ξ‖ ^ 2 : ℝ) ≠ 0 := by positivity
    simp [← mul_assoc, hq]
  rw [hprod] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (integral_mono hb_int hw hb_le)) fourierMomentConstant_nonneg)

theorem fourierHNormSq_nonneg (s : ℕ) (ψ : ComplexTest) :
    0 ≤ fourierHNormSq s ψ :=
  integral_nonneg fun _ => by positivity

/-- A Fourier multiplier of order at most two has the required `H³` control. -/
theorem sqrt_l2Sq_le_of_fourier_bound (ψ φ : ComplexTest) {C : ℝ} (hC : 0 ≤ C)
    (hw : Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 3 *
      ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ ^ 2))
    (hφ : ∀ ξ : Space, ‖FourierTransform.fourierCLE ℂ ComplexTest φ ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) * ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖) :
    Real.sqrt (l2Sq (φ : Space → ℂ)) ≤ C * Real.sqrt (fourierHNormSq 3 ψ) := by
  have hsq : (∫ ξ : Space, ‖FourierTransform.fourierCLE ℂ ComplexTest φ ξ‖ ^ 2) ≤
      C ^ 2 * fourierHNormSq 3 ψ := by
    rw [fourierHNormSq, ← integral_const_mul]
    apply integral_mono (SchwartzParseval.integrable_norm_sq_fourier φ)
      (hw.const_mul (C ^ 2))
    intro ξ
    calc
      ‖FourierTransform.fourierCLE ℂ ComplexTest φ ξ‖ ^ 2 ≤
          (C * (1 + ‖ξ‖ ^ 2) * ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hφ ξ) 2
      _ = C ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ 2 *
          ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ ^ 2) := by ring
      _ ≤ C ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ 3 *
          ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg ‖ξ‖)) (by norm_num)
  simp only [FourierTransform.fourierCLE_apply] at hsq
  rw [SchwartzParseval.integral_norm_sq_fourier] at hsq
  calc
    Real.sqrt (l2Sq (φ : Space → ℂ)) ≤
        Real.sqrt (C ^ 2 * fourierHNormSq 3 ψ) := Real.sqrt_le_sqrt hsq
    _ = C * Real.sqrt (fourierHNormSq 3 ψ) := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]

/-- Exact magnitude of the coordinate-derivative Fourier multiplier. -/
theorem norm_fourier_partialCLM (i : Fin 3) (ψ : ComplexTest) (ξ : Space) :
    ‖FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i ψ) ξ‖ =
      (2 * Real.pi) * ‖ξ i‖ * ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ := by
  rw [fourier_partialCLM_apply]
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_of_nonneg Real.pi_pos.le]
  norm_num

theorem norm_fourier_partialCLM_le (i : Fin 3) (ψ : ComplexTest) (ξ : Space) :
    ‖FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i ψ) ξ‖ ≤
      (2 * Real.pi) * ‖ξ‖ * ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ := by
  rw [norm_fourier_partialCLM]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le ξ i) (by positivity)) (norm_nonneg _)

theorem norm_test_le_integral_fourier (ψ : ComplexTest) (x : Space) :
    ‖ψ x‖ ≤ ∫ ξ : Space, ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ := by
  calc
    ‖ψ x‖ = ‖(𝓕⁻ (𝓕 ψ)) x‖ := by
      rw [FourierTransform.fourierInv_fourier_eq]
    _ ≤ _ := VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem integral_norm_fourier_partialCLM_le_of_integrable (i : Fin 3) (ψ : ComplexTest)
    (hw : Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 3 *
      ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ ^ 2)) :
    (∫ ξ : Space, ‖FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i ψ) ξ‖) ≤
      (2 * Real.pi * fourierMomentConstant) * Real.sqrt (fourierHNormSq 3 ψ) := by
  have hm : Integrable (fun ξ : Space => ‖ξ‖ *
      ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖) := by
    simpa only [pow_one] using
      (FourierTransform.fourierCLE ℂ ComplexTest ψ).integrable_pow_mul volume 1
  calc
    (∫ ξ : Space, ‖FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i ψ) ξ‖) ≤
        ∫ ξ : Space, (2 * Real.pi) *
          (‖ξ‖ * ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖) := by
      apply integral_mono (FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i
          ψ)).integrable.norm
        (hm.const_mul (2 * Real.pi))
      intro ξ
      simpa only [mul_assoc] using norm_fourier_partialCLM_le i ψ ξ
    _ = (2 * Real.pi) * (∫ ξ : Space, ‖ξ‖ *
        ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖) := integral_const_mul _ _
    _ ≤ (2 * Real.pi) * (fourierMomentConstant * Real.sqrt (fourierHNormSq 3 ψ)) :=
      mul_le_mul_of_nonneg_left
        (integral_first_moment_le (FourierTransform.fourierCLE ℂ ComplexTest
            ψ).continuous.aestronglyMeasurable
          hw) (by positivity)
    _ = _ := by ring

theorem sqrt_l2Sq_test_le_of_integrable (ψ : ComplexTest)
    (hw : Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 3 *
      ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ ^ 2)) :
    Real.sqrt (l2Sq (ψ : Space → ℂ)) ≤ Real.sqrt (fourierHNormSq 3 ψ) := by
  simpa only [one_mul] using
    sqrt_l2Sq_le_of_fourier_bound ψ ψ (C := 1) (by positivity) hw (fun ξ => by
      rw [one_mul]
      exact le_mul_of_one_le_left (norm_nonneg _)
        (le_add_of_nonneg_right (sq_nonneg ‖ξ‖)))

theorem sqrt_l2Sq_partial_partial_le_of_integrable (i : Fin 3) (ψ : ComplexTest)
    (hw : Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 3 *
      ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ ^ 2)) :
    Real.sqrt (l2Sq (partialCLM i (partialCLM i ψ) : Space → ℂ)) ≤
      (2 * Real.pi) ^ 2 * Real.sqrt (fourierHNormSq 3 ψ) := by
  apply sqrt_l2Sq_le_of_fourier_bound ψ (partialCLM i (partialCLM i ψ))
    (sq_nonneg _) hw
  intro ξ
  calc
    ‖FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i (partialCLM i ψ)) ξ‖ ≤
        (2 * Real.pi) * ‖ξ‖ *
          ‖FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i ψ) ξ‖ :=
      norm_fourier_partialCLM_le i (partialCLM i ψ) ξ
    _ ≤ (2 * Real.pi) * ‖ξ‖ *
        ((2 * Real.pi) * ‖ξ‖ * ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖) :=
      mul_le_mul_of_nonneg_left (norm_fourier_partialCLM_le i ψ ξ) (by positivity)
    _ = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
        ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ := by ring
    _ ≤ (2 * Real.pi) ^ 2 * (1 + ‖ξ‖ ^ 2) *
        ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ := by gcongr; linarith

theorem norm_partialCLM_le_of_integrable (i : Fin 3) (ψ : ComplexTest)
    (hw : Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 3 *
      ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ ^ 2)) (x : Space) :
    ‖partialCLM i ψ x‖ ≤
      (2 * Real.pi * fourierMomentConstant) * Real.sqrt (fourierHNormSq 3 ψ) :=
  (norm_test_le_integral_fourier (partialCLM i ψ) x).trans
    (integral_norm_fourier_partialCLM_le_of_integrable i ψ hw)

theorem norm_rieszTest_partialCLM_le_of_integrable (i j k : Fin 3) (ψ : ComplexTest)
    (hw : Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ 3 *
      ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖ ^ 2)) (x : Space) :
    ‖rieszTest i j (partialCLM k ψ) x‖ ≤
      (2 * Real.pi * fourierMomentConstant) * Real.sqrt (fourierHNormSq 3 ψ) :=
  (RieszTestOperators.norm_rieszTest_le_integral i j (partialCLM k ψ) x).trans
    (integral_norm_fourier_partialCLM_le_of_integrable k ψ hw)

/-- The first moment of a Schwartz Fourier transform is controlled uniformly by `H³`. -/
theorem fourier_first_moment_le (ψ : ComplexTest) :
    (∫ ξ : Space, ‖ξ‖ * ‖FourierTransform.fourierCLE ℂ ComplexTest ψ ξ‖) ≤
      fourierMomentConstant * Real.sqrt (fourierHNormSq 3 ψ) :=
  integral_first_moment_le (FourierTransform.fourierCLE ℂ ComplexTest
      ψ).continuous.aestronglyMeasurable
    (FourierSobolevWeights.integrable_fourierHNormSq_three ψ)

theorem integral_norm_fourier_partialCLM_le (i : Fin 3) (ψ : ComplexTest) :
    (∫ ξ : Space, ‖FourierTransform.fourierCLE ℂ ComplexTest (partialCLM i ψ) ξ‖) ≤
      (2 * Real.pi * fourierMomentConstant) * Real.sqrt (fourierHNormSq 3 ψ) :=
  integral_norm_fourier_partialCLM_le_of_integrable i ψ
    (FourierSobolevWeights.integrable_fourierHNormSq_three ψ)

/-- The spatial `L²` norm of a test is at most its Fourier `H³` norm. -/
theorem sqrt_l2Sq_test_le (ψ : ComplexTest) :
    Real.sqrt (l2Sq (ψ : Space → ℂ)) ≤ Real.sqrt (fourierHNormSq 3 ψ) :=
  sqrt_l2Sq_test_le_of_integrable ψ
    (FourierSobolevWeights.integrable_fourierHNormSq_three ψ)

/-- Coordinate second derivatives have a common `H³` bound. -/
theorem sqrt_l2Sq_partial_partial_le (i : Fin 3) (ψ : ComplexTest) :
    Real.sqrt (l2Sq (partialCLM i (partialCLM i ψ) : Space → ℂ)) ≤
      (2 * Real.pi) ^ 2 * Real.sqrt (fourierHNormSq 3 ψ) :=
  sqrt_l2Sq_partial_partial_le_of_integrable i ψ
    (FourierSobolevWeights.integrable_fourierHNormSq_three ψ)

/-- The first derivative is bounded pointwise by one constant times the Fourier `H³` norm. -/
theorem norm_partialCLM_le (i : Fin 3) (ψ : ComplexTest) (x : Space) :
    ‖partialCLM i ψ x‖ ≤
      (2 * Real.pi * fourierMomentConstant) * Real.sqrt (fourierHNormSq 3 ψ) :=
  norm_partialCLM_le_of_integrable i ψ
    (FourierSobolevWeights.integrable_fourierHNormSq_three ψ) x

/-- Applying the bounded Riesz symbol preserves the same pointwise test bound. -/
theorem norm_rieszTest_partialCLM_le (i j k : Fin 3) (ψ : ComplexTest) (x : Space) :
    ‖rieszTest i j (partialCLM k ψ) x‖ ≤
      (2 * Real.pi * fourierMomentConstant) * Real.sqrt (fourierHNormSq 3 ψ) :=
  norm_rieszTest_partialCLM_le_of_integrable i j k ψ
    (FourierSobolevWeights.integrable_fourierHNormSq_three ψ) x

/-- One constant controls all test expressions appearing in pressure recovery. -/
theorem exists_uniform_test_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : ComplexTest,
      Real.sqrt (l2Sq (ψ : Space → ℂ)) ≤ C * Real.sqrt (fourierHNormSq 3 ψ) ∧
      (∀ i : Fin 3, Real.sqrt (l2Sq (partialCLM i (partialCLM i ψ) : Space → ℂ)) ≤
        C * Real.sqrt (fourierHNormSq 3 ψ)) ∧
      (∀ (i : Fin 3) (x : Space), ‖partialCLM i ψ x‖ ≤
        C * Real.sqrt (fourierHNormSq 3 ψ)) ∧
      (∀ (i j k : Fin 3) (x : Space), ‖rieszTest i j (partialCLM k ψ) x‖ ≤
        C * Real.sqrt (fourierHNormSq 3 ψ)) := by
  let C := max 1 (max ((2 * Real.pi) ^ 2) (2 * Real.pi * fourierMomentConstant))
  have h₁ : 1 ≤ C := le_max_left _ _
  have h₂ : (2 * Real.pi) ^ 2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : 2 * Real.pi * fourierMomentConstant ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, zero_le_one.trans h₁, fun ψ => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (sqrt_l2Sq_test_le ψ).trans
      ((one_mul (Real.sqrt (fourierHNormSq 3 ψ))).symm.trans_le
        (mul_le_mul_of_nonneg_right h₁ (Real.sqrt_nonneg _)))
  · intro i
    exact (sqrt_l2Sq_partial_partial_le i ψ).trans
      (mul_le_mul_of_nonneg_right h₂ (Real.sqrt_nonneg _))
  · intro i x
    exact (norm_partialCLM_le i ψ x).trans
      (mul_le_mul_of_nonneg_right h₃ (Real.sqrt_nonneg _))
  · intro i j k x
    exact (norm_rieszTest_partialCLM_le i j k ψ x).trans
      (mul_le_mul_of_nonneg_right h₃ (Real.sqrt_nonneg _))

end NavierStokesR3.PressureTestBounds

end
end

end

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NavierStokesR3.PressureFunctionals

open ProblemStatement Comparison HarmonicTestFunctionals PressureTestBounds

/-- Pairing an `L²` coefficient with a Schwartz test is integrable. -/
theorem integrable_l2_pair {W : Space → ℝ} (hW : MemLp W 2) (ψ : ComplexTest) :
    Integrable (fun x : Space => (W x : ℂ) * ψ x) := by
  have hprod : Integrable (fun x : Space => ‖W x‖ * ‖ψ x‖) :=
    hW.norm.integrable_mul (ψ.memLp 2).norm
  apply hprod.mono'
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hW.1).mul
      ψ.continuous.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by simp [Complex.norm_real]

/-- Cauchy--Schwarz for the actual coefficient/test pairing. -/
theorem norm_l2_pair_le {W : Space → ℝ} (hW : MemLp W 2) (ψ : ComplexTest) :
    ‖∫ x : Space, (W x : ℂ) * ψ x‖ ≤
      Real.sqrt (l2Sq W) * Real.sqrt (l2Sq (ψ : Space → ℂ)) := by
  calc
    ‖∫ x : Space, (W x : ℂ) * ψ x‖ ≤ ∫ x : Space, ‖(W x : ℂ) * ψ x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : Space, ‖W x‖ * ‖ψ x‖ := by simp only [norm_mul, Complex.norm_real]
    _ ≤ _ := by
      have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure Space))
        (f := fun x => ‖W x‖) (g := fun x => ‖ψ x‖) Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (by simpa using hW.norm) (by simpa using (ψ.memLp 2).norm)
      simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, l2Sq] using h

/-- An `L¹` coefficient may be paired with any Schwartz test. -/
theorem integrable_l1_pair {g : Space → ℝ} (hg : Integrable g) (ψ : ComplexTest) :
    Integrable (fun x : Space => (g x : ℂ) * ψ x) := by
  have hgc : Integrable (fun x : Space => (g x : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hg
  have h := hgc.bdd_mul ψ.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_test_le_integral_fourier ψ))
  simpa only [mul_comm] using h

/-- The canonical pressure pairing is finite for an `L¹` coefficient. -/
theorem integrable_l1_riesz_pair {g : Space → ℝ} (hg : Integrable g)
    (i j : Fin 3) (ψ : ComplexTest) :
    Integrable (fun x : Space => (g x : ℂ) * rieszTest i j ψ x) :=
  RieszTestOperators.integrable_mul_rieszTest i j ψ
    (Complex.ofRealCLM.integrable_comp hg)

/-- A pointwise test bound gives the usual `L¹` pairing estimate. -/
theorem norm_l1_pair_le_of_bound {g : Space → ℝ} (hg : Integrable g)
    {f : Space → ℂ} (hf : Integrable (fun x : Space => (g x : ℂ) * f x))
    {B : ℝ} (hB : ∀ x : Space, ‖f x‖ ≤ B) :
    ‖∫ x : Space, (g x : ℂ) * f x‖ ≤ (∫ x : Space, ‖g x‖) * B := by
  calc
    ‖∫ x : Space, (g x : ℂ) * f x‖ ≤ ∫ x : Space, ‖(g x : ℂ) * f x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : Space, ‖g x‖ * B := by
      apply integral_mono hf.norm (hg.norm.mul_const B)
      intro x
      change ‖(g x : ℂ) * f x‖ ≤ ‖g x‖ * B
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
    _ = (∫ x : Space, ‖g x‖) * B := integral_mul_const _ _

/-- The ordinary inclusion of Schwartz tests into complex-valued functions. -/
noncomputable def testValueLinear : ComplexTest →ₗ[ℂ] (Space → ℂ) where
  toFun ψ := ψ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Integrating a linear family of tests against a fixed coefficient is linear
when every displayed integrand is integrable. -/
def integralPairLinear (g : Space → ℝ) (T : ComplexTest →ₗ[ℂ] (Space → ℂ))
    (hint : ∀ ψ : ComplexTest, Integrable (fun x : Space => (g x : ℂ) * T ψ x)) :
    ComplexTest →ₗ[ℂ] ℂ where
  toFun ψ := ∫ x : Space, (g x : ℂ) * T ψ x
  map_add' ψ φ := by
    simp only [map_add, Pi.add_apply, mul_add]
    exact integral_add (hint ψ) (hint φ)
  map_smul' c ψ := by
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    calc
      (∫ x : Space, (g x : ℂ) * (c * T ψ x)) =
          ∫ x : Space, c * ((g x : ℂ) * T ψ x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = c * ∫ x : Space, (g x : ℂ) * T ψ x := integral_const_mul _ _

/-- The linear `L²` coefficient pairing. -/
def l2PairLinear (W : Space → ℝ) (hW : MemLp W 2) : ComplexTest →ₗ[ℂ] ℂ :=
  integralPairLinear W testValueLinear (integrable_l2_pair hW)

/-- The linear `L¹` coefficient pairing. -/
def l1PairLinear (g : Space → ℝ) (hg : Integrable g) : ComplexTest →ₗ[ℂ] ℂ :=
  integralPairLinear g testValueLinear (integrable_l1_pair hg)

@[simp] theorem l2PairLinear_apply (W : Space → ℝ) (hW : MemLp W 2) (ψ : ComplexTest) :
    l2PairLinear W hW ψ = ∫ x : Space, (W x : ℂ) * ψ x := rfl

@[simp] theorem l1PairLinear_apply (g : Space → ℝ) (hg : Integrable g) (ψ : ComplexTest) :
    l1PairLinear g hg ψ = ∫ x : Space, (g x : ℂ) * ψ x := rfl

/-- The coefficients are the two time averages of velocity and the time average
of the quadratic tensor in the conservative pressure equation. -/
def averagedPressureDifferenceValue (W0 W1 : Space → ℝ)
    (G : Fin 3 → Fin 3 → Space → ℝ) (k : Fin 3) (ψ : ComplexTest) : ℂ :=
  (∫ x : Space, (W0 x : ℂ) * laplacianCLM ψ x) +
    (∫ x : Space, (W1 x : ℂ) * ψ x) +
    (∑ i : Fin 3, ∫ x : Space, (G k i x : ℂ) * partialCLM i ψ x) +
    ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (G i j) (partialCLM k ψ)

/-- Every term of the pressure-difference functional is an integrable pairing. -/
theorem integrable_terms {W0 W1 : Space → ℝ} {G : Fin 3 → Fin 3 → Space → ℝ}
    (hW0 : MemLp W0 2) (hW1 : MemLp W1 2)
    (hG : ∀ i j : Fin 3, Integrable (G i j)) (k : Fin 3) (ψ : ComplexTest) :
    Integrable (fun x : Space => (W0 x : ℂ) * laplacianCLM ψ x) ∧
      Integrable (fun x : Space => (W1 x : ℂ) * ψ x) ∧
      (∀ i : Fin 3, Integrable (fun x : Space => (G k i x : ℂ) * partialCLM i ψ x)) ∧
      (∀ i j : Fin 3, Integrable (fun x : Space =>
        (G i j x : ℂ) * rieszTest i j (partialCLM k ψ) x)) := by
  exact ⟨integrable_l2_pair hW0 (laplacianCLM ψ), integrable_l2_pair hW1 ψ,
    fun i => integrable_l1_pair (hG k i) (partialCLM i ψ),
    fun i j => integrable_l1_riesz_pair (hG i j) i j (partialCLM k ψ)⟩

theorem l2_pair_laplacian_eq_sum {W : Space → ℝ} (hW : MemLp W 2)
    (ψ : ComplexTest) :
    (∫ x : Space, (W x : ℂ) * laplacianCLM ψ x) =
      ∑ i : Fin 3, ∫ x : Space, (W x : ℂ) * partialCLM i (partialCLM i ψ) x := by
  change l2PairLinear W hW (laplacianCLM ψ) = _
  simp only [laplacianCLM, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    map_sum, l2PairLinear_apply]

theorem norm_l2_laplacian_pair_le {W : Space → ℝ} (hW : MemLp W 2)
    (ψ : ComplexTest) {B : ℝ}
    (hB : ∀ i : Fin 3,
      Real.sqrt (l2Sq (partialCLM i (partialCLM i ψ) : Space → ℂ)) ≤ B) :
    ‖∫ x : Space, (W x : ℂ) * laplacianCLM ψ x‖ ≤ 3 * Real.sqrt (l2Sq W) * B := by
  rw [l2_pair_laplacian_eq_sum hW ψ]
  calc
    ‖∑ i : Fin 3, ∫ x : Space, (W x : ℂ) * partialCLM i (partialCLM i ψ) x‖ ≤
        ∑ i : Fin 3, ‖∫ x : Space, (W x : ℂ) * partialCLM i (partialCLM i ψ) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, Real.sqrt (l2Sq W) * B := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_l2_pair_le hW (partialCLM i (partialCLM i ψ))).trans
        (mul_le_mul_of_nonneg_left (hB i) (Real.sqrt_nonneg _))
    _ = 3 * Real.sqrt (l2Sq W) * B := by simp [mul_assoc]

/-- The actual pressure-difference expression is bounded by the Fourier `H³`
norm, with a constant depending only on the given coefficients. -/
theorem averagedPressureDifferenceValue_bound {W0 W1 : Space → ℝ}
    {G : Fin 3 → Fin 3 → Space → ℝ}
    (hW0 : MemLp W0 2) (hW1 : MemLp W1 2)
    (hG : ∀ i j : Fin 3, Integrable (G i j)) (k : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : ComplexTest,
      ‖averagedPressureDifferenceValue W0 W1 G k ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ) := by
  obtain ⟨B, hB, htest⟩ := exists_uniform_test_bound
  let M := 3 * Real.sqrt (l2Sq W0) + Real.sqrt (l2Sq W1) +
    (∑ i : Fin 3, ∫ x : Space, ‖G k i x‖) +
    ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Space, ‖G i j x‖
  have hmass (i j : Fin 3) : 0 ≤ ∫ x : Space, ‖G i j x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hrow : 0 ≤ ∑ i : Fin 3, ∫ x : Space, ‖G k i x‖ :=
    Finset.sum_nonneg fun i _ => hmass k i
  have hall : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Space, ‖G i j x‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hmass i j
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M * B, mul_nonneg hM hB, ?_⟩
  intro ψ
  obtain ⟨hbase, hsecond, hfirst, hriesz⟩ := htest ψ
  have h0 := norm_l2_laplacian_pair_le hW0 ψ hsecond
  have h1 : ‖∫ x : Space, (W1 x : ℂ) * ψ x‖ ≤
      Real.sqrt (l2Sq W1) * (B * Real.sqrt (fourierHNormSq 3 ψ)) :=
    (norm_l2_pair_le hW1 ψ).trans
      (mul_le_mul_of_nonneg_left hbase (Real.sqrt_nonneg _))
  have hrow_bound :
      ‖∑ i : Fin 3, ∫ x : Space, (G k i x : ℂ) * partialCLM i ψ x‖ ≤
        (∑ i : Fin 3, ∫ x : Space, ‖G k i x‖) * (B * Real.sqrt (fourierHNormSq 3 ψ)) := by
    calc
      ‖∑ i : Fin 3, ∫ x : Space, (G k i x : ℂ) * partialCLM i ψ x‖ ≤
          ∑ i : Fin 3, ‖∫ x : Space, (G k i x : ℂ) * partialCLM i ψ x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, (∫ x : Space, ‖G k i x‖) *
          (B * Real.sqrt (fourierHNormSq 3 ψ)) := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_l1_pair_le_of_bound (hG k i)
          (integrable_l1_pair (hG k i) (partialCLM i ψ)) (hfirst i)
      _ = _ := by rw [Finset.sum_mul]
  have hpressure_bound :
      ‖∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (G i j) (partialCLM k ψ)‖ ≤
        (∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Space, ‖G i j x‖) *
          (B * Real.sqrt (fourierHNormSq 3 ψ)) := by
    calc
      ‖∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (G i j) (partialCLM k ψ)‖ ≤
          ∑ i : Fin 3, ‖∑ j : Fin 3, pressurePair i j (G i j) (partialCLM k ψ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖pressurePair i j (G i j) (partialCLM k ψ)‖ :=
        Finset.sum_le_sum fun _ _ => norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, (∫ x : Space, ‖G i j x‖) *
          (B * Real.sqrt (fourierHNormSq 3 ψ)) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact norm_l1_pair_le_of_bound (hG i j)
          (integrable_l1_riesz_pair (hG i j) i j (partialCLM k ψ)) (hriesz i j k)
      _ = _ := by simp only [Finset.sum_mul]
  have htriangle : ‖averagedPressureDifferenceValue W0 W1 G k ψ‖ ≤
      ‖∫ x : Space, (W0 x : ℂ) * laplacianCLM ψ x‖ +
      ‖∫ x : Space, (W1 x : ℂ) * ψ x‖ +
      ‖∑ i : Fin 3, ∫ x : Space, (G k i x : ℂ) * partialCLM i ψ x‖ +
      ‖∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (G i j) (partialCLM k ψ)‖ := by
    exact (norm_add_le _ _).trans (add_le_add_left
      ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)) _)
  calc
    ‖averagedPressureDifferenceValue W0 W1 G k ψ‖ ≤ _ := htriangle
    _ ≤ 3 * Real.sqrt (l2Sq W0) * (B * Real.sqrt (fourierHNormSq 3 ψ)) +
        Real.sqrt (l2Sq W1) * (B * Real.sqrt (fourierHNormSq 3 ψ)) +
        (∑ i : Fin 3, ∫ x : Space, ‖G k i x‖) * (B * Real.sqrt (fourierHNormSq 3 ψ)) +
        (∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Space, ‖G i j x‖) *
          (B * Real.sqrt (fourierHNormSq 3 ψ)) :=
      add_le_add (add_le_add (add_le_add h0 h1) hrow_bound) hpressure_bound
    _ = (M * B) * Real.sqrt (fourierHNormSq 3 ψ) := by dsimp [M]; ring

/-- The canonical pressure pairing, as an actual complex-linear map on tests. -/
def pressurePairLinear (i j : Fin 3) (g : Space → ℝ) (hg : Integrable g) :
    ComplexTest →ₗ[ℂ] ℂ :=
  integralPairLinear g (RieszTestOperators.rieszTestLinear i j)
    (integrable_l1_riesz_pair hg i j)

@[simp] theorem pressurePairLinear_apply (i j : Fin 3) (g : Space → ℝ)
    (hg : Integrable g) (ψ : ComplexTest) :
    pressurePairLinear i j g hg ψ = pressurePair i j g ψ := rfl

/-- The averaged pressure-gradient difference determined by the stated
velocity and quadratic-tensor coefficients. -/
def averagedPressureDifference (W0 W1 : Space → ℝ)
    (G : Fin 3 → Fin 3 → Space → ℝ)
    (hW0 : MemLp W0 2) (hW1 : MemLp W1 2)
    (hG : ∀ i j : Fin 3, Integrable (G i j)) (k : Fin 3) :
    ComplexTest →ₗ[ℂ] ℂ :=
  (l2PairLinear W0 hW0).comp laplacianCLM.toLinearMap +
    l2PairLinear W1 hW1 +
    (∑ i : Fin 3, (l1PairLinear (G k i) (hG k i)).comp (partialCLM i).toLinearMap) +
    ∑ i : Fin 3, ∑ j : Fin 3,
      (pressurePairLinear i j (G i j) (hG i j)).comp (partialCLM k).toLinearMap

@[simp] theorem averagedPressureDifference_apply (W0 W1 : Space → ℝ)
    (G : Fin 3 → Fin 3 → Space → ℝ)
    (hW0 : MemLp W0 2) (hW1 : MemLp W1 2)
    (hG : ∀ i j : Fin 3, Integrable (G i j)) (k : Fin 3) (ψ : ComplexTest) :
    averagedPressureDifference W0 W1 G hW0 hW1 hG k ψ =
      averagedPressureDifferenceValue W0 W1 G k ψ := by
  simp only [averagedPressureDifference, averagedPressureDifferenceValue,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    l2PairLinear_apply, l1PairLinear_apply, pressurePairLinear_apply]
  rfl

/-- The actual complex-linear functional satisfies a uniform `H³` estimate. -/
theorem averagedPressureDifference_bound {W0 W1 : Space → ℝ}
    {G : Fin 3 → Fin 3 → Space → ℝ}
    (hW0 : MemLp W0 2) (hW1 : MemLp W1 2)
    (hG : ∀ i j : Fin 3, Integrable (G i j)) (k : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : ComplexTest,
      ‖averagedPressureDifference W0 W1 G hW0 hW1 hG k ψ‖ ≤
        C * Real.sqrt (fourierHNormSq 3 ψ) := by
  simpa only [averagedPressureDifference_apply] using
    averagedPressureDifferenceValue_bound hW0 hW1 hG k

end NavierStokesR3.PressureFunctionals
