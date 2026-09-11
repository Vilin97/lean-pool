/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelPairedBound
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ProblemStatement
public import Mathlib.Analysis.Fourier.FourierTransform
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelCancellation
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PairedKernelBound
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RadialKernelBounds
import Mathlib.MeasureTheory.Integral.Prod
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszTestOperators
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonFourierSetup
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszSymbolRegularity

/-!
# The pressure commutator

The Fourier-defined double Riesz operator has the actual heat representation.
We first subtract the two time-integrable heat evolutions, insert the cutoff
difference, and only then use the absolute-integrability theorem to interchange
time and space. The resulting kernel has the proved radial `L^(4/3)` majorant.
-/

section

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

end
end

end

section

/-!
# Fourier representation of the heat kernel

The ordinary Gaussian Fourier formula is normalized to the three dimensional
heat kernel used in the comparison proof. Two justified differentiations of
the inverse Fourier integral identify the Hessian multiplier with its kernel.
-/

section

/-!
# Gaussian moments for Fourier differentiation

The zeroth, first and second norm moments of a Gaussian are integrable.
The only polynomial estimate used here absorbs the square of the norm into
a Gaussian with half the decay rate.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- A real Gaussian, regarded as a complex-valued function, is integrable. -/
theorem integrable_complex_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => (Real.exp (-a * ‖x‖ ^ 2) : ℂ)) := by
  simpa only [zero_mul, add_zero, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow] using
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (a : ℂ)) (by simpa only [Complex.ofReal_re] using ha) 0 (0 : Space)

/-- The ordinary real Gaussian is integrable on three-dimensional space. -/
theorem integrable_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => Real.exp (-a * ‖x‖ ^ 2)) := by
  refine (integrable_complex_gaussian ha).norm.congr ?_
  filter_upwards with x
  exact Complex.norm_of_nonneg (Real.exp_nonneg _)

private theorem sq_mul_gaussian_le (a r : ℝ) (ha : 0 < a) :
    r ^ 2 * Real.exp (-a * r ^ 2) ≤
      (2 / a) * Real.exp (-(a / 2) * r ^ 2) := by
  have hlinear : (a / 2) * r ^ 2 ≤ Real.exp ((a / 2) * r ^ 2) := by
    linarith [Real.add_one_le_exp ((a / 2) * r ^ 2)]
  have hmul := mul_le_mul_of_nonneg_right hlinear (Real.exp_nonneg (-a * r ^ 2))
  have he : Real.exp ((a / 2) * r ^ 2) * Real.exp (-a * r ^ 2) =
      Real.exp (-(a / 2) * r ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hmul
  calc
    r ^ 2 * Real.exp (-a * r ^ 2) =
        (2 / a) * (((a / 2) * r ^ 2) * Real.exp (-a * r ^ 2)) := by
      field_simp [ha.ne']
    _ ≤ (2 / a) * Real.exp (-(a / 2) * r ^ 2) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)

/-- The second norm moment of a Gaussian is integrable. -/
theorem integrable_norm_sq_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)) := by
  have hc : Continuous (fun x : Space => ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)) := by
    fun_prop
  refine ((integrable_gaussian (a := a / 2) (by positivity)).const_mul (2 / a)).mono'
    hc.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact sq_mul_gaussian_le a ‖x‖ ha

/-- The first norm moment follows from the zeroth and second moments. -/
theorem integrable_norm_gaussian {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space => ‖x‖ * Real.exp (-a * ‖x‖ ^ 2)) := by
  have hc : Continuous (fun x : Space => ‖x‖ * Real.exp (-a * ‖x‖ ^ 2)) := by
    fun_prop
  refine ((integrable_gaussian ha).add (integrable_norm_sq_gaussian ha)).mono'
    hc.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ‖x‖ * Real.exp (-a * ‖x‖ ^ 2) ≤
        (1 + ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      nlinarith [sq_nonneg (‖x‖ - 1 / 2)]
    _ = Real.exp (-a * ‖x‖ ^ 2) + ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2) := by ring

end NavierStokesR3.Comparison

end
end

end

@[expose] public section

noncomputable section

open MeasureTheory

namespace NavierStokesR3.Comparison

open ProblemStatement

theorem fourierIntegral_gaussian_real {a : ℝ} (ha : 0 < a) (z : Space) :
    FourierTransform.fourier (fun ξ : Space => (Real.exp (-a * ‖ξ‖ ^ 2) : ℂ)) z =
      (((Real.pi / a) ^ (3 / 2 : ℝ) *
        Real.exp (-Real.pi ^ 2 * ‖z‖ ^ 2 / a) : ℝ) : ℂ) := by
  have hdim : Module.finrank ℝ Space = 3 := by
    simp [Space, NavierStokes.ProblemStatement.Space]
  have hpow : ((Real.pi : ℂ) / (a : ℂ)) ^ ((3 : ℂ) / 2) =
      (((Real.pi / a) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_div, Complex.ofReal_cpow (by positivity)]
    simp
  have h := fourier_gaussian_innerProductSpace
    (V := Space) (b := (a : ℂ)) (by simpa using ha) z
  rw [hdim] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [hpow] at h
  simpa only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_pow] using h

/-- Inverse Fourier transform of the heat semigroup's Gaussian multiplier. -/
theorem fourierIntegralInv_heatGaussian {s : ℝ} (hs : 0 < s) (z : Space) :
    FourierTransform.fourierInv
        (fun ξ : Space => (Real.exp (-(4 * Real.pi ^ 2 * s) * ‖ξ‖ ^ 2) : ℂ)) z =
      (heatKernel s z : ℂ) := by
  have ha : 0 < 4 * Real.pi ^ 2 * s := by positivity
  have hb : 0 < 4 * Real.pi * s := by positivity
  rw [Real.fourierInv_eq_fourier_neg, fourierIntegral_gaussian_real ha]
  simp only [norm_neg]
  have hratio : Real.pi / (4 * Real.pi ^ 2 * s) = (4 * Real.pi * s)⁻¹ := by
    field_simp [Real.pi_ne_zero, hs.ne']
  have hpower : (Real.pi / (4 * Real.pi ^ 2 * s)) ^ (3 / 2 : ℝ) =
      (4 * Real.pi * s) ^ (-(3 / 2 : ℝ)) := by
    rw [hratio, Real.rpow_def_of_pos (inv_pos.mpr hb), Real.rpow_def_of_pos hb,
      Real.log_inv]
    congr 1
    ring
  have hexponent : -Real.pi ^ 2 * ‖z‖ ^ 2 / (4 * Real.pi ^ 2 * s) =
      -(‖z‖ ^ 2) / (4 * s) := by
    field_simp [Real.pi_ne_zero, hs.ne']
  rw [hpower, hexponent]
  rfl

private theorem continuous_complex_coordinate (i : Fin 3) :
    Continuous (fun x : Space => (x i : ℂ)) := by
  exact Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (EuclideanSpace.equiv (Fin 3) ℝ).continuous)

private theorem norm_coordinate_multiplier_le (c : ℂ) (i : Fin 3)
    (f : Space → ℂ) (ξ : Space) :
    ‖c * (ξ i : ℂ) * f ξ‖ ≤ ‖c‖ * (‖ξ‖ * ‖f ξ‖) := by
  have hcoord : ‖(ξ i : ℂ)‖ ≤ ‖ξ‖ := by
    simpa only [Complex.norm_real] using PiLp.norm_apply_le ξ i
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖c‖ * ‖ξ‖ * ‖f ξ‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoord (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

private theorem integrable_coordinate_multiplier {f : Space → ℂ}
    (c : ℂ) (i : Fin 3) (hf : AEStronglyMeasurable f)
    (h1 : Integrable (fun ξ : Space => ‖ξ‖ * ‖f ξ‖)) :
    Integrable (fun ξ : Space => c * (ξ i : ℂ) * f ξ) := by
  apply (h1.const_mul ‖c‖).mono'
  · exact (continuous_const.mul (continuous_complex_coordinate i)).aestronglyMeasurable.mul hf
  · filter_upwards with ξ
    exact norm_coordinate_multiplier_le c i f ξ

private theorem integrable_coordinate_multiplier_moment {f : Space → ℂ}
    (c : ℂ) (i : Fin 3) (hf : AEStronglyMeasurable f)
    (h2 : Integrable (fun ξ : Space => ‖ξ‖ ^ 2 * ‖f ξ‖)) :
    Integrable (fun ξ : Space => ‖ξ‖ * ‖c * (ξ i : ℂ) * f ξ‖) := by
  have hF : AEStronglyMeasurable (fun ξ : Space => c * (ξ i : ℂ) * f ξ) :=
    (continuous_const.mul (continuous_complex_coordinate i)).aestronglyMeasurable.mul hf
  apply (h2.const_mul ‖c‖).mono'
  · exact continuous_norm.aestronglyMeasurable.mul hF.norm
  · filter_upwards with ξ
    rw [norm_mul, norm_norm, norm_norm]
    calc
      _ ≤ ‖ξ‖ * (‖c‖ * (‖ξ‖ * ‖f ξ‖)) :=
        mul_le_mul_of_nonneg_left (norm_coordinate_multiplier_le c i f ξ) (norm_nonneg _)
      _ = _ := by ring

private theorem partialD_ofReal {f : Space → ℝ} (hf : Differentiable ℝ f)
    (i : Fin 3) (z : Space) :
    partialD i (fun x : Space => (f x : ℂ)) z = (partialD (E := ℝ) i f z : ℂ) := by
  unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
  change fderiv ℝ (Complex.ofRealCLM ∘ f) z
    (NavierStokes.ProblemStatement.coordinateVector i) = _
  rw [((Complex.ofRealCLM.hasFDerivAt).comp z (hf z).hasFDerivAt).fderiv]
  rfl

private theorem differentiable_partial_heatKernel {s : ℝ} (hs : 0 < s) (j : Fin 3) :
    Differentiable ℝ (partialD j (heatKernel s)) := by
  have hc : Differentiable ℝ (fun x : Space => x j) := by
    convert! (innerSL ℝ (NavierStokes.ProblemStatement.coordinateVector j)).differentiable
      using 1
    ext x
    simp [NavierStokes.ProblemStatement.coordinateVector, EuclideanSpace.inner_single_left]
  rw [show partialD j (heatKernel s) =
    (fun x : Space => -(x j / (2 * s)) * heatKernel s x) from
    funext (partial_heatKernel hs j)]
  simpa only [div_eq_mul_inv] using!
    ((hc.mul_const ((2 * s)⁻¹)).neg.mul (differentiable_heatKernel hs))

private theorem secondPartial_ofReal_heatKernel {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    partialD i (partialD j (fun x : Space => (heatKernel s x : ℂ))) z =
      (heatKernelSecond s i j z : ℂ) := by
  have hfirst : partialD j (fun x : Space => (heatKernel s x : ℂ)) =
      (fun x : Space => (partialD (E := ℝ) j (heatKernel s) x : ℂ)) :=
    funext (partialD_ofReal (differentiable_heatKernel hs) j)
  rw [hfirst, partialD_ofReal (differentiable_partial_heatKernel hs j) i z,
    ← heatKernelSecond_eq_partial hs i j z]

private theorem heatKernelFourierData {s : ℝ} (hs : 0 < s) (i j : Fin 3) :
    Integrable (fun ξ : Space => (heatSecondSymbol s i j ξ : ℂ)) ∧
      ∀ z : Space, FourierTransform.fourierInv
        (fun ξ : Space => (heatSecondSymbol s i j ξ : ℂ)) z =
          (heatKernelSecond s i j z : ℂ) := by
  let a : ℝ := 4 * Real.pi ^ 2 * s
  let g : Space → ℂ := fun ξ => (Real.exp (-a * ‖ξ‖ ^ 2) : ℂ)
  let c : ℂ := 2 * Real.pi * Complex.I
  let f1 : Space → ℂ := fun ξ => c * (ξ j : ℂ) * g ξ
  let f2 : Space → ℂ := fun ξ => c * (ξ i : ℂ) * f1 ξ
  have ha : 0 < a := by dsimp [a]; positivity
  have hg : Integrable g := integrable_complex_gaussian ha
  have hg1 : Integrable (fun ξ : Space => ‖ξ‖ * ‖g ξ‖) := by
    simpa only [g, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      integrable_norm_gaussian ha
  have hg2 : Integrable (fun ξ : Space => ‖ξ‖ ^ 2 * ‖g ξ‖) := by
    simpa only [g, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      integrable_norm_sq_gaussian ha
  have hf1 : Integrable f1 :=
    integrable_coordinate_multiplier c j hg.aestronglyMeasurable hg1
  have hf1moment : Integrable (fun ξ : Space => ‖ξ‖ * ‖f1 ξ‖) :=
    integrable_coordinate_multiplier_moment c j hg.aestronglyMeasurable hg2
  have hf2 : Integrable f2 :=
    integrable_coordinate_multiplier c i hf1.aestronglyMeasurable hf1moment
  have hf2eq : f2 = (fun ξ : Space => (heatSecondSymbol s i j ξ : ℂ)) := by
    funext ξ
    dsimp [f2, f1, g, c, a]
    unfold heatSecondSymbol
    have he : -(4 * Real.pi ^ 2 * s) * ‖ξ‖ ^ 2 =
        -(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * s := by ring
    rw [he]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have h0 : FourierTransform.fourierInv g = (fun x : Space => (heatKernel s x : ℂ)) := by
    funext x
    exact fourierIntegralInv_heatGaussian hs x
  have hd1 : partialD j (FourierTransform.fourierInv g) = FourierTransform.fourierInv f1 := by
    funext x
    unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
    simpa [f1, c, NavierStokes.ProblemStatement.coordinateVector,
      EuclideanSpace.inner_single_right] using
      RieszTestOperators.fderiv_fourierInv_apply hg hg1 x
        (NavierStokes.ProblemStatement.coordinateVector j)
  have hd2 : partialD i (FourierTransform.fourierInv f1) = FourierTransform.fourierInv f2 := by
    funext x
    unfold partialD NavierStokes.PeriodicIntegration.spatialPartial
    simpa [f2, c, NavierStokes.ProblemStatement.coordinateVector,
      EuclideanSpace.inner_single_right] using
      RieszTestOperators.fderiv_fourierInv_apply hf1 hf1moment x
        (NavierStokes.ProblemStatement.coordinateVector i)
  constructor
  · rw [← hf2eq]
    exact hf2
  · intro z
    rw [← hf2eq, ← hd2, ← hd1, h0]
    exact secondPartial_ofReal_heatKernel hs i j z

/-- The positive-time heat Hessian multiplier is integrable in frequency. -/
theorem integrable_heatSecondSymbol_space {s : ℝ} (hs : 0 < s) (i j : Fin 3) :
    Integrable (fun ξ : Space => (heatSecondSymbol s i j ξ : ℂ)) :=
  (heatKernelFourierData hs i j).1

/-- The inverse Fourier transform of the heat Hessian multiplier is its actual kernel. -/
theorem fourierIntegralInv_heatSecondSymbol {s : ℝ} (hs : 0 < s)
    (i j : Fin 3) (z : Space) :
    FourierTransform.fourierInv (fun ξ : Space => (heatSecondSymbol s i j ξ : ℂ)) z =
      (heatKernelSecond s i j z : ℂ) :=
  (heatKernelFourierData hs i j).2 z

end NavierStokesR3.Comparison

end
end

end

section

/-!
# Fubini after insertion of the cutoff difference

The time kernel is multiplied by the cutoff difference before estimating its
absolute integral. The resulting radial majorant belongs to `L^(4/3)`, so
Hölder with the `L^4` test function proves integrability on space times time.
-/

@[expose] public section

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

end
end

end

section

/-!
# An inverse Fourier multiplier as a convolution

For integrable `A` and `ψ`, the inverse Fourier transform of `A * Fourier ψ`
is the convolution of `inverseFourier A` with `ψ`.  Absolute product
integrability also proves that the spatial convolution exists at every point;
no global integrability of `inverseFourier A` is required.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace NavierStokesR3.Comparison

open ProblemStatement

private theorem integrable_inverseFourierProduct {A ψ : Space → ℂ}
    (hA : Integrable A) (hψ : Integrable ψ) (x : Space) :
    Integrable (fun p : Space × Space =>
      Real.fourierChar ⟪p.1, x - p.2⟫ • (A p.1 * ψ p.2))
      ((volume : Measure Space).prod (volume : Measure Space)) := by
  have hp : Continuous (fun p : Space × Space => Real.fourierChar ⟪p.1, x - p.2⟫) :=
    Real.continuous_fourierChar.comp
      (continuous_fst.inner (continuous_const.sub continuous_snd))
  refine (hA.norm.mul_prod hψ.norm).mono' ?_ ?_
  · exact hp.aestronglyMeasurable.smul
      (hA.aestronglyMeasurable.comp_fst.mul hψ.aestronglyMeasurable.comp_snd)
  · exact Filter.Eventually.of_forall fun p => by
      simp only [Circle.norm_smul, norm_mul, le_refl]

private theorem inverseFourierProduct_integral_frequency (A ψ : Space → ℂ)
    (x y : Space) :
    (∫ ξ : Space, Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y)) =
      FourierTransform.fourierInv A (x - y) * ψ y := by
  rw [Real.fourierInv_eq]
  simp only [Circle.smul_def, smul_eq_mul, ← mul_assoc, integral_mul_const]

private theorem inverseFourierProduct_integral_space (A ψ : Space → ℂ)
    (x ξ : Space) :
    (∫ y : Space, Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y)) =
      Real.fourierChar ⟪ξ, x⟫ • (A ξ * FourierTransform.fourier ψ ξ) := by
  rw [Real.fourier_eq]
  calc
    (∫ y : Space, Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y)) =
        ∫ y : Space, Real.fourierChar ⟪ξ, x⟫ •
          (A ξ * (Real.fourierChar (-⟪y, ξ⟫) • ψ y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hphase : Real.fourierChar ⟪ξ, x - y⟫ =
          Real.fourierChar ⟪ξ, x⟫ * Real.fourierChar (-⟪y, ξ⟫) := by
        rw [← Real.fourierChar.map_add_eq_mul]
        congr 1
        rw [inner_sub_right, real_inner_comm y ξ]
        ring
      rw [hphase, mul_smul]
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    _ = Real.fourierChar ⟪ξ, x⟫ •
        (A ξ * ∫ y : Space, Real.fourierChar (-⟪y, ξ⟫) • ψ y) := by
      simp only [Circle.smul_def, smul_eq_mul, integral_const_mul]

/-- Convolution with an inverse Fourier transform is integrable at every fixed point. -/
theorem integrable_fourierIntegralInv_convolution {A ψ : Space → ℂ}
    (hA : Integrable A) (hψ : Integrable ψ) (x : Space) :
    Integrable (fun y : Space => FourierTransform.fourierInv A (x - y) * ψ y) := by
  apply (integrable_inverseFourierProduct hA hψ x).integral_prod_right.congr
  exact Filter.Eventually.of_forall fun y =>
    inverseFourierProduct_integral_frequency A ψ x y

/-- Multiplication by an integrable Fourier multiplier becomes a spatial convolution. -/
theorem fourierIntegralInv_mul_fourier {A ψ : Space → ℂ}
    (hA : Integrable A) (hψ : Integrable ψ) (x : Space) :
    FourierTransform.fourierInv (fun ξ : Space => A ξ * FourierTransform.fourier ψ ξ) x =
      ∫ y : Space, FourierTransform.fourierInv A (x - y) * ψ y := by
  calc
    FourierTransform.fourierInv (fun ξ : Space => A ξ * FourierTransform.fourier ψ ξ) x =
        ∫ ξ : Space, ∫ y : Space,
          Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y) := by
      rw [Real.fourierInv_eq]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ =>
        (inverseFourierProduct_integral_space A ψ x ξ).symm
    _ = ∫ y : Space, ∫ ξ : Space,
        Real.fourierChar ⟪ξ, x - y⟫ • (A ξ * ψ y) :=
      integral_integral_swap (integrable_inverseFourierProduct hA hψ x)
    _ = ∫ y : Space, FourierTransform.fourierInv A (x - y) * ψ y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y =>
        inverseFourierProduct_integral_frequency A ψ x y

end NavierStokesR3.Comparison

end
end

end

@[expose] public section

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
