/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernel
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszHeatRepresentation
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.GaussianMoments
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszTestOperators

/-!
# Fourier representation of the heat kernel

The ordinary Gaussian Fourier formula is normalized to the three dimensional
heat kernel used in the comparison proof. Two justified differentiations of
the inverse Fourier integral identify the Hessian multiplier with its kernel.
-/

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
