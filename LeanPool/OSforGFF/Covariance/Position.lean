/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

-- Import our basic definitions
import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Spacetime.Euclidean
import LeanPool.OSforGFF.Spacetime.DiscreteSymmetry
import LeanPool.OSforGFF.Schwinger.Defs
import LeanPool.OSforGFF.General.FunctionalAnalysis
import LeanPool.OSforGFF.Covariance.Momentum
import LeanPool.OSforGFF.Covariance.Parseval

/-!
# Position-Space Free Covariance

Position-space covariance C(x,y) = (m/4π²|x−y|) K₁(m|x−y|) and its properties:
Euclidean invariance, time reflection invariance, and Schwinger representation
C(x,y) = ∫₀^∞ e^{−sm²} H(s,|x−y|) ds via the heat kernel.

## Main definitions

- `freeCovarianceℂBilinear`: bilinear form ⟨f, Cg⟩ = ∫∫ f(x) C(x,y) g(y) dx dy

## Key Results

- `freeCovariance_euclidean_invariant`: Euclidean invariance of the covariance
- `covariance_timeReflection_invariant`: Time reflection invariance
-/

open MeasureTheory Complex Real Filter
open TopologicalSpace
open scoped Real InnerProductSpace BigOperators

/-! ## Dependencies

No axioms declared here. Uses `freeCovarianceℂ_bilinear_integrable` transitively
via `parseval_triple_integrand_integrable` in `Covariance.Parseval`.
-/

noncomputable section

/-- ** (Parseval for Covariance - Position Space formulation with regulator):**
    The fundamental Parseval identity relating the regulated covariance bilinear form to
    momentum-space propagator. The regulator exp(-α(2π)²‖k‖²) ensures absolute convergence.

    Uses `freePropagatorMomentumMathlib` which accounts for the 2π factor in Mathlib's Fourier
    convention.
    Defined in FourierTransforms.lean as `parseval_covariance_schwartz_regulated`.
-/
theorem parseval_covariance_schwartz_regulated' (α : ℝ) (hα : 0 < α) (m : ℝ) [Fact (0 < m)] (f :
  TestFunctionℂ) :
  (∫ x, ∫ y,
    f x * (freeCovarianceRegulated α m x y : ℂ) * (starRingEnd ℂ (f y)) ∂volume ∂volume).re
  = ∫ k, Real.exp (-α * (2 * Real.pi)^2 * ‖k‖^2) * ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 *
    freePropagatorMomentumMathlib m k ∂volume :=
  _root_.parseval_covariance_schwartz_regulated α hα m f

/-- **(Time Reflection Change of Variables):**
    Integrating a function over spacetime is unchanged when both variables are composed with
    geometric time reflection.  This packages the measure-preserving property of time reflection
    together with Fubini's theorem for later use in reflection-positivity arguments.
-/
lemma double_integral_timeReflection
  (G : SpaceTime → SpaceTime → ℂ)
  (_hG : Integrable (fun p : SpaceTime × SpaceTime => G p.1 p.2) (volume.prod volume)) :
  ∫ x, ∫ y, G (QFT.timeReflection x) (QFT.timeReflection y) ∂volume ∂volume
    = ∫ x, ∫ y, G x y ∂volume ∂volume := by
  have hmp := QFT.timeReflection_measurePreserving
  have hmeas := QFT.timeReflectionLE.toMeasurableEquiv.measurableEmbedding
  -- Apply change of variables for inner integral first
  have h_inner : ∀ x, ∫ y, G x (QFT.timeReflection y) = ∫ y, G x y :=
    fun x => hmp.integral_comp hmeas (fun y => G x y)
  simp_rw [h_inner]
  -- Then apply change of variables for outer integral
  exact hmp.integral_comp hmeas (fun x => ∫ y, G x y)

/-- Specialized time-reflection change of variables for covariance-type kernels.
    This packages the combination of `double_integral_timeReflection` and the
    observation that `compTimeReflection` is just composition with
    `timeReflection`, so we can reuse the general measure-preserving lemma
    without re-establishing integrability each time.
-/
lemma double_integral_timeReflection_covariance
  (m : ℝ) (f g : TestFunctionℂ)
  (hf : Integrable (fun p : SpaceTime × SpaceTime =>
      (QFT.compTimeReflection f) p.1 * (freeCovariance m p.1 p.2 : ℂ) * g p.2)
      (volume.prod volume)) :
  ∫ x, ∫ y,
      (QFT.compTimeReflection f) x * (freeCovariance m x y : ℂ) * g y ∂volume ∂volume
    = ∫ x, ∫ y,
        f x * (freeCovariance m (QFT.timeReflection x) (QFT.timeReflection y) : ℂ)
          * (QFT.compTimeReflection g) y ∂volume ∂volume := by
  -- compTimeReflection h x = h (timeReflectionCLM x) = h (timeReflection x)
  have h_comp : ∀ h : TestFunctionℂ, ∀ x, (QFT.compTimeReflection h) x = h (QFT.timeReflection x)
    := by
    intro h x
    simp only [QFT.compTimeReflection, SchwartzMap.compCLM_apply, Function.comp_apply]
    rfl  -- timeReflectionCLM x = timeReflection x by definition
  -- Rewrite both sides using the definition of compTimeReflection
  simp_rw [h_comp]
  -- Now goal is: ∫∫ f(Θx) * C(x,y) * g(y) = ∫∫ f(x) * C(Θx, Θy) * g(Θy)
  -- timeReflection is an involution: Θ ∘ Θ = id
  have hinv : ∀ z, QFT.timeReflection (QFT.timeReflection z) = z := by
    intro z
    exact QFT.timeReflectionLE.left_inv z
  -- Transform RHS using double_integral_timeReflection (in reverse direction)
  -- After substitution x' = Θx, y' = Θy: RHS = ∫∫ f(Θx') * C(x', y') * g(y')
  rw [← double_integral_timeReflection (fun x y => f (QFT.timeReflection x) * (freeCovariance m x y
    : ℂ) * g y) hf]
  -- Use Θ∘Θ = id to simplify f(Θ(Θx)) = f(x)
  simp only [hinv]

/-! ### Reflection Positivity for Free Covariance

For real test functions supported on positive time (t > 0), the cross-covariance
∫∫ (Θf)(x) C(x,y) f(y) dx dy ≥ 0 where Θ is time reflection.

Mathematical justification: In momentum space, the free covariance factorizes as
C(x,y) = ∫ e^{ik·(x-y)} / (k² + m²) dk. For functions with positive time support,
the time integral factorizes via contour integration, yielding an exponential
e^{-ω|t|} factor (where ω = √(|p|² + m²)) which ensures the cross-term is positive.

This is the key input for Osterwalder-Schrader reflection positivity (OS3).

**PROVEN:** See `QFT.freeCovariance_reflection_positive_bilinear` in CovarianceRP.lean,
which uses the direct momentum representation approach (RPProof namespace).
-/


/-! ### Complex Bilinear Form on Test Functions

The following section develops the bilinear structure of the covariance form.
All results assume m > 0 (positive mass) which is required for integrability.
-/

/-- The position-space integrand for the complex covariance bilinear form is integrable
    for Schwartz test functions, using translation-invariant L¹ kernel integrability.
-/
theorem freeCovarianceℂ_bilinear_integrable
    (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
    Integrable (fun p : SpaceTime × SpaceTime =>
      (f p.1) * (freeCovariance m p.1 p.2) * (g p.2)) volume := by
  exact freeCovarianceℂ_bilinear_integrable' m f g

/-- Integrability of the covariance kernel evaluated on a time-reflected test function.
    This follows directly from `freeCovarianceℂ_bilinear_integrable` since `compTimeReflection`
    maps test functions to test functions.
-/
lemma integrable_compTimeReflection_covariance
  (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
  Integrable (fun p : SpaceTime × SpaceTime =>
      (QFT.compTimeReflection f) p.1 * (freeCovariance m p.1 p.2 : ℂ) * f p.2)
    (volume.prod volume) := by
  rw [← Measure.volume_eq_prod]
  exact freeCovarianceℂ_bilinear_integrable m (QFT.compTimeReflection f) f


/-- Relationship between compTimeReflection of toComplex and compTimeReflectionReal:
    they agree pointwise as complex values.
-/
lemma compTimeReflection_toComplex_eq_ofReal
  (f : TestFunction) (x : SpaceTime) :
  (QFT.compTimeReflection (toComplex f)) x = ((QFT.compTimeReflectionReal f) x : ℂ) := by
  simp only [QFT.compTimeReflection, QFT.compTimeReflectionReal,
    SchwartzMap.compCLM_apply, Function.comp_apply, toComplex_apply]

/-- The real part of a complex integral of a real-valued function equals the real integral.
    This uses `integral_ofReal_eq` and `Complex.ofReal_re`.
-/
lemma re_integral_ofReal {α : Type*} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ)
    (hf : Integrable h μ) :
    (∫ x, (h x : ℂ) ∂μ).re = ∫ x, h x ∂μ := by
  rw [integral_ofReal_eq μ h hf]
  exact Complex.ofReal_re _

/-- Integrability of the real covariance kernel obtained from a real test function. -/
lemma integrable_real_covariance_kernel
  (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
  Integrable (fun p : SpaceTime × SpaceTime =>
      (QFT.compTimeReflectionReal f) p.1 * freeCovariance m p.1 p.2 * f p.2)
    (volume.prod volume) := by
  -- Get integrability from complex lemma
  have h_complex := integrable_compTimeReflection_covariance m (toComplex f)
  -- Show the integrands match (after casting)
  -- The complex integrand with toComplex f equals the real integrand cast to ℂ
  have h_eq : (fun p : SpaceTime × SpaceTime =>
      (QFT.compTimeReflection (toComplex f)) p.1 * (freeCovariance m p.1 p.2 : ℂ)
          * (toComplex f) p.2)
      = (fun p => (((QFT.compTimeReflectionReal f) p.1 : ℂ) * ((freeCovariance m p.1 p.2 : ℝ) : ℂ)
          * ((f p.2 : ℝ) : ℂ))) := by
    ext p
    simp only [compTimeReflection_toComplex_eq_ofReal, toComplex_apply]
  rw [h_eq] at h_complex
  -- h_complex has distributed casts: ↑a * ↑b * ↑c
  -- We need integrability of the real function a * b * c
  -- Key: ‖↑a * ↑b * ↑c‖ = ‖a * b * c‖ since all factors are real
  have h_norm_eq : ∀ p : SpaceTime × SpaceTime,
      ‖((QFT.compTimeReflectionReal f) p.1 : ℂ) * ((freeCovariance m p.1 p.2 : ℝ) : ℂ)
          * ((f p.2 : ℝ) : ℂ)‖
      = ‖(QFT.compTimeReflectionReal f) p.1 * freeCovariance m p.1 p.2 * f p.2‖ := by
    intro p
    simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  -- The .re of distributed casts ↑a * ↑b * ↑c equals a * b * c
  have h_re_eq : ∀ p : SpaceTime × SpaceTime,
      (((QFT.compTimeReflectionReal f) p.1 : ℂ) * ((freeCovariance m p.1 p.2 : ℝ) : ℂ)
          * ((f p.2 : ℝ) : ℂ)).re
      = (QFT.compTimeReflectionReal f) p.1 * freeCovariance m p.1 p.2 * f p.2 := by
    intro p
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  -- Transfer integrability using norm equivalence via Integrable.mono'
  -- The real integrand is the .re of the complex integrand (which is real-valued)
  apply Integrable.mono' h_complex.norm
  · -- AEStronglyMeasurable for real function: use that it's the .re of the complex one
    convert h_complex.aestronglyMeasurable.re using 2 with p
    exact (h_re_eq p).symm
  · -- ‖real_integrand‖ ≤ ‖complex_integrand‖ a.e. (actually equal)
    filter_upwards with p
    rw [← h_norm_eq p]

/-- Fubini helper: rewrite the real kernel double integral over the product measure. -/
lemma integral_prod_real_covariance_kernel
  (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
  ∫ p : SpaceTime × SpaceTime,
      (QFT.compTimeReflectionReal f) p.1 * freeCovariance m p.1 p.2 * f p.2 ∂(volume.prod volume)
    =
      ∫ x, ∫ y,
        (QFT.compTimeReflectionReal f) x * freeCovariance m x y * f y ∂volume ∂volume := by
  rw [MeasureTheory.integral_prod]
  exact integrable_real_covariance_kernel m f

/-- Complex Fubini helper mirroring `integral_prod_real_covariance_kernel`. -/
lemma integral_prod_complex_covariance_kernel
  (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
  ∫ p : SpaceTime × SpaceTime,
      (QFT.compTimeReflection (toComplex f)) p.1 * (freeCovariance m p.1 p.2 : ℂ)
          * (toComplex f) p.2 ∂(volume.prod volume)
    =
      ∫ x, ∫ y,
        (QFT.compTimeReflection (toComplex f)) x * (freeCovariance m x y : ℂ)
          * (toComplex f) y ∂volume ∂volume := by
  rw [MeasureTheory.integral_prod]
  exact integrable_compTimeReflection_covariance m (toComplex f)

/-- ** (Real-Complex Integral Correspondence):**
  The real integral with compTimeReflectionReal equals the real part of the
  corresponding complex integral after complexification.

  **Proof idea**: The complex integrand equals `(r x y : ℂ)` where `r` is the real integrand
  (using `compTimeReflection_toComplex_eq_ofReal` and `toComplex_apply`).
  For real-valued integrands, the `.re` of the complex integral equals the real integral
  via `integral_ofReal_eq` applied twice.
-/
lemma real_integral_eq_complex_re
  (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
  ∫ x, ∫ y, (QFT.compTimeReflectionReal f) x * freeCovariance m x y * f y ∂volume ∂volume
    = (∫ x, ∫ y, (QFT.compTimeReflection (toComplex f)) x * (freeCovariance m x y : ℂ)
        * (toComplex f) y ∂volume ∂volume).re := by
  -- Key: The complex integrand equals ofReal of the real product
  have h_eq : ∀ x y, (QFT.compTimeReflection (toComplex f)) x * (freeCovariance m x y : ℂ)
        * (toComplex f) y
      = ((QFT.compTimeReflectionReal f) x * freeCovariance m x y * f y : ℂ) := by
    intro x y
    simp only [compTimeReflection_toComplex_eq_ofReal, toComplex_apply]
  -- Strategy: use Fubini to convert to product measure, apply re_integral_ofReal, convert back
  -- First rewrite RHS using Fubini for complex (before h_eq rewrite)
  rw [← integral_prod_complex_covariance_kernel m f]
  -- Now RHS is (∫ p, complex_integrand(p)).re
  -- Rewrite the complex integrand using h_eq
  have h_eq_prod : ∀ p : SpaceTime × SpaceTime,
      (QFT.compTimeReflection (toComplex f)) p.1 * (freeCovariance m p.1 p.2 : ℂ)
          * (toComplex f) p.2
      = ((QFT.compTimeReflectionReal f) p.1 * freeCovariance m p.1 p.2 * f p.2 : ℂ) := by
    intro p
    exact h_eq p.1 p.2
  simp_rw [h_eq_prod]
  -- Now RHS is (∫ p, (r(p) : ℂ)).re where r is real
  -- But the cast is distributed: ↑a * ↑b * ↑c, need to convert to ↑(a*b*c)
  simp only [← Complex.ofReal_mul]
  -- Now RHS has the single cast form ↑(a * b * c)
  -- Use Fubini on LHS
  rw [← integral_prod_real_covariance_kernel m f]
  -- Now goal is: ∫ r(p) = (∫ (r(p) : ℂ)).re
  symm
  exact re_integral_ofReal (volume.prod volume)
    (fun p => (QFT.compTimeReflectionReal f) p.1 * freeCovariance m p.1 p.2 * f p.2)
    (integrable_real_covariance_kernel m f)

/-- ** (Complex Conjugate Identity for Real Functions):**
  For real-valued test functions lifted to complex, the complex conjugate equals the original.
  This allows us to match the Parseval identity which uses starRingEnd.
-/
lemma toComplex_star_eq
  (f : TestFunction) (x : SpaceTime) :
  starRingEnd ℂ ((toComplex f) x) = (toComplex f) x := by
  -- toComplex f x = (f x : ℂ) by definition
  simp only [toComplex_apply]
  -- The conjugate of a real number (lifted to ℂ) is itself
  exact Complex.conj_ofReal (f x)

/-- The time-reflected complexification of a real test function remains real-valued. -/
lemma compTimeReflection_toComplex_star_eq
  (f : TestFunction) (x : SpaceTime) :
  starRingEnd ℂ ((QFT.compTimeReflection (toComplex f)) x)
    = (QFT.compTimeReflection (toComplex f)) x := by
  -- compTimeReflection is composition with timeReflectionCLM
  simp only [QFT.compTimeReflection, SchwartzMap.compCLM_apply, Function.comp_apply]
  -- Now we have (toComplex f) (QFT.timeReflectionCLM x)
  -- Use the fact that toComplex produces real values
  exact toComplex_star_eq f (QFT.timeReflectionCLM x)

/-! ## Euclidean Invariance -/

/-- Euclidean invariance of the free covariance.
    Since freeCovariance only depends on ‖x - y‖ (via the Bessel form), and Euclidean
    transformations preserve distances, this follows immediately.
-/
theorem freeCovariance_euclidean_invariant (m : ℝ)
  (g : QFT.E) (x y : SpaceTime) :
  freeCovariance m (QFT.act g x) (QFT.act g y) = freeCovariance m x y := by
  -- freeCovariance = freeCovarianceBessel only depends on ‖x - y‖
  -- Euclidean transformations preserve this distance
  unfold freeCovariance freeCovarianceBessel
  -- QFT.act g x - QFT.act g y = g.R (x - y) where g.R is a linear isometry
  have h_diff : QFT.act g x - QFT.act g y = g.R (x - y) := by simp [QFT.act]
  simp only [h_diff, g.R.norm_map]

/-- Time reflection as an element of the Euclidean group (rotation with no translation). -/
def timeReflectionE : QFT.E := ⟨QFT.timeReflectionLE.toLinearIsometry, 0⟩

/-- The Euclidean action of timeReflectionE equals timeReflection. -/
lemma act_timeReflectionE (x : SpaceTime) : QFT.act timeReflectionE x = QFT.timeReflection x := by
  simp only [timeReflectionE, QFT.act, add_zero, LinearIsometryEquiv.coe_toLinearIsometry]
  rfl

/-- ** (Time Reflection Invariance - Position Space):**
  The position-space covariance kernel is invariant under geometric time reflection.
  This follows from general Euclidean invariance since time reflection is in O(4).
-/
lemma covariance_timeReflection_invariant (m : ℝ) :
    ∀ x y, freeCovariance m (QFT.timeReflection x) (QFT.timeReflection y) = freeCovariance m x y :=
      by
  intro x y
  rw [← act_timeReflectionE x, ← act_timeReflectionE y]
  exact freeCovariance_euclidean_invariant m timeReflectionE x y

/-! ## Complex Extension

Note: `freeCovarianceℂBilinear` is defined in Parseval.lean (imported above).
The following lemmas prove properties of this bilinear form.
-/

/-- For each fixed `x`, the inner integral in the complex bilinear form is absolutely integrable.
    This follows from product integrability (`freeCovarianceℂ_bilinear_integrable`) plus Fubini.
-/
lemma freeCovarianceℂ_bilinear_inner_integrable
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  Integrable (fun x => ∫ y, (f x) * (freeCovariance m x y) * (g y) ∂volume) volume := by
  have h := freeCovarianceℂ_bilinear_integrable m f g
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

/-- For each fixed `x`, the inner integral defining the bilinear form is integrable in `y`.
    Together with the previous lemma, this allows iterated integration.
    Follows from product integrability via Fubini (`Integrable.prod_right_ae`).
-/
lemma freeCovarianceℂ_bilinear_slice_integrable
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  ∀ᵐ x ∂volume, Integrable (fun y => (f x) * (freeCovariance m x y) * (g y)) volume := by
  have h := freeCovarianceℂ_bilinear_integrable m f g
  rw [Measure.volume_eq_prod] at h
  exact h.prod_right_ae

/-- Generalized bilinearity in the first argument: scalar multiplication and addition combined. -/
theorem freeCovarianceℂ_bilinear_add_smul_left
  (m : ℝ) [Fact (0 < m)] (c : ℂ) (f₁ f₂ g : TestFunctionℂ) :
    freeCovarianceℂBilinear m (c • f₁ + f₂) g
      = c * freeCovarianceℂBilinear m f₁ g + freeCovarianceℂBilinear m f₂ g := by
  classical
  -- Expand the definition and introduce convenient abbreviations for the
  -- outer integrands that appear in the bilinear form.
  simp only [freeCovarianceℂBilinear]
  set F := fun x : SpaceTime =>
    ∫ y, ((c • f₁ + f₂) x) * (freeCovariance m x y : ℂ) * (g y) ∂volume
  set F₁ := fun x : SpaceTime =>
    ∫ y, f₁ x * (freeCovariance m x y : ℂ) * (g y) ∂volume
  set F₂ := fun x : SpaceTime =>
    ∫ y, f₂ x * (freeCovariance m x y : ℂ) * (g y) ∂volume
  have hF : Integrable F volume :=
    freeCovarianceℂ_bilinear_inner_integrable m (c • f₁ + f₂) g
  have hF₁ : Integrable F₁ volume :=
    freeCovarianceℂ_bilinear_inner_integrable m f₁ g
  have hF₂ : Integrable F₂ volume :=
    freeCovarianceℂ_bilinear_inner_integrable m f₂ g
  -- For almost every x we can expand the inner integral using linearity.
  have h_add_smul_ae :
      F =ᵐ[volume] fun x => c * F₁ x + F₂ x := by
    have h_slice₁ :=
      freeCovarianceℂ_bilinear_slice_integrable m f₁ g
    have h_slice₂ :=
      freeCovarianceℂ_bilinear_slice_integrable m f₂ g
    refine (h_slice₁.and h_slice₂).mono ?_
    intro x hx
    rcases hx with ⟨hf₁x, hf₂x⟩
    have hfun :
        (fun y => ((c • f₁ + f₂) x) * (freeCovariance m x y : ℂ) * (g y))
          = fun y =>
              c * (f₁ x * (freeCovariance m x y : ℂ) * (g y))
                + f₂ x * (freeCovariance m x y : ℂ) * (g y) := by
      funext y
      -- (c • f₁ + f₂) x = c * f₁ x + f₂ x
      have h1 : (c • f₁ + f₂) x = c * f₁ x + f₂ x := rfl
      rw [h1]
      ring
    calc
      F x
          = ∫ y,
              ((c • f₁ + f₂) x) * (freeCovariance m x y) * (g y) ∂volume := rfl
      _ = ∫ y,
            (c * (f₁ x * (freeCovariance m x y) * (g y)) +
              f₂ x * (freeCovariance m x y) * (g y)) ∂volume := by
            rw [hfun]
      _ = c * F₁ x + F₂ x := by
            have h_const_out : ∫ y, c * (f₁ x * (freeCovariance m x y) * (g y)) ∂volume
                             = c * ∫ y, (f₁ x * (freeCovariance m x y) * (g y)) ∂volume := by
              exact MeasureTheory.integral_const_mul c _
            rw [integral_add, h_const_out]
            · apply Integrable.const_mul
              exact hf₁x
            · exact hf₂x
  have h_int_eq : ∫ x, F x ∂volume = ∫ x, (c * F₁ x + F₂ x) ∂volume :=
    integral_congr_ae h_add_smul_ae
  -- Apply linearity of the outer integral.
  have hF₁_smul : Integrable (fun x => c * F₁ x) volume := by
    apply Integrable.const_mul
    exact hF₁
  have h_sum := integral_add hF₁_smul hF₂
  calc
    ∫ x, F x ∂volume
        = ∫ x, (c * F₁ x + F₂ x) ∂volume := h_int_eq
    _ = (∫ x, c * F₁ x ∂volume) + (∫ x, F₂ x ∂volume) := h_sum
    _ = c * (∫ x, F₁ x ∂volume) + (∫ x, F₂ x ∂volume) := by
        congr 1; exact MeasureTheory.integral_const_mul _ _

theorem freeCovarianceℂ_bilinear_add_left
  (m : ℝ) [Fact (0 < m)] (f₁ f₂ g : TestFunctionℂ) :
    freeCovarianceℂBilinear m (f₁ + f₂) g
      = freeCovarianceℂBilinear m f₁ g + freeCovarianceℂBilinear m f₂ g := by
  -- Use the generalized lemma with c = 1
  have h := freeCovarianceℂ_bilinear_add_smul_left m 1 f₁ f₂ g
  -- Simplify 1 • f₁ = f₁ and 1 * (...) = (...)
  simp only [one_smul, one_mul] at h
  exact h

theorem freeCovarianceℂ_bilinear_smul_left
  (m : ℝ) [Fact (0 < m)] (c : ℂ) (f g : TestFunctionℂ) :
    freeCovarianceℂBilinear m (c • f) g = c * freeCovarianceℂBilinear m f g := by
  -- Use the generalized lemma with f₁ = f and f₂ = 0
  have h := freeCovarianceℂ_bilinear_add_smul_left m c f 0 g
  -- Simplify: c • f + 0 = c • f
  rw [add_zero] at h
  -- Need to show freeCovarianceℂBilinear m 0 g = 0
  have zero_bilinear : freeCovarianceℂBilinear m 0 g = 0 := by
    unfold freeCovarianceℂBilinear
    -- 0 x = 0, so the integrand becomes 0 * ... = 0
    have h : ∀ x y, (0 : TestFunctionℂ) x * (freeCovariance m x y : ℂ) * g y = 0 := by
      intro x y
      -- (0 : TestFunctionℂ) x = 0
      have : (0 : TestFunctionℂ) x = 0 := rfl
      rw [this]
      simp only [zero_mul]
    simp_rw [h]
    rw [integral_zero, integral_zero]
  rw [zero_bilinear, add_zero] at h
  exact h

/-- Symmetry of the complex bilinear form: swapping arguments gives the same result. -/
theorem freeCovarianceℂ_bilinear_symm
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
    freeCovarianceℂBilinear m f g = freeCovarianceℂBilinear m g f := by
  unfold freeCovarianceℂBilinear
  -- Use the symmetry of the underlying covariance kernel freeCovariance m x y = freeCovariance m y
  -- x
  -- Apply change of variables: swap x ↔ y in the integration domain
  have h : ∫ x, ∫ y, (f x) * (freeCovariance m x y) * (g y) ∂volume ∂volume
         = ∫ y, ∫ x, (f x) * (freeCovariance m x y) * (g y) ∂volume ∂volume := by
    -- Swap the order of integration (follows from Fubini's theorem)
    -- We have the necessary integrability condition from freeCovarianceℂ_bilinear_integrable
    apply MeasureTheory.integral_integral_swap
    -- The integrand is integrable on the product space
    exact freeCovarianceℂ_bilinear_integrable m f g
  rw [h]
  -- Now apply variable relabeling: swap variable names x ↔ y in the second integral
  -- ∫ y, ∫ x, f x * freeCovariance m x y * g y = ∫ x, ∫ y, f y * freeCovariance m y x * g x
  have relabel : ∫ y, ∫ x, (f x) * (freeCovariance m x y) * (g y) ∂volume ∂volume
               = ∫ x, ∫ y, (f y) * (freeCovariance m y x) * (g x) ∂volume ∂volume := by
    -- This is just renaming bound variables, which is always valid
    rfl
  rw [relabel]
  -- Now use symmetry of freeCovariance: freeCovariance m y x = freeCovariance m x y
  congr 1 with x
  congr 1 with y
  rw [freeCovariance_symmetric m y x]
  -- Rearrange: g x * freeCovariance m x y * f y = g x * freeCovariance m x y * f y
  ring

theorem freeCovarianceℂ_bilinear_smul_right
  (m : ℝ) [Fact (0 < m)] (c : ℂ) (f g : TestFunctionℂ) :
    freeCovarianceℂBilinear m f (c • g) = c * freeCovarianceℂBilinear m f g := by
  -- Use symmetry to convert right scalar multiplication to left scalar multiplication
  -- freeCovarianceℂBilinear m f (c • g) = freeCovarianceℂBilinear m (c • g) f
  rw [freeCovarianceℂ_bilinear_symm m f (c • g)]
  -- Apply left scalar multiplication: freeCovarianceℂBilinear m (c • g) f = c *
  -- freeCovarianceℂBilinear m g f
  rw [freeCovarianceℂ_bilinear_smul_left m c g f]
  -- Use symmetry again: c * freeCovarianceℂBilinear m g f = c * freeCovarianceℂBilinear m f g
  rw [freeCovarianceℂ_bilinear_symm m g f]

theorem freeCovarianceℂ_bilinear_add_right
  (m : ℝ) [Fact (0 < m)] (f g₁ g₂ : TestFunctionℂ) :
    freeCovarianceℂBilinear m f (g₁ + g₂)
      = freeCovarianceℂBilinear m f g₁ + freeCovarianceℂBilinear m f g₂ := by
  -- Use symmetry to convert right addition to left addition
  -- freeCovarianceℂBilinear m f (g₁ + g₂) = freeCovarianceℂBilinear m (g₁ + g₂) f
  rw [freeCovarianceℂ_bilinear_symm m f (g₁ + g₂)]
  -- Apply left addition: freeCovarianceℂBilinear m (g₁ + g₂) f = freeCovarianceℂBilinear m g₁ f +
  -- freeCovarianceℂBilinear m g₂ f
  rw [freeCovarianceℂ_bilinear_add_left m g₁ g₂ f]
  -- Use symmetry on each term: freeCovarianceℂBilinear m g₁ f + freeCovarianceℂBilinear m g₂ f =
  -- freeCovarianceℂBilinear m f g₁ + freeCovarianceℂBilinear m f g₂
  rw [freeCovarianceℂ_bilinear_symm m g₁ f, freeCovarianceℂ_bilinear_symm m g₂ f]

/-- Complex extension of the covariance for complex test functions, using regulated Fourier
form. -/
def freeCovarianceℂRegulated (α : ℝ) (m : ℝ) (f g : TestFunctionℂ) : ℂ :=
  ∫ x, ∫ y,
    (f x) * freeCovarianceRegulated α m x y * starRingEnd ℂ (g y)
      ∂volume ∂volume

/-- The regulated complex covariance is positive definite for any α > 0. -/
theorem freeCovarianceℂ_regulated_positive (α : ℝ) (hα : 0 < α) (m : ℝ) [Fact (0 < m)] (f :
  TestFunctionℂ) :
  0 ≤ (freeCovarianceℂRegulated α m f f).re := by
  unfold freeCovarianceℂRegulated
  rw [parseval_covariance_schwartz_regulated' α hα m f]
  apply MeasureTheory.integral_nonneg
  intro k
  apply mul_nonneg
  · apply mul_nonneg
    · exact Real.exp_nonneg _
    · exact sq_nonneg _
  · exact freePropagatorMomentum_mathlib_nonneg m (Fact.out) k

/-- Complex extension of the covariance for complex test functions (limit form via Bessel). -/
def freeCovarianceℂ (m : ℝ) (f g : TestFunctionℂ) : ℂ :=
  ∫ x, ∫ y, (f x) * (freeCovariance m x y) * (starRingEnd ℂ (g y)) ∂volume ∂volume

/-- The complex covariance (Bessel form) is positive definite. -/
theorem freeCovarianceℂ_positive (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    0 ≤ (freeCovarianceℂ m f f).re := by
  -- The regulated form converges to the Bessel form as α → 0⁺
  -- Use the specialized f = f version which leverages momentum-space DCT
  have h_tendsto := bilinear_covariance_regulated_tendsto_self m f
  -- This is the same as: freeCovarianceℂRegulated α m f f → freeCovarianceℂ m f f
  have h_tendsto' : Filter.Tendsto (fun α => freeCovarianceℂRegulated α m f f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (freeCovarianceℂ m f f)) := h_tendsto
  -- By continuity of .re, the real parts also converge
  have h_tendsto_re : Filter.Tendsto (fun α => (freeCovarianceℂRegulated α m f f).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (freeCovarianceℂ m f f).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp h_tendsto'
  -- The regulated forms are nonnegative for α > 0
  have h_nonneg : ∀ᶠ α in nhdsWithin 0 (Set.Ioi 0),
      0 ≤ (freeCovarianceℂRegulated α m f f).re := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact freeCovarianceℂ_regulated_positive α hα m f
  -- Pass through the limit
  exact ge_of_tendsto h_tendsto_re h_nonneg

/-- **(Parseval for Bessel Covariance):**
    The Parseval identity for the well-defined Bessel form of the covariance.
    This directly relates the position-space covariance integral to the momentum-space integral.

    Note: Unlike the regulated form, this uses freeCovariance (Bessel K₁ form) which is
    well-defined pointwise. The equality holds because the Bessel form equals the limit
    of the regulated forms.
-/
theorem parseval_covariance_schwartz_bessel (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    (freeCovarianceℂ m f f).re
    = ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentumMathlib m k ∂volume
      := by
  -- Strategy: Use uniqueness of limits
  -- 1. bilinear_covariance_regulated_tendsto_self: lim (regulated) = Bessel (in ℂ) for f = f case
  -- 2. parseval_covariance_schwartz_correct: lim (regulated).re = momentum (in ℝ)
  -- 3. By continuity of .re: (Bessel).re = momentum
  -- The Bessel form is defined as freeCovarianceℂ
  -- freeCovarianceℂ m f f = ∫∫ f(x) * C(x,y) * conj(f(y))
  have h_bessel_eq : freeCovarianceℂ m f f =
      ∫ x, ∫ y, f x * (freeCovariance m x y : ℂ) * (starRingEnd ℂ (f y)) := rfl
  -- The complex bilinear form converges to the Bessel form
  -- Use the specialized f = f version which leverages momentum-space DCT
  have h_tendsto_complex := bilinear_covariance_regulated_tendsto_self m f
  -- The .re of the regulated form converges to the momentum integral
  have h_tendsto_re := parseval_covariance_schwartz_correct m f
  -- By continuity of .re, the limit of (regulated).re equals (limit of regulated).re
  have h_re_continuous : Continuous Complex.re := Complex.continuous_re
  -- The .re of the limit equals the limit of .re
  have h_re_tendsto : Filter.Tendsto
      (fun α => (∫ x, ∫ y, f x * (freeCovarianceRegulated α m x y : ℂ) * (starRingEnd ℂ (f y))).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, ∫ y, f x * (freeCovariance m x y : ℂ) * (starRingEnd ℂ (f y))).re) :=
    h_re_continuous.continuousAt.tendsto.comp h_tendsto_complex
  -- By uniqueness of limits in ℝ, the two limits are equal
  have h_unique := tendsto_nhds_unique h_re_tendsto h_tendsto_re
  rw [h_bessel_eq]
  exact h_unique

/-! ## OS Properties -/
